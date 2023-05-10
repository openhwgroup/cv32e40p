// Copyright 2020 Silicon Labs, Inc.
//
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License").
//
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
//
// You may obtain a copy of the License at:
//
//     https://solderpad.org/licenses/SHL-2.0/
//
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof distributed under the License
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS
// OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
//
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Arjan Bink - arjan.bink@silabs.com                         //
//                                                                            //
// Design Name:    Sleep Unit                                                 //
// Project Name:   CV32E40P                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Sleep unit containing the instantiated clock gate which    //
//                 provides the gated clock (clk_gated_o) for the rest        //
//                 of the design.                                             //
//                                                                            //
//                 The clock is gated for the following scenarios:            //
//                                                                            //
//                 - While waiting for fetch to become enabled                //
//                 - While blocked on a WFI (COREV_CLUSTER = 0)               //
//                 - While clock_en_i = 0 during a cv.elw (COREV_CLUSTER = 1) //
//                                                                            //
//                 Sleep is signaled via core_sleep_o when:                   //
//                                                                            //
//                 - During a cv.elw (except in debug (i.e. pending debug     //
//                   request, debug mode, single stepping, trigger match)     //
//                 - During a WFI (except in debug)                           //
//                                                                            //
// Requirements:   If COREV_CLUSTER = 1 the environment must guarantee:       //
//                                                                            //
//                 - If core_sleep_o    == 1'b0, then pulp_clock_en_i == 1'b1 //
//                 - If pulp_clock_en_i == 1'b0, then irq_i == 'b0            //
//                 - If pulp_clock_en_i == 1'b0, then debug_req_i == 1'b0     //
//                 - If pulp_clock_en_i == 1'b0, then instr_rvalid_i == 1'b0  //
//                 - If pulp_clock_en_i == 1'b0, then instr_gnt_i == 1'b0     //
//                 - If pulp_clock_en_i == 1'b0, then data_rvalid_i == 1'b0   //
//                 - If pulp_clock_en_i == 1'b0, then data_gnt_i == 1'b1      //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40p_sleep_unit #(
    parameter COREV_CLUSTER = 0
) (
    // Clock, reset interface
    input  logic clk_ungated_i,  // Free running clock
    input  logic rst_n,
    output logic clk_gated_o,  // Gated clock
    input  logic scan_cg_en_i,  // Enable all clock gates for testing

    // Core sleep
    output logic core_sleep_o,

    // Fetch enable
    input  logic fetch_enable_i,
    output logic fetch_enable_o,

    // Core status
    input logic if_busy_i,
    input logic ctrl_busy_i,
    input logic lsu_busy_i,
    input logic apu_busy_i,

    // PULP Cluster interface
    input logic pulp_clock_en_i,  // PULP clock enable (only used if COREV_CLUSTER = 1)
    input logic p_elw_start_i,
    input logic p_elw_finish_i,
    input logic debug_p_elw_no_sleep_i,

    // WFI wake
    input logic wake_from_sleep_i
);

  import cv32e40p_pkg::*;

  logic fetch_enable_q;  // Sticky version of fetch_enable_i
  logic fetch_enable_d;
  logic              core_busy_q;               // Is core still busy (and requires a clock) with what needs to finish before entering sleep?
  logic core_busy_d;
  logic p_elw_busy_q;  // Busy with cv.elw (transaction in progress)?
  logic p_elw_busy_d;
  logic clock_en;  // Final clock enable

  //////////////////////////////////////////////////////////////////////////////
  // Sleep FSM
  //////////////////////////////////////////////////////////////////////////////

  // Make sticky version of fetch_enable_i
  assign fetch_enable_d = fetch_enable_i ? 1'b1 : fetch_enable_q;

  generate
    if (COREV_CLUSTER) begin : g_pulp_sleep

      // Busy unless in a cv.elw and IF/APU are no longer busy
      assign core_busy_d = p_elw_busy_d ? (if_busy_i || apu_busy_i) : 1'b1;

      // Enable the clock only after the initial fetch enable while busy or instructed so by PULP Cluster's pulp_clock_en_i
      assign clock_en = fetch_enable_q && (pulp_clock_en_i || core_busy_q);

      // Sleep only in response to cv.elw onec no longer busy (but not during various debug scenarios)
      assign core_sleep_o = p_elw_busy_d && !core_busy_q && !debug_p_elw_no_sleep_i;

      // cv.elw is busy between load start and load finish (data_req_o / data_rvalid_i)
      assign p_elw_busy_d = p_elw_start_i ? 1'b1 : (p_elw_finish_i ? 1'b0 : p_elw_busy_q);

    end else begin : g_no_pulp_sleep

      // Busy when any of the sub units is busy (typically wait for the instruction buffer to fill up)
      assign core_busy_d = if_busy_i || ctrl_busy_i || lsu_busy_i || apu_busy_i;

      // Enable the clock only after the initial fetch enable while busy or waking up to become busy
      assign clock_en = fetch_enable_q && (wake_from_sleep_i || core_busy_q);

      // Sleep only in response to WFI which leads to clock disable; debug_wfi_no_sleep_o in
      // cv32e40p_controller determines the scenarios for which WFI can(not) cause sleep.
      assign core_sleep_o = fetch_enable_q && !clock_en;

      // cv.elw does not exist for COREV_CLUSTER = 0
      assign p_elw_busy_d = 1'b0;

    end
  endgenerate

  always_ff @(posedge clk_ungated_i, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      core_busy_q    <= 1'b0;
      p_elw_busy_q   <= 1'b0;
      fetch_enable_q <= 1'b0;
    end else begin
      core_busy_q    <= core_busy_d;
      p_elw_busy_q   <= p_elw_busy_d;
      fetch_enable_q <= fetch_enable_d;
    end
  end

  // Fetch enable for Controller
  assign fetch_enable_o = fetch_enable_q;

  // Main clock gate of CV32E40P
  cv32e40p_clock_gate core_clock_gate_i (
      .clk_i       (clk_ungated_i),
      .en_i        (clock_en),
      .scan_cg_en_i(scan_cg_en_i),
      .clk_o       (clk_gated_o)
  );

  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------

`ifdef CV32E40P_ASSERT_ON

  // Clock gate is disabled during RESET state of the controller
  property p_clock_en_0;
    @(posedge clk_ungated_i) disable iff (!rst_n) ((id_stage_i.controller_i.ctrl_fsm_cs == cv32e40p_pkg::RESET) && (id_stage_i.controller_i.ctrl_fsm_ns == cv32e40p_pkg::RESET)) |-> (clock_en == 1'b0);
  endproperty

  a_clock_en_0 :
  assert property (p_clock_en_0);

  // Clock gate is enabled when exit from RESET state is required
  property p_clock_en_1;
    @(posedge clk_ungated_i) disable iff (!rst_n) ((id_stage_i.controller_i.ctrl_fsm_cs == cv32e40p_pkg::RESET) && (id_stage_i.controller_i.ctrl_fsm_ns != cv32e40p_pkg::RESET)) |-> (clock_en == 1'b1);
  endproperty

  a_clock_en_1 :
  assert property (p_clock_en_1);

  // Clock gate is not enabled before receiving fetch_enable_i pulse
  property p_clock_en_2;
    @(posedge clk_ungated_i) disable iff (!rst_n) (fetch_enable_q == 1'b0) |-> (clock_en == 1'b0);
  endproperty

  a_clock_en_2 :
  assert property (p_clock_en_2);

  generate
    if (COREV_CLUSTER) begin : g_pulp_cluster_assertions

      // Clock gate is only possibly disabled in RESET or when COREV_CLUSTER disables clock
      property p_clock_en_3;
        @(posedge clk_ungated_i) disable iff (!rst_n) (clock_en == 1'b0) -> ((id_stage_i.controller_i.ctrl_fsm_cs == cv32e40p_pkg::RESET) || (COREV_CLUSTER && !pulp_clock_en_i));
      endproperty

      a_clock_en_3 :
      assert property (p_clock_en_3);

      // Core can only sleep in response to cv.elw
      property p_only_sleep_during_p_elw;
        @(posedge clk_ungated_i) disable iff (!rst_n) (core_sleep_o == 1'b1) |-> (p_elw_busy_d == 1'b1);
      endproperty

      a_only_sleep_during_p_elw :
      assert property (p_only_sleep_during_p_elw);


      // Environment fully controls clock_en during sleep
      property p_full_clock_en_control;
        @(posedge clk_ungated_i) disable iff (!rst_n) (core_sleep_o == 1'b1) |-> (pulp_clock_en_i == clock_en);
      endproperty

      a_full_clock_en_control :
      assert property (p_full_clock_en_control);

    end else begin : g_no_pulp_cluster_assertions

      // Clock gate is only possibly disabled in RESET or SLEEP
      property p_clock_en_4;
        @(posedge clk_ungated_i) disable iff (!rst_n) (clock_en == 1'b0) -> ((id_stage_i.controller_i.ctrl_fsm_cs == cv32e40p_pkg::RESET) || (id_stage_i.controller_i.ctrl_fsm_ns == cv32e40p_pkg::SLEEP));
      endproperty

      a_clock_en_4 :
      assert property (p_clock_en_4);

      // Clock gate is enabled when exit from SLEEP state is required
      property p_clock_en_5;
        @(posedge clk_ungated_i) disable iff (!rst_n)  ((id_stage_i.controller_i.ctrl_fsm_cs == cv32e40p_pkg::SLEEP) && (id_stage_i.controller_i.ctrl_fsm_ns != cv32e40p_pkg::SLEEP)) |-> (clock_en == 1'b1);
      endproperty

      a_clock_en_5 :
      assert property (p_clock_en_5);

      // Core sleep is only signaled in SLEEP state
      property p_core_sleep;
        @(posedge clk_ungated_i) disable iff (!rst_n) (core_sleep_o == 1'b1) -> ((id_stage_i.controller_i.ctrl_fsm_cs == cv32e40p_pkg::SLEEP));
      endproperty

      a_core_sleep :
      assert property (p_core_sleep);

      // Core can only become non-busy due to SLEEP entry
      property p_non_busy;
        @(posedge clk_ungated_i) disable iff (!rst_n) (core_busy_d == 1'b0) |-> (id_stage_i.controller_i.ctrl_fsm_cs == cv32e40p_pkg::WAIT_SLEEP) || (id_stage_i.controller_i.ctrl_fsm_cs == cv32e40p_pkg::SLEEP);
      endproperty

      a_non_busy :
      assert property (p_non_busy);

      // During (COREV_CLUSTER = 0) sleep it should be allowed to externally gate clk_i
      property p_gate_clk_i;
        @(posedge clk_ungated_i) disable iff (!rst_n) (core_sleep_o == 1'b1) |-> (core_busy_q == core_busy_d) && (p_elw_busy_q == p_elw_busy_d) && (fetch_enable_q == fetch_enable_d);
      endproperty

      a_gate_clk_i :
      assert property (p_gate_clk_i);

      // During sleep the internal clock is gated
      property p_gate_clock_during_sleep;
        @(posedge clk_ungated_i) disable iff (!rst_n) (core_sleep_o == 1'b1) |-> (clock_en == 1'b0);
      endproperty

      a_gate_clock_during_sleep :
      assert property (p_gate_clock_during_sleep);

      // Sleep mode can only be entered in response to a WFI instruction
      property p_only_sleep_for_wfi;
        @(posedge clk_ungated_i) disable iff (!rst_n) (core_sleep_o == 1'b1) |-> (id_stage_i.instr == {
          12'b000100000101, 13'b0, OPCODE_SYSTEM
        });
      endproperty

      a_only_sleep_for_wfi :
      assert property (p_only_sleep_for_wfi);

      // In sleep mode the core will not be busy (e.g. no ongoing/outstanding instruction or data transactions)
      property p_not_busy_during_sleep;
        @(posedge clk_ungated_i) disable iff (!rst_n) (core_sleep_o == 1'b1) |-> ((core_busy_q == 1'b0) && (core_busy_d == 1'b0));
      endproperty

      a_not_busy_during_sleep :
      assert property (p_not_busy_during_sleep);

    end
  endgenerate

`endif

endmodule  // cv32e40p_sleep_unit
