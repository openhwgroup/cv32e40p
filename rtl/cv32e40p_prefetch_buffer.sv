// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Design Name:    Prefetcher Buffer for 32 bit memory interface              //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Prefetch Buffer that caches instructions. This cuts overly //
//                 long critical paths to the instruction cache               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

// input port: send address one cycle before the data
// clear_i clears the FIFO for the following cycle. in_addr_i can be sent in
// this cycle already

module cv32e40p_prefetch_buffer #(
    parameter PULP_OBI = 0,  // Legacy PULP OBI behavior
    parameter COREV_PULP = 1  // PULP ISA Extension (including PULP specific CSRs and hardware loop, excluding p.elw)
) (
    input logic clk,
    input logic rst_n,

    input logic        req_i,
    input logic        branch_i,
    input logic [31:0] branch_addr_i,

    input logic        hwlp_jump_i,
    input logic [31:0] hwlp_target_i,

    input  logic        fetch_ready_i,
    output logic        fetch_valid_o,
    output logic [31:0] fetch_rdata_o,

    // goes to instruction memory / instruction cache
    output logic        instr_req_o,
    input  logic        instr_gnt_i,
    output logic [31:0] instr_addr_o,
    input  logic [31:0] instr_rdata_i,
    input  logic        instr_rvalid_i,
    input  logic        instr_err_i,  // Not used yet (future addition)
    input  logic        instr_err_pmp_i,  // Not used yet (future addition)

    // Prefetch Buffer Status
    output logic busy_o
);
  // FIFO_DEPTH controls also the number of outstanding memory requests
  // FIFO_DEPTH must be greater than 1 to respect assertion in prefetch controller
  // FIFO_DEPTH must be a power of 2 (because of the FIFO implementation)
  localparam FIFO_DEPTH                     = 2; //must be greater or equal to 2 //Set at least to 3 to avoid stalls compared to the master branch
  localparam int unsigned FIFO_ADDR_DEPTH = $clog2(FIFO_DEPTH);

  // Transaction request (between cv32e40p_prefetch_controller and cv32e40p_obi_interface)
  logic                     trans_valid;
  logic                     trans_ready;
  logic [             31:0] trans_addr;

  logic                     fifo_flush;
  logic                     fifo_flush_but_first;
  logic [FIFO_ADDR_DEPTH:0] fifo_cnt;  // fifo_cnt should count from 0 to FIFO_DEPTH!

  logic [             31:0] fifo_rdata;
  logic                     fifo_push;
  logic                     fifo_pop;
  logic                     fifo_empty;

  // Transaction response interface (between cv32e40p_obi_interface and cv32e40p_fetch_fifo)
  logic                     resp_valid;
  logic [             31:0] resp_rdata;
  logic                     resp_err;  // Unused for now

  //////////////////////////////////////////////////////////////////////////////
  // Prefetch Controller
  //////////////////////////////////////////////////////////////////////////////

  cv32e40p_prefetch_controller #(
      .DEPTH     (FIFO_DEPTH),
      .PULP_OBI  (PULP_OBI),
      .COREV_PULP(COREV_PULP)
  ) prefetch_controller_i (
      .clk  (clk),
      .rst_n(rst_n),

      .req_i        (req_i),
      .branch_i     (branch_i),
      .branch_addr_i(branch_addr_i),
      .busy_o       (busy_o),

      .hwlp_jump_i  (hwlp_jump_i),
      .hwlp_target_i(hwlp_target_i),

      .trans_valid_o(trans_valid),
      .trans_ready_i(trans_ready),
      .trans_addr_o (trans_addr),

      .resp_valid_i(resp_valid),

      .fetch_ready_i(fetch_ready_i),
      .fetch_valid_o(fetch_valid_o),

      .fifo_push_o           (fifo_push),
      .fifo_pop_o            (fifo_pop),
      .fifo_flush_o          (fifo_flush),
      .fifo_flush_but_first_o(fifo_flush_but_first),
      .fifo_cnt_i            (fifo_cnt),
      .fifo_empty_i          (fifo_empty)
  );

  //////////////////////////////////////////////////////////////////////////////
  // Fetch FIFO && fall-through path
  //////////////////////////////////////////////////////////////////////////////

  cv32e40p_fifo #(
      .FALL_THROUGH(1'b0),
      .DATA_WIDTH  (32),
      .DEPTH       (FIFO_DEPTH)
  ) fifo_i (
      .clk_i            (clk),
      .rst_ni           (rst_n),
      .flush_i          (fifo_flush),
      .flush_but_first_i(fifo_flush_but_first),
      .testmode_i       (1'b0),
      .full_o           (),
      .empty_o          (fifo_empty),
      .cnt_o            (fifo_cnt),
      .data_i           (resp_rdata),
      .push_i           (fifo_push),
      .data_o           (fifo_rdata),
      .pop_i            (fifo_pop)
  );

  // First POP from the FIFO if it is not empty.
  // Otherwise, try to fall-through it.
  assign fetch_rdata_o = fifo_empty ? resp_rdata : fifo_rdata;

  //////////////////////////////////////////////////////////////////////////////
  // OBI interface
  //////////////////////////////////////////////////////////////////////////////

  cv32e40p_obi_interface #(
      .TRANS_STABLE(0)  // trans_* is NOT guaranteed stable during waited transfers;
      // this is ignored for legacy PULP behavior (not compliant to OBI)
  )                                                     // Keep this parameter stuck to 0 to make HWLP work

  instruction_obi_i
  (
      .clk  (clk),
      .rst_n(rst_n),

      .trans_valid_i(trans_valid),
      .trans_ready_o(trans_ready),
      .trans_addr_i ({trans_addr[31:2], 2'b00}),
      .trans_we_i   (1'b0),  // Instruction interface (never write)
      .trans_be_i   (4'b1111),  // Corresponding obi_be_o not used
      .trans_wdata_i(32'b0),  // Corresponding obi_wdata_o not used
      .trans_atop_i (6'b0),  // Atomics not used on instruction bus

      .resp_valid_o(resp_valid),
      .resp_rdata_o(resp_rdata),
      .resp_err_o  (resp_err),  // Unused for now

      .obi_req_o   (instr_req_o),
      .obi_gnt_i   (instr_gnt_i),
      .obi_addr_o  (instr_addr_o),
      .obi_we_o    (),  // Left unconnected on purpose
      .obi_be_o    (),  // Left unconnected on purpose
      .obi_wdata_o (),  // Left unconnected on purpose
      .obi_atop_o  (),  // Left unconnected on purpose
      .obi_rdata_i (instr_rdata_i),
      .obi_rvalid_i(instr_rvalid_i),
      .obi_err_i   (instr_err_i)
  );

  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------

`ifdef CV32E40P_ASSERT_ON

  // FIFO_DEPTH must be greater than 1. Otherwise, the property
  // p_hwlp_end_already_gnt_when_hwlp_branch in cv32e40p_prefetch_controller
  // is not verified, since the prefetcher cannot ask for HWLP_END the cycle
  // in which HWLP_END-4 is being absorbed by ID.
  property p_fifo_depth_gt_1;
    @(posedge clk) (FIFO_DEPTH > 1);
  endproperty

  a_fifo_depth_gt_1 :
  assert property (p_fifo_depth_gt_1);

  // Check that branch target address is half-word aligned (RV32-C)
  property p_branch_halfword_aligned;
    @(posedge clk) (branch_i) |-> (branch_addr_i[0] == 1'b0);
  endproperty

  a_branch_halfword_aligned :
  assert property (p_branch_halfword_aligned);

  // Check that bus interface transactions are word aligned
  property p_instr_addr_word_aligned;
    @(posedge clk) (1'b1) |-> (instr_addr_o[1:0] == 2'b00);
  endproperty

  a_instr_addr_word_aligned :
  assert property (p_instr_addr_word_aligned);

  // Check that a taken branch can only occur if fetching is requested
  property p_branch_implies_req;
    @(posedge clk) (branch_i) |-> (req_i);
  endproperty

  a_branch_implies_req :
  assert property (p_branch_implies_req);

  // Check that after a taken branch the initial FIFO output is not accepted
  property p_branch_invalidates_fifo;
    @(posedge clk) (branch_i) |-> (!(fetch_valid_o && fetch_ready_i));
  endproperty

  a_branch_invalidates_fifo :
  assert property (p_branch_invalidates_fifo);

  // External instruction bus errors are not supported yet. PMP errors are not supported yet.
  //
  // Note: Once PMP is re-introduced please consider to make instr_err_pmp_i a 'data' signal
  // that is qualified with instr_req_o && instr_gnt_i (instead of suppressing instr_gnt_i
  // as is currently done. This will keep the instr_req_o/instr_gnt_i protocol intact.
  //
  // JUST RE-ENABLING the PMP VIA ITS USE_PMP LOCALPARAM WILL NOT WORK BECAUSE OF THE
  // GRANT SUPPRESSION IN THE PMP.

  property p_no_error;
    @(posedge clk) (1'b1) |-> ((instr_err_i == 1'b0) && (instr_err_pmp_i == 1'b0));
  endproperty

  a_no_error :
  assert property (p_no_error);




`endif

endmodule  // cv32e40p_prefetch_buffer
