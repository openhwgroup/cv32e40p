// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Wrapper for a cv32e40p, containing cv32e40p, and tracer
// Contributor: Davide Schiavone <davide@openhwgroup.org>

`ifdef CV32E40P_ASSERT_ON
`include "cv32e40p_prefetch_controller_sva.sv"
`endif

`include "cv32e40p_core_log.sv"

`ifdef CV32E40P_APU_TRACE
`include "cv32e40p_apu_tracer.sv"
`endif

`ifdef CV32E40P_TRACE_EXECUTION
`include "cv32e40p_tracer.sv"
`endif

module cv32e40p_tb_wrapper #(
    parameter PULP_XPULP       = 0, // PULP ISA Extension (incl. custom CSRs and hardware loop, excl. p.elw)
    parameter PULP_CLUSTER = 0,  // PULP Cluster interface (incl. p.elw)
    parameter FPU = 0,  // Floating Point Unit (interfaced via APU interface)
    parameter PULP_ZFINX = 0,  // Float-in-General Purpose registers
    parameter NUM_MHPMCOUNTERS = 1
) (
    // Clock and Reset
    input logic clk_i,
    input logic rst_ni,

    input logic pulp_clock_en_i,  // PULP clock enable (only used if PULP_CLUSTER = 1)
    input logic scan_cg_en_i,  // Enable all clock gates for testing

    // Core ID, Cluster ID, debug mode halt address and boot address are considered more or less static
    input logic [31:0] boot_addr_i,
    input logic [31:0] mtvec_addr_i,
    input logic [31:0] dm_halt_addr_i,
    input logic [31:0] hart_id_i,
    input logic [31:0] dm_exception_addr_i,

    // Instruction memory interface
    output logic        instr_req_o,
    input  logic        instr_gnt_i,
    input  logic        instr_rvalid_i,
    output logic [31:0] instr_addr_o,
    input  logic [31:0] instr_rdata_i,

    // Data memory interface
    output logic        data_req_o,
    input  logic        data_gnt_i,
    input  logic        data_rvalid_i,
    output logic        data_we_o,
    output logic [ 3:0] data_be_o,
    output logic [31:0] data_addr_o,
    output logic [31:0] data_wdata_o,
    input  logic [31:0] data_rdata_i,

    // Interrupt inputs
    input  logic [31:0] irq_i,  // CLINT interrupts + CLINT extension interrupts
    output logic        irq_ack_o,
    output logic [ 4:0] irq_id_o,

    // Debug Interface
    input  logic debug_req_i,
    output logic debug_havereset_o,
    output logic debug_running_o,
    output logic debug_halted_o,

    // CPU Control Signals
    input  logic fetch_enable_i,
    output logic core_sleep_o
);

`ifdef CV32E40P_ASSERT_ON

  // RTL Assertions
  bind cv32e40p_prefetch_controller:
      cv32e40p_wrapper_i.core_i.if_stage_i.prefetch_buffer_i.prefetch_controller_i
      cv32e40p_prefetch_controller_sva
      #(
      .DEPTH          (DEPTH),
      .PULP_XPULP     (PULP_XPULP),
      .PULP_OBI       (PULP_OBI),
      .FIFO_ADDR_DEPTH(FIFO_ADDR_DEPTH)
  ) prefetch_controller_sva (.*);

`endif  // CV32E40P_ASSERT_ON

`ifndef SYNTHESIS
  cv32e40p_core_log #(
      .PULP_XPULP      (PULP_XPULP),
      .PULP_CLUSTER    (PULP_CLUSTER),
      .FPU             (FPU),
      .PULP_ZFINX      (PULP_ZFINX),
      .NUM_MHPMCOUNTERS(NUM_MHPMCOUNTERS)
  ) core_log_i (
      .clk_i             (cv32e40p_wrapper_i.core_i.id_stage_i.clk),
      .is_decoding_i     (cv32e40p_wrapper_i.core_i.id_stage_i.is_decoding_o),
      .illegal_insn_dec_i(cv32e40p_wrapper_i.core_i.id_stage_i.illegal_insn_dec),
      .hart_id_i         (cv32e40p_wrapper_i.core_i.hart_id_i),
      .pc_id_i           (cv32e40p_wrapper_i.core_i.pc_id)
  );
`endif  // SYNTHESIS

`ifdef CV32E40P_APU_TRACE
  cv32e40p_apu_tracer apu_tracer_i (
      .clk_i       (cv32e40p_wrapper_i.core_i.rst_ni),
      .rst_n       (cv32e40p_wrapper_i.core_i.clk_i),
      .hart_id_i   (cv32e40p_wrapper_i.core_i.hart_id_i),
      .apu_valid_i (cv32e40p_wrapper_i.core_i.ex_stage_i.apu_valid),
      .apu_waddr_i (cv32e40p_wrapper_i.core_i.ex_stage_i.apu_waddr),
      .apu_result_i(cv32e40p_wrapper_i.core_i.ex_stage_i.apu_result)
  );
`endif

`ifdef CV32E40P_TRACE_EXECUTION
  cv32e40p_tracer #(
      .FPU       (FPU),
      .PULP_ZFINX(PULP_ZFINX)
  ) tracer_i (
      .clk_i(cv32e40p_wrapper_i.core_i.clk_i),  // always-running clock for tracing
      .rst_n(cv32e40p_wrapper_i.core_i.rst_ni),

      .hart_id_i(cv32e40p_wrapper_i.core_i.hart_id_i),

      .pc                (cv32e40p_wrapper_i.core_i.id_stage_i.pc_id_i),
      .instr             (cv32e40p_wrapper_i.core_i.id_stage_i.instr),
      .controller_state_i(cv32e40p_wrapper_i.core_i.id_stage_i.controller_i.ctrl_fsm_cs),
      .compressed        (cv32e40p_wrapper_i.core_i.id_stage_i.is_compressed_i),
      .id_valid          (cv32e40p_wrapper_i.core_i.id_stage_i.id_valid_o),
      .is_decoding       (cv32e40p_wrapper_i.core_i.id_stage_i.is_decoding_o),
      .is_illegal        (cv32e40p_wrapper_i.core_i.id_stage_i.illegal_insn_dec),
      .trigger_match     (cv32e40p_wrapper_i.core_i.id_stage_i.trigger_match_i),
      .rs1_value         (cv32e40p_wrapper_i.core_i.id_stage_i.operand_a_fw_id),
      .rs2_value         (cv32e40p_wrapper_i.core_i.id_stage_i.operand_b_fw_id),
      .rs3_value         (cv32e40p_wrapper_i.core_i.id_stage_i.alu_operand_c),
      .rs2_value_vec     (cv32e40p_wrapper_i.core_i.id_stage_i.alu_operand_b),

      .rs1_is_fp(cv32e40p_wrapper_i.core_i.id_stage_i.regfile_fp_a),
      .rs2_is_fp(cv32e40p_wrapper_i.core_i.id_stage_i.regfile_fp_b),
      .rs3_is_fp(cv32e40p_wrapper_i.core_i.id_stage_i.regfile_fp_c),
      .rd_is_fp (cv32e40p_wrapper_i.core_i.id_stage_i.regfile_fp_d),

      .ex_valid    (cv32e40p_wrapper_i.core_i.ex_valid),
      .ex_reg_addr (cv32e40p_wrapper_i.core_i.regfile_alu_waddr_fw),
      .ex_reg_we   (cv32e40p_wrapper_i.core_i.regfile_alu_we_fw),
      .ex_reg_wdata(cv32e40p_wrapper_i.core_i.regfile_alu_wdata_fw),

      .ex_data_addr   (cv32e40p_wrapper_i.core_i.data_addr_o),
      .ex_data_req    (cv32e40p_wrapper_i.core_i.data_req_o),
      .ex_data_gnt    (cv32e40p_wrapper_i.core_i.data_gnt_i),
      .ex_data_we     (cv32e40p_wrapper_i.core_i.data_we_o),
      .ex_data_wdata  (cv32e40p_wrapper_i.core_i.data_wdata_o),
      .data_misaligned(cv32e40p_wrapper_i.core_i.data_misaligned),

      .ebrk_insn(cv32e40p_wrapper_i.core_i.id_stage_i.ebrk_insn_dec),
      .debug_mode(cv32e40p_wrapper_i.core_i.debug_mode),
      .ebrk_force_debug_mode (cv32e40p_wrapper_i.core_i.id_stage_i.controller_i.ebrk_force_debug_mode),

      .wb_bypass(cv32e40p_wrapper_i.core_i.ex_stage_i.branch_in_ex_i),

      .wb_valid    (cv32e40p_wrapper_i.core_i.wb_valid),
      .wb_reg_addr (cv32e40p_wrapper_i.core_i.regfile_waddr_fw_wb_o),
      .wb_reg_we   (cv32e40p_wrapper_i.core_i.regfile_we_wb),
      .wb_reg_wdata(cv32e40p_wrapper_i.core_i.regfile_wdata),

      .imm_u_type       (cv32e40p_wrapper_i.core_i.id_stage_i.imm_u_type),
      .imm_uj_type      (cv32e40p_wrapper_i.core_i.id_stage_i.imm_uj_type),
      .imm_i_type       (cv32e40p_wrapper_i.core_i.id_stage_i.imm_i_type),
      .imm_iz_type      (cv32e40p_wrapper_i.core_i.id_stage_i.imm_iz_type[11:0]),
      .imm_z_type       (cv32e40p_wrapper_i.core_i.id_stage_i.imm_z_type),
      .imm_s_type       (cv32e40p_wrapper_i.core_i.id_stage_i.imm_s_type),
      .imm_sb_type      (cv32e40p_wrapper_i.core_i.id_stage_i.imm_sb_type),
      .imm_s2_type      (cv32e40p_wrapper_i.core_i.id_stage_i.imm_s2_type),
      .imm_s3_type      (cv32e40p_wrapper_i.core_i.id_stage_i.imm_s3_type),
      .imm_vs_type      (cv32e40p_wrapper_i.core_i.id_stage_i.imm_vs_type),
      .imm_vu_type      (cv32e40p_wrapper_i.core_i.id_stage_i.imm_vu_type),
      .imm_shuffle_type (cv32e40p_wrapper_i.core_i.id_stage_i.imm_shuffle_type),
      .imm_clip_type    (cv32e40p_wrapper_i.core_i.id_stage_i.instr[11:7]),
      .apu_en_i         (cv32e40p_wrapper_i.apu_req),
      .apu_singlecycle_i(cv32e40p_wrapper_i.core_i.ex_stage_i.apu_singlecycle),
      .apu_multicycle_i (cv32e40p_wrapper_i.core_i.ex_stage_i.apu_multicycle),
      .apu_rvalid_i     (cv32e40p_wrapper_i.apu_rvalid)
  );
`endif

  // Instantiate the Core and the optinal FPU
  cv32e40p_wrapper #(
      .PULP_XPULP      (PULP_XPULP),
      .PULP_CLUSTER    (PULP_CLUSTER),
      .FPU             (FPU),
      .PULP_ZFINX      (PULP_ZFINX),
      .NUM_MHPMCOUNTERS(NUM_MHPMCOUNTERS)
  ) cv32e40p_wrapper_i (
      .clk_i (clk_i),
      .rst_ni(rst_ni),

      .pulp_clock_en_i(pulp_clock_en_i),
      .scan_cg_en_i   (scan_cg_en_i),

      .boot_addr_i        (boot_addr_i),
      .mtvec_addr_i       (mtvec_addr_i),
      .dm_halt_addr_i     (dm_halt_addr_i),
      .hart_id_i          (hart_id_i),
      .dm_exception_addr_i(dm_exception_addr_i),

      .instr_req_o   (instr_req_o),
      .instr_gnt_i   (instr_gnt_i),
      .instr_rvalid_i(instr_rvalid_i),
      .instr_addr_o  (instr_addr_o),
      .instr_rdata_i (instr_rdata_i),

      .data_req_o   (data_req_o),
      .data_gnt_i   (data_gnt_i),
      .data_rvalid_i(data_rvalid_i),
      .data_we_o    (data_we_o),
      .data_be_o    (data_be_o),
      .data_addr_o  (data_addr_o),
      .data_wdata_o (data_wdata_o),
      .data_rdata_i (data_rdata_i),

      .irq_i    (irq_i),
      .irq_ack_o(irq_ack_o),
      .irq_id_o (irq_id_o),

      .debug_req_i      (debug_req_i),
      .debug_havereset_o(debug_havereset_o),
      .debug_running_o  (debug_running_o),
      .debug_halted_o   (debug_halted_o),

      .fetch_enable_i(fetch_enable_i),
      .core_sleep_o  (core_sleep_o)
  );

endmodule
