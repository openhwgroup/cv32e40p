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

module cv32e40p_wrapper import cv32e40p_apu_core_pkg::*;
#(
  parameter PULP_XPULP          =  1,                   // PULP ISA Extension (incl. custom CSRs and hardware loop, excl. p.elw) !!! HARDWARE LOOP IS NOT OPERATIONAL YET !!!
  parameter PULP_CLUSTER        =  0,                   // PULP Cluster interface (incl. p.elw)
  parameter FPU                 =  0,                   // Floating Point Unit (interfaced via APU interface)
  parameter PULP_ZFINX          =  0,                   // Float-in-General Purpose registers
  parameter NUM_MHPMCOUNTERS    =  1
)
(
  // Clock and Reset
  input  logic        clk_i,
  input  logic        rst_ni,

  input  logic        pulp_clock_en_i,                  // PULP clock enable (only used if PULP_CLUSTER = 1)
  input  logic        scan_cg_en_i,                     // Enable all clock gates for testing

  // Core ID, Cluster ID, debug mode halt address and boot address are considered more or less static
  input  logic [31:0] boot_addr_i,
  input  logic [31:0] mtvec_addr_i,
  input  logic [31:0] dm_halt_addr_i,
  input  logic [31:0] hart_id_i,
  input  logic [31:0] dm_exception_addr_i,

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
  output logic [3:0]  data_be_o,
  output logic [31:0] data_addr_o,
  output logic [31:0] data_wdata_o,
  input  logic [31:0] data_rdata_i,

  // apu-interconnect
  // handshake signals
  output logic                           apu_master_req_o,
  output logic                           apu_master_ready_o,
  input logic                            apu_master_gnt_i,
  // request channel
  output logic [APU_NARGS_CPU-1:0][31:0] apu_master_operands_o,
  output logic [APU_WOP_CPU-1:0]         apu_master_op_o,
  output logic [WAPUTYPE-1:0]            apu_master_type_o,
  output logic [APU_NDSFLAGS_CPU-1:0]    apu_master_flags_o,
  // response channel
  input logic                            apu_master_valid_i,
  input logic [31:0]                     apu_master_result_i,
  input logic [APU_NUSFLAGS_CPU-1:0]     apu_master_flags_i,

  // Interrupt inputs
  input  logic [31:0] irq_i,                    // CLINT interrupts + CLINT extension interrupts
  output logic        irq_ack_o,
  output logic [4:0]  irq_id_o,

  // Debug Interface
  input  logic        debug_req_i,


  // CPU Control Signals
  input  logic        fetch_enable_i,
  output logic        core_sleep_o
);

    bind cv32e40p_core cv32e40p_core_log core_log_i();

`ifdef CV32E40P_APU_TRACE
    bind cv32e40p_core cv32e40p_apu_tracer apu_tracer_i();
`endif

`ifdef CV32E40P_TRACE_EXECUTION
    bind cv32e40p_core cv32e40p_tracer tracer_i(
      .clk_i          ( clk_i                                ), // always-running clock for tracing
      .rst_n          ( rst_ni                               ),

      .hart_id_i      ( hart_id_i                            ),

      .pc             ( id_stage_i.pc_id_i                   ),
      .instr          ( id_stage_i.instr                     ),
      .controller_state_i ( id_stage_i.controller_i.ctrl_fsm_cs ),
      .compressed     ( id_stage_i.is_compressed_i           ),
      .id_valid       ( id_stage_i.id_valid_o                ),
      .is_decoding    ( id_stage_i.is_decoding_o             ),
      .is_illegal     ( id_stage_i.illegal_insn_dec          ),
      .rs1_value      ( id_stage_i.operand_a_fw_id           ),
      .rs2_value      ( id_stage_i.operand_b_fw_id           ),
      .rs3_value      ( id_stage_i.alu_operand_c             ),
      .rs2_value_vec  ( id_stage_i.alu_operand_b             ),

      .rs1_is_fp      ( id_stage_i.regfile_fp_a              ),
      .rs2_is_fp      ( id_stage_i.regfile_fp_b              ),
      .rs3_is_fp      ( id_stage_i.regfile_fp_c              ),
      .rd_is_fp       ( id_stage_i.regfile_fp_d              ),

      .ex_valid       ( ex_valid                             ),
      .ex_reg_addr    ( regfile_alu_waddr_fw                 ),
      .ex_reg_we      ( regfile_alu_we_fw                    ),
      .ex_reg_wdata   ( regfile_alu_wdata_fw                 ),

      .ex_data_addr   ( data_addr_o                          ),
      .ex_data_req    ( data_req_o                           ),
      .ex_data_gnt    ( data_gnt_i                           ),
      .ex_data_we     ( data_we_o                            ),
      .ex_data_wdata  ( data_wdata_o                         ),
      .data_misaligned ( data_misaligned                     ),

      .wb_bypass      ( ex_stage_i.branch_in_ex_i            ),

      .wb_valid       ( wb_valid                             ),
      .wb_reg_addr    ( regfile_waddr_fw_wb_o                ),
      .wb_reg_we      ( regfile_we_wb                        ),
      .wb_reg_wdata   ( regfile_wdata                        ),

      .imm_u_type     ( id_stage_i.imm_u_type                ),
      .imm_uj_type    ( id_stage_i.imm_uj_type               ),
      .imm_i_type     ( id_stage_i.imm_i_type                ),
      .imm_iz_type    ( id_stage_i.imm_iz_type[11:0]         ),
      .imm_z_type     ( id_stage_i.imm_z_type                ),
      .imm_s_type     ( id_stage_i.imm_s_type                ),
      .imm_sb_type    ( id_stage_i.imm_sb_type               ),
      .imm_s2_type    ( id_stage_i.imm_s2_type               ),
      .imm_s3_type    ( id_stage_i.imm_s3_type               ),
      .imm_vs_type    ( id_stage_i.imm_vs_type               ),
      .imm_vu_type    ( id_stage_i.imm_vu_type               ),
      .imm_shuffle_type ( id_stage_i.imm_shuffle_type        ),
      .imm_clip_type  ( id_stage_i.instr_rdata_i[11:7]       )
    );

`endif

    // instantiate the core
    cv32e40p_core
        #(
          .PULP_XPULP            ( PULP_XPULP            ),
          .PULP_CLUSTER          ( PULP_CLUSTER          ),
          .FPU                   ( FPU                   ),
          .PULP_ZFINX            ( PULP_ZFINX            ),
          .NUM_MHPMCOUNTERS      ( NUM_MHPMCOUNTERS      ))
    core_i (.*);


endmodule
