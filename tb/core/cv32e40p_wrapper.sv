// Copyright 2018 Robert Balas <balasr@student.ethz.ch>
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Wrapper for a RI5CY testbench, containing RI5CY, Memory and stdout peripheral
// Contributor: Robert Balas <balasr@student.ethz.ch>

module cv32e40p_wrapper
    #(parameter INSTR_RDATA_WIDTH = 32,
      parameter RAM_ADDR_WIDTH = 20,
      parameter BOOT_ADDR = 'h180,
      parameter PULP_CLUSTER = 0,
      parameter FPU = 0,
      parameter PULP_ZFINX = 0,
      parameter DM_HALTADDRESS = 32'h1A110800)
    (input logic         clk_i,
     input logic         rst_ni,

     input logic         fetch_enable_i,
     output logic        tests_passed_o,
     output logic        tests_failed_o,
     output logic [31:0] exit_value_o,
     output logic        exit_valid_o);

    // signals connecting core to memory
    logic                         instr_req;
    logic                         instr_gnt;
    logic                         instr_rvalid;
    logic [31:0]                  instr_addr;
    logic [INSTR_RDATA_WIDTH-1:0] instr_rdata;

    logic                         data_req;
    logic                         data_gnt;
    logic                         data_rvalid;
    logic [31:0]                  data_addr;
    logic                         data_we;
    logic [3:0]                   data_be;
    logic [31:0]                  data_rdata;
    logic [31:0]                  data_wdata;
    logic [5:0]                   data_atop = 6'b0;

    // signals to debug unit
    logic                         debug_req_i;

    // irq signals
    logic                         irq_ack;
    logic [4:0]                   irq_id_out;
    logic                         irq_software;
    logic                         irq_timer;
    logic                         irq_external;
    logic [15:0]                  irq_fast;

    logic                         core_sleep_o;

    assign debug_req_i = 1'b0;

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
          .PULP_HWLP             ( 0                     ),
          .PULP_CLUSTER          ( PULP_CLUSTER          ),
          .FPU                   ( FPU                   ),
          .PULP_ZFINX            ( PULP_ZFINX            ),
          .NUM_MHPMCOUNTERS      ( 1                     ))
    core_i
        (
         .clk_i                  ( clk_i                 ),
         .rst_ni                 ( rst_ni                ),

         .pulp_clock_en_i        ( 1'b1                  ),
         .scan_cg_en_i           ( 1'b0                  ),

         .boot_addr_i            ( BOOT_ADDR             ),
         .mtvec_addr_i           ( 32'h0                 ),
         .dm_halt_addr_i         ( DM_HALTADDRESS        ),
         .hart_id_i              ( 32'h0                 ),

         .instr_addr_o           ( instr_addr            ),
         .instr_req_o            ( instr_req             ),
         .instr_rdata_i          ( instr_rdata           ),
         .instr_gnt_i            ( instr_gnt             ),
         .instr_rvalid_i         ( instr_rvalid          ),

         .data_addr_o            ( data_addr             ),
         .data_wdata_o           ( data_wdata            ),
         .data_we_o              ( data_we               ),
         .data_req_o             ( data_req              ),
         .data_be_o              ( data_be               ),
         .data_rdata_i           ( data_rdata            ),
         .data_gnt_i             ( data_gnt              ),
         .data_rvalid_i          ( data_rvalid           ),

         .apu_master_req_o       (                       ),
         .apu_master_ready_o     (                       ),
         .apu_master_gnt_i       (1'b0                   ),
         .apu_master_operands_o  (                       ),
         .apu_master_op_o        (                       ),
         .apu_master_type_o      (                       ),
         .apu_master_flags_o     (                       ),
         .apu_master_valid_i     (1'b0                   ),
         .apu_master_result_i    (32'b0                  ),
         .apu_master_flags_i     (5'b0                   ),

         .irq_i                  ( {irq_fast, 4'b0, irq_external, 3'b0, irq_timer, 3'b0, irq_software, 3'b0 } ),
         .irq_ack_o              ( irq_ack               ),
         .irq_id_o               ( irq_id_out            ),

         .debug_req_i            ( debug_req_i           ),

         .fetch_enable_i         ( fetch_enable_i        ),
         .core_sleep_o           ( core_sleep_o           ));

    // this handles read to RAM and memory mapped pseudo peripherals
    mm_ram
        #(.RAM_ADDR_WIDTH (RAM_ADDR_WIDTH),
          .INSTR_RDATA_WIDTH (INSTR_RDATA_WIDTH))
    ram_i
        (.clk_i          ( clk_i                          ),
         .rst_ni         ( rst_ni                         ),

         .instr_req_i    ( instr_req                      ),
         .instr_addr_i   ( instr_addr[RAM_ADDR_WIDTH-1:0] ),
         .instr_rdata_o  ( instr_rdata                    ),
         .instr_rvalid_o ( instr_rvalid                   ),
         .instr_gnt_o    ( instr_gnt                      ),

         .data_req_i     ( data_req                       ),
         .data_addr_i    ( data_addr                      ),
         .data_we_i      ( data_we                        ),
         .data_be_i      ( data_be                        ),
         .data_wdata_i   ( data_wdata                     ),
         .data_rdata_o   ( data_rdata                     ),
         .data_rvalid_o  ( data_rvalid                    ),
         .data_gnt_o     ( data_gnt                       ),
         .data_atop_i    ( data_atop                      ),

         .irq_id_i       ( irq_id_out                     ),
         .irq_ack_i      ( irq_ack                        ),

         // output irq lines to Core
         .irq_software_o ( irq_software                   ),
         .irq_timer_o    ( irq_timer                      ),
         .irq_external_o ( irq_external                   ),
         .irq_fast_o     ( irq_fast                       ),

         .pc_core_id_i   ( core_i.pc_id                   ),

         .tests_passed_o ( tests_passed_o                 ),
         .tests_failed_o ( tests_failed_o                 ),
         .exit_valid_o   ( exit_valid_o                   ),
         .exit_value_o   ( exit_value_o                   ));

endmodule // cv32e40p_wrapper
