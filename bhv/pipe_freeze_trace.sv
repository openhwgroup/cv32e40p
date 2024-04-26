// Copyright 2024 OpenHW Group and Dolphin Design
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License");
// you may not use this file except in compliance with the License, or,
// at your option, the Apache License version 2.0.
// You may obtain a copy of the License at
//
// https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////////
//                                                                                //
// Contributors: Yoann Pruvost, Dolphin Design <yoann.pruvost@dolphin.fr>         //
//                                                                                //
// Description:  Structures, Functions and Task used to store all information     //
//               coming from the core pipeline at every posedge.                  //
//               Those information will then be processed by RVFI.                //
//                                                                                //
////////////////////////////////////////////////////////////////////////////////////

typedef struct {
  logic is_decoding;
  logic is_illegal;
  logic trigger_match;
  logic data_misaligned;
  logic lsu_data_we_ex;
  logic debug_mode;
  logic [2:0] debug_cause;
  //// INSTR IF Probes ////
  logic instr_req;
  logic instr_grant;
  logic instr_rvalid;

  logic prefetch_req;
  logic pc_set;

  logic instr_valid_id;
  logic [31:0] instr_rdata_id;
  logic is_fetch_failed_id;
  logic instr_req_int;
  logic clear_instr_valid;
  //// IF Probes ////
  logic if_valid;
  logic if_ready;
  logic instr_valid_if;
  logic [31:0] instr_if;
  logic [31:0] pc_if;
  logic instr_pmp_err_if;

  //// ID probes ////
  logic [31:0] pc_id;
  logic id_valid;

  logic id_ready;
  logic [1:0] rf_re_id;
  logic sys_en_id;
  logic sys_mret_insn_id;
  logic jump_in_id;
  logic [31:0] jump_target_id;
  logic is_compressed_id;

  logic ebrk_insn_dec;
  logic ecall_insn_dec;
  logic mret_insn_dec;
  logic mret_dec;

  logic [5:0] csr_cause;

  logic debug_csr_save;
  logic minstret;
  // LSU
  logic lsu_en_id;
  logic lsu_we_id;
  logic [1:0] lsu_size_id;
  // Register reads
  logic [5:0] rs1_addr_id;
  logic [5:0] rs2_addr_id;
  logic [5:0] rs3_addr_id;
  logic [31:0] operand_a_fw_id;
  logic [31:0] operand_b_fw_id;
  logic [31:0] operand_c_fw_id;

  //// EX probes ////

  // Register writes in EX
  logic ex_ready;
  logic ex_valid;

  logic ex_reg_we;
  logic [5:0] ex_reg_addr;
  logic [31:0] ex_reg_wdata;

  logic apu_en_ex;
  logic apu_singlecycle;
  logic apu_multicycle;
  logic wb_contention_lsu;
  logic wb_contention;
  logic regfile_we_lsu;

  logic branch_in_ex;
  logic branch_decision_ex;
  logic dret_in_ex;
  // LSU
  logic lsu_en_ex;
  logic lsu_pmp_err_ex;
  logic lsu_pma_err_atomic_ex;

  logic [31:0] branch_target_ex;

  logic [31:0] data_addr_ex;
  logic [31:0] data_wdata_ex;
  logic lsu_split_q_ex;

  logic mult_ready;
  logic alu_ready;

  //// WB probes ////
  logic [31:0] pc_wb;
  logic wb_ready;
  logic wb_valid;
  logic ebreak_in_wb;
  logic [31:0] instr_rdata_wb;
  logic csr_en_wb;
  logic sys_wfi_insn_wb;
  // Register writes
  logic rf_we_wb;
  logic [5:0] rf_addr_wb;
  logic [31:0] rf_wdata_wb;
  logic rf_alu_we_ex;
  // LSU
  logic [31:0] lsu_rdata_wb;

  logic data_we_ex;
  logic [5:0] data_atop_ex;
  logic [1:0] data_type_ex;
  logic [31:0] alu_operand_c_ex;
  logic [1:0] data_reg_offset_ex;
  logic data_load_event_ex;
  logic [1:0] data_sign_ext_ex;
  logic [31:0] lsu_rdata;
  logic data_req_ex;
  logic [31:0] alu_operand_a_ex;
  logic [31:0] alu_operand_b_ex;
  logic useincr_addr_ex;
  logic data_misaligned_ex;
  logic p_elw_start;
  logic p_elw_finish;
  logic lsu_ready_ex;
  logic lsu_ready_wb;
  logic [3:0] lsu_data_be;
  logic data_req_pmp;
  logic data_gnt_pmp;
  logic data_rvalid;
  logic data_err_pmp;
  logic [31:0] data_addr_pmp;
  logic data_we;
  logic [5:0] data_atop;
  logic [3:0] data_be;
  logic [31:0] data_wdata;
  logic [31:0] data_rdata;

  // APU //
  logic apu_req;
  logic apu_gnt;
  logic apu_rvalid;
  // PC //
  logic [31:0] branch_addr_n;

  // Controller FSM probes
  ctrl_state_e ctrl_fsm_cs;
  ctrl_state_e ctrl_fsm_ns;
  logic pending_single_step;
  logic single_step_allowed;
  logic nmi_pending;
  logic nmi_is_store;
  logic pending_debug;
  logic debug_mode_q;
  logic [3:0] pc_mux;
  logic [2:0] exc_pc_mux;

  // Interrupt Controller probes
  logic [31:0] irq;
  logic irq_wu_ctrl;
  logic [4:0] irq_id_ctrl;

  logic dummy;

  struct {
    //// CSR Probes ////
    csr_num_e addr;
    logic we;
    logic [31:0] wdata_int;

    logic mstatus_we;
    logic mstatus_fs_we;
    logic misa_we;
    logic mtvec_we;
    logic mscratch_we;
    logic mepc_we;
    logic mcause_we;
    logic dcsr_we;

    logic fregs_we;

    logic jvt_we;
    Status_t mstatus_n;
    Status_t mstatus_q;
    FS_t mstatus_fs_n;
    FS_t mstatus_fs_q;

    logic mstatush_we;
    logic [31:0] misa_n;
    logic [31:0] misa_q;

    logic [31:0] mie_n;
    logic [31:0] mie_q;
    logic mie_we;
    logic [23:0] mtvec_n;
    logic [23:0] mtvec_q;
    logic [1:0] mtvec_mode_n;
    logic [1:0] mtvec_mode_q;

    logic mtvt_we;
    logic [31:0] mcountinhibit_n;
    logic [31:0] mcountinhibit_q;
    logic mcountinhibit_we;
    logic [31:0][31:0] mhpmevent_n;
    logic [31:0][31:0] mhpmevent_q;
    logic [31:0] mhpmevent_we;
    logic [31:0] mscratch_n;
    logic [31:0] mscratch_q;
    logic [31:0] mepc_n;
    logic [31:0] mepc_q;

    logic [31:0] mcause_n;
    logic [31:0] mcause_q;
    logic [31:0] mip_n;
    logic [31:0] mip_q;
    logic mip_we;
    logic [31:0] mnxti_n;
    logic [31:0] mnxti_q;
    logic mnxti_we;

    logic mintstatus_we;
    logic [31:0] mintthresh_n;
    logic [31:0] mintthresh_q;
    logic mintthresh_we;
    logic [31:0] mscratchcsw_n;
    logic [31:0] mscratchcsw_q;
    logic mscratchcsw_we;
    logic [31:0] mscratchcswl_n;
    logic [31:0] mscratchcswl_q;
    logic mscratchcswl_we;
    logic [31:0] mclicbase_n;
    logic [31:0] mclicbase_q;
    logic mclicbase_we;
    logic [31:0] tdata1_n;
    logic [31:0] tdata1_q;
    logic tdata1_we;
    logic [31:0] tdata2_n;
    logic [31:0] tdata2_q;
    logic tdata2_we;
    logic [31:0] tinfo_n;
    logic [31:0] tinfo_q;

    Dcsr_t dcsr_n;
    Dcsr_t dcsr_q;

    logic [31:0] dpc_n;
    logic [31:0] dpc_q;
    logic dpc_we;
    logic [31:0] dscratch0_n;
    logic [31:0] dscratch0_q;
    logic dscratch0_we;
    logic [31:0] dscratch1_n;
    logic [31:0] dscratch1_q;
    logic dscratch1_we;
    logic [31:0] mconfigptr_n;
    logic [31:0] mconfigptr_q;
    logic mconfigptr_we;


    // performance counters
    //  cycle,  instret,  hpcounter,  cycleh,  instreth,  hpcounterh
    // mcycle, minstret, mhpcounter, mcycleh, minstreth, mhpcounterh
    logic [31:0][MHPMCOUNTER_WIDTH-1:0] mhpmcounter_q;
    logic [31:0] mhpmcounter_write_lower;
    logic [31:0] mhpmcounter_write_upper;

    logic [31:0] mvendorid;
    logic [31:0] marchid;
    logic [31:0] mhartid;
    logic [31:0] mimpid;

    logic [31:0] mcounteren_n;
    logic [31:0] mcounteren_q;
    logic mcounteren_we;

    logic [7:0] pmpcfg_n[16];
    logic [7:0] pmpcfg_q[16];
    logic [15:0] pmpcfg_we;
    logic [31:0] pmpaddr_n;  // PMP address input shared for all pmpaddr registers
    logic [31:0] pmpaddr_q[16];
    logic [15:0] pmpaddr_we;
    logic [31:0] mseccfg_n;
    logic [31:0] mseccfg_q;
    logic mseccfg_we;
    logic [31:0] mseccfgh_n;
    logic [31:0] mseccfgh_q;
    logic mseccfgh_we;

    logic [31:0] fflags_n;
    logic [31:0] fflags_q;
    logic fflags_we;

    logic [31:0] frm_n;
    logic [31:0] frm_q;
    logic frm_we;

    logic [31:0] fcsr_n;
    logic [31:0] fcsr_q;
    logic fcsr_we;

  } csr;
  struct {
    logic [1:0][31:0] start_q;
    logic [1:0][31:0] end_q;
    logic [1:0][31:0] counter_q;
    logic [1:0][31:0] counter_n;
  } hwloop;
} pipe_trace_t;

pipe_trace_t r_pipe_freeze_trace;

// Compute each CSR write enable
function compute_csr_we();
  r_pipe_freeze_trace.csr.mstatus_we    = 1'b0;
  r_pipe_freeze_trace.csr.mstatus_fs_we = 1'b0;
  r_pipe_freeze_trace.csr.misa_we       = 1'b0;
  r_pipe_freeze_trace.csr.mtvec_we      = 1'b0;
  r_pipe_freeze_trace.csr.mscratch_we   = 1'b0;
  r_pipe_freeze_trace.csr.mepc_we       = 1'b0;
  r_pipe_freeze_trace.csr.mcause_we     = 1'b0;
  r_pipe_freeze_trace.csr.dcsr_we       = 1'b0;
  r_pipe_freeze_trace.csr.fflags_we     = 1'b0;
  r_pipe_freeze_trace.csr.frm_we        = 1'b0;
  r_pipe_freeze_trace.csr.fcsr_we       = 1'b0;
  r_pipe_freeze_trace.csr.mhpmevent_we  = '0;
  r_pipe_freeze_trace.csr.dpc_we        = csr_dpc_we_i;
  if (r_pipe_freeze_trace.csr.we) begin
    case (r_pipe_freeze_trace.csr.addr)
      CSR_MSTATUS: begin
        r_pipe_freeze_trace.csr.mstatus_we    = 1'b1;
        r_pipe_freeze_trace.csr.mstatus_fs_we = 1'b1;
      end
      CSR_MISA:      r_pipe_freeze_trace.csr.misa_we = 1'b1;
      CSR_MTVEC:     r_pipe_freeze_trace.csr.mtvec_we = 1'b1;
      CSR_MSCRATCH:  r_pipe_freeze_trace.csr.mscratch_we = 1'b1;
      CSR_MEPC:      r_pipe_freeze_trace.csr.mepc_we = 1'b1;
      CSR_MCAUSE:    r_pipe_freeze_trace.csr.mcause_we = 1'b1;
      CSR_DCSR:      r_pipe_freeze_trace.csr.dcsr_we = 1'b1;
      CSR_FFLAGS: begin
        r_pipe_freeze_trace.csr.fflags_we = 1'b1;
        r_pipe_freeze_trace.csr.mstatus_fs_we = 1'b1;
      end
      CSR_FRM: begin
        r_pipe_freeze_trace.csr.frm_we = 1'b1;
        r_pipe_freeze_trace.csr.mstatus_fs_we = 1'b1;
      end
      CSR_FCSR: begin
        r_pipe_freeze_trace.csr.fcsr_we = 1'b1;
        r_pipe_freeze_trace.csr.mstatus_fs_we = 1'b1;
      end
      CSR_DPC:       r_pipe_freeze_trace.csr.dpc_we = 1'b1;
      CSR_DSCRATCH0: r_pipe_freeze_trace.csr.dscratch0_we = 1'b1;
      CSR_DSCRATCH1: r_pipe_freeze_trace.csr.dscratch1_we = 1'b1;
    endcase
  end

  if (csr_mhpmevent_we_i) begin
    r_pipe_freeze_trace.csr.mhpmevent_we[r_pipe_freeze_trace.csr.addr[4:0]] = 1'b1;
  end
  // CSR_MCAUSE:   r_pipe_freeze_trace.csr.mcause_we = r_pipe_freeze_trace.csr.mcause_n != r_pipe_freeze_trace.csr.mcause_q; //for debug purpose
endfunction
/*
   * At negedge we buffer all signals form rtl
   * The rest of the tracer will work from those buffered signals
   */

function void if_probes();
  r_pipe_freeze_trace.if_valid           = if_valid_i;
  r_pipe_freeze_trace.if_ready           = if_ready_i;
  r_pipe_freeze_trace.instr_valid_if     = instr_valid_if_i;
  r_pipe_freeze_trace.instr_if           = instr_if_i;
  r_pipe_freeze_trace.pc_if              = pc_if_i;
  r_pipe_freeze_trace.instr_pmp_err_if   = instr_pmp_err_if_i;

  r_pipe_freeze_trace.instr_valid_id     = instr_valid_id_i;
  r_pipe_freeze_trace.instr_rdata_id     = instr_rdata_id_i;
  r_pipe_freeze_trace.is_fetch_failed_id = is_fetch_failed_id_i;
  r_pipe_freeze_trace.instr_req_int      = instr_req_int_i;
  r_pipe_freeze_trace.clear_instr_valid  = clear_instr_valid_i;
endfunction

event e_pipe_monitor_ok;

task monitor_pipeline();
  $display("*****Starting pipeline monitoring*****\n");
  forever begin
    wait(clk_i_d == 1'b0 & rst_ni == 1'b1);

    r_pipe_freeze_trace.instr_req       = instr_req_i;
    r_pipe_freeze_trace.instr_grant     = instr_grant_i;
    r_pipe_freeze_trace.instr_rvalid    = instr_rvalid_i;
    r_pipe_freeze_trace.is_decoding     = is_decoding_i;
    r_pipe_freeze_trace.is_illegal      = is_illegal_i;
    r_pipe_freeze_trace.trigger_match   = trigger_match_i;
    r_pipe_freeze_trace.data_misaligned = data_misaligned_i;
    r_pipe_freeze_trace.lsu_data_we_ex  = lsu_data_we_ex_i;

    r_pipe_freeze_trace.debug_mode      = debug_mode_i;
    r_pipe_freeze_trace.debug_cause     = debug_cause_i;
    r_pipe_freeze_trace.prefetch_req    = prefetch_req_i;
    r_pipe_freeze_trace.pc_set          = pc_set_i;
    //// IF probes ////
    if_probes();
    //// ID probes ////
    r_pipe_freeze_trace.pc_id = pc_id_i;
    r_pipe_freeze_trace.id_valid = id_valid_i;

    r_pipe_freeze_trace.id_ready = id_ready_i;
    r_pipe_freeze_trace.rf_re_id = rf_re_id_i;
    r_pipe_freeze_trace.sys_en_id = sys_en_id_i;
    r_pipe_freeze_trace.sys_mret_insn_id = sys_mret_insn_id_i;
    r_pipe_freeze_trace.jump_in_id = jump_in_id_i;
    r_pipe_freeze_trace.jump_target_id = jump_target_id_i;
    r_pipe_freeze_trace.is_compressed_id = is_compressed_id_i;
    r_pipe_freeze_trace.ebrk_insn_dec = ebrk_insn_dec_i;
    r_pipe_freeze_trace.ecall_insn_dec = ecall_insn_dec_i;
    r_pipe_freeze_trace.mret_insn_dec = mret_insn_dec_i;
    r_pipe_freeze_trace.mret_dec = mret_dec_i;
    r_pipe_freeze_trace.csr_cause = csr_cause_i;
    r_pipe_freeze_trace.debug_csr_save = debug_csr_save_i;
    r_pipe_freeze_trace.minstret = minstret_i;
    // LSU
    r_pipe_freeze_trace.lsu_en_id = lsu_en_id_i;
    r_pipe_freeze_trace.lsu_we_id = lsu_we_id_i;
    r_pipe_freeze_trace.lsu_size_id = lsu_size_id_i;
    // Register reads
    r_pipe_freeze_trace.rs1_addr_id = rs1_addr_id_i;
    r_pipe_freeze_trace.rs2_addr_id = rs2_addr_id_i;
    r_pipe_freeze_trace.rs3_addr_id = rs3_addr_id_i;
    r_pipe_freeze_trace.operand_a_fw_id = operand_a_fw_id_i;
    r_pipe_freeze_trace.operand_b_fw_id = operand_b_fw_id_i;
    r_pipe_freeze_trace.operand_c_fw_id = operand_c_fw_id_i;

    //// EX probes ////

    // Register writes in EX
    r_pipe_freeze_trace.ex_ready = ex_ready_i;
    r_pipe_freeze_trace.ex_valid = ex_valid_i;

    r_pipe_freeze_trace.ex_reg_we = ex_reg_we_i;
    r_pipe_freeze_trace.ex_reg_addr = ex_reg_addr_i;
    r_pipe_freeze_trace.ex_reg_wdata = ex_reg_wdata_i;

    r_pipe_freeze_trace.apu_en_ex = apu_en_ex_i;
    r_pipe_freeze_trace.apu_singlecycle = apu_singlecycle_i;
    r_pipe_freeze_trace.apu_multicycle = apu_multicycle_i;
    r_pipe_freeze_trace.wb_contention_lsu = wb_contention_lsu_i;
    r_pipe_freeze_trace.wb_contention = wb_contention_i;
    r_pipe_freeze_trace.regfile_we_lsu = regfile_we_lsu_i;

    r_pipe_freeze_trace.branch_in_ex = branch_in_ex_i;
    r_pipe_freeze_trace.branch_decision_ex = branch_decision_ex_i;
    r_pipe_freeze_trace.dret_in_ex = dret_in_ex_i;
    // LSU
    r_pipe_freeze_trace.lsu_en_ex = lsu_en_ex_i;
    r_pipe_freeze_trace.lsu_pmp_err_ex = lsu_pmp_err_ex_i;
    r_pipe_freeze_trace.lsu_pma_err_atomic_ex = lsu_pma_err_atomic_ex_i;

    r_pipe_freeze_trace.branch_target_ex = branch_target_ex_i;

    r_pipe_freeze_trace.data_addr_ex = data_addr_ex_i;
    r_pipe_freeze_trace.data_wdata_ex = data_wdata_ex_i;
    r_pipe_freeze_trace.lsu_split_q_ex = lsu_split_q_ex_i;

    r_pipe_freeze_trace.mult_ready = mult_ready_i;
    r_pipe_freeze_trace.alu_ready = alu_ready_i;
    //// WB probes ////
    r_pipe_freeze_trace.pc_wb = pc_wb_i;
    r_pipe_freeze_trace.wb_ready = wb_ready_i;
    r_pipe_freeze_trace.wb_valid = wb_valid_i;
    r_pipe_freeze_trace.ebreak_in_wb = ebreak_in_wb_i;
    r_pipe_freeze_trace.instr_rdata_wb = instr_rdata_wb_i;
    r_pipe_freeze_trace.csr_en_wb = csr_en_wb_i;
    r_pipe_freeze_trace.sys_wfi_insn_wb = sys_wfi_insn_wb_i;
    // Register writes
    r_pipe_freeze_trace.rf_we_wb = rf_we_wb_i;
    r_pipe_freeze_trace.rf_addr_wb = rf_addr_wb_i;
    r_pipe_freeze_trace.rf_wdata_wb = rf_wdata_wb_i;
    r_pipe_freeze_trace.rf_alu_we_ex = regfile_alu_we_ex_i;
    // LSU
    r_pipe_freeze_trace.lsu_rdata_wb = lsu_rdata_wb_i;

    r_pipe_freeze_trace.data_we_ex = data_we_ex_i;
    r_pipe_freeze_trace.data_atop_ex = data_atop_ex_i;
    r_pipe_freeze_trace.data_type_ex = data_type_ex_i;
    r_pipe_freeze_trace.alu_operand_c_ex = alu_operand_c_ex_i;
    r_pipe_freeze_trace.data_reg_offset_ex = data_reg_offset_ex_i;
    r_pipe_freeze_trace.data_load_event_ex = data_load_event_ex_i;
    r_pipe_freeze_trace.data_sign_ext_ex = data_sign_ext_ex_i;
    r_pipe_freeze_trace.lsu_rdata = lsu_rdata_i;
    r_pipe_freeze_trace.data_req_ex = data_req_ex_i;
    r_pipe_freeze_trace.alu_operand_a_ex = alu_operand_a_ex_i;
    r_pipe_freeze_trace.alu_operand_b_ex = alu_operand_b_ex_i;
    r_pipe_freeze_trace.useincr_addr_ex = useincr_addr_ex_i;
    r_pipe_freeze_trace.data_misaligned_ex = data_misaligned_ex_i;
    r_pipe_freeze_trace.p_elw_start = p_elw_start_i;
    r_pipe_freeze_trace.p_elw_finish = p_elw_finish_i;
    r_pipe_freeze_trace.lsu_ready_ex = lsu_ready_ex_i;
    r_pipe_freeze_trace.lsu_ready_wb = lsu_ready_wb_i;
    r_pipe_freeze_trace.lsu_data_be = lsu_data_be_i;

    r_pipe_freeze_trace.data_req_pmp = data_req_pmp_i;
    r_pipe_freeze_trace.data_gnt_pmp = data_gnt_pmp_i;
    r_pipe_freeze_trace.data_rvalid = data_rvalid_i;
    r_pipe_freeze_trace.data_err_pmp = data_err_pmp_i;
    r_pipe_freeze_trace.data_addr_pmp = data_addr_pmp_i;
    r_pipe_freeze_trace.data_we = data_we_i;
    r_pipe_freeze_trace.data_atop = data_atop_i;
    r_pipe_freeze_trace.data_be = data_be_i;
    r_pipe_freeze_trace.data_wdata = data_wdata_i;
    r_pipe_freeze_trace.data_rdata = data_rdata_i;

    //// APU ////
    r_pipe_freeze_trace.apu_req = apu_req_i;
    r_pipe_freeze_trace.apu_gnt = apu_gnt_i;
    r_pipe_freeze_trace.apu_rvalid = apu_rvalid_i;

    // PC //
    r_pipe_freeze_trace.branch_addr_n = branch_addr_n_i;

    // Controller FSM probes
    r_pipe_freeze_trace.ctrl_fsm_cs = ctrl_fsm_cs_i;
    r_pipe_freeze_trace.pc_mux = pc_mux_i;
    r_pipe_freeze_trace.exc_pc_mux = exc_pc_mux_i;

    // CSR
    r_pipe_freeze_trace.csr.addr = csr_addr_i;
    r_pipe_freeze_trace.csr.we = csr_we_i;
    r_pipe_freeze_trace.csr.wdata_int = csr_wdata_int_i;

    r_pipe_freeze_trace.csr.fregs_we = csr_fregs_we_i;

    r_pipe_freeze_trace.csr.jvt_we = csr_jvt_we_i;
    r_pipe_freeze_trace.csr.mstatus_n = csr_mstatus_n_i;
    r_pipe_freeze_trace.csr.mstatus_q = csr_mstatus_q_i;
    r_pipe_freeze_trace.csr.mstatus_fs_n = csr_mstatus_fs_n_i;
    r_pipe_freeze_trace.csr.mstatus_fs_q = csr_mstatus_fs_q_i;

    r_pipe_freeze_trace.csr.mstatush_we = csr_mstatush_we_i;
    r_pipe_freeze_trace.csr.misa_n = csr_misa_n_i;
    r_pipe_freeze_trace.csr.misa_q = csr_misa_q_i;

    r_pipe_freeze_trace.csr.mie_n = csr_mie_n_i;
    r_pipe_freeze_trace.csr.mie_q = csr_mie_q_i;
    r_pipe_freeze_trace.csr.mie_we = csr_mie_we_i;
    r_pipe_freeze_trace.csr.mtvec_n = csr_mtvec_n_i;
    r_pipe_freeze_trace.csr.mtvec_q = csr_mtvec_q_i;
    r_pipe_freeze_trace.csr.mtvec_mode_n = csr_mtvec_mode_n_i;
    r_pipe_freeze_trace.csr.mtvec_mode_q = csr_mtvec_mode_q_i;

    r_pipe_freeze_trace.csr.mtvt_we = csr_mtvt_we_i;
    r_pipe_freeze_trace.csr.mcountinhibit_n = csr_mcountinhibit_n_i;
    r_pipe_freeze_trace.csr.mcountinhibit_q = csr_mcountinhibit_q_i;
    r_pipe_freeze_trace.csr.mcountinhibit_we = csr_mcountinhibit_we_i;
    r_pipe_freeze_trace.csr.mhpmevent_n = csr_mhpmevent_n_i;
    r_pipe_freeze_trace.csr.mhpmevent_q = csr_mhpmevent_q_i;
    r_pipe_freeze_trace.csr.mscratch_n = csr_mscratch_n_i;
    r_pipe_freeze_trace.csr.mscratch_q = csr_mscratch_q_i;
    r_pipe_freeze_trace.csr.mepc_n = csr_mepc_n_i;
    r_pipe_freeze_trace.csr.mepc_q = csr_mepc_q_i;

    r_pipe_freeze_trace.csr.mcause_n[31] = csr_mcause_n_i[5];
    r_pipe_freeze_trace.csr.mcause_n[30:0] = {24'h0, csr_mcause_n_i[4:0]};
    r_pipe_freeze_trace.csr.mcause_q[31] = csr_mcause_q_i[5];
    r_pipe_freeze_trace.csr.mcause_q[30:0] = {24'h0, csr_mcause_q_i[4:0]};

    r_pipe_freeze_trace.csr.mip_n = csr_mip_n_i;
    r_pipe_freeze_trace.csr.mip_q = csr_mip_q_i;
    r_pipe_freeze_trace.csr.mip_we = csr_mip_we_i;
    r_pipe_freeze_trace.csr.mnxti_n = csr_mnxti_n_i;
    r_pipe_freeze_trace.csr.mnxti_q = csr_mnxti_q_i;
    r_pipe_freeze_trace.csr.mnxti_we = csr_mnxti_we_i;

    r_pipe_freeze_trace.csr.mintstatus_we = csr_mintstatus_we_i;
    r_pipe_freeze_trace.csr.mintthresh_n = csr_mintthresh_n_i;
    r_pipe_freeze_trace.csr.mintthresh_q = csr_mintthresh_q_i;
    r_pipe_freeze_trace.csr.mintthresh_we = csr_mintthresh_we_i;
    r_pipe_freeze_trace.csr.mscratchcsw_n = csr_mscratchcsw_n_i;
    r_pipe_freeze_trace.csr.mscratchcsw_q = csr_mscratchcsw_q_i;
    r_pipe_freeze_trace.csr.mscratchcsw_we = csr_mscratchcsw_we_i;
    r_pipe_freeze_trace.csr.mscratchcswl_n = csr_mscratchcswl_n_i;
    r_pipe_freeze_trace.csr.mscratchcswl_q = csr_mscratchcswl_q_i;
    r_pipe_freeze_trace.csr.mscratchcswl_we = csr_mscratchcswl_we_i;
    r_pipe_freeze_trace.csr.mclicbase_n = csr_mclicbase_n_i;
    r_pipe_freeze_trace.csr.mclicbase_q = csr_mclicbase_q_i;
    r_pipe_freeze_trace.csr.mclicbase_we = csr_mclicbase_we_i;
    r_pipe_freeze_trace.csr.tdata1_n = csr_tdata1_n_i;
    r_pipe_freeze_trace.csr.tdata1_q = csr_tdata1_q_i;
    r_pipe_freeze_trace.csr.tdata1_we = csr_tdata1_we_i;
    r_pipe_freeze_trace.csr.tdata2_n = csr_tdata2_n_i;
    r_pipe_freeze_trace.csr.tdata2_q = csr_tdata2_q_i;
    r_pipe_freeze_trace.csr.tdata2_we = csr_tdata2_we_i;
    r_pipe_freeze_trace.csr.tinfo_n = csr_tinfo_n_i;
    r_pipe_freeze_trace.csr.tinfo_q = csr_tinfo_q_i;

    r_pipe_freeze_trace.csr.dcsr_n = csr_dcsr_n_i;
    r_pipe_freeze_trace.csr.dcsr_q = csr_dcsr_q_i;

    r_pipe_freeze_trace.csr.dpc_n = csr_dpc_n_i;
    r_pipe_freeze_trace.csr.dpc_q = csr_dpc_q_i;
    // r_pipe_freeze_trace.csr.dpc_we = csr_dpc_we_i;
    r_pipe_freeze_trace.csr.dscratch0_n = csr_dscratch0_n_i;
    r_pipe_freeze_trace.csr.dscratch0_q = csr_dscratch0_q_i;
    r_pipe_freeze_trace.csr.dscratch0_we = csr_dscratch0_we_i;
    r_pipe_freeze_trace.csr.dscratch1_n = csr_dscratch1_n_i;
    r_pipe_freeze_trace.csr.dscratch1_q = csr_dscratch1_q_i;
    r_pipe_freeze_trace.csr.dscratch1_we = csr_dscratch1_we_i;
    r_pipe_freeze_trace.csr.mconfigptr_n = csr_mconfigptr_n_i;
    r_pipe_freeze_trace.csr.mconfigptr_q = csr_mconfigptr_q_i;
    r_pipe_freeze_trace.csr.mconfigptr_we = csr_mconfigptr_we_i;

    r_pipe_freeze_trace.csr.mhpmcounter_q = csr_mhpmcounter_q_i;
    r_pipe_freeze_trace.csr.mhpmcounter_write_lower = csr_mhpmcounter_write_lower_i;
    r_pipe_freeze_trace.csr.mhpmcounter_write_upper = csr_mhpmcounter_write_upper_i;

    r_pipe_freeze_trace.csr.mvendorid = csr_mvendorid_i;
    r_pipe_freeze_trace.csr.marchid = csr_marchid_i;
    r_pipe_freeze_trace.csr.mhartid = csr_mhartid_i;
    r_pipe_freeze_trace.csr.mimpid = csr_mimpid_i;

    r_pipe_freeze_trace.csr.mcounteren_n = csr_mcounteren_n_i;
    r_pipe_freeze_trace.csr.mcounteren_q = csr_mcounteren_q_i;
    r_pipe_freeze_trace.csr.mcounteren_we = csr_mcounteren_we_i;

    r_pipe_freeze_trace.csr.pmpcfg_n = csr_pmpcfg_n_i;
    r_pipe_freeze_trace.csr.pmpcfg_q = csr_pmpcfg_q_i;
    r_pipe_freeze_trace.csr.pmpcfg_we = csr_pmpcfg_we_i;
    r_pipe_freeze_trace.csr.pmpaddr_n = csr_pmpaddr_n_i;
    r_pipe_freeze_trace.csr.pmpaddr_q = csr_pmpaddr_q_i;
    r_pipe_freeze_trace.csr.pmpaddr_we = csr_pmpaddr_we_i;
    r_pipe_freeze_trace.csr.mseccfg_n = csr_mseccfg_n_i;
    r_pipe_freeze_trace.csr.mseccfg_q = csr_mseccfg_q_i;
    r_pipe_freeze_trace.csr.mseccfg_we = csr_mseccfg_we_i;
    r_pipe_freeze_trace.csr.mseccfgh_n = csr_mseccfgh_n_i;
    r_pipe_freeze_trace.csr.mseccfgh_q = csr_mseccfgh_q_i;
    r_pipe_freeze_trace.csr.mseccfgh_we = csr_mseccfgh_we_i;

    r_pipe_freeze_trace.csr.fflags_n = {27'b0, csr_fcsr_fflags_n_i};
    r_pipe_freeze_trace.csr.fflags_q = {27'b0, csr_fcsr_fflags_q_i};
    r_pipe_freeze_trace.csr.frm_n = {28'b0, csr_fcsr_frm_n_i};
    r_pipe_freeze_trace.csr.frm_q = {28'b0, csr_fcsr_frm_q_i};
    r_pipe_freeze_trace.csr.fcsr_n = {24'b0, csr_fcsr_frm_n_i, csr_fcsr_fflags_n_i};
    r_pipe_freeze_trace.csr.fcsr_q = {24'b0, csr_fcsr_frm_q_i, csr_fcsr_fflags_q_i};

    r_pipe_freeze_trace.hwloop.start_q = hwlp_start_q_i;
    r_pipe_freeze_trace.hwloop.end_q = hwlp_end_q_i;
    r_pipe_freeze_trace.hwloop.counter_q = hwlp_counter_q_i;
    r_pipe_freeze_trace.hwloop.counter_n = hwlp_counter_n_i;

    compute_csr_we();

    //If fcsr_we has triggered, then fflags_we and frm_we should also be triggered
    if (r_pipe_freeze_trace.csr.fcsr_we) begin
      r_pipe_freeze_trace.csr.fflags_we = 1'b1;
      r_pipe_freeze_trace.csr.frm_we    = 1'b1;
    end

    if (csr_fcsr_fflags_we_i) begin
      r_pipe_freeze_trace.csr.fflags_we     = 1'b1;
      r_pipe_freeze_trace.csr.fcsr_we       = 1'b1;
      r_pipe_freeze_trace.csr.mstatus_fs_we = 1'b1;
    end

    ->e_pipe_monitor_ok;

    wait(clk_i_d == 1'b1);
  end
endtask
