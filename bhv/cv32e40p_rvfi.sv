// Copyright 2024 Dolphin Design
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
// Contributors: Davide Schiavone, OpenHW Group <davide@openhwgroup.org>          //
//               Halfdan Bechmann, Silicon Labs <halfdan.bechmann@silabs.com>     //
//               Yoann Pruvost, Dolphin Design <yoann.pruvost@dolphin.fr>         //
//                                                                                //
// Description:  CV32E40P RVFI interface                                          //
//                                                                                //
////////////////////////////////////////////////////////////////////////////////////

`include "cv32e40p_rvfi_pkg.sv"

module cv32e40p_rvfi
  import cv32e40p_pkg::*;
  import cv32e40p_rvfi_pkg::*;
#(
    parameter FPU   = 0,
    parameter ZFINX = 0,
    parameter NUM_MHPMCOUNTERS = 1
) (
    input logic clk_i,
    input logic rst_ni,

    input logic is_decoding_i,
    input logic is_illegal_i,
    input logic trigger_match_i,
    input logic data_misaligned_i,
    input logic lsu_data_we_ex_i,

    input logic       debug_mode_i,
    input logic [2:0] debug_cause_i,
    //// INSTR IF Probes ////
    input logic       instr_req_i,
    input logic       instr_grant_i,
    input logic       instr_rvalid_i,

    input logic        prefetch_req_i,
    input logic        pc_set_i,
    //// IF Probes ////
    input logic        if_valid_i,
    input logic        if_ready_i,
    input logic        instr_valid_if_i,
    input logic [31:0] instr_if_i,
    input logic [31:0] pc_if_i,
    input logic        instr_pmp_err_if_i,

    input logic        instr_valid_id_i,
    input logic [31:0] instr_rdata_id_i,
    input logic        is_fetch_failed_id_i,
    input logic        instr_req_int_i,
    input logic        clear_instr_valid_i,
    //// ID probes ////
    input logic [31:0] pc_id_i,
    input logic        id_valid_i,

    input logic        id_ready_i,
    input logic [ 1:0] rf_re_id_i,
    input logic        sys_en_id_i,
    input logic        sys_mret_insn_id_i,
    input logic        jump_in_id_i,
    input logic [31:0] jump_target_id_i,
    input logic        is_compressed_id_i,

    input logic ebrk_insn_dec_i,
    input logic ecall_insn_dec_i,

    input logic mret_insn_dec_i,
    input logic mret_dec_i,

    input logic [5:0] csr_cause_i,

    input logic              debug_csr_save_i,
    // HWLOOP regs
    input logic [ 1:0][31:0] hwlp_start_q_i,
    input logic [ 1:0][31:0] hwlp_end_q_i,
    input logic [ 1:0][31:0] hwlp_counter_q_i,
    input logic [ 1:0][31:0] hwlp_counter_n_i,
    input logic              minstret_i,
    // LSU
    input logic              lsu_en_id_i,
    input logic              lsu_we_id_i,
    input logic [ 1:0]       lsu_size_id_i,
    // Register reads
    input logic [ 5:0]       rs1_addr_id_i,
    input logic [ 5:0]       rs2_addr_id_i,
    input logic [ 5:0]       rs3_addr_id_i,
    input logic [31:0]       operand_a_fw_id_i,
    input logic [31:0]       operand_b_fw_id_i,
    input logic [31:0]       operand_c_fw_id_i,

    //// EX probes ////

    // Register writes in EX
    input logic ex_ready_i,
    input logic ex_valid_i,

    input logic        ex_reg_we_i,
    input logic [ 5:0] ex_reg_addr_i,
    input logic [31:0] ex_reg_wdata_i,

    input logic apu_en_ex_i,
    input logic apu_singlecycle_i,
    input logic apu_multicycle_i,
    input logic wb_contention_lsu_i,
    input logic wb_contention_i,
    input logic regfile_we_lsu_i,

    input logic branch_in_ex_i,
    input logic branch_decision_ex_i,
    input logic dret_in_ex_i,
    // LSU
    input logic lsu_en_ex_i,
    input logic lsu_pmp_err_ex_i,
    input logic lsu_pma_err_atomic_ex_i,

    input logic [31:0] branch_target_ex_i,

    input logic [31:0] data_addr_ex_i,
    input logic [31:0] data_wdata_ex_i,
    input logic        lsu_split_q_ex_i,

    input logic mult_ready_i,
    input logic alu_ready_i,

    //// WB probes ////
    input logic [31:0] pc_wb_i,
    input logic        wb_ready_i,
    input logic        wb_valid_i,
    input logic        ebreak_in_wb_i,
    input logic [31:0] instr_rdata_wb_i,
    input logic        csr_en_wb_i,
    input logic        sys_wfi_insn_wb_i,
    // Register writes
    input logic        rf_we_wb_i,
    input logic [ 5:0] rf_addr_wb_i,
    input logic [31:0] rf_wdata_wb_i,
    input logic        regfile_alu_we_ex_i,
    // LSU
    input logic [31:0] lsu_rdata_wb_i,

    input logic        data_we_ex_i,
    input logic [ 5:0] data_atop_ex_i,
    input logic [ 1:0] data_type_ex_i,
    input logic [31:0] alu_operand_c_ex_i,
    input logic [ 1:0] data_reg_offset_ex_i,
    input logic        data_load_event_ex_i,
    input logic [ 1:0] data_sign_ext_ex_i,
    input logic [31:0] lsu_rdata_i,
    input logic        data_req_ex_i,
    input logic [31:0] alu_operand_a_ex_i,
    input logic [31:0] alu_operand_b_ex_i,
    input logic        useincr_addr_ex_i,
    input logic        data_misaligned_ex_i,
    input logic        p_elw_start_i,
    input logic        p_elw_finish_i,
    input logic        lsu_ready_ex_i,
    input logic        lsu_ready_wb_i,

    input logic [3:0] lsu_data_be_i,

    input logic        data_req_pmp_i,
    input logic        data_gnt_pmp_i,
    input logic        data_rvalid_i,
    input logic        data_err_pmp_i,
    input logic [31:0] data_addr_pmp_i,
    input logic        data_we_i,
    input logic [ 5:0] data_atop_i,
    input logic [ 3:0] data_be_i,
    input logic [31:0] data_wdata_i,
    input logic [31:0] data_rdata_i,

    //// APU ////
    input logic apu_req_i,
    input logic apu_gnt_i,
    input logic apu_rvalid_i,


    // PC //
    input logic [31:0] branch_addr_n_i,

    // Controller FSM probes
    input ctrl_state_e       ctrl_fsm_cs_i,
    input ctrl_state_e       ctrl_fsm_ns_i,
    input logic              pending_single_step_i,
    input logic              single_step_allowed_i,
    input logic              pending_debug_i,
    input logic              debug_mode_q_i,
    input logic        [3:0] pc_mux_i,
    input logic        [2:0] exc_pc_mux_i,

    // Interrupt Controller probes
    input logic [31:0] irq_i,
    input logic        irq_wu_ctrl_i,
    input logic [ 4:0] irq_id_ctrl_i,

    //// CSR Probes ////
    input csr_num_e        csr_addr_i,
    input logic            csr_we_i,
    input logic     [31:0] csr_wdata_int_i,

    input logic    csr_fregs_we_i,
    input logic    csr_jvt_we_i,
    input Status_t csr_mstatus_n_i,
    input Status_t csr_mstatus_q_i,
    input FS_t     csr_mstatus_fs_n_i,
    input FS_t     csr_mstatus_fs_q_i,

    input logic        csr_mstatush_we_i,
    input logic [31:0] csr_misa_n_i,
    input logic [31:0] csr_misa_q_i,

    input logic [31:0] csr_mie_n_i,
    input logic [31:0] csr_mie_q_i,
    input logic        csr_mie_we_i,
    input logic [23:0] csr_mtvec_n_i,
    input logic [23:0] csr_mtvec_q_i,
    input logic [ 1:0] csr_mtvec_mode_n_i,
    input logic [ 1:0] csr_mtvec_mode_q_i,

    input logic              csr_mtvt_we_i,
    input logic [31:0]       csr_mcountinhibit_n_i,
    input logic [31:0]       csr_mcountinhibit_q_i,
    input logic              csr_mcountinhibit_we_i,
    input logic [31:0][31:0] csr_mhpmevent_n_i,
    input logic [31:0][31:0] csr_mhpmevent_q_i,
    input logic [31:0]       csr_mhpmevent_we_i,
    input logic [31:0]       csr_mscratch_n_i,
    input logic [31:0]       csr_mscratch_q_i,
    input logic [31:0]       csr_mepc_n_i,
    input logic [31:0]       csr_mepc_q_i,

    input logic [ 5:0] csr_mcause_n_i,
    input logic [ 5:0] csr_mcause_q_i,
    input logic [31:0] csr_mip_n_i,
    input logic [31:0] csr_mip_q_i,
    input logic        csr_mip_we_i,
    input logic [31:0] csr_mnxti_n_i,
    input logic [31:0] csr_mnxti_q_i,
    input logic        csr_mnxti_we_i,

    input logic        csr_mintstatus_we_i,
    input logic [31:0] csr_mintthresh_n_i,
    input logic [31:0] csr_mintthresh_q_i,
    input logic        csr_mintthresh_we_i,
    input logic [31:0] csr_mscratchcsw_n_i,
    input logic [31:0] csr_mscratchcsw_q_i,
    input logic        csr_mscratchcsw_we_i,
    input logic [31:0] csr_mscratchcswl_n_i,
    input logic [31:0] csr_mscratchcswl_q_i,
    input logic        csr_mscratchcswl_we_i,
    input logic [31:0] csr_mclicbase_n_i,
    input logic [31:0] csr_mclicbase_q_i,
    input logic        csr_mclicbase_we_i,
    input logic [31:0] csr_tdata1_n_i,
    input logic [31:0] csr_tdata1_q_i,
    input logic        csr_tdata1_we_i,
    input logic [31:0] csr_tdata2_n_i,
    input logic [31:0] csr_tdata2_q_i,
    input logic        csr_tdata2_we_i,
    input logic [31:0] csr_tinfo_n_i,
    input logic [31:0] csr_tinfo_q_i,

    input Dcsr_t csr_dcsr_n_i,
    input Dcsr_t csr_dcsr_q_i,

    input logic [31:0] csr_dpc_n_i,
    input logic [31:0] csr_dpc_q_i,
    input logic        csr_dpc_we_i,
    input logic [31:0] csr_dscratch0_n_i,
    input logic [31:0] csr_dscratch0_q_i,
    input logic        csr_dscratch0_we_i,
    input logic [31:0] csr_dscratch1_n_i,
    input logic [31:0] csr_dscratch1_q_i,
    input logic        csr_dscratch1_we_i,
    input logic [31:0] csr_mconfigptr_n_i,
    input logic [31:0] csr_mconfigptr_q_i,
    input logic        csr_mconfigptr_we_i,

    // performance counters
    //  cycle,  instret,  hpcounter,  cycleh,  instreth,  hpcounterh
    // mcycle, minstret, mhpcounter, mcycleh, minstreth, mhpcounterh
    input logic [63:0][MHPMCOUNTER_WIDTH-1:0] csr_mhpmcounter_q_i,
    input logic [31:0]                        csr_mhpmcounter_write_lower_i,
    input logic [31:0]                        csr_mhpmcounter_write_upper_i,

    input logic [31:0] csr_mvendorid_i,
    input logic [31:0] csr_marchid_i,
    input logic [31:0] csr_mhartid_i,
    input logic [31:0] csr_mimpid_i,

    input logic [31:0] csr_mcounteren_n_i,
    input logic [31:0] csr_mcounteren_q_i,
    input logic        csr_mcounteren_we_i,

    input logic [ 7:0] csr_pmpcfg_n_i   [16],
    input logic [ 7:0] csr_pmpcfg_q_i   [16],
    input logic [15:0] csr_pmpcfg_we_i,
    input logic [31:0] csr_pmpaddr_n_i,  // PMP address input shared for all pmpaddr registers
    input logic [31:0] csr_pmpaddr_q_i  [16],
    input logic [15:0] csr_pmpaddr_we_i,
    input logic [31:0] csr_mseccfg_n_i,
    input logic [31:0] csr_mseccfg_q_i,
    input logic        csr_mseccfg_we_i,
    input logic [31:0] csr_mseccfgh_n_i,
    input logic [31:0] csr_mseccfgh_q_i,
    input logic        csr_mseccfgh_we_i,

    input logic [4:0] csr_fcsr_fflags_n_i,
    input logic [4:0] csr_fcsr_fflags_q_i,
    input logic       csr_fcsr_fflags_we_i,
    input logic [2:0] csr_fcsr_frm_n_i,
    input logic [2:0] csr_fcsr_frm_q_i,

    // RISC-V Formal Interface
    // Does not comply with the coding standards of _i/_o suffixes, but follow,
    // the convention of RISC-V Formal Interface Specification.
    output logic       [ 0:0] rvfi_valid,
    output logic       [63:0] rvfi_order,
    output integer            rvfi_start_cycle,
    output time               rvfi_start_time,
    output integer            rvfi_stop_cycle,
    output time               rvfi_stop_time,
    output logic       [31:0] rvfi_insn,
    output rvfi_trap_t        rvfi_trap,
    output logic       [ 0:0] rvfi_halt,
    output rvfi_intr_t        rvfi_intr,
    output logic       [ 1:0] rvfi_mode,
    output logic       [ 1:0] rvfi_ixl,
    output logic       [ 1:0] rvfi_nmip,

    output logic [2:0] rvfi_dbg,
    output logic [0:0] rvfi_dbg_mode,

    output rvfi_wu_t       rvfi_wu,
    output logic     [0:0] rvfi_sleep,

    output logic [ 4:0] rvfi_rd_addr    [1:0],
    output logic [31:0] rvfi_rd_wdata   [1:0],
    output logic        rvfi_frd_wvalid [1:0],
    output logic [ 4:0] rvfi_frd_addr   [1:0],
    output logic [31:0] rvfi_frd_wdata  [1:0],
    output logic        rvfi_2_rd,
    output logic [ 4:0] rvfi_rs1_addr,
    output logic [ 4:0] rvfi_rs2_addr,
    output logic [ 4:0] rvfi_rs3_addr,
    output logic [31:0] rvfi_rs1_rdata,
    output logic [31:0] rvfi_rs2_rdata,
    output logic [31:0] rvfi_rs3_rdata,
    output logic [ 4:0] rvfi_frs1_addr,
    output logic [ 4:0] rvfi_frs2_addr,
    output logic [ 4:0] rvfi_frs3_addr,
    output logic        rvfi_frs1_rvalid,
    output logic        rvfi_frs2_rvalid,
    output logic        rvfi_frs3_rvalid,
    output logic [31:0] rvfi_frs1_rdata,
    output logic [31:0] rvfi_frs2_rdata,
    output logic [31:0] rvfi_frs3_rdata,

    output logic [31:0] rvfi_pc_rdata,
    output logic [31:0] rvfi_pc_wdata,

    output logic [31:0] rvfi_mem_addr,
    output logic [31:0] rvfi_mem_rmask,
    output logic [31:0] rvfi_mem_wmask,
    output logic [31:0] rvfi_mem_rdata,
    output logic [31:0] rvfi_mem_wdata,

    // CSRs
    output logic [31:0]       rvfi_csr_fflags_rmask,
    output logic [31:0]       rvfi_csr_fflags_wmask,
    output logic [31:0]       rvfi_csr_fflags_rdata,
    output logic [31:0]       rvfi_csr_fflags_wdata,
    output logic [31:0]       rvfi_csr_frm_rmask,
    output logic [31:0]       rvfi_csr_frm_wmask,
    output logic [31:0]       rvfi_csr_frm_rdata,
    output logic [31:0]       rvfi_csr_frm_wdata,
    output logic [31:0]       rvfi_csr_fcsr_rmask,
    output logic [31:0]       rvfi_csr_fcsr_wmask,
    output logic [31:0]       rvfi_csr_fcsr_rdata,
    output logic [31:0]       rvfi_csr_fcsr_wdata,
    output logic [31:0]       rvfi_csr_jvt_rmask,
    output logic [31:0]       rvfi_csr_jvt_wmask,
    output logic [31:0]       rvfi_csr_jvt_rdata,
    output logic [31:0]       rvfi_csr_jvt_wdata,
    output logic [31:0]       rvfi_csr_mstatus_rmask,
    output logic [31:0]       rvfi_csr_mstatus_wmask,
    output logic [31:0]       rvfi_csr_mstatus_rdata,
    output logic [31:0]       rvfi_csr_mstatus_wdata,
    output logic [31:0]       rvfi_csr_mstatush_rmask,
    output logic [31:0]       rvfi_csr_mstatush_wmask,
    output logic [31:0]       rvfi_csr_mstatush_rdata,
    output logic [31:0]       rvfi_csr_mstatush_wdata,
    output logic [31:0]       rvfi_csr_misa_rmask,
    output logic [31:0]       rvfi_csr_misa_wmask,
    output logic [31:0]       rvfi_csr_misa_rdata,
    output logic [31:0]       rvfi_csr_misa_wdata,
    output logic [31:0]       rvfi_csr_mie_rmask,
    output logic [31:0]       rvfi_csr_mie_wmask,
    output logic [31:0]       rvfi_csr_mie_rdata,
    output logic [31:0]       rvfi_csr_mie_wdata,
    output logic [31:0]       rvfi_csr_mtvec_rmask,
    output logic [31:0]       rvfi_csr_mtvec_wmask,
    output logic [31:0]       rvfi_csr_mtvec_rdata,
    output logic [31:0]       rvfi_csr_mtvec_wdata,
    output logic [31:0]       rvfi_csr_mtvt_rmask,
    output logic [31:0]       rvfi_csr_mtvt_wmask,
    output logic [31:0]       rvfi_csr_mtvt_rdata,
    output logic [31:0]       rvfi_csr_mtvt_wdata,
    output logic [31:0]       rvfi_csr_mcountinhibit_rmask,
    output logic [31:0]       rvfi_csr_mcountinhibit_wmask,
    output logic [31:0]       rvfi_csr_mcountinhibit_rdata,
    output logic [31:0]       rvfi_csr_mcountinhibit_wdata,
    output logic [31:0][31:0] rvfi_csr_mhpmevent_rmask,  // 3-31 implemented
    output logic [31:0][31:0] rvfi_csr_mhpmevent_wmask,
    output logic [31:0][31:0] rvfi_csr_mhpmevent_rdata,
    output logic [31:0][31:0] rvfi_csr_mhpmevent_wdata,
    output logic [31:0]       rvfi_csr_mscratch_rmask,
    output logic [31:0]       rvfi_csr_mscratch_wmask,
    output logic [31:0]       rvfi_csr_mscratch_rdata,
    output logic [31:0]       rvfi_csr_mscratch_wdata,
    output logic [31:0]       rvfi_csr_mepc_rmask,
    output logic [31:0]       rvfi_csr_mepc_wmask,
    output logic [31:0]       rvfi_csr_mepc_rdata,
    output logic [31:0]       rvfi_csr_mepc_wdata,
    output logic [31:0]       rvfi_csr_mcause_rmask,
    output logic [31:0]       rvfi_csr_mcause_wmask,
    output logic [31:0]       rvfi_csr_mcause_rdata,
    output logic [31:0]       rvfi_csr_mcause_wdata,
    output logic [31:0]       rvfi_csr_mtval_rmask,
    output logic [31:0]       rvfi_csr_mtval_wmask,
    output logic [31:0]       rvfi_csr_mtval_rdata,
    output logic [31:0]       rvfi_csr_mtval_wdata,
    output logic [31:0]       rvfi_csr_mip_rmask,
    output logic [31:0]       rvfi_csr_mip_wmask,
    output logic [31:0]       rvfi_csr_mip_rdata,
    output logic [31:0]       rvfi_csr_mip_wdata,
    output logic [31:0]       rvfi_csr_mnxti_rmask,
    output logic [31:0]       rvfi_csr_mnxti_wmask,
    output logic [31:0]       rvfi_csr_mnxti_rdata,
    output logic [31:0]       rvfi_csr_mnxti_wdata,
    output logic [31:0]       rvfi_csr_mintstatus_rmask,
    output logic [31:0]       rvfi_csr_mintstatus_wmask,
    output logic [31:0]       rvfi_csr_mintstatus_rdata,
    output logic [31:0]       rvfi_csr_mintstatus_wdata,
    output logic [31:0]       rvfi_csr_mintthresh_rmask,
    output logic [31:0]       rvfi_csr_mintthresh_wmask,
    output logic [31:0]       rvfi_csr_mintthresh_rdata,
    output logic [31:0]       rvfi_csr_mintthresh_wdata,
    output logic [31:0]       rvfi_csr_mscratchcsw_rmask,
    output logic [31:0]       rvfi_csr_mscratchcsw_wmask,
    output logic [31:0]       rvfi_csr_mscratchcsw_rdata,
    output logic [31:0]       rvfi_csr_mscratchcsw_wdata,
    output logic [31:0]       rvfi_csr_mscratchcswl_rmask,
    output logic [31:0]       rvfi_csr_mscratchcswl_wmask,
    output logic [31:0]       rvfi_csr_mscratchcswl_rdata,
    output logic [31:0]       rvfi_csr_mscratchcswl_wdata,
    output logic [31:0]       rvfi_csr_mclicbase_rmask,
    output logic [31:0]       rvfi_csr_mclicbase_wmask,
    output logic [31:0]       rvfi_csr_mclicbase_rdata,
    output logic [31:0]       rvfi_csr_mclicbase_wdata,
    output logic [31:0]       rvfi_csr_tselect_rmask,
    output logic [31:0]       rvfi_csr_tselect_wmask,
    output logic [31:0]       rvfi_csr_tselect_rdata,
    output logic [31:0]       rvfi_csr_tselect_wdata,
    output logic [ 3:0][31:0] rvfi_csr_tdata_rmask,  // 1-3 implemented
    output logic [ 3:0][31:0] rvfi_csr_tdata_wmask,
    output logic [ 3:0][31:0] rvfi_csr_tdata_rdata,
    output logic [ 3:0][31:0] rvfi_csr_tdata_wdata,
    output logic [31:0]       rvfi_csr_tinfo_rmask,
    output logic [31:0]       rvfi_csr_tinfo_wmask,
    output logic [31:0]       rvfi_csr_tinfo_rdata,
    output logic [31:0]       rvfi_csr_tinfo_wdata,
    output logic [31:0]       rvfi_csr_mcontext_rmask,
    output logic [31:0]       rvfi_csr_mcontext_wmask,
    output logic [31:0]       rvfi_csr_mcontext_rdata,
    output logic [31:0]       rvfi_csr_mcontext_wdata,
    output logic [31:0]       rvfi_csr_scontext_rmask,
    output logic [31:0]       rvfi_csr_scontext_wmask,
    output logic [31:0]       rvfi_csr_scontext_rdata,
    output logic [31:0]       rvfi_csr_scontext_wdata,
    output logic [31:0]       rvfi_csr_dcsr_rmask,
    output logic [31:0]       rvfi_csr_dcsr_wmask,
    output logic [31:0]       rvfi_csr_dcsr_rdata,
    output logic [31:0]       rvfi_csr_dcsr_wdata,
    output logic [31:0]       rvfi_csr_dpc_rmask,
    output logic [31:0]       rvfi_csr_dpc_wmask,
    output logic [31:0]       rvfi_csr_dpc_rdata,
    output logic [31:0]       rvfi_csr_dpc_wdata,
    output logic [ 1:0][31:0] rvfi_csr_dscratch_rmask,  // 0-1 implemented
    output logic [ 1:0][31:0] rvfi_csr_dscratch_wmask,
    output logic [ 1:0][31:0] rvfi_csr_dscratch_rdata,
    output logic [ 1:0][31:0] rvfi_csr_dscratch_wdata,
    output logic [31:0]       rvfi_csr_mcycle_rmask,
    output logic [31:0]       rvfi_csr_mcycle_wmask,
    output logic [31:0]       rvfi_csr_mcycle_rdata,
    output logic [31:0]       rvfi_csr_mcycle_wdata,
    output logic [31:0]       rvfi_csr_minstret_rmask,
    output logic [31:0]       rvfi_csr_minstret_wmask,
    output logic [31:0]       rvfi_csr_minstret_rdata,
    output logic [31:0]       rvfi_csr_minstret_wdata,
    output logic [31:0][31:0] rvfi_csr_mhpmcounter_rmask,  // 3-31 implemented
    output logic [31:0][31:0] rvfi_csr_mhpmcounter_wmask,
    output logic [31:0][31:0] rvfi_csr_mhpmcounter_rdata,
    output logic [31:0][31:0] rvfi_csr_mhpmcounter_wdata,
    output logic [31:0]       rvfi_csr_mcycleh_rmask,
    output logic [31:0]       rvfi_csr_mcycleh_wmask,
    output logic [31:0]       rvfi_csr_mcycleh_rdata,
    output logic [31:0]       rvfi_csr_mcycleh_wdata,
    output logic [31:0]       rvfi_csr_minstreth_rmask,
    output logic [31:0]       rvfi_csr_minstreth_wmask,
    output logic [31:0]       rvfi_csr_minstreth_rdata,
    output logic [31:0]       rvfi_csr_minstreth_wdata,
    output logic [31:0][31:0] rvfi_csr_mhpmcounterh_rmask,  // 3-31 implemented
    output logic [31:0][31:0] rvfi_csr_mhpmcounterh_wmask,
    output logic [31:0][31:0] rvfi_csr_mhpmcounterh_rdata,
    output logic [31:0][31:0] rvfi_csr_mhpmcounterh_wdata,
    output logic [31:0]       rvfi_csr_cycle_rmask,
    output logic [31:0]       rvfi_csr_cycle_wmask,
    output logic [31:0]       rvfi_csr_cycle_rdata,
    output logic [31:0]       rvfi_csr_cycle_wdata,
    output logic [31:0]       rvfi_csr_instret_rmask,
    output logic [31:0]       rvfi_csr_instret_wmask,
    output logic [31:0]       rvfi_csr_instret_rdata,
    output logic [31:0]       rvfi_csr_instret_wdata,
    output logic [31:0][31:0] rvfi_csr_hpmcounter_rmask,  // 3-31 implemented
    output logic [31:0][31:0] rvfi_csr_hpmcounter_wmask,
    output logic [31:0][31:0] rvfi_csr_hpmcounter_rdata,
    output logic [31:0][31:0] rvfi_csr_hpmcounter_wdata,
    output logic [31:0]       rvfi_csr_cycleh_rmask,
    output logic [31:0]       rvfi_csr_cycleh_wmask,
    output logic [31:0]       rvfi_csr_cycleh_rdata,
    output logic [31:0]       rvfi_csr_cycleh_wdata,
    output logic [31:0]       rvfi_csr_instreth_rmask,
    output logic [31:0]       rvfi_csr_instreth_wmask,
    output logic [31:0]       rvfi_csr_instreth_rdata,
    output logic [31:0]       rvfi_csr_instreth_wdata,
    output logic [31:0][31:0] rvfi_csr_hpmcounterh_rmask,  // 3-31 implemented
    output logic [31:0][31:0] rvfi_csr_hpmcounterh_wmask,
    output logic [31:0][31:0] rvfi_csr_hpmcounterh_rdata,
    output logic [31:0][31:0] rvfi_csr_hpmcounterh_wdata,
    output logic [31:0]       rvfi_csr_mvendorid_rmask,
    output logic [31:0]       rvfi_csr_mvendorid_wmask,
    output logic [31:0]       rvfi_csr_mvendorid_rdata,
    output logic [31:0]       rvfi_csr_mvendorid_wdata,
    output logic [31:0]       rvfi_csr_marchid_rmask,
    output logic [31:0]       rvfi_csr_marchid_wmask,
    output logic [31:0]       rvfi_csr_marchid_rdata,
    output logic [31:0]       rvfi_csr_marchid_wdata,
    output logic [31:0]       rvfi_csr_mimpid_rmask,
    output logic [31:0]       rvfi_csr_mimpid_wmask,
    output logic [31:0]       rvfi_csr_mimpid_rdata,
    output logic [31:0]       rvfi_csr_mimpid_wdata,
    output logic [31:0]       rvfi_csr_mhartid_rmask,
    output logic [31:0]       rvfi_csr_mhartid_wmask,
    output logic [31:0]       rvfi_csr_mhartid_rdata,
    output logic [31:0]       rvfi_csr_mhartid_wdata,

    output logic [31:0] rvfi_csr_mcounteren_rmask,
    output logic [31:0] rvfi_csr_mcounteren_wmask,
    output logic [31:0] rvfi_csr_mcounteren_rdata,
    output logic [31:0] rvfi_csr_mcounteren_wdata,

    output logic [ 3:0][31:0] rvfi_csr_pmpcfg_rmask,
    output logic [ 3:0][31:0] rvfi_csr_pmpcfg_wmask,
    output logic [ 3:0][31:0] rvfi_csr_pmpcfg_rdata,
    output logic [ 3:0][31:0] rvfi_csr_pmpcfg_wdata,
    output logic [15:0][31:0] rvfi_csr_pmpaddr_rmask,
    output logic [15:0][31:0] rvfi_csr_pmpaddr_wmask,
    output logic [15:0][31:0] rvfi_csr_pmpaddr_rdata,
    output logic [15:0][31:0] rvfi_csr_pmpaddr_wdata,
    output logic [31:0]       rvfi_csr_mseccfg_rmask,
    output logic [31:0]       rvfi_csr_mseccfg_wmask,
    output logic [31:0]       rvfi_csr_mseccfg_rdata,
    output logic [31:0]       rvfi_csr_mseccfg_wdata,
    output logic [31:0]       rvfi_csr_mseccfgh_rmask,
    output logic [31:0]       rvfi_csr_mseccfgh_wmask,
    output logic [31:0]       rvfi_csr_mseccfgh_rdata,
    output logic [31:0]       rvfi_csr_mseccfgh_wdata,

    output logic [31:0] rvfi_csr_mconfigptr_rmask,
    output logic [31:0] rvfi_csr_mconfigptr_wmask,
    output logic [31:0] rvfi_csr_mconfigptr_rdata,
    output logic [31:0] rvfi_csr_mconfigptr_wdata,

    output logic [31:0] rvfi_csr_lpstart0_rmask,
    output logic [31:0] rvfi_csr_lpstart0_wmask,
    output logic [31:0] rvfi_csr_lpstart0_rdata,
    output logic [31:0] rvfi_csr_lpstart0_wdata,
    output logic [31:0] rvfi_csr_lpend0_rmask,
    output logic [31:0] rvfi_csr_lpend0_wmask,
    output logic [31:0] rvfi_csr_lpend0_rdata,
    output logic [31:0] rvfi_csr_lpend0_wdata,
    output logic [31:0] rvfi_csr_lpcount0_rmask,
    output logic [31:0] rvfi_csr_lpcount0_wmask,
    output logic [31:0] rvfi_csr_lpcount0_rdata,
    output logic [31:0] rvfi_csr_lpcount0_wdata,
    output logic [31:0] rvfi_csr_lpstart1_rmask,
    output logic [31:0] rvfi_csr_lpstart1_wmask,
    output logic [31:0] rvfi_csr_lpstart1_rdata,
    output logic [31:0] rvfi_csr_lpstart1_wdata,
    output logic [31:0] rvfi_csr_lpend1_rmask,
    output logic [31:0] rvfi_csr_lpend1_wmask,
    output logic [31:0] rvfi_csr_lpend1_rdata,
    output logic [31:0] rvfi_csr_lpend1_wdata,
    output logic [31:0] rvfi_csr_lpcount1_rmask,
    output logic [31:0] rvfi_csr_lpcount1_wmask,
    output logic [31:0] rvfi_csr_lpcount1_rdata,
    output logic [31:0] rvfi_csr_lpcount1_wdata
);


  bit clk_i_d;
  assign #0.01 clk_i_d = clk_i;

  integer cycles;
  // cycle counter
  always_ff @(posedge clk_i_d, negedge rst_ni) begin
    if (rst_ni == 1'b0) cycles <= 0;
    else cycles <= cycles + 1;
  end

  logic pc_mux_debug;
  logic pc_mux_dret;
  logic pc_mux_exception;
  logic pc_mux_debug_exception;
  logic pc_mux_interrupt;
  logic pc_mux_nmi;

  localparam logic [31:0] MSTATUS_WRITE_MASK = 32'h0000_6088;
  localparam logic [31:0] MCOUNTINHIBIT_WRITE_MASK = {{(29-NUM_MHPMCOUNTERS){1'b0}}, {(NUM_MHPMCOUNTERS){1'b1}}, 3'b101};
  localparam NUM_HPM_EVENTS = 16;
  localparam logic [31:0] MHPMEVENT_WRITE_MASK = {{(31-NUM_HPM_EVENTS){1'b0}}, {(NUM_HPM_EVENTS){1'b1}}};

  `include "pipe_freeze_trace.sv"

  `include "insn_trace.sv"

insn_trace_t trace_if, trace_id, trace_ex, trace_ex_next, trace_wb;
  insn_trace_t tmp_trace_wb;
  insn_trace_t rvfi_trace_q[$], wb_bypass_trace_q[$];

  bit           clear_trace_ex;  //  = 1'b1;
  bit           clear_trace_wb;

  logic         csr_is_irq;
  logic         is_dbg_taken;
  logic   [2:0] saved_debug_cause;
  integer       next_send;

  event         e_empty_queue;
  function void empty_fifo();
    integer i, trace_q_size;
    trace_q_size = wb_bypass_trace_q.size();
    if (trace_q_size > 50) begin
      $fatal("Reorder queue too long\n");
    end
    if (trace_q_size != 0) begin
      for (i = 0; i < trace_q_size; i++) begin
        insn_trace_t new_rvfi_trace;
        new_rvfi_trace = new();
        new_rvfi_trace.copy_full(wb_bypass_trace_q.pop_front());
        if (next_send == new_rvfi_trace.m_order) begin
          new_rvfi_trace.m_csr.mstatus_fs_rdata = r_pipe_freeze_trace.csr.mstatus_fs_n;
          rvfi_trace_q.push_back(new_rvfi_trace);
          next_send = next_send + 1;
          ->e_empty_queue;
        end else begin
          wb_bypass_trace_q.push_back(new_rvfi_trace);
        end
      end
    end
    trace_q_size = wb_bypass_trace_q.size();  //Re-calculate here for accurate status
  endfunction
  /*
   * Function used to alocate a new insn and send it to the rvfi driver
   */
  event e_add_to_bypass;
  function void send_rvfi(insn_trace_t m_wb_insn);
    insn_trace_t new_rvfi_trace;
    new_rvfi_trace = new();
    new_rvfi_trace.copy_full(m_wb_insn);
    if (next_send == new_rvfi_trace.m_order) begin
      rvfi_trace_q.push_back(new_rvfi_trace);
      next_send = next_send + 1;
    end else begin
      wb_bypass_trace_q.push_back(new_rvfi_trace);
      ->e_add_to_bypass;
    end
    empty_fifo();
  endfunction

  /*
   * Assing rvfi signals once the instruction is completed
   */
  `define SET_RVFI_CSR_FROM_INSN(CSR_NAME) \
    rvfi_csr_``CSR_NAME``_rdata  = new_rvfi_trace.m_csr.``CSR_NAME``_rdata; \
    rvfi_csr_``CSR_NAME``_rmask  = new_rvfi_trace.m_csr.``CSR_NAME``_rmask; \
    rvfi_csr_``CSR_NAME``_wdata  = new_rvfi_trace.m_csr.``CSR_NAME``_wdata; \
    rvfi_csr_``CSR_NAME``_wmask  = new_rvfi_trace.m_csr.``CSR_NAME``_wmask;

  logic [31:0] s_fflags_mirror;
  logic [31:0] s_frm_mirror;
  logic [31:0] s_fcsr_mirror;

  function void set_rvfi();
    insn_trace_t new_rvfi_trace;
    new_rvfi_trace = rvfi_trace_q.pop_front();

    if (new_rvfi_trace.m_is_apu) begin
      if (new_rvfi_trace.m_csr.fflags_we) begin
        s_fflags_mirror = new_rvfi_trace.m_csr.fflags_wdata;
      end else begin
        s_fflags_mirror = new_rvfi_trace.m_csr.fflags_rdata;
      end
      if (new_rvfi_trace.m_csr.frm_we) begin
        s_frm_mirror = new_rvfi_trace.m_csr.frm_wdata;
      end else begin
        s_frm_mirror = new_rvfi_trace.m_csr.frm_rdata;
      end
      if (new_rvfi_trace.m_csr.fcsr_we) begin
        s_fcsr_mirror = new_rvfi_trace.m_csr.fcsr_wdata;
      end else begin
        s_fcsr_mirror = new_rvfi_trace.m_csr.fcsr_rdata;
      end

    end else begin
      new_rvfi_trace.m_csr.fflags_rdata = s_fflags_mirror;
      new_rvfi_trace.m_csr.frm_rdata = s_frm_mirror;
      new_rvfi_trace.m_csr.fcsr_rdata = s_fcsr_mirror;

      if (new_rvfi_trace.m_fflags_we_non_apu) begin
        s_fflags_mirror = new_rvfi_trace.m_csr.fflags_wdata;
        s_fcsr_mirror = new_rvfi_trace.m_csr.fcsr_wdata;
        new_rvfi_trace.m_csr.fflags_wmask = 32'hFFFF_FFFF;
        new_rvfi_trace.m_csr.fcsr_wmask = 32'hFFFF_FFFF;
      end
      if (new_rvfi_trace.m_frm_we_non_apu) begin
        s_frm_mirror = new_rvfi_trace.m_csr.frm_wdata;
        s_fcsr_mirror = new_rvfi_trace.m_csr.fcsr_wdata;
        new_rvfi_trace.m_csr.frm_wmask = 32'hFFFF_FFFF;
        new_rvfi_trace.m_csr.fcsr_wmask = 32'hFFFF_FFFF;
      end
      if (new_rvfi_trace.m_fcsr_we_non_apu) begin
        s_fcsr_mirror = new_rvfi_trace.m_csr.fcsr_wdata;
        s_fflags_mirror = new_rvfi_trace.m_csr.fflags_wdata;
        s_frm_mirror = new_rvfi_trace.m_csr.frm_wdata;
        new_rvfi_trace.m_csr.fcsr_wmask = 32'hFFFF_FFFF;
        new_rvfi_trace.m_csr.fflags_wmask = 32'hFFFF_FFFF;
        new_rvfi_trace.m_csr.frm_wmask = 32'hFFFF_FFFF;
      end
    end

    rvfi_order       = new_rvfi_trace.m_order;
    rvfi_start_cycle = new_rvfi_trace.m_start_cycle;
    rvfi_start_time  = new_rvfi_trace.m_start_time;
    rvfi_stop_cycle = new_rvfi_trace.m_stop_cycle;
    rvfi_stop_time  = new_rvfi_trace.m_stop_time;
    rvfi_pc_rdata    = new_rvfi_trace.m_pc_rdata;
    rvfi_insn        = new_rvfi_trace.m_insn;

    rvfi_rs1_addr    = '0;
    rvfi_rs1_rdata   = '0;
    rvfi_rs2_addr    = '0;
    rvfi_rs2_rdata   = '0;
    rvfi_rs3_addr    = '0;
    rvfi_rs3_rdata   = '0;
    rvfi_frs1_rvalid = '0;
    rvfi_frs1_addr   = '0;
    rvfi_frs1_rdata  = '0;
    rvfi_frs2_rvalid = '0;
    rvfi_frs2_addr   = '0;
    rvfi_frs2_rdata  = '0;
    rvfi_frs3_rvalid = '0;
    rvfi_frs3_addr   = '0;
    rvfi_frs3_rdata  = '0;

    if (new_rvfi_trace.m_rs1_addr[5]) begin
      rvfi_frs1_rvalid = 1'b1;
      rvfi_frs1_addr   = new_rvfi_trace.m_rs1_addr[4:0];
      rvfi_frs1_rdata  = new_rvfi_trace.m_rs1_rdata;
    end else begin
      rvfi_rs1_addr  = new_rvfi_trace.m_rs1_addr[4:0];
      rvfi_rs1_rdata = new_rvfi_trace.m_rs1_rdata;
    end

    if (new_rvfi_trace.m_rs2_addr[5]) begin
      rvfi_frs2_rvalid = 1'b1;
      rvfi_frs2_addr   = new_rvfi_trace.m_rs2_addr[4:0];
      rvfi_frs2_rdata  = new_rvfi_trace.m_rs2_rdata;
    end else begin
      rvfi_rs2_addr  = new_rvfi_trace.m_rs2_addr[4:0];
      rvfi_rs2_rdata = new_rvfi_trace.m_rs2_rdata;
    end

    if (new_rvfi_trace.m_rs3_addr[5]) begin
      rvfi_frs3_rvalid = 1'b1;
      rvfi_frs3_addr   = new_rvfi_trace.m_rs3_addr[4:0];
      rvfi_frs3_rdata  = new_rvfi_trace.m_rs3_rdata;
    end else begin
      rvfi_rs3_addr  = new_rvfi_trace.m_rs3_addr[4:0];
      rvfi_rs3_rdata = new_rvfi_trace.m_rs3_rdata;
    end

    rvfi_frd_wvalid[0] = '0;
    rvfi_frd_addr[0]   = '0;
    rvfi_frd_wdata[0]  = '0;

    rvfi_frd_wvalid[1] = '0;
    rvfi_frd_addr[1]   = '0;
    rvfi_frd_wdata[1]  = '0;

    rvfi_2_rd = new_rvfi_trace.m_2_rd_insn;
    if (new_rvfi_trace.m_rd_addr[0][5] == 1'b0) begin
      rvfi_rd_addr[0]  = new_rvfi_trace.m_rd_addr[0][4:0];
      rvfi_rd_wdata[0] = new_rvfi_trace.m_rd_wdata[0];

    end else begin
      rvfi_rd_addr[0] = '0;
      rvfi_rd_wdata[0] = '0;

      rvfi_frd_wvalid[0] = 1'b1;
      rvfi_frd_addr[0] = new_rvfi_trace.m_rd_addr[0][4:0];
      rvfi_frd_wdata[0] = new_rvfi_trace.m_rd_wdata[0];
    end

    if (new_rvfi_trace.m_2_rd_insn) begin
      if (new_rvfi_trace.m_rd_addr[1][5] == 1'b0) begin
        rvfi_rd_addr[1]  = new_rvfi_trace.m_rd_addr[1][4:0];
        rvfi_rd_wdata[1] = new_rvfi_trace.m_rd_wdata[1];
      end else begin
        rvfi_frd_wvalid[1] = 1'b1;
        rvfi_frd_addr[1] = new_rvfi_trace.m_rd_addr[1][4:0];
        rvfi_frd_wdata[1] = new_rvfi_trace.m_rd_wdata[1];

        rvfi_rd_addr[1] = '0;
        rvfi_rd_wdata[1] = '0;
      end
    end else begin
      rvfi_rd_addr[1]  = '0;
      rvfi_rd_wdata[1] = '0;
    end

    rvfi_mem_addr  = new_rvfi_trace.m_mem.addr;
    rvfi_mem_rmask = new_rvfi_trace.m_mem.rmask;
    rvfi_mem_wmask = new_rvfi_trace.m_mem.wmask;
    rvfi_mem_rdata = new_rvfi_trace.m_mem.rdata;
    rvfi_mem_wdata = new_rvfi_trace.m_mem.wdata;

    rvfi_dbg       = new_rvfi_trace.m_dbg_cause;
    rvfi_dbg_mode  = new_rvfi_trace.m_dbg_taken;

    rvfi_trap.trap = 0;
    if (new_rvfi_trace.m_is_illegal) begin
      rvfi_trap.trap = 1'b1;
    end

    if (new_rvfi_trace.m_trap) begin
      rvfi_trap.trap = 1'b1;
    end

    //CSR
    rvfi_csr_mstatus_rmask = new_rvfi_trace.m_csr.mstatus_rmask | new_rvfi_trace.m_csr.mstatus_fs_rmask;
    rvfi_csr_mstatus_wmask = new_rvfi_trace.m_csr.mstatus_wmask & MSTATUS_WRITE_MASK;
    rvfi_csr_mstatus_wmask[31] = new_rvfi_trace.m_csr.mstatus_fs_wmask[31];
    rvfi_csr_mstatus_wmask[14:13] = new_rvfi_trace.m_csr.mstatus_fs_wmask[14:13];

    if (FPU == 1 && ZFINX == 0) begin
      rvfi_csr_mstatus_rdata[31] = (new_rvfi_trace.m_csr.mstatus_fs_rdata == FS_DIRTY) ? 1'b1 : 1'b0;
    end else begin
      rvfi_csr_mstatus_rdata[31] = '0;
    end
    rvfi_csr_mstatus_rdata[30:18] = '0;
    rvfi_csr_mstatus_rdata[17] = new_rvfi_trace.m_csr.mstatus_rdata.mprv;
    rvfi_csr_mstatus_rdata[16:15] = '0;
    if (FPU == 1 && ZFINX == 0) begin
      rvfi_csr_mstatus_rdata[14:13] = new_rvfi_trace.m_csr.mstatus_fs_rdata;
    end else begin
      rvfi_csr_mstatus_rdata[14:13] = '0;
    end
    rvfi_csr_mstatus_rdata[12:11] = new_rvfi_trace.m_csr.mstatus_rdata.mpp;
    rvfi_csr_mstatus_rdata[10:8] = '0;
    rvfi_csr_mstatus_rdata[7] = new_rvfi_trace.m_csr.mstatus_rdata.mpie;
    rvfi_csr_mstatus_rdata[6:5] = '0;
    rvfi_csr_mstatus_rdata[4] = new_rvfi_trace.m_csr.mstatus_rdata.upie;
    rvfi_csr_mstatus_rdata[3] = new_rvfi_trace.m_csr.mstatus_rdata.mie;
    rvfi_csr_mstatus_rdata[2:1] = '0;
    rvfi_csr_mstatus_rdata[0] = new_rvfi_trace.m_csr.mstatus_rdata.uie;

    if (FPU == 1 && ZFINX == 0) begin
      rvfi_csr_mstatus_wdata[31] = (new_rvfi_trace.m_csr.mstatus_fs_wdata == FS_DIRTY) ? 1'b1 : 1'b0;
    end else begin
      rvfi_csr_mstatus_wdata[31] = '0;
    end
    rvfi_csr_mstatus_wdata[30:18] = '0;
    // MPRV is not implemented in the target configuration, writes to it are ignored
    rvfi_csr_mstatus_wdata[17] = 1'b0;  //new_rvfi_trace.m_csr.mstatus_wdata.mprv;
    rvfi_csr_mstatus_wdata[16:15] = '0;
    if (FPU == 1 && ZFINX == 0) begin
      rvfi_csr_mstatus_wdata[14:13] = new_rvfi_trace.m_csr.mstatus_fs_wdata;
    end else begin
      rvfi_csr_mstatus_wdata[14:13] = '0;
    end
    rvfi_csr_mstatus_wdata[12:11] = new_rvfi_trace.m_csr.mstatus_wdata.mpp;
    rvfi_csr_mstatus_wdata[10:8] = '0;
    rvfi_csr_mstatus_wdata[7] = new_rvfi_trace.m_csr.mstatus_wdata.mpie;
    rvfi_csr_mstatus_wdata[6:5] = '0;
    // UPIE is not implemented in the target configuration, writes to it are ignored
    rvfi_csr_mstatus_wdata[4] = 1'b0;  //new_rvfi_trace.m_csr.mstatus_wdata.upie;
    rvfi_csr_mstatus_wdata[3] = new_rvfi_trace.m_csr.mstatus_wdata.mie;
    rvfi_csr_mstatus_wdata[2:1] = '0;
    // UIE is not implemented in the target configuration, writes to it are ignored
    rvfi_csr_mstatus_wdata[0] = 1'b0;  //new_rvfi_trace.m_csr.mstatus_wdata.uie;

    `SET_RVFI_CSR_FROM_INSN(misa)
    `SET_RVFI_CSR_FROM_INSN(mie)
    `SET_RVFI_CSR_FROM_INSN(mtvec)

    rvfi_csr_mcountinhibit_rdata = new_rvfi_trace.m_csr.mcountinhibit_rdata;
    rvfi_csr_mcountinhibit_rmask = new_rvfi_trace.m_csr.mcountinhibit_rmask;
    rvfi_csr_mcountinhibit_wdata = new_rvfi_trace.m_csr.mcountinhibit_wdata;
    rvfi_csr_mcountinhibit_wmask = new_rvfi_trace.m_csr.mcountinhibit_wmask & MCOUNTINHIBIT_WRITE_MASK;

    `SET_RVFI_CSR_FROM_INSN(mscratch)
    `SET_RVFI_CSR_FROM_INSN(mepc)
    `SET_RVFI_CSR_FROM_INSN(mcause)
    `SET_RVFI_CSR_FROM_INSN(mcycle)
    `SET_RVFI_CSR_FROM_INSN(minstret)
    `SET_RVFI_CSR_FROM_INSN(minstreth)

    // `SET_RVFI_CSR_FROM_INSN(cycle)
    // `SET_RVFI_CSR_FROM_INSN(instret)
    rvfi_csr_instret_rdata = new_rvfi_trace.m_csr.minstret_rdata;
    rvfi_csr_instret_rmask = new_rvfi_trace.m_csr.minstret_rmask;
    rvfi_csr_instret_wdata = new_rvfi_trace.m_csr.minstret_wdata;
    rvfi_csr_instret_wmask = new_rvfi_trace.m_csr.minstret_wmask;

    for(int idx=3; idx<32; idx++) begin
    rvfi_csr_mhpmcounter_rmask[idx] = new_rvfi_trace.m_csr.mhpmcounter_rmask[idx][31:0];
    rvfi_csr_mhpmcounter_wmask[idx] = new_rvfi_trace.m_csr.mhpmcounter_wmask[idx][31:0];
    rvfi_csr_mhpmcounter_rdata[idx] = new_rvfi_trace.m_csr.mhpmcounter_rdata[idx][31:0];
    rvfi_csr_mhpmcounter_wdata[idx] = new_rvfi_trace.m_csr.mhpmcounter_wdata[idx][31:0];

    rvfi_csr_mhpmcounterh_rmask[idx] = new_rvfi_trace.m_csr.mhpmcounter_rmask[idx][63:32];
    rvfi_csr_mhpmcounterh_wmask[idx] = new_rvfi_trace.m_csr.mhpmcounter_wmask[idx][63:32];
    rvfi_csr_mhpmcounterh_rdata[idx] = new_rvfi_trace.m_csr.mhpmcounter_rdata[idx][63:32];
    rvfi_csr_mhpmcounterh_wdata[idx] = new_rvfi_trace.m_csr.mhpmcounter_wdata[idx][63:32];

    rvfi_csr_mhpmevent_rmask[idx] = new_rvfi_trace.m_csr.mhpmevent_rmask[idx];
    rvfi_csr_mhpmevent_wmask[idx] = new_rvfi_trace.m_csr.mhpmevent_wmask[idx] & MHPMEVENT_WRITE_MASK;
    rvfi_csr_mhpmevent_rdata[idx] = new_rvfi_trace.m_csr.mhpmevent_rdata[idx];
    rvfi_csr_mhpmevent_wdata[idx] = new_rvfi_trace.m_csr.mhpmevent_wdata[idx];
    end
    // `SET_RVFI_CSR_FROM_INSN(instreth)
    rvfi_csr_instreth_rdata = new_rvfi_trace.m_csr.minstreth_rdata;
    rvfi_csr_instreth_rmask = new_rvfi_trace.m_csr.minstreth_rmask;
    rvfi_csr_instreth_wdata = new_rvfi_trace.m_csr.minstreth_wdata;
    rvfi_csr_instreth_wmask = new_rvfi_trace.m_csr.minstreth_wmask;

    `SET_RVFI_CSR_FROM_INSN(mip)

    rvfi_csr_tdata_rdata[0] = 'Z;
    rvfi_csr_tdata_rmask[0] = '0;  // Does not exist
    rvfi_csr_tdata_wdata[0] = 'Z;  // Does not exist
    rvfi_csr_tdata_wmask[0] = '0;

    rvfi_csr_tdata_rdata[1] = new_rvfi_trace.m_csr.tdata1_rdata;
    rvfi_csr_tdata_rmask[1] = new_rvfi_trace.m_csr.tdata1_rmask;  //'1
    rvfi_csr_tdata_wdata[1] = new_rvfi_trace.m_csr.tdata1_wdata;
    rvfi_csr_tdata_wmask[1] = new_rvfi_trace.m_csr.tdata1_wmask;

    rvfi_csr_tdata_rdata[2] = new_rvfi_trace.m_csr.tdata2_rdata;
    rvfi_csr_tdata_rmask[2] = new_rvfi_trace.m_csr.tdata2_rmask;  //'1
    rvfi_csr_tdata_wdata[2] = new_rvfi_trace.m_csr.tdata2_wdata;
    rvfi_csr_tdata_wmask[2] = new_rvfi_trace.m_csr.tdata2_wmask;

    rvfi_csr_tdata_rmask[3] = '1;

    `SET_RVFI_CSR_FROM_INSN(tinfo)
    `SET_RVFI_CSR_FROM_INSN(dcsr)
    `SET_RVFI_CSR_FROM_INSN(dpc)
    rvfi_csr_dscratch_rmask[0] = new_rvfi_trace.m_csr.dscratch0_rmask;
    rvfi_csr_dscratch_wmask[0] = new_rvfi_trace.m_csr.dscratch0_wmask;
    rvfi_csr_dscratch_rdata[0] = new_rvfi_trace.m_csr.dscratch0_rdata;
    rvfi_csr_dscratch_wdata[0] = new_rvfi_trace.m_csr.dscratch0_wdata;
    rvfi_csr_dscratch_rmask[1] = new_rvfi_trace.m_csr.dscratch1_rmask;
    rvfi_csr_dscratch_wmask[1] = new_rvfi_trace.m_csr.dscratch1_wmask;
    rvfi_csr_dscratch_rdata[1] = new_rvfi_trace.m_csr.dscratch1_rdata;
    rvfi_csr_dscratch_wdata[1] = new_rvfi_trace.m_csr.dscratch1_wdata;
    // `SET_RVFI_CSR_FROM_INSN(dscratch0)
    `SET_RVFI_CSR_FROM_INSN(mvendorid)
    `SET_RVFI_CSR_FROM_INSN(marchid)

    `SET_RVFI_CSR_FROM_INSN(fflags)
    `SET_RVFI_CSR_FROM_INSN(frm)
    `SET_RVFI_CSR_FROM_INSN(fcsr)

    `SET_RVFI_CSR_FROM_INSN(lpstart0)
    `SET_RVFI_CSR_FROM_INSN(lpend0)
    `SET_RVFI_CSR_FROM_INSN(lpcount0)
    `SET_RVFI_CSR_FROM_INSN(lpstart1)
    `SET_RVFI_CSR_FROM_INSN(lpend1)
    `SET_RVFI_CSR_FROM_INSN(lpcount1)

  endfunction  // set_rvfi

  function void sample_perf_counter_to_id(int idx);
    trace_id.m_csr.mhpmcounter_rdata[idx][31:0] = r_pipe_freeze_trace.csr.mhpmcounter_q[idx][31:0];
    trace_id.m_csr.mhpmcounter_rmask[idx][31:0] = '1;
  endfunction

  function void perf_counter_to_id(int idx);
    if(!trace_id.m_csr.mhpmcounter_we[idx][0]) begin
      trace_id.m_csr.mhpmcounter_wdata[idx][31:0] = r_pipe_freeze_trace.csr.wdata_int;
    end
    if(r_pipe_freeze_trace.csr.mhpmcounter_write_lower[idx]) begin
        trace_id.m_csr.mhpmcounter_we[idx][0]    = r_pipe_freeze_trace.csr.mhpmcounter_write_lower[idx];
        trace_id.m_csr.mhpmcounter_wdata[idx][31:0] = r_pipe_freeze_trace.csr.wdata_int;
        trace_id.m_csr.mhpmcounter_wmask[idx][31:0] = r_pipe_freeze_trace.csr.mhpmcounter_write_lower[idx] ? '1 : '0;
    end
    sample_perf_counter_to_id(idx);
  endfunction

  function void sample_perf_event_to_trace(int idx, insn_trace_t m_trace);
    m_trace.m_csr.mhpmevent_rdata[idx] = r_pipe_freeze_trace.csr.mhpmevent_q[idx];
    m_trace.m_csr.mhpmevent_rmask[idx] = '1;
  endfunction

  function void perf_event_to_trace(int idx, insn_trace_t m_trace);
    if(!m_trace.m_csr.mhpmevent_we[idx]) begin
      m_trace.m_csr.mhpmevent_wdata[idx] = r_pipe_freeze_trace.csr.wdata_int;
    end
    if(r_pipe_freeze_trace.csr.mhpmevent_we[idx]) begin
        m_trace.m_csr.mhpmevent_we[idx]    = r_pipe_freeze_trace.csr.mhpmevent_we[idx];
        m_trace.m_csr.mhpmevent_wdata[idx] = r_pipe_freeze_trace.csr.wdata_int;
        m_trace.m_csr.mhpmevent_wmask[idx] = r_pipe_freeze_trace.csr.mhpmevent_we[idx] ? '1 : '0;
    end
    sample_perf_event_to_trace(idx, m_trace);
  endfunction

  function void sample_minstret_to_trace(insn_trace_t m_trace);
    m_trace.m_csr.minstret_rdata = r_pipe_freeze_trace.csr.mhpmcounter_q[2][31:0];
    m_trace.m_csr.minstret_rmask = '1;
  endfunction

  function void minstret_to_trace(insn_trace_t m_trace);
    if(!m_trace.m_csr.minstret_we) begin
      m_trace.m_csr.minstret_wdata = r_pipe_freeze_trace.csr.wdata_int;
    end
    if(r_pipe_freeze_trace.csr.mhpmcounter_write_lower[2]) begin
        m_trace.m_csr.minstret_we    = r_pipe_freeze_trace.csr.mhpmcounter_write_lower[2];
        m_trace.m_csr.minstret_wdata = r_pipe_freeze_trace.csr.wdata_int;
        m_trace.m_csr.minstret_wmask = r_pipe_freeze_trace.csr.mhpmcounter_write_lower[2] ? '1 : '0;
    end
    sample_minstret_to_trace(m_trace);
  endfunction

  function void sample_perf_counter_h_to_id(int idx);
    trace_id.m_csr.mhpmcounter_rdata[idx][63:32] = r_pipe_freeze_trace.csr.mhpmcounter_q[idx][63:0];
    trace_id.m_csr.mhpmcounter_rmask[idx][63:32] = '1;
  endfunction

  function void perf_counter_h_to_id(int idx);
    if(!trace_id.m_csr.mhpmcounter_we[idx][1]) begin
      trace_id.m_csr.mhpmcounter_wdata[idx][63:32] = r_pipe_freeze_trace.csr.wdata_int;
    end
    if(r_pipe_freeze_trace.csr.mhpmcounter_write_lower[idx]) begin
        trace_id.m_csr.mhpmcounter_we[idx][1]    = r_pipe_freeze_trace.csr.mhpmcounter_write_lower[idx];
        trace_id.m_csr.mhpmcounter_wdata[idx][63:32] = r_pipe_freeze_trace.csr.wdata_int;
        trace_id.m_csr.mhpmcounter_wmask[idx][63:32] = r_pipe_freeze_trace.csr.mhpmcounter_write_lower[idx] ? '1 : '0;
    end
    sample_perf_counter_h_to_id(idx);
  endfunction

  function void sample_minstreth_to_trace(insn_trace_t m_trace);
    m_trace.m_csr.minstreth_rdata = r_pipe_freeze_trace.csr.mhpmcounter_q[2][63:32];
    m_trace.m_csr.minstreth_rmask = '1;
  endfunction

  function void sample_mcycle_to_trace(insn_trace_t m_trace);
    m_trace.m_csr.mcycle_we    = r_pipe_freeze_trace.csr.mhpmcounter_write_lower[0];
    m_trace.m_csr.mcycle_rdata = r_pipe_freeze_trace.csr.mhpmcounter_q[0][31:0];
    m_trace.m_csr.mcycle_rmask = '1;
    m_trace.m_csr.mcycle_wdata = r_pipe_freeze_trace.csr.mhpmcounter_q[31:0];
    m_trace.m_csr.mcycle_wmask = r_pipe_freeze_trace.csr.mhpmcounter_write_lower[0] ? '1 : '0;
  endfunction

  function void minstreth_to_trace(insn_trace_t m_trace);
    if(!m_trace.m_csr.minstreth_we) begin
      m_trace.m_csr.minstreth_wdata = r_pipe_freeze_trace.csr.wdata_int;
    end
    if(r_pipe_freeze_trace.csr.mhpmcounter_write_upper[2]) begin
        m_trace.m_csr.minstreth_we    = r_pipe_freeze_trace.csr.mhpmcounter_write_upper[2];
        m_trace.m_csr.minstreth_wdata = r_pipe_freeze_trace.csr.wdata_int;
        m_trace.m_csr.minstreth_wmask = r_pipe_freeze_trace.csr.mhpmcounter_write_upper[2] ? '1 : '0;
    end
    sample_minstreth_to_trace(m_trace);
  endfunction

  function void sample_perf_counter_to_trace(insn_trace_t m_trace);
    sample_minstret_to_trace(m_trace);
    sample_minstreth_to_trace(m_trace);
    sample_mcycle_to_trace(m_trace);
    for(int idx=3; idx<32; idx++)begin
      sample_perf_event_to_trace(idx, m_trace); //TO CHANGE
    end
  endfunction

  function void perf_counter_to_trace(insn_trace_t m_trace);
      if(r_pipe_freeze_trace.csr.mhpmcounter_write_lower[2]) begin
          minstret_to_trace(m_trace);
      end
      if(r_pipe_freeze_trace.csr.mhpmcounter_write_upper[2]) begin
          minstreth_to_trace(m_trace);
      end
      for(int idx=3; idx<32; idx++) begin
          if(r_pipe_freeze_trace.csr.mhpmcounter_write_lower[idx]) begin
              perf_counter_to_id(idx);
          end
          if(r_pipe_freeze_trace.csr.mhpmcounter_write_upper[idx]) begin
              perf_counter_h_to_id(idx);
          end
          if(r_pipe_freeze_trace.csr.mhpmevent_we[idx]) begin
              perf_event_to_trace(idx, m_trace);
          end
      end
  endfunction

  function void tinfo_to_trace(insn_trace_t m_trace);
    m_trace.m_csr.tinfo_we    = '0; // READ ONLY csr_tinfo_we_i;
    m_trace.m_csr.tinfo_rdata = r_pipe_freeze_trace.csr.tinfo_q;
    m_trace.m_csr.tinfo_rmask = '1;
    m_trace.m_csr.tinfo_wdata = r_pipe_freeze_trace.csr.tinfo_n;
    m_trace.m_csr.tinfo_wmask = '0;
  endfunction

  function void mtvec_to_id();
    trace_id.m_csr.mtvec_we = r_pipe_freeze_trace.csr.mtvec_we;
    trace_id.m_csr.mtvec_rdata = {
      r_pipe_freeze_trace.csr.mtvec_q, 6'h0, r_pipe_freeze_trace.csr.mtvec_mode_q
    };
    trace_id.m_csr.mtvec_rmask = '1;
    trace_id.m_csr.mtvec_wdata = {
      r_pipe_freeze_trace.csr.mtvec_n, 6'h0, r_pipe_freeze_trace.csr.mtvec_mode_n
    };
    ;
    trace_id.m_csr.mtvec_wmask = r_pipe_freeze_trace.csr.mtvec_we ? '1 : '0;
  endfunction

  function void dcsr_to_id();
    trace_id.m_csr.dcsr_wdata = trace_id.m_csr.dcsr_we ? trace_id.m_csr.dcsr_wdata : r_pipe_freeze_trace.csr.dcsr_n;
    trace_id.m_csr.dcsr_we = r_pipe_freeze_trace.csr.dcsr_we | trace_id.m_csr.dcsr_we;
    trace_id.m_csr.dcsr_rdata = r_pipe_freeze_trace.csr.dcsr_q;
    trace_id.m_csr.dcsr_rmask = '1;
    trace_id.m_csr.dcsr_wdata = r_pipe_freeze_trace.csr.dcsr_n;
    trace_id.m_csr.dcsr_wmask = r_pipe_freeze_trace.csr.dcsr_we ? '1 : '0;
  endfunction

  function void csrId_to_id();
    trace_id.m_csr.mvendorid_we    = '0;
    trace_id.m_csr.mvendorid_rdata = r_pipe_freeze_trace.csr.mvendorid;
    trace_id.m_csr.mvendorid_rmask = '1;
    trace_id.m_csr.mvendorid_wdata = '0;
    trace_id.m_csr.mvendorid_wmask = '0;

    trace_id.m_csr.marchid_we      = '0;
    trace_id.m_csr.marchid_rdata   = r_pipe_freeze_trace.csr.marchid;
    trace_id.m_csr.marchid_rmask   = '0;
    trace_id.m_csr.marchid_wdata   = '0;
    trace_id.m_csr.marchid_wmask   = '0;
  endfunction

  function void lpcount1_to_id();
    trace_id.m_csr.lpcount1_we    = '0;
    trace_id.m_csr.lpcount1_rdata = r_pipe_freeze_trace.hwloop.counter_q[1];
    trace_id.m_csr.lpcount1_rmask = '1;
    trace_id.m_csr.lpcount1_wdata = '0;
    trace_id.m_csr.lpcount1_wmask = '0;
  endfunction

  function void lpcount0_to_id();
    trace_id.m_csr.lpcount0_we    = '0;
    trace_id.m_csr.lpcount0_rdata = r_pipe_freeze_trace.hwloop.counter_q[0];
    trace_id.m_csr.lpcount0_rmask = '1;
    trace_id.m_csr.lpcount0_wdata = '0;
    trace_id.m_csr.lpcount0_wmask = '0;
  endfunction

  function void lpend0_to_id();
    trace_id.m_csr.lpend0_we    = '0;
    trace_id.m_csr.lpend0_rdata = r_pipe_freeze_trace.hwloop.end_q[0];
    trace_id.m_csr.lpend0_rmask = '1;
    trace_id.m_csr.lpend0_wdata = '0;
    trace_id.m_csr.lpend0_wmask = '0;
  endfunction

  function void lpend1_to_id();
    trace_id.m_csr.lpend1_we    = '0;
    trace_id.m_csr.lpend1_rdata = r_pipe_freeze_trace.hwloop.end_q[1];
    trace_id.m_csr.lpend1_rmask = '1;
    trace_id.m_csr.lpend1_wdata = '0;
    trace_id.m_csr.lpend1_wmask = '0;
  endfunction

  function void lpstart0_to_id();
    trace_id.m_csr.lpstart0_we    = '0;
    trace_id.m_csr.lpstart0_rdata = r_pipe_freeze_trace.hwloop.start_q[0];
    trace_id.m_csr.lpstart0_rmask = '1;
    trace_id.m_csr.lpstart0_wdata = '0;
    trace_id.m_csr.lpstart0_wmask = '0;
  endfunction

  function void lpstart1_to_id();
    trace_id.m_csr.lpstart1_we    = '0;
    trace_id.m_csr.lpstart1_rdata = r_pipe_freeze_trace.hwloop.start_q[1];
    trace_id.m_csr.lpstart1_rmask = '1;
    trace_id.m_csr.lpstart1_wdata = '0;
    trace_id.m_csr.lpstart1_wmask = '0;
  endfunction

  function void hwloop_to_id();
    lpcount0_to_id();
    lpend0_to_id();
    lpstart0_to_id();

    lpcount1_to_id();
    lpend1_to_id();
    lpstart1_to_id();
  endfunction

  bit s_was_flush;  //debug exception is flagged as trap only if preceed by a flush
  //Work arround until I find the coreect way to distinguish trap
  function void check_trap();
    bit s_dbg_exception, s_exception, s_irq;
    s_dbg_exception = 1'b0;
    s_exception     = 1'b0;
    s_irq           = 1'b0;

    if (r_pipe_freeze_trace.pc_mux == PC_EXCEPTION) begin
      if (r_pipe_freeze_trace.exc_pc_mux[1] == 1'b1) begin
        if (r_pipe_freeze_trace.ctrl_fsm_cs != XRET_JUMP) begin
          s_dbg_exception = 1'b1;
        end
      end
      if (r_pipe_freeze_trace.exc_pc_mux == EXC_PC_EXCEPTION) begin
        s_exception = 1'b1;
      end
      if (r_pipe_freeze_trace.exc_pc_mux == EXC_PC_IRQ) begin
        s_irq = 1'b1;
        trace_if.m_is_irq = 1'b1;
      end
    end

    if (s_was_flush == 1'b0) begin
      s_dbg_exception = 1'b0;
    end

  endfunction
  /*
   * This tracer works with three process,
   *
   * The first one simply stores information from the pipeline every clock cycles and sends those information to the second process
   *
   * The second process uses those information to fill the rvfi interface with the correct values
   *
   * The third updates the rvfi interface
   */
  `define CSR_FROM_PIPE(TRACE_NAME, CSR_NAME) \
    if(!trace_``TRACE_NAME``.m_csr.``CSR_NAME``_we) begin \
      trace_``TRACE_NAME``.m_csr.``CSR_NAME``_wdata   = r_pipe_freeze_trace.csr.``CSR_NAME``_n; \
    end\
    if (r_pipe_freeze_trace.csr.``CSR_NAME``_we) begin \
      trace_``TRACE_NAME``.m_csr.``CSR_NAME``_we      = r_pipe_freeze_trace.csr.``CSR_NAME``_we; \
      trace_``TRACE_NAME``.m_csr.``CSR_NAME``_wdata   = r_pipe_freeze_trace.csr.``CSR_NAME``_n; \
      trace_``TRACE_NAME``.m_csr.``CSR_NAME``_wmask   = '1; \
    end \
    trace_``TRACE_NAME``.m_csr.``CSR_NAME``_rdata   = r_pipe_freeze_trace.csr.``CSR_NAME``_q; \
    trace_``TRACE_NAME``.m_csr.``CSR_NAME``_rmask   = '1;

  event e_mstatus_to_id;
  event e_fregs_dirty_1, e_fregs_dirty_2, e_fregs_dirty_3;
  function void mstatus_to_id();
    `CSR_FROM_PIPE(id, mstatus)
    `CSR_FROM_PIPE(id, mstatus_fs)
    if(r_pipe_freeze_trace.csr.fregs_we && !r_pipe_freeze_trace.csr.mstatus_fs_we && !(r_pipe_freeze_trace.csr.we && r_pipe_freeze_trace.csr.mstatus_fs_we)) begin //writes happening in ex that needs to be reported to id
      trace_id.m_csr.mstatus_fs_rdata = r_pipe_freeze_trace.csr.mstatus_fs_n;
      ->e_fregs_dirty_2;
    end
    ->e_mstatus_to_id;
  endfunction
  //those event are for debug purpose
  event e_dev_send_wb_1, e_dev_send_wb_2;
  event
      e_dev_commit_rf_to_ex_1,
      e_dev_commit_rf_to_ex_2,
      e_dev_commit_rf_to_ex_3,
      e_dev_commit_rf_to_ex_4,
      e_dev_commit_rf_to_ex_5;
  event e_if_2_id_1, e_if_2_id_2, e_if_2_id_3, e_if_2_id_4;
  event e_ex_to_wb_1, e_ex_to_wb_2;
  event e_id_to_ex_1, e_id_to_ex_2;
  event e_commit_dpc;
  event e_csr_in_ex, e_csr_irq;

  event e_send_rvfi_trace_apu_resp;
  event
      e_send_rvfi_trace_ex_1,
      e_send_rvfi_trace_ex_2,
      e_send_rvfi_trace_ex_3,
      e_send_rvfi_trace_ex_4,
      e_send_rvfi_trace_ex_5,
      e_send_rvfi_trace_ex_6;
  event e_send_rvfi_trace_wb_1, e_send_rvfi_trace_wb_2, e_send_rvfi_trace_wb_3;
  event e_send_rvfi_trace_id_1;

  //used to match memory response to memory request and corresponding instruction
  integer cnt_data_req, cnt_data_resp;
  integer cnt_apu_req, cnt_apu_resp;

  insn_trace_t apu_trace_q[$];
  insn_trace_t trace_apu_req, trace_apu_resp;

  function void csr_to_apu_resp();
    `CSR_FROM_PIPE(apu_resp, fcsr)
    `CSR_FROM_PIPE(apu_resp, fflags)

    `CSR_FROM_PIPE(apu_resp, mstatus_fs)

    if (r_pipe_freeze_trace.csr.mstatus_fs_we && (trace_id.m_order > trace_apu_resp.m_order)) begin
      trace_id.m_csr.mstatus_fs_rdata = r_pipe_freeze_trace.csr.mstatus_fs_n;
    end
    if (r_pipe_freeze_trace.csr.mstatus_fs_we && (trace_ex.m_order > trace_apu_resp.m_order)) begin
      trace_ex.m_csr.mstatus_fs_rdata = r_pipe_freeze_trace.csr.mstatus_fs_n;
    end
    if (r_pipe_freeze_trace.csr.mstatus_fs_we && (trace_wb.m_order > trace_apu_resp.m_order)) begin
      trace_wb.m_csr.mstatus_fs_rdata = r_pipe_freeze_trace.csr.mstatus_fs_n;
    end
  endfunction

  function void csr_to_apu_req();
    `CSR_FROM_PIPE(apu_req, misa)
    `CSR_FROM_PIPE(apu_req, tdata1)
    `CSR_FROM_PIPE(apu_req, tdata2)
    trace_apu_req.m_csr.tinfo_we = '0;  // READ ONLY csr_tinfo_we_i;
    trace_apu_req.m_csr.tinfo_rdata = r_pipe_freeze_trace.csr.tinfo_q;
    trace_apu_req.m_csr.tinfo_rmask = '1;
    trace_apu_req.m_csr.tinfo_wdata = r_pipe_freeze_trace.csr.tinfo_n;
    trace_apu_req.m_csr.tinfo_wmask = '0;

    trace_apu_req.m_csr.minstret_we = r_pipe_freeze_trace.csr.mhpmcounter_write_lower[2];
    trace_apu_req.m_csr.minstret_rdata = r_pipe_freeze_trace.csr.mhpmcounter_q[2];
    trace_apu_req.m_csr.minstret_rmask = '1;
    trace_apu_req.m_csr.minstret_wdata = r_pipe_freeze_trace.csr.mhpmcounter_q;
    trace_apu_req.m_csr.minstret_wmask = r_pipe_freeze_trace.csr.mhpmcounter_write_lower[2] ? '1 : '0;

    trace_apu_req.m_csr.lpcount0_we = '0;
    trace_apu_req.m_csr.lpcount0_rdata = r_pipe_freeze_trace.hwloop.counter_q[0];
    trace_apu_req.m_csr.lpcount0_rmask = '1;
    trace_apu_req.m_csr.lpcount0_wdata = '0;
    trace_apu_req.m_csr.lpcount0_wmask = '0;

    trace_apu_req.m_csr.lpcount1_we = '0;
    trace_apu_req.m_csr.lpcount1_rdata = r_pipe_freeze_trace.hwloop.counter_q[1];
    trace_apu_req.m_csr.lpcount1_rmask = '1;
    trace_apu_req.m_csr.lpcount1_wdata = '0;
    trace_apu_req.m_csr.lpcount1_wmask = '0;

    `CSR_FROM_PIPE(apu_req, frm)


  endfunction

  function void fcsr_to_wb();
    `CSR_FROM_PIPE(wb, fflags)
    `CSR_FROM_PIPE(wb, frm)
    `CSR_FROM_PIPE(wb, fcsr)
    trace_wb.m_csr.fflags_wmask = '0;
    trace_wb.m_csr.frm_wmask    = '0;
    trace_wb.m_csr.fcsr_wmask   = '0;
  endfunction

  bit s_apu_to_alu_port;
  bit s_apu_to_lsu_port;

  function void apu_resp();
    if (!r_pipe_freeze_trace.wb_contention_lsu) begin
      if (apu_trace_q.size() > 0) begin
        trace_apu_resp = apu_trace_q.pop_front();
        if (s_apu_to_alu_port) begin
          if (r_pipe_freeze_trace.ex_reg_we) begin
            trace_apu_resp.m_rd_addr[0]  = r_pipe_freeze_trace.ex_reg_addr;
            trace_apu_resp.m_rd_wdata[0] = r_pipe_freeze_trace.ex_reg_wdata;
          end
        end else if (s_apu_to_lsu_port) begin
          if (r_pipe_freeze_trace.rf_we_wb) begin
            trace_apu_resp.m_rd_addr[0]  = r_pipe_freeze_trace.rf_addr_wb;
            trace_apu_resp.m_rd_wdata[0] = r_pipe_freeze_trace.rf_wdata_wb;
          end
        end
        csr_to_apu_resp();

        trace_apu_resp.m_stop_cycle = cycles;
        trace_apu_resp.m_stop_time = $time;
        send_rvfi(trace_apu_resp);
        ->e_send_rvfi_trace_apu_resp;
      end
    end
  endfunction

  /*
   * Decoding is complete and instruction enters execute stage
   * If at that time, minstret is not asserted it means we have a trap
   */
  bit s_is_pc_set;  //If pc_set, wait until next trace_id to commit csr changes
  bit s_is_irq_start;
  bit s_id_done;
  function void if_to_id();
    if (trace_id.m_valid) begin
      `CSR_FROM_PIPE(id, misa)
      `CSR_FROM_PIPE(id, tdata1)
      `CSR_FROM_PIPE(id, tdata2)
      tinfo_to_trace(trace_id);
      `CSR_FROM_PIPE(id, mip)
      send_rvfi(trace_id);
    end
    trace_id.init(trace_if);
    trace_id.m_trap       = ~r_pipe_freeze_trace.minstret;
    trace_id.m_is_illegal = trace_id.m_is_illegal | r_pipe_freeze_trace.is_illegal;
    `CSR_FROM_PIPE(id, dpc)
    s_is_pc_set           = 1'b0;
    s_is_irq_start        = 1'b0;
    trace_if.m_valid      = 1'b0;
    s_id_done             = 1'b0;
  endfunction

  function logic [31:0] be_to_mask(logic [3:0] be);
    logic [31:0] mask;
    mask[7:0]   = (be[0] == 1'b1) ? 8'hFF : 8'h00;
    mask[15:8]  = (be[1] == 1'b1) ? 8'hFF : 8'h00;
    mask[23:16] = (be[2] == 1'b1) ? 8'hFF : 8'h00;
    mask[31:24] = (be[3] == 1'b1) ? 8'hFF : 8'h00;

    be_to_mask  = mask;
    return mask;
  endfunction

  function void commit_rf_to_trace(insn_trace_t m_trace);
    if (m_trace.m_got_ex_reg) begin
        m_trace.m_rd_addr[1] = r_pipe_freeze_trace.rf_addr_wb;
        m_trace.m_rd_wdata[1] = r_pipe_freeze_trace.rf_wdata_wb;
        m_trace.m_2_rd_insn = 1'b1;
        m_trace.m_got_first_data = 1'b1;
    end else begin
        m_trace.m_rd_addr[0] = r_pipe_freeze_trace.rf_addr_wb;
        m_trace.m_rd_wdata[0] = r_pipe_freeze_trace.rf_wdata_wb;
        m_trace.m_got_first_data = 1'b1;
    end
  endfunction

  task compute_pipeline();
    bit s_new_valid_insn;
    bit s_ex_valid_adjusted;
    bit s_wb_valid_adjusted;

    bit s_apu_wb_ok;
    bit s_apu_0_cycle_reps;

    bit s_fflags_we_non_apu;
    bit s_frm_we_non_apu;
    bit s_fcsr_we_non_apu;

    bit s_skip_wb;  // used to skip wb monitoring when apu resp and not lsu

    bit s_core_is_decoding;  // For readability, ctrl_fsm is DECODE or DECODE_HWLOOP

    bit s_ex_reg_we_adjusted;  //ex_reg_we
    bit s_rf_we_wb_adjusted;  //

    bit s_dont_override_mstatus_fs_id;

    trace_if             = new();
    trace_id             = new();
    trace_ex             = new();
    trace_wb             = new();
    s_new_valid_insn     = 1'b0;
    s_ex_valid_adjusted  = 1'b0;

    s_id_done            = 1'b0;
    s_apu_wb_ok          = 1'b0;
    s_apu_0_cycle_reps   = 1'b0;

    next_send            = 1;
    cnt_data_req         = 0;
    cnt_data_resp        = 0;
    cnt_apu_req          = 0;
    cnt_apu_resp         = 0;
    csr_is_irq           = '0;
    is_dbg_taken         = '0;
    s_was_flush          = 1'b0;

    s_is_pc_set          = 1'b0;
    s_is_irq_start       = 1'b0;

    s_is_pc_set          = 1'b0;
    s_is_irq_start       = 1'b0;
    s_skip_wb            = 1'b0;

    s_core_is_decoding   = 1'b0;

    s_ex_reg_we_adjusted = 1'b0;
    s_rf_we_wb_adjusted  = 1'b0;

    s_dont_override_mstatus_fs_id = 1'b0;

    forever begin
      wait(e_pipe_monitor_ok.triggered);  // event triggered
      #1;

      s_core_is_decoding = (r_pipe_freeze_trace.ctrl_fsm_cs == DECODE) || (r_pipe_freeze_trace.ctrl_fsm_cs == DECODE_HWLOOP);
      check_trap();

      pc_mux_interrupt = 1'b0;
      if (r_pipe_freeze_trace.pc_mux == 4'b0100) begin
        if (r_pipe_freeze_trace.exc_pc_mux == 3'b001) begin
          pc_mux_interrupt = 1'b1;
          s_is_irq_start   = 1'b1;
        end
      end

      if (r_pipe_freeze_trace.ctrl_fsm_cs == DBG_TAKEN_ID && r_pipe_freeze_trace.ebrk_insn_dec) begin
        if (trace_id.m_valid) begin
          `CSR_FROM_PIPE(id, misa)
          `CSR_FROM_PIPE(id, tdata1)
          `CSR_FROM_PIPE(id, tdata2)
          tinfo_to_trace(trace_id);
          `CSR_FROM_PIPE(id, mip)
        end
      end

      if (r_pipe_freeze_trace.data_rvalid) begin
        cnt_data_resp = cnt_data_resp + 1;
      end

      if (r_pipe_freeze_trace.apu_req && r_pipe_freeze_trace.apu_gnt) begin
        cnt_apu_req = cnt_apu_req + 1;
      end
      if (r_pipe_freeze_trace.apu_rvalid) begin
        cnt_apu_resp = cnt_apu_resp + 1;
        if (r_pipe_freeze_trace.apu_singlecycle | r_pipe_freeze_trace.apu_multicycle) begin
          s_apu_to_alu_port = 1'b1;
          s_apu_to_lsu_port = 1'b0;
        end else begin
          s_apu_to_lsu_port = 1'b1;
          s_apu_to_alu_port = 1'b0;
        end
      end else begin
        s_apu_to_lsu_port = 1'b0;
        s_apu_to_alu_port = 1'b0;
      end

      if(r_pipe_freeze_trace.apu_req && r_pipe_freeze_trace.apu_gnt && r_pipe_freeze_trace.apu_rvalid && (cnt_apu_resp == cnt_apu_req)) begin
        s_apu_0_cycle_reps = 1'b1;
      end else begin
        s_apu_0_cycle_reps = 1'b0;
      end

      if (trace_ex.m_valid & s_wb_valid_adjusted) begin
        // Used flopped values in case write happened before wb_valid
        sample_perf_counter_to_trace(trace_ex);
        trace_ex.m_csr.got_minstret = '1;
      end

      if (trace_wb.m_valid & trace_wb.m_is_apu & (trace_wb.m_apu_req_id == cnt_apu_resp)) begin
        s_apu_wb_ok = 1'b1;
      end else begin
        s_apu_wb_ok = 1'b0;
      end

      s_new_valid_insn = r_pipe_freeze_trace.id_valid && r_pipe_freeze_trace.is_decoding;// && !r_pipe_freeze_trace.apu_rvalid;

      s_wb_valid_adjusted = r_pipe_freeze_trace.wb_valid && (s_core_is_decoding || (r_pipe_freeze_trace.ctrl_fsm_cs == FLUSH_EX) || (r_pipe_freeze_trace.ctrl_fsm_cs == FLUSH_WB) || (r_pipe_freeze_trace.ctrl_fsm_cs == DBG_FLUSH) || (r_pipe_freeze_trace.ctrl_fsm_cs == DBG_TAKEN_ID) || (r_pipe_freeze_trace.ctrl_fsm_cs == DBG_TAKEN_IF));// && !r_pipe_freeze_trace.apu_rvalid;;
      s_ex_reg_we_adjusted = r_pipe_freeze_trace.ex_reg_we && r_pipe_freeze_trace.mult_ready && r_pipe_freeze_trace.alu_ready && r_pipe_freeze_trace.lsu_ready_ex && !s_apu_to_alu_port;
      s_rf_we_wb_adjusted = r_pipe_freeze_trace.rf_we_wb && (~r_pipe_freeze_trace.data_misaligned_ex && r_pipe_freeze_trace.wb_ready) && (!s_apu_to_lsu_port || r_pipe_freeze_trace.wb_contention_lsu);

      s_fflags_we_non_apu = 1'b0;
      if (r_pipe_freeze_trace.csr.fflags_we) begin
        if (cnt_apu_resp == cnt_apu_req) begin  //No ongoing apu instruction
          s_fflags_we_non_apu = 1'b1;
        end
      end

      s_frm_we_non_apu = 1'b0;
      if (r_pipe_freeze_trace.csr.frm_we) begin
        if (cnt_apu_resp == cnt_apu_req) begin  //No ongoing apu instruction
          s_frm_we_non_apu = 1'b1;
        end
      end

      s_fcsr_we_non_apu = 1'b0;
      if (r_pipe_freeze_trace.csr.fcsr_we) begin
        if (cnt_apu_resp == cnt_apu_req) begin  //No ongoing apu instruction
          s_fcsr_we_non_apu = 1'b1;
        end
      end

      //WB_STAGE
      s_skip_wb = 1'b0;
      if (r_pipe_freeze_trace.apu_rvalid && (apu_trace_q.size() > 0)) begin
        apu_resp();
        if (!r_pipe_freeze_trace.data_rvalid) begin
          s_skip_wb = 1'b1;
        end
      end

      if (trace_wb.m_valid && !s_skip_wb && s_rf_we_wb_adjusted) begin
        if (trace_wb.m_2_rd_insn) begin
          trace_wb.m_rd_addr[1]  = r_pipe_freeze_trace.rf_addr_wb;
          trace_wb.m_rd_wdata[1] = r_pipe_freeze_trace.rf_wdata_wb;
        end else if (trace_wb.m_ex_fw) begin
          trace_wb.m_rd_addr[1]  = r_pipe_freeze_trace.rf_addr_wb;
          trace_wb.m_rd_wdata[1] = r_pipe_freeze_trace.rf_wdata_wb;
          trace_wb.m_2_rd_insn   = 1'b1;
        end else begin
          trace_wb.m_rd_addr[0]  = r_pipe_freeze_trace.rf_addr_wb;
          trace_wb.m_rd_wdata[0] = r_pipe_freeze_trace.rf_wdata_wb;
        end

        if (r_pipe_freeze_trace.csr.fregs_we) begin
          `CSR_FROM_PIPE(wb, mstatus_fs)
          trace_wb.m_csr.mstatus_fs_we = 1'b1;
          trace_wb.m_csr.mstatus_fs_wmask = '1;
          if(r_pipe_freeze_trace.csr.we && r_pipe_freeze_trace.csr.mstatus_fs_we) begin //In this specific case, two writes to mstatus_fs happen at the same time. We need to recreate the writes caused by fregs_we
            trace_wb.m_csr.mstatus_fs_wdata = FS_DIRTY;
          end
          ->e_fregs_dirty_1;
        end

        send_rvfi(trace_wb);
        ->e_dev_send_wb_1; ->e_send_rvfi_trace_wb_2;
        trace_wb.m_valid = 1'b0;

      end

      if (trace_ex.m_valid) begin
        if(trace_ex.m_instret_smaple_trigger == 1) begin //time to sample instret
          sample_perf_counter_to_trace(trace_ex);
        end
        trace_ex.m_instret_smaple_trigger = trace_ex.m_instret_smaple_trigger + 1;

        `CSR_FROM_PIPE(ex, misa)
        `CSR_FROM_PIPE(ex, tdata1)
        `CSR_FROM_PIPE(ex, tdata2)
        tinfo_to_trace(trace_ex);

        if (s_rf_we_wb_adjusted) begin
          ->e_dev_commit_rf_to_ex_4;
          if (!(trace_ex.m_got_ex_reg) && trace_ex.m_mem_req_id_valid[0]) begin
            trace_ex.m_rd_addr[0] = r_pipe_freeze_trace.rf_addr_wb;
            trace_ex.m_rd_wdata[0] = r_pipe_freeze_trace.rf_wdata_wb;
            trace_ex.m_got_first_data = 1'b1;
            trace_ex.m_mem_req_id_valid[0] = 1'b0;
          end else if (trace_ex.m_mem_req_id_valid[1]) begin
            trace_ex.m_rd_addr[1] = r_pipe_freeze_trace.rf_addr_wb;
            trace_ex.m_rd_wdata[1] = r_pipe_freeze_trace.rf_wdata_wb;
            trace_ex.m_got_first_data = 1'b1;
            trace_ex.m_mem_req_id_valid[1] = 1'b0;
          end
        end

        if (s_wb_valid_adjusted) begin
          if (trace_wb.m_valid) begin
            send_rvfi(trace_ex);
            trace_ex.m_valid = 1'b0;
            ->e_send_rvfi_trace_ex_2;
          end else begin

            if (s_rf_we_wb_adjusted) begin
              ->e_dev_commit_rf_to_ex_1;
              commit_rf_to_trace(trace_ex);

              if (r_pipe_freeze_trace.csr.fregs_we && (r_pipe_freeze_trace.rf_we_wb && r_pipe_freeze_trace.rf_addr_wb[5])) begin //Catching mstatus_fs updates caused by flw
                `CSR_FROM_PIPE(ex, mstatus_fs)
                trace_ex.m_csr.mstatus_fs_we = 1'b1;
                trace_ex.m_csr.mstatus_fs_wmask = '1;
                if(r_pipe_freeze_trace.csr.we && r_pipe_freeze_trace.csr.mstatus_fs_we) begin //In this specific case, two writes to mstatus_fs happen at the same time. We need to recreate the writes caused by fregs_we
                  trace_ex.m_csr.mstatus_fs_wdata = FS_DIRTY;
                end else begin
                  trace_id.m_csr.mstatus_fs_rdata = trace_ex.m_csr.mstatus_fs_wdata;
                  s_dont_override_mstatus_fs_id = 1'b1;
                end
                ->e_fregs_dirty_3;
              end

              send_rvfi(trace_ex);
              trace_ex.m_valid = 1'b0;

            end else begin
              if (trace_ex.m_is_load) begin  // only move relevant instr in wb stage
                ->e_ex_to_wb_1;
                trace_wb.move_down_pipe(trace_ex);
              end else begin
                send_rvfi(trace_ex);
                ->e_send_rvfi_trace_ex_6;
              end
              trace_ex.m_valid = 1'b0;
            end
          end
        end else if (s_rf_we_wb_adjusted && !s_was_flush) begin
          ->e_dev_commit_rf_to_ex_2;
          commit_rf_to_trace(trace_ex);
        end
      end

      // If mret, we need to keep the instruction in Id during flush_ex because mstatus update happens at that time
      s_ex_valid_adjusted = (r_pipe_freeze_trace.ex_valid && r_pipe_freeze_trace.ex_ready) && (s_core_is_decoding || (r_pipe_freeze_trace.ctrl_fsm_cs == DBG_TAKEN_IF) || (r_pipe_freeze_trace.ctrl_fsm_cs == DBG_TAKEN_ID) || (r_pipe_freeze_trace.ctrl_fsm_cs == DBG_FLUSH) || ((r_pipe_freeze_trace.ctrl_fsm_cs == FLUSH_EX) && !r_pipe_freeze_trace.mret_insn_dec));
      //EX_STAGE

      if (trace_id.m_valid) begin
        if(trace_id.m_instret_smaple_trigger == 1) begin //time to sample instret
          sample_perf_counter_to_trace(trace_id);
          for(int idx=3; idx<32; idx++) begin
              sample_perf_counter_to_id(idx);
              sample_perf_counter_h_to_id(idx);
              sample_perf_event_to_trace(idx, trace_id);
          end
        end
        trace_id.m_instret_smaple_trigger = trace_id.m_instret_smaple_trigger + 1;

        if(trace_id.m_sample_csr_write_in_ex && !csr_is_irq && !s_is_irq_start) begin //First cycle after id_ready, csr write is asserted in this cycle
          `CSR_FROM_PIPE(id, mstatus)
          if(!s_dont_override_mstatus_fs_id) begin
              `CSR_FROM_PIPE(id, mstatus_fs)
          end
          `CSR_FROM_PIPE(id, mepc)
          `CSR_FROM_PIPE(id, mcause)
          `CSR_FROM_PIPE(id, dscratch0)
          `CSR_FROM_PIPE(id, dscratch1)
          if(r_pipe_freeze_trace.csr.we && (r_pipe_freeze_trace.csr.addr == CSR_DPC)) begin
            `CSR_FROM_PIPE(id, dpc)
          end

          `CSR_FROM_PIPE(id, mcountinhibit)

          perf_counter_to_trace(trace_id);
          ->e_csr_in_ex;
        end

        if(r_pipe_freeze_trace.is_decoding) begin
            trace_id.m_sample_csr_write_in_ex = 1'b0;
        end
        mtvec_to_id();

        `CSR_FROM_PIPE(id, mip)
        `CSR_FROM_PIPE(id, misa)

        `CSR_FROM_PIPE(id, mcountinhibit)
        `CSR_FROM_PIPE(id, mscratch)
        `CSR_FROM_PIPE(id, mie)

        `CSR_FROM_PIPE(id, fflags)
        `CSR_FROM_PIPE(id, frm)
        `CSR_FROM_PIPE(id, fcsr)

        if (r_pipe_freeze_trace.csr.dcsr_we) begin
          dcsr_to_id();
        end

        if (s_fflags_we_non_apu) begin
          trace_id.m_fflags_we_non_apu = 1'b1;
        end

        if (s_frm_we_non_apu) begin
          trace_id.m_frm_we_non_apu = 1'b1;
        end

        if (s_fcsr_we_non_apu) begin
          trace_id.m_fcsr_we_non_apu = 1'b1;
        end

        trace_ex.m_csr.fflags_wmask = '0;
        trace_ex.m_csr.frm_wmask    = '0;
        trace_ex.m_csr.fcsr_wmask   = '0;

        if(r_pipe_freeze_trace.ctrl_fsm_cs == XRET_JUMP) begin //xret exit pipeline
            tinfo_to_trace(trace_id);
            `CSR_FROM_PIPE(id, tdata1)
            `CSR_FROM_PIPE(id, tdata2)
            send_rvfi(trace_id);
            trace_id.m_valid = 1'b0;
            s_dont_override_mstatus_fs_id = 1'b0;
        end

        if (r_pipe_freeze_trace.apu_req && r_pipe_freeze_trace.apu_gnt) begin
          trace_id.m_is_apu = 1'b1;
          trace_id.m_apu_req_id = cnt_apu_req;
          trace_apu_req = new();
          trace_apu_req.copy_full(trace_id);
          csr_to_apu_req();
          trace_apu_req.set_to_apu();
          apu_trace_q.push_back(trace_apu_req);
          trace_id.m_valid = 1'b0;
          s_dont_override_mstatus_fs_id = 1'b0;

          if(r_pipe_freeze_trace.apu_rvalid && (cnt_apu_req == cnt_apu_resp)) begin//APU return in the same cycle
            apu_resp();
          end
        end

        if (s_ex_valid_adjusted) begin  //A valid instruction goes from ID to EX
          if (trace_ex.m_valid) begin  //We need to bypass wb
            send_rvfi(trace_ex);
            trace_ex.m_valid = 1'b0;
            ->e_send_rvfi_trace_ex_3;
          end
          if (r_pipe_freeze_trace.ex_reg_we && !s_apu_to_alu_port) begin
            trace_id.m_ex_fw    = 1'b1;
            trace_id.m_rd_addr[0]  = r_pipe_freeze_trace.ex_reg_addr;
            trace_id.m_rd_wdata[0] = r_pipe_freeze_trace.ex_reg_wdata;
            trace_id.m_got_ex_reg = 1'b1;
          end else if (!trace_ex.m_valid & s_rf_we_wb_adjusted & !trace_id.m_ex_fw) begin
            trace_id.m_rd_addr[0]  = r_pipe_freeze_trace.rf_addr_wb;
            trace_id.m_rd_wdata[0] = r_pipe_freeze_trace.rf_wdata_wb;
          end else if (s_rf_we_wb_adjusted) begin
            trace_id.m_rd_addr[1]  = r_pipe_freeze_trace.rf_addr_wb;
            trace_id.m_rd_wdata[1] = r_pipe_freeze_trace.rf_wdata_wb;
            trace_id.m_2_rd_insn   = 1'b1;
          end

          if (r_pipe_freeze_trace.data_req_ex) begin
            cnt_data_req = cnt_data_req + 1;
            trace_id.m_is_memory = 1'b1;
            trace_id.m_mem_req_id[0] = cnt_data_req;
            trace_id.m_mem_req_id_valid[0] = 1'b1;

            trace_id.m_mem.addr = r_pipe_freeze_trace.data_addr_pmp;
            if (r_pipe_freeze_trace.data_misaligned) begin
              cnt_data_req = cnt_data_req + 1;
              trace_id.m_mem_req_id[0] = cnt_data_req;
            end

            if (!r_pipe_freeze_trace.data_we_ex) begin
              trace_id.m_is_load   = 1'b1;
              trace_id.m_mem.wmask = be_to_mask(r_pipe_freeze_trace.lsu_data_be);  //'1;
            end else begin
              trace_id.m_mem.rmask = be_to_mask(r_pipe_freeze_trace.lsu_data_be);  //'1;
            end

            if (trace_id.m_got_ex_reg) begin  // Shift index 0 to 1
              trace_id.m_mem_req_id[1] = trace_id.m_mem_req_id[0];
              trace_id.m_mem_req_id[0] = 0;
              trace_id.m_mem_req_id_valid[1] = 1'b1;
              trace_id.m_mem_req_id_valid[0] = 1'b0;
            end
          end
          hwloop_to_id();
          trace_ex.move_down_pipe(trace_id);  // The instruction moves forward from ID to EX
          trace_id.m_valid = 1'b0;
          s_dont_override_mstatus_fs_id = 1'b0;
          ->e_id_to_ex_1;

        end else if (r_pipe_freeze_trace.ex_reg_we && r_pipe_freeze_trace.rf_alu_we_ex) begin
          trace_id.m_ex_fw          = 1'b1;
          trace_id.m_rd_addr[0]     = r_pipe_freeze_trace.ex_reg_addr;
          trace_id.m_rd_wdata[0]    = r_pipe_freeze_trace.ex_reg_wdata;
          trace_id.m_got_ex_reg     = 1'b1;
          trace_id.m_got_regs_write = 1'b1;
          // mem_req_id[0] already set here indicates req_id was set before rf write from EX
          // Hence adjust the req_id again here for such cases
          if (trace_id.m_mem_req_id[0] != 0) begin
            trace_id.m_mem_req_id[1] = trace_id.m_mem_req_id[0];
            trace_id.m_mem_req_id[0] = 0;
            trace_id.m_mem_req_id_valid[0] = 1'b0;
            trace_id.m_mem_req_id_valid[1] = 1'b1;
          end
        end
      end  //trace_if.m_valid

      //ID_STAGE
      if (s_new_valid_insn) begin  // There is a new valid instruction
        if (trace_id.m_valid) begin
          if (trace_ex.m_valid) begin
            if (trace_wb.m_valid) begin
              send_rvfi(trace_ex);
              ->e_send_rvfi_trace_ex_4;
            end else begin
              if (trace_ex.m_is_load) begin  // only move relevant instr in wb stage
                ->e_ex_to_wb_2;
                trace_wb.move_down_pipe(trace_ex);
              end else begin
                send_rvfi(trace_ex);
                ->e_send_rvfi_trace_ex_5;
              end
            end
            trace_ex.m_valid = 1'b0;
          end
          if (r_pipe_freeze_trace.data_req_ex) begin
            cnt_data_req = cnt_data_req + 1;
            trace_id.m_is_memory = 1'b1;
            trace_id.m_mem_req_id[0] = cnt_data_req;
            trace_id.m_mem_req_id_valid[0] = 1'b1;
            trace_id.m_mem.addr = r_pipe_freeze_trace.data_addr_pmp;
            if (r_pipe_freeze_trace.data_misaligned) begin
              cnt_data_req = cnt_data_req + 1;
              trace_id.m_mem_req_id[0] = cnt_data_req;
            end
            if (!r_pipe_freeze_trace.data_we_ex) begin
              trace_id.m_is_load = 1'b1;
            end
            if (trace_id.m_got_ex_reg) begin  // Shift index 0 to 1
              trace_id.m_mem_req_id[1] = trace_id.m_mem_req_id[0];
              trace_id.m_mem_req_id[0] = 0;
              trace_id.m_mem_req_id_valid[0] = 1'b0;
              trace_id.m_mem_req_id_valid[1] = 1'b1;
            end
          end else if (s_rf_we_wb_adjusted && !r_pipe_freeze_trace.ex_reg_we) begin
            trace_id.m_rd_addr[0]  = r_pipe_freeze_trace.rf_addr_wb;
            trace_id.m_rd_wdata[0] = r_pipe_freeze_trace.rf_wdata_wb;
          end

          hwloop_to_id();
          trace_ex.move_down_pipe(trace_id);
          trace_id.m_valid = 1'b0;
          s_dont_override_mstatus_fs_id = 1'b0;
          ->e_id_to_ex_2;
        end
        if_to_id();
        trace_id.m_is_ebreak = trace_if.m_is_ebreak;
        csrId_to_id();
        `CSR_FROM_PIPE(id, dscratch0)
        `CSR_FROM_PIPE(id, dscratch1)
        mstatus_to_id();
        ->e_if_2_id_1;
      end else begin
        if (trace_id.m_valid) begin
          `CSR_FROM_PIPE(id, dscratch0)
          `CSR_FROM_PIPE(id, dscratch1)
        end
      end

      //IF_STAGE
      if(trace_if.m_valid) begin
        if(r_pipe_freeze_trace.is_illegal && r_pipe_freeze_trace.is_decoding) begin
          trace_if.m_is_illegal = 1'b1;
        end
      end

      if (r_pipe_freeze_trace.if_valid && r_pipe_freeze_trace.if_ready && r_pipe_freeze_trace.instr_valid_if) begin
        if (trace_if.m_valid) begin
          if (r_pipe_freeze_trace.id_valid && r_pipe_freeze_trace.id_ready && !trace_id.m_valid && r_pipe_freeze_trace.ebrk_insn_dec) begin
            if_to_id();
            trace_id.m_is_ebreak = '1;  //trace_if.m_is_ebreak;
            ->e_if_2_id_2;
          end else if (trace_if.m_is_illegal) begin
            if_to_id();
            ->e_if_2_id_3;
          end else if (r_pipe_freeze_trace.ecall_insn_dec) begin
            if_to_id();
            ->e_if_2_id_4;
          end
        end


        trace_if.m_insn = r_pipe_freeze_trace.instr_if;  //Instr comes from if, buffer for one cycle
        trace_if.m_pc_rdata = r_pipe_freeze_trace.pc_if;
        trace_if.m_dbg_taken = is_dbg_taken;
        trace_if.m_dbg_cause = saved_debug_cause;
        trace_if.m_is_ebreak = '0;
        trace_if.m_trap = 1'b0;

        trace_if.m_valid = 1'b1;
      end

      if (csr_is_irq && !s_is_pc_set) begin
        mstatus_to_id();
        `CSR_FROM_PIPE(id, mepc)
        `CSR_FROM_PIPE(id, mcause)
        ->e_csr_irq;
      end

      if (!s_id_done && r_pipe_freeze_trace.is_decoding) begin
        dcsr_to_id();
        ->e_commit_dpc;
      end

      if (r_pipe_freeze_trace.pc_set) begin
        s_is_pc_set = 1'b1;
      end

      csr_is_irq = r_pipe_freeze_trace.csr_cause[5];
      is_dbg_taken      = ((r_pipe_freeze_trace.ctrl_fsm_cs == DBG_TAKEN_ID) | (r_pipe_freeze_trace.ctrl_fsm_cs == DBG_TAKEN_IF)) ? 1'b1 : 1'b0;
      saved_debug_cause = r_pipe_freeze_trace.debug_cause;
      s_id_done = r_pipe_freeze_trace.id_valid;
      if((r_pipe_freeze_trace.ctrl_fsm_cs == DBG_FLUSH) || (r_pipe_freeze_trace.ctrl_fsm_cs == FLUSH_EX) || (r_pipe_freeze_trace.ctrl_fsm_cs == FLUSH_WB)) begin
        s_was_flush = 1'b1;
      end else begin
        s_was_flush = 1'b0;
      end
      #1;
    end
  endtask

  task update_rvfi();
    rvfi_valid       = 1'b0;
    rvfi_order       = '0;
    rvfi_insn        = '0;
    rvfi_pc_rdata    = '0;
    rvfi_rd_addr[0]  = '0;
    rvfi_rd_wdata[0] = '0;
    rvfi_rd_addr[1]  = '0;
    rvfi_rd_wdata[1] = '0;
    rvfi_rs1_addr    = '0;
    rvfi_rs2_addr    = '0;
    rvfi_rs3_addr    = '0;
    rvfi_rs1_rdata   = '0;
    rvfi_rs2_rdata   = '0;
    rvfi_rs3_rdata   = '0;
    rvfi_mem_addr    = '0;
    rvfi_mem_rmask   = '0;
    rvfi_mem_wmask   = '0;
    rvfi_mem_rdata   = '0;
    rvfi_mem_wdata   = '0;

    rvfi_mode        = 2'b11;  //priv_lvl_i; //TODO: correct this if needed

    $display("*****Starting update rvfi task*****\n");
    wait(clk_i_d == 1'b1);
    forever begin
      wait(clk_i_d == 1'b1);
      if (rvfi_trace_q.size() != 0) begin
        set_rvfi();
        rvfi_valid = 1'b1;
      end else begin
        rvfi_valid = 1'b0;
      end
      wait(clk_i_d == 1'b0);
    end
  endtask

  initial begin
    fork
      monitor_pipeline();
      compute_pipeline();
      update_rvfi();
    join
  end

endmodule  // cv32e40p_rvfi
