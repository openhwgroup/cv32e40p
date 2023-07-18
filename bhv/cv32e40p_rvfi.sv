// Copyright (c) 2020 OpenHW Group
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

// CV32E40P RVFI interface
//
// Contributors: Davide Schiavone, OpenHW Group <davide@openhwgroup.org>
//               Halfdan Bechmann, Silicon Labs <halfdan.bechmann@silabs.com>
//               Yoann Pruvost, Dolphin Design <yoann.pruvost@dolphin.fr>

`include "cv32e40p_rvfi_pkg.sv"

module cv32e40p_rvfi
  import cv32e40p_pkg::*;
  import cv32e40p_rvfi_pkg::*;
#(
    parameter FPU   = 0,
    parameter ZFINX = 0
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
    input logic [31:0]       operand_a_fw_id_i,
    input logic [31:0]       operand_b_fw_id_i,

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
    input logic [31:0][MHPMCOUNTER_WIDTH-1:0] csr_mhpmcounter_q_i,
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
    output logic [ 4:0] rvfi_rs1_addr,
    output logic [ 4:0] rvfi_rs2_addr,
    output logic [31:0] rvfi_rs1_rdata,
    output logic [31:0] rvfi_rs2_rdata,
    output logic [ 4:0] rvfi_frs1_addr,
    output logic [ 4:0] rvfi_frs2_addr,
    output logic        rvfi_frs1_rvalid,
    output logic        rvfi_frs2_rvalid,
    output logic [31:0] rvfi_frs1_rdata,
    output logic [31:0] rvfi_frs2_rdata,

    output logic [31:0] rvfi_pc_rdata,
    output logic [31:0] rvfi_pc_wdata,

    output logic [31:0] rvfi_mem_addr,
    output logic [ 3:0] rvfi_mem_rmask,
    output logic [ 3:0] rvfi_mem_wmask,
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

  logic pc_mux_debug;
  logic pc_mux_dret;
  logic pc_mux_exception;
  logic pc_mux_debug_exception;
  logic pc_mux_interrupt;
  logic pc_mux_nmi;

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

  function void empty_fifo();
    integer i, trace_q_size;
    trace_q_size = wb_bypass_trace_q.size();
    if (trace_q_size > 40) begin
      $fatal("Reorder queue too long\n");
    end
    if (trace_q_size != 0) begin
      for (i = 0; i < trace_q_size; i++) begin
        insn_trace_t new_rvfi_trace;
        new_rvfi_trace = new();
        new_rvfi_trace.copy_full(wb_bypass_trace_q.pop_front());
        if (next_send == new_rvfi_trace.m_order) begin
          rvfi_trace_q.push_back(new_rvfi_trace);
          next_send = next_send + 1;
        end else begin
          wb_bypass_trace_q.push_back(new_rvfi_trace);
        end
      end
    end
  endfunction
  /*
   * Function used to alocate a new insn and send it to the rvfi driver
   */
  function void send_rvfi(insn_trace_t m_wb_insn);
    insn_trace_t new_rvfi_trace;
    new_rvfi_trace = new();
    new_rvfi_trace.copy_full(m_wb_insn);
    if (next_send == new_rvfi_trace.m_order) begin
      rvfi_trace_q.push_back(new_rvfi_trace);
      next_send = next_send + 1;
      // empty_fifo();
    end else begin
      wb_bypass_trace_q.push_back(new_rvfi_trace);
    end
    empty_fifo();
  endfunction

  /*
   *
   */
  function void f_bypass_wb(insn_trace_t m_ex_insn);
    insn_trace_t new_rvfi_trace;
    new_rvfi_trace = new();
    new_rvfi_trace.copy_full(m_ex_insn);
    if (m_ex_insn.m_ex_fw) begin
      new_rvfi_trace.m_rd_addr  = m_ex_insn.m_rd_addr;
      new_rvfi_trace.m_rd_wdata = m_ex_insn.m_rd_wdata;
    end else begin
      new_rvfi_trace.m_rd_addr[0]  = '0;
      new_rvfi_trace.m_rd_wdata[0] = '0;
      new_rvfi_trace.m_rd_addr[1]  = '0;
      new_rvfi_trace.m_rd_wdata[1] = '0;
    end
    wb_bypass_trace_q.push_back(new_rvfi_trace);
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
  logic [31:0] r_previous_minstret;

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
    end


    //FOR DEBUG!!!!!!!!!!!!!!!!!!!!!!
    // if(new_rvfi_trace.m_order == 64'h0000_0000_0000_4423) begin
    //     new_rvfi_trace.m_csr.mcause_rdata = 32'h8000_0010;
    //     new_rvfi_trace.m_csr.mcause_wdata = 32'h8000_0010;
    //     new_rvfi_trace.m_csr.mstatus_rdata = 32'h0000_1888;
    //     new_rvfi_trace.m_csr.mstatus_wdata = 32'h0000_1888;
    //     new_rvfi_trace.m_csr.mepc_rdata = 32'h0000_554E;
    //     new_rvfi_trace.m_csr.mepc_wdata = 32'h0000_554E;
    // end

    rvfi_order    = new_rvfi_trace.m_order;
    rvfi_pc_rdata = new_rvfi_trace.m_pc_rdata;
    rvfi_insn     = new_rvfi_trace.m_insn;

    //Trying something here
    //Flag as trap everytime minstret is not incremented

    if (new_rvfi_trace.m_instret_cnt == r_previous_minstret) begin
      // new_rvfi_trace.m_trap = 1'b0;
      new_rvfi_trace.m_trap = 1'b1;
    end else begin
      r_previous_minstret   = new_rvfi_trace.m_instret_cnt;
      new_rvfi_trace.m_trap = 1'b0;
    end

    rvfi_rs1_addr    = '0;
    rvfi_rs1_rdata   = '0;
    rvfi_rs2_addr    = '0;
    rvfi_rs2_rdata   = '0;
    rvfi_frs1_rvalid = '0;
    rvfi_frs1_addr   = '0;
    rvfi_frs1_rdata  = '0;
    rvfi_frs2_rvalid = '0;
    rvfi_frs2_addr   = '0;
    rvfi_frs2_rdata  = '0;

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

    rvfi_frd_wvalid[0] = '0;
    rvfi_frd_addr[0]   = '0;
    rvfi_frd_wdata[0]  = '0;

    rvfi_frd_wvalid[1] = '0;
    rvfi_frd_addr[1]   = '0;
    rvfi_frd_wdata[1]  = '0;

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
    `SET_RVFI_CSR_FROM_INSN(mstatus)
    `SET_RVFI_CSR_FROM_INSN(misa)
    `SET_RVFI_CSR_FROM_INSN(mie)
    `SET_RVFI_CSR_FROM_INSN(mtvec)
    `SET_RVFI_CSR_FROM_INSN(mcountinhibit)
    `SET_RVFI_CSR_FROM_INSN(mscratch)
    `SET_RVFI_CSR_FROM_INSN(mepc)
    `SET_RVFI_CSR_FROM_INSN(mcause)
    `SET_RVFI_CSR_FROM_INSN(minstret)
    `SET_RVFI_CSR_FROM_INSN(mip)

    rvfi_csr_tdata_rdata[0]   = 'Z;
    rvfi_csr_tdata_rmask[0]   = '0;  // Does not exist
    rvfi_csr_tdata_wdata[0]   = 'Z;  // Does not exist
    rvfi_csr_tdata_wmask[0]   = '0;

    rvfi_csr_tdata_rdata[1]   = new_rvfi_trace.m_csr.tdata1_rdata;
    rvfi_csr_tdata_rmask[1]   = new_rvfi_trace.m_csr.tdata1_rmask;  //'1
    rvfi_csr_tdata_wdata[1]   = new_rvfi_trace.m_csr.tdata1_wdata;
    rvfi_csr_tdata_wmask[1]   = new_rvfi_trace.m_csr.tdata1_wmask;

    rvfi_csr_tdata_rmask[3:2] = '1;

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

  endfunction // set_rvfi

  int r_instret_cnt;
  function void minstret_to_id();
    trace_id.m_csr.minstret_we    = r_pipe_freeze_trace.csr.mhpmcounter_write_lower[2];
    trace_id.m_csr.minstret_rdata = r_pipe_freeze_trace.csr.mhpmcounter_q[2];
    trace_id.m_csr.minstret_rmask = '1;
    trace_id.m_csr.minstret_wdata = r_pipe_freeze_trace.csr.mhpmcounter_q;
    trace_id.m_csr.minstret_wmask = r_pipe_freeze_trace.csr.mhpmcounter_write_lower[2] ? '1 : '0;
    trace_id.m_instret_cnt        = r_instret_cnt;
  endfunction

  function void minstret_to_ex();
    trace_ex.m_csr.minstret_we    = r_pipe_freeze_trace.csr.mhpmcounter_write_lower[2];
    trace_ex.m_csr.minstret_rdata = r_pipe_freeze_trace.csr.mhpmcounter_q[2];
    trace_ex.m_csr.minstret_rmask = '1;
    trace_ex.m_csr.minstret_wdata = r_pipe_freeze_trace.csr.mhpmcounter_q;
    trace_ex.m_csr.minstret_wmask = r_pipe_freeze_trace.csr.mhpmcounter_write_lower[2] ? '1 : '0;
    trace_ex.m_instret_cnt        = r_instret_cnt;
  endfunction

  function void tinfo_to_id();
    trace_id.m_csr.tinfo_we    = '0; // READ ONLY csr_tinfo_we_i;
    trace_id.m_csr.tinfo_rdata = r_pipe_freeze_trace.csr.tinfo_q;
    trace_id.m_csr.tinfo_rmask = '1;
    trace_id.m_csr.tinfo_wdata = r_pipe_freeze_trace.csr.tinfo_n;
    trace_id.m_csr.tinfo_wmask = '0;
  endfunction

  function void tinfo_to_ex();
    trace_ex.m_csr.tinfo_we    = '0; // READ ONLY csr_tinfo_we_i;
    trace_ex.m_csr.tinfo_rdata = r_pipe_freeze_trace.csr.tinfo_q;
    trace_ex.m_csr.tinfo_rmask = '1;
    trace_ex.m_csr.tinfo_wdata = r_pipe_freeze_trace.csr.tinfo_n;
    trace_ex.m_csr.tinfo_wmask = '0;
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

  function void mstatus_to_id();
    trace_id.m_csr.mstatus_we    = r_pipe_freeze_trace.csr.mstatus_we;
    trace_id.m_csr.mstatus_rdata = r_pipe_freeze_trace.csr.mstatus_full_q;
    trace_id.m_csr.mstatus_rmask = '1;
    trace_id.m_csr.mstatus_wdata = r_pipe_freeze_trace.csr.mstatus_full_n;
    trace_id.m_csr.mstatus_wmask = r_pipe_freeze_trace.csr.mstatus_we ? '1 : '0;
  endfunction

  function void dcsr_to_id();
    trace_id.m_csr.dcsr_we    = r_pipe_freeze_trace.csr.dcsr_we;
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
        trace_if.m_trap = 1'b1;
      end
    end

    if (s_was_flush == 1'b0) begin
      s_dbg_exception = 1'b0;
    end

    if (r_pipe_freeze_trace.pc_id == trace_if.m_pc_rdata) begin
      if (trace_if.m_valid && (s_dbg_exception || s_exception)) begin
        trace_if.m_trap = 1'b1;
      end
    end

    if (r_pipe_freeze_trace.pc_id == trace_ex.m_pc_rdata) begin
      if (trace_ex.m_valid && (s_dbg_exception || s_exception)) begin
        trace_ex.m_trap = 1'b1;
      end
    end

    if (r_pipe_freeze_trace.pc_id == trace_wb.m_pc_rdata) begin
      if (trace_wb.m_valid && (s_dbg_exception || s_exception)) begin
        trace_wb.m_trap = 1'b1;
      end
    end

    if (r_pipe_freeze_trace.pc_id == trace_id.m_pc_rdata) begin
      if (trace_id.m_valid && (s_dbg_exception || s_exception)) begin
        trace_id.m_trap = 1'b1;
      end
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
  `define CSR_FROM_PIPE(TRACE_NAME,
                        CSR_NAME) \
    trace_``TRACE_NAME``.m_csr.``CSR_NAME``_we      = r_pipe_freeze_trace.csr.``CSR_NAME``_we; \
    trace_``TRACE_NAME``.m_csr.``CSR_NAME``_rdata   = r_pipe_freeze_trace.csr.``CSR_NAME``_q; \
    trace_``TRACE_NAME``.m_csr.``CSR_NAME``_rmask   = '1; \
    trace_``TRACE_NAME``.m_csr.``CSR_NAME``_wdata   = r_pipe_freeze_trace.csr.``CSR_NAME``_n; \
    trace_``TRACE_NAME``.m_csr.``CSR_NAME``_wmask   = r_pipe_freeze_trace.csr.``CSR_NAME``_we ? '1 : '0;

  //those event are for debug purpose
  event e_dev_send_wb_1, e_dev_send_wb_2;
  event e_dev_commit_rf_to_ex_1, e_dev_commit_rf_to_ex_2, e_dev_commit_rf_to_ex_3;
  event e_if_2_id_1, e_if_2_id_2;
  event e_ex_to_wb_1, e_ex_to_wb_2;
  event e_id_to_ex_1, e_id_to_ex_2;
  event e_commit_dpc;

  event e_send_rvfi_trace_apu_resp;
  event e_send_rvfi_trace_ex_1, e_send_rvfi_trace_ex_2, e_send_rvfi_trace_ex_3, e_send_rvfi_trace_ex_4;
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

    trace_apu_resp.m_csr.mstatus_we    = r_pipe_freeze_trace.csr.mstatus_we;
    trace_apu_resp.m_csr.mstatus_rdata = r_pipe_freeze_trace.csr.mstatus_full_q;
    trace_apu_resp.m_csr.mstatus_rmask = '1;
    trace_apu_resp.m_csr.mstatus_wdata = r_pipe_freeze_trace.csr.mstatus_full_n;
    trace_apu_resp.m_csr.mstatus_wmask = r_pipe_freeze_trace.csr.mstatus_we ? '1 : '0;
  endfunction

  function void csr_to_apu_req();
    `CSR_FROM_PIPE(apu_req, misa)
    `CSR_FROM_PIPE(apu_req, tdata1)
    trace_apu_req.m_csr.tinfo_we    = '0; // READ ONLY csr_tinfo_we_i;
    trace_apu_req.m_csr.tinfo_rdata = r_pipe_freeze_trace.csr.tinfo_q;
    trace_apu_req.m_csr.tinfo_rmask = '1;
    trace_apu_req.m_csr.tinfo_wdata = r_pipe_freeze_trace.csr.tinfo_n;
    trace_apu_req.m_csr.tinfo_wmask = '0;


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
        send_rvfi(trace_apu_resp);
        ->e_send_rvfi_trace_apu_resp;
      end
    end
  endfunction

  task compute_pipeline();
    bit s_new_valid_insn;
    bit s_ex_valid_adjusted;
    bit s_wb_valid_adjusted;

    bit s_id_done;

    bit s_apu_wb_ok;
    bit s_apu_0_cycle_reps;

    bit s_fflags_we_non_apu;
    bit s_frm_we_non_apu;
    bit s_is_pc_set;  //If pc_set, wait until next trace_id to commit csr changes
    bit s_is_irq_start;

    bit s_skip_wb;  // used to skip wb monitoring when apu resp and not lsu
    bit s_increase_instret_1;
    bit s_increase_instret_2;

    bit s_test_for_dret;

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

    r_previous_minstret  = -1;

    s_is_pc_set          = 1'b0;
    s_is_irq_start       = 1'b0;

    s_is_pc_set          = 1'b0;
    s_is_irq_start       = 1'b0;
    s_skip_wb            = 1'b0;

    r_instret_cnt        = 0;
    s_increase_instret_1 = 1'b0;
    s_increase_instret_2 = 1'b0;

    s_test_for_dret = 1'b0;

    $display("*****Starting pipeline computing*****\n");
    forever begin
      wait(e_pipe_monitor_ok.triggered); // event triggered
      #1;

      check_trap();

      if (s_increase_instret_2) begin
        r_instret_cnt = r_instret_cnt + 1;
      end
      s_increase_instret_2 = s_increase_instret_1;
      s_increase_instret_1 = r_pipe_freeze_trace.minstret;

      pc_mux_interrupt = 1'b0;
      if (r_pipe_freeze_trace.pc_mux == 4'b0100) begin
        if (r_pipe_freeze_trace.exc_pc_mux == 3'b001) begin
          pc_mux_interrupt = 1'b1;
          s_is_irq_start   = 1'b1;
        end
      end

      if (r_pipe_freeze_trace.ctrl_fsm_cs == DBG_TAKEN_ID && r_pipe_freeze_trace.ebrk_insn_dec) begin
        if (trace_wb.m_valid) begin
          send_rvfi(trace_wb);
          trace_wb.m_valid = 1'b0;
          ->e_send_rvfi_trace_wb_1;
        end
        if (trace_ex.m_valid) begin
          send_rvfi(trace_ex);
          trace_ex.m_valid = 1'b0;
          ->e_send_rvfi_trace_ex_1;
        end
        if (trace_id.m_valid) begin

          minstret_to_id();
          `CSR_FROM_PIPE(id, misa)
          `CSR_FROM_PIPE(id, tdata1)
          tinfo_to_id();
          `CSR_FROM_PIPE(id, mip)
          send_rvfi(trace_id);
          trace_id.m_valid = 1'b0;
          ->e_send_rvfi_trace_id_1;
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
        minstret_to_ex();
        trace_ex.m_csr.got_minstret = '1;
      end

      if (trace_wb.m_valid & trace_wb.m_is_apu & (trace_wb.m_apu_req_id == cnt_apu_resp)) begin
        s_apu_wb_ok = 1'b1;
      end else begin
        s_apu_wb_ok = 1'b0;
      end

      s_new_valid_insn = r_pipe_freeze_trace.id_valid && r_pipe_freeze_trace.is_decoding;// && !r_pipe_freeze_trace.apu_rvalid;

      s_wb_valid_adjusted = r_pipe_freeze_trace.wb_valid && ((r_pipe_freeze_trace.ctrl_fsm_cs == DECODE) || (r_pipe_freeze_trace.ctrl_fsm_cs == FLUSH_EX) || (r_pipe_freeze_trace.ctrl_fsm_cs == DECODE_HWLOOP));// && !r_pipe_freeze_trace.apu_rvalid;;

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

      //WB_STAGE
      s_skip_wb = 1'b0;
      if (r_pipe_freeze_trace.apu_rvalid && (apu_trace_q.size() > 0)) begin
        apu_resp();
        if (!r_pipe_freeze_trace.data_rvalid) begin
          s_skip_wb = 1'b1;
        end
      end
      if (trace_wb.m_valid && !s_skip_wb) begin
        if (r_pipe_freeze_trace.rf_we_wb) begin
          if((trace_wb.m_rd_addr[0] == r_pipe_freeze_trace.rf_addr_wb) && (cnt_data_resp == trace_wb.m_mem_req_id[0])) begin
            trace_wb.m_rd_addr[0]  = r_pipe_freeze_trace.rf_addr_wb;
            trace_wb.m_rd_wdata[0] = r_pipe_freeze_trace.rf_wdata_wb;
          end else if (trace_wb.m_2_rd_insn && (trace_wb.m_rd_addr[1] == r_pipe_freeze_trace.rf_addr_wb) && (cnt_data_resp == trace_wb.m_mem_req_id[0])) begin
            trace_wb.m_rd_addr[1]  = r_pipe_freeze_trace.rf_addr_wb;
            trace_wb.m_rd_wdata[1] = r_pipe_freeze_trace.rf_wdata_wb;
          end
        end

        if (!trace_wb.m_data_missaligned) begin
          send_rvfi(trace_wb);
          ->e_dev_send_wb_1;
          ->e_send_rvfi_trace_wb_2;
          trace_wb.m_valid = 1'b0;
        end else begin
          if (s_wb_valid_adjusted) begin
            if (r_pipe_freeze_trace.rf_we_wb) begin
              if (!trace_wb.m_ex_fw) begin
                trace_wb.m_rd_addr[0]  = r_pipe_freeze_trace.rf_addr_wb;
                trace_wb.m_rd_wdata[0] = r_pipe_freeze_trace.rf_wdata_wb;
              end
              if (trace_wb.m_data_missaligned && !trace_wb.m_got_first_data) begin
                trace_wb.m_got_first_data = 1'b1;
              end else begin
                send_rvfi(trace_wb);
                ->e_dev_send_wb_2;
                ->e_send_rvfi_trace_wb_3;
                trace_wb.m_valid = 1'b0;
              end
            end // rf_we_wb
          end
        end
      end

      if (trace_ex.m_valid) begin

        `CSR_FROM_PIPE(ex, misa)
        `CSR_FROM_PIPE(ex, tdata1)
        tinfo_to_ex();

        if(r_pipe_freeze_trace.rf_we_wb) begin
          if(cnt_data_resp == trace_ex.m_mem_req_id[0]) begin
            trace_ex.m_rd_addr[0]  = r_pipe_freeze_trace.rf_addr_wb;
            trace_ex.m_rd_wdata[0] = r_pipe_freeze_trace.rf_wdata_wb;
          end else if (cnt_data_resp == trace_ex.m_mem_req_id[1]) begin
            trace_ex.m_rd_addr[1]  = r_pipe_freeze_trace.rf_addr_wb;
            trace_ex.m_rd_wdata[1] = r_pipe_freeze_trace.rf_wdata_wb;
            trace_ex.m_got_first_data = 1'b1;
          end
        end

        if (s_wb_valid_adjusted) begin
          if (trace_wb.m_valid) begin
            send_rvfi(trace_ex);
            trace_ex.m_valid = 1'b0;
            ->e_send_rvfi_trace_ex_2;
          end else begin
            if (r_pipe_freeze_trace.rf_we_wb) begin
              ->e_dev_commit_rf_to_ex_1;
              if (trace_ex.m_got_ex_reg) begin
                trace_ex.m_rd_addr[1]  = r_pipe_freeze_trace.rf_addr_wb;
                trace_ex.m_rd_wdata[1] = r_pipe_freeze_trace.rf_wdata_wb;
                trace_ex.m_2_rd_insn   = 1'b1;
              end else begin
                trace_ex.m_rd_addr[0] = r_pipe_freeze_trace.rf_addr_wb;
                trace_ex.m_rd_wdata[0] = r_pipe_freeze_trace.rf_wdata_wb;
                trace_ex.m_got_first_data = 1'b1;
              end
            end

            if (!s_ex_valid_adjusted & !trace_ex.m_csr.got_minstret) begin
              minstret_to_ex();
            end
            ->e_ex_to_wb_1;
            trace_wb.move_down_pipe(trace_ex);
            trace_ex.m_valid = 1'b0;
          end
        end else if (r_pipe_freeze_trace.rf_we_wb) begin
          ->e_dev_commit_rf_to_ex_2;
          if (trace_ex.m_got_ex_reg) begin
            trace_ex.m_rd_addr[1]  = r_pipe_freeze_trace.rf_addr_wb;
            trace_ex.m_rd_wdata[1] = r_pipe_freeze_trace.rf_wdata_wb;
            trace_ex.m_2_rd_insn   = 1'b1;
          end else begin
            trace_ex.m_rd_addr[0] = r_pipe_freeze_trace.rf_addr_wb;
            trace_ex.m_rd_wdata[0] = r_pipe_freeze_trace.rf_wdata_wb;
            trace_ex.m_got_first_data = 1'b1;
          end
        end
      end

      s_ex_valid_adjusted = (r_pipe_freeze_trace.ex_valid || s_test_for_dret) && ((r_pipe_freeze_trace.ctrl_fsm_cs == DECODE) || (r_pipe_freeze_trace.ctrl_fsm_cs == DECODE_HWLOOP)) && (!r_pipe_freeze_trace.apu_rvalid || r_pipe_freeze_trace.data_req_ex);
      s_test_for_dret = r_pipe_freeze_trace.ex_valid && r_pipe_freeze_trace.ctrl_fsm_cs == DBG_TAKEN_IF;
      //EX_STAGE
      if (trace_id.m_valid) begin
        mtvec_to_id();

        `CSR_FROM_PIPE(id, mip)

        if (!csr_is_irq && !s_is_irq_start) begin
          mstatus_to_id();
          `CSR_FROM_PIPE(id, mepc)
          if (trace_id.m_csr.mcause_we == '0) begin  //for debug purpose
            `CSR_FROM_PIPE(id, mcause)
          end
        end

        `CSR_FROM_PIPE(id, mcountinhibit)
        `CSR_FROM_PIPE(id, mscratch)
        `CSR_FROM_PIPE(id, mie)

        `CSR_FROM_PIPE(id, fflags)
        `CSR_FROM_PIPE(id, frm)
        `CSR_FROM_PIPE(id, fcsr)

        if (r_pipe_freeze_trace.csr.we) begin
            `CSR_FROM_PIPE(id, dpc)
        end
        if (s_fflags_we_non_apu) begin
          trace_id.m_fflags_we_non_apu = 1'b1;
        end

        if (s_frm_we_non_apu) begin
          trace_id.m_frm_we_non_apu = 1'b1;
        end
        trace_ex.m_csr.fflags_wmask = '0;
        trace_ex.m_csr.frm_wmask    = '0;
        trace_ex.m_csr.fcsr_wmask   = '0;

        if (r_pipe_freeze_trace.apu_req) begin
          trace_id.m_is_apu = 1'b1;
          trace_id.m_apu_req_id = cnt_apu_req;
          trace_apu_req = new();
          trace_apu_req.copy_full(trace_id);
          csr_to_apu_req();
          if(s_increase_instret_2) begin
            trace_apu_req.m_instret_cnt = r_instret_cnt + 1;
          end else begin
            trace_apu_req.m_instret_cnt = r_instret_cnt;
          end
          trace_apu_req.set_to_apu();
          apu_trace_q.push_back(trace_apu_req);
          trace_id.m_valid = 1'b0;

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
          if (r_pipe_freeze_trace.ex_reg_we && !r_pipe_freeze_trace.apu_rvalid) begin
            trace_id.m_ex_fw    = 1'b1;
            trace_id.m_rd_addr[0]  = r_pipe_freeze_trace.ex_reg_addr;
            trace_id.m_rd_wdata[0] = r_pipe_freeze_trace.ex_reg_wdata;
            trace_id.m_got_ex_reg = 1'b1;
          end else if (!trace_ex.m_valid & r_pipe_freeze_trace.rf_we_wb & !trace_id.m_ex_fw) begin
            trace_id.m_rd_addr[0]  = r_pipe_freeze_trace.rf_addr_wb;
            trace_id.m_rd_wdata[0] = r_pipe_freeze_trace.rf_wdata_wb;
          end

          if (r_pipe_freeze_trace.data_req_ex) begin
            cnt_data_req = cnt_data_req + 1;
            trace_id.m_is_memory = 1'b1;
            trace_id.m_mem_req_id[0] = cnt_data_req;

            trace_id.m_mem.addr = r_pipe_freeze_trace.data_addr_pmp;
            if (r_pipe_freeze_trace.data_misaligned) begin
              cnt_data_req = cnt_data_req + 1;
            end
            if (!r_pipe_freeze_trace.data_we_ex) begin
              trace_id.m_is_load = 1'b1;
              if (r_pipe_freeze_trace.data_misaligned) begin
                trace_id.m_data_missaligned = 1'b1;
                trace_id.m_mem_req_id[1] = trace_id.m_mem_req_id[0];
                trace_id.m_mem_req_id[0] = cnt_data_req;
              end
            end
          end
          ->e_id_to_ex_1;
          hwloop_to_id();
          trace_ex.move_down_pipe(trace_id);  // The instruction moves forward from ID to EX
          trace_id.m_valid = 1'b0;
          ->e_id_to_ex_1;

        end else if (r_pipe_freeze_trace.ex_reg_we) begin
          trace_id.m_ex_fw          = 1'b1;
          trace_id.m_rd_addr[0]     = r_pipe_freeze_trace.ex_reg_addr;
          trace_id.m_rd_wdata[0]    = r_pipe_freeze_trace.ex_reg_wdata;
          trace_id.m_got_ex_reg     = 1'b1;
          trace_id.m_got_regs_write = 1'b1;
        end
      end

      //ID_STAGE
      if (s_new_valid_insn) begin  // There is a new valid instruction
        if (trace_id.m_valid) begin
          if (trace_ex.m_valid) begin
            minstret_to_ex();
            if (trace_wb.m_valid) begin
              send_rvfi(trace_ex);
              ->e_send_rvfi_trace_ex_4;
            end else begin
              ->e_ex_to_wb_2;
              trace_wb.move_down_pipe(trace_ex);
            end
            trace_ex.m_valid = 1'b0;
          end
          if (r_pipe_freeze_trace.data_req_ex) begin
            cnt_data_req = cnt_data_req + 1;
            trace_id.m_is_memory = 1'b1;
            trace_id.m_mem_req_id[0] = cnt_data_req;

            trace_id.m_mem.addr = r_pipe_freeze_trace.data_addr_pmp;
            if (r_pipe_freeze_trace.data_misaligned) begin
              cnt_data_req = cnt_data_req + 1;
            end
            if (!r_pipe_freeze_trace.data_we_ex) begin
              trace_id.m_is_load = 1'b1;
              if (r_pipe_freeze_trace.data_misaligned) begin
                trace_id.m_data_missaligned = 1'b1;
                trace_id.m_mem_req_id[1] = trace_id.m_mem_req_id[0];
                trace_id.m_mem_req_id[0] = cnt_data_req;
              end
            end
          end else if (r_pipe_freeze_trace.rf_we_wb && !r_pipe_freeze_trace.ex_reg_we) begin
            trace_id.m_rd_addr[0]  = r_pipe_freeze_trace.rf_addr_wb;
            trace_id.m_rd_wdata[0] = r_pipe_freeze_trace.rf_wdata_wb;
          end

          hwloop_to_id();
          trace_ex.move_down_pipe(trace_id);
          trace_id.m_valid = 1'b0;
          ->e_id_to_ex_2;
        end
        trace_id.init(trace_if);
        trace_id.m_is_ebreak  = trace_if.m_is_ebreak;
        trace_id.m_is_illegal = r_pipe_freeze_trace.is_illegal;
        s_is_pc_set           = 1'b0;
        s_is_irq_start        = 1'b0;
        trace_if.m_valid      = 1'b0;
        s_id_done             = 1'b0;

        csrId_to_id();

        `CSR_FROM_PIPE(id, dscratch0)
        `CSR_FROM_PIPE(id, dscratch1)
        mstatus_to_id();

        `CSR_FROM_PIPE(id, dpc)
        ->e_if_2_id_1;
      end else begin
        if (trace_id.m_valid) begin
          `CSR_FROM_PIPE(id, dscratch0)
          `CSR_FROM_PIPE(id, dscratch1)
        end
      end

      //IF_STAGE

      if (r_pipe_freeze_trace.if_valid && r_pipe_freeze_trace.if_ready) begin
        if(trace_if.m_valid && r_pipe_freeze_trace.id_valid && r_pipe_freeze_trace.id_ready && !trace_id.m_valid && r_pipe_freeze_trace.ebrk_insn_dec) begin
          trace_id.init(trace_if);
          trace_id.m_is_ebreak  = '1;  //trace_if.m_is_ebreak;
          trace_id.m_is_illegal = r_pipe_freeze_trace.is_illegal;
          s_is_pc_set           = 1'b0;
          s_is_irq_start        = 1'b0;
          trace_if.m_valid      = 1'b0;
          s_id_done             = 1'b0;
          `CSR_FROM_PIPE(id, dpc)
          ->e_if_2_id_2;
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
      end

      if (!s_id_done) begin
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
    rvfi_rs1_rdata   = '0;
    rvfi_rs2_rdata   = '0;
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
