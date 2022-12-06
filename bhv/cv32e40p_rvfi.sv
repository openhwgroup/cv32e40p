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
// Contributors: Davide Schiavone <davide@openhwgroup.org>
//               Halfdan Bechmann <halfdan.bechmann@silabs.com>
//               Yoann Pruvost <yoann.pruvost@dolphin.fr>
import cv32e40p_pkg::*;
typedef struct packed {
  logic [31:28] xdebugver;
  logic [27:16] zero2;
  logic ebreakm;
  logic zero1;
  logic ebreaks;
  logic ebreaku;
  logic stepie;
  logic stopcount;
  logic stoptime;
  logic [8:6] cause;
  logic zero0;
  logic mprven;
  logic nmip;
  logic step;
  PrivLvl_t prv;
} Dcsr_t;

typedef struct packed {
  logic uie;
  // logic sie;      - unimplemented, hardwired to '0
  // logic hie;      - unimplemented, hardwired to '0
  logic mie;
  logic upie;
  // logic spie;     - unimplemented, hardwired to '0
  // logic hpie;     - unimplemented, hardwired to '0
  logic mpie;
  // logic spp;      - unimplemented, hardwired to '0
  // logic[1:0] hpp; - unimplemented, hardwired to '0
  PrivLvl_t mpp;
  logic mprv;
} Status_t;

`include "cv32e40p_rvfi_pkg.sv"

module cv32e40p_rvfi
  import cv32e40p_pkg::*;
  import cv32e40p_rvfi_pkg::*;
(
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

    input logic        debug_csr_save_i,
    // LSU
    input logic        lsu_en_id_i,
    input logic        lsu_we_id_i,
    input logic [ 1:0] lsu_size_id_i,
    // Register reads
    input logic [ 4:0] rs1_addr_id_i,
    input logic [ 4:0] rs2_addr_id_i,
    input logic [31:0] operand_a_fw_id_i,
    input logic [31:0] operand_b_fw_id_i,

    //// EX probes ////

    // Register writes in EX
    input logic ex_ready_i,
    input logic ex_valid_i,

    input logic        ex_reg_we_i,
    input logic [ 4:0] ex_reg_addr_i,
    input logic [31:0] ex_reg_wdata_i,

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
    input logic [ 4:0] rf_addr_wb_i,
    input logic [31:0] rf_wdata_wb_i,
    // LSU
    input logic [31:0] lsu_rdata_wb_i,
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

    output logic [ 4:0] rvfi_rd_addr,
    output logic [31:0] rvfi_rd_wdata,
    output logic [ 4:0] rvfi_rs1_addr,
    output logic [ 4:0] rvfi_rs2_addr,
    output logic [31:0] rvfi_rs1_rdata,
    output logic [31:0] rvfi_rs2_rdata,

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
    output logic [31:0] rvfi_csr_mconfigptr_wdata
);


  bit clk_i_d;
  assign #0.01 clk_i_d = clk_i;

  logic pc_mux_debug;
  logic pc_mux_dret;
  logic pc_mux_exception;
  logic pc_mux_debug_exception;
  logic pc_mux_interrupt;
  logic pc_mux_nmi;


  /*
   * This struct is used to store all information comming from the core at every posedge
   * The information will then be processed
   */
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

    logic [5:0] csr_cause;

    logic debug_csr_save;
    // LSU
    logic lsu_en_id;
    logic lsu_we_id;
    logic [1:0] lsu_size_id;
    // Register reads
    logic [4:0] rs1_addr_id;
    logic [4:0] rs2_addr_id;
    logic [31:0] operand_a_fw_id;
    logic [31:0] operand_b_fw_id;

    //// EX probes ////

    // Register writes in EX
    logic ex_ready;
    logic ex_valid;

    logic ex_reg_we;
    logic [4:0] ex_reg_addr;
    logic [31:0] ex_reg_wdata;

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
    logic [4:0] rf_addr_wb;
    logic [31:0] rf_wdata_wb;
    // LSU
    logic [31:0] lsu_rdata_wb;
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

    struct {
      //// CSR Probes ////
      csr_num_e addr;
      logic we;
      logic [31:0] wdata_int;

      logic mstatus_we;
      logic misa_we;
      logic mtvec_we;
      logic mscratch_we;
      logic mepc_we;
      logic mcause_we;
      logic dcsr_we;

      logic jvt_we;
      Status_t mstatus_n;
      Status_t mstatus_q;
      logic [31:0] mstatus_full_n;
      logic [31:0] mstatus_full_q;

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
    } csr;
  } pipe_t;

  pipe_t r_pipe_freeze;

  event  e_pipe_monitor_ok;

  // Compute each CSR write enable
  function compute_csr_we();
    r_pipe_freeze.csr.mstatus_we  = 1'b0;
    r_pipe_freeze.csr.misa_we     = 1'b0;
    r_pipe_freeze.csr.mtvec_we    = 1'b0;
    r_pipe_freeze.csr.mscratch_we = 1'b0;
    r_pipe_freeze.csr.mepc_we     = 1'b0;
    r_pipe_freeze.csr.mcause_we   = 1'b0;
    r_pipe_freeze.csr.dcsr_we     = 1'b0;

    if (r_pipe_freeze.csr.we) begin
      case (r_pipe_freeze.csr.addr)
        CSR_MSTATUS:  r_pipe_freeze.csr.mstatus_we = 1'b1;
        CSR_MISA:     r_pipe_freeze.csr.misa_we = 1'b1;
        CSR_MTVEC:    r_pipe_freeze.csr.mtvec_we = 1'b1;
        CSR_MSCRATCH: r_pipe_freeze.csr.mscratch_we = 1'b1;
        CSR_MEPC:     r_pipe_freeze.csr.mepc_we = 1'b1;
        CSR_MCAUSE:   r_pipe_freeze.csr.mcause_we = 1'b1;
        CSR_DCSR:     r_pipe_freeze.csr.dcsr_we = 1'b1;
      endcase
    end
    // CSR_MCAUSE:   r_pipe_freeze.csr.mcause_we = r_pipe_freeze.csr.mcause_n != r_pipe_freeze.csr.mcause_q; //for debug purpose
  endfunction
  /*
   * At negedge we buffer all signals form rtl
   * The rest of the tracer will work from those buffered signals
   */
  task monitor_pipeline();
    $display("*****Starting pipeline monitoring*****\n");
    forever begin
      wait(clk_i_d == 1'b0 & rst_ni == 1'b1);
      // r_pipe_freeze. <= ;

      r_pipe_freeze.instr_req                   = instr_req_i;
      r_pipe_freeze.instr_grant                 = instr_grant_i;
      r_pipe_freeze.instr_rvalid                = instr_rvalid_i;
      r_pipe_freeze.is_decoding                 = is_decoding_i;
      r_pipe_freeze.is_illegal                  = is_illegal_i;
      r_pipe_freeze.trigger_match               = trigger_match_i;
      r_pipe_freeze.data_misaligned             = data_misaligned_i;
      r_pipe_freeze.lsu_data_we_ex              = lsu_data_we_ex_i;

      r_pipe_freeze.debug_mode                  = debug_mode_i;
      r_pipe_freeze.debug_cause                 = debug_cause_i;
      r_pipe_freeze.prefetch_req                = prefetch_req_i;
      r_pipe_freeze.pc_set                      = pc_set_i;
      //// IF probes ////
      r_pipe_freeze.if_valid                    = if_valid_i;
      r_pipe_freeze.if_ready                    = if_ready_i;
      r_pipe_freeze.instr_valid_if              = instr_valid_if_i;
      r_pipe_freeze.instr_if                    = instr_if_i;
      r_pipe_freeze.pc_if                       = pc_if_i;
      r_pipe_freeze.instr_pmp_err_if            = instr_pmp_err_if_i;

      r_pipe_freeze.instr_valid_id              = instr_valid_id_i;
      r_pipe_freeze.instr_rdata_id              = instr_rdata_id_i;
      r_pipe_freeze.is_fetch_failed_id          = is_fetch_failed_id_i;
      r_pipe_freeze.instr_req_int               = instr_req_int_i;
      r_pipe_freeze.clear_instr_valid           = clear_instr_valid_i;
      //// ID probes ////
      r_pipe_freeze.pc_id                       = pc_id_i;
      r_pipe_freeze.id_valid                    = id_valid_i;

      r_pipe_freeze.id_ready                    = id_ready_i;
      r_pipe_freeze.rf_re_id                    = rf_re_id_i;
      r_pipe_freeze.sys_en_id                   = sys_en_id_i;
      r_pipe_freeze.sys_mret_insn_id            = sys_mret_insn_id_i;
      r_pipe_freeze.jump_in_id                  = jump_in_id_i;
      r_pipe_freeze.jump_target_id              = jump_target_id_i;
      r_pipe_freeze.is_compressed_id            = is_compressed_id_i;
      r_pipe_freeze.ebrk_insn_dec               = ebrk_insn_dec_i;
      r_pipe_freeze.csr_cause                   = csr_cause_i;
      r_pipe_freeze.debug_csr_save              = debug_csr_save_i;
      // LSU
      r_pipe_freeze.lsu_en_id                   = lsu_en_id_i;
      r_pipe_freeze.lsu_we_id                   = lsu_we_id_i;
      r_pipe_freeze.lsu_size_id                 = lsu_size_id_i;
      // Register reads
      r_pipe_freeze.rs1_addr_id                 = rs1_addr_id_i;
      r_pipe_freeze.rs2_addr_id                 = rs2_addr_id_i;
      r_pipe_freeze.operand_a_fw_id             = operand_a_fw_id_i;
      r_pipe_freeze.operand_b_fw_id             = operand_b_fw_id_i;

      //// EX probes ////

      // Register writes in EX
      r_pipe_freeze.ex_ready                    = ex_ready_i;
      r_pipe_freeze.ex_valid                    = ex_valid_i;

      r_pipe_freeze.ex_reg_we                   = ex_reg_we_i;
      r_pipe_freeze.ex_reg_addr                 = ex_reg_addr_i;
      r_pipe_freeze.ex_reg_wdata                = ex_reg_wdata_i;

      r_pipe_freeze.branch_in_ex                = branch_in_ex_i;
      r_pipe_freeze.branch_decision_ex          = branch_decision_ex_i;
      r_pipe_freeze.dret_in_ex                  = dret_in_ex_i;
      // LSU
      r_pipe_freeze.lsu_en_ex                   = lsu_en_ex_i;
      r_pipe_freeze.lsu_pmp_err_ex              = lsu_pmp_err_ex_i;
      r_pipe_freeze.lsu_pma_err_atomic_ex       = lsu_pma_err_atomic_ex_i;

      r_pipe_freeze.branch_target_ex            = branch_target_ex_i;

      r_pipe_freeze.data_addr_ex                = data_addr_ex_i;
      r_pipe_freeze.data_wdata_ex               = data_wdata_ex_i;
      r_pipe_freeze.lsu_split_q_ex              = lsu_split_q_ex_i;

      //// WB probes ////
      r_pipe_freeze.pc_wb                       = pc_wb_i;
      r_pipe_freeze.wb_ready                    = wb_ready_i;
      r_pipe_freeze.wb_valid                    = wb_valid_i;
      r_pipe_freeze.ebreak_in_wb                = ebreak_in_wb_i;
      r_pipe_freeze.instr_rdata_wb              = instr_rdata_wb_i;
      r_pipe_freeze.csr_en_wb                   = csr_en_wb_i;
      r_pipe_freeze.sys_wfi_insn_wb             = sys_wfi_insn_wb_i;
      // Register writes
      r_pipe_freeze.rf_we_wb                    = rf_we_wb_i;
      r_pipe_freeze.rf_addr_wb                  = rf_addr_wb_i;
      r_pipe_freeze.rf_wdata_wb                 = rf_wdata_wb_i;
      // LSU
      r_pipe_freeze.lsu_rdata_wb                = lsu_rdata_wb_i;
      // PC //
      r_pipe_freeze.branch_addr_n               = branch_addr_n_i;

      // Controller FSM probes
      r_pipe_freeze.ctrl_fsm_cs                 = ctrl_fsm_cs_i;
      r_pipe_freeze.pc_mux                      = pc_mux_i;
      r_pipe_freeze.exc_pc_mux                  = exc_pc_mux_i;

      // CSR
      r_pipe_freeze.csr.addr                    = csr_addr_i;
      r_pipe_freeze.csr.we                      = csr_we_i;
      r_pipe_freeze.csr.wdata_int               = csr_wdata_int_i;

      r_pipe_freeze.csr.jvt_we                  = csr_jvt_we_i;
      r_pipe_freeze.csr.mstatus_n               = csr_mstatus_n_i;
      r_pipe_freeze.csr.mstatus_q               = csr_mstatus_q_i;

      r_pipe_freeze.csr.mstatus_full_q[31:18]   = '0;
      r_pipe_freeze.csr.mstatus_full_q[17]      = r_pipe_freeze.csr.mstatus_q.mprv;
      r_pipe_freeze.csr.mstatus_full_q[16:13]   = '0;
      r_pipe_freeze.csr.mstatus_full_q[12:11]   = r_pipe_freeze.csr.mstatus_q.mpp;
      r_pipe_freeze.csr.mstatus_full_q[10:8]    = '0;
      r_pipe_freeze.csr.mstatus_full_q[7]       = r_pipe_freeze.csr.mstatus_q.mpie;
      r_pipe_freeze.csr.mstatus_full_q[6:5]     = '0;
      r_pipe_freeze.csr.mstatus_full_q[4]       = r_pipe_freeze.csr.mstatus_q.upie;
      r_pipe_freeze.csr.mstatus_full_q[3]       = r_pipe_freeze.csr.mstatus_q.mie;
      r_pipe_freeze.csr.mstatus_full_q[2:1]     = '0;
      r_pipe_freeze.csr.mstatus_full_q[0]       = r_pipe_freeze.csr.mstatus_q.uie;

      r_pipe_freeze.csr.mstatus_full_n[31:18]   = '0;
      r_pipe_freeze.csr.mstatus_full_n[17]      = r_pipe_freeze.csr.mstatus_n.mprv;
      r_pipe_freeze.csr.mstatus_full_n[16:13]   = '0;
      r_pipe_freeze.csr.mstatus_full_n[12:11]   = r_pipe_freeze.csr.mstatus_n.mpp;
      r_pipe_freeze.csr.mstatus_full_n[10:8]    = '0;
      r_pipe_freeze.csr.mstatus_full_n[7]       = r_pipe_freeze.csr.mstatus_n.mpie;
      r_pipe_freeze.csr.mstatus_full_n[6:5]     = '0;
      r_pipe_freeze.csr.mstatus_full_n[4]       = r_pipe_freeze.csr.mstatus_n.upie;
      r_pipe_freeze.csr.mstatus_full_n[3]       = r_pipe_freeze.csr.mstatus_n.mie;
      r_pipe_freeze.csr.mstatus_full_n[2:1]     = '0;
      r_pipe_freeze.csr.mstatus_full_n[0]       = r_pipe_freeze.csr.mstatus_n.uie;

      r_pipe_freeze.csr.mstatush_we             = csr_mstatush_we_i;
      r_pipe_freeze.csr.misa_n                  = csr_misa_n_i;
      r_pipe_freeze.csr.misa_q                  = csr_misa_q_i;

      r_pipe_freeze.csr.mie_n                   = csr_mie_n_i;
      r_pipe_freeze.csr.mie_q                   = csr_mie_q_i;
      r_pipe_freeze.csr.mie_we                  = csr_mie_we_i;
      r_pipe_freeze.csr.mtvec_n                 = csr_mtvec_n_i;
      r_pipe_freeze.csr.mtvec_q                 = csr_mtvec_q_i;
      r_pipe_freeze.csr.mtvec_mode_n            = csr_mtvec_mode_n_i;
      r_pipe_freeze.csr.mtvec_mode_q            = csr_mtvec_mode_q_i;

      r_pipe_freeze.csr.mtvt_we                 = csr_mtvt_we_i;
      r_pipe_freeze.csr.mcountinhibit_n         = csr_mcountinhibit_n_i;
      r_pipe_freeze.csr.mcountinhibit_q         = csr_mcountinhibit_q_i;
      r_pipe_freeze.csr.mcountinhibit_we        = csr_mcountinhibit_we_i;
      r_pipe_freeze.csr.mhpmevent_n             = csr_mhpmevent_n_i;
      r_pipe_freeze.csr.mhpmevent_q             = csr_mhpmevent_q_i;
      r_pipe_freeze.csr.mhpmevent_we            = csr_mhpmevent_we_i;
      r_pipe_freeze.csr.mscratch_n              = csr_mscratch_n_i;
      r_pipe_freeze.csr.mscratch_q              = csr_mscratch_q_i;
      r_pipe_freeze.csr.mepc_n                  = csr_mepc_n_i;
      r_pipe_freeze.csr.mepc_q                  = csr_mepc_q_i;

      r_pipe_freeze.csr.mcause_n[31]            = csr_mcause_n_i[5];
      r_pipe_freeze.csr.mcause_n[30:0]          = {24'h0, csr_mcause_n_i[4:0]};
      r_pipe_freeze.csr.mcause_q[31]            = csr_mcause_q_i[5];
      r_pipe_freeze.csr.mcause_q[30:0]          = {24'h0, csr_mcause_q_i[4:0]};

      r_pipe_freeze.csr.mip_n                   = csr_mip_n_i;
      r_pipe_freeze.csr.mip_q                   = csr_mip_q_i;
      r_pipe_freeze.csr.mip_we                  = csr_mip_we_i;
      r_pipe_freeze.csr.mnxti_n                 = csr_mnxti_n_i;
      r_pipe_freeze.csr.mnxti_q                 = csr_mnxti_q_i;
      r_pipe_freeze.csr.mnxti_we                = csr_mnxti_we_i;

      r_pipe_freeze.csr.mintstatus_we           = csr_mintstatus_we_i;
      r_pipe_freeze.csr.mintthresh_n            = csr_mintthresh_n_i;
      r_pipe_freeze.csr.mintthresh_q            = csr_mintthresh_q_i;
      r_pipe_freeze.csr.mintthresh_we           = csr_mintthresh_we_i;
      r_pipe_freeze.csr.mscratchcsw_n           = csr_mscratchcsw_n_i;
      r_pipe_freeze.csr.mscratchcsw_q           = csr_mscratchcsw_q_i;
      r_pipe_freeze.csr.mscratchcsw_we          = csr_mscratchcsw_we_i;
      r_pipe_freeze.csr.mscratchcswl_n          = csr_mscratchcswl_n_i;
      r_pipe_freeze.csr.mscratchcswl_q          = csr_mscratchcswl_q_i;
      r_pipe_freeze.csr.mscratchcswl_we         = csr_mscratchcswl_we_i;
      r_pipe_freeze.csr.mclicbase_n             = csr_mclicbase_n_i;
      r_pipe_freeze.csr.mclicbase_q             = csr_mclicbase_q_i;
      r_pipe_freeze.csr.mclicbase_we            = csr_mclicbase_we_i;
      r_pipe_freeze.csr.tdata1_n                = csr_tdata1_n_i;
      r_pipe_freeze.csr.tdata1_q                = csr_tdata1_q_i;
      r_pipe_freeze.csr.tdata1_we               = csr_tdata1_we_i;
      r_pipe_freeze.csr.tdata2_n                = csr_tdata2_n_i;
      r_pipe_freeze.csr.tdata2_q                = csr_tdata2_q_i;
      r_pipe_freeze.csr.tdata2_we               = csr_tdata2_we_i;
      r_pipe_freeze.csr.tinfo_n                 = csr_tinfo_n_i;
      r_pipe_freeze.csr.tinfo_q                 = csr_tinfo_q_i;

      r_pipe_freeze.csr.dcsr_n                  = csr_dcsr_n_i;
      r_pipe_freeze.csr.dcsr_q                  = csr_dcsr_q_i;

      r_pipe_freeze.csr.dpc_n                   = csr_dpc_n_i;
      r_pipe_freeze.csr.dpc_q                   = csr_dpc_q_i;
      r_pipe_freeze.csr.dpc_we                  = csr_dpc_we_i;
      r_pipe_freeze.csr.dscratch0_n             = csr_dscratch0_n_i;
      r_pipe_freeze.csr.dscratch0_q             = csr_dscratch0_q_i;
      r_pipe_freeze.csr.dscratch0_we            = csr_dscratch0_we_i;
      r_pipe_freeze.csr.dscratch1_n             = csr_dscratch1_n_i;
      r_pipe_freeze.csr.dscratch1_q             = csr_dscratch1_q_i;
      r_pipe_freeze.csr.dscratch1_we            = csr_dscratch1_we_i;
      r_pipe_freeze.csr.mconfigptr_n            = csr_mconfigptr_n_i;
      r_pipe_freeze.csr.mconfigptr_q            = csr_mconfigptr_q_i;
      r_pipe_freeze.csr.mconfigptr_we           = csr_mconfigptr_we_i;

      r_pipe_freeze.csr.mhpmcounter_q           = csr_mhpmcounter_q_i;
      r_pipe_freeze.csr.mhpmcounter_write_lower = csr_mhpmcounter_write_lower_i;
      r_pipe_freeze.csr.mhpmcounter_write_upper = csr_mhpmcounter_write_upper_i;

      r_pipe_freeze.csr.mvendorid               = csr_mvendorid_i;
      r_pipe_freeze.csr.marchid                 = csr_marchid_i;
      r_pipe_freeze.csr.mhartid                 = csr_mhartid_i;
      r_pipe_freeze.csr.mimpid                  = csr_mimpid_i;

      r_pipe_freeze.csr.mcounteren_n            = csr_mcounteren_n_i;
      r_pipe_freeze.csr.mcounteren_q            = csr_mcounteren_q_i;
      r_pipe_freeze.csr.mcounteren_we           = csr_mcounteren_we_i;

      r_pipe_freeze.csr.pmpcfg_n                = csr_pmpcfg_n_i;
      r_pipe_freeze.csr.pmpcfg_q                = csr_pmpcfg_q_i;
      r_pipe_freeze.csr.pmpcfg_we               = csr_pmpcfg_we_i;
      r_pipe_freeze.csr.pmpaddr_n               = csr_pmpaddr_n_i;
      r_pipe_freeze.csr.pmpaddr_q               = csr_pmpaddr_q_i;
      r_pipe_freeze.csr.pmpaddr_we              = csr_pmpaddr_we_i;
      r_pipe_freeze.csr.mseccfg_n               = csr_mseccfg_n_i;
      r_pipe_freeze.csr.mseccfg_q               = csr_mseccfg_q_i;
      r_pipe_freeze.csr.mseccfg_we              = csr_mseccfg_we_i;
      r_pipe_freeze.csr.mseccfgh_n              = csr_mseccfgh_n_i;
      r_pipe_freeze.csr.mseccfgh_q              = csr_mseccfgh_q_i;
      r_pipe_freeze.csr.mseccfgh_we             = csr_mseccfgh_we_i;

      compute_csr_we();

      // #1;
      ->e_pipe_monitor_ok;
      wait(clk_i_d == 1'b1);
    end
  endtask

  logic [31:0] csr_mtvec_full_q, csr_mtvec_full_n;

  `include "insn_trace.sv"

insn_trace_t trace_if, trace_id, trace_ex, trace_ex_next, trace_wb;
  insn_trace_t tmp_trace_wb;
  insn_trace_t rvfi_trace_q[$], wb_bypass_trace_q[$];

  bit           clear_trace_ex;  //  = 1'b1;
  bit           clear_trace_wb;

  logic   [3:0] next_if_pc_mux_q    [$];
  logic   [2:0] next_if_exc_pc_mux_q[$];
  logic   [3:0] next_if_pc_mux;
  logic   [2:0] next_if_exc_pc_mux;

  logic         csr_is_irq;
  logic         is_dbg_taken;
  logic   [2:0] saved_debug_cause;
  integer       next_send;

  function void empty_fifo();
    while (wb_bypass_trace_q.size() != 0) begin
      rvfi_trace_q.push_back(wb_bypass_trace_q.pop_front());
      next_send = next_send + 1;
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
      empty_fifo();
    end else begin
      wb_bypass_trace_q.push_back(new_rvfi_trace);
    end
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
      new_rvfi_trace.m_rd_addr  = '0;
      new_rvfi_trace.m_rd_wdata = '0;
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

  function void set_rvfi();
    insn_trace_t new_rvfi_trace;
    new_rvfi_trace = rvfi_trace_q.pop_front();
    rvfi_order     = new_rvfi_trace.m_order;
    rvfi_pc_rdata  = new_rvfi_trace.m_pc_rdata;
    rvfi_insn      = new_rvfi_trace.m_insn;
    rvfi_rs1_addr  = new_rvfi_trace.m_rs1_addr;
    rvfi_rs2_addr  = new_rvfi_trace.m_rs2_addr;
    rvfi_rs1_rdata = new_rvfi_trace.m_rs1_rdata;
    rvfi_rs2_rdata = new_rvfi_trace.m_rs2_rdata;
    rvfi_rd_addr   = new_rvfi_trace.m_rd_addr;
    rvfi_rd_wdata  = new_rvfi_trace.m_rd_wdata;

    rvfi_mem_addr  = new_rvfi_trace.mem_addr;
    rvfi_mem_rmask = new_rvfi_trace.mem_rmask;
    rvfi_mem_wmask = new_rvfi_trace.mem_wmask;
    rvfi_mem_rdata = new_rvfi_trace.mem_rdata;
    rvfi_mem_wdata = new_rvfi_trace.mem_wdata;

    rvfi_intr      = new_rvfi_trace.m_intr;

    rvfi_dbg       = new_rvfi_trace.m_dbg_cause;
    rvfi_dbg_mode  = new_rvfi_trace.m_dbg_taken;
    // rvfi_trap;

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
    trace_``TRACE_NAME``.m_csr.``CSR_NAME``_we      = r_pipe_freeze.csr.``CSR_NAME``_we; \
    trace_``TRACE_NAME``.m_csr.``CSR_NAME``_rdata   = r_pipe_freeze.csr.``CSR_NAME``_q; \
    trace_``TRACE_NAME``.m_csr.``CSR_NAME``_rmask   = '1; \
    trace_``TRACE_NAME``.m_csr.``CSR_NAME``_wdata   = r_pipe_freeze.csr.``CSR_NAME``_n; \
    trace_``TRACE_NAME``.m_csr.``CSR_NAME``_wmask   = r_pipe_freeze.csr.``CSR_NAME``_we ? '1 : '0;

  task compute_pipeline();
    bit s_new_valid_insn;
    bit s_ex_valid_adjusted;
    bit s_wb_valid_adjusted;

    bit s_id_done;

    trace_if = new();
    trace_id = new();
    trace_ex = new();
    trace_wb = new();
    s_new_valid_insn = 1'b0;
    s_ex_valid_adjusted = 1'b0;

    s_id_done = 1'b0;

    next_send = 1;
    next_if_pc_mux = '0;
    next_if_exc_pc_mux = '0;

    csr_is_irq = '0;
    is_dbg_taken = '0;

    $display("*****Starting pipeline computing*****\n");
    forever begin
      wait(e_pipe_monitor_ok.triggered);
      #1;

      if (r_pipe_freeze.if_valid && r_pipe_freeze.if_ready) begin
        next_if_pc_mux = next_if_pc_mux_q.pop_front();
        next_if_exc_pc_mux = next_if_exc_pc_mux_q.pop_front();
        pc_mux_interrupt = (next_if_pc_mux == PC_EXCEPTION && next_if_exc_pc_mux == EXC_PC_IRQ);
        pc_mux_nmi = '0;
        pc_mux_debug       = (next_if_pc_mux == PC_EXCEPTION && (next_if_exc_pc_mux == EXC_PC_DBD | next_if_exc_pc_mux == EXC_PC_DBE));
        pc_mux_exception = '0;
      end


      if (r_pipe_freeze.ctrl_fsm_cs == DBG_FLUSH && r_pipe_freeze.ebrk_insn_dec) begin
        if (trace_wb.m_valid) begin
          send_rvfi(trace_wb);
          trace_wb.m_valid = 1'b0;
        end
        if (trace_ex.m_valid) begin
          send_rvfi(trace_ex);
          trace_ex.m_valid = 1'b0;
        end
        if (trace_id.m_valid) begin

          trace_id.m_csr.minstret_we    = r_pipe_freeze.csr.mhpmcounter_write_lower[2];
          trace_id.m_csr.minstret_rdata = r_pipe_freeze.csr.mhpmcounter_q[2];
          trace_id.m_csr.minstret_rmask = '1;
          trace_id.m_csr.minstret_wdata = r_pipe_freeze.csr.mhpmcounter_q;
          trace_id.m_csr.minstret_wmask = r_pipe_freeze.csr.mhpmcounter_write_lower[2] ? '1 : '0;

          `CSR_FROM_PIPE(id, misa)
          `CSR_FROM_PIPE(id, tdata1)
          trace_id.m_csr.tinfo_we    = '0; // READ ONLY csr_tinfo_we_i;
          trace_id.m_csr.tinfo_rdata = r_pipe_freeze.csr.tinfo_q;
          trace_id.m_csr.tinfo_rmask = '1;
          trace_id.m_csr.tinfo_wdata = r_pipe_freeze.csr.tinfo_n;
          trace_id.m_csr.tinfo_wmask = '0;
          `CSR_FROM_PIPE(id, mip)
          send_rvfi(trace_id);
          trace_id.m_valid = 1'b0;
        end
      end



      if (trace_ex.m_valid & s_wb_valid_adjusted) begin
        // Used flopped values in case write happened before wb_valid
        trace_ex.m_csr.minstret_we    = r_pipe_freeze.csr.mhpmcounter_write_lower[2];
        trace_ex.m_csr.minstret_rdata = r_pipe_freeze.csr.mhpmcounter_q[2];
        trace_ex.m_csr.minstret_rmask = '1;
        trace_ex.m_csr.minstret_wdata = r_pipe_freeze.csr.mhpmcounter_q;
        trace_ex.m_csr.minstret_wmask = r_pipe_freeze.csr.mhpmcounter_write_lower[2] ? '1 : '0;
        trace_ex.m_csr.got_minstret = '1;
      end

      s_new_valid_insn = r_pipe_freeze.id_valid && r_pipe_freeze.is_decoding;

      s_wb_valid_adjusted = r_pipe_freeze.wb_valid && (r_pipe_freeze.ctrl_fsm_cs == DECODE);

      //WB_STAGE
      if (trace_wb.m_valid) begin
        if (!trace_wb.m_data_missaligned) begin
          send_rvfi(trace_wb);
          trace_wb.m_valid = 1'b0;
        end else begin
          if (s_wb_valid_adjusted) begin
            if (r_pipe_freeze.rf_we_wb) begin
              if (!trace_wb.m_ex_fw) begin
                trace_wb.m_rd_addr  = r_pipe_freeze.rf_addr_wb;
                trace_wb.m_rd_wdata = r_pipe_freeze.rf_wdata_wb;
              end
              if (trace_wb.m_data_missaligned && !trace_wb.m_got_first_data) begin
                trace_wb.m_got_first_data = 1'b1;
              end else begin
                send_rvfi(trace_wb);
                trace_wb.m_valid = 1'b0;
              end
            end
          end
        end
      end

      if (trace_ex.m_valid) begin

        `CSR_FROM_PIPE(ex, misa)
        `CSR_FROM_PIPE(ex, mip)
        `CSR_FROM_PIPE(ex, tdata1)

        trace_ex.m_csr.tinfo_we    = '0; // READ ONLY csr_tinfo_we_i;
        trace_ex.m_csr.tinfo_rdata = r_pipe_freeze.csr.tinfo_q;
        trace_ex.m_csr.tinfo_rmask = '1;
        trace_ex.m_csr.tinfo_wdata = r_pipe_freeze.csr.tinfo_n;
        trace_ex.m_csr.tinfo_wmask = '0;

        if (s_wb_valid_adjusted) begin
          if (trace_wb.m_valid) begin
            send_rvfi(trace_ex);
            trace_ex.m_valid = 1'b0;
          end else begin
            if (r_pipe_freeze.rf_we_wb) begin
              trace_ex.m_rd_addr = r_pipe_freeze.rf_addr_wb;
              trace_ex.m_rd_wdata = r_pipe_freeze.rf_wdata_wb;
              trace_ex.m_got_first_data = 1'b1;
            end

            if (!s_ex_valid_adjusted & !trace_ex.m_csr.got_minstret) begin
              trace_ex.m_csr.minstret_we = r_pipe_freeze.csr.mhpmcounter_write_lower[2];
              trace_ex.m_csr.minstret_rdata = r_pipe_freeze.csr.mhpmcounter_q[2];
              trace_ex.m_csr.minstret_rmask = '1;
              trace_ex.m_csr.minstret_wdata = r_pipe_freeze.csr.mhpmcounter_q;
              trace_ex.m_csr.minstret_wmask = r_pipe_freeze.csr.mhpmcounter_write_lower[2] ? '1 : '0;
            end

            trace_wb.move_down_pipe(trace_ex);
            trace_ex.m_valid = 1'b0;
          end
        end else if (r_pipe_freeze.rf_we_wb) begin
          trace_ex.m_rd_addr = r_pipe_freeze.rf_addr_wb;
          trace_ex.m_rd_wdata = r_pipe_freeze.rf_wdata_wb;
          trace_ex.m_got_first_data = 1'b1;
        end
      end

      s_ex_valid_adjusted = r_pipe_freeze.ex_valid && (r_pipe_freeze.ctrl_fsm_cs == DECODE);

      //EX_STAGE
      if (trace_id.m_valid) begin

        trace_id.m_csr.mtvec_we = r_pipe_freeze.csr.mtvec_we;
        trace_id.m_csr.mtvec_rdata = {
          r_pipe_freeze.csr.mtvec_q, 6'h0, r_pipe_freeze.csr.mtvec_mode_q
        };
        trace_id.m_csr.mtvec_rmask = '1;
        trace_id.m_csr.mtvec_wdata = {
          r_pipe_freeze.csr.mtvec_n, 6'h0, r_pipe_freeze.csr.mtvec_mode_n
        };
        ;
        trace_id.m_csr.mtvec_wmask = r_pipe_freeze.csr.mtvec_we ? '1 : '0;

        if (!csr_is_irq) begin
          trace_id.m_csr.mstatus_we    = r_pipe_freeze.csr.mstatus_we;
          trace_id.m_csr.mstatus_rdata = r_pipe_freeze.csr.mstatus_full_q;
          trace_id.m_csr.mstatus_rmask = '1;
          trace_id.m_csr.mstatus_wdata = r_pipe_freeze.csr.mstatus_full_n;
          trace_id.m_csr.mstatus_wmask = r_pipe_freeze.csr.mstatus_we ? '1 : '0;

          `CSR_FROM_PIPE(id, mepc)
          if (trace_id.m_csr.mcause_we == '0) begin  //for debug purpose
            `CSR_FROM_PIPE(id, mcause)
          end
        end

        `CSR_FROM_PIPE(id, mcountinhibit)
        `CSR_FROM_PIPE(id, mscratch)
        `CSR_FROM_PIPE(id, mie)

        if (s_ex_valid_adjusted) begin  //A valid instruction goes from ID to EX
          if (trace_ex.m_valid) begin  //We need to bypass wb
            send_rvfi(trace_ex);
            trace_ex.m_valid = 1'b0;
          end
          if (r_pipe_freeze.ex_reg_we) begin
            trace_id.m_ex_fw    = 1'b1;
            trace_id.m_rd_addr  = r_pipe_freeze.ex_reg_addr;
            trace_id.m_rd_wdata = r_pipe_freeze.ex_reg_wdata;
          end else if (!trace_ex.m_valid & r_pipe_freeze.rf_we_wb & !trace_id.m_ex_fw) begin
            trace_id.m_rd_addr  = r_pipe_freeze.rf_addr_wb;
            trace_id.m_rd_wdata = r_pipe_freeze.rf_wdata_wb;
          end

          if (r_pipe_freeze.data_misaligned && !r_pipe_freeze.lsu_data_we_ex) begin
            trace_id.m_data_missaligned = 1'b1;
          end

          trace_ex.move_down_pipe(trace_id);  // The instruction moves forward from ID to EX
          trace_id.m_valid = 1'b0;

        end else if (r_pipe_freeze.ex_reg_we) begin
          trace_id.m_ex_fw          = 1'b1;
          trace_id.m_rd_addr        = r_pipe_freeze.ex_reg_addr;
          trace_id.m_rd_wdata       = r_pipe_freeze.ex_reg_wdata;
          trace_id.m_got_regs_write = 1'b1;
        end
      end

      //ID_STAGE
      if (s_new_valid_insn) begin  // There is a new valid instruction
        if (trace_id.m_valid) begin
          if (trace_ex.m_valid) begin
            trace_ex.m_csr.minstret_we    = r_pipe_freeze.csr.mhpmcounter_write_lower[2];
            trace_ex.m_csr.minstret_rdata = r_pipe_freeze.csr.mhpmcounter_q[2];
            trace_ex.m_csr.minstret_rmask = '1;
            trace_ex.m_csr.minstret_wdata = r_pipe_freeze.csr.mhpmcounter_q;
            trace_ex.m_csr.minstret_wmask = r_pipe_freeze.csr.mhpmcounter_write_lower[2] ? '1 : '0;
            send_rvfi(trace_ex);
            trace_ex.m_valid = 1'b0;
          end
          trace_ex.move_down_pipe(trace_id);
          trace_id.m_valid = 1'b0;
        end
        trace_id.init(trace_if.m_insn);
        trace_id.m_intr                = trace_if.m_intr;
        trace_id.m_dbg_taken           = trace_if.m_dbg_taken;
        trace_id.m_dbg_cause           = trace_if.m_dbg_cause;
        trace_id.m_is_ebreak           = trace_if.m_is_ebreak;

        trace_if.m_valid               = 1'b0;
        s_id_done                      = 1'b0;
        trace_id.m_csr.mvendorid_we    = '0;
        trace_id.m_csr.mvendorid_rdata = r_pipe_freeze.csr.mvendorid;
        trace_id.m_csr.mvendorid_rmask = '1;
        trace_id.m_csr.mvendorid_wdata = '0;
        trace_id.m_csr.mvendorid_wmask = '0;

        trace_id.m_csr.marchid_we      = '0;
        trace_id.m_csr.marchid_rdata   = r_pipe_freeze.csr.marchid;
        trace_id.m_csr.marchid_rmask   = '0;
        trace_id.m_csr.marchid_wdata   = '0;
        trace_id.m_csr.marchid_wmask   = '0;

        `CSR_FROM_PIPE(id, dscratch0)
        `CSR_FROM_PIPE(id, dscratch1)

        trace_id.m_csr.mstatus_we    = r_pipe_freeze.csr.mstatus_we;
        trace_id.m_csr.mstatus_rdata = r_pipe_freeze.csr.mstatus_full_q;
        trace_id.m_csr.mstatus_rmask = '1;
        trace_id.m_csr.mstatus_wdata = r_pipe_freeze.csr.mstatus_full_n;
        trace_id.m_csr.mstatus_wmask = r_pipe_freeze.csr.mstatus_we ? '1 : '0;

      end else begin
        if (trace_id.m_valid) begin
          `CSR_FROM_PIPE(id, dscratch0)
          `CSR_FROM_PIPE(id, dscratch1)
        end
      end

      //IF_STAGE

      if (r_pipe_freeze.if_valid && r_pipe_freeze.if_ready) begin
        if(trace_if.m_valid && r_pipe_freeze.id_valid && r_pipe_freeze.id_ready && !trace_id.m_valid && r_pipe_freeze.ebrk_insn_dec) begin//trace_if.m_valid & r_pipe_freeze.is_decoding) begin
          trace_id.init(trace_if.m_insn);
          trace_id.m_intr      = trace_if.m_intr;
          trace_id.m_dbg_taken = trace_if.m_dbg_taken;
          trace_id.m_dbg_cause = trace_if.m_dbg_cause;
          trace_id.m_is_ebreak = '1;  //trace_if.m_is_ebreak;
          s_id_done            = 1'b0;
          trace_if.m_valid     = 1'b0;
        end
        trace_if.m_insn      = r_pipe_freeze.instr_if;  //Instr comes from if, buffer for one cycle
        trace_if.m_pc_rdata  = r_pipe_freeze.pc_if;
        trace_if.m_dbg_taken = is_dbg_taken;
        trace_if.m_dbg_cause = saved_debug_cause;
        trace_if.m_is_ebreak = '0;

        //check if interrupt
        if (pc_mux_interrupt || pc_mux_nmi || pc_mux_exception) begin
          trace_if.m_intr.intr      = 1'b1;
          trace_if.m_intr.interrupt = pc_mux_interrupt || pc_mux_nmi;
          trace_if.m_intr.exception = pc_mux_exception;
          // trace_if.m_intr.cause     = r_pipe_freeze.ctrl_fsm_cs.csr_cause.exception_code;
        end else if (pc_mux_debug) begin
        end else begin
          trace_if.m_intr.intr      = '0;
          trace_if.m_intr.interrupt = '0;
          trace_if.m_intr.exception = '0;
        end
        trace_if.m_valid = 1'b1;
      end

      if (r_pipe_freeze.pc_set & r_pipe_freeze.prefetch_req) begin
        next_if_pc_mux_q.delete();
        next_if_exc_pc_mux_q.delete();
      end
      if (r_pipe_freeze.instr_req && r_pipe_freeze.instr_grant) begin
        next_if_pc_mux_q.push_back(r_pipe_freeze.pc_mux);
        next_if_exc_pc_mux_q.push_back(r_pipe_freeze.exc_pc_mux);
      end

      if (csr_is_irq) begin
        trace_id.m_csr.mstatus_we    = r_pipe_freeze.csr.mstatus_we;
        trace_id.m_csr.mstatus_rdata = r_pipe_freeze.csr.mstatus_full_q;
        trace_id.m_csr.mstatus_rmask = '1;
        trace_id.m_csr.mstatus_wdata = r_pipe_freeze.csr.mstatus_full_n;
        trace_id.m_csr.mstatus_wmask = r_pipe_freeze.csr.mstatus_we ? '1 : '0;

        `CSR_FROM_PIPE(id, mepc)
        `CSR_FROM_PIPE(id, mcause)
      end

      if (!s_id_done) begin
        `CSR_FROM_PIPE(id, dpc)

        trace_id.m_csr.dcsr_we    = r_pipe_freeze.csr.dcsr_we;
        trace_id.m_csr.dcsr_rdata = r_pipe_freeze.csr.dcsr_q;
        trace_id.m_csr.dcsr_rmask = '1;
        trace_id.m_csr.dcsr_wdata = r_pipe_freeze.csr.dcsr_n;
        trace_id.m_csr.dcsr_wmask = r_pipe_freeze.csr.dcsr_we ? '1 : '0;
      end

      csr_is_irq        = r_pipe_freeze.csr_cause[5];
      is_dbg_taken      = (r_pipe_freeze.ctrl_fsm_cs == DBG_TAKEN_ID) ? 1'b1 : 1'b0;
      saved_debug_cause = r_pipe_freeze.debug_cause;
      s_id_done         = r_pipe_freeze.id_valid;
      #1;
    end
  endtask

  task update_rvfi();
    rvfi_valid     = 1'b0;
    rvfi_order     = '0;
    rvfi_insn      = '0;
    rvfi_pc_rdata  = '0;
    rvfi_rd_addr   = '0;
    rvfi_rd_wdata  = '0;
    rvfi_rs1_addr  = '0;
    rvfi_rs2_addr  = '0;
    rvfi_rs1_rdata = '0;
    rvfi_rs2_rdata = '0;
    rvfi_mem_addr  = '0;
    rvfi_mem_rmask = '0;
    rvfi_mem_wmask = '0;
    rvfi_mem_rdata = '0;
    rvfi_mem_wdata = '0;

    rvfi_mode      = 2'b11;  //priv_lvl_i; //TODO: correct this if needed

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
