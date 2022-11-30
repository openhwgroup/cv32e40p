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

    input logic        is_decoding_i,
    input logic        is_illegal_i,
    input logic        trigger_match_i,
    input logic        data_misaligned_i,
    input logic        lsu_data_we_ex_i,

    input logic        debug_mode_i,
    input logic [2:0]  debug_cause_i,
    //// INSTR IF Probes ////
    input logic        instr_req_i,
    input logic        instr_grant_i,
    input logic        instr_rvalid_i,

    input logic        prefetch_req_i,
    input logic        pc_set_i,
    //// IF Probes ////
    input logic        if_valid_i,
    input logic        if_ready_i,
    input logic        instr_valid_if_i,
    input logic [31:0] instr_if_i,
    input logic [31:0] pc_if_i,
    input logic        instr_pmp_err_if_i,

    input logic        instr_valid_id_i    ,
    input logic [31:0] instr_rdata_id_i    ,
    input logic        is_fetch_failed_id_i,
    input logic        instr_req_int_i     ,
    input logic        clear_instr_valid_i ,
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

    input logic        ebrk_insn_dec_i,

    input logic [5:0]  csr_cause_i,

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
    input ctrl_state_e ctrl_fsm_cs_i,
    input ctrl_state_e ctrl_fsm_ns_i,
    input logic        pending_single_step_i,
    input logic        single_step_allowed_i,
    input logic        nmi_pending_i,
    input logic        nmi_is_store_i,
    input logic        pending_debug_i,
    input logic        debug_mode_q_i,
    input logic [3:0]  pc_mux_i,
    input logic [2:0]  exc_pc_mux_i,

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

  // CSR inputs in struct format
  rvfi_csr_map_t             rvfi_csr_rdata_d;
  rvfi_csr_map_t             rvfi_csr_wdata_d;
  rvfi_csr_map_t             rvfi_csr_wmask_d;

  rvfi_csr_map_t             rvfi_csr_rdata;
  rvfi_csr_map_t             rvfi_csr_wdata;
  rvfi_csr_map_t             rvfi_csr_wmask;

  // Reads from autonomous registers propagate from EX stage
  rvfi_auto_csr_map_t        ex_csr_rdata;
  rvfi_auto_csr_map_t        ex_csr_rdata_d;
  /*
  logic [31:0][31:0] csr_mhpmcounter_n_l;
  logic [31:0][31:0] csr_mhpmcounter_n_h;
  logic [31:0][31:0] csr_mhpmcounter_q_l;
  logic [31:0][31:0] csr_mhpmcounter_q_h;
  logic [31:0][31:0] csr_mhpmcounter_we_l;
  logic [31:0][31:0] csr_mhpmcounter_we_h;

  // Signals for special handling of performance counters
  logic [31:0][31:0] mhpmcounter_l_rdata_q;
  logic [31:0][31:0] mhpmcounter_l_wdata_q;
  logic [31:0][31:0] mhpmcounter_h_rdata_q;
  logic [31:0][31:0] mhpmcounter_h_wdata_q;

  // Counter was written during WB and possibly before wb_valid
  logic [31:0]       mhpmcounter_l_during_wb;
  logic [31:0]       mhpmcounter_h_during_wb;


  logic [63:0] data_wdata_ror; // Intermediate rotate signal, as direct part-select not supported in all tools

  logic         wb_valid_wfi_delayed;
  */
  // logic                      wb_valid_adjusted;

  logic         pc_mux_debug;
  logic         pc_mux_dret;
  logic         pc_mux_exception;
  logic         pc_mux_debug_exception;
  logic         pc_mux_interrupt;
  logic         pc_mux_nmi;
/*
  logic [6:0]   insn_opcode;
  logic [4:0]   insn_rd;
  logic [2:0]   insn_funct3;
  logic [4:0]   insn_rs1;
  logic [4:0]   insn_rs2;
  logic [6:0]   insn_funct7;
  logic [11:0]  insn_csr;

  assign insn_opcode = rvfi_insn[6:0];
  assign insn_rd     = rvfi_insn[11:7];
  assign insn_funct3 = rvfi_insn[14:12];
  assign insn_rs1    = rvfi_insn[19:15];
  assign insn_rs2    = rvfi_insn[24:20];
  assign insn_funct7 = rvfi_insn[31:25];
  assign insn_csr    = rvfi_insn[31:20];

  */

  /*
   * This struct is used to store all information comming from the core at every posedge
   * The information will then be processed
   */
  typedef struct {
      logic        is_decoding;
      logic        is_illegal;
      logic        trigger_match;
      logic        data_misaligned;
      logic        lsu_data_we_ex;
      logic        debug_mode;
      logic [2:0]  debug_cause;
      //// INSTR IF Probes ////
      logic        instr_req;
      logic        instr_grant;
      logic        instr_rvalid;

      logic        prefetch_req;
      logic        pc_set;

      logic        instr_valid_id    ;
      logic [31:0] instr_rdata_id    ;
      logic        is_fetch_failed_id;
      logic        instr_req_int     ;
      logic        clear_instr_valid ;
      //// IF Probes ////
      logic        if_valid;
      logic        if_ready;
      logic        instr_valid_if;
      logic [31:0] instr_if;
      logic [31:0] pc_if;
      logic        instr_pmp_err_if;

      //// ID probes ////
      logic [31:0] pc_id;
      logic        id_valid;

      logic        id_ready;
      logic [ 1:0] rf_re_id;
      logic        sys_en_id;
      logic        sys_mret_insn_id;
      logic        jump_in_id;
      logic [31:0] jump_target_id;
      logic        is_compressed_id;

      logic        ebrk_insn_dec;

      logic [5:0]  csr_cause;

      logic        debug_csr_save;
      // LSU
      logic        lsu_en_id;
      logic        lsu_we_id;
      logic [ 1:0] lsu_size_id;
      // Register reads
      logic [ 4:0] rs1_addr_id;
      logic [ 4:0] rs2_addr_id;
      logic [31:0] operand_a_fw_id;
      logic [31:0] operand_b_fw_id;

      //// EX probes ////

      // Register writes in EX
      logic ex_ready;
      logic ex_valid;

      logic        ex_reg_we;
      logic [ 4:0] ex_reg_addr;
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
      logic        lsu_split_q_ex;

      //// WB probes ////
      logic [31:0] pc_wb;
      logic        wb_ready;
      logic        wb_valid;
      logic        ebreak_in_wb;
      logic [31:0] instr_rdata_wb;
      logic        csr_en_wb;
      logic        sys_wfi_insn_wb;
      // Register writes
      logic        rf_we_wb;
      logic [ 4:0] rf_addr_wb;
      logic [31:0] rf_wdata_wb;
      // LSU
      logic [31:0] lsu_rdata_wb;
      // PC //
      logic [31:0] branch_addr_n;

      // Controller FSM probes
      ctrl_state_e ctrl_fsm_cs;
      ctrl_state_e ctrl_fsm_ns;
      logic        pending_single_step;
      logic        single_step_allowed;
      logic        nmi_pending;
      logic        nmi_is_store;
      logic        pending_debug;
      logic        debug_mode_q;
      logic [3:0]  pc_mux;
      logic [2:0]  exc_pc_mux;

      // Interrupt Controller probes
      logic [31:0] irq;
      logic        irq_wu_ctrl;
      logic [ 4:0] irq_id_ctrl;

      struct {
        //// CSR Probes ////
        csr_num_e        addr;
        logic            we;
        logic     [31:0] wdata_int;

        logic mstatus_we  ;
        logic misa_we     ;
        logic mtvec_we    ;
        logic mscratch_we ;
        logic mepc_we     ;
        logic mcause_we   ;
        logic dcsr_we     ;

        logic    jvt_we;
        Status_t mstatus_n;
        Status_t mstatus_q;
        logic [31:0] mstatus_full_n;
        logic [31:0] mstatus_full_q;

        logic        mstatush_we;
        logic [31:0] misa_n;
        logic [31:0] misa_q;

        logic [31:0] mie_n;
        logic [31:0] mie_q;
        logic        mie_we;
        logic [23:0] mtvec_n;
        logic [23:0] mtvec_q;
        logic [ 1:0] mtvec_mode_n;
        logic [ 1:0] mtvec_mode_q;

        logic              mtvt_we;
        logic [31:0]       mcountinhibit_n;
        logic [31:0]       mcountinhibit_q;
        logic              mcountinhibit_we;
        logic [31:0][31:0] mhpmevent_n;
        logic [31:0][31:0] mhpmevent_q;
        logic [31:0]       mhpmevent_we;
        logic [31:0]       mscratch_n;
        logic [31:0]       mscratch_q;
        logic [31:0]       mepc_n;
        logic [31:0]       mepc_q;

        logic [31:0] mcause_n;
        logic [31:0] mcause_q;
        logic [31:0] mip_n;
        logic [31:0] mip_q;
        logic        mip_we;
        logic [31:0] mnxti_n;
        logic [31:0] mnxti_q;
        logic        mnxti_we;

        logic        mintstatus_we;
        logic [31:0] mintthresh_n;
        logic [31:0] mintthresh_q;
        logic        mintthresh_we;
        logic [31:0] mscratchcsw_n;
        logic [31:0] mscratchcsw_q;
        logic        mscratchcsw_we;
        logic [31:0] mscratchcswl_n;
        logic [31:0] mscratchcswl_q;
        logic        mscratchcswl_we;
        logic [31:0] mclicbase_n;
        logic [31:0] mclicbase_q;
        logic        mclicbase_we;
        logic [31:0] tdata1_n;
        logic [31:0] tdata1_q;
        logic        tdata1_we;
        logic [31:0] tdata2_n;
        logic [31:0] tdata2_q;
        logic        tdata2_we;
        logic [31:0] tinfo_n;
        logic [31:0] tinfo_q;

        Dcsr_t dcsr_n;
        Dcsr_t dcsr_q;

        logic [31:0] dpc_n;
        logic [31:0] dpc_q;
        logic        dpc_we;
        logic [31:0] dscratch0_n;
        logic [31:0] dscratch0_q;
        logic        dscratch0_we;
        logic [31:0] dscratch1_n;
        logic [31:0] dscratch1_q;
        logic        dscratch1_we;
        logic [31:0] mconfigptr_n;
        logic [31:0] mconfigptr_q;
        logic        mconfigptr_we;


        // performance counters
        //  cycle,  instret,  hpcounter,  cycleh,  instreth,  hpcounterh
        // mcycle, minstret, mhpcounter, mcycleh, minstreth, mhpcounterh
        logic [31:0][MHPMCOUNTER_WIDTH-1:0] mhpmcounter_q;
        logic [31:0]                        mhpmcounter_write_lower;
        logic [31:0]                        mhpmcounter_write_upper;

        logic [31:0] mvendorid;
        logic [31:0] marchid;
        logic [31:0] mhartid;
        logic [31:0] mimpid;

        logic [31:0] mcounteren_n;
        logic [31:0] mcounteren_q;
        logic        mcounteren_we;

        logic [ 7:0] pmpcfg_n   [16];
        logic [ 7:0] pmpcfg_q   [16];
        logic [15:0] pmpcfg_we;
        logic [31:0] pmpaddr_n;  // PMP address input shared for all pmpaddr registers
        logic [31:0] pmpaddr_q  [16];
        logic [15:0] pmpaddr_we;
        logic [31:0] mseccfg_n;
        logic [31:0] mseccfg_q;
        logic        mseccfg_we;
        logic [31:0] mseccfgh_n;
        logic [31:0] mseccfgh_q;
        logic        mseccfgh_we;
      } csr;
  } pipe_t;

  pipe_t r_pipe_freeze;

  event e_pipe_monitor_ok;

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

        r_pipe_freeze.instr_req        = instr_req_i;
        r_pipe_freeze.instr_grant      = instr_grant_i;
        r_pipe_freeze.instr_rvalid     = instr_rvalid_i;
        r_pipe_freeze.is_decoding      = is_decoding_i;
        r_pipe_freeze.is_illegal       = is_illegal_i;
        r_pipe_freeze.trigger_match    = trigger_match_i;
        r_pipe_freeze.data_misaligned  = data_misaligned_i;
        r_pipe_freeze.lsu_data_we_ex   = lsu_data_we_ex_i;

        r_pipe_freeze.debug_mode       = debug_mode_i;
        r_pipe_freeze.debug_cause      = debug_cause_i;
        r_pipe_freeze.prefetch_req     = prefetch_req_i;
        r_pipe_freeze.pc_set           = pc_set_i;
        //// IF probes ////
        r_pipe_freeze.if_valid         = if_valid_i ;
        r_pipe_freeze.if_ready         = if_ready_i ;
        r_pipe_freeze.instr_valid_if   = instr_valid_if_i ;
        r_pipe_freeze.instr_if         = instr_if_i ;
        r_pipe_freeze.pc_if            = pc_if_i ;
        r_pipe_freeze.instr_pmp_err_if = instr_pmp_err_if_i ;

        r_pipe_freeze.instr_valid_id     = instr_valid_id_i    ;
        r_pipe_freeze.instr_rdata_id     = instr_rdata_id_i    ;
        r_pipe_freeze.is_fetch_failed_id = is_fetch_failed_id_i;
        r_pipe_freeze.instr_req_int      = instr_req_int_i     ;
        r_pipe_freeze.clear_instr_valid  = clear_instr_valid_i ;
        //// ID probes ////
        r_pipe_freeze.pc_id    = pc_id_i;
        r_pipe_freeze.id_valid = id_valid_i;

        r_pipe_freeze.id_ready         = id_ready_i        ;
        r_pipe_freeze.rf_re_id         = rf_re_id_i        ;
        r_pipe_freeze.sys_en_id        = sys_en_id_i       ;
        r_pipe_freeze.sys_mret_insn_id = sys_mret_insn_id_i;
        r_pipe_freeze.jump_in_id       = jump_in_id_i      ;
        r_pipe_freeze.jump_target_id   = jump_target_id_i  ;
        r_pipe_freeze.is_compressed_id = is_compressed_id_i;
        r_pipe_freeze.ebrk_insn_dec    = ebrk_insn_dec_i   ;
        r_pipe_freeze.csr_cause        = csr_cause_i;
        r_pipe_freeze.debug_csr_save   = debug_csr_save_i;
        // LSU
        r_pipe_freeze.lsu_en_id   = lsu_en_id_i;
        r_pipe_freeze.lsu_we_id   = lsu_we_id_i;
        r_pipe_freeze.lsu_size_id = lsu_size_id_i;
        // Register reads
        r_pipe_freeze.rs1_addr_id     = rs1_addr_id_i;
        r_pipe_freeze.rs2_addr_id     = rs2_addr_id_i;
        r_pipe_freeze.operand_a_fw_id = operand_a_fw_id_i;
        r_pipe_freeze.operand_b_fw_id = operand_b_fw_id_i;

        //// EX probes ////

        // Register writes in EX
        r_pipe_freeze.ex_ready = ex_ready_i;
        r_pipe_freeze.ex_valid = ex_valid_i;

        r_pipe_freeze.ex_reg_we    = ex_reg_we_i;
        r_pipe_freeze.ex_reg_addr  = ex_reg_addr_i;
        r_pipe_freeze.ex_reg_wdata = ex_reg_wdata_i;

        r_pipe_freeze.branch_in_ex       = branch_in_ex_i;
        r_pipe_freeze.branch_decision_ex = branch_decision_ex_i;
        r_pipe_freeze.dret_in_ex         = dret_in_ex_i;
        // LSU
        r_pipe_freeze.lsu_en_ex             = lsu_en_ex_i;
        r_pipe_freeze.lsu_pmp_err_ex        = lsu_pmp_err_ex_i;
        r_pipe_freeze.lsu_pma_err_atomic_ex = lsu_pma_err_atomic_ex_i;

        r_pipe_freeze.branch_target_ex = branch_target_ex_i;

        r_pipe_freeze.data_addr_ex   = data_addr_ex_i;
        r_pipe_freeze.data_wdata_ex  = data_wdata_ex_i;
        r_pipe_freeze.lsu_split_q_ex = lsu_split_q_ex_i;

        //// WB probes ////
        r_pipe_freeze.pc_wb           = pc_wb_i;
        r_pipe_freeze.wb_ready        = wb_ready_i;
        r_pipe_freeze.wb_valid        = wb_valid_i;
        r_pipe_freeze.ebreak_in_wb    = ebreak_in_wb_i;
        r_pipe_freeze.instr_rdata_wb  = instr_rdata_wb_i;
        r_pipe_freeze.csr_en_wb       = csr_en_wb_i;
        r_pipe_freeze.sys_wfi_insn_wb = sys_wfi_insn_wb_i;
        // Register writes
        r_pipe_freeze.rf_we_wb    = rf_we_wb_i;
        r_pipe_freeze.rf_addr_wb  = rf_addr_wb_i;
        r_pipe_freeze.rf_wdata_wb = rf_wdata_wb_i;
        // LSU
        r_pipe_freeze.lsu_rdata_wb = lsu_rdata_wb_i;
        // PC //
        r_pipe_freeze.branch_addr_n = branch_addr_n_i;

        // Controller FSM probes
        r_pipe_freeze.ctrl_fsm_cs = ctrl_fsm_cs_i;
        r_pipe_freeze.pc_mux      = pc_mux_i;
        r_pipe_freeze.exc_pc_mux  = exc_pc_mux_i;

        // CSR
        r_pipe_freeze.csr.addr      = csr_addr_i     ;
        r_pipe_freeze.csr.we        = csr_we_i       ;
        r_pipe_freeze.csr.wdata_int = csr_wdata_int_i;

        r_pipe_freeze.csr.jvt_we    = csr_jvt_we_i   ;
        r_pipe_freeze.csr.mstatus_n = csr_mstatus_n_i;
        r_pipe_freeze.csr.mstatus_q = csr_mstatus_q_i;

        r_pipe_freeze.csr.mstatus_full_q[31:18] = '0;
        r_pipe_freeze.csr.mstatus_full_q[17] = r_pipe_freeze.csr.mstatus_q.mprv;
        r_pipe_freeze.csr.mstatus_full_q[16:13] = '0;
        r_pipe_freeze.csr.mstatus_full_q[12:11] = r_pipe_freeze.csr.mstatus_q.mpp;
        r_pipe_freeze.csr.mstatus_full_q[10:8] = '0;
        r_pipe_freeze.csr.mstatus_full_q[7] = r_pipe_freeze.csr.mstatus_q.mpie;
        r_pipe_freeze.csr.mstatus_full_q[6:5] = '0;
        r_pipe_freeze.csr.mstatus_full_q[4] = r_pipe_freeze.csr.mstatus_q.upie;
        r_pipe_freeze.csr.mstatus_full_q[3] = r_pipe_freeze.csr.mstatus_q.mie;
        r_pipe_freeze.csr.mstatus_full_q[2:1] = '0;
        r_pipe_freeze.csr.mstatus_full_q[0] = r_pipe_freeze.csr.mstatus_q.uie;

        r_pipe_freeze.csr.mstatus_full_n[31:18] = '0;
        r_pipe_freeze.csr.mstatus_full_n[17] = r_pipe_freeze.csr.mstatus_n.mprv;
        r_pipe_freeze.csr.mstatus_full_n[16:13] = '0;
        r_pipe_freeze.csr.mstatus_full_n[12:11] = r_pipe_freeze.csr.mstatus_n.mpp;
        r_pipe_freeze.csr.mstatus_full_n[10:8] = '0;
        r_pipe_freeze.csr.mstatus_full_n[7] = r_pipe_freeze.csr.mstatus_n.mpie;
        r_pipe_freeze.csr.mstatus_full_n[6:5] = '0;
        r_pipe_freeze.csr.mstatus_full_n[4] = r_pipe_freeze.csr.mstatus_n.upie;
        r_pipe_freeze.csr.mstatus_full_n[3] = r_pipe_freeze.csr.mstatus_n.mie;
        r_pipe_freeze.csr.mstatus_full_n[2:1] = '0;
        r_pipe_freeze.csr.mstatus_full_n[0] = r_pipe_freeze.csr.mstatus_n.uie;

        r_pipe_freeze.csr.mstatush_we = csr_mstatush_we_i;
        r_pipe_freeze.csr.misa_n      = csr_misa_n_i;
        r_pipe_freeze.csr.misa_q      = csr_misa_q_i;

        r_pipe_freeze.csr.mie_n        = csr_mie_n_i  ;
        r_pipe_freeze.csr.mie_q        = csr_mie_q_i  ;
        r_pipe_freeze.csr.mie_we       = csr_mie_we_i ;
        r_pipe_freeze.csr.mtvec_n      = csr_mtvec_n_i ;
        r_pipe_freeze.csr.mtvec_q      = csr_mtvec_q_i ;
        r_pipe_freeze.csr.mtvec_mode_n = csr_mtvec_mode_n_i ;
        r_pipe_freeze.csr.mtvec_mode_q = csr_mtvec_mode_q_i ;

        r_pipe_freeze.csr.mtvt_we          = csr_mtvt_we_i ;
        r_pipe_freeze.csr.mcountinhibit_n  = csr_mcountinhibit_n_i ;
        r_pipe_freeze.csr.mcountinhibit_q  = csr_mcountinhibit_q_i ;
        r_pipe_freeze.csr.mcountinhibit_we = csr_mcountinhibit_we_i ;
        r_pipe_freeze.csr.mhpmevent_n      = csr_mhpmevent_n_i ;
        r_pipe_freeze.csr.mhpmevent_q      = csr_mhpmevent_q_i ;
        r_pipe_freeze.csr.mhpmevent_we     = csr_mhpmevent_we_i ;
        r_pipe_freeze.csr.mscratch_n       = csr_mscratch_n_i ;
        r_pipe_freeze.csr.mscratch_q       = csr_mscratch_q_i ;
        r_pipe_freeze.csr.mepc_n           = csr_mepc_n_i ;
        r_pipe_freeze.csr.mepc_q           = csr_mepc_q_i ;

        r_pipe_freeze.csr.mcause_n[31]   = csr_mcause_n_i[5] ;
        r_pipe_freeze.csr.mcause_n[30:0] = {24'h0, csr_mcause_n_i[4:0]} ;
        r_pipe_freeze.csr.mcause_q[31]   = csr_mcause_q_i[5] ;
        r_pipe_freeze.csr.mcause_q[30:0] = {24'h0, csr_mcause_q_i[4:0]} ;

        r_pipe_freeze.csr.mip_n    = csr_mip_n_i ;
        r_pipe_freeze.csr.mip_q    = csr_mip_q_i ;
        r_pipe_freeze.csr.mip_we   = csr_mip_we_i ;
        r_pipe_freeze.csr.mnxti_n  = csr_mnxti_n_i ;
        r_pipe_freeze.csr.mnxti_q  = csr_mnxti_q_i ;
        r_pipe_freeze.csr.mnxti_we = csr_mnxti_we_i ;

        r_pipe_freeze.csr.mintstatus_we   = csr_mintstatus_we_i ;
        r_pipe_freeze.csr.mintthresh_n    = csr_mintthresh_n_i ;
        r_pipe_freeze.csr.mintthresh_q    = csr_mintthresh_q_i ;
        r_pipe_freeze.csr.mintthresh_we   = csr_mintthresh_we_i ;
        r_pipe_freeze.csr.mscratchcsw_n   = csr_mscratchcsw_n_i ;
        r_pipe_freeze.csr.mscratchcsw_q   = csr_mscratchcsw_q_i ;
        r_pipe_freeze.csr.mscratchcsw_we  = csr_mscratchcsw_we_i ;
        r_pipe_freeze.csr.mscratchcswl_n  = csr_mscratchcswl_n_i ;
        r_pipe_freeze.csr.mscratchcswl_q  = csr_mscratchcswl_q_i ;
        r_pipe_freeze.csr.mscratchcswl_we = csr_mscratchcswl_we_i ;
        r_pipe_freeze.csr.mclicbase_n     = csr_mclicbase_n_i ;
        r_pipe_freeze.csr.mclicbase_q     = csr_mclicbase_q_i ;
        r_pipe_freeze.csr.mclicbase_we    = csr_mclicbase_we_i ;
        r_pipe_freeze.csr.tdata1_n        = csr_tdata1_n_i ;
        r_pipe_freeze.csr.tdata1_q        = csr_tdata1_q_i ;
        r_pipe_freeze.csr.tdata1_we       = csr_tdata1_we_i ;
        r_pipe_freeze.csr.tdata2_n        = csr_tdata2_n_i ;
        r_pipe_freeze.csr.tdata2_q        = csr_tdata2_q_i ;
        r_pipe_freeze.csr.tdata2_we       = csr_tdata2_we_i ;
        r_pipe_freeze.csr.tinfo_n         = csr_tinfo_n_i ;
        r_pipe_freeze.csr.tinfo_q         = csr_tinfo_q_i ;

        r_pipe_freeze.csr.dcsr_n  = csr_dcsr_n_i;
        r_pipe_freeze.csr.dcsr_q  = csr_dcsr_q_i;

        r_pipe_freeze.csr.dpc_n         = csr_dpc_n_i ;
        r_pipe_freeze.csr.dpc_q         = csr_dpc_q_i ;
        r_pipe_freeze.csr.dpc_we        = csr_dpc_we_i ;
        r_pipe_freeze.csr.dscratch0_n   = csr_dscratch0_n_i ;
        r_pipe_freeze.csr.dscratch0_q   = csr_dscratch0_q_i ;
        r_pipe_freeze.csr.dscratch0_we  = csr_dscratch0_we_i ;
        r_pipe_freeze.csr.dscratch1_n   = csr_dscratch1_n_i ;
        r_pipe_freeze.csr.dscratch1_q   = csr_dscratch1_q_i ;
        r_pipe_freeze.csr.dscratch1_we  = csr_dscratch1_we_i ;
        r_pipe_freeze.csr.mconfigptr_n  = csr_mconfigptr_n_i ;
        r_pipe_freeze.csr.mconfigptr_q  = csr_mconfigptr_q_i ;
        r_pipe_freeze.csr.mconfigptr_we = csr_mconfigptr_we_i ;

        r_pipe_freeze.csr.mhpmcounter_q           = csr_mhpmcounter_q_i ;
        r_pipe_freeze.csr.mhpmcounter_write_lower = csr_mhpmcounter_write_lower_i ;
        r_pipe_freeze.csr.mhpmcounter_write_upper = csr_mhpmcounter_write_upper_i ;

        r_pipe_freeze.csr.mvendorid = csr_mvendorid_i ;
        r_pipe_freeze.csr.marchid   = csr_marchid_i ;
        r_pipe_freeze.csr.mhartid   = csr_mhartid_i ;
        r_pipe_freeze.csr.mimpid    = csr_mimpid_i ;

        r_pipe_freeze.csr.mcounteren_n  = csr_mcounteren_n_i ;
        r_pipe_freeze.csr.mcounteren_q  = csr_mcounteren_q_i ;
        r_pipe_freeze.csr.mcounteren_we = csr_mcounteren_we_i ;

        r_pipe_freeze.csr.pmpcfg_n    = csr_pmpcfg_n_i    ;
        r_pipe_freeze.csr.pmpcfg_q    = csr_pmpcfg_q_i    ;
        r_pipe_freeze.csr.pmpcfg_we   = csr_pmpcfg_we_i   ;
        r_pipe_freeze.csr.pmpaddr_n   = csr_pmpaddr_n_i   ;
        r_pipe_freeze.csr.pmpaddr_q   = csr_pmpaddr_q_i   ;
        r_pipe_freeze.csr.pmpaddr_we  = csr_pmpaddr_we_i  ;
        r_pipe_freeze.csr.mseccfg_n   = csr_mseccfg_n_i   ;
        r_pipe_freeze.csr.mseccfg_q   = csr_mseccfg_q_i   ;
        r_pipe_freeze.csr.mseccfg_we  = csr_mseccfg_we_i  ;
        r_pipe_freeze.csr.mseccfgh_n  = csr_mseccfgh_n_i  ;
        r_pipe_freeze.csr.mseccfgh_q  = csr_mseccfgh_q_i  ;
        r_pipe_freeze.csr.mseccfgh_we = csr_mseccfgh_we_i ;

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

  bit clear_trace_ex;  //  = 1'b1;
  bit clear_trace_wb;

  logic [3:0] next_if_pc_mux_q[$];
  logic [2:0] next_if_exc_pc_mux_q[$];
  logic [3:0] next_if_pc_mux;
  logic [2:0] next_if_exc_pc_mux;

  logic       csr_is_irq;
  logic       is_dbg_taken;
  logic [2:0] saved_debug_cause;
  integer next_send;

  function void empty_fifo();
    while(wb_bypass_trace_q.size() != 0) begin
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
      if(next_send == new_rvfi_trace.m_order) begin
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
    rvfi_order              = new_rvfi_trace.m_order;
    rvfi_pc_rdata           = new_rvfi_trace.m_pc_rdata;
    rvfi_insn               = new_rvfi_trace.m_insn;
    rvfi_rs1_addr           = new_rvfi_trace.m_rs1_addr;
    rvfi_rs2_addr           = new_rvfi_trace.m_rs2_addr;
    rvfi_rs1_rdata          = new_rvfi_trace.m_rs1_rdata;
    rvfi_rs2_rdata          = new_rvfi_trace.m_rs2_rdata;
    rvfi_rd_addr            = new_rvfi_trace.m_rd_addr;
    rvfi_rd_wdata           = new_rvfi_trace.m_rd_wdata;

    rvfi_mem_addr           = new_rvfi_trace.mem_addr;
    rvfi_mem_rmask          = new_rvfi_trace.mem_rmask;
    rvfi_mem_wmask          = new_rvfi_trace.mem_wmask;
    rvfi_mem_rdata          = new_rvfi_trace.mem_rdata;
    rvfi_mem_wdata          = new_rvfi_trace.mem_wdata;

    rvfi_intr               = new_rvfi_trace.m_intr;

    rvfi_dbg                = new_rvfi_trace.m_dbg_cause;
    rvfi_dbg_mode           = new_rvfi_trace.m_dbg_taken;
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

    rvfi_csr_tdata_rdata[0] = 'Z;
    rvfi_csr_tdata_rmask[0] = '0;  // Does not exist
    rvfi_csr_tdata_wdata[0] = 'Z;  // Does not exist
    rvfi_csr_tdata_wmask[0] = '0;

    rvfi_csr_tdata_rdata[1] = new_rvfi_trace.m_csr.tdata1_rdata;
    rvfi_csr_tdata_rmask[1] = new_rvfi_trace.m_csr.tdata1_rmask; //'1
    rvfi_csr_tdata_wdata[1] = new_rvfi_trace.m_csr.tdata1_wdata;
    rvfi_csr_tdata_wmask[1] = new_rvfi_trace.m_csr.tdata1_wmask;

    rvfi_csr_tdata_rmask[3:2] = '1;

  /*
  assign rvfi_csr_rdata_d.tdata[2]           = csr_tdata2_q_i;
  assign rvfi_csr_wdata_d.tdata[2]           = csr_tdata2_n_i;
  assign rvfi_csr_wmask_d.tdata[2]           = csr_tdata2_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.tdata[3]           = '0;
  assign rvfi_csr_wdata_d.tdata[3]           = '0; // Not implemented, read 0
  assign rvfi_csr_wmask_d.tdata[3]           = '0;
  */

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

    csr_is_irq   = '0;
    is_dbg_taken = '0;

    $display("*****Starting pipeline computing*****\n");
    forever begin
        wait(e_pipe_monitor_ok.triggered);
        #1;

        if (r_pipe_freeze.if_valid && r_pipe_freeze.if_ready) begin
            next_if_pc_mux     = next_if_pc_mux_q.pop_front();
            next_if_exc_pc_mux = next_if_exc_pc_mux_q.pop_front();
            pc_mux_interrupt   = (next_if_pc_mux == PC_EXCEPTION && next_if_exc_pc_mux == EXC_PC_IRQ);
            pc_mux_nmi         = '0;
            pc_mux_debug       = (next_if_pc_mux == PC_EXCEPTION && (next_if_exc_pc_mux == EXC_PC_DBD | next_if_exc_pc_mux == EXC_PC_DBE));
            pc_mux_exception   = '0;
        end


        if(r_pipe_freeze.ctrl_fsm_cs==DBG_FLUSH && r_pipe_freeze.ebrk_insn_dec) begin
            if(trace_wb.m_valid) begin
              send_rvfi(trace_wb);
              trace_wb.m_valid = 1'b0;
            end
            if(trace_ex.m_valid) begin
              send_rvfi(trace_ex);
              trace_ex.m_valid = 1'b0;
            end
            if(trace_id.m_valid) begin
              // trace_id.m_csr.dcsr_we    = r_pipe_freeze.csr.dcsr_we;
              // trace_id.m_csr.dcsr_rdata = r_pipe_freeze.csr.dcsr_q;
              // trace_id.m_csr.dcsr_rmask = '1;
              // trace_id.m_csr.dcsr_wdata = r_pipe_freeze.csr.dcsr_n;
              // trace_id.m_csr.dcsr_wmask = r_pipe_freeze.csr.dcsr_we ? '1 : '0;

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



        if(trace_ex.m_valid & s_wb_valid_adjusted) begin
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
          if(!trace_wb.m_data_missaligned) begin
            send_rvfi(trace_wb);
            trace_wb.m_valid = 1'b0;
          end else begin
            if(s_wb_valid_adjusted) begin
              if (r_pipe_freeze.rf_we_wb) begin
                if(!trace_wb.m_ex_fw)begin
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

        if(trace_ex.m_valid) begin

          `CSR_FROM_PIPE(ex, misa)
          `CSR_FROM_PIPE(ex, mip)
          `CSR_FROM_PIPE(ex, tdata1)

          trace_ex.m_csr.tinfo_we    = '0; // READ ONLY csr_tinfo_we_i;
          trace_ex.m_csr.tinfo_rdata = r_pipe_freeze.csr.tinfo_q;
          trace_ex.m_csr.tinfo_rmask = '1;
          trace_ex.m_csr.tinfo_wdata = r_pipe_freeze.csr.tinfo_n;
          trace_ex.m_csr.tinfo_wmask = '0;

          if (s_wb_valid_adjusted) begin
            if(trace_wb.m_valid) begin
              send_rvfi(trace_ex);
              trace_ex.m_valid = 1'b0;
            end else begin
              if(r_pipe_freeze.rf_we_wb) begin
                trace_ex.m_rd_addr  = r_pipe_freeze.rf_addr_wb;
                trace_ex.m_rd_wdata = r_pipe_freeze.rf_wdata_wb;
                trace_ex.m_got_first_data = 1'b1;
              end

              if(!s_ex_valid_adjusted & !trace_ex.m_csr.got_minstret) begin
                trace_ex.m_csr.minstret_we    = r_pipe_freeze.csr.mhpmcounter_write_lower[2];
                trace_ex.m_csr.minstret_rdata = r_pipe_freeze.csr.mhpmcounter_q[2];
                trace_ex.m_csr.minstret_rmask = '1;
                trace_ex.m_csr.minstret_wdata = r_pipe_freeze.csr.mhpmcounter_q;
                trace_ex.m_csr.minstret_wmask = r_pipe_freeze.csr.mhpmcounter_write_lower[2] ? '1 : '0;
              end

              trace_wb.move_down_pipe(trace_ex);
              trace_ex.m_valid = 1'b0;
            end
          end else if (r_pipe_freeze.rf_we_wb) begin
              trace_ex.m_rd_addr  = r_pipe_freeze.rf_addr_wb;
              trace_ex.m_rd_wdata = r_pipe_freeze.rf_wdata_wb;
              trace_ex.m_got_first_data = 1'b1;
          end
        end

        s_ex_valid_adjusted = r_pipe_freeze.ex_valid && (r_pipe_freeze.ctrl_fsm_cs == DECODE);

        //EX_STAGE
        if(trace_id.m_valid) begin

          trace_id.m_csr.mtvec_we    = r_pipe_freeze.csr.mtvec_we;
          trace_id.m_csr.mtvec_rdata = {r_pipe_freeze.csr.mtvec_q, 6'h0, r_pipe_freeze.csr.mtvec_mode_q};
          trace_id.m_csr.mtvec_rmask = '1;
          trace_id.m_csr.mtvec_wdata = {r_pipe_freeze.csr.mtvec_n , 6'h0, r_pipe_freeze.csr.mtvec_mode_n};;
          trace_id.m_csr.mtvec_wmask = r_pipe_freeze.csr.mtvec_we ? '1 : '0;

          if(!csr_is_irq) begin
            trace_id.m_csr.mstatus_we    = r_pipe_freeze.csr.mstatus_we;
            trace_id.m_csr.mstatus_rdata = r_pipe_freeze.csr.mstatus_full_q;
            trace_id.m_csr.mstatus_rmask = '1;
            trace_id.m_csr.mstatus_wdata = r_pipe_freeze.csr.mstatus_full_n;
            trace_id.m_csr.mstatus_wmask = r_pipe_freeze.csr.mstatus_we ? '1 : '0;

            `CSR_FROM_PIPE(id, mepc)
            if(trace_id.m_csr.mcause_we == '0) begin //for debug purpose
              `CSR_FROM_PIPE(id, mcause)
            end
          end

          `CSR_FROM_PIPE(id, mcountinhibit)
          `CSR_FROM_PIPE(id, mscratch)
          `CSR_FROM_PIPE(id, mie)

          if (s_ex_valid_adjusted) begin  //A valid instruction goes from ID to EX
            if(trace_ex.m_valid) begin //We need to bypass wb
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

            trace_ex.move_down_pipe(trace_id); // The instruction moves forward from ID to EX
            trace_id.m_valid = 1'b0;

          end else if (r_pipe_freeze.ex_reg_we) begin
            trace_id.m_ex_fw          = 1'b1;
            trace_id.m_rd_addr        = r_pipe_freeze.ex_reg_addr;
            trace_id.m_rd_wdata       = r_pipe_freeze.ex_reg_wdata;
            trace_id.m_got_regs_write = 1'b1;
          end
        end

        //ID_STAGE
        if(s_new_valid_insn) begin// There is a new valid instruction
          if(trace_id.m_valid) begin
            if(trace_ex.m_valid) begin
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
          trace_id.m_intr      = trace_if.m_intr;
          trace_id.m_dbg_taken = trace_if.m_dbg_taken;
          trace_id.m_dbg_cause = trace_if.m_dbg_cause;
          trace_id.m_is_ebreak = trace_if.m_is_ebreak;

          trace_if.m_valid = 1'b0;
          s_id_done = 1'b0;
          trace_id.m_csr.mvendorid_we    = '0;
          trace_id.m_csr.mvendorid_rdata = r_pipe_freeze.csr.mvendorid;
          trace_id.m_csr.mvendorid_rmask = '1;
          trace_id.m_csr.mvendorid_wdata = '0;
          trace_id.m_csr.mvendorid_wmask = '0;

          trace_id.m_csr.marchid_we    = '0;
          trace_id.m_csr.marchid_rdata = r_pipe_freeze.csr.marchid;
          trace_id.m_csr.marchid_rmask = '0;
          trace_id.m_csr.marchid_wdata = '0;
          trace_id.m_csr.marchid_wmask = '0;

          `CSR_FROM_PIPE(id, dscratch0)
          `CSR_FROM_PIPE(id, dscratch1)

          trace_id.m_csr.mstatus_we    = r_pipe_freeze.csr.mstatus_we;
          trace_id.m_csr.mstatus_rdata = r_pipe_freeze.csr.mstatus_full_q;
          trace_id.m_csr.mstatus_rmask = '1;
          trace_id.m_csr.mstatus_wdata = r_pipe_freeze.csr.mstatus_full_n;
          trace_id.m_csr.mstatus_wmask = r_pipe_freeze.csr.mstatus_we ? '1 : '0;

        end else begin
          if(trace_id.m_valid) begin
            `CSR_FROM_PIPE(id, dscratch0)
            `CSR_FROM_PIPE(id, dscratch1)
          end
        end

        //IF_STAGE


        // pc_mux_nmi             = (r_pipe_freeze.ctrl_fsm_cs.pc_mux == PC_TRAP_NMI);
        // pc_mux_debug           = (r_pipe_freeze.ctrl_fsm_cs.pc_mux == PC_TRAP_DBD);
        // pc_mux_exception       = (r_pipe_freeze.ctrl_fsm_cs.pc_mux == PC_TRAP_EXC) || pc_mux_debug_exception ;
        // if(next_if_pc_mux_q.size() != 0 && r_pipe_freeze.instr_rvalid) begin
        //     next_if_pc_mux = next_if_pc_mux_q.pop_front();
        //     next_if_exc_pc_mux = next_if_exc_pc_mux_q.pop_front();
        // end
        if (r_pipe_freeze.if_valid && r_pipe_freeze.if_ready) begin
          if(trace_if.m_valid && r_pipe_freeze.id_valid && r_pipe_freeze.id_ready && !trace_id.m_valid && r_pipe_freeze.ebrk_insn_dec) begin//trace_if.m_valid & r_pipe_freeze.is_decoding) begin
            trace_id.init(trace_if.m_insn);
            trace_id.m_intr      = trace_if.m_intr;
            trace_id.m_dbg_taken = trace_if.m_dbg_taken;
            trace_id.m_dbg_cause = trace_if.m_dbg_cause;
            trace_id.m_is_ebreak = '1;//trace_if.m_is_ebreak;
            s_id_done = 1'b0;
            trace_if.m_valid = 1'b0;
          end
            trace_if.m_insn      = r_pipe_freeze.instr_if;  //Instr comes from if, buffer for one cycle
            trace_if.m_pc_rdata  = r_pipe_freeze.pc_if;
            trace_if.m_dbg_taken = is_dbg_taken;
            trace_if.m_dbg_cause = saved_debug_cause;
            trace_if.m_is_ebreak = '0;

            //check if interrupt
            if(pc_mux_interrupt || pc_mux_nmi || pc_mux_exception) begin
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

        if(r_pipe_freeze.pc_set & r_pipe_freeze.prefetch_req) begin
            next_if_pc_mux_q.delete();
            next_if_exc_pc_mux_q.delete();
        end
        if(r_pipe_freeze.instr_req && r_pipe_freeze.instr_grant) begin
            next_if_pc_mux_q.push_back(r_pipe_freeze.pc_mux);
            next_if_exc_pc_mux_q.push_back(r_pipe_freeze.exc_pc_mux);
        end

        // if(r_pipe_freeze.ctrl_fsm_cs==DECODE) begin
        //     trace_ex.m_csr.dcsr_we    = r_pipe_freeze.csr.dcsr_we;
        //     trace_ex.m_csr.dcsr_rdata = r_pipe_freeze.csr.dcsr_q;
        //     trace_ex.m_csr.dcsr_rmask = '1;
        //     trace_ex.m_csr.dcsr_wdata = r_pipe_freeze.csr.dcsr_n;
        //     trace_ex.m_csr.dcsr_wmask = r_pipe_freeze.csr.dcsr_we ? '1 : '0;
        //   end

        if(csr_is_irq) begin
          trace_id.m_csr.mstatus_we    = r_pipe_freeze.csr.mstatus_we;
          trace_id.m_csr.mstatus_rdata = r_pipe_freeze.csr.mstatus_full_q;
          trace_id.m_csr.mstatus_rmask = '1;
          trace_id.m_csr.mstatus_wdata = r_pipe_freeze.csr.mstatus_full_n;
          trace_id.m_csr.mstatus_wmask = r_pipe_freeze.csr.mstatus_we ? '1 : '0;

          `CSR_FROM_PIPE(id, mepc)
          `CSR_FROM_PIPE(id, mcause)
        end

        if(!s_id_done) begin
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
        s_id_done = r_pipe_freeze.id_valid;
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
      if(rvfi_trace_q.size() != 0) begin
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

  /*
  // The pc_mux signals probe the MUX in the IF stage to extract information about events in the WB stage.
  // These signals are therefore used both in the WB stage to see effects of the executed instruction (e.g. rvfi_trap), and
  // in the IF stage to see the reason for executing the instruction (e.g. rvfi_intr).
  assign pc_mux_interrupt       = (ctrl_fsm_i.pc_mux == PC_TRAP_IRQ);
  assign pc_mux_nmi             = (ctrl_fsm_i.pc_mux == PC_TRAP_NMI);
  assign pc_mux_debug           = (ctrl_fsm_i.pc_mux == PC_TRAP_DBD);
  assign pc_mux_exception       = (ctrl_fsm_i.pc_mux == PC_TRAP_EXC) || pc_mux_debug_exception ;
  // The debug exception for mret is taken in ID (contrary to all other exceptions). In the case where we have a dret in the EX stage at the same time,
  // this can lead to a situation we take the exception for the mret even though it never reaches the WB stage.
  // This works in rtl because the exception handler instructions will get killed.
  // In rvfi this exception needs to be ignored as it comes from an instruction that does not retire.
  assign pc_mux_debug_exception = (ctrl_fsm_i.pc_mux == PC_TRAP_DBE) && !dret_in_ex_i;
  assign pc_mux_dret            = (ctrl_fsm_i.pc_mux == PC_DRET);

  assign branch_taken_ex = branch_in_ex_i && branch_decision_ex_i;

  // Assign rvfi channels
  assign rvfi_halt = 1'b0; // No intruction causing halt in cv32e40x
  assign rvfi_ixl = 2'b01; // XLEN for current privilege level, must be 1(32) for RV32 systems

  logic         in_trap_clr;
  // Clear in trap pipeline when it reaches rvfi_intr
  // This is done to avoid reporting already signaled triggers as supressed during by debug
  assign in_trap_clr = wb_valid_adjusted && in_trap[STAGE_WB].intr;


  // Store information about wakeup until first instruction is retired
  // This information needs to be stored at the wakeup because other interrupts
  // can be triggered between wakeup and the first instruction executed after wakeup
  rvfi_wu_t     rvfi_wu_next;
  logic         store_irq_wu_cause;

  assign rvfi_wu_next.wu = rvfi_sleep; // If sleep is still set, it is the first instruction after wakeup
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      wb_valid_wfi_delayed   <= 1'b0;
      store_irq_wu_cause     <= 1'b0;
      rvfi_wu_next.interrupt <= 1'b0;
      rvfi_wu_next.debug     <= 1'b0;
      rvfi_wu_next.cause     <= '0;
    end else begin
      wb_valid_wfi_delayed <= wb_valid_i && (ctrl_fsm_ns_i == SLEEP);
      // Store wake-up sources when core exits sleep
      if ((ctrl_fsm_cs_i == SLEEP) && (ctrl_fsm_ns_i != SLEEP)) begin
        rvfi_wu_next.interrupt <= irq_wu_ctrl_i;
        store_irq_wu_cause     <= irq_wu_ctrl_i;
        rvfi_wu_next.debug     <= pending_debug_i || debug_mode_q_i;
      end
      // IRQ cause is flopped and is therefore one cycle behind wakeup triggers
      if (store_irq_wu_cause) begin
        store_irq_wu_cause <= 1'b0;
        rvfi_wu_next.cause <= {'0, irq_id_ctrl_i}; // NMIs will not wake up the core
      end
    end
  end

  // Set rvfi_trap for instructions causing exception or debug entry.
  rvfi_trap_t  rvfi_trap_next;

  always_comb begin
    rvfi_trap_next = '0;

    if (pc_mux_debug) begin
      // All debug entries will set pc_mux_debug but only synchronous debug entries will set wb_valid (and in turn rvfi_valid)
      // as asynchronous entries will kill the WB stage whereas synchronous entries will not.
      // Indicate that the trap is a synchronous trap into debug mode
      rvfi_trap_next.debug       = 1'b1;
      // Special case for debug entry from debug mode caused by EBREAK as it is not captured by ctrl_fsm_i.debug_cause
      rvfi_trap_next.debug_cause = ebreak_in_wb_i ? DBG_CAUSE_EBREAK : ctrl_fsm_i.debug_cause;
    end

    if (pc_mux_exception) begin
      // Indicate synchronous (non-debug entry) trap
      rvfi_trap_next.exception       = 1'b1;
      rvfi_trap_next.exception_cause = ctrl_fsm_i.csr_cause.exception_code[5:0]; // All synchronous exceptions fit in lower 6 bits

      // Separate exception causes with the same ecseption cause code
      case (ctrl_fsm_i.csr_cause.exception_code)
        EXC_CAUSE_INSTR_FAULT : begin
          rvfi_trap_next.cause_type = instr_pmp_err[STAGE_WB] ? 2'h1 : 2'h0;
        end
        EXC_CAUSE_BREAKPOINT : begin
          // Todo: Add support for trigger match exceptions when implemented in rtl
        end
        EXC_CAUSE_LOAD_FAULT : begin
          rvfi_trap_next.cause_type = mem_err[STAGE_WB];
        end
        EXC_CAUSE_STORE_FAULT : begin
          rvfi_trap_next.cause_type = mem_err[STAGE_WB];
        end
        default : begin
          // rvfi_trap_next.cause_type is only set for exception codes that can have multiple causes
        end
      endcase // case (ctrl_fsm_i.csr_cause.exception_code)

    end

    if(pending_single_step_i && single_step_allowed_i) begin
      // The timing of the single step debug entry does not allow using pc_mux for detection
      rvfi_trap_next.debug       = 1'b1;
      rvfi_trap_next.debug_cause = DBG_CAUSE_STEP;

      // In the case of an exception in WB and pending single step, both the exception and the debug flag will be set
    end

    // Set trap bit if there is an exception or debug entry
    rvfi_trap_next.trap = rvfi_trap_next.exception || rvfi_trap_next.debug;
  end


  // WFI instructions can use two cycles in WB if there are no flopped pending wakeup sources.
  // In this case their retirement happens in the second cycle, but becuase it makes no difference functionally in rtl,
  // wb_valid is set in the first WFI cycle to avoid introducing support logic for a multicycle WB stage.
  // Moving wb_valid to second cycle of WFI instructions in these cases is therefore needed.
  assign wb_valid_adjusted = (sys_wfi_insn_wb_i && ((ctrl_fsm_ns_i == SLEEP) || (ctrl_fsm_cs_i == SLEEP))) ?
                             wb_valid_wfi_delayed :
                             wb_valid_i;
  */

/*
  // Pipeline stage model //
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      // pc_wdata           <= '0;
      // in_trap            <= '0;
      // debug_mode         <= '0;
      // debug_cause        <= '0;
      // instr_pmp_err      <= '0;
      // rs1_addr           <= '0;
      // rs2_addr           <= '0;
      // rs1_rdata          <= '0;
      // rs2_rdata          <= '0;
      // mem_rmask          <= '0;
      // mem_wmask          <= '0;
      // ex_mem_addr        <= '0;
      // ex_mem_wdata       <= '0;
      // mem_err            <= '0;
      ex_csr_rdata   <= '0;
      // rvfi_dbg           <= '0;
      // rvfi_dbg_mode      <= '0;
      // rvfi_wu            <= '0;
      // rvfi_sleep         <= 1'b0;

      // rvfi_pc_wdata      <= '0;
      // rvfi_trap          <= '0;
      // rvfi_intr          <= 1'b0;
      rvfi_csr_rdata <= '0;
      rvfi_csr_wdata <= '0;
      rvfi_csr_wmask <= '0;

      // rvfi_mem_addr      <= '0;
      // rvfi_mem_rmask     <= '0;
      // rvfi_mem_rdata     <= '0;
      // rvfi_mem_wmask     <= '0;
      // rvfi_mem_wdata     <= '0;

    end else begin

      //// IF Stage ////
      // if (if_valid_i && id_ready_i) begin
      // debug_mode [STAGE_ID] <= ctrl_fsm_i.debug_mode; // Probing in IF to ensure LSU instructions that are not killed can complete
      // instr_pmp_err[STAGE_ID] <= instr_pmp_err_if_i;    // Instruction fetch pmp error probed to separate pmp- from pma-errors

      // Capturing events that happen when the IF stage is not valid and
      // propagating them through the pipeline with the next valid instruction

      // Capture events
      // in_trap    [STAGE_ID] <= in_trap    [STAGE_IF];
      // debug_cause[STAGE_ID] <= debug_cause[STAGE_IF];

      // Clear captured events
      // in_trap    [STAGE_IF] <= 1'b0;
      // debug_cause[STAGE_IF] <= '0;

      // end else begin
      // if (in_trap_clr) begin
      // Clear interrupt pipeline when it reaches rvfi_intr
      // in_trap    [STAGE_ID] <= '0;
      // end

      // IF stage is killed and not valid during debug entry. If debug is taken,
      // debug cause is saved to propagate through rvfi pipeline together with next valid instruction
      // if (pc_mux_debug) begin
      // Debug cause input only valid during debug taken
      // Special case for debug entry from debug mode caused by EBREAK as it is not captured by ctrl_fsm_i.debug_cause
      // A higher priority debug request (e.g. trigger match) will pull ebreak_in_wb_i low and allow the debug cause to propagate
      // debug_cause[STAGE_IF] <=  ebreak_in_wb_i ? 3'h1 : ctrl_fsm_i.debug_cause;

      // If there is a trap in the pipeline when debug is taken, the trap will be supressed but the side-effects will not.
      // The succeeding instruction therefore needs to re-trigger the intr signals if it it did not reach the rvfi output.
      // in_trap[STAGE_IF] <= in_trap[STAGE_IF].intr ? in_trap[STAGE_IF] :
      //  in_trap[STAGE_ID].intr ? in_trap[STAGE_ID] :
      //  in_trap[STAGE_EX].intr ? in_trap[STAGE_EX] :
      // in_trap[STAGE_WB];
      // end

      // Picking up trap entry when IF is not valid to propagate for next valid instruction
      // The in trap signal is set for the first instruction of interrupt- and exception handlers (not debug handler)
      // if (pc_mux_interrupt || pc_mux_nmi || pc_mux_exception) begin
      // in_trap[STAGE_IF].intr      <= 1'b1;
      // in_trap[STAGE_IF].interrupt <= pc_mux_interrupt || pc_mux_nmi;
      // in_trap[STAGE_IF].exception <= pc_mux_exception;
      // in_trap[STAGE_IF].cause     <= ctrl_fsm_i.csr_cause.exception_code;
      // end
      // end

      //// ID Stage ////
      // if(id_valid_i && ex_ready_i) begin

      //   if (jump_in_id_i) begin
      //     // Predicting mret/jump explicitly instead of using branch_addr_n to
      //     // avoid including asynchronous traps and debug reqs in prediction
      //     pc_wdata [STAGE_EX] <= (sys_en_id_i && sys_mret_insn_id_i) ? csr_mepc_q_i : jump_target_id_i;
      //   end else begin
      //     pc_wdata [STAGE_EX] <= is_compressed_id_i ?  pc_id_i + 2 : pc_id_i + 4;
      //   end

      //   in_trap    [STAGE_EX] <= in_trap    [STAGE_ID];
      //   debug_mode [STAGE_EX] <= debug_mode [STAGE_ID];
      //   debug_cause[STAGE_EX] <= debug_cause[STAGE_ID];
      //   instr_pmp_err[STAGE_EX] <= instr_pmp_err[STAGE_ID];
      //   rs1_addr   [STAGE_EX] <= rs1_addr_id;
      //   rs2_addr   [STAGE_EX] <= rs2_addr_id;
      //   rs1_rdata  [STAGE_EX] <= rs1_rdata_id;
      //   rs2_rdata  [STAGE_EX] <= rs2_rdata_id;
      //   mem_rmask  [STAGE_EX] <= (lsu_en_id_i && !lsu_we_id_i) ? rvfi_mem_mask_int : '0;
      //   mem_wmask  [STAGE_EX] <= (lsu_en_id_i &&  lsu_we_id_i) ? rvfi_mem_mask_int : '0;
      // end else begin
      //   if (in_trap_clr) begin
      //     // Clear interrupt pipeline when it reaches rvfi_intr
      //     in_trap    [STAGE_EX] <= '0;
      //   end
      // end

      //// EX Stage ////
      if (ex_valid_i && wb_ready_i) begin
        //   // Predicting branch target explicitly to avoid predicting asynchronous events
        //   pc_wdata   [STAGE_WB] <= branch_taken_ex ? branch_target_ex_i : pc_wdata[STAGE_EX];
        //   debug_mode [STAGE_WB] <= debug_mode         [STAGE_EX];
        //   debug_cause[STAGE_WB] <= debug_cause        [STAGE_EX];
        //   instr_pmp_err[STAGE_WB] <= instr_pmp_err    [STAGE_EX];
        //   rs1_addr   [STAGE_WB] <= rs1_addr           [STAGE_EX];
        //   rs2_addr   [STAGE_WB] <= rs2_addr           [STAGE_EX];
        //   rs1_rdata  [STAGE_WB] <= rs1_rdata          [STAGE_EX];
        //   rs2_rdata  [STAGE_WB] <= rs2_rdata          [STAGE_EX];
        //   mem_rmask  [STAGE_WB] <= mem_rmask          [STAGE_EX];
        //   mem_wmask  [STAGE_WB] <= mem_wmask          [STAGE_EX];
        //   in_trap    [STAGE_WB] <= in_trap            [STAGE_EX];

        //   if (!lsu_split_q_ex_i) begin
        //     // The second part of the split misaligned acess is suppressed to keep
        //     // the start address and data for the whole misaligned transfer
        //     ex_mem_addr         <= rvfi_mem_addr_d;
        //     ex_mem_wdata        <= rvfi_mem_wdata_d;
        //   end

        //   mem_err   [STAGE_WB]  <= lsu_pmp_err_ex_i        ? MEM_ERR_PMP :
        //                            lsu_pma_err_atomic_ex_i ? MEM_ERR_ATOMIC :
        //                                                      MEM_ERR_IO_ALIGN;

        //   // Read autonomuos CSRs from EX perspective
        ex_csr_rdata <= ex_csr_rdata_d;

        // end else begin
        //   if (in_trap_clr) begin
        //     // Clear interrupt pipeline when it reaches rvfi_intr
        //     in_trap    [STAGE_WB] <= '0;
        //   end
      end

      //// WB Stage ////
      //
      // rvfi_trap       <= rvfi_trap_next;
      //
      // rvfi_mem_rdata  <= lsu_rdata_wb_i;

      // Read/Write CSRs
      rvfi_csr_rdata <= rvfi_csr_rdata_d;
      rvfi_csr_wdata <= rvfi_csr_wdata_d;
      rvfi_csr_wmask <= rvfi_csr_wmask_d;
      //
      // rvfi_intr      <= in_trap   [STAGE_WB];
      // rvfi_mem_rmask <= mem_rmask [STAGE_WB];
      // rvfi_mem_wmask <= mem_wmask [STAGE_WB];
      // rvfi_mem_addr  <= ex_mem_addr;
      // rvfi_mem_wdata <= ex_mem_wdata;
      //

      //
      // rvfi_dbg       <= debug_cause[STAGE_WB];
      // rvfi_dbg_mode  <= debug_mode [STAGE_WB];
      //
      // rvfi_sleep     <= (ctrl_fsm_ns_i == SLEEP);
      // rvfi_wu        <= rvfi_wu_next;
      //
      // Set expected next PC, half-word aligned
      // Predict synchronous exceptions and synchronous debug entry in WB to include all causes
      // rvfi_pc_wdata <= (pc_mux_debug || pc_mux_exception) ? branch_addr_n_i & ~32'b1 :
      //  (pc_mux_dret) ? csr_dpc_q_i :
      //  pc_wdata[STAGE_WB] & ~32'b1;
      // end else begin
      // rvfi_sleep     <= rvfi_sleep; // Keep sleep signal asserted until next valid WB
    end
  end  // always_ff @
  */
  /*
  assign rvfi_nmip = {nmi_is_store_i, nmi_pending_i};

  // Capture possible performance counter writes during WB, before wb_valid
  // If counter write happens before wb_valid (LSU stalled waiting for rvalid for example),
  // we must keep _n and _q values to correctly set _rdata and _wdata when rvfi_valid is set.
  // If wb_valid occurs in the same cycle as the write, the flags are zero and any
  // stored values will not be used.
  generate for (genvar i = 0; i < 32; i++)
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        mhpmcounter_l_rdata_q[i] <= '0;
        mhpmcounter_h_rdata_q[i] <= '0;
        mhpmcounter_l_wdata_q[i] <= '0;
        mhpmcounter_h_wdata_q[i] <= '0;
        mhpmcounter_l_during_wb[i] <= 1'b0;
        mhpmcounter_h_during_wb[i] <= 1'b0;
      end else begin
        // Clear flags on wb_valid
        if (wb_valid_i) begin
          mhpmcounter_l_during_wb[i] <= 1'b0;
          mhpmcounter_h_during_wb[i] <= 1'b0;
        end else begin
          // Capture counter writes.
          if (csr_mhpmcounter_we_l[i]) begin
            mhpmcounter_l_during_wb[i] <= 1'b1;
            mhpmcounter_l_rdata_q[i]   <= csr_mhpmcounter_q_l[i];
            mhpmcounter_l_wdata_q[i]   <= csr_mhpmcounter_n_l[i];
          end

          if (csr_mhpmcounter_we_h[i]) begin
            mhpmcounter_h_during_wb[i] <= 1'b1;
            mhpmcounter_h_rdata_q[i]   <= csr_mhpmcounter_q_h[i];
            mhpmcounter_h_wdata_q[i]   <= csr_mhpmcounter_n_h[i];
          end
        end
      end
    end
  endgenerate
  //////////////////


  // Byte enable based on data size
  always_comb begin
    unique case (lsu_size_id_i)
      2'b00:   rvfi_mem_mask_int = 4'b0001;
      2'b01:   rvfi_mem_mask_int = 4'b0011;
      2'b10:   rvfi_mem_mask_int = 4'b1111;
      default: rvfi_mem_mask_int = 4'b0000;
    endcase
  end

  // Memory adddress
  assign rvfi_mem_addr_d = data_addr_ex_i;

  // Align Memory write data
  assign rvfi_mem_wdata_d  = data_wdata_ror[31:0];
  assign data_wdata_ror    = {data_wdata_ex_i, data_wdata_ex_i} >> (8*rvfi_mem_addr_d[1:0]); // Rotate right

  // Destination Register
  // The rd_addr signal in rtl can contain contain unused non-zero values when not reading
  assign rd_addr_wb  = (rf_we_wb_i)      ? rf_addr_wb_i  : '0;
  assign rd_wdata_wb = (rd_addr_wb != 0) ? rf_wdata_wb_i : '0; // Gating wdata for x0 as it is assigned to 0
                                                               // in RTL regardless of wdata (which can be non-zero)

  // Source Register Read Data
  // Setting register read data from operands if there was a read and clearing if there was not as operands can contain
  // data that is not read from the register file when not reading (e.g. for immediate instructions).
  // Can't use register file rdata directly as forwarded data is needed for instructions using the same register back-to-back
  assign rs1_rdata_id = (rf_re_id_i[0]) ? operand_a_fw_id_i : '0;
  assign rs2_rdata_id = (rf_re_id_i[1]) ? operand_b_fw_id_i : '0;
  // The rs* address signals can contain unused non-zero values when not reading
  assign rs1_addr_id  = (rf_re_id_i[0]) ? rs1_addr_id_i     : '0;
  assign rs2_addr_id  = (rf_re_id_i[1]) ? rs2_addr_id_i     : '0;

  ////////////////////////////////
  //  CSRs                      //
  ////////////////////////////////

  // Zc* Register (Jump Vector Table)
  assign rvfi_csr_rdata_d.jvt                = csr_jvt_q_i;
  assign rvfi_csr_wdata_d.jvt                = csr_jvt_n_i;
  assign rvfi_csr_wmask_d.jvt                = csr_jvt_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.mstatush           = csr_mstatush_q_i;
  assign rvfi_csr_wdata_d.mstatush           = csr_mstatush_n_i;
  assign rvfi_csr_wmask_d.mstatush           = csr_mstatush_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.mtvt               = csr_mtvt_q_i;
  assign rvfi_csr_wdata_d.mtvt               = csr_mtvt_n_i;
  assign rvfi_csr_wmask_d.mtvt               = csr_mtvt_we_i   ? '1 : '0;

  assign rvfi_csr_rdata_d.mhpmevent          = csr_mhpmevent_q_i;
  assign rvfi_csr_wdata_d.mhpmevent          = csr_mhpmevent_n_i;
  assign rvfi_csr_wmask_d.mhpmevent[2:0]     = '0; // No mhpevent0-2 registers
  generate for (genvar i = 3; i < 32; i++)
    assign rvfi_csr_wmask_d.mhpmevent[i]     = csr_mhpmevent_we_i[i] ? '1 : '0;
  endgenerate

*/
  // Machine trap handling
  assign rvfi_csr_rdata_d.mscratch = csr_mscratch_q_i;
  assign rvfi_csr_wdata_d.mscratch = csr_mscratch_n_i;
  assign rvfi_csr_wmask_d.mscratch = r_pipe_freeze.csr.mscratch_we ? '1 : '0;
  assign rvfi_csr_rdata_d.mepc = csr_mepc_q_i;
  assign rvfi_csr_wdata_d.mepc = csr_mepc_n_i;


  /*
  assign rvfi_csr_rdata_d.mtval              = '0;
  assign rvfi_csr_wdata_d.mtval              = '0; // Not implemented, read 0
  assign rvfi_csr_wmask_d.mtval              = '0;

  // MIP is read in EX by CSR instructions, evaluated combinatorically in WB by the WFI instruction,
  // and is evaluated in WB for all other instructions
  assign ex_csr_rdata_d.mip                  = csr_mip_q_i;
  assign rvfi_csr_rdata_d.mip                = csr_en_wb_i       ? ex_csr_rdata.mip :
                                               sys_wfi_insn_wb_i ?            irq_i :
                                                                        csr_mip_q_i;
  assign rvfi_csr_wdata_d.mip                = csr_mip_n_i;
  assign rvfi_csr_wmask_d.mip                = csr_mip_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.mnxti              = csr_mnxti_q_i;
  assign rvfi_csr_wdata_d.mnxti              = csr_mnxti_n_i;
  assign rvfi_csr_wmask_d.mnxti              = csr_mnxti_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.mintstatus         = csr_mintstatus_q_i;
  assign rvfi_csr_wdata_d.mintstatus         = csr_mintstatus_n_i;
  assign rvfi_csr_wmask_d.mintstatus         = csr_mintstatus_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.mintthresh         = csr_mintthresh_q_i;
  assign rvfi_csr_wdata_d.mintthresh         = csr_mintthresh_n_i;
  assign rvfi_csr_wmask_d.mintthresh         = csr_mintthresh_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.mscratchcsw        = csr_mscratchcsw_q_i;
  assign rvfi_csr_wdata_d.mscratchcsw        = csr_mscratchcsw_n_i;
  assign rvfi_csr_wmask_d.mscratchcsw        = csr_mscratchcsw_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.mscratchcswl       = csr_mscratchcswl_q_i;
  assign rvfi_csr_wdata_d.mscratchcswl       = csr_mscratchcswl_n_i;
  assign rvfi_csr_wmask_d.mscratchcswl       = csr_mscratchcswl_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.mclicbase          = csr_mclicbase_q_i;
  assign rvfi_csr_wdata_d.mclicbase          = csr_mclicbase_n_i;
  assign rvfi_csr_wmask_d.mclicbase          = csr_mclicbase_we_i ? '1 : '0;

  // Trigger
  assign rvfi_csr_rdata_d.tselect            = '0;
  assign rvfi_csr_wdata_d.tselect            = '0; // Not implemented, read 0
  assign rvfi_csr_wmask_d.tselect            = '0;

  // TODO: do not tie off mcontext inside the module
  assign rvfi_csr_rdata_d.mcontext           = '0;
  assign rvfi_csr_wdata_d.mcontext           = '0; // Not implemented, read 0
  assign rvfi_csr_wmask_d.mcontext           = '0;

  assign rvfi_csr_rdata_d.scontext           = '0;
  assign rvfi_csr_wdata_d.scontext           = '0; // Not implemented, read 0
  assign rvfi_csr_wmask_d.scontext           = '0;

  */
  // Debug / Trace
  assign ex_csr_rdata_d.nmip                 = csr_dcsr_q_i[3]; // dcsr.nmip is autonomous. Propagate read value from EX stage

  /*
  assign rvfi_csr_rdata_d.dpc                = csr_dpc_q_i;
  assign rvfi_csr_wdata_d.dpc                = csr_dpc_n_i;
  assign rvfi_csr_wmask_d.dpc                = csr_dpc_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.dscratch[0]        = csr_dscratch0_q_i;
  assign rvfi_csr_wdata_d.dscratch[0]        = csr_dscratch0_n_i;
  assign rvfi_csr_wmask_d.dscratch[0]        = csr_dscratch0_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.dscratch[1]        = csr_dscratch1_q_i;
  assign rvfi_csr_wdata_d.dscratch[1]        = csr_dscratch1_n_i;
  assign rvfi_csr_wmask_d.dscratch[1]        = csr_dscratch1_we_i ? '1 : '0;

  // Performance Monitors
  generate
    for (genvar i = 0; i < 32; i++) begin
      assign csr_mhpmcounter_n_l[i]  = csr_mhpmcounter_n_i[i][31: 0];
      assign csr_mhpmcounter_n_h[i]  = csr_mhpmcounter_n_i[i][63:32];
      assign csr_mhpmcounter_q_l[i]  = csr_mhpmcounter_q_i[i][31: 0];
      assign csr_mhpmcounter_q_h[i]  = csr_mhpmcounter_q_i[i][63:32];
      assign csr_mhpmcounter_we_l[i] = csr_mhpmcounter_we_i[i][0] ? '1 : '0;
      assign csr_mhpmcounter_we_h[i] = csr_mhpmcounter_we_i[i][1] ? '1 : '0;
    end
  endgenerate

  assign ex_csr_rdata_d.mcycle               = csr_mhpmcounter_q_l [CSR_MCYCLE & 'hF];
  assign rvfi_csr_rdata_d.mcycle             = ex_csr_rdata.mcycle;
  assign rvfi_csr_wdata_d.mcycle             = csr_mhpmcounter_n_l [CSR_MCYCLE & 'hF];
  assign rvfi_csr_wmask_d.mcycle             = csr_mhpmcounter_we_l[CSR_MCYCLE & 'hF];
*/

  /*
  assign rvfi_csr_rdata_d.mhpmcounter[ 2:0]  = 'Z;
  assign rvfi_csr_wdata_d.mhpmcounter[ 2:0]  = 'Z; // Does not exist
  assign rvfi_csr_wmask_d.mhpmcounter[ 2:0]  = '0;

  // Used flopped values in case write happened before wb_valid
  generate
    for (genvar i = 3; i < 32; i++) begin
      assign rvfi_csr_rdata_d.mhpmcounter[i]  = !mhpmcounter_l_during_wb[i] ? csr_mhpmcounter_q_l [i] : mhpmcounter_l_rdata_q[i];
      assign rvfi_csr_wdata_d.mhpmcounter[i]  = !mhpmcounter_l_during_wb[i] ? csr_mhpmcounter_n_l [i] : mhpmcounter_l_wdata_q[i];
      assign rvfi_csr_wmask_d.mhpmcounter[i]  = !mhpmcounter_l_during_wb[i] ? csr_mhpmcounter_we_l[i] : '1;
    end
  endgenerate

  assign ex_csr_rdata_d.mcycleh              = csr_mhpmcounter_q_h [CSR_MCYCLEH & 'hF];
  assign rvfi_csr_rdata_d.mcycleh            = ex_csr_rdata.mcycleh;
  assign rvfi_csr_wdata_d.mcycleh            = csr_mhpmcounter_n_h [CSR_MCYCLEH & 'hF];
  assign rvfi_csr_wmask_d.mcycleh            = csr_mhpmcounter_we_h[CSR_MCYCLEH & 'hF];
*/
  assign rvfi_csr_rdata_d.minstreth          = (MHPMCOUNTER_WIDTH == 64) ? csr_mhpmcounter_q_i[2][63:32] : '0;//!mhpmcounter_h_during_wb[CSR_MINSTRETH & 'hF] ? csr_mhpmcounter_q_h [CSR_MINSTRETH & 'hF] : mhpmcounter_h_rdata_q[CSR_MINSTRETH & 'hF];
  assign rvfi_csr_wdata_d.minstreth          = (MHPMCOUNTER_WIDTH == 64) ? csr_wdata_int_i : '0;//!mhpmcounter_h_during_wb[CSR_MINSTRETH & 'hF] ? csr_mhpmcounter_n_h [CSR_MINSTRETH & 'hF] : mhpmcounter_h_wdata_q[CSR_MINSTRETH & 'hF];
  assign rvfi_csr_wmask_d.minstreth          = (MHPMCOUNTER_WIDTH == 64) ? (csr_mhpmcounter_write_upper_i[2] ? '1 : '0 ) : '0;//!mhpmcounter_h_during_wb[CSR_MINSTRETH & 'hF] ? csr_mhpmcounter_we_h[CSR_MINSTRETH & 'hF] : '1;
  /*
  assign rvfi_csr_rdata_d.mhpmcounterh[ 2:0] = 'Z;
  assign rvfi_csr_wdata_d.mhpmcounterh[ 2:0] = 'Z;  // Does not exist
  assign rvfi_csr_wmask_d.mhpmcounterh[ 2:0] = '0;

  // Used flopped values in case write happened before wb_valid
  generate
    for (genvar i = 3; i < 32; i++) begin
      assign rvfi_csr_rdata_d.mhpmcounterh[i]  = !mhpmcounter_h_during_wb[i] ? csr_mhpmcounter_q_h [i] : mhpmcounter_h_rdata_q[i];
      assign rvfi_csr_wdata_d.mhpmcounterh[i]  = !mhpmcounter_h_during_wb[i] ? csr_mhpmcounter_n_h [i] : mhpmcounter_h_wdata_q[i];
      assign rvfi_csr_wmask_d.mhpmcounterh[i]  = !mhpmcounter_h_during_wb[i] ? csr_mhpmcounter_we_h[i] : '1;
    end
  endgenerate

  assign ex_csr_rdata_d.cycle                = csr_mhpmcounter_q_l [CSR_CYCLE & 'hF];
  assign rvfi_csr_rdata_d.cycle              = ex_csr_rdata.cycle;
  assign rvfi_csr_wdata_d.cycle              = csr_mhpmcounter_n_l [CSR_CYCLE & 'hF];
  assign rvfi_csr_wmask_d.cycle              = csr_mhpmcounter_we_l[CSR_CYCLE & 'hF];

  assign rvfi_csr_rdata_d.instret            = csr_mhpmcounter_q_l [CSR_INSTRET & 'hF];
  assign rvfi_csr_wdata_d.instret            = csr_mhpmcounter_n_l [CSR_INSTRET & 'hF];
  assign rvfi_csr_wmask_d.instret            = csr_mhpmcounter_we_l[CSR_INSTRET & 'hF];

  assign rvfi_csr_rdata_d.hpmcounter[ 2:0]   = 'Z;
  assign rvfi_csr_wdata_d.hpmcounter[ 2:0]   = 'Z;  // Does not exist
  assign rvfi_csr_wmask_d.hpmcounter[ 2:0]   = '0;
  assign rvfi_csr_rdata_d.hpmcounter[31:3]   = csr_mhpmcounter_q_l [31:3];
  assign rvfi_csr_wdata_d.hpmcounter[31:3]   = csr_mhpmcounter_n_l [31:3];
  assign rvfi_csr_wmask_d.hpmcounter[31:3]   = csr_mhpmcounter_we_l[31:3];

  assign ex_csr_rdata_d.cycleh               = csr_mhpmcounter_q_h [CSR_CYCLEH & 'hF];
  assign rvfi_csr_rdata_d.cycleh             = ex_csr_rdata.cycleh;
  assign rvfi_csr_wdata_d.cycleh             = csr_mhpmcounter_n_h [CSR_CYCLEH & 'hF];
  assign rvfi_csr_wmask_d.cycleh             = csr_mhpmcounter_we_h[CSR_CYCLEH & 'hF];

  assign rvfi_csr_rdata_d.instreth           = csr_mhpmcounter_q_h [CSR_INSTRETH & 'hF];
  assign rvfi_csr_wdata_d.instreth           = csr_mhpmcounter_n_h [CSR_INSTRETH & 'hF];
  assign rvfi_csr_wmask_d.instreth           = csr_mhpmcounter_we_h[CSR_INSTRETH & 'hF];

  assign rvfi_csr_rdata_d.hpmcounterh[ 2:0]  = 'Z;
  assign rvfi_csr_wdata_d.hpmcounterh[ 2:0]  = 'Z; // Does not exist
  assign rvfi_csr_wmask_d.hpmcounterh[ 2:0]  = '0;
  assign rvfi_csr_rdata_d.hpmcounterh[31:3]  = csr_mhpmcounter_q_h [31:3];
  assign rvfi_csr_wdata_d.hpmcounterh[31:3]  = csr_mhpmcounter_n_h [31:3];
  assign rvfi_csr_wmask_d.hpmcounterh[31:3]  = csr_mhpmcounter_we_h[31:3];

  assign rvfi_csr_wdata_d.mimpid             = '0; // Read Only
  assign rvfi_csr_wmask_d.mimpid             = '0;
  assign rvfi_csr_rdata_d.mimpid             = csr_mimpid_i;

  assign rvfi_csr_wdata_d.mhartid            = '0; // Read Only
  assign rvfi_csr_wmask_d.mhartid            = '0;
  assign rvfi_csr_rdata_d.mhartid            = csr_mhartid_i;

  // User Mode
  assign rvfi_csr_rdata_d.mcounteren         = csr_mcounteren_q_i;
  assign rvfi_csr_wdata_d.mcounteren         = csr_mcounteren_n_i;
  assign rvfi_csr_wmask_d.mcounteren         = csr_mcounteren_we_i ? '1 : '0;

  // PMP
  // Special case for the PMP cfg registers because they are split by pmp region and not by register
  generate
    for (genvar i = 0; i < 16; i++ ) begin // Max 16 pmp regions
      // 4 regions in each register
      assign rvfi_csr_wdata_d.pmpcfg[i/4][8*(i%4)+:8] = csr_pmpcfg_n_i[i];
      assign rvfi_csr_rdata_d.pmpcfg[i/4][8*(i%4)+:8] = csr_pmpcfg_q_i[i];
      assign rvfi_csr_wmask_d.pmpcfg[i/4][8*(i%4)+:8] = csr_pmpcfg_we_i[i] ? '1 : '0;

      assign rvfi_csr_wdata_d.pmpaddr[i]          = csr_pmpaddr_n_i; // input shared between all registers
      assign rvfi_csr_rdata_d.pmpaddr[i]          = csr_pmpaddr_q_i[i];
    assign rvfi_csr_wmask_d.pmpaddr[i]       = csr_pmpaddr_we_i[i] ? '1 : '0;
    end
  endgenerate

  assign rvfi_csr_wdata_d.mseccfg         = csr_mseccfg_n_i;
  assign rvfi_csr_rdata_d.mseccfg         = csr_mseccfg_q_i;
  assign rvfi_csr_wmask_d.mseccfg         = csr_mseccfg_we_i ? '1 : '0;
  assign rvfi_csr_wdata_d.mseccfgh        = csr_mseccfgh_n_i;
  assign rvfi_csr_rdata_d.mseccfgh        = csr_mseccfgh_q_i;
  assign rvfi_csr_wmask_d.mseccfgh        = csr_mseccfgh_we_i ? '1 : '0;

  assign rvfi_csr_rdata_d.mconfigptr      = csr_mconfigptr_q_i;
  assign rvfi_csr_wdata_d.mconfigptr      = csr_mconfigptr_n_i;
  assign rvfi_csr_wmask_d.mconfigptr      = csr_mconfigptr_we_i ? '1 : '0;

  // CSR outputs //
  assign rvfi_csr_jvt_rdata               = rvfi_csr_rdata.jvt;
  assign rvfi_csr_jvt_rmask               = '1;
  assign rvfi_csr_jvt_wdata               = rvfi_csr_wdata.jvt;
  assign rvfi_csr_jvt_wmask               = rvfi_csr_wmask.jvt;*/
  /*
  assign rvfi_csr_mstatush_rdata          = rvfi_csr_rdata.mstatush;
  assign rvfi_csr_mstatush_rmask          = '1;
  assign rvfi_csr_mstatush_wdata          = rvfi_csr_wdata.mstatush;
  assign rvfi_csr_mstatush_wmask          = rvfi_csr_wmask.mstatush;

  assign rvfi_csr_mtvt_rdata              = rvfi_csr_rdata.mtvt;
  assign rvfi_csr_mtvt_rmask              = '1;
  assign rvfi_csr_mtvt_wdata              = rvfi_csr_wdata.mtvt;
  assign rvfi_csr_mtvt_wmask              = rvfi_csr_wmask.mtvt;

  assign rvfi_csr_mhpmevent_rdata         = rvfi_csr_rdata.mhpmevent;
  assign rvfi_csr_mhpmevent_rmask[ 2:0]   = '1;
  assign rvfi_csr_mhpmevent_rmask[31:3]   = '1;
  assign rvfi_csr_mhpmevent_wdata         = rvfi_csr_wdata.mhpmevent;
  assign rvfi_csr_mhpmevent_wmask         = rvfi_csr_wmask.mhpmevent;

  assign rvfi_csr_mtval_rdata             = rvfi_csr_rdata.mtval;
  assign rvfi_csr_mtval_rmask             = '1;
  assign rvfi_csr_mtval_wdata             = rvfi_csr_wdata.mtval;
  assign rvfi_csr_mtval_wmask             = rvfi_csr_wmask.mtval;
  assign rvfi_csr_mnxti_rmask             = '1;
  assign rvfi_csr_mnxti_rdata             = rvfi_csr_rdata.mnxti;
  assign rvfi_csr_mnxti_wmask             = rvfi_csr_wmask.mnxti;
  assign rvfi_csr_mnxti_wdata             = rvfi_csr_wdata.mnxti;
  assign rvfi_csr_mintstatus_rdata        = rvfi_csr_rdata.mintstatus;
  assign rvfi_csr_mintstatus_rmask        = '1;
  assign rvfi_csr_mintstatus_wdata        = rvfi_csr_wdata.mintstatus;
  assign rvfi_csr_mintstatus_wmask        = rvfi_csr_wmask.mintstatus;
  assign rvfi_csr_mintthresh_rdata        = rvfi_csr_rdata.mintthresh;
  assign rvfi_csr_mintthresh_rmask        = '1;
  assign rvfi_csr_mintthresh_wdata        = rvfi_csr_wdata.mintthresh;
  assign rvfi_csr_mintthresh_wmask        = rvfi_csr_wmask.mintthresh;
  assign rvfi_csr_mscratchcsw_rdata       = rvfi_csr_rdata.mscratchcsw;
  assign rvfi_csr_mscratchcsw_rmask       = '1;
  assign rvfi_csr_mscratchcsw_wdata       = rvfi_csr_wdata.mscratchcsw;
  assign rvfi_csr_mscratchcsw_wmask       = rvfi_csr_wmask.mscratchcsw;
  assign rvfi_csr_mscratchcswl_rdata      = rvfi_csr_rdata.mscratchcswl;
  assign rvfi_csr_mscratchcswl_rmask      = '1;
  assign rvfi_csr_mscratchcswl_wdata      = rvfi_csr_wdata.mscratchcswl;
  assign rvfi_csr_mscratchcswl_wmask      = rvfi_csr_wmask.mscratchcswl;
  assign rvfi_csr_mclicbase_rdata         = rvfi_csr_rdata.mclicbase;
  assign rvfi_csr_mclicbase_rmask         = '1;
  assign rvfi_csr_mclicbase_wdata         = rvfi_csr_wdata.mclicbase;
  assign rvfi_csr_mclicbase_wmask         = rvfi_csr_wmask.mclicbase;
  assign rvfi_csr_tselect_rdata           = rvfi_csr_rdata.tselect;
  assign rvfi_csr_tselect_rmask           = '1;
  assign rvfi_csr_tselect_wdata           = rvfi_csr_wdata.tselect;
  assign rvfi_csr_tselect_wmask           = rvfi_csr_wmask.tselect;

  assign rvfi_csr_mcontext_rdata          = rvfi_csr_rdata.mcontext;
  assign rvfi_csr_mcontext_rmask          = '1;
  assign rvfi_csr_mcontext_wdata          = rvfi_csr_wdata.mcontext;
  assign rvfi_csr_mcontext_wmask          = rvfi_csr_wmask.mcontext;
  assign rvfi_csr_scontext_rdata          = rvfi_csr_rdata.scontext;
  assign rvfi_csr_scontext_rmask          = '1;
  assign rvfi_csr_scontext_wdata          = rvfi_csr_wdata.scontext;
  assign rvfi_csr_scontext_wmask          = rvfi_csr_wmask.scontext;

  assign rvfi_csr_dpc_rdata               = rvfi_csr_rdata.dpc;
  assign rvfi_csr_dpc_rmask               = '1;
  assign rvfi_csr_dpc_wdata               = rvfi_csr_wdata.dpc;
  assign rvfi_csr_dpc_wmask               = rvfi_csr_wmask.dpc;
  assign rvfi_csr_dscratch_rdata          = rvfi_csr_rdata.dscratch;
  assign rvfi_csr_dscratch_rmask          = '1;
  assign rvfi_csr_dscratch_wdata          = rvfi_csr_wdata.dscratch;
  assign rvfi_csr_dscratch_wmask          = rvfi_csr_wmask.dscratch;
  assign rvfi_csr_mcycle_rdata            = rvfi_csr_rdata.mcycle;
  assign rvfi_csr_mcycle_rmask            = '1;
  assign rvfi_csr_mcycle_wdata            = rvfi_csr_wdata.mcycle;
  assign rvfi_csr_mcycle_wmask            = rvfi_csr_wmask.mcycle;
  */

  assign rvfi_csr_mhpmcounter_rdata = rvfi_csr_rdata.mhpmcounter;
  assign rvfi_csr_mhpmcounter_rmask[2:0] = '0;
  assign rvfi_csr_mhpmcounter_rmask[31:3] = '1;
  assign rvfi_csr_mhpmcounter_wdata = rvfi_csr_wdata.mhpmcounter;
  assign rvfi_csr_mhpmcounter_wmask = rvfi_csr_wmask.mhpmcounter;
  /*
  assign rvfi_csr_mcycleh_rdata           = rvfi_csr_rdata.mcycleh;
  assign rvfi_csr_mcycleh_rmask           = '1;
  assign rvfi_csr_mcycleh_wdata           = rvfi_csr_wdata.mcycleh;
  assign rvfi_csr_mcycleh_wmask           = rvfi_csr_wmask.mcycleh;
  */
  assign rvfi_csr_minstreth_rdata = rvfi_csr_rdata.minstreth;
  assign rvfi_csr_minstreth_rmask = '1;
  assign rvfi_csr_minstreth_wdata = rvfi_csr_wdata.minstreth;
  assign rvfi_csr_minstreth_wmask = rvfi_csr_wmask.minstreth;
  /*
  assign rvfi_csr_mhpmcounterh_rdata      = rvfi_csr_rdata.mhpmcounterh;
  assign rvfi_csr_mhpmcounterh_rmask[ 2:0] = '0;
  assign rvfi_csr_mhpmcounterh_rmask[31:3] = '1;
  assign rvfi_csr_mhpmcounterh_wdata      = rvfi_csr_wdata.mhpmcounterh;
  assign rvfi_csr_mhpmcounterh_wmask      = rvfi_csr_wmask.mhpmcounterh;

  assign rvfi_csr_mimpid_rdata            = rvfi_csr_rdata.mimpid;
  assign rvfi_csr_mimpid_rmask            = '1;
  assign rvfi_csr_mimpid_wdata            = rvfi_csr_wdata.mimpid;
  assign rvfi_csr_mimpid_wmask            = rvfi_csr_wmask.mimpid;
  assign rvfi_csr_cycle_rdata             = rvfi_csr_rdata.cycle;
  assign rvfi_csr_cycle_rmask             = '1;
  assign rvfi_csr_cycle_wdata             = rvfi_csr_wdata.cycle;
  assign rvfi_csr_cycle_wmask             = rvfi_csr_wmask.cycle;
  assign rvfi_csr_hpmcounter_rdata        = rvfi_csr_rdata.hpmcounter;
  assign rvfi_csr_hpmcounter_rmask[ 2:0]  = '0;
  assign rvfi_csr_hpmcounter_rmask[31:3]  = '1;
  assign rvfi_csr_hpmcounter_wdata        = rvfi_csr_wdata.hpmcounter;
  assign rvfi_csr_hpmcounter_wmask        = rvfi_csr_wmask.hpmcounter;
  assign rvfi_csr_cycleh_rdata            = rvfi_csr_rdata.cycleh;
  assign rvfi_csr_cycleh_rmask            = '1;
  assign rvfi_csr_cycleh_wdata            = rvfi_csr_wdata.cycleh;
  assign rvfi_csr_cycleh_wmask            = rvfi_csr_wmask.cycleh;
  assign rvfi_csr_instreth_rdata          = rvfi_csr_rdata.instreth;
  assign rvfi_csr_instreth_rmask          = '1;
  assign rvfi_csr_instreth_wdata          = rvfi_csr_wdata.instreth;
  assign rvfi_csr_instreth_wmask          = rvfi_csr_wmask.instreth;
  assign rvfi_csr_hpmcounterh_rdata       = rvfi_csr_rdata.hpmcounterh;
  assign rvfi_csr_hpmcounterh_rmask[ 2:0] = '0;
  assign rvfi_csr_hpmcounterh_rmask[31:3] = '1;
  assign rvfi_csr_hpmcounterh_wdata       = rvfi_csr_wdata.hpmcounterh;
  assign rvfi_csr_hpmcounterh_wmask       = rvfi_csr_wmask.hpmcounterh;
  assign rvfi_csr_mcounteren_rdata        = rvfi_csr_rdata.mcounteren;
  assign rvfi_csr_mcounteren_rmask        = '1;
  assign rvfi_csr_mcounteren_wdata        = rvfi_csr_wdata.mcounteren;
  assign rvfi_csr_mcounteren_wmask        = rvfi_csr_wmask.mcounteren;
  assign rvfi_csr_pmpcfg_rdata            = rvfi_csr_rdata.pmpcfg;
  assign rvfi_csr_pmpcfg_rmask            = '1;
  assign rvfi_csr_pmpcfg_wdata            = rvfi_csr_wmask.pmpcfg;
  assign rvfi_csr_pmpcfg_wmask            = rvfi_csr_wdata.pmpcfg;
  assign rvfi_csr_pmpaddr_rdata           = rvfi_csr_rdata.pmpaddr;
  assign rvfi_csr_pmpaddr_rmask           = '1;
  assign rvfi_csr_pmpaddr_wdata           = rvfi_csr_wdata.pmpaddr;
  assign rvfi_csr_pmpaddr_wmask           = rvfi_csr_wmask.pmpaddr;
  assign rvfi_csr_mseccfg_rdata           = rvfi_csr_rdata.mseccfg;
  assign rvfi_csr_mseccfg_rmask           = '1;
  assign rvfi_csr_mseccfg_wdata           = rvfi_csr_wdata.mseccfg;
  assign rvfi_csr_mseccfg_wmask           = rvfi_csr_wmask.mseccfg;
  assign rvfi_csr_mseccfgh_rdata          = rvfi_csr_rdata.mseccfgh;
  assign rvfi_csr_mseccfgh_rmask          = '1;
  assign rvfi_csr_mseccfgh_wdata          = rvfi_csr_wdata.mseccfgh;
  assign rvfi_csr_mseccfgh_wmask          = rvfi_csr_wmask.mseccfgh;
*/
endmodule  // cv32e40p_rvfi
