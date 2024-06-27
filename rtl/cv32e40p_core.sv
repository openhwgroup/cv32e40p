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
// Engineer:       Matthias Baer - baermatt@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Top level module                                           //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Top level module of the RISC-V core.                       //
//                 added APU, FPU parameter to include the APU_dispatcher     //
//                 and the FPU                                                //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40p_core
  import cv32e40p_apu_core_pkg::*;
#(
    parameter COREV_PULP =  0,  // PULP ISA Extension (incl. custom CSRs and hardware loop, excl. cv.elw)
    parameter COREV_CLUSTER = 0,  // PULP Cluster interface (incl. cv.elw)
    parameter FPU = 0,  // Floating Point Unit (interfaced via APU interface)
    parameter FPU_ADDMUL_LAT = 0,  // Floating-Point ADDition/MULtiplication lane pipeline registers number
    parameter FPU_OTHERS_LAT = 0,  // Floating-Point COMParison/CONVersion lanes pipeline registers number
    parameter ZFINX = 0,  // Float-in-General Purpose registers
    parameter NUM_MHPMCOUNTERS = 1
) (
    // Clock and Reset
    input logic clk_i,
    input logic rst_ni,

    input logic pulp_clock_en_i,  // PULP clock enable (only used if COREV_CLUSTER = 1)
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

    // CVFPU interface
    output logic                              apu_busy_o,
    // handshake signals
    output logic                              apu_req_o,
    input  logic                              apu_gnt_i,
    // request channel
    output logic [   APU_NARGS_CPU-1:0][31:0] apu_operands_o,
    output logic [     APU_WOP_CPU-1:0]       apu_op_o,
    output logic [APU_NDSFLAGS_CPU-1:0]       apu_flags_o,
    // response channel
    input  logic                              apu_rvalid_i,
    input  logic [                31:0]       apu_result_i,
    input  logic [APU_NUSFLAGS_CPU-1:0]       apu_flags_i,

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

  import cv32e40p_pkg::*;

  // Unused parameters and signals (left in code for future design extensions)
  localparam PULP_SECURE = 0;
  localparam N_PMP_ENTRIES = 16;
  localparam USE_PMP = 0;  // if PULP_SECURE is 1, you can still not use the PMP
  localparam A_EXTENSION = 0;
  localparam DEBUG_TRIGGER_EN = 1;

  // PULP bus interface behavior
  // If enabled will allow non-stable address phase signals during waited instructions requests and
  // will re-introduce combinatorial paths from instr_rvalid_i to instr_req_o and from from data_rvalid_i
  // to data_req_o
  localparam PULP_OBI = 0;

  // Unused signals related to above unused parameters
  // Left in code (with their original _i, _o postfixes) for future design extensions;
  // these used to be former inputs/outputs of RI5CY

  logic [5:0] data_atop_o;  // atomic operation, only active if parameter `A_EXTENSION != 0`
  logic       irq_sec_i;
  logic       sec_lvl_o;

  localparam N_HWLP = 2;
  localparam APU = (FPU == 1) ? 1 : 0;

  // IF/ID signals
  logic        instr_valid_id;
  logic [31:0] instr_rdata_id;  // Instruction sampled inside IF stage
  logic        is_compressed_id;
  logic        illegal_c_insn_id;
  logic        is_fetch_failed_id;

  logic        clear_instr_valid;
  logic        pc_set;

  logic [ 3:0] pc_mux_id;  // Mux selector for next PC
  logic [ 2:0] exc_pc_mux_id;  // Mux selector for exception PC
  logic [ 4:0] m_exc_vec_pc_mux_id;  // Mux selector for vectored IRQ PC
  logic [ 4:0] u_exc_vec_pc_mux_id;  // Mux selector for vectored IRQ PC
  logic [ 4:0] exc_cause;

  logic [ 1:0] trap_addr_mux;

  logic [31:0] pc_if;  // Program counter in IF stage
  logic [31:0] pc_id;  // Program counter in ID stage

  // ID performance counter signals
  logic        is_decoding;

  logic        useincr_addr_ex;  // Active when post increment
  logic        data_misaligned;

  logic        mult_multicycle;

  // Jump and branch target and decision (EX->IF)
  logic [31:0] jump_target_id, jump_target_ex;
  logic               branch_in_ex;
  logic               branch_decision;
  logic        [ 1:0] ctrl_transfer_insn_in_dec;

  logic               ctrl_busy;
  logic               if_busy;
  logic               lsu_busy;

  logic        [31:0] pc_ex;  // PC of last executed branch or cv.elw

  // ALU Control
  logic               alu_en_ex;
  alu_opcode_e        alu_operator_ex;
  logic        [31:0] alu_operand_a_ex;
  logic        [31:0] alu_operand_b_ex;
  logic        [31:0] alu_operand_c_ex;
  logic        [ 4:0] bmask_a_ex;
  logic        [ 4:0] bmask_b_ex;
  logic        [ 1:0] imm_vec_ext_ex;
  logic        [ 1:0] alu_vec_mode_ex;
  logic alu_is_clpx_ex, alu_is_subrot_ex;
  logic        [                 1:0]       alu_clpx_shift_ex;

  // Multiplier Control
  mul_opcode_e                              mult_operator_ex;
  logic        [                31:0]       mult_operand_a_ex;
  logic        [                31:0]       mult_operand_b_ex;
  logic        [                31:0]       mult_operand_c_ex;
  logic                                     mult_en_ex;
  logic                                     mult_sel_subword_ex;
  logic        [                 1:0]       mult_signed_mode_ex;
  logic        [                 4:0]       mult_imm_ex;
  logic        [                31:0]       mult_dot_op_a_ex;
  logic        [                31:0]       mult_dot_op_b_ex;
  logic        [                31:0]       mult_dot_op_c_ex;
  logic        [                 1:0]       mult_dot_signed_ex;
  logic                                     mult_is_clpx_ex;
  logic        [                 1:0]       mult_clpx_shift_ex;
  logic                                     mult_clpx_img_ex;

  // FPU
  logic                                     fs_off;
  logic        [            C_RM-1:0]       frm_csr;
  logic        [         C_FFLAG-1:0]       fflags_csr;
  logic                                     fflags_we;
  logic                                     fregs_we;

  // APU
  logic                                     apu_en_ex;
  logic        [APU_NDSFLAGS_CPU-1:0]       apu_flags_ex;
  logic        [     APU_WOP_CPU-1:0]       apu_op_ex;
  logic        [                 1:0]       apu_lat_ex;
  logic        [   APU_NARGS_CPU-1:0][31:0] apu_operands_ex;
  logic        [                 5:0]       apu_waddr_ex;

  logic        [                 2:0][ 5:0] apu_read_regs;
  logic        [                 2:0]       apu_read_regs_valid;
  logic                                     apu_read_dep;
  logic                                     apu_read_dep_for_jalr;
  logic        [                 1:0][ 5:0] apu_write_regs;
  logic        [                 1:0]       apu_write_regs_valid;
  logic                                     apu_write_dep;

  logic                                     perf_apu_type;
  logic                                     perf_apu_cont;
  logic                                     perf_apu_dep;
  logic                                     perf_apu_wb;

  // Register Write Control
  logic        [                 5:0]       regfile_waddr_ex;
  logic                                     regfile_we_ex;
  logic        [                 5:0]       regfile_waddr_fw_wb_o;  // From WB to ID
  logic                                     regfile_we_wb;
  logic                                     regfile_we_wb_power;
  logic        [                31:0]       regfile_wdata;

  logic        [                 5:0]       regfile_alu_waddr_ex;
  logic                                     regfile_alu_we_ex;

  logic        [                 5:0]       regfile_alu_waddr_fw;
  logic                                     regfile_alu_we_fw;
  logic                                     regfile_alu_we_fw_power;
  logic        [                31:0]       regfile_alu_wdata_fw;

  // CSR control
  logic                                     csr_access_ex;
  csr_opcode_e                              csr_op_ex;
  logic [23:0] mtvec, utvec;
  logic        [ 1:0] mtvec_mode;
  logic        [ 1:0] utvec_mode;

  csr_opcode_e        csr_op;
  csr_num_e           csr_addr;
  csr_num_e           csr_addr_int;
  logic        [31:0] csr_rdata;
  logic        [31:0] csr_wdata;
  PrivLvl_t           current_priv_lvl;

  // Data Memory Control:  From ID stage (id-ex pipe) <--> load store unit
  logic               data_we_ex;
  logic        [ 5:0] data_atop_ex;
  logic        [ 1:0] data_type_ex;
  logic        [ 1:0] data_sign_ext_ex;
  logic        [ 1:0] data_reg_offset_ex;
  logic               data_req_ex;
  logic               data_load_event_ex;
  logic               data_misaligned_ex;

  logic               p_elw_start;  // Start of cv.elw load (when data_req_o is sent)
  logic               p_elw_finish;  // Finish of cv.elw load (when data_rvalid_i is received)

  logic        [31:0] lsu_rdata;

  // stall control
  logic               halt_if;
  logic               id_ready;
  logic               ex_ready;

  logic               id_valid;
  logic               ex_valid;
  logic               wb_valid;

  logic               lsu_ready_ex;
  logic               lsu_ready_wb;

  logic               apu_ready_wb;

  // Signals between instruction core interface and pipe (if and id stages)
  logic               instr_req_int;  // Id stage asserts a req to instruction core interface

  // Interrupts
  logic m_irq_enable, u_irq_enable;
  logic csr_irq_sec;
  logic [31:0] mepc, uepc, depc;
  logic [             31:0]       mie_bypass;
  logic [             31:0]       mip;

  logic                           csr_save_cause;
  logic                           csr_save_if;
  logic                           csr_save_id;
  logic                           csr_save_ex;
  logic [              5:0]       csr_cause;
  logic                           csr_restore_mret_id;
  logic                           csr_restore_uret_id;
  logic                           csr_restore_dret_id;
  logic                           csr_mtvec_init;

  // HPM related control signals
  logic [             31:0]       mcounteren;

  // debug mode and dcsr configuration
  logic                           debug_mode;
  logic [              2:0]       debug_cause;
  logic                           debug_csr_save;
  logic                           debug_single_step;
  logic                           debug_ebreakm;
  logic                           debug_ebreaku;
  logic                           trigger_match;
  logic                           debug_p_elw_no_sleep;

  // Hardware loop controller signals
  logic [       N_HWLP-1:0][31:0] hwlp_start;
  logic [       N_HWLP-1:0][31:0] hwlp_end;
  logic [       N_HWLP-1:0][31:0] hwlp_cnt;

  logic [             31:0]       hwlp_target;
  logic                           hwlp_jump;

  // Performance Counters
  logic                           mhpmevent_minstret;
  logic                           mhpmevent_load;
  logic                           mhpmevent_store;
  logic                           mhpmevent_jump;
  logic                           mhpmevent_branch;
  logic                           mhpmevent_branch_taken;
  logic                           mhpmevent_compressed;
  logic                           mhpmevent_jr_stall;
  logic                           mhpmevent_imiss;
  logic                           mhpmevent_ld_stall;
  logic                           mhpmevent_pipe_stall;

  logic                           perf_imiss;

  // Wake signal
  logic                           wake_from_sleep;

  // PMP signals
  logic [N_PMP_ENTRIES-1:0][31:0] pmp_addr;
  logic [N_PMP_ENTRIES-1:0][ 7:0] pmp_cfg;

  logic                           data_req_pmp;
  logic [             31:0]       data_addr_pmp;
  logic                           data_gnt_pmp;
  logic                           data_err_pmp;
  logic                           data_err_ack;
  logic                           instr_req_pmp;
  logic                           instr_gnt_pmp;
  logic [             31:0]       instr_addr_pmp;
  logic                           instr_err_pmp;

  // Mux selector for vectored IRQ PC
  assign m_exc_vec_pc_mux_id = (mtvec_mode == 2'b0) ? 5'h0 : exc_cause;
  assign u_exc_vec_pc_mux_id = (utvec_mode == 2'b0) ? 5'h0 : exc_cause;

  // PULP_SECURE == 0
  assign irq_sec_i = 1'b0;

  // APU master signals
  assign apu_flags_o = apu_flags_ex;

  //////////////////////////////////////////////////////////////////////////////////////////////
  //   ____ _            _      __  __                                                   _    //
  //  / ___| | ___   ___| | __ |  \/  | __ _ _ __   __ _  __ _  ___ _ __ ___   ___ _ __ | |_  //
  // | |   | |/ _ \ / __| |/ / | |\/| |/ _` | '_ \ / _` |/ _` |/ _ \ '_ ` _ \ / _ \ '_ \| __| //
  // | |___| | (_) | (__|   <  | |  | | (_| | | | | (_| | (_| |  __/ | | | | |  __/ | | | |_  //
  //  \____|_|\___/ \___|_|\_\ |_|  |_|\__,_|_| |_|\__,_|\__, |\___|_| |_| |_|\___|_| |_|\__| //
  //                                                     |___/                                //
  //////////////////////////////////////////////////////////////////////////////////////////////

  logic clk;
  logic fetch_enable;

  cv32e40p_sleep_unit #(
      .COREV_CLUSTER(COREV_CLUSTER)
  ) sleep_unit_i (
      // Clock, reset interface
      .clk_ungated_i(clk_i),  // Ungated clock
      .rst_n        (rst_ni),
      .clk_gated_o  (clk),  // Gated clock
      .scan_cg_en_i (scan_cg_en_i),

      // Core sleep
      .core_sleep_o(core_sleep_o),

      // Fetch enable
      .fetch_enable_i(fetch_enable_i),
      .fetch_enable_o(fetch_enable),

      // Core status
      .if_busy_i  (if_busy),
      .ctrl_busy_i(ctrl_busy),
      .lsu_busy_i (lsu_busy),
      .apu_busy_i (apu_busy_o),

      // PULP cluster
      .pulp_clock_en_i       (pulp_clock_en_i),
      .p_elw_start_i         (p_elw_start),
      .p_elw_finish_i        (p_elw_finish),
      .debug_p_elw_no_sleep_i(debug_p_elw_no_sleep),

      // WFI wake
      .wake_from_sleep_i(wake_from_sleep)
  );


  //////////////////////////////////////////////////
  //   ___ _____   ____ _____  _    ____ _____    //
  //  |_ _|  ___| / ___|_   _|/ \  / ___| ____|   //
  //   | || |_    \___ \ | | / _ \| |  _|  _|     //
  //   | ||  _|    ___) || |/ ___ \ |_| | |___    //
  //  |___|_|     |____/ |_/_/   \_\____|_____|   //
  //                                              //
  //////////////////////////////////////////////////
  cv32e40p_if_stage #(
      .COREV_PULP (COREV_PULP),
      .PULP_OBI   (PULP_OBI),
      .PULP_SECURE(PULP_SECURE),
      .FPU        (FPU),
      .ZFINX      (ZFINX)
  ) if_stage_i (
      .clk  (clk),
      .rst_n(rst_ni),

      // boot address
      .boot_addr_i        (boot_addr_i[31:0]),
      .dm_exception_addr_i(dm_exception_addr_i[31:0]),

      // debug mode halt address
      .dm_halt_addr_i(dm_halt_addr_i[31:0]),

      // trap vector location
      .m_trap_base_addr_i(mtvec),
      .u_trap_base_addr_i(utvec),
      .trap_addr_mux_i   (trap_addr_mux),

      // instruction request control
      .req_i(instr_req_int),

      // instruction cache interface
      .instr_req_o    (instr_req_pmp),
      .instr_addr_o   (instr_addr_pmp),
      .instr_gnt_i    (instr_gnt_pmp),
      .instr_rvalid_i (instr_rvalid_i),
      .instr_rdata_i  (instr_rdata_i),
      .instr_err_i    (1'b0),  // Bus error (not used yet)
      .instr_err_pmp_i(instr_err_pmp),  // PMP error

      // outputs to ID stage
      .instr_valid_id_o (instr_valid_id),
      .instr_rdata_id_o (instr_rdata_id),
      .is_fetch_failed_o(is_fetch_failed_id),

      // control signals
      .clear_instr_valid_i(clear_instr_valid),
      .pc_set_i           (pc_set),

      .mepc_i(mepc),  // exception return address
      .uepc_i(uepc),  // exception return address

      .depc_i(depc),  // debug return address

      .pc_mux_i    (pc_mux_id),  // sel for pc multiplexer
      .exc_pc_mux_i(exc_pc_mux_id),


      .pc_id_o(pc_id),
      .pc_if_o(pc_if),

      .is_compressed_id_o (is_compressed_id),
      .illegal_c_insn_id_o(illegal_c_insn_id),

      .m_exc_vec_pc_mux_i(m_exc_vec_pc_mux_id),
      .u_exc_vec_pc_mux_i(u_exc_vec_pc_mux_id),

      .csr_mtvec_init_o(csr_mtvec_init),

      // from hwloop registers
      .hwlp_jump_i  (hwlp_jump),
      .hwlp_target_i(hwlp_target),


      // Jump targets
      .jump_target_id_i(jump_target_id),
      .jump_target_ex_i(jump_target_ex),

      // pipeline stalls
      .halt_if_i (halt_if),
      .id_ready_i(id_ready),

      .if_busy_o   (if_busy),
      .perf_imiss_o(perf_imiss)
  );


  /////////////////////////////////////////////////
  //   ___ ____    ____ _____  _    ____ _____   //
  //  |_ _|  _ \  / ___|_   _|/ \  / ___| ____|  //
  //   | || | | | \___ \ | | / _ \| |  _|  _|    //
  //   | || |_| |  ___) || |/ ___ \ |_| | |___   //
  //  |___|____/  |____/ |_/_/   \_\____|_____|  //
  //                                             //
  /////////////////////////////////////////////////
  cv32e40p_id_stage #(
      .COREV_PULP      (COREV_PULP),
      .COREV_CLUSTER   (COREV_CLUSTER),
      .N_HWLP          (N_HWLP),
      .PULP_SECURE     (PULP_SECURE),
      .USE_PMP         (USE_PMP),
      .A_EXTENSION     (A_EXTENSION),
      .APU             (APU),
      .FPU             (FPU),
      .FPU_ADDMUL_LAT  (FPU_ADDMUL_LAT),
      .FPU_OTHERS_LAT  (FPU_OTHERS_LAT),
      .ZFINX           (ZFINX),
      .APU_NARGS_CPU   (APU_NARGS_CPU),
      .APU_WOP_CPU     (APU_WOP_CPU),
      .APU_NDSFLAGS_CPU(APU_NDSFLAGS_CPU),
      .APU_NUSFLAGS_CPU(APU_NUSFLAGS_CPU),
      .DEBUG_TRIGGER_EN(DEBUG_TRIGGER_EN)
  ) id_stage_i (
      .clk          (clk),  // Gated clock
      .clk_ungated_i(clk_i),  // Ungated clock
      .rst_n        (rst_ni),

      .scan_cg_en_i(scan_cg_en_i),

      // Processor Enable
      .fetch_enable_i               ( fetch_enable         ),     // Delayed version so that clock can remain gated until fetch enabled
      .ctrl_busy_o(ctrl_busy),
      .is_decoding_o(is_decoding),

      // Interface to instruction memory
      .instr_valid_i(instr_valid_id),
      .instr_rdata_i(instr_rdata_id),
      .instr_req_o  (instr_req_int),

      // Jumps and branches
      .branch_in_ex_o             (branch_in_ex),
      .branch_decision_i          (branch_decision),
      .jump_target_o              (jump_target_id),
      .ctrl_transfer_insn_in_dec_o(ctrl_transfer_insn_in_dec),

      // IF and ID control signals
      .clear_instr_valid_o(clear_instr_valid),
      .pc_set_o           (pc_set),
      .pc_mux_o           (pc_mux_id),
      .exc_pc_mux_o       (exc_pc_mux_id),
      .exc_cause_o        (exc_cause),
      .trap_addr_mux_o    (trap_addr_mux),

      .is_fetch_failed_i(is_fetch_failed_id),

      .pc_id_i(pc_id),

      .is_compressed_i (is_compressed_id),
      .illegal_c_insn_i(illegal_c_insn_id),

      // Stalls
      .halt_if_o(halt_if),

      .id_ready_o(id_ready),
      .ex_ready_i(ex_ready),
      .wb_ready_i(lsu_ready_wb),

      .id_valid_o(id_valid),
      .ex_valid_i(ex_valid),

      // From the Pipeline ID/EX
      .pc_ex_o(pc_ex),

      .alu_en_ex_o        (alu_en_ex),
      .alu_operator_ex_o  (alu_operator_ex),
      .alu_operand_a_ex_o (alu_operand_a_ex),
      .alu_operand_b_ex_o (alu_operand_b_ex),
      .alu_operand_c_ex_o (alu_operand_c_ex),
      .bmask_a_ex_o       (bmask_a_ex),
      .bmask_b_ex_o       (bmask_b_ex),
      .imm_vec_ext_ex_o   (imm_vec_ext_ex),
      .alu_vec_mode_ex_o  (alu_vec_mode_ex),
      .alu_is_clpx_ex_o   (alu_is_clpx_ex),
      .alu_is_subrot_ex_o (alu_is_subrot_ex),
      .alu_clpx_shift_ex_o(alu_clpx_shift_ex),

      .regfile_waddr_ex_o(regfile_waddr_ex),
      .regfile_we_ex_o   (regfile_we_ex),

      .regfile_alu_we_ex_o   (regfile_alu_we_ex),
      .regfile_alu_waddr_ex_o(regfile_alu_waddr_ex),

      // MUL
      .mult_operator_ex_o   (mult_operator_ex),  // from ID to EX stage
      .mult_en_ex_o         (mult_en_ex),  // from ID to EX stage
      .mult_sel_subword_ex_o(mult_sel_subword_ex),  // from ID to EX stage
      .mult_signed_mode_ex_o(mult_signed_mode_ex),  // from ID to EX stage
      .mult_operand_a_ex_o  (mult_operand_a_ex),  // from ID to EX stage
      .mult_operand_b_ex_o  (mult_operand_b_ex),  // from ID to EX stage
      .mult_operand_c_ex_o  (mult_operand_c_ex),  // from ID to EX stage
      .mult_imm_ex_o        (mult_imm_ex),  // from ID to EX stage

      .mult_dot_op_a_ex_o  (mult_dot_op_a_ex),  // from ID to EX stage
      .mult_dot_op_b_ex_o  (mult_dot_op_b_ex),  // from ID to EX stage
      .mult_dot_op_c_ex_o  (mult_dot_op_c_ex),  // from ID to EX stage
      .mult_dot_signed_ex_o(mult_dot_signed_ex),  // from ID to EX stage
      .mult_is_clpx_ex_o   (mult_is_clpx_ex),  // from ID to EX stage
      .mult_clpx_shift_ex_o(mult_clpx_shift_ex),  // from ID to EX stage
      .mult_clpx_img_ex_o  (mult_clpx_img_ex),  // from ID to EX stage

      // FPU
      .fs_off_i(fs_off),
      .frm_i   (frm_csr),

      // APU
      .apu_en_ex_o      (apu_en_ex),
      .apu_op_ex_o      (apu_op_ex),
      .apu_lat_ex_o     (apu_lat_ex),
      .apu_operands_ex_o(apu_operands_ex),
      .apu_flags_ex_o   (apu_flags_ex),
      .apu_waddr_ex_o   (apu_waddr_ex),

      .apu_read_regs_o        (apu_read_regs),
      .apu_read_regs_valid_o  (apu_read_regs_valid),
      .apu_read_dep_i         (apu_read_dep),
      .apu_read_dep_for_jalr_i(apu_read_dep_for_jalr),
      .apu_write_regs_o       (apu_write_regs),
      .apu_write_regs_valid_o (apu_write_regs_valid),
      .apu_write_dep_i        (apu_write_dep),
      .apu_perf_dep_o         (perf_apu_dep),
      .apu_busy_i             (apu_busy_o),

      // CSR ID/EX
      .csr_access_ex_o      (csr_access_ex),
      .csr_op_ex_o          (csr_op_ex),
      .current_priv_lvl_i   (current_priv_lvl),
      .csr_irq_sec_o        (csr_irq_sec),
      .csr_cause_o          (csr_cause),
      .csr_save_if_o        (csr_save_if),  // control signal to save pc
      .csr_save_id_o        (csr_save_id),  // control signal to save pc
      .csr_save_ex_o        (csr_save_ex),  // control signal to save pc
      .csr_restore_mret_id_o(csr_restore_mret_id),  // control signal to restore pc
      .csr_restore_uret_id_o(csr_restore_uret_id),  // control signal to restore pc

      .csr_restore_dret_id_o(csr_restore_dret_id),  // control signal to restore pc

      .csr_save_cause_o(csr_save_cause),

      // hardware loop signals to IF hwlp controller
      .hwlp_start_o(hwlp_start),
      .hwlp_end_o  (hwlp_end),
      .hwlp_cnt_o  (hwlp_cnt),

      .hwlp_jump_o  (hwlp_jump),
      .hwlp_target_o(hwlp_target),

      // LSU
      .data_req_ex_o       (data_req_ex),  // to load store unit
      .data_we_ex_o        (data_we_ex),  // to load store unit
      .atop_ex_o           (data_atop_ex),
      .data_type_ex_o      (data_type_ex),  // to load store unit
      .data_sign_ext_ex_o  (data_sign_ext_ex),  // to load store unit
      .data_reg_offset_ex_o(data_reg_offset_ex),  // to load store unit
      .data_load_event_ex_o(data_load_event_ex),  // to load store unit

      .data_misaligned_ex_o(data_misaligned_ex),  // to load store unit

      .prepost_useincr_ex_o(useincr_addr_ex),
      .data_misaligned_i   (data_misaligned),
      .data_err_i          (data_err_pmp),
      .data_err_ack_o      (data_err_ack),

      // Interrupt Signals
      .irq_i         (irq_i),
      .irq_sec_i     ((PULP_SECURE) ? irq_sec_i : 1'b0),
      .mie_bypass_i  (mie_bypass),
      .mip_o         (mip),
      .m_irq_enable_i(m_irq_enable),
      .u_irq_enable_i(u_irq_enable),
      .irq_ack_o     (irq_ack_o),
      .irq_id_o      (irq_id_o),

      // Debug Signal
      .debug_mode_o          (debug_mode),
      .debug_cause_o         (debug_cause),
      .debug_csr_save_o      (debug_csr_save),
      .debug_req_i           (debug_req_i),
      .debug_havereset_o     (debug_havereset_o),
      .debug_running_o       (debug_running_o),
      .debug_halted_o        (debug_halted_o),
      .debug_single_step_i   (debug_single_step),
      .debug_ebreakm_i       (debug_ebreakm),
      .debug_ebreaku_i       (debug_ebreaku),
      .trigger_match_i       (trigger_match),
      .debug_p_elw_no_sleep_o(debug_p_elw_no_sleep),

      // Wakeup Signal
      .wake_from_sleep_o(wake_from_sleep),

      // Forward Signals
      .regfile_waddr_wb_i   (regfile_waddr_fw_wb_o),  // Write address ex-wb pipeline
      .regfile_we_wb_i      (regfile_we_wb),  // write enable for the register file
      .regfile_we_wb_power_i(regfile_we_wb_power),
      .regfile_wdata_wb_i   (regfile_wdata),  // write data to commit in the register file

      .regfile_alu_waddr_fw_i   (regfile_alu_waddr_fw),
      .regfile_alu_we_fw_i      (regfile_alu_we_fw),
      .regfile_alu_we_fw_power_i(regfile_alu_we_fw_power),
      .regfile_alu_wdata_fw_i   (regfile_alu_wdata_fw),

      // from ALU
      .mult_multicycle_i(mult_multicycle),

      // Performance Counters
      .mhpmevent_minstret_o    (mhpmevent_minstret),
      .mhpmevent_load_o        (mhpmevent_load),
      .mhpmevent_store_o       (mhpmevent_store),
      .mhpmevent_jump_o        (mhpmevent_jump),
      .mhpmevent_branch_o      (mhpmevent_branch),
      .mhpmevent_branch_taken_o(mhpmevent_branch_taken),
      .mhpmevent_compressed_o  (mhpmevent_compressed),
      .mhpmevent_jr_stall_o    (mhpmevent_jr_stall),
      .mhpmevent_imiss_o       (mhpmevent_imiss),
      .mhpmevent_ld_stall_o    (mhpmevent_ld_stall),
      .mhpmevent_pipe_stall_o  (mhpmevent_pipe_stall),

      .perf_imiss_i(perf_imiss),
      .mcounteren_i(mcounteren)
  );


  /////////////////////////////////////////////////////
  //   _______  __  ____ _____  _    ____ _____      //
  //  | ____\ \/ / / ___|_   _|/ \  / ___| ____|     //
  //  |  _|  \  /  \___ \ | | / _ \| |  _|  _|       //
  //  | |___ /  \   ___) || |/ ___ \ |_| | |___      //
  //  |_____/_/\_\ |____/ |_/_/   \_\____|_____|     //
  //                                                 //
  /////////////////////////////////////////////////////
  cv32e40p_ex_stage #(
      .COREV_PULP      (COREV_PULP),
      .FPU             (FPU),
      .APU_NARGS_CPU   (APU_NARGS_CPU),
      .APU_WOP_CPU     (APU_WOP_CPU),
      .APU_NDSFLAGS_CPU(APU_NDSFLAGS_CPU),
      .APU_NUSFLAGS_CPU(APU_NUSFLAGS_CPU)
  ) ex_stage_i (
      // Global signals: Clock and active low asynchronous reset
      .clk  (clk),
      .rst_n(rst_ni),

      // Alu signals from ID stage
      .alu_en_i        (alu_en_ex),
      .alu_operator_i  (alu_operator_ex),  // from ID/EX pipe registers
      .alu_operand_a_i (alu_operand_a_ex),  // from ID/EX pipe registers
      .alu_operand_b_i (alu_operand_b_ex),  // from ID/EX pipe registers
      .alu_operand_c_i (alu_operand_c_ex),  // from ID/EX pipe registers
      .bmask_a_i       (bmask_a_ex),  // from ID/EX pipe registers
      .bmask_b_i       (bmask_b_ex),  // from ID/EX pipe registers
      .imm_vec_ext_i   (imm_vec_ext_ex),  // from ID/EX pipe registers
      .alu_vec_mode_i  (alu_vec_mode_ex),  // from ID/EX pipe registers
      .alu_is_clpx_i   (alu_is_clpx_ex),  // from ID/EX pipe registers
      .alu_is_subrot_i (alu_is_subrot_ex),  // from ID/Ex pipe registers
      .alu_clpx_shift_i(alu_clpx_shift_ex),  // from ID/EX pipe registers

      // Multipler
      .mult_operator_i   (mult_operator_ex),  // from ID/EX pipe registers
      .mult_operand_a_i  (mult_operand_a_ex),  // from ID/EX pipe registers
      .mult_operand_b_i  (mult_operand_b_ex),  // from ID/EX pipe registers
      .mult_operand_c_i  (mult_operand_c_ex),  // from ID/EX pipe registers
      .mult_en_i         (mult_en_ex),  // from ID/EX pipe registers
      .mult_sel_subword_i(mult_sel_subword_ex),  // from ID/EX pipe registers
      .mult_signed_mode_i(mult_signed_mode_ex),  // from ID/EX pipe registers
      .mult_imm_i        (mult_imm_ex),  // from ID/EX pipe registers
      .mult_dot_op_a_i   (mult_dot_op_a_ex),  // from ID/EX pipe registers
      .mult_dot_op_b_i   (mult_dot_op_b_ex),  // from ID/EX pipe registers
      .mult_dot_op_c_i   (mult_dot_op_c_ex),  // from ID/EX pipe registers
      .mult_dot_signed_i (mult_dot_signed_ex),  // from ID/EX pipe registers
      .mult_is_clpx_i    (mult_is_clpx_ex),  // from ID/EX pipe registers
      .mult_clpx_shift_i (mult_clpx_shift_ex),  // from ID/EX pipe registers
      .mult_clpx_img_i   (mult_clpx_img_ex),  // from ID/EX pipe registers

      .mult_multicycle_o(mult_multicycle),  // to ID/EX pipe registers

      .data_req_i          (data_req_o),  // from ID/EX pipeline
      .data_rvalid_i       (data_rvalid_i),  // from ID/EX pipeline
      .data_misaligned_ex_i(data_misaligned_ex),  // from ID/EX pipeline
      .data_misaligned_i   (data_misaligned),

      .ctrl_transfer_insn_in_dec_i(ctrl_transfer_insn_in_dec),

      // FPU
      .fpu_fflags_we_o(fflags_we),
      .fpu_fflags_o   (fflags_csr),

      // APU
      .apu_en_i      (apu_en_ex),
      .apu_op_i      (apu_op_ex),
      .apu_lat_i     (apu_lat_ex),
      .apu_operands_i(apu_operands_ex),
      .apu_waddr_i   (apu_waddr_ex),

      .apu_read_regs_i        (apu_read_regs),
      .apu_read_regs_valid_i  (apu_read_regs_valid),
      .apu_read_dep_o         (apu_read_dep),
      .apu_read_dep_for_jalr_o(apu_read_dep_for_jalr),
      .apu_write_regs_i       (apu_write_regs),
      .apu_write_regs_valid_i (apu_write_regs_valid),
      .apu_write_dep_o        (apu_write_dep),

      .apu_perf_type_o(perf_apu_type),
      .apu_perf_cont_o(perf_apu_cont),
      .apu_perf_wb_o  (perf_apu_wb),
      .apu_ready_wb_o (apu_ready_wb),
      .apu_busy_o     (apu_busy_o),

      // CVFPU interface
      // handshake signals
      .apu_req_o     (apu_req_o),
      .apu_gnt_i     (apu_gnt_i),
      // request channel
      .apu_operands_o(apu_operands_o),
      .apu_op_o      (apu_op_o),
      // response channel
      .apu_rvalid_i  (apu_rvalid_i),
      .apu_result_i  (apu_result_i),
      .apu_flags_i   (apu_flags_i),

      .lsu_en_i   (data_req_ex),
      .lsu_rdata_i(lsu_rdata),

      // interface with CSRs
      .csr_access_i(csr_access_ex),
      .csr_rdata_i (csr_rdata),

      // From ID Stage: Regfile control signals
      .branch_in_ex_i     (branch_in_ex),
      .regfile_alu_waddr_i(regfile_alu_waddr_ex),
      .regfile_alu_we_i   (regfile_alu_we_ex),

      .regfile_waddr_i(regfile_waddr_ex),
      .regfile_we_i   (regfile_we_ex),

      // Output of ex stage pipeline
      .regfile_waddr_wb_o   (regfile_waddr_fw_wb_o),
      .regfile_we_wb_o      (regfile_we_wb),
      .regfile_we_wb_power_o(regfile_we_wb_power),
      .regfile_wdata_wb_o   (regfile_wdata),

      // To IF: Jump and branch target and decision
      .jump_target_o    (jump_target_ex),
      .branch_decision_o(branch_decision),

      // To ID stage: Forwarding signals
      .regfile_alu_waddr_fw_o   (regfile_alu_waddr_fw),
      .regfile_alu_we_fw_o      (regfile_alu_we_fw),
      .regfile_alu_we_fw_power_o(regfile_alu_we_fw_power),
      .regfile_alu_wdata_fw_o   (regfile_alu_wdata_fw),

      // stall control
      .is_decoding_i (is_decoding),
      .lsu_ready_ex_i(lsu_ready_ex),
      .lsu_err_i     (data_err_pmp),

      .ex_ready_o(ex_ready),
      .ex_valid_o(ex_valid),
      .wb_ready_i(lsu_ready_wb)
  );


  ////////////////////////////////////////////////////////////////////////////////////////
  //    _     ___    _    ____    ____ _____ ___  ____  _____   _   _ _   _ ___ _____   //
  //   | |   / _ \  / \  |  _ \  / ___|_   _/ _ \|  _ \| ____| | | | | \ | |_ _|_   _|  //
  //   | |  | | | |/ _ \ | | | | \___ \ | || | | | |_) |  _|   | | | |  \| || |  | |    //
  //   | |__| |_| / ___ \| |_| |  ___) || || |_| |  _ <| |___  | |_| | |\  || |  | |    //
  //   |_____\___/_/   \_\____/  |____/ |_| \___/|_| \_\_____|  \___/|_| \_|___| |_|    //
  //                                                                                    //
  ////////////////////////////////////////////////////////////////////////////////////////

  cv32e40p_load_store_unit #(
      .PULP_OBI(PULP_OBI)
  ) load_store_unit_i (
      .clk  (clk),
      .rst_n(rst_ni),

      //output to data memory
      .data_req_o    (data_req_pmp),
      .data_gnt_i    (data_gnt_pmp),
      .data_rvalid_i (data_rvalid_i),
      .data_err_i    (1'b0),  // Bus error (not used yet)
      .data_err_pmp_i(data_err_pmp),  // PMP error

      .data_addr_o (data_addr_pmp),
      .data_we_o   (data_we_o),
      .data_atop_o (data_atop_o),
      .data_be_o   (data_be_o),
      .data_wdata_o(data_wdata_o),
      .data_rdata_i(data_rdata_i),

      // signal from ex stage
      .data_we_ex_i        (data_we_ex),
      .data_atop_ex_i      (data_atop_ex),
      .data_type_ex_i      (data_type_ex),
      .data_wdata_ex_i     (alu_operand_c_ex),
      .data_reg_offset_ex_i(data_reg_offset_ex),
      .data_load_event_ex_i(data_load_event_ex),
      .data_sign_ext_ex_i  (data_sign_ext_ex),  // sign extension

      .data_rdata_ex_o  (lsu_rdata),
      .data_req_ex_i    (data_req_ex),
      .operand_a_ex_i   (alu_operand_a_ex),
      .operand_b_ex_i   (alu_operand_b_ex),
      .addr_useincr_ex_i(useincr_addr_ex),

      .data_misaligned_ex_i(data_misaligned_ex),  // from ID/EX pipeline
      .data_misaligned_o   (data_misaligned),

      .p_elw_start_o (p_elw_start),
      .p_elw_finish_o(p_elw_finish),

      // control signals
      .lsu_ready_ex_o(lsu_ready_ex),
      .lsu_ready_wb_o(lsu_ready_wb),

      .busy_o(lsu_busy)
  );

  // Tracer signal
  assign wb_valid = lsu_ready_wb;


  //////////////////////////////////////
  //        ____ ____  ____           //
  //       / ___/ ___||  _ \ ___      //
  //      | |   \___ \| |_) / __|     //
  //      | |___ ___) |  _ <\__ \     //
  //       \____|____/|_| \_\___/     //
  //                                  //
  //   Control and Status Registers   //
  //////////////////////////////////////

  cv32e40p_cs_registers #(
      .N_HWLP          (N_HWLP),
      .A_EXTENSION     (A_EXTENSION),
      .FPU             (FPU),
      .ZFINX           (ZFINX),
      .APU             (APU),
      .PULP_SECURE     (PULP_SECURE),
      .USE_PMP         (USE_PMP),
      .N_PMP_ENTRIES   (N_PMP_ENTRIES),
      .NUM_MHPMCOUNTERS(NUM_MHPMCOUNTERS),
      .COREV_PULP      (COREV_PULP),
      .COREV_CLUSTER   (COREV_CLUSTER),
      .DEBUG_TRIGGER_EN(DEBUG_TRIGGER_EN)
  ) cs_registers_i (
      .clk  (clk),
      .rst_n(rst_ni),

      // Hart ID from outside
      .hart_id_i       (hart_id_i),
      .mtvec_o         (mtvec),
      .utvec_o         (utvec),
      .mtvec_mode_o    (mtvec_mode),
      .utvec_mode_o    (utvec_mode),
      // mtvec address
      .mtvec_addr_i    (mtvec_addr_i[31:0]),
      .csr_mtvec_init_i(csr_mtvec_init),
      // Interface to CSRs (SRAM like)
      .csr_addr_i      (csr_addr),
      .csr_wdata_i     (csr_wdata),
      .csr_op_i        (csr_op),
      .csr_rdata_o     (csr_rdata),

      .fs_off_o   (fs_off),
      .frm_o      (frm_csr),
      .fflags_i   (fflags_csr),
      .fflags_we_i(fflags_we),
      .fregs_we_i (fregs_we),

      // Interrupt related control signals
      .mie_bypass_o  (mie_bypass),
      .mip_i         (mip),
      .m_irq_enable_o(m_irq_enable),
      .u_irq_enable_o(u_irq_enable),
      .csr_irq_sec_i (csr_irq_sec),
      .sec_lvl_o     (sec_lvl_o),
      .mepc_o        (mepc),
      .uepc_o        (uepc),

      // HPM related control signals
      .mcounteren_o(mcounteren),

      // debug
      .debug_mode_i       (debug_mode),
      .debug_cause_i      (debug_cause),
      .debug_csr_save_i   (debug_csr_save),
      .depc_o             (depc),
      .debug_single_step_o(debug_single_step),
      .debug_ebreakm_o    (debug_ebreakm),
      .debug_ebreaku_o    (debug_ebreaku),
      .trigger_match_o    (trigger_match),

      .priv_lvl_o(current_priv_lvl),

      .pmp_addr_o(pmp_addr),
      .pmp_cfg_o (pmp_cfg),

      .pc_if_i(pc_if),
      .pc_id_i(pc_id),
      .pc_ex_i(pc_ex),

      .csr_save_if_i     (csr_save_if),
      .csr_save_id_i     (csr_save_id),
      .csr_save_ex_i     (csr_save_ex),
      .csr_restore_mret_i(csr_restore_mret_id),
      .csr_restore_uret_i(csr_restore_uret_id),

      .csr_restore_dret_i(csr_restore_dret_id),

      .csr_cause_i     (csr_cause),
      .csr_save_cause_i(csr_save_cause),

      // from hwloop registers
      .hwlp_start_i(hwlp_start),
      .hwlp_end_i  (hwlp_end),
      .hwlp_cnt_i  (hwlp_cnt),

      // performance counter related signals
      .mhpmevent_minstret_i    (mhpmevent_minstret),
      .mhpmevent_load_i        (mhpmevent_load),
      .mhpmevent_store_i       (mhpmevent_store),
      .mhpmevent_jump_i        (mhpmevent_jump),
      .mhpmevent_branch_i      (mhpmevent_branch),
      .mhpmevent_branch_taken_i(mhpmevent_branch_taken),
      .mhpmevent_compressed_i  (mhpmevent_compressed),
      .mhpmevent_jr_stall_i    (mhpmevent_jr_stall),
      .mhpmevent_imiss_i       (mhpmevent_imiss),
      .mhpmevent_ld_stall_i    (mhpmevent_ld_stall),
      .mhpmevent_pipe_stall_i  (mhpmevent_pipe_stall),
      .apu_typeconflict_i      (perf_apu_type),
      .apu_contention_i        (perf_apu_cont),
      .apu_dep_i               (perf_apu_dep),
      .apu_wb_i                (perf_apu_wb)
  );

  //  CSR access
  assign csr_addr = csr_addr_int;
  assign csr_wdata = alu_operand_a_ex;
  assign csr_op = csr_op_ex;

  assign csr_addr_int = csr_num_e'(csr_access_ex ? alu_operand_b_ex[11:0] : '0);

  //  Floating-Point registers write
  assign fregs_we     = (FPU == 1 & ZFINX == 0) ? ((regfile_alu_we_fw && regfile_alu_waddr_fw[5]) ||
                                                   (regfile_we_wb     && regfile_waddr_fw_wb_o[5]))
                                                : 1'b0;

  ///////////////////////////
  //   ____  __  __ ____   //
  //  |  _ \|  \/  |  _ \  //
  //  | |_) | |\/| | |_) | //
  //  |  __/| |  | |  __/  //
  //  |_|   |_|  |_|_|     //
  //                       //
  ///////////////////////////

  generate
    if (PULP_SECURE && USE_PMP) begin : gen_pmp
      cv32e40p_pmp #(
          .N_PMP_ENTRIES(N_PMP_ENTRIES)
      ) pmp_unit_i (
          .clk  (clk),
          .rst_n(rst_ni),

          .pmp_privil_mode_i(current_priv_lvl),

          .pmp_addr_i(pmp_addr),
          .pmp_cfg_i (pmp_cfg),


          .data_req_i (data_req_pmp),
          .data_addr_i(data_addr_pmp),
          .data_we_i  (data_we_o),
          .data_gnt_o (data_gnt_pmp),

          .data_req_o    (data_req_o),
          .data_gnt_i    (data_gnt_i),
          .data_addr_o   (data_addr_o),
          .data_err_o    (data_err_pmp),
          .data_err_ack_i(data_err_ack),

          .instr_req_i (instr_req_pmp),
          .instr_addr_i(instr_addr_pmp),
          .instr_gnt_o (instr_gnt_pmp),

          .instr_req_o (instr_req_o),
          .instr_gnt_i (instr_gnt_i),
          .instr_addr_o(instr_addr_o),
          .instr_err_o (instr_err_pmp)
      );
    end else begin : gen_no_pmp
      assign instr_req_o   = instr_req_pmp;
      assign instr_addr_o  = instr_addr_pmp;
      assign instr_gnt_pmp = instr_gnt_i;
      assign instr_err_pmp = 1'b0;

      assign data_req_o    = data_req_pmp;
      assign data_addr_o   = data_addr_pmp;
      assign data_gnt_pmp  = data_gnt_i;
      assign data_err_pmp  = 1'b0;
    end
  endgenerate

`ifdef CV32E40P_ASSERT_ON

  //----------------------------------------------------------------------------
  // Assumptions
  //----------------------------------------------------------------------------

  generate
    if (COREV_CLUSTER) begin : gen_pulp_cluster_assumptions

      // Assumptions/requirements on the environment when pulp_clock_en_i = 0
      property p_env_req_0;
        @(posedge clk_i) disable iff (!rst_ni) (pulp_clock_en_i == 1'b0) |-> (irq_i == 'b0) && (debug_req_i == 1'b0) &&
                                                                            (instr_rvalid_i == 1'b0) && (instr_gnt_i == 1'b0) &&
                                                                            (data_rvalid_i == 1'b0) && (data_gnt_i == 1'b0);
      endproperty

      a_env_req_0 :
      assume property (p_env_req_0);

      // Assumptions/requirements on the environment when core_sleep_o = 0
      property p_env_req_1;
        @(posedge clk_i) disable iff (!rst_ni) (core_sleep_o == 1'b0) |-> (pulp_clock_en_i == 1'b1);
      endproperty

      a_env_req_1 :
      assume property (p_env_req_1);

    end
  endgenerate

  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------

  generate
    if (!COREV_CLUSTER) begin : gen_no_pulp_cluster_assertions
      // Check that a taken IRQ is actually enabled (e.g. that we do not react to an IRQ that was just disabled in MIE)
      property p_irq_enabled_0;
        @(posedge clk) disable iff (!rst_ni) (pc_set && (pc_mux_id == PC_EXCEPTION) && (exc_pc_mux_id == EXC_PC_IRQ)) |->
         (cs_registers_i.mie_n[exc_cause] && cs_registers_i.mstatus_q.mie);
      endproperty

      a_irq_enabled_0 :
      assert property (p_irq_enabled_0);

      // Check that a taken IRQ was for an enabled cause and that mstatus.mie gets disabled
      property p_irq_enabled_1;
        @(posedge clk) disable iff (!rst_ni) (pc_set && (pc_mux_id == PC_EXCEPTION) && (exc_pc_mux_id == EXC_PC_IRQ)) |=>
         (cs_registers_i.mcause_q[5] && cs_registers_i.mie_q[cs_registers_i.mcause_q[4:0]] && !cs_registers_i.mstatus_q.mie);
      endproperty

      a_irq_enabled_1 :
      assert property (p_irq_enabled_1);
    end
  endgenerate

  generate
    if (!COREV_PULP) begin : gen_no_pulp_xpulp_assertions

      // Illegal, ECALL, EBRK checks excluded for PULP due to other definition for for Hardware Loop

      // First illegal instruction decoded
      logic        first_illegal_found;
      logic        first_ecall_found;
      logic        first_ebrk_found;
      logic [31:0] expected_illegal_mepc;
      logic [31:0] expected_ecall_mepc;
      logic [31:0] expected_ebrk_mepc;

      always_ff @(posedge clk, negedge rst_ni) begin
        if (rst_ni == 1'b0) begin
          first_illegal_found   <= 1'b0;
          first_ecall_found     <= 1'b0;
          first_ebrk_found      <= 1'b0;
          expected_illegal_mepc <= 32'b0;
          expected_ecall_mepc   <= 32'b0;
          expected_ebrk_mepc    <= 32'b0;
        end else begin
          if (!first_illegal_found && is_decoding && id_valid && id_stage_i.illegal_insn_dec && !id_stage_i.controller_i.debug_mode_n) begin
            first_illegal_found   <= 1'b1;
            expected_illegal_mepc <= pc_id;
          end
          if (!first_ecall_found && is_decoding && id_valid && id_stage_i.ecall_insn_dec && !id_stage_i.controller_i.debug_mode_n) begin
            first_ecall_found   <= 1'b1;
            expected_ecall_mepc <= pc_id;
          end
          if (!first_ebrk_found && is_decoding && id_valid && id_stage_i.ebrk_insn_dec && (id_stage_i.controller_i.ctrl_fsm_ns != DBG_FLUSH)) begin
            first_ebrk_found   <= 1'b1;
            expected_ebrk_mepc <= pc_id;
          end
        end
      end

      // First mepc write for illegal instruction exception
      logic        first_cause_illegal_found;
      logic        first_cause_ecall_found;
      logic        first_cause_ebrk_found;
      logic [31:0] actual_illegal_mepc;
      logic [31:0] actual_ecall_mepc;
      logic [31:0] actual_ebrk_mepc;

      always_ff @(posedge clk, negedge rst_ni) begin
        if (rst_ni == 1'b0) begin
          first_cause_illegal_found <= 1'b0;
          first_cause_ecall_found   <= 1'b0;
          first_cause_ebrk_found    <= 1'b0;
          actual_illegal_mepc       <= 32'b0;
          actual_ecall_mepc         <= 32'b0;
          actual_ebrk_mepc          <= 32'b0;
        end else begin
          if (!first_cause_illegal_found && (cs_registers_i.csr_cause_i == {
                1'b0, EXC_CAUSE_ILLEGAL_INSN
              }) && csr_save_cause) begin
            first_cause_illegal_found <= 1'b1;
            actual_illegal_mepc       <= cs_registers_i.mepc_n;
          end
          if (!first_cause_ecall_found && (cs_registers_i.csr_cause_i == {
                1'b0, EXC_CAUSE_ECALL_MMODE
              }) && csr_save_cause) begin
            first_cause_ecall_found <= 1'b1;
            actual_ecall_mepc       <= cs_registers_i.mepc_n;
          end
          if (!first_cause_ebrk_found && (cs_registers_i.csr_cause_i == {
                1'b0, EXC_CAUSE_BREAKPOINT
              }) && csr_save_cause) begin
            first_cause_ebrk_found <= 1'b1;
            actual_ebrk_mepc       <= cs_registers_i.mepc_n;
          end
        end
      end

      // Check that mepc is updated with PC of illegal instruction
      property p_illegal_mepc;
        @(posedge clk) disable iff (!rst_ni) (first_illegal_found && first_cause_illegal_found) |=> (expected_illegal_mepc == actual_illegal_mepc);
      endproperty

      a_illegal_mepc :
      assert property (p_illegal_mepc);

      // Check that mepc is updated with PC of the ECALL instruction
      property p_ecall_mepc;
        @(posedge clk) disable iff (!rst_ni) (first_ecall_found && first_cause_ecall_found) |=> (expected_ecall_mepc == actual_ecall_mepc);
      endproperty

      a_ecall_mepc :
      assert property (p_ecall_mepc);

      // Check that mepc is updated with PC of EBRK instruction
      property p_ebrk_mepc;
        @(posedge clk) disable iff (!rst_ni) (first_ebrk_found && first_cause_ebrk_found) |=> (expected_ebrk_mepc == actual_ebrk_mepc);
      endproperty

      a_ebrk_mepc :
      assert property (p_ebrk_mepc);

    end
  endgenerate

  // Single Step only decodes one instruction in non debug mode and next instruction decode is in debug mode
  logic inst_taken;
  assign inst_taken = id_valid && is_decoding;

  a_single_step :
  assert property
  (
    @(posedge clk) disable iff (!rst_ni)
    (inst_taken && debug_single_step && ~debug_mode)
    ##1 inst_taken [->1]
    |-> (debug_mode && debug_single_step));

`endif

endmodule
