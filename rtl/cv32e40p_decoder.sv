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
// Engineer        Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Additional contributions by:                                               //
//                 Matthias Baer - baermatt@student.ethz.ch                   //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Decoder                                                    //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Decoder                                                    //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40p_decoder
  import cv32e40p_pkg::*;
  import cv32e40p_apu_core_pkg::*;
  import cv32e40p_fpu_pkg::*;
#(
  parameter COREV_PULP        = 1,              // PULP ISA Extension (including PULP specific CSRs and hardware loop, excluding cv.elw)
  parameter COREV_CLUSTER     = 0,              // PULP ISA Extension cv.elw (need COREV_PULP = 1)
  parameter A_EXTENSION       = 0,
  parameter FPU               = 0,
  parameter FPU_ADDMUL_LAT    = 0,
  parameter FPU_OTHERS_LAT    = 0,
  parameter ZFINX             = 0,
  parameter PULP_SECURE       = 0,
  parameter USE_PMP           = 0,
  parameter APU_WOP_CPU       = 6,
  parameter DEBUG_TRIGGER_EN  = 1
)
(
  // signals running to/from controller
  input  logic        deassert_we_i,           // deassert we, we are stalled or not active

  output logic        illegal_insn_o,          // illegal instruction encountered
  output logic        ebrk_insn_o,             // trap instruction encountered

  output logic        mret_insn_o,             // return from exception instruction encountered (M)
  output logic        uret_insn_o,             // return from exception instruction encountered (S)
  output logic        dret_insn_o,             // return from debug (M)

  output logic        mret_dec_o,              // return from exception instruction encountered (M) without deassert
  output logic        uret_dec_o,              // return from exception instruction encountered (S) without deassert
  output logic        dret_dec_o,              // return from debug (M) without deassert

  output logic        ecall_insn_o,            // environment call (syscall) instruction encountered
  output logic        wfi_o       ,            // pipeline flush is requested

  output logic        fencei_insn_o,           // fence.i instruction

  output logic        rega_used_o,             // rs1 is used by current instruction
  output logic        regb_used_o,             // rs2 is used by current instruction
  output logic        regc_used_o,             // rs3 is used by current instruction

  output logic        reg_fp_a_o,              // fp reg a is used
  output logic        reg_fp_b_o,              // fp reg b is used
  output logic        reg_fp_c_o,              // fp reg c is used
  output logic        reg_fp_d_o,              // fp reg d is used

  output logic [ 0:0] bmask_a_mux_o,           // bit manipulation mask a mux
  output logic [ 1:0] bmask_b_mux_o,           // bit manipulation mask b mux
  output logic        alu_bmask_a_mux_sel_o,   // bit manipulation mask a mux (reg or imm)
  output logic        alu_bmask_b_mux_sel_o,   // bit manipulation mask b mux (reg or imm)

  // from IF/ID pipeline
  input  logic [31:0] instr_rdata_i,           // instruction read from instr memory/cache
  input  logic        illegal_c_insn_i,        // compressed instruction decode failed

  // ALU signals
  output logic        alu_en_o,                // ALU enable
  output alu_opcode_e alu_operator_o, // ALU operation selection
  output logic [2:0]  alu_op_a_mux_sel_o,      // operand a selection: reg value, PC, immediate or zero
  output logic [2:0]  alu_op_b_mux_sel_o,      // operand b selection: reg value or immediate
  output logic [1:0]  alu_op_c_mux_sel_o,      // operand c selection: reg value or jump target
  output logic        alu_vec_o,               // vectorial instruction
  output logic [1:0]  alu_vec_mode_o,          // selects between 32 bit, 16 bit and 8 bit vectorial modes
  output logic        scalar_replication_o,    // scalar replication enable
  output logic        scalar_replication_c_o,  // scalar replication enable for operand C
  output logic [0:0]  imm_a_mux_sel_o,         // immediate selection for operand a
  output logic [3:0]  imm_b_mux_sel_o,         // immediate selection for operand b
  output logic [1:0]  regc_mux_o,              // register c selection: S3, RD or 0
  output logic        is_clpx_o,               // whether the instruction is complex (pulpv3) or not
  output logic        is_subrot_o,

  // MUL related control signals
  output mul_opcode_e mult_operator_o,         // Multiplication operation selection
  output logic        mult_int_en_o,           // perform integer multiplication
  output logic        mult_dot_en_o,           // perform dot multiplication
  output logic [0:0]  mult_imm_mux_o,          // Multiplication immediate mux selector
  output logic        mult_sel_subword_o,      // Select subwords for 16x16 bit of multiplier
  output logic [1:0]  mult_signed_mode_o,      // Multiplication in signed mode
  output logic [1:0]  mult_dot_signed_o,       // Dot product in signed mode

  // FPU
  input  logic            fs_off_i, // Floating-Point State field from MSTATUS
  input  logic [C_RM-1:0] frm_i,    // Rounding mode from float CSR

  output logic [cv32e40p_fpu_pkg::FP_FORMAT_BITS-1:0]  fpu_dst_fmt_o,   // fpu destination format
  output logic [cv32e40p_fpu_pkg::FP_FORMAT_BITS-1:0]  fpu_src_fmt_o,   // fpu source format
  output logic [cv32e40p_fpu_pkg::INT_FORMAT_BITS-1:0] fpu_int_fmt_o,   // fpu integer format (for casts)

  // APU
  output logic                   apu_en_o,
  output logic [APU_WOP_CPU-1:0] apu_op_o,
  output logic [1:0]             apu_lat_o,
  output logic [2:0]             fp_rnd_mode_o,

  // register file related signals
  output logic        regfile_mem_we_o,        // write enable for regfile
  output logic        regfile_alu_we_o,        // write enable for 2nd regfile port
  output logic        regfile_alu_we_dec_o,    // write enable for 2nd regfile port without deassert
  output logic        regfile_alu_waddr_sel_o, // Select register write address for ALU/MUL operations

  // CSR manipulation
  output logic        csr_access_o,            // access to CSR
  output logic        csr_status_o,            // access to xstatus CSR
  output csr_opcode_e csr_op_o,                // operation to perform on CSR
  input  PrivLvl_t    current_priv_lvl_i,      // The current privilege level

  // LD/ST unit signals
  output logic        data_req_o,              // start transaction to data memory
  output logic        data_we_o,               // data memory write enable
  output logic        prepost_useincr_o,       // when not active bypass the alu result for address calculation
  output logic [1:0]  data_type_o,             // data type on data memory: byte, half word or word
  output logic [1:0]  data_sign_extension_o,   // sign extension on read data from data memory / NaN boxing
  output logic [1:0]  data_reg_offset_o,       // offset in byte inside register for stores
  output logic        data_load_event_o,       // data request is in the special event range

  // Atomic memory access
  output logic [5:0] atop_o,

  // hwloop signals
  output logic [2:0]  hwlp_we_o,               // write enable for hwloop regs
  output logic [1:0]  hwlp_target_mux_sel_o,   // selects immediate for hwloop target
  output logic [1:0]  hwlp_start_mux_sel_o,    // selects hwloop start address input
  output logic        hwlp_cnt_mux_sel_o,      // selects hwloop counter input

  input  logic        debug_mode_i,            // processor is in debug mode
  input  logic        debug_wfi_no_sleep_i,    // do not let WFI cause sleep

  // jump/branches
  output logic [1:0]  ctrl_transfer_insn_in_dec_o,  // control transfer instruction without deassert
  output logic [1:0]  ctrl_transfer_insn_in_id_o,   // control transfer instructio is decoded
  output logic [1:0]  ctrl_transfer_target_mux_sel_o,        // jump target selection

  // HPM related control signals
  input  logic [31:0] mcounteren_i
);

  // write enable/request control
  logic       regfile_mem_we;
  logic       regfile_alu_we;
  logic       data_req;
  logic [2:0] hwlp_we;
  logic       csr_illegal;
  logic [1:0] ctrl_transfer_insn;

  csr_opcode_e csr_op;

  logic       alu_en;
  logic       mult_int_en;
  logic       mult_dot_en;
  logic       apu_en;

  // this instruction needs floating-point rounding-mode verification
  logic check_fprm;

  logic [cv32e40p_fpu_pkg::OP_BITS-1:0] fpu_op;     // fpu operation
  logic                                 fpu_op_mod; // fpu operation modifier
  logic                                 fpu_vec_op; // fpu vectorial operation
  // unittypes for latencies to help us decode for APU
  enum logic[1:0] {ADDMUL, DIVSQRT, NONCOMP, CONV} fp_op_group;


  /////////////////////////////////////////////
  //   ____                     _            //
  //  |  _ \  ___  ___ ___   __| | ___ _ __  //
  //  | | | |/ _ \/ __/ _ \ / _` |/ _ \ '__| //
  //  | |_| |  __/ (_| (_) | (_| |  __/ |    //
  //  |____/ \___|\___\___/ \__,_|\___|_|    //
  //                                         //
  /////////////////////////////////////////////

  always_comb
  begin: instruction_decoder
    ctrl_transfer_insn             = BRANCH_NONE;
    ctrl_transfer_target_mux_sel_o = JT_JAL;

    alu_en                         = 1'b1;
    alu_operator_o                 = ALU_SLTU;
    alu_op_a_mux_sel_o             = OP_A_REGA_OR_FWD;
    alu_op_b_mux_sel_o             = OP_B_REGB_OR_FWD;
    alu_op_c_mux_sel_o             = OP_C_REGC_OR_FWD;
    alu_vec_o                      = 1'b0;
    alu_vec_mode_o                 = VEC_MODE32;
    scalar_replication_o           = 1'b0;
    scalar_replication_c_o         = 1'b0;
    regc_mux_o                     = REGC_ZERO;
    imm_a_mux_sel_o                = IMMA_ZERO;
    imm_b_mux_sel_o                = IMMB_I;

    mult_int_en                    = 1'b0;
    mult_dot_en                    = 1'b0;
    mult_operator_o                = MUL_I;
    mult_imm_mux_o                 = MIMM_ZERO;
    mult_signed_mode_o             = 2'b00;
    mult_sel_subword_o             = 1'b0;
    mult_dot_signed_o              = 2'b00;

    apu_en                         = 1'b0;
    apu_op_o                       = '0;
    apu_lat_o                      = '0;
    fp_rnd_mode_o                  = '0;
    fpu_op                         = cv32e40p_fpu_pkg::SGNJ;
    fpu_op_mod                     = 1'b0;
    fpu_vec_op                     = 1'b0;
    fpu_dst_fmt_o                  = cv32e40p_fpu_pkg::FP32;
    fpu_src_fmt_o                  = cv32e40p_fpu_pkg::FP32;
    fpu_int_fmt_o                  = cv32e40p_fpu_pkg::INT32;
    check_fprm                     = 1'b0;
    fp_op_group                    = ADDMUL;

    regfile_mem_we                 = 1'b0;
    regfile_alu_we                 = 1'b0;
    regfile_alu_waddr_sel_o        = 1'b1;

    prepost_useincr_o              = 1'b1;

    hwlp_we                        = 3'b0;
    hwlp_target_mux_sel_o          = 2'b0;
    hwlp_start_mux_sel_o           = 2'b0;
    hwlp_cnt_mux_sel_o             = 1'b0;

    csr_access_o                   = 1'b0;
    csr_status_o                   = 1'b0;
    csr_illegal                    = 1'b0;
    csr_op                         = CSR_OP_READ;
    mret_insn_o                    = 1'b0;
    uret_insn_o                    = 1'b0;

    dret_insn_o                    = 1'b0;

    data_we_o                      = 1'b0;
    data_type_o                    = 2'b00;
    data_sign_extension_o          = 2'b00;
    data_reg_offset_o              = 2'b00;
    data_req                       = 1'b0;
    data_load_event_o              = 1'b0;

    atop_o                         = 6'b000000;

    illegal_insn_o                 = 1'b0;
    ebrk_insn_o                    = 1'b0;
    ecall_insn_o                   = 1'b0;
    wfi_o                          = 1'b0;

    fencei_insn_o                  = 1'b0;

    rega_used_o                    = 1'b0;
    regb_used_o                    = 1'b0;
    regc_used_o                    = 1'b0;
    reg_fp_a_o                     = 1'b0;
    reg_fp_b_o                     = 1'b0;
    reg_fp_c_o                     = 1'b0;
    reg_fp_d_o                     = 1'b0;

    bmask_a_mux_o                  = BMASK_A_ZERO;
    bmask_b_mux_o                  = BMASK_B_ZERO;
    alu_bmask_a_mux_sel_o          = BMASK_A_IMM;
    alu_bmask_b_mux_sel_o          = BMASK_B_IMM;

    is_clpx_o                      = 1'b0;
    is_subrot_o                    = 1'b0;

    mret_dec_o                     = 1'b0;
    uret_dec_o                     = 1'b0;
    dret_dec_o                     = 1'b0;

    unique case (instr_rdata_i[6:0])

      //////////////////////////////////////
      //      _ _   _ __  __ ____  ____   //
      //     | | | | |  \/  |  _ \/ ___|  //
      //  _  | | | | | |\/| | |_) \___ \  //
      // | |_| | |_| | |  | |  __/ ___) | //
      //  \___/ \___/|_|  |_|_|   |____/  //
      //                                  //
      //////////////////////////////////////

      OPCODE_JAL: begin   // Jump and Link
        ctrl_transfer_target_mux_sel_o = JT_JAL;
        ctrl_transfer_insn    = BRANCH_JAL;
        // Calculate and store PC+4
        alu_op_a_mux_sel_o  = OP_A_CURRPC;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMMB_PCINCR;
        alu_operator_o      = ALU_ADD;
        regfile_alu_we      = 1'b1;
        // Calculate jump target (= PC + UJ imm)
      end

      OPCODE_JALR: begin  // Jump and Link Register
        ctrl_transfer_target_mux_sel_o = JT_JALR;
        ctrl_transfer_insn    = BRANCH_JALR;
        // Calculate and store PC+4
        alu_op_a_mux_sel_o  = OP_A_CURRPC;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMMB_PCINCR;
        alu_operator_o      = ALU_ADD;
        regfile_alu_we      = 1'b1;
        // Calculate jump target (= RS1 + I imm)
        rega_used_o         = 1'b1;

        if (instr_rdata_i[14:12] != 3'b0) begin
          ctrl_transfer_insn = BRANCH_NONE;
          regfile_alu_we     = 1'b0;
          illegal_insn_o     = 1'b1;
        end
      end

      OPCODE_BRANCH: begin // Branch
        ctrl_transfer_target_mux_sel_o = JT_COND;
        ctrl_transfer_insn             = BRANCH_COND;
        alu_op_c_mux_sel_o             = OP_C_JT;
        rega_used_o                    = 1'b1;
        regb_used_o                    = 1'b1;

        unique case (instr_rdata_i[14:12])
          3'b000 : alu_operator_o = ALU_EQ;
          3'b001 : alu_operator_o = ALU_NE;
          3'b100 : alu_operator_o = ALU_LTS;
          3'b101 : alu_operator_o = ALU_GES;
          3'b110 : alu_operator_o = ALU_LTU;
          3'b111 : alu_operator_o = ALU_GEU;
          default: illegal_insn_o = 1'b1;
        endcase
      end


      //////////////////////////////////
      //  _     ____    ______ _____  //
      // | |   |  _ \  / / ___|_   _| //
      // | |   | | | |/ /\___ \ | |   //
      // | |___| |_| / /  ___) || |   //
      // |_____|____/_/  |____/ |_|   //
      //                              //
      //////////////////////////////////

      OPCODE_STORE: begin
        data_req           = 1'b1;
        data_we_o          = 1'b1;
        rega_used_o        = 1'b1;
        regb_used_o        = 1'b1;
        alu_operator_o     = ALU_ADD;
        // pass write data through ALU operand c
        alu_op_c_mux_sel_o = OP_C_REGB_OR_FWD;
        // offset from immediate
        imm_b_mux_sel_o    = IMMB_S;
        alu_op_b_mux_sel_o = OP_B_IMM;

        // store size
        unique case (instr_rdata_i[14:12])
          3'b000 : data_type_o = 2'b10; // SB
          3'b001 : data_type_o = 2'b01; // SH
          3'b010 : data_type_o = 2'b00; // SW
          default: begin
            illegal_insn_o = 1'b1;
            data_req       = 1'b0;
            data_we_o      = 1'b0;
          end
        endcase
      end

      OPCODE_LOAD: begin
        data_req           = 1'b1;
        regfile_mem_we     = 1'b1;
        rega_used_o        = 1'b1;
        alu_operator_o     = ALU_ADD;
        // offset from immediate
        alu_op_b_mux_sel_o = OP_B_IMM;
        imm_b_mux_sel_o    = IMMB_I;

        // sign/zero extension
        data_sign_extension_o = {1'b0,~instr_rdata_i[14]};

        // load size
        unique case (instr_rdata_i[14:12])
          3'b000, 3'b100: data_type_o = 2'b10; // LB/LBU
          3'b001, 3'b101: data_type_o = 2'b01; // LH/LHU
          3'b010        : data_type_o = 2'b00; // LW
          default: begin
            illegal_insn_o = 1'b1;
          end
        endcase
      end

      OPCODE_AMO: begin
        if (A_EXTENSION) begin : decode_amo
          if (instr_rdata_i[14:12] == 3'b010) begin // RV32A Extension (word)
            data_req          = 1'b1;
            data_type_o       = 2'b00;
            rega_used_o       = 1'b1;
            regb_used_o       = 1'b1;
            regfile_mem_we    = 1'b1;
            prepost_useincr_o = 1'b0; // only use alu_operand_a as address (not a+b)
            alu_op_a_mux_sel_o = OP_A_REGA_OR_FWD;

            data_sign_extension_o = 1'b1;

            // Apply AMO instruction at `atop_o`.
            atop_o = {1'b1, instr_rdata_i[31:27]};

            unique case (instr_rdata_i[31:27])
              AMO_LR: begin
                data_we_o = 1'b0;
              end
              AMO_SC,
              AMO_SWAP,
              AMO_ADD,
              AMO_XOR,
              AMO_AND,
              AMO_OR,
              AMO_MIN,
              AMO_MAX,
              AMO_MINU,
              AMO_MAXU: begin
                data_we_o = 1'b1;
                alu_op_c_mux_sel_o = OP_C_REGB_OR_FWD; // pass write data through ALU operand c
              end
              default : illegal_insn_o = 1'b1;
            endcase
          end
          else begin
            illegal_insn_o = 1'b1;
          end
        end else begin : no_decode_amo
          illegal_insn_o = 1'b1;
        end
      end

      //////////////////////////
      //     _    _    _   _  //
      //    / \  | |  | | | | //
      //   / _ \ | |  | | | | //
      //  / ___ \| |__| |_| | //
      // /_/   \_\_____\___/  //
      //                      //
      //////////////////////////

      OPCODE_LUI: begin  // Load Upper Immediate
        alu_op_a_mux_sel_o  = OP_A_IMM;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_a_mux_sel_o     = IMMA_ZERO;
        imm_b_mux_sel_o     = IMMB_U;
        alu_operator_o      = ALU_ADD;
        regfile_alu_we      = 1'b1;
      end

      OPCODE_AUIPC: begin  // Add Upper Immediate to PC
        alu_op_a_mux_sel_o  = OP_A_CURRPC;
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMMB_U;
        alu_operator_o      = ALU_ADD;
        regfile_alu_we      = 1'b1;
      end

      OPCODE_OPIMM: begin // Register-Immediate ALU Operations
        alu_op_b_mux_sel_o  = OP_B_IMM;
        imm_b_mux_sel_o     = IMMB_I;
        regfile_alu_we      = 1'b1;
        rega_used_o         = 1'b1;

        unique case (instr_rdata_i[14:12])
          3'b000: alu_operator_o = ALU_ADD;  // Add Immediate
          3'b010: alu_operator_o = ALU_SLTS; // Set to one if Lower Than Immediate
          3'b011: alu_operator_o = ALU_SLTU; // Set to one if Lower Than Immediate Unsigned
          3'b100: alu_operator_o = ALU_XOR;  // Exclusive Or with Immediate
          3'b110: alu_operator_o = ALU_OR;   // Or with Immediate
          3'b111: alu_operator_o = ALU_AND;  // And with Immediate

          3'b001: begin
            alu_operator_o = ALU_SLL;  // Shift Left Logical by Immediate
            if (instr_rdata_i[31:25] != 7'b0)
              illegal_insn_o = 1'b1;
          end

          3'b101: begin
            if (instr_rdata_i[31:25] == 7'b0)
              alu_operator_o = ALU_SRL;  // Shift Right Logical by Immediate
            else if (instr_rdata_i[31:25] == 7'b010_0000)
              alu_operator_o = ALU_SRA;  // Shift Right Arithmetically by Immediate
            else
              illegal_insn_o = 1'b1;
          end


        endcase
      end

      OPCODE_OP: begin

        // PREFIX 11
        if (instr_rdata_i[31:30] == 2'b11) begin
          illegal_insn_o = 1'b1;

        // PREFIX 10
        end else if (instr_rdata_i[31:30] == 2'b10) begin
          if (instr_rdata_i[29:25] == 5'b00000) begin
            illegal_insn_o = 1'b1;

          ///////////////////////
          // VECTORIAL FLOAT OPS
          ///////////////////////
          end else begin
            // Vectorial FP
            if (FPU == 1 && C_XFVEC == 1) begin

              // using APU instead of ALU
              alu_en           = 1'b0;
              apu_en           = 1'b1;
              // by default, set all registers to FP registers and use 2
              rega_used_o      = 1'b1;
              regb_used_o      = 1'b1;
              if (ZFINX == 0) begin
                reg_fp_a_o     = 1'b1;
                reg_fp_b_o     = 1'b1;
                reg_fp_d_o     = 1'b1;
              end else begin
                reg_fp_a_o     = 1'b0;
                reg_fp_b_o     = 1'b0;
                reg_fp_d_o     = 1'b0;
              end
              fpu_vec_op       = 1'b1;
              // replication bit comes from instruction (can change for some ops)
              scalar_replication_o = instr_rdata_i[14];
              // by default we need to verify rm is legal but assume it is for now
              check_fprm       = 1'b1;
              fp_rnd_mode_o    = frm_i; // all vectorial ops have rm from fcsr

              // Decode Formats
              unique case (instr_rdata_i[13:12])
                // FP32
                2'b00: begin
                  fpu_dst_fmt_o  = cv32e40p_fpu_pkg::FP32;
                  alu_vec_mode_o = VEC_MODE32;
                end
                // FP16ALT
                2'b01: begin
                  fpu_dst_fmt_o  = cv32e40p_fpu_pkg::FP16ALT;
                  alu_vec_mode_o = VEC_MODE16;
                end
                // FP16
                2'b10: begin
                  fpu_dst_fmt_o  = cv32e40p_fpu_pkg::FP16;
                  alu_vec_mode_o = VEC_MODE16;
                end
                // FP8
                2'b11: begin
                  fpu_dst_fmt_o  = cv32e40p_fpu_pkg::FP8;
                  alu_vec_mode_o = VEC_MODE8;
                end
              endcase

              // By default, src=dst
              fpu_src_fmt_o = fpu_dst_fmt_o;

              // decode vectorial FP instruction
              unique case (instr_rdata_i[29:25]) inside
                // vfadd.vfmt - Vectorial FP Addition
                5'b00001: begin
                  fpu_op      = cv32e40p_fpu_pkg::ADD;
                  fp_op_group = ADDMUL;
                  // FPnew needs addition operands as operand B and C
                  alu_op_b_mux_sel_o     = OP_B_REGA_OR_FWD;
                  alu_op_c_mux_sel_o     = OP_C_REGB_OR_FWD;
                  scalar_replication_o   = 1'b0;
                  scalar_replication_c_o = instr_rdata_i[14];
                end
                // vfsub.vfmt - Vectorial FP Subtraction
                5'b00010: begin
                  fpu_op      = cv32e40p_fpu_pkg::ADD;
                  fpu_op_mod  = 1'b1;
                  fp_op_group = ADDMUL;
                  // FPnew needs addition operands as operand B and C
                  alu_op_b_mux_sel_o     = OP_B_REGA_OR_FWD;
                  alu_op_c_mux_sel_o     = OP_C_REGB_OR_FWD;
                  scalar_replication_o   = 1'b0;
                  scalar_replication_c_o = instr_rdata_i[14];
                end
                // vfmul.vfmt - Vectorial FP Multiplication
                5'b00011: begin
                  fpu_op      = cv32e40p_fpu_pkg::MUL;
                  fp_op_group = ADDMUL;
                end
                // vfdiv.vfmt - Vectorial FP Division
                5'b00100: begin
                  fpu_op      = cv32e40p_fpu_pkg::DIV;
                  fp_op_group = DIVSQRT;
                end
                // vfmin.vfmt - Vectorial FP Minimum
                5'b00101: begin
                  fpu_op        = cv32e40p_fpu_pkg::MINMAX;
                  fp_rnd_mode_o = 3'b000; // min
                  fp_op_group   = NONCOMP;
                  check_fprm    = 1'b0; // instruction encoded in rm
                end
                // vfmax.vfmt - Vectorial FP Maximum
                5'b00110: begin
                  fpu_op        = cv32e40p_fpu_pkg::MINMAX;
                  fp_rnd_mode_o = 3'b001; // max
                  fp_op_group   = NONCOMP;
                  check_fprm    = 1'b0; // instruction encoded in rm
                end
                // vfsqrt.vfmt - Vectorial FP Square Root
                5'b00111: begin
                  regb_used_o = 1'b0;
                  fpu_op      = cv32e40p_fpu_pkg::SQRT;
                  fp_op_group = DIVSQRT;
                  // rs2 and R must be zero
                  if ((instr_rdata_i[24:20] != 5'b00000) || instr_rdata_i[14]) begin
                    illegal_insn_o = 1'b1;
                  end
                end
                // vfmac.vfmt - Vectorial FP Multiply-Accumulate
                5'b01000: begin
                  regc_used_o = 1'b1;
                  regc_mux_o  = REGC_RD; // third operand is rd
                  if (ZFINX == 0) begin
                    reg_fp_c_o = 1'b1;
                  end else begin
                    reg_fp_c_o = 1'b0;
                  end
                  fpu_op      = cv32e40p_fpu_pkg::FMADD;
                  fp_op_group = ADDMUL;
                end
                // vfmre.vfmt - Vectorial FP Multiply-Reduce
                5'b01001: begin
                  regc_used_o = 1'b1;
                  regc_mux_o  = REGC_RD; // third operand is rd
                  if (ZFINX == 0) begin
                    reg_fp_c_o = 1'b1;
                  end else begin
                    reg_fp_c_o = 1'b0;
                  end
                  fpu_op      = cv32e40p_fpu_pkg::FMADD;
                  fpu_op_mod  = 1'b1;
                  fp_op_group = ADDMUL;
                end
                // Moves, Conversions, Classifications
                5'b01100: begin
                  regb_used_o          = 1'b0;
                  scalar_replication_o = 1'b0;
                  // Decode Operation in rs2
                  unique case (instr_rdata_i[24:20]) inside
                    // vfmv.{x.vfmt/vfmt.x} - Vectorial FP Reg <-> GP Reg Moves
                    5'b00000: begin
                      alu_op_b_mux_sel_o = OP_B_REGA_OR_FWD; // set rs2 = rs1 so we can map FMV to SGNJ in the unit
                      fpu_op             = cv32e40p_fpu_pkg::SGNJ;
                      fp_rnd_mode_o      = 3'b011;  // passthrough without checking nan-box
                      fp_op_group        = NONCOMP;
                      check_fprm         = 1'b0;
                      // GP reg to FP reg
                      if (instr_rdata_i[14]) begin
                        reg_fp_a_o       = 1'b0; // go from integer regfile
                        fpu_op_mod       = 1'b0; // nan-box result
                      end
                      // FP reg to GP reg
                      else begin
                        reg_fp_d_o       = 1'b0; // go to integer regfile
                        fpu_op_mod       = 1'b1; // sign-extend result
                      end
                    end
                    // vfclass.vfmt - Vectorial FP Classifications
                    5'b00001: begin
                      reg_fp_d_o    = 1'b0; // go to integer regfile
                      fpu_op        = cv32e40p_fpu_pkg::CLASSIFY;
                      fp_rnd_mode_o = 3'b000;
                      fp_op_group   = NONCOMP;
                      check_fprm    = 1'b0;
                      // R must not be set
                      if (instr_rdata_i[14]) illegal_insn_o = 1'b1;
                    end
                    // vfcvt.{x.vfmt/vfmt.x} - Vectorial FP <-> Int Conversions
                    5'b0001?: begin
                      fp_op_group = CONV;
                      fpu_op_mod  = instr_rdata_i[14]; // signed/unsigned switch
                      // Integer width matches FP width
                      unique case (instr_rdata_i[13:12])
                        // FP32
                        2'b00 : fpu_int_fmt_o = cv32e40p_fpu_pkg::INT32;
                        // FP16[ALT]
                        2'b01,
                        2'b10: fpu_int_fmt_o = cv32e40p_fpu_pkg::INT16;
                        // FP8
                        2'b11: fpu_int_fmt_o = cv32e40p_fpu_pkg::INT8;
                      endcase
                      // Int to FP conversion
                      if (instr_rdata_i[20]) begin
                        reg_fp_a_o = 1'b0; // go from integer regfile
                        fpu_op     = cv32e40p_fpu_pkg::I2F;
                      end
                      // FP to Int conversion
                      else begin
                        reg_fp_d_o = 1'b0; // go to integer regfile
                        fpu_op     = cv32e40p_fpu_pkg::F2I;
                      end
                    end
                    // vfcvt.vfmt.vfmt - Vectorial FP <-> FP Conversions
                    5'b001??: begin
                      fpu_op      = cv32e40p_fpu_pkg::F2F;
                      fp_op_group = CONV;
                      // check source format
                      unique case (instr_rdata_i[21:20])
                        // Only process instruction if corresponding extension is active (static)
                        2'b00: begin
                          fpu_src_fmt_o = cv32e40p_fpu_pkg::FP32;
                          if (~C_RVF) illegal_insn_o = 1'b1;
                        end
                        2'b01: begin
                          fpu_src_fmt_o = cv32e40p_fpu_pkg::FP16ALT;
                          if (~C_XF16ALT) illegal_insn_o = 1'b1;
                        end
                        2'b10: begin
                          fpu_src_fmt_o = cv32e40p_fpu_pkg::FP16;
                          if (~C_XF16) illegal_insn_o = 1'b1;
                        end
                        2'b11: begin
                          fpu_src_fmt_o = cv32e40p_fpu_pkg::FP8;
                          if (~C_XF8) illegal_insn_o = 1'b1;
                        end
                      endcase
                      // R must not be set
                      if (instr_rdata_i[14]) illegal_insn_o = 1'b1;
                    end
                    // others
                    default : illegal_insn_o = 1'b1;
                  endcase
                end
                // vfsgnj.vfmt - Vectorial FP Sign Injection
                5'b01101: begin
                  fpu_op        = cv32e40p_fpu_pkg::SGNJ;
                  fp_rnd_mode_o = 3'b000; // sgnj
                  fp_op_group   = NONCOMP;
                  check_fprm    = 1'b0;
                end
                // vfsgnjn.vfmt - Vectorial FP Negated Sign Injection
                5'b01110: begin
                  fpu_op        = cv32e40p_fpu_pkg::SGNJ;
                  fp_rnd_mode_o = 3'b001; // sgnjn
                  fp_op_group   = NONCOMP;
                  check_fprm    = 1'b0;
                end
                // vfsgnjx.vfmt - Vectorial FP Xored Sign Injection
                5'b01111: begin
                  fpu_op        = cv32e40p_fpu_pkg::SGNJ;
                  fp_rnd_mode_o = 3'b010; // sgnjx
                  fp_op_group   = NONCOMP;
                  check_fprm    = 1'b0;
                end
                // vfeq.vfmt - Vectorial FP Equals
                5'b10000: begin
                  reg_fp_d_o    = 1'b0; // go to integer regfile
                  fpu_op        = cv32e40p_fpu_pkg::CMP;
                  fp_rnd_mode_o = 3'b010; // eq
                  fp_op_group   = NONCOMP;
                  check_fprm    = 1'b0;
                end
                // vfne.vfmt - Vectorial FP Not Equals
                5'b10001: begin
                  reg_fp_d_o    = 1'b0; // go to integer regfile
                  fpu_op        = cv32e40p_fpu_pkg::CMP;
                  fpu_op_mod    = 1'b1; // invert output
                  fp_rnd_mode_o = 3'b010; // eq
                  fp_op_group   = NONCOMP;
                  check_fprm    = 1'b0;
                end
                // vflt.vfmt - Vectorial FP Less Than
                5'b10010: begin
                  reg_fp_d_o    = 1'b0; // go to integer regfile
                  fpu_op        = cv32e40p_fpu_pkg::CMP;
                  fp_rnd_mode_o = 3'b001; // lt
                  fp_op_group   = NONCOMP;
                  check_fprm    = 1'b0;
                end
                // vfge.vfmt - Vectorial FP Greater Than or Equals
                5'b10011: begin
                  reg_fp_d_o    = 1'b0; // go to integer regfile
                  fpu_op        = cv32e40p_fpu_pkg::CMP;
                  fpu_op_mod    = 1'b1; // invert output
                  fp_rnd_mode_o = 3'b001; // lt
                  fp_op_group   = NONCOMP;
                  check_fprm    = 1'b0;
                end
                // vfle.vfmt - Vectorial FP Less Than or Equals
                5'b10100: begin
                  reg_fp_d_o    = 1'b0; // go to integer regfile
                  fpu_op        = cv32e40p_fpu_pkg::CMP;
                  fp_rnd_mode_o = 3'b000; // le
                  fp_op_group   = NONCOMP;
                  check_fprm    = 1'b0;
                end
                // vfgt.vfmt - Vectorial FP Greater Than
                5'b10101: begin
                  reg_fp_d_o    = 1'b0; // go to integer regfile
                  fpu_op        = cv32e40p_fpu_pkg::CMP;
                  fpu_op_mod    = 1'b1; // invert output
                  fp_rnd_mode_o = 3'b000; // le
                  fp_op_group   = NONCOMP;
                  check_fprm    = 1'b0;
                end
                // vfcpk{a-d}.vfmt.s/d
                5'b110??: begin
                  // vfcpk{{a/c}/{b/d}} selection in R bit
                  fpu_op_mod           = instr_rdata_i[14];
                  fp_op_group          = CONV;
                  scalar_replication_o = 1'b0;

                  if (instr_rdata_i[25]) fpu_op = cv32e40p_fpu_pkg::CPKCD; // vfcpk{c/d}
                  else fpu_op = cv32e40p_fpu_pkg::CPKAB; // vfcpk{a/b}

                  // vfcpk{a-d}.vfmt.d - from double
                  if (instr_rdata_i[26]) begin
                    fpu_src_fmt_o  = cv32e40p_fpu_pkg::FP64;
                    if (~C_RVD) illegal_insn_o = 1'b1;
                  end
                  // vfcpk{a-d}.vfmt.s
                  else begin
                    fpu_src_fmt_o  = cv32e40p_fpu_pkg::FP32;
                    if (~C_RVF) illegal_insn_o = 1'b1;
                  end
                  // Resolve legal vfcpk / format combinations (mostly static)
                  if (fpu_op == cv32e40p_fpu_pkg::CPKCD) begin // vfcpk{c/d} not possible unless FP8 and FLEN>=64
                    if (~C_XF8 || ~C_RVD) illegal_insn_o = 1'b1;
                  end else begin
                    if (instr_rdata_i[14]) begin // vfcpkb
                      // vfcpkb not possible for FP32
                      if (fpu_dst_fmt_o == cv32e40p_fpu_pkg::FP32) illegal_insn_o = 1'b1;
                      // vfcpkb not possible for FP16[ALT] if not RVD
                      if (~C_RVD && (fpu_dst_fmt_o != cv32e40p_fpu_pkg::FP8)) illegal_insn_o = 1'b1;
                    end
                  end
                end
                // Rest are illegal instructions
                default: begin
                  illegal_insn_o = 1'b1;
                end
              endcase

              // check enabled formats (static)
              // need RVD for F vectors
              if ((~C_RVF || ~C_RVD) && fpu_dst_fmt_o == cv32e40p_fpu_pkg::FP32) illegal_insn_o = 1'b1;
              // need RVF for F16 vectors
              if ((~C_XF16 || ~C_RVF) && fpu_dst_fmt_o == cv32e40p_fpu_pkg::FP16) illegal_insn_o = 1'b1;
              // need RVF for F16 vectors
              if ((~C_XF16ALT || ~C_RVF) && fpu_dst_fmt_o == cv32e40p_fpu_pkg::FP16ALT) begin
                illegal_insn_o = 1'b1;
              end
              // need F16 for F8 vectors
              if ((~C_XF8 || (~C_XF16 && ~C_XF16ALT)) && fpu_dst_fmt_o == cv32e40p_fpu_pkg::FP8) begin
                illegal_insn_o = 1'b1;
              end

              // check rounding mode
              if (check_fprm) begin
                unique case (frm_i) inside
                  [3'b000:3'b100] : ; //legal rounding modes
                  default         : illegal_insn_o = 1'b1;
                endcase
              end

              // Set latencies for FPnew from config. The C_LAT constants contain the number
              // of pipeline registers. the APU takes the following values:
              // 1 = single cycle (no latency), 2 = one pipestage, 3 = two or more pipestages
              case (fp_op_group)
                // ADDMUL has format dependent latency
                ADDMUL : begin
                  unique case (fpu_dst_fmt_o)
                    cv32e40p_fpu_pkg::FP32    : apu_lat_o = (FPU_ADDMUL_LAT<2)? FPU_ADDMUL_LAT+1: 2'h3;
                    cv32e40p_fpu_pkg::FP16    : apu_lat_o = (C_LAT_FP16<2)    ? C_LAT_FP16+1    : 2'h3;
                    cv32e40p_fpu_pkg::FP16ALT : apu_lat_o = (C_LAT_FP16ALT<2) ? C_LAT_FP16ALT+1 : 2'h3;
                    cv32e40p_fpu_pkg::FP8     : apu_lat_o = (C_LAT_FP8<2)     ? C_LAT_FP8+1     : 2'h3;
                    default : ;
                  endcase
                end
                // DIVSQRT is iterative and takes more than 2 cycles
                DIVSQRT : apu_lat_o = 2'h3;
                // NONCOMP uses the same latency for all formats
                NONCOMP : apu_lat_o = (FPU_OTHERS_LAT<2) ? FPU_OTHERS_LAT+1 : 2'h3;
                // CONV uses the same latency for all formats
                CONV    : apu_lat_o = (FPU_OTHERS_LAT<2) ? FPU_OTHERS_LAT+1 : 2'h3;
              endcase

              // Set FPnew OP and OPMOD as the APU op
              apu_op_o = {fpu_vec_op, fpu_op_mod, fpu_op};

            // no FPU or FPU and no Vectors
            end else begin
              illegal_insn_o = 1'b1;
            end
          end // Vectorial Float Ops

        end  // PREFIX 10

        // PREFIX 00/01
        else begin
          regfile_alu_we = 1'b1;
          rega_used_o    = 1'b1;

          if (~instr_rdata_i[28]) regb_used_o = 1'b1;

          unique case ({instr_rdata_i[30:25], instr_rdata_i[14:12]})
            // RV32I ALU operations
            {6'b00_0000, 3'b000}: alu_operator_o = ALU_ADD;   // Add
            {6'b10_0000, 3'b000}: alu_operator_o = ALU_SUB;   // Sub
            {6'b00_0000, 3'b010}: alu_operator_o = ALU_SLTS;  // Set Lower Than
            {6'b00_0000, 3'b011}: alu_operator_o = ALU_SLTU;  // Set Lower Than Unsigned
            {6'b00_0000, 3'b100}: alu_operator_o = ALU_XOR;   // Xor
            {6'b00_0000, 3'b110}: alu_operator_o = ALU_OR;    // Or
            {6'b00_0000, 3'b111}: alu_operator_o = ALU_AND;   // And
            {6'b00_0000, 3'b001}: alu_operator_o = ALU_SLL;   // Shift Left Logical
            {6'b00_0000, 3'b101}: alu_operator_o = ALU_SRL;   // Shift Right Logical
            {6'b10_0000, 3'b101}: alu_operator_o = ALU_SRA;   // Shift Right Arithmetic

            // supported RV32M instructions
            {6'b00_0001, 3'b000}: begin // mul
              alu_en          = 1'b0;
              mult_int_en     = 1'b1;
              mult_operator_o = MUL_MAC32;
              regc_mux_o      = REGC_ZERO;
            end
            {6'b00_0001, 3'b001}: begin // mulh
              alu_en             = 1'b0;
              mult_int_en        = 1'b1;
              regc_used_o        = 1'b1;
              regc_mux_o         = REGC_ZERO;
              mult_signed_mode_o = 2'b11;
              mult_operator_o    = MUL_H;
            end
            {6'b00_0001, 3'b010}: begin // mulhsu
              alu_en             = 1'b0;
              mult_int_en        = 1'b1;
              regc_used_o        = 1'b1;
              regc_mux_o         = REGC_ZERO;
              mult_signed_mode_o = 2'b01;
              mult_operator_o    = MUL_H;
            end
            {6'b00_0001, 3'b011}: begin // mulhu
              alu_en             = 1'b0;
              mult_int_en        = 1'b1;
              regc_used_o        = 1'b1;
              regc_mux_o         = REGC_ZERO;
              mult_signed_mode_o = 2'b00;
              mult_operator_o    = MUL_H;
            end
            {6'b00_0001, 3'b100}: begin // div
              alu_op_a_mux_sel_o = OP_A_REGB_OR_FWD;
              alu_op_b_mux_sel_o = OP_B_REGA_OR_FWD;
              regb_used_o        = 1'b1;
              alu_operator_o     = ALU_DIV;
            end
            {6'b00_0001, 3'b101}: begin // divu
              alu_op_a_mux_sel_o = OP_A_REGB_OR_FWD;
              alu_op_b_mux_sel_o = OP_B_REGA_OR_FWD;
              regb_used_o        = 1'b1;
              alu_operator_o     = ALU_DIVU;
            end
            {6'b00_0001, 3'b110}: begin // rem
              alu_op_a_mux_sel_o = OP_A_REGB_OR_FWD;
              alu_op_b_mux_sel_o = OP_B_REGA_OR_FWD;
              regb_used_o        = 1'b1;
              alu_operator_o     = ALU_REM;
            end
            {6'b00_0001, 3'b111}: begin // remu
              alu_op_a_mux_sel_o = OP_A_REGB_OR_FWD;
              alu_op_b_mux_sel_o = OP_B_REGA_OR_FWD;
              regb_used_o        = 1'b1;
              alu_operator_o     = ALU_REMU;
            end

            default: begin
              illegal_insn_o = 1'b1;
            end
          endcase
        end
      end

      ////////////////////////////
      //  ______ _____  _    _  //
      // |  ____|  __ \| |  | | //
      // | |__  | |__) | |  | | //
      // |  __| |  ___/| |  | | //
      // | |    | |    | |__| | //
      // |_|    |_|     \____/  //
      //                        //
      ////////////////////////////

      // Floating Point arithmetic
      OPCODE_OP_FP: begin
        if (FPU == 1 && (ZFINX == 1 || fs_off_i == 1'b0)) begin

          // using APU instead of ALU
          alu_en           = 1'b0;
          apu_en           = 1'b1;
          // by default, set all registers to FP registers and use 2
          rega_used_o      = 1'b1;
          regb_used_o      = 1'b1;
          if (ZFINX == 0) begin
            reg_fp_a_o     = 1'b1;
            reg_fp_b_o     = 1'b1;
            reg_fp_d_o     = 1'b1;
          end else begin
            reg_fp_a_o     = 1'b0;
            reg_fp_b_o     = 1'b0;
            reg_fp_d_o     = 1'b0;
          end
          // by default we need to verify rm is legal but assume it is for now
          check_fprm       = 1'b1;
          fp_rnd_mode_o    = instr_rdata_i[14:12];

          // Decode Formats (preliminary, can change for some ops)
          unique case (instr_rdata_i[26:25])
            // FP32
            2'b00: fpu_dst_fmt_o = cv32e40p_fpu_pkg::FP32;
            // FP64
            2'b01: fpu_dst_fmt_o = cv32e40p_fpu_pkg::FP64;
            // FP16 or FP16ALT
            2'b10: begin
              // FP16alt encoded in rm field
              if (instr_rdata_i[14:12] == 3'b101) fpu_dst_fmt_o = cv32e40p_fpu_pkg::FP16ALT;
              // this can still change to FP16ALT
              else fpu_dst_fmt_o = cv32e40p_fpu_pkg::FP16;
            end
            // FP8
            2'b11: fpu_dst_fmt_o = cv32e40p_fpu_pkg::FP8;
          endcase

          // By default, src=dst
          fpu_src_fmt_o = fpu_dst_fmt_o;

          // decode FP instruction
          unique case (instr_rdata_i[31:27])
            // fadd.fmt - FP Addition
            5'b00000: begin
              fpu_op             = cv32e40p_fpu_pkg::ADD;
              fp_op_group        = ADDMUL;
              alu_op_b_mux_sel_o = OP_B_REGA_OR_FWD;
              alu_op_c_mux_sel_o = OP_C_REGB_OR_FWD;
            end
            // fsub.fmt - FP Subtraction
            5'b00001: begin
              fpu_op             = cv32e40p_fpu_pkg::ADD;
              fpu_op_mod         = 1'b1;
              fp_op_group        = ADDMUL;
              alu_op_b_mux_sel_o = OP_B_REGA_OR_FWD;
              alu_op_c_mux_sel_o = OP_C_REGB_OR_FWD;
            end
            // fmul.fmt - FP Multiplication
            5'b00010: begin
              fpu_op      = cv32e40p_fpu_pkg::MUL;
              fp_op_group = ADDMUL;
            end
            // fdiv.fmt - FP Division
            5'b00011: begin
              fpu_op      = cv32e40p_fpu_pkg::DIV;
              fp_op_group = DIVSQRT;
            end
            // fsqrt.fmt - FP Square Root
            5'b01011: begin
              regb_used_o = 1'b0;
              fpu_op      = cv32e40p_fpu_pkg::SQRT;
              fp_op_group = DIVSQRT;
              // rs2 must be zero
              if (instr_rdata_i[24:20] != 5'b00000) illegal_insn_o = 1'b1;
            end
            // fsgn{j[n]/jx}.fmt - FP Sign Injection
            5'b00100: begin
              fpu_op        = cv32e40p_fpu_pkg::SGNJ;
              fp_op_group   = NONCOMP;
              check_fprm    = 1'b0; // instruction encoded in rm, do the check here
              if (C_XF16ALT) begin  // FP16ALT instructions encoded in rm separately (static)
                if (!(instr_rdata_i[14:12] inside {[3'b000:3'b010], [3'b100:3'b110]})) begin
                  illegal_insn_o = 1'b1;
                end
                // FP16ALT uses special encoding here
                if (instr_rdata_i[14]) begin
                  fpu_dst_fmt_o = cv32e40p_fpu_pkg::FP16ALT;
                  fpu_src_fmt_o = cv32e40p_fpu_pkg::FP16ALT;
                end else begin
                  fp_rnd_mode_o = {1'b0, instr_rdata_i[13:12]};
                end
              end else begin
                if (!(instr_rdata_i[14:12] inside {[3'b000:3'b010]})) illegal_insn_o = 1'b1;
              end
            end
            // fmin/fmax.fmt - FP Minimum / Maximum
            5'b00101: begin
              fpu_op        = cv32e40p_fpu_pkg::MINMAX;
              fp_op_group   = NONCOMP;
              check_fprm    = 1'b0; // instruction encoded in rm, do the check here
              if (C_XF16ALT) begin  // FP16ALT instructions encoded in rm separately (static)
                if (!(instr_rdata_i[14:12] inside {[3'b000:3'b001], [3'b100:3'b101]})) begin
                  illegal_insn_o = 1'b1;
                end
                // FP16ALT uses special encoding here
                if (instr_rdata_i[14]) begin
                  fpu_dst_fmt_o = cv32e40p_fpu_pkg::FP16ALT;
                  fpu_src_fmt_o = cv32e40p_fpu_pkg::FP16ALT;
                end else begin
                  fp_rnd_mode_o = {1'b0, instr_rdata_i[13:12]};
                end
              end else begin
                if (!(instr_rdata_i[14:12] inside {[3'b000:3'b001]})) illegal_insn_o = 1'b1;
              end
            end
            // fcvt.fmt.fmt - FP to FP Conversion
            5'b01000: begin
              regb_used_o   = 1'b0;
              fpu_op        = cv32e40p_fpu_pkg::F2F;
              fp_op_group   = CONV;
              // bits [22:20] used, other bits must be 0
              if (instr_rdata_i[24:23]) illegal_insn_o = 1'b1;
              // check source format
              unique case (instr_rdata_i[22:20])
                // Only process instruction if corresponding extension is active (static)
                3'b000: begin
                  if (!(C_RVF && (C_XF16 || C_XF16ALT || C_XF8))) illegal_insn_o = 1'b1;
                  fpu_src_fmt_o = cv32e40p_fpu_pkg::FP32;
                end
                3'b001: begin
                  if (~C_RVD) illegal_insn_o = 1'b1;
                  fpu_src_fmt_o = cv32e40p_fpu_pkg::FP64;
                end
                3'b010: begin
                  if (~C_XF16) illegal_insn_o = 1'b1;
                  fpu_src_fmt_o = cv32e40p_fpu_pkg::FP16;
                end
                3'b110: begin
                  if (~C_XF16ALT) illegal_insn_o = 1'b1;
                  fpu_src_fmt_o = cv32e40p_fpu_pkg::FP16ALT;
                end
                3'b011: begin
                  if (~C_XF8) illegal_insn_o = 1'b1;
                  fpu_src_fmt_o = cv32e40p_fpu_pkg::FP8;
                end
                default: illegal_insn_o = 1'b1;
              endcase
            end
            // fmulex.s.fmt - FP Expanding Multiplication to FP32
            5'b01001: begin
              if (~C_XF16 && ~C_XF16ALT && ~C_XF8) illegal_insn_o = 1;
              fpu_op        = cv32e40p_fpu_pkg::MUL;
              fp_op_group   = ADDMUL;
              // set dst format to FP32
              fpu_dst_fmt_o = cv32e40p_fpu_pkg::FP32;
            end
            // fmacex.s.fmt - FP Expanding Multipy-Accumulate to FP32
            5'b01010: begin
              if (~C_XF16 && ~C_XF16ALT && ~C_XF8) illegal_insn_o = 1;
              regc_used_o = 1'b1;
              regc_mux_o  = REGC_RD; // third operand is rd
              if (ZFINX == 0) begin
                reg_fp_c_o = 1'b1;
              end else begin
                reg_fp_c_o = 1'b0;
              end
              fpu_op      = cv32e40p_fpu_pkg::FMADD;
              fp_op_group = ADDMUL;
              // set dst format to FP32
              fpu_dst_fmt_o = cv32e40p_fpu_pkg::FP32;
            end
            // feq/flt/fle.fmt - FP Comparisons
            5'b10100: begin
              fpu_op        = cv32e40p_fpu_pkg::CMP;
              fp_op_group   = NONCOMP;
              reg_fp_d_o    = 1'b0; // go to integer regfile
              check_fprm    = 1'b0; // instruction encoded in rm, do the check here
              if (C_XF16ALT) begin  // FP16ALT instructions encoded in rm separately (static)
                if (!(instr_rdata_i[14:12] inside {[3'b000:3'b010], [3'b100:3'b110]})) begin
                  illegal_insn_o = 1'b1;
                end
                // FP16ALT uses special encoding here
                if (instr_rdata_i[14]) begin
                  fpu_dst_fmt_o = cv32e40p_fpu_pkg::FP16ALT;
                  fpu_src_fmt_o = cv32e40p_fpu_pkg::FP16ALT;
                end else begin
                  fp_rnd_mode_o = {1'b0, instr_rdata_i[13:12]};
                end
              end else begin
                if (!(instr_rdata_i[14:12] inside {[3'b000:3'b010]})) illegal_insn_o = 1'b1;
              end
            end
            // fcvt.ifmt.fmt - FP to Int Conversion
            5'b11000: begin
              regb_used_o = 1'b0;
              reg_fp_d_o  = 1'b0; // go to integer regfile
              fpu_op      = cv32e40p_fpu_pkg::F2I;
              fp_op_group = CONV;
              fpu_op_mod  = instr_rdata_i[20]; // signed/unsigned switch

              unique case (instr_rdata_i[26:25]) //fix for casting to different formats other than FP32
                2'b00: begin
                  if (~C_RVF) illegal_insn_o = 1;
                  else fpu_src_fmt_o = cv32e40p_fpu_pkg::FP32;
                end
                2'b01: begin
                  if (~C_RVD) illegal_insn_o = 1;
                  else fpu_src_fmt_o = cv32e40p_fpu_pkg::FP64;
                end
                2'b10: begin
                  if (instr_rdata_i[14:12] == 3'b101) begin
                    if (~C_XF16ALT) illegal_insn_o = 1;
                    else fpu_src_fmt_o = cv32e40p_fpu_pkg::FP16ALT;
                  end else if (~C_XF16) begin
                    illegal_insn_o = 1;
                  end else begin
                    fpu_src_fmt_o = cv32e40p_fpu_pkg::FP16;
                  end
                end
                2'b11: begin
                  if (~C_XF8) illegal_insn_o = 1;
                  else fpu_src_fmt_o = cv32e40p_fpu_pkg::FP8;
                end
              endcase // unique case (instr_rdata_i[26:25])
              // bits [21:20] used, other bits must be 0
              if (instr_rdata_i[24:21]) illegal_insn_o = 1'b1;   // in RV32, no casts to L allowed.
            end
            // fcvt.fmt.ifmt - Int to FP Conversion
            5'b11010: begin
              regb_used_o = 1'b0;
              reg_fp_a_o  = 1'b0; // go from integer regfile
              fpu_op      = cv32e40p_fpu_pkg::I2F;
              fp_op_group = CONV;
              fpu_op_mod  = instr_rdata_i[20]; // signed/unsigned switch
              // bits [21:20] used, other bits must be 0
              if (instr_rdata_i[24:21]) illegal_insn_o = 1'b1;   // in RV32, no casts to L allowed.
            end
            // move and class
            5'b11100: begin
              regb_used_o = 1'b0;
              reg_fp_d_o  = 1'b0; // go to integer regfile
              fp_op_group = NONCOMP;
              check_fprm  = 1'b0; // instruction encoded in rm, do the check here
              // fmv.x.fmt - FPR to GPR Move
              if ((ZFINX == 0 && instr_rdata_i[14:12] == 3'b000) || (C_XF16ALT && instr_rdata_i[14:12] == 3'b100)) begin
                alu_op_b_mux_sel_o  = OP_B_REGA_OR_FWD; // set rs2 = rs1 so we can map FMV to SGNJ in the unit
                fpu_op              = cv32e40p_fpu_pkg::SGNJ; // mapped to SGNJ-passthrough since no recoding
                fpu_op_mod          = 1'b1;    // sign-extend result
                fp_rnd_mode_o       = 3'b011;  // passthrough without checking nan-box
                // FP16ALT uses special encoding here
                if (instr_rdata_i[14]) begin
                  fpu_dst_fmt_o = cv32e40p_fpu_pkg::FP16ALT;
                  fpu_src_fmt_o = cv32e40p_fpu_pkg::FP16ALT;
                end
              // fclass.fmt - FP Classify
              end else if (instr_rdata_i[14:12] == 3'b001 || (C_XF16ALT && instr_rdata_i[14:12] == 3'b101)) begin
                fpu_op        = cv32e40p_fpu_pkg::CLASSIFY;
                fp_rnd_mode_o = 3'b000;
                // FP16ALT uses special encoding here
                if (instr_rdata_i[14]) begin
                  fpu_dst_fmt_o = cv32e40p_fpu_pkg::FP16ALT;
                  fpu_src_fmt_o = cv32e40p_fpu_pkg::FP16ALT;
                end
              end else begin
                illegal_insn_o = 1'b1;
              end
              // rs2 must be zero
              if (instr_rdata_i[24:20]) illegal_insn_o = 1'b1;
            end
            // fmv.fmt.x - GPR to FPR Move
            5'b11110: begin
              regb_used_o         = 1'b0;
              reg_fp_a_o          = 1'b0; // go from integer regfile
              alu_op_b_mux_sel_o  = OP_B_REGA_OR_FWD; // set rs2 = rs1 so we can map FMV to SGNJ in the unit
              fpu_op              = cv32e40p_fpu_pkg::SGNJ; // mapped to SGNJ-passthrough since no recoding
              fpu_op_mod          = 1'b0;    // nan-box result
              fp_op_group         = NONCOMP;
              fp_rnd_mode_o       = 3'b011;  // passthrough without checking nan-box
              check_fprm          = 1'b0; // instruction encoded in rm, do the check here
              if ((ZFINX == 0 && instr_rdata_i[14:12] == 3'b000) || (C_XF16ALT && instr_rdata_i[14:12] == 3'b100)) begin
                // FP16ALT uses special encoding here
                if (instr_rdata_i[14]) begin
                  fpu_dst_fmt_o = cv32e40p_fpu_pkg::FP16ALT;
                  fpu_src_fmt_o = cv32e40p_fpu_pkg::FP16ALT;
                end
              end else begin
                illegal_insn_o = 1'b1;
              end
              // rs2 must be zero
              if (instr_rdata_i[24:20] != 5'b00000) illegal_insn_o = 1'b1;
            end
            // Rest are illegal instructions
            default: illegal_insn_o = 1'b1;
          endcase

          // check enabled formats (static)
          if (~C_RVF && fpu_dst_fmt_o == cv32e40p_fpu_pkg::FP32) illegal_insn_o = 1'b1;
          if ((~C_RVD) && fpu_dst_fmt_o == cv32e40p_fpu_pkg::FP64) illegal_insn_o = 1'b1;
          if ((~C_XF16) && fpu_dst_fmt_o == cv32e40p_fpu_pkg::FP16) illegal_insn_o = 1'b1;
          if ((~C_XF16ALT) && fpu_dst_fmt_o == cv32e40p_fpu_pkg::FP16ALT) begin
            illegal_insn_o = 1'b1;
          end
          if ((~C_XF8) && fpu_dst_fmt_o == cv32e40p_fpu_pkg::FP8) illegal_insn_o = 1'b1;

          // check rounding mode
          if (check_fprm) begin
            unique case (instr_rdata_i[14:12]) inside
              3'b000, 3'b001, 3'b010, 3'b011, 3'b100: ; //legal rounding modes
              3'b101: begin      // Alternative Half-Precsision encded as fmt=10 and rm=101
                if (~C_XF16ALT || fpu_dst_fmt_o != cv32e40p_fpu_pkg::FP16ALT) illegal_insn_o = 1'b1;
                // actual rounding mode from frm csr
                unique case (frm_i) inside
                  3'b000, 3'b001, 3'b010, 3'b011, 3'b100 : fp_rnd_mode_o = frm_i; //legal rounding modes
                  default                                : illegal_insn_o = 1'b1;
                endcase
              end
              3'b111: begin
                // rounding mode from frm csr
                unique case (frm_i) inside
                  3'b000, 3'b001, 3'b010, 3'b011, 3'b100 : fp_rnd_mode_o = frm_i; //legal rounding modes
                  default                                : illegal_insn_o = 1'b1;
                endcase
              end
              default : illegal_insn_o = 1'b1;
            endcase
          end

          // Set latencies for FPnew from config. The C_LAT constants contain the number
          // of pipeline registers. the APU takes the following values:
          // 1 = single cycle (no latency), 2 = one pipestage, 3 = two or more pipestages
          case (fp_op_group)
            // ADDMUL has format dependent latency
            ADDMUL : begin
              unique case (fpu_dst_fmt_o)
                cv32e40p_fpu_pkg::FP32    : apu_lat_o = (FPU_ADDMUL_LAT<2)? FPU_ADDMUL_LAT+1: 2'h3;
                cv32e40p_fpu_pkg::FP64    : apu_lat_o = (C_LAT_FP64<2)    ? C_LAT_FP64+1    : 2'h3;
                cv32e40p_fpu_pkg::FP16    : apu_lat_o = (C_LAT_FP16<2)    ? C_LAT_FP16+1    : 2'h3;
                cv32e40p_fpu_pkg::FP16ALT : apu_lat_o = (C_LAT_FP16ALT<2) ? C_LAT_FP16ALT+1 : 2'h3;
                cv32e40p_fpu_pkg::FP8     : apu_lat_o = (C_LAT_FP8<2)     ? C_LAT_FP8+1     : 2'h3;
                default : ;
              endcase
            end
            // DIVSQRT is iterative and takes more than 2 cycles
            DIVSQRT : apu_lat_o = 2'h3;
            // NONCOMP uses the same latency for all formats
            NONCOMP : apu_lat_o = (FPU_OTHERS_LAT<2) ? FPU_OTHERS_LAT+1 : 2'h3;
            // CONV uses the same latency for all formats
            CONV    : apu_lat_o = (FPU_OTHERS_LAT<2) ? FPU_OTHERS_LAT+1 : 2'h3;
            default: ;
          endcase

          // Set FPnew OP and OPMOD as the APU op
          apu_op_o = {fpu_vec_op, fpu_op_mod, fpu_op};

        // No FPU or (ZFINX == 0 && MSTATUS.FS == FS_OFF)
        end else begin
          illegal_insn_o = 1'b1;
        end
      end

      // Floating Point fused arithmetic
      OPCODE_OP_FMADD,
      OPCODE_OP_FMSUB,
      OPCODE_OP_FNMSUB,
      OPCODE_OP_FNMADD : begin
        if (FPU == 1 && (ZFINX == 1 || fs_off_i == 1'b0)) begin
          // using APU instead of ALU
          alu_en        = 1'b0;
          apu_en        = 1'b1;
          // all registers are FP registers and use three
          rega_used_o   = 1'b1;
          regb_used_o   = 1'b1;
          regc_used_o   = 1'b1;
          regc_mux_o    = REGC_S4;
          if (ZFINX == 0) begin
            reg_fp_a_o  = 1'b1;
            reg_fp_b_o  = 1'b1;
            reg_fp_c_o  = 1'b1;
            reg_fp_d_o  = 1'b1;
          end else begin
            reg_fp_a_o  = 1'b0;
            reg_fp_b_o  = 1'b0;
            reg_fp_c_o  = 1'b0;
            reg_fp_d_o  = 1'b0;
          end
          fp_rnd_mode_o = instr_rdata_i[14:12];

          // Decode Formats
          unique case (instr_rdata_i[26:25])
            // FP32
            2'b00 : fpu_dst_fmt_o = cv32e40p_fpu_pkg::FP32;
            // FP64
            2'b01 : fpu_dst_fmt_o = cv32e40p_fpu_pkg::FP64;
            // FP16 or FP16ALT
            2'b10 : begin
              // FP16alt encoded in rm field
              if (instr_rdata_i[14:12] == 3'b101) fpu_dst_fmt_o = cv32e40p_fpu_pkg::FP16ALT;
              else fpu_dst_fmt_o = cv32e40p_fpu_pkg::FP16;
            end
            // FP8
            2'b11 : fpu_dst_fmt_o = cv32e40p_fpu_pkg::FP8;
          endcase

          // By default, src=dst
          fpu_src_fmt_o = fpu_dst_fmt_o;

          // decode FP intstruction
          unique case (instr_rdata_i[6:0])
            // fmadd.fmt - FP Fused multiply-add
            OPCODE_OP_FMADD : begin
              fpu_op     = cv32e40p_fpu_pkg::FMADD;
            end
            // fmsub.fmt - FP Fused multiply-subtract
            OPCODE_OP_FMSUB : begin
              fpu_op     = cv32e40p_fpu_pkg::FMADD;
              fpu_op_mod = 1'b1;
            end
            // fnmsub.fmt - FP Negated fused multiply-subtract
            OPCODE_OP_FNMSUB : begin
              fpu_op     = cv32e40p_fpu_pkg::FNMSUB;
            end
            // fnmadd.fmt - FP Negated fused multiply-add
            OPCODE_OP_FNMADD : begin
              fpu_op     = cv32e40p_fpu_pkg::FNMSUB;
              fpu_op_mod = 1'b1;
            end
            default : ;
          endcase

          // check enabled formats (static)
          if (~C_RVF && fpu_dst_fmt_o == cv32e40p_fpu_pkg::FP32) illegal_insn_o = 1'b1;
          if ((~C_RVD) && fpu_dst_fmt_o == cv32e40p_fpu_pkg::FP64) illegal_insn_o = 1'b1;
          if ((~C_XF16) && fpu_dst_fmt_o == cv32e40p_fpu_pkg::FP16) illegal_insn_o = 1'b1;
          if ((~C_XF16ALT) && fpu_dst_fmt_o == cv32e40p_fpu_pkg::FP16ALT) begin
            illegal_insn_o = 1'b1;
          end
          if ((~C_XF8) && fpu_dst_fmt_o == cv32e40p_fpu_pkg::FP8) illegal_insn_o = 1'b1;

          // check rounding mode
          unique case (instr_rdata_i[14:12]) inside
            3'b000, 3'b001, 3'b010, 3'b011, 3'b100: ; //legal rounding modes
            3'b101: begin      // Alternative Half-Precsision encded as fmt=10 and rm=101
              if (~C_XF16ALT || fpu_dst_fmt_o != cv32e40p_fpu_pkg::FP16ALT) illegal_insn_o = 1'b1;
              // actual rounding mode from frm csr
              unique case (frm_i) inside
                3'b000, 3'b001, 3'b010, 3'b011, 3'b100 : fp_rnd_mode_o = frm_i; //legal rounding modes
                default         : illegal_insn_o = 1'b1;
              endcase
            end
            3'b111: begin
              // rounding mode from frm csr
              unique case (frm_i) inside
                3'b000, 3'b001, 3'b010, 3'b011, 3'b100 : fp_rnd_mode_o = frm_i; //legal rounding modes
                default         : illegal_insn_o = 1'b1;
              endcase
            end
            default : illegal_insn_o = 1'b1;
          endcase

          // Set latencies for FPnew from config. The C_LAT constants contain the number
          // of pipeline registers. the APU takes the following values:
          // 1 = single cycle (no latency), 2 = one pipestage, 3 = two or more pipestages
          // format dependent latency
          unique case (fpu_dst_fmt_o)
            cv32e40p_fpu_pkg::FP32    : apu_lat_o = (FPU_ADDMUL_LAT<2)? FPU_ADDMUL_LAT+1: 2'h3;
            cv32e40p_fpu_pkg::FP64    : apu_lat_o = (C_LAT_FP64<2)    ? C_LAT_FP64+1    : 2'h3;
            cv32e40p_fpu_pkg::FP16    : apu_lat_o = (C_LAT_FP16<2)    ? C_LAT_FP16+1    : 2'h3;
            cv32e40p_fpu_pkg::FP16ALT : apu_lat_o = (C_LAT_FP16ALT<2) ? C_LAT_FP16ALT+1 : 2'h3;
            cv32e40p_fpu_pkg::FP8     : apu_lat_o = (C_LAT_FP8<2)     ? C_LAT_FP8+1     : 2'h3;
            default : ;
          endcase

          // Set FPnew OP and OPMOD as the APU op
          apu_op_o = {fpu_vec_op, fpu_op_mod, fpu_op};

        // No FPU or (ZFINX == 0 && MSTATUS.FS == FS_OFF)
        end else begin
          illegal_insn_o = 1'b1;
        end
      end

      OPCODE_STORE_FP: begin
        if (FPU == 1 && ZFINX == 0 && fs_off_i == 1'b0) begin
          data_req            = 1'b1;
          data_we_o           = 1'b1;
          rega_used_o         = 1'b1;
          regb_used_o         = 1'b1;
          alu_operator_o      = ALU_ADD;
          reg_fp_b_o          = 1'b1;

          // offset from immediate
          imm_b_mux_sel_o     = IMMB_S;
          alu_op_b_mux_sel_o  = OP_B_IMM;

          // pass write data through ALU operand c
          alu_op_c_mux_sel_o = OP_C_REGB_OR_FWD;

          // Decode data type
          unique case (instr_rdata_i[14:12])
            // fsb - FP8 store
            3'b000 : if (C_XF8) data_type_o = 2'b10;
                     else illegal_insn_o = 1'b1;
            // fsh - FP16 store
            3'b001 : if (C_XF16 | C_XF16ALT) data_type_o = 2'b01;
                     else illegal_insn_o = 1'b1;
            // fsw - FP32 store
            3'b010 : if (C_RVF) data_type_o = 2'b00;
                     else illegal_insn_o = 1'b1;
            // fsd - FP64 store
            3'b011 : if (C_RVD) data_type_o = 2'b00; // 64bit stores unsupported!
                     else illegal_insn_o = 1'b1;
            default: illegal_insn_o = 1'b1;
          endcase

          // sanitize memory bus signals for illegal instr (not sure if needed??)
          if (illegal_insn_o) begin
            data_req       = 1'b0;
            data_we_o      = 1'b0;
          end
        // No FPU or ZFINX or MSTATUS.FS == FS_OFF
        end else begin
          illegal_insn_o = 1'b1;
        end
      end

      OPCODE_LOAD_FP: begin
        if (FPU == 1 && ZFINX == 0 && fs_off_i == 1'b0) begin
          data_req            = 1'b1;
          regfile_mem_we      = 1'b1;
          reg_fp_d_o          = 1'b1;
          rega_used_o         = 1'b1;
          alu_operator_o      = ALU_ADD;

          // offset from immediate
          imm_b_mux_sel_o     = IMMB_I;
          alu_op_b_mux_sel_o  = OP_B_IMM;

          // NaN boxing
          data_sign_extension_o = 2'b10;

          // Decode data type
          unique case (instr_rdata_i[14:12])
            // flb - FP8 load
            3'b000 : if (C_XF8) data_type_o = 2'b10;
                     else illegal_insn_o = 1'b1;
            // flh - FP16 load
            3'b001 : if (C_XF16 | C_XF16ALT) data_type_o = 2'b01;
                     else illegal_insn_o = 1'b1;
            // flw - FP32 load
            3'b010 : if (C_RVF) data_type_o = 2'b00;
                     else illegal_insn_o = 1'b1;
            // fld - FP64 load
            3'b011 : if (C_RVD) data_type_o = 2'b00; // 64bit loads unsupported!
                     else illegal_insn_o = 1'b1;
            default: illegal_insn_o = 1'b1;
          endcase
        // No FPU or ZFINX or MSTATUS.FS == FS_OFF
        end else begin
          illegal_insn_o = 1'b1;
        end
      end

      OPCODE_CUSTOM_0: begin
        if (COREV_PULP && instr_rdata_i[14:13] != 2'b11) begin // cv.l[bhw][u] and cv.elw
          data_req           = 1'b1;
          regfile_mem_we     = 1'b1;
          rega_used_o        = 1'b1;
          alu_operator_o     = ALU_ADD;
          // offset from immediate
          alu_op_b_mux_sel_o = OP_B_IMM;
          imm_b_mux_sel_o    = IMMB_I;

          // post-increment setup
          if (instr_rdata_i[13:12] != 2'b11) begin
            prepost_useincr_o       = 1'b0;
            regfile_alu_waddr_sel_o = 1'b0;
            regfile_alu_we          = 1'b1;
          end

          // sign/zero extension
          data_sign_extension_o = {1'b0,~instr_rdata_i[14]};

          // load size
          unique case (instr_rdata_i[13:12])
            2'b00  : data_type_o = 2'b10; // LB/LBU
            2'b01  : data_type_o = 2'b01; // LH/LHU
            default: data_type_o = 2'b00; // LW/ELW
          endcase

          // special cv.elw (event load)
          if (instr_rdata_i[13:12] == 2'b11) begin
            if (COREV_CLUSTER) begin
              data_load_event_o = 1'b1;
            end else begin
              // cv.elw only valid for COREV_CLUSTER = 1
              illegal_insn_o    = 1'b1;
            end
          end
        end else if (COREV_PULP) begin   // cv.beqimm and cv.bneimm 
          ctrl_transfer_target_mux_sel_o = JT_COND;
          ctrl_transfer_insn             = BRANCH_COND;
          alu_op_c_mux_sel_o             = OP_C_JT;
          rega_used_o                    = 1'b1;
          // offset from immediate
          alu_op_b_mux_sel_o             = OP_B_IMM;
          imm_b_mux_sel_o                = IMMB_BI;

          if (instr_rdata_i[12] == 1'b0) begin // cv.beqimm
            alu_operator_o      = ALU_EQ;
          end else begin                       // cv.bneimm
            alu_operator_o      = ALU_NE;
          end
        end else begin
          illegal_insn_o = 1'b1;
        end
      end

      OPCODE_CUSTOM_1: begin
        if (COREV_PULP) begin
          unique case (instr_rdata_i[14:12])
            3'b000, 3'b001, 3'b010: begin  // Immediate Post-Incremented Store
              data_req                = 1'b1;
              data_we_o               = 1'b1;
              rega_used_o             = 1'b1;
              regb_used_o             = 1'b1;
              alu_operator_o          = ALU_ADD;
              // pass write data through ALU operand c
              alu_op_c_mux_sel_o      = OP_C_REGB_OR_FWD;
              // offset from immediate
              imm_b_mux_sel_o         = IMMB_S;
              alu_op_b_mux_sel_o      = OP_B_IMM;

              // post-increment setup
              prepost_useincr_o       = 1'b0;
              regfile_alu_waddr_sel_o = 1'b0;
              regfile_alu_we          = 1'b1;

              // store size
              unique case (instr_rdata_i[13:12])
                2'b00  : data_type_o = 2'b10; // SB
                2'b01  : data_type_o = 2'b01; // SH
                default: data_type_o = 2'b00; // SW
              endcase
            end

            3'b011 : begin // Plane A
              unique case (instr_rdata_i[31:25])
                7'b0000000, 7'b0000001, 7'b0000010, 7'b0000011,         // Register Post-Incremented          Load
                7'b0000100, 7'b0000101, 7'b0000110, 7'b0000111,         // Register Indexed                   Load
                7'b0001000, 7'b0001001, 7'b0001010, 7'b0001011,         // Register Post-Incremented Unsigned Load
                7'b0001100, 7'b0001101, 7'b0001110, 7'b0001111: begin   // Register Indexed          Unsigned Load
                  data_req           = 1'b1;
                  regfile_mem_we     = 1'b1;
                  rega_used_o        = 1'b1;
                  alu_operator_o     = ALU_ADD;
                  // offset from RS2
                  regb_used_o        = 1'b1;
                  alu_op_b_mux_sel_o = OP_B_REGB_OR_FWD;

                  // post-increment setup
                  if (instr_rdata_i[27] == 1'b0) begin
                    prepost_useincr_o       = 1'b0;
                    regfile_alu_waddr_sel_o = 1'b0;
                    regfile_alu_we          = 1'b1;
                  end

                  // sign/zero extension
                  data_sign_extension_o = {1'b0,~instr_rdata_i[28]};

                  // load size
                  unique case ({instr_rdata_i[28],instr_rdata_i[26:25]})
                    3'b000 : data_type_o = 2'b10; // LB
                    3'b001 : data_type_o = 2'b01; // LH
                    3'b010 : data_type_o = 2'b00; // LW
                    3'b100 : data_type_o = 2'b10; // LBU
                    3'b101 : data_type_o = 2'b01; // LHU
                    default: begin
                      illegal_insn_o = 1'b1;
                      data_req       = 1'b0;
                      regfile_mem_we = 1'b0;
                      regfile_alu_we = 1'b0;
                    end
                  endcase
                end

                7'b0010000, 7'b0010001, 7'b0010010, 7'b0010011,         // Register Post-Incremented Store
                7'b0010100, 7'b0010101, 7'b0010110, 7'b0010111: begin   // Register Indexed          Store
                  data_req           = 1'b1;
                  data_we_o          = 1'b1;
                  rega_used_o        = 1'b1;
                  regb_used_o        = 1'b1;
                  alu_operator_o     = ALU_ADD;
                  // pass write data through ALU operand c
                  alu_op_c_mux_sel_o = OP_C_REGB_OR_FWD;
                  // offset from register
                  regc_used_o        = 1'b1;
                  alu_op_b_mux_sel_o = OP_B_REGC_OR_FWD;
                  regc_mux_o         = REGC_RD;

                  // post-increment setup
                  if (instr_rdata_i[27] == 1'b0) begin
                    prepost_useincr_o       = 1'b0;
                    regfile_alu_waddr_sel_o = 1'b0;
                    regfile_alu_we          = 1'b1;
                  end

                  // store size
                  unique case (instr_rdata_i[26:25])
                    2'b00  : data_type_o = 2'b10; // SB
                    2'b01  : data_type_o = 2'b01; // SH
                    2'b10  : data_type_o = 2'b00; // SW
                    default: begin
                      illegal_insn_o = 1'b1;
                      data_req       = 1'b0;
                      data_we_o      = 1'b0;
                      data_type_o    = 2'b00;
                    end
                  endcase
                end

                7'b0011000, 7'b0011001, 7'b0011010, 7'b0011011,
                7'b0011100, 7'b0011101, 7'b0011110, 7'b0011111: begin   // Register Bit-Manipulation
                  regfile_alu_we        = 1'b1;
                  rega_used_o           = 1'b1;
                  regb_used_o           = 1'b1;

                  bmask_a_mux_o         = BMASK_A_S3;
                  bmask_b_mux_o         = BMASK_B_S2;
                  alu_op_b_mux_sel_o    = OP_B_IMM;
                  alu_bmask_a_mux_sel_o = BMASK_A_REG;

                  unique case (instr_rdata_i[27:25])
                    3'b000: begin                                      // cv.extractr
                      alu_operator_o        = ALU_BEXT;
                      imm_b_mux_sel_o       = IMMB_S2;
                      bmask_b_mux_o         = BMASK_B_ZERO;
                      alu_op_b_mux_sel_o    = OP_B_BMASK;
                    end
                    3'b001: begin                                      // cv.extractur
                      alu_operator_o        = ALU_BEXTU;
                      imm_b_mux_sel_o       = IMMB_S2;
                      bmask_b_mux_o         = BMASK_B_ZERO;
                      alu_op_b_mux_sel_o    = OP_B_BMASK;
                    end
                    3'b010: begin                                      // cv.insertr
                      alu_operator_o        = ALU_BINS;
                      imm_b_mux_sel_o       = IMMB_S2;
                      regc_used_o           = 1'b1;
                      regc_mux_o            = REGC_RD;
                      alu_op_b_mux_sel_o    = OP_B_BMASK;
                      alu_bmask_b_mux_sel_o = BMASK_B_REG;
                    end
                    3'b100: begin                                      // cv.bclrr
                      alu_operator_o        = ALU_BCLR;
                      alu_bmask_b_mux_sel_o = BMASK_B_REG;
                    end
                    3'b101: begin                                      // cv.bsetr
                      alu_operator_o        = ALU_BSET;
                      alu_bmask_b_mux_sel_o = BMASK_B_REG;
                    end
                    default: illegal_insn_o = 1'b1;
                  endcase
                end

                7'b0100000, 7'b0100001, 7'b0100010, 7'b0100011,
                7'b0100100, 7'b0100101, 7'b0100110, 7'b0100111,
                7'b0101000, 7'b0101001, 7'b0101010, 7'b0101011,
                7'b0101100, 7'b0101101, 7'b0101110, 7'b0101111,
                7'b0110000, 7'b0110001, 7'b0110010, 7'b0110011,
                7'b0110100, 7'b0110101, 7'b0110110, 7'b0110111,
                7'b0111000, 7'b0111001, 7'b0111010, 7'b0111011,
                7'b0111100, 7'b0111101, 7'b0111110, 7'b0111111: begin  // General ALU
                  regfile_alu_we = 1'b1;
                  rega_used_o    = 1'b1;
                  regb_used_o    = 1'b1;

                  unique case (instr_rdata_i[29:25])
                    5'b00000: alu_operator_o = ALU_ROR;                // cv.ror
                    5'b00001: begin                                    // cv.ff1
                      regb_used_o    = 1'b0;
                      alu_operator_o = ALU_FF1;
                      if (instr_rdata_i[24:20] != 5'b0) begin
                        illegal_insn_o = 1'b1;
                      end
                    end
                    5'b00010: begin                                    // cv.fl1
                      regb_used_o    = 1'b0;
                      alu_operator_o = ALU_FL1;
                      if (instr_rdata_i[24:20] != 5'b0) begin
                        illegal_insn_o = 1'b1;
                      end
                    end
                    5'b00011: begin                                    // cv.clb
                      regb_used_o    = 1'b0;
                      alu_operator_o = ALU_CLB;
                      if (instr_rdata_i[24:20] != 5'b0) begin
                        illegal_insn_o = 1'b1;
                      end
                    end
                    5'b00100: begin                                    // cv.cnt
                      regb_used_o    = 1'b0;
                      alu_operator_o = ALU_CNT;
                      if (instr_rdata_i[24:20] != 5'b0) begin
                        illegal_insn_o = 1'b1;
                      end
                    end
                    5'b01000: begin                                    // cv.abs
                      alu_operator_o = ALU_ABS;
                      if (instr_rdata_i[24:20] != 5'b0) begin
                        illegal_insn_o = 1'b1;
                      end
                    end
                    5'b01001: alu_operator_o = ALU_SLETS;              // cv.slet
                    5'b01010: alu_operator_o = ALU_SLETU;              // cv.sletu
                    5'b01011: alu_operator_o = ALU_MIN;                // cv.min
                    5'b01100: alu_operator_o = ALU_MINU;               // cv.minu
                    5'b01101: alu_operator_o = ALU_MAX;                // cv.max
                    5'b01110: alu_operator_o = ALU_MAXU;               // cv.maxu
                    5'b10000: begin                                    // cv.exths
                      regb_used_o    = 1'b0;
                      alu_operator_o = ALU_EXTS;
                      alu_vec_mode_o = VEC_MODE16;
                      if (instr_rdata_i[24:20] != 5'b0) begin
                        illegal_insn_o = 1'b1;
                      end
                    end
                    5'b10001: begin                                    // cv.exthz
                      regb_used_o    = 1'b0;
                      alu_operator_o = ALU_EXT;
                      alu_vec_mode_o = VEC_MODE16;
                      if (instr_rdata_i[24:20] != 5'b0) begin
                        illegal_insn_o = 1'b1;
                      end
                    end
                    5'b10010: begin                                    // cv.extbs
                      regb_used_o    = 1'b0;
                      alu_operator_o = ALU_EXTS;
                      alu_vec_mode_o = VEC_MODE8;
                      if (instr_rdata_i[24:20] != 5'b0) begin
                        illegal_insn_o = 1'b1;
                      end
                    end
                    5'b10011: begin                                    // cv.extbz
                      regb_used_o    = 1'b0;
                      alu_operator_o = ALU_EXT;
                      alu_vec_mode_o = VEC_MODE8;
                      if (instr_rdata_i[24:20] != 5'b0) begin
                        illegal_insn_o = 1'b1;
                      end
                    end
                    5'b11000: begin                                    // cv.clip
                      regb_used_o        = 1'b0;
                      alu_operator_o     = ALU_CLIP;
                      alu_op_b_mux_sel_o = OP_B_IMM;
                      imm_b_mux_sel_o    = IMMB_CLIP;
                    end
                    5'b11001: begin                                    // cv.clipu
                      regb_used_o        = 1'b0;
                      alu_operator_o     = ALU_CLIPU;
                      alu_op_b_mux_sel_o = OP_B_IMM;
                      imm_b_mux_sel_o    = IMMB_CLIP;
                    end
                    5'b11010: alu_operator_o = ALU_CLIP;               // cv.clipr
                    5'b11011: alu_operator_o = ALU_CLIPU;              // cv.clipur
                    default : illegal_insn_o = 1'b1;
                  endcase
                end

                7'b1000000, 7'b1000001, 7'b1000010, 7'b1000011,
                7'b1000100, 7'b1000101, 7'b1000110, 7'b1000111: begin  // Add/Sub with Normalization and Rounding
                  regfile_alu_we        = 1'b1;
                  rega_used_o           = 1'b1;
                  regb_used_o           = 1'b1;
                  regc_used_o           = 1'b1;
                  regc_mux_o            = REGC_RD;
                  bmask_a_mux_o         = BMASK_A_ZERO;
                  bmask_b_mux_o         = BMASK_B_S3;
                  alu_bmask_b_mux_sel_o = BMASK_B_REG;
                  alu_op_a_mux_sel_o    = OP_A_REGC_OR_FWD;
                  alu_op_b_mux_sel_o    = OP_B_REGA_OR_FWD;

                  unique case (instr_rdata_i[27:25])
                    3'b001:  alu_operator_o = ALU_ADDU;                 // cv.adduNr
                    3'b010:  alu_operator_o = ALU_ADDR;                 // cv.addRNr
                    3'b011:  alu_operator_o = ALU_ADDUR;                // cv.adduRNr
                    3'b100:  alu_operator_o = ALU_SUB;                  // cv.subNr
                    3'b101:  alu_operator_o = ALU_SUBU;                 // cv.subuNr
                    3'b110:  alu_operator_o = ALU_SUBR;                 // cv.subRNr
                    3'b111:  alu_operator_o = ALU_SUBUR;                // cv.subuRNr
                    default: alu_operator_o = ALU_ADD;                  // cv.addNr
                  endcase
                end

                7'b1001000, 7'b1001001: begin
                  alu_en          = 1'b0;
                  mult_int_en     = 1'b1;
                  regfile_alu_we  = 1'b1;
                  rega_used_o     = 1'b1;
                  regb_used_o     = 1'b1;
                  regc_used_o     = 1'b1;
                  regc_mux_o      = REGC_RD;

                  if (instr_rdata_i[25] == 1'b0) begin
                    mult_operator_o = MUL_MAC32;                       // cv.mac
                  end else begin
                    mult_operator_o = MUL_MSU32;                       // cv.msu
                  end
                end

                default: illegal_insn_o = 1'b1;
              endcase
            end // Plane A

            ///////////////////////////////////////////////
            //  _   ___        ___     ___   ___  ____   //
            // | | | \ \      / / |   / _ \ / _ \|  _ \  //
            // | |_| |\ \ /\ / /| |  | | | | | | | |_) | //
            // |  _  | \ V  V / | |__| |_| | |_| |  __/  //
            // |_| |_|  \_/\_/  |_____\___/ \___/|_|     //
            //                                           //
            ///////////////////////////////////////////////
            3'b100 : begin // Plane B
              hwlp_target_mux_sel_o = 2'b0;

              unique case (instr_rdata_i[11:8])
                4'b0000: begin
                  // lp.starti: set start address to PC + I-type immediate
                  hwlp_we[0]           = 1'b1;
                  hwlp_start_mux_sel_o = 2'b0;
                  if (instr_rdata_i[19:15] != 5'b0) begin
                    illegal_insn_o = 1'b1;
                  end
                end
                4'b0001: begin
                  // lp.start: set start address to rs1 content
                  hwlp_we[0]           = 1'b1;
                  hwlp_start_mux_sel_o = 2'b10;
                  rega_used_o          = 1'b1;
                  if (instr_rdata_i[31:20] != 12'b0) begin
                    illegal_insn_o = 1'b1;
                  end
                end
                4'b0010: begin
                  // lp.endi: set end address to PC + I-type immediate - 4
                  hwlp_we[1] = 1'b1;
                  if (instr_rdata_i[19:15] != 5'b0) begin
                    illegal_insn_o = 1'b1;
                  end
                end
                4'b0011: begin
                  // lp.end: set end address to (rs1 - 4) content
                  hwlp_we[1]            = 1'b1;
                  hwlp_target_mux_sel_o = 2'b10;
                  rega_used_o           = 1'b1;
                  if (instr_rdata_i[31:20] != 12'b0) begin
                    illegal_insn_o = 1'b1;
                  end
                end
                4'b0100: begin
                  // lp.counti: initialize counter from I-type immediate
                  hwlp_we[2]         = 1'b1;
                  hwlp_cnt_mux_sel_o = 1'b0;
                  if (instr_rdata_i[19:15] != 5'b0) begin
                    illegal_insn_o = 1'b1;
                  end
                end
                4'b0101: begin
                  // lp.count: initialize counter from rs1
                  hwlp_we[2]         = 1'b1;
                  hwlp_cnt_mux_sel_o = 1'b1;
                  rega_used_o        = 1'b1;
                  if (instr_rdata_i[31:20] != 12'b0) begin
                    illegal_insn_o = 1'b1;
                  end
                end
                4'b0110: begin
                  // lp.setupi: initialize counter from immediate, set start address to
                  // next instruction and end address to PC + I-type immediate - 4
                  hwlp_we               = 3'b111;
                  hwlp_target_mux_sel_o = 2'b01;
                  hwlp_start_mux_sel_o  = 2'b01;
                  hwlp_cnt_mux_sel_o    = 1'b0;
                end
                4'b0111: begin
                  // lp.setup: initialize counter from rs1, set start address to
                  // next instruction and end address to PC + I-type immediate - 4
                  hwlp_we              = 3'b111;
                  hwlp_start_mux_sel_o = 2'b01;
                  hwlp_cnt_mux_sel_o   = 1'b1;
                  rega_used_o          = 1'b1;
                end
                default: begin
                  illegal_insn_o = 1'b1;
                end
              endcase
            end // Plane B

            default: illegal_insn_o = 1'b1;
          endcase

        end else begin
          illegal_insn_o = 1'b1;
        end
      end

      OPCODE_CUSTOM_2: begin  // PULP specific ALU instructions with two source operands and one immediate
        if (COREV_PULP) begin
          regfile_alu_we = 1'b1;
          rega_used_o    = 1'b1;
          regb_used_o    = 1'b1;

          unique case (instr_rdata_i[14:13])
            2'b00: begin
              // Bit Manipulation instructions
              regb_used_o         = 1'b0;
              bmask_a_mux_o       = BMASK_A_S3;
              bmask_b_mux_o       = BMASK_B_S2;
              alu_op_b_mux_sel_o  = OP_B_IMM;
     
              unique case ({instr_rdata_i[31:30], instr_rdata_i[12]})
                {2'b00, 1'b0}: begin                                       // cv.extract
                  alu_operator_o  = ALU_BEXT;
                  imm_b_mux_sel_o = IMMB_S2;
                  bmask_b_mux_o   = BMASK_B_ZERO;
                end
                {2'b01, 1'b0}: begin                                       // cv.extractu
                  alu_operator_o  = ALU_BEXTU;
                  imm_b_mux_sel_o = IMMB_S2;
                  bmask_b_mux_o   = BMASK_B_ZERO;
                end
                {2'b10, 1'b0}: begin                                       // cv.insert
                  alu_operator_o  = ALU_BINS;
                  imm_b_mux_sel_o = IMMB_S2;
                  regc_used_o     = 1'b1;
                  regc_mux_o      = REGC_RD;
                end
                {2'b00, 1'b1}: begin                                       // cv.bclr
                  alu_operator_o = ALU_BCLR;
                end
                {2'b01, 1'b1}: begin                                       // cv.bset
                  alu_operator_o = ALU_BSET;
                end
                {2'b11, 1'b1}: begin                                       // cv.bitrev
                  alu_operator_o        = ALU_BREV;
                  // Enable write back to RD
                  regc_used_o           = 1'b1;
                  regc_mux_o            = REGC_RD;
                  // Extract the source register on operand a
                  imm_b_mux_sel_o       = IMMB_S2;
                  // Map the radix to bmask_a immediate
                  alu_bmask_a_mux_sel_o = BMASK_A_IMM;
                  if (instr_rdata_i[29:27] != 3'b0) begin
                    illegal_insn_o = 1'b1;
                  end
                end
                default: illegal_insn_o = 1'b1;
              endcase
            end

            2'b01: begin
              // ADD/SUB with normalization and rounding
              bmask_a_mux_o  = BMASK_A_ZERO;
              bmask_b_mux_o  = BMASK_B_S3;

              // decide between using unsigned and rounding, and combinations
              unique case ({instr_rdata_i[31:30], instr_rdata_i[12]})
                {2'b01, 1'b0}: alu_operator_o = ALU_ADDU;                  // cv.adduN
                {2'b10, 1'b0}: alu_operator_o = ALU_ADDR;                  // cv.addRN
                {2'b11, 1'b0}: alu_operator_o = ALU_ADDUR;                 // cv.adduRN
                {2'b00, 1'b1}: alu_operator_o = ALU_SUB;                   // cv.subN
                {2'b01, 1'b1}: alu_operator_o = ALU_SUBU;                  // cv.subuN
                {2'b10, 1'b1}: alu_operator_o = ALU_SUBR;                  // cv.subRN
                {2'b11, 1'b1}: alu_operator_o = ALU_SUBUR;                 // cv.subuRN
                default      : alu_operator_o = ALU_ADD;                   // cv.addN
              endcase

            end

            default: begin
              // MUL/MAC with subword selection
              alu_en             = 1'b0;
              mult_int_en        = 1'b1;

              mult_imm_mux_o     = MIMM_S3;
              mult_sel_subword_o = instr_rdata_i[30];                      // cv.mulhhsN, cv.mulhhsRN, cv.mulhhuN, cv.mulhhuRN
                                                                           // cv.machhsN, cv.machhsRN, cv.machhuN, cv.machhuRN
              mult_signed_mode_o = {2{~instr_rdata_i[12]}};                // cv.mulsN,   cv.mulhhsN,  cv.mulsRN,  cv.mulhhsRN
                                                                           // cv.macsN,   cv.machhsN,  cv.macsRN,  cv.machhsRN

              if (instr_rdata_i[13]) begin                                 // cv.macsN,   cv.machhsN,  cv.macsRN,  cv.machhsRN
                                                                           // cv.macuN,   cv.machhuN,  cv.macuRN,  cv.machhuRN
                regc_used_o = 1'b1;
                regc_mux_o  = REGC_RD;
              end else begin                                               // cv.mulsN,   cv.mulhhsN,  cv.mulsRN,  cv.mulhhsRN
                                                                           // cv.muluN,   cv.mulhhuN,  cv.muluRN,  cv.mulhhuRN
                regc_mux_o  = REGC_ZERO;
              end

              if (instr_rdata_i[31]) begin                                 // cv.mulsRN,  cv.mulhhsRN, cv.muluRN,  cv.mulhhuRN
                                                                           // cv.macsRN,  cv.machhsRN, cv.macuRN,  cv.machhuRN
                mult_operator_o = MUL_IR;
              end else begin                                               // cv.mulsN,   cv.mulhhsN,  cv.muluN,   cv.mulhhuN
                                                                           // cv.macsN,   cv.machhsN,  cv.macuN,   cv.machhuN
                mult_operator_o = MUL_I;
              end
            end
          endcase
        end else begin
          illegal_insn_o = 1'b1;
        end
      end

      OPCODE_CUSTOM_3: begin
        if (COREV_PULP) begin
          regfile_alu_we      = 1'b1;
          rega_used_o         = 1'b1;
          imm_b_mux_sel_o     = IMMB_VS;

          alu_vec_o = 1'b1;
          // vector size
          if (instr_rdata_i[12]) begin
            alu_vec_mode_o  = VEC_MODE8;
            mult_operator_o = MUL_DOT8;
          end else begin
            alu_vec_mode_o  = VEC_MODE16;
            mult_operator_o = MUL_DOT16;
          end

          // distinguish normal vector, sc and sci modes
          if (instr_rdata_i[14]) begin
            scalar_replication_o = 1'b1;

            if (instr_rdata_i[13]) begin
              // immediate scalar replication, .sci
              alu_op_b_mux_sel_o = OP_B_IMM;
            end else begin
              // register scalar replication, .sc
              regb_used_o = 1'b1;
            end
          end else begin
            // normal register use
            regb_used_o = 1'b1;
          end

          // now decode the instruction
          unique case (instr_rdata_i[31:26])
            6'b00000_0: begin // cv.add
              alu_operator_o = ALU_ADD;
              imm_b_mux_sel_o = IMMB_VS;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b00001_0: begin // cv.sub
              alu_operator_o = ALU_SUB;
              imm_b_mux_sel_o = IMMB_VS;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b00010_0: begin // cv.avg
              alu_operator_o = ALU_ADD;
              imm_b_mux_sel_o = IMMB_VS;
              bmask_b_mux_o = BMASK_B_ONE;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b00011_0: begin // cv.avgu
             alu_operator_o = ALU_ADDU;
             imm_b_mux_sel_o = IMMB_VU;
             bmask_b_mux_o = BMASK_B_ONE;
             if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
               illegal_insn_o = 1'b1;
             end
             if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                 instr_rdata_i[25] != 1'b0) begin
               illegal_insn_o = 1'b1;
             end
            end
            6'b00100_0: begin // cv.min
             alu_operator_o = ALU_MIN;
             imm_b_mux_sel_o = IMMB_VS;
             if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
               illegal_insn_o = 1'b1;
             end
             if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                 instr_rdata_i[25] != 1'b0) begin
               illegal_insn_o = 1'b1;
             end
            end
            6'b00101_0: begin // cv.minu
              alu_operator_o = ALU_MINU;
              imm_b_mux_sel_o = IMMB_VU;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b00110_0: begin // cv.max
              alu_operator_o = ALU_MAX;
              imm_b_mux_sel_o = IMMB_VS;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b00111_0: begin // cv.maxu
              alu_operator_o = ALU_MAXU;
              imm_b_mux_sel_o = IMMB_VU;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b01000_0: begin // cv.srl
              alu_operator_o = ALU_SRL;
              imm_b_mux_sel_o = IMMB_VS;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
              // Imm6 restrictions
              if ((instr_rdata_i[14:12] == 3'b110 && instr_rdata_i[24:23] != 2'b0) ||
                  (instr_rdata_i[14:12] == 3'b111 && instr_rdata_i[24:22] != 3'b0)) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b01001_0: begin // cv.sra
              alu_operator_o = ALU_SRA;
              imm_b_mux_sel_o = IMMB_VS;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
              // Imm6 restrictions
              if ((instr_rdata_i[14:12] == 3'b110 && instr_rdata_i[24:23] != 2'b0) ||
                  (instr_rdata_i[14:12] == 3'b111 && instr_rdata_i[24:22] != 3'b0)) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b01010_0: begin // cv.sll
              alu_operator_o = ALU_SLL;
              imm_b_mux_sel_o = IMMB_VS;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
              // Imm6 restrictions
              if ((instr_rdata_i[14:12] == 3'b110 && instr_rdata_i[24:23] != 2'b0) ||
                  (instr_rdata_i[14:12] == 3'b111 && instr_rdata_i[24:22] != 3'b0)) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b01011_0: begin // cv.or
              alu_operator_o = ALU_OR;
              imm_b_mux_sel_o = IMMB_VS;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b01100_0: begin // cv.xor
              alu_operator_o = ALU_XOR;
              imm_b_mux_sel_o = IMMB_VS;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b01101_0: begin // cv.and
              alu_operator_o = ALU_AND;
              imm_b_mux_sel_o = IMMB_VS;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b01110_0: begin // cv.abs
              alu_operator_o = ALU_ABS;
              imm_b_mux_sel_o = IMMB_VS;
              if (instr_rdata_i[14:12] != 3'b000 && instr_rdata_i[14:12] != 3'b001) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[25:20] != 6'b000000) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b10000_0: begin // cv.dotup
              alu_en            = 1'b0;
              mult_dot_en       = 1'b1;
              mult_dot_signed_o = 2'b00;
              imm_b_mux_sel_o   = IMMB_VU;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b10001_0: begin // cv.dotusp
              alu_en            = 1'b0;
              mult_dot_en       = 1'b1;
              mult_dot_signed_o = 2'b01;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b10010_0: begin // cv.dotsp
              alu_en            = 1'b0;
              mult_dot_en       = 1'b1;
              mult_dot_signed_o = 2'b11;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b10011_0: begin // cv.sdotup
              alu_en            = 1'b0;
              mult_dot_en       = 1'b1;
              mult_dot_signed_o = 2'b00;
              regc_used_o       = 1'b1;
              regc_mux_o        = REGC_RD;
              imm_b_mux_sel_o   = IMMB_VU;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b10100_0: begin // cv.sdotusp
              alu_en            = 1'b0;
              mult_dot_en       = 1'b1;
              mult_dot_signed_o = 2'b01;
              regc_used_o       = 1'b1;
              regc_mux_o        = REGC_RD;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b10101_0: begin // cv.sdotsp
              alu_en            = 1'b0;
              mult_dot_en       = 1'b1;
              mult_dot_signed_o = 2'b11;
              regc_used_o       = 1'b1;
              regc_mux_o        = REGC_RD;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b10111_0: begin
              unique case (instr_rdata_i[14:13])
                2'b00: alu_operator_o = ALU_EXTS; // cv.extract
                2'b01: alu_operator_o = ALU_EXT;  // cv.extractu
                2'b10: begin                      // cv.insert
                  alu_operator_o     = ALU_INS;
                  regc_used_o        = 1'b1;
                  regc_mux_o         = REGC_RD;
                  alu_op_b_mux_sel_o = OP_B_REGC_OR_FWD;
                end
                default: illegal_insn_o = 1'b1;
              endcase
              // Imm6 restrictions
              if ((instr_rdata_i[12] == 1'b0 && instr_rdata_i[24:20] != 5'b0) ||
                  (instr_rdata_i[12] == 1'b1 && instr_rdata_i[24:21] != 4'b0)) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b11000_0: begin // cv.shuffle, cv.shuffleI0
              alu_operator_o       = ALU_SHUF;
              imm_b_mux_sel_o      = IMMB_SHUF;
              regb_used_o          = 1'b1;
              scalar_replication_o = 1'b0;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011 ||
                  instr_rdata_i[14:12] == 3'b100 || instr_rdata_i[14:12] == 3'b101) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
              // Imm6 restriction
              if (instr_rdata_i[14:12] == 3'b110 && instr_rdata_i[24:21] != 4'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b11001_0,
            6'b11010_0,
            6'b11011_0: begin // cv.shuffleI1 cv.shuffleI2 cv.shuffleI3
              alu_operator_o       = ALU_SHUF;
              imm_b_mux_sel_o      = IMMB_SHUF;
              regb_used_o          = 1'b1;
              scalar_replication_o = 1'b0;
              if (instr_rdata_i[14:12] != 3'b111) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b11100_0: begin // cv.shuffle2
              alu_operator_o       = ALU_SHUF2;
              regb_used_o          = 1'b1;
              regc_used_o          = 1'b1;
              regc_mux_o           = REGC_RD;
              scalar_replication_o = 1'b0;
              if (instr_rdata_i[14:12] != 3'b000 && instr_rdata_i[14:12] != 3'b001) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b11110_0: begin // cv.pack, cv.pack.h
              alu_operator_o = instr_rdata_i[25] ? ALU_PCKHI : ALU_PCKLO;
              regb_used_o    = 1'b1;
              if (instr_rdata_i[14:12] != 3'b000) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b11111_0: begin // cv.packhi, cv.packlo
              alu_operator_o = instr_rdata_i[25] ? ALU_PCKHI : ALU_PCKLO;
              regb_used_o    = 1'b1;
              regc_used_o    = 1'b1;
              regc_mux_o     = REGC_RD;
              if (instr_rdata_i[14:12] != 3'b001) begin
                illegal_insn_o = 1'b1;
              end
            end

            // Comparisons, always have bit 26 set
            6'b00000_1: begin // cv.cmpeq
              alu_operator_o  = ALU_EQ;
              imm_b_mux_sel_o = IMMB_VS;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b00001_1: begin // cv.cmpne
              alu_operator_o  = ALU_NE;
              imm_b_mux_sel_o = IMMB_VS;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b00010_1: begin // cv.cmpgt
              alu_operator_o  = ALU_GTS;
              imm_b_mux_sel_o = IMMB_VS;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b00011_1: begin // cv.cmpge
              alu_operator_o  = ALU_GES;
              imm_b_mux_sel_o = IMMB_VS;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b00100_1: begin // cv.cmplt
              alu_operator_o  = ALU_LTS;
              imm_b_mux_sel_o = IMMB_VS;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b00101_1: begin // cv.cmple
              alu_operator_o  = ALU_LES;
              imm_b_mux_sel_o = IMMB_VS;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b00110_1: begin // cv.cmpgtu
              alu_operator_o  = ALU_GTU;
              imm_b_mux_sel_o = IMMB_VU;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b00111_1: begin // cv.cmpgeu
              alu_operator_o  = ALU_GEU;
              imm_b_mux_sel_o = IMMB_VU;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b01000_1: begin // cv.cmpltu
              alu_operator_o  = ALU_LTU;
              imm_b_mux_sel_o = IMMB_VU;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b01001_1: begin // cv.cmpleu
              alu_operator_o  = ALU_LEU;
              imm_b_mux_sel_o = IMMB_VU;
              if (instr_rdata_i[14:12] == 3'b010 || instr_rdata_i[14:12] == 3'b011) begin
                illegal_insn_o = 1'b1;
              end
              if (instr_rdata_i[14:12] != 3'b110 && instr_rdata_i[14:12] != 3'b111 &&
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end

            /*  Complex instructions */
            6'b01010_1: begin // cv.cplxmul.{r,i}.{/,div2,div4,div8}
              alu_en               = 1'b0;
              mult_dot_en          = 1'b1;
              mult_dot_signed_o    = 2'b11;
              is_clpx_o            = 1'b1;
              regc_used_o          = 1'b1;
              regc_mux_o           = REGC_RD;
              scalar_replication_o = 1'b0;
              alu_op_b_mux_sel_o   = OP_B_REGB_OR_FWD;
              regb_used_o          = 1'b1;
              illegal_insn_o       = instr_rdata_i[12];
            end
            6'b01011_1: begin // cv.cplxconj
              alu_operator_o       = ALU_ABS;
              is_clpx_o            = 1'b1;
              scalar_replication_o = 1'b0;
              regb_used_o          = 1'b0;
              if (instr_rdata_i[14:12] != 3'b000 || instr_rdata_i[25:20] != 6'b000000) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b01100_1: begin // cv.subrotmj.{/,div2,div4,div8}
              alu_operator_o       = ALU_SUB;
              is_clpx_o            = 1'b1;
              scalar_replication_o = 1'b0;
              alu_op_b_mux_sel_o   = OP_B_REGB_OR_FWD;
              regb_used_o          = 1'b1;
              is_subrot_o          = 1'b1;
              if (instr_rdata_i[12] != 1'b0 || instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b01101_1: begin // cv.add.{div2,div4,div8}
              alu_operator_o       = ALU_ADD;
              is_clpx_o            = 1'b1;
              scalar_replication_o = 1'b0;
              alu_op_b_mux_sel_o   = OP_B_REGB_OR_FWD;
              regb_used_o          = 1'b1;
              if (instr_rdata_i[12] != 1'b0 || instr_rdata_i[14:12] == 3'b000 ||
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end
            6'b01110_1: begin // cv.sub.{div2,div4,div8}
              alu_operator_o       = ALU_SUB;
              is_clpx_o            = 1'b1;
              scalar_replication_o = 1'b0;
              alu_op_b_mux_sel_o   = OP_B_REGB_OR_FWD;
              regb_used_o          = 1'b1;
              if (instr_rdata_i[12] != 1'b0 || instr_rdata_i[14:12] == 3'b000 ||
                  instr_rdata_i[25] != 1'b0) begin
                illegal_insn_o = 1'b1;
              end
            end

            default: illegal_insn_o = 1'b1;
          endcase
        end else begin
          illegal_insn_o = 1'b1;
        end
      end

      ////////////////////////////////////////////////
      //  ____  ____  _____ ____ ___    _    _      //
      // / ___||  _ \| ____/ ___|_ _|  / \  | |     //
      // \___ \| |_) |  _|| |    | |  / _ \ | |     //
      //  ___) |  __/| |__| |___ | | / ___ \| |___  //
      // |____/|_|   |_____\____|___/_/   \_\_____| //
      //                                            //
      ////////////////////////////////////////////////

      OPCODE_FENCE: begin
        unique case (instr_rdata_i[14:12])
          3'b000: begin // FENCE (FENCE.I instead, a bit more conservative)
            // flush pipeline
            fencei_insn_o = 1'b1;
          end

          3'b001: begin // FENCE.I
            // flush prefetch buffer, flush pipeline
            fencei_insn_o = 1'b1;
          end

          default: illegal_insn_o =  1'b1;
        endcase
      end

      OPCODE_SYSTEM: begin
        if (instr_rdata_i[14:12] == 3'b000)
        begin
          // non CSR related SYSTEM instructions
          if ( {instr_rdata_i[19:15], instr_rdata_i[11:7]} == '0)
          begin
            unique case (instr_rdata_i[31:20])
              12'h000:  // ECALL
              begin
                // environment (system) call
                ecall_insn_o  = 1'b1;
              end

              12'h001:  // ebreak
              begin
                // debugger trap
                ebrk_insn_o = 1'b1;
              end

              12'h302:  // mret
              begin
                illegal_insn_o = (PULP_SECURE) ? current_priv_lvl_i != PRIV_LVL_M : 1'b0;
                mret_insn_o    = ~illegal_insn_o;
                mret_dec_o     = 1'b1;
              end

              12'h002:  // uret
              begin
                illegal_insn_o = (PULP_SECURE) ? 1'b0 : 1'b1;
                uret_insn_o    = ~illegal_insn_o;
                uret_dec_o     = 1'b1;
              end

              12'h7b2:  // dret
              begin
                illegal_insn_o = !debug_mode_i;
                dret_insn_o    =  debug_mode_i;
                dret_dec_o     =  1'b1;
              end

              12'h105:  // wfi
              begin
                wfi_o = 1'b1;
                if (debug_wfi_no_sleep_i) begin
                  // Treat as NOP (do not cause sleep mode entry)
                  // Using decoding similar to ADDI, but without register reads/writes,
                  // i.e. keep regfile_alu_we = 0, rega_used_o = 0
                  alu_op_b_mux_sel_o = OP_B_IMM;
                  imm_b_mux_sel_o = IMMB_I;
                  alu_operator_o = ALU_ADD;
                end
              end

              default: illegal_insn_o = 1'b1;
            endcase
          end else illegal_insn_o = 1'b1;
        end
        else
        begin
          // instruction to read/modify CSR
          csr_access_o        = 1'b1;
          regfile_alu_we      = 1'b1;
          alu_op_b_mux_sel_o  = OP_B_IMM;
          imm_a_mux_sel_o     = IMMA_Z;
          imm_b_mux_sel_o     = IMMB_I;    // CSR address is encoded in I imm

          if (instr_rdata_i[14] == 1'b1) begin
            // rs1 field is used as immediate
            alu_op_a_mux_sel_o = OP_A_IMM;
          end else begin
            rega_used_o        = 1'b1;
            alu_op_a_mux_sel_o = OP_A_REGA_OR_FWD;
          end

          // instr_rdata_i[19:14] = rs or immediate value
          //   if set or clear with rs == x0 or imm == 0,
          //   then do not perform a write action
          unique case (instr_rdata_i[13:12])
            2'b01:   csr_op = CSR_OP_WRITE;
            2'b10:   csr_op = instr_rdata_i[19:15] == 5'b0 ? CSR_OP_READ : CSR_OP_SET;
            2'b11:   csr_op = instr_rdata_i[19:15] == 5'b0 ? CSR_OP_READ : CSR_OP_CLEAR;
            default: csr_illegal = 1'b1;
          endcase

          if (instr_rdata_i[29:28] > current_priv_lvl_i) begin
            // No access to higher privilege CSR
            csr_illegal = 1'b1;
          end

          // Determine if CSR access is illegal
          case (instr_rdata_i[31:20])
            // Floating point
            CSR_FFLAGS :
                if (FPU == 0 || fs_off_i == 1'b1) csr_illegal = 1'b1;

            CSR_FRM,
              CSR_FCSR :
                if (FPU == 0 || fs_off_i == 1'b1) begin
                  csr_illegal = 1'b1;
                end else begin
                  // FRM updated value needed by following FPU instruction
                  if (csr_op != CSR_OP_READ) csr_status_o = 1'b1;
                end

            //  Writes to read only CSRs results in illegal instruction
            CSR_MVENDORID,
              CSR_MARCHID,
              CSR_MIMPID,
              CSR_MHARTID :
                if (csr_op != CSR_OP_READ) csr_illegal = 1'b1;

            // These are valid CSR registers
            CSR_MSTATUS,
              CSR_MEPC,
              CSR_MTVEC,
              CSR_MCAUSE :
                // Not illegal, but treat as status CSR for side effect handling
                csr_status_o = 1'b1;

            // These are valid CSR registers
            CSR_MISA,
              CSR_MIE,
              CSR_MSCRATCH,
              CSR_MTVAL,
              CSR_MIP :
                ; // do nothing, not illegal

            // Hardware Performance Monitor
            CSR_MCYCLE,
              CSR_MINSTRET,
              CSR_MHPMCOUNTER3,
              CSR_MHPMCOUNTER4,  CSR_MHPMCOUNTER5,  CSR_MHPMCOUNTER6,  CSR_MHPMCOUNTER7,
              CSR_MHPMCOUNTER8,  CSR_MHPMCOUNTER9,  CSR_MHPMCOUNTER10, CSR_MHPMCOUNTER11,
              CSR_MHPMCOUNTER12, CSR_MHPMCOUNTER13, CSR_MHPMCOUNTER14, CSR_MHPMCOUNTER15,
              CSR_MHPMCOUNTER16, CSR_MHPMCOUNTER17, CSR_MHPMCOUNTER18, CSR_MHPMCOUNTER19,
              CSR_MHPMCOUNTER20, CSR_MHPMCOUNTER21, CSR_MHPMCOUNTER22, CSR_MHPMCOUNTER23,
              CSR_MHPMCOUNTER24, CSR_MHPMCOUNTER25, CSR_MHPMCOUNTER26, CSR_MHPMCOUNTER27,
              CSR_MHPMCOUNTER28, CSR_MHPMCOUNTER29, CSR_MHPMCOUNTER30, CSR_MHPMCOUNTER31,
              CSR_MCYCLEH,
              CSR_MINSTRETH,
              CSR_MHPMCOUNTER3H,
              CSR_MHPMCOUNTER4H,  CSR_MHPMCOUNTER5H,  CSR_MHPMCOUNTER6H,  CSR_MHPMCOUNTER7H,
              CSR_MHPMCOUNTER8H,  CSR_MHPMCOUNTER9H,  CSR_MHPMCOUNTER10H, CSR_MHPMCOUNTER11H,
              CSR_MHPMCOUNTER12H, CSR_MHPMCOUNTER13H, CSR_MHPMCOUNTER14H, CSR_MHPMCOUNTER15H,
              CSR_MHPMCOUNTER16H, CSR_MHPMCOUNTER17H, CSR_MHPMCOUNTER18H, CSR_MHPMCOUNTER19H,
              CSR_MHPMCOUNTER20H, CSR_MHPMCOUNTER21H, CSR_MHPMCOUNTER22H, CSR_MHPMCOUNTER23H,
              CSR_MHPMCOUNTER24H, CSR_MHPMCOUNTER25H, CSR_MHPMCOUNTER26H, CSR_MHPMCOUNTER27H,
              CSR_MHPMCOUNTER28H, CSR_MHPMCOUNTER29H, CSR_MHPMCOUNTER30H, CSR_MHPMCOUNTER31H,
              CSR_MCOUNTINHIBIT,
              CSR_MHPMEVENT3,
              CSR_MHPMEVENT4,  CSR_MHPMEVENT5,  CSR_MHPMEVENT6,  CSR_MHPMEVENT7,
              CSR_MHPMEVENT8,  CSR_MHPMEVENT9,  CSR_MHPMEVENT10, CSR_MHPMEVENT11,
              CSR_MHPMEVENT12, CSR_MHPMEVENT13, CSR_MHPMEVENT14, CSR_MHPMEVENT15,
              CSR_MHPMEVENT16, CSR_MHPMEVENT17, CSR_MHPMEVENT18, CSR_MHPMEVENT19,
              CSR_MHPMEVENT20, CSR_MHPMEVENT21, CSR_MHPMEVENT22, CSR_MHPMEVENT23,
              CSR_MHPMEVENT24, CSR_MHPMEVENT25, CSR_MHPMEVENT26, CSR_MHPMEVENT27,
              CSR_MHPMEVENT28, CSR_MHPMEVENT29, CSR_MHPMEVENT30, CSR_MHPMEVENT31 :
                // Not illegal, but treat as status CSR to get accurate counts
                csr_status_o = 1'b1;

            // Hardware Performance Monitor (unprivileged read-only mirror CSRs)
            CSR_CYCLE,
              CSR_INSTRET,
              CSR_HPMCOUNTER3,
              CSR_HPMCOUNTER4,  CSR_HPMCOUNTER5,  CSR_HPMCOUNTER6,  CSR_HPMCOUNTER7,
              CSR_HPMCOUNTER8,  CSR_HPMCOUNTER9,  CSR_HPMCOUNTER10, CSR_HPMCOUNTER11,
              CSR_HPMCOUNTER12, CSR_HPMCOUNTER13, CSR_HPMCOUNTER14, CSR_HPMCOUNTER15,
              CSR_HPMCOUNTER16, CSR_HPMCOUNTER17, CSR_HPMCOUNTER18, CSR_HPMCOUNTER19,
              CSR_HPMCOUNTER20, CSR_HPMCOUNTER21, CSR_HPMCOUNTER22, CSR_HPMCOUNTER23,
              CSR_HPMCOUNTER24, CSR_HPMCOUNTER25, CSR_HPMCOUNTER26, CSR_HPMCOUNTER27,
              CSR_HPMCOUNTER28, CSR_HPMCOUNTER29, CSR_HPMCOUNTER30, CSR_HPMCOUNTER31,
              CSR_CYCLEH,
              CSR_INSTRETH,
              CSR_HPMCOUNTER3H,
              CSR_HPMCOUNTER4H,  CSR_HPMCOUNTER5H,  CSR_HPMCOUNTER6H,  CSR_HPMCOUNTER7H,
              CSR_HPMCOUNTER8H,  CSR_HPMCOUNTER9H,  CSR_HPMCOUNTER10H, CSR_HPMCOUNTER11H,
              CSR_HPMCOUNTER12H, CSR_HPMCOUNTER13H, CSR_HPMCOUNTER14H, CSR_HPMCOUNTER15H,
              CSR_HPMCOUNTER16H, CSR_HPMCOUNTER17H, CSR_HPMCOUNTER18H, CSR_HPMCOUNTER19H,
              CSR_HPMCOUNTER20H, CSR_HPMCOUNTER21H, CSR_HPMCOUNTER22H, CSR_HPMCOUNTER23H,
              CSR_HPMCOUNTER24H, CSR_HPMCOUNTER25H, CSR_HPMCOUNTER26H, CSR_HPMCOUNTER27H,
              CSR_HPMCOUNTER28H, CSR_HPMCOUNTER29H, CSR_HPMCOUNTER30H, CSR_HPMCOUNTER31H :
                // Read-only and readable from user mode only if the bit of mcounteren is set
                if ((csr_op != CSR_OP_READ) ||
                    (PULP_SECURE && (current_priv_lvl_i != PRIV_LVL_M) && !mcounteren_i[instr_rdata_i[24:20]])) begin
                  csr_illegal = 1'b1;
                end else begin
                  csr_status_o = 1'b1;
                end

            // This register only exists in user mode
            CSR_MCOUNTEREN :
                if (!PULP_SECURE) begin
                  csr_illegal = 1'b1;
                end else begin
                  csr_status_o = 1'b1;
                end

            // Debug register access
            CSR_DCSR,
              CSR_DPC,
              CSR_DSCRATCH0,
              CSR_DSCRATCH1 :
                if (!debug_mode_i) begin
                  csr_illegal = 1'b1;
                end else begin
                  csr_status_o = 1'b1;
                end

            // Debug Trigger register access
            CSR_TSELECT,
              CSR_TDATA1,
              CSR_TDATA2,
              CSR_TDATA3,
              CSR_TINFO,
              CSR_MCONTEXT,
              CSR_SCONTEXT :
                if (DEBUG_TRIGGER_EN != 1)
                  csr_illegal = 1'b1;

            // Hardware Loop register
            CSR_LPSTART0,
              CSR_LPEND0,
              CSR_LPCOUNT0,
              CSR_LPSTART1,
              CSR_LPEND1,
              CSR_LPCOUNT1:
                if (!COREV_PULP || csr_op != CSR_OP_READ) csr_illegal = 1'b1;

            // UHARTID access
            CSR_UHARTID :
                if (!COREV_PULP || csr_op != CSR_OP_READ) csr_illegal = 1'b1;

            // PRIVLV access
            CSR_PRIVLV :
                if (!COREV_PULP || csr_op != CSR_OP_READ) begin
                  csr_illegal = 1'b1;
                end else begin
                  csr_status_o = 1'b1;
                end

            // ZFINX
            CSR_ZFINX :
                if (!COREV_PULP || (FPU && !ZFINX) || csr_op != CSR_OP_READ) begin
                  csr_illegal = 1'b1;
                end

            // PMP register access
            CSR_PMPCFG0,
              CSR_PMPCFG1,
              CSR_PMPCFG2,
              CSR_PMPCFG3,
              CSR_PMPADDR0,
              CSR_PMPADDR1,
              CSR_PMPADDR2,
              CSR_PMPADDR3,
              CSR_PMPADDR4,
              CSR_PMPADDR5,
              CSR_PMPADDR6,
              CSR_PMPADDR7,
              CSR_PMPADDR8,
              CSR_PMPADDR9,
              CSR_PMPADDR10,
              CSR_PMPADDR11,
              CSR_PMPADDR12,
              CSR_PMPADDR13,
              CSR_PMPADDR14,
              CSR_PMPADDR15 :
                if (!USE_PMP) csr_illegal = 1'b1;

            // User register access
            CSR_USTATUS,
              CSR_UEPC,
              CSR_UTVEC,
              CSR_UCAUSE :
                if (!PULP_SECURE) begin
                  csr_illegal = 1'b1;
                end else begin
                  csr_status_o = 1'b1;
                end

            default : csr_illegal = 1'b1;

          endcase // case (instr_rdata_i[31:20])

          illegal_insn_o = csr_illegal;

        end
      end
      default: illegal_insn_o = 1'b1;
    endcase

    // make sure invalid compressed instruction causes an exception
    if (illegal_c_insn_i) begin
      illegal_insn_o = 1'b1;
    end

  end

  // deassert we signals (in case of stalls)
  assign alu_en_o                    = (deassert_we_i) ? 1'b0          : alu_en;
  assign mult_int_en_o               = (deassert_we_i) ? 1'b0          : mult_int_en;
  assign mult_dot_en_o               = (deassert_we_i) ? 1'b0          : mult_dot_en;
  assign apu_en_o                    = (deassert_we_i) ? 1'b0          : apu_en;
  assign regfile_mem_we_o            = (deassert_we_i) ? 1'b0          : regfile_mem_we;
  assign regfile_alu_we_o            = (deassert_we_i) ? 1'b0          : regfile_alu_we;
  assign data_req_o                  = (deassert_we_i) ? 1'b0          : data_req;
  assign hwlp_we_o                   = (deassert_we_i) ? 3'b0          : hwlp_we;
  assign csr_op_o                    = (deassert_we_i) ? CSR_OP_READ   : csr_op;
  assign ctrl_transfer_insn_in_id_o  = (deassert_we_i) ? BRANCH_NONE   : ctrl_transfer_insn;

  assign ctrl_transfer_insn_in_dec_o  = ctrl_transfer_insn;
  assign regfile_alu_we_dec_o         = regfile_alu_we;

endmodule // cv32e40p_decoder
