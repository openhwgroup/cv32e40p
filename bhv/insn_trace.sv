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
// Description:  Macros and Functions to print information on RVFI interface      //
//                                                                                //
////////////////////////////////////////////////////////////////////////////////////

  `define DEFINE_CSR(CSR_NAME) \
    logic ``CSR_NAME``_we; \
    logic [31:0] ``CSR_NAME``_rdata; \
    logic [31:0] ``CSR_NAME``_rmask; \
    logic [31:0] ``CSR_NAME``_wdata; \
    logic [31:0] ``CSR_NAME``_wmask;

  `define ASSIGN_CSR(CSR_NAME) \
    this.m_csr.``CSR_NAME``_we    = m_source.m_csr.``CSR_NAME``_we; \
    this.m_csr.``CSR_NAME``_rdata = m_source.m_csr.``CSR_NAME``_rdata; \
    this.m_csr.``CSR_NAME``_rmask = m_source.m_csr.``CSR_NAME``_rmask; \
    this.m_csr.``CSR_NAME``_wdata = m_source.m_csr.``CSR_NAME``_wdata; \
    this.m_csr.``CSR_NAME``_wmask = m_source.m_csr.``CSR_NAME``_wmask;

  `define INIT_CSR(CSR_NAME) \
    this.m_csr.``CSR_NAME``_we    = '0; \
    this.m_csr.``CSR_NAME``_wmask = '0;

  import cv32e40p_tracer_pkg::*;
  class insn_trace_t;
    bit m_valid;
    logic [63:0] m_order;
    integer      m_start_cycle;
    integer      m_stop_cycle;
    time         m_start_time;
    time         m_stop_time;
    bit          m_skip_order; //next order was used by trap;
    logic [31:0] m_pc_rdata;
    logic [31:0] m_insn;
    string       m_mnemonic;
    logic        m_is_ebreak;
    logic        m_is_illegal;
    logic        m_is_irq;
    logic        m_is_memory;
    logic        m_is_load;
    logic        m_is_apu;
    logic        m_is_apu_ok;
    integer      m_apu_req_id;
    integer      m_mem_req_id[1:0];
    logic [ 1:0] m_mem_req_id_valid;
    logic        m_data_missaligned;
    logic        m_got_first_data;
    logic        m_got_ex_reg;
    logic       m_dbg_taken;
    logic [2:0] m_dbg_cause;

    logic       m_fflags_we_non_apu;
    logic       m_frm_we_non_apu;
    logic       m_fcsr_we_non_apu;
    logic [5:0] m_rs1_addr;
    logic [5:0] m_rs2_addr;
    logic [5:0] m_rs3_addr;
    logic [31:0] m_rs1_rdata;
    logic [31:0] m_rs2_rdata;
    logic [31:0] m_rs3_rdata;

    bit m_trap;

    bit m_got_regs_write;
    bit m_ex_fw;
    logic [ 5:0] m_rd_addr [1:0];
    logic [31:0] m_rd_wdata[1:0];
    logic        m_2_rd_insn; //this instruction uses 2 destination registers
    rvfi_intr_t m_intr;

    bit m_move_down_pipe;

    int m_instret_cnt;
    int m_instret_smaple_trigger; //We need to sample minstret from csr 2 cycle after id is doen

    bit m_sample_csr_write_in_ex;

    struct {
      logic [31:0] addr ;
      logic [31:0] rmask;
      logic [31:0] rdata;
      logic [31:0] wmask;
      logic [31:0] wdata;
    } m_mem;

    struct {
      logic mstatus_we;
      logic [31:0] mstatus_rmask;
      Status_t mstatus_wdata;
      logic [31:0] mstatus_wmask;
      Status_t mstatus_rdata;

      logic mstatus_fs_we;
      FS_t mstatus_fs_rdata;
      logic [31:0] mstatus_fs_rmask;
      FS_t mstatus_fs_wdata;
      logic [31:0] mstatus_fs_wmask;

      // mstatush

      `DEFINE_CSR(misa)
      `DEFINE_CSR(mie)
      `DEFINE_CSR(mtvec)
      //mtvec_mode
      //mtvt
      `DEFINE_CSR(mcountinhibit)
      //mhpmevent

      `DEFINE_CSR(mscratch)
      `DEFINE_CSR(mepc)
      `DEFINE_CSR(mcause)
      `DEFINE_CSR(mcycle)
      `DEFINE_CSR(minstret)
      bit got_minstret;
      `DEFINE_CSR(mcycleh)
      `DEFINE_CSR(minstreth)
      `DEFINE_CSR(cycle)
      `DEFINE_CSR(instret)
      // bit got_minstret;
      `DEFINE_CSR(cycleh)
      `DEFINE_CSR(instreth)

      logic [31:0][ 1:0]    mhpmcounter_we;
      logic [31:0][63:0] mhpmcounter_rdata;
      logic [31:0][63:0] mhpmcounter_rmask;
      logic [31:0][63:0] mhpmcounter_wdata;
      logic [31:0][63:0] mhpmcounter_wmask;

      logic [31:0]          mhpmevent_we;
      logic [31:0][31:0] mhpmevent_rdata;
      logic [31:0][31:0] mhpmevent_rmask;
      logic [31:0][31:0] mhpmevent_wdata;
      logic [31:0][31:0] mhpmevent_wmask;
      `DEFINE_CSR(mip)
      //mnxti
      //mintstatus
      //mintthresh
      //mscratchcsw
      //mscratchcswl
      //mclicbase

      `DEFINE_CSR(tdata1)
      `DEFINE_CSR(tdata2)
      `DEFINE_CSR(tinfo)
      `DEFINE_CSR(dcsr)

      `DEFINE_CSR(dpc)
      `DEFINE_CSR(dscratch0)
      `DEFINE_CSR(dscratch1)
      //dscratch1
      //mconfigptr
      //mhpmcounter

      `DEFINE_CSR(mvendorid)
      `DEFINE_CSR(marchid)

      `DEFINE_CSR(fflags)
      `DEFINE_CSR(frm   )
      `DEFINE_CSR(fcsr  )

      `DEFINE_CSR(lpstart0 )
      `DEFINE_CSR(lpend0   )
      `DEFINE_CSR(lpcount0 )
      `DEFINE_CSR(lpstart1 )
      `DEFINE_CSR(lpend1   )
      `DEFINE_CSR(lpcount1 )

    } m_csr;

    enum logic[2:0] {
      IF, ID, EX, WB, WB_2, APU
    } m_stage;


    function new();
      this.m_order                  = 0;
      this.m_start_cycle            = 0;
      this.m_stop_cycle             = 0;
      this.m_start_time             = 0;
      this.m_stop_time              = 0;
      this.m_skip_order             = 1'b0;
      this.m_valid                  = 1'b0;
      this.m_move_down_pipe         = 1'b0;
      this.m_data_missaligned       = 1'b0;
      this.m_got_first_data         = 1'b0;
      this.m_got_ex_reg             = 1'b0;
      this.m_intr                   = '0;
      this.m_dbg_taken              = 1'b0;
      this.m_dbg_cause              = '0;
      this.m_is_ebreak              = '0;
      this.m_is_illegal             = '0;
      this.m_is_irq                 = '0;
      this.m_is_memory              = 1'b0;
      this.m_is_load                = 1'b0;
      this.m_is_apu                 = 1'b0;
      this.m_is_apu_ok              = 1'b0;
      this.m_apu_req_id             = 0;
      this.m_mem_req_id[0]          = 0;
      this.m_mem_req_id[1]          = 0;
      this.m_mem_req_id_valid       = '0;
      this.m_trap                   = 1'b0;
      this.m_fflags_we_non_apu      = 1'b0;
      this.m_frm_we_non_apu         = 1'b0;
      this.m_fcsr_we_non_apu        = 1'b0;
      this.m_instret_cnt            = 0;
      this.m_instret_smaple_trigger = 0;
      this.m_sample_csr_write_in_ex = 1'b1;
    endfunction

    function void get_mnemonic();

      this.m_mnemonic = "INVALID";

      if(!is_compressed_id_i) begin
        // use casex instead of case inside due to ModelSim bug
        casex (this.m_insn)
          // Aliases
          32'h00_00_00_13: this.m_mnemonic = "nop";
          // Regular opcodes
          INSTR_LUI:       this.m_mnemonic = "lui";
          INSTR_AUIPC:     this.m_mnemonic = "auipc";
          INSTR_JAL:       this.m_mnemonic = "jal";
          INSTR_JALR:      this.m_mnemonic = "jalr";
          // BRANCH
          INSTR_BEQ:       this.m_mnemonic = "beq";
          INSTR_BNE:       this.m_mnemonic = "bne";
          INSTR_BLT:       this.m_mnemonic = "blt";
          INSTR_BGE:       this.m_mnemonic = "bge";
          INSTR_BLTU:      this.m_mnemonic = "bltu";
          INSTR_BGEU:      this.m_mnemonic = "bgeu";
          INSTR_BEQIMM:    this.m_mnemonic = "cv.beqimm";
          INSTR_BNEIMM:    this.m_mnemonic = "cv.bneimm";
          // OPIMM
          INSTR_ADDI:      this.m_mnemonic = "addi";
          INSTR_SLTI:      this.m_mnemonic = "slti";
          INSTR_SLTIU:     this.m_mnemonic = "sltiu";
          INSTR_XORI:      this.m_mnemonic = "xori";
          INSTR_ORI:       this.m_mnemonic = "ori";
          INSTR_ANDI:      this.m_mnemonic = "andi";
          INSTR_SLLI:      this.m_mnemonic = "slli";
          INSTR_SRLI:      this.m_mnemonic = "srli";
          INSTR_SRAI:      this.m_mnemonic = "srai";
          // OP
          INSTR_ADD:       this.m_mnemonic = "add";
          INSTR_SUB:       this.m_mnemonic = "sub";
          INSTR_SLL:       this.m_mnemonic = "sll";
          INSTR_SLT:       this.m_mnemonic = "slt";
          INSTR_SLTU:      this.m_mnemonic = "sltu";
          INSTR_XOR:       this.m_mnemonic = "xor";
          INSTR_SRL:       this.m_mnemonic = "srl";
          INSTR_SRA:       this.m_mnemonic = "sra";
          INSTR_OR:        this.m_mnemonic = "or";
          INSTR_AND:       this.m_mnemonic = "and";
          INSTR_EXTHS:     this.m_mnemonic = "cv.exths";
          INSTR_EXTHZ:     this.m_mnemonic = "cv.exthz";
          INSTR_EXTBS:     this.m_mnemonic = "cv.extbs";
          INSTR_EXTBZ:     this.m_mnemonic = "cv.extbz";
          INSTR_PAVG:      this.m_mnemonic = "cv.avg";
          INSTR_PAVGU:     this.m_mnemonic = "cv.avgu";

          INSTR_PADDN:   this.m_mnemonic = "cv.addN";
          INSTR_PADDUN:  this.m_mnemonic = "cv.adduN";
          INSTR_PADDRN:  this.m_mnemonic = "cv.addRN";
          INSTR_PADDURN: this.m_mnemonic = "cv.adduRN";
          INSTR_PSUBN:   this.m_mnemonic = "cv.subN";
          INSTR_PSUBUN:  this.m_mnemonic = "cv.subuN";
          INSTR_PSUBRN:  this.m_mnemonic = "cv.subRN";
          INSTR_PSUBURN: this.m_mnemonic = "cv.subuRN";

          INSTR_PADDNR:   this.m_mnemonic = "cv.addNr";
          INSTR_PADDUNR:  this.m_mnemonic = "cv.adduNr";
          INSTR_PADDRNR:  this.m_mnemonic = "cv.addRNr";
          INSTR_PADDURNR: this.m_mnemonic = "cv.adduRNr";
          INSTR_PSUBNR:   this.m_mnemonic = "cv.subNr";
          INSTR_PSUBUNR:  this.m_mnemonic = "cv.subuNr";
          INSTR_PSUBRNR:  this.m_mnemonic = "cv.subRNr";
          INSTR_PSUBURNR: this.m_mnemonic = "cv.subuRNr";

          INSTR_PSLET:  this.m_mnemonic = "cv.slet";
          INSTR_PSLETU: this.m_mnemonic = "cv.sletu";
          INSTR_PMIN:   this.m_mnemonic = "cv.min";
          INSTR_PMINU:  this.m_mnemonic = "cv.minu";
          INSTR_PMAX:   this.m_mnemonic = "cv.max";
          INSTR_PMAXU:  this.m_mnemonic = "cv.maxu";
          INSTR_PABS:   this.m_mnemonic = "cv.abs";
          INSTR_PCLIP:  this.m_mnemonic = "cv.clip";
          INSTR_PCLIPU: this.m_mnemonic = "cv.clipu";
          INSTR_PBEXT:  this.m_mnemonic = "cv.extract";
          INSTR_PBEXTU: this.m_mnemonic = "cv.extractu";
          INSTR_PBINS:  this.m_mnemonic = "cv.insert";
          INSTR_PBCLR:  this.m_mnemonic = "cv.bclr";
          INSTR_PBSET:  this.m_mnemonic = "cv.bset";
          INSTR_PBREV:  this.m_mnemonic = "cv.bitrev";

          INSTR_PCLIPR:  this.m_mnemonic = "cv.clipr";
          INSTR_PCLIPUR: this.m_mnemonic = "cv.clipur";
          INSTR_PBEXTR:  this.m_mnemonic = "cv.extractr";
          INSTR_PBEXTUR: this.m_mnemonic = "cv.extractur";
          INSTR_PBINSR:  this.m_mnemonic = "cv.insertr";
          INSTR_PBCLRR:  this.m_mnemonic = "cv.bclrr";
          INSTR_PBSETR:  this.m_mnemonic = "cv.bsetr";


          INSTR_FF1: this.m_mnemonic = "cv.ff1";
          INSTR_FL1: this.m_mnemonic = "cv.fl1";
          INSTR_CLB: this.m_mnemonic = "cv.clb";
          INSTR_CNT: this.m_mnemonic = "cv.cnt";
          INSTR_ROR: this.m_mnemonic = "cv.ror";

          // FENCE
          INSTR_FENCE:  this.m_mnemonic = "fence";
          INSTR_FENCEI: this.m_mnemonic = "fencei";
          // SYSTEM (CSR manipulation)
          INSTR_CSRRW:  this.m_mnemonic = "csrrw";
          INSTR_CSRRS:  this.m_mnemonic = "csrrs";
          INSTR_CSRRC:  this.m_mnemonic = "csrrc";
          INSTR_CSRRWI: this.m_mnemonic = "csrrwi";
          INSTR_CSRRSI: this.m_mnemonic = "csrrsi";
          INSTR_CSRRCI: this.m_mnemonic = "csrrci";
          // SYSTEM (others)
          INSTR_ECALL:  this.m_mnemonic = "ecall";
          INSTR_EBREAK: this.m_mnemonic = "ebreak";
          INSTR_URET:   this.m_mnemonic = "uret";
          INSTR_MRET:   this.m_mnemonic = "mret";
          INSTR_WFI:    this.m_mnemonic = "wfi";

          INSTR_DRET: this.m_mnemonic = "dret";

          // RV32M
          INSTR_PMUL:      this.m_mnemonic = "mul";
          INSTR_PMUH:      this.m_mnemonic = "mulh";
          INSTR_PMULHSU:   this.m_mnemonic = "mulhsu";
          INSTR_PMULHU:    this.m_mnemonic = "mulhu";
          INSTR_DIV:       this.m_mnemonic = "div";
          INSTR_DIVU:      this.m_mnemonic = "divu";
          INSTR_REM:       this.m_mnemonic = "rem";
          INSTR_REMU:      this.m_mnemonic = "remu";
          // PULP MULTIPLIER
          INSTR_PMAC:      this.m_mnemonic = "cv.mac";
          INSTR_PMSU:      this.m_mnemonic = "cv.msu";
          INSTR_PMULSN:    this.m_mnemonic = "cv.mulsN";
          INSTR_PMULHHSN:  this.m_mnemonic = "cv.mulhhsN";
          INSTR_PMULSRN:   this.m_mnemonic = "cv.mulsRN";
          INSTR_PMULHHSRN: this.m_mnemonic = "cv.mulhhsRN";
          INSTR_PMULUN:    this.m_mnemonic = "cv.muluN";
          INSTR_PMULHHUN:  this.m_mnemonic = "cv.mulhhuN";
          INSTR_PMULURN:   this.m_mnemonic = "cv.muluRN";
          INSTR_PMULHHURN: this.m_mnemonic = "cv.mulhhuRN";
          INSTR_PMACSN:    this.m_mnemonic = "cv.macsN";
          INSTR_PMACHHSN:  this.m_mnemonic = "cv.machhsN";
          INSTR_PMACSRN:   this.m_mnemonic = "cv.macsRN";
          INSTR_PMACHHSRN: this.m_mnemonic = "cv.machhsRN";
          INSTR_PMACUN:    this.m_mnemonic = "cv.macuN";
          INSTR_PMACHHUN:  this.m_mnemonic = "cv.machhuN";
          INSTR_PMACURN:   this.m_mnemonic = "cv.macuRN";
          INSTR_PMACHHURN: this.m_mnemonic = "cv.machhuRN";

          // FP-OP
          INSTR_FMADD:   this.m_mnemonic = "fmadd.s";
          INSTR_FMSUB:   this.m_mnemonic = "fmsub.s";
          INSTR_FNMADD:  this.m_mnemonic = "fnmadd.s";
          INSTR_FNMSUB:  this.m_mnemonic = "fnmsub.s";
          INSTR_FADD:    this.m_mnemonic = "fadd.s";
          INSTR_FSUB:    this.m_mnemonic = "fsub.s";
          INSTR_FMUL:    this.m_mnemonic = "fmul.s";
          INSTR_FDIV:    this.m_mnemonic = "fdiv.s";
          INSTR_FSQRT:   this.m_mnemonic = "fsqrt.s";
          INSTR_FSGNJS:  this.m_mnemonic = "fsgnj.s";
          INSTR_FSGNJNS: this.m_mnemonic = "fsgnjn.s";
          INSTR_FSGNJXS: this.m_mnemonic = "fsgnjx.s";
          INSTR_FMIN:    this.m_mnemonic = "fmin.s";
          INSTR_FMAX:    this.m_mnemonic = "fmax.s";
          INSTR_FCVTWS:  this.m_mnemonic = "fcvt.w.s";
          INSTR_FCVTWUS: this.m_mnemonic = "fcvt.wu.s";
          INSTR_FMVXS:   this.m_mnemonic = "fmv.x.s";
          INSTR_FEQS:    this.m_mnemonic = "feq.s";
          INSTR_FLTS:    this.m_mnemonic = "flt.s";
          INSTR_FLES:    this.m_mnemonic = "fle.s";
          INSTR_FCLASS:  this.m_mnemonic = "fclass.s";
          INSTR_FCVTSW:  this.m_mnemonic = "fcvt.s.w";
          INSTR_FCVTSWU: this.m_mnemonic = "fcvt.s.wu";
          INSTR_FMVSX:   this.m_mnemonic = "fmv.s.x";

          // RV32A
          INSTR_LR      : this.m_mnemonic = "lr.w";
          INSTR_SC      : this.m_mnemonic = "sc.w";
          INSTR_AMOSWAP : this.m_mnemonic = "amoswap.w";
          INSTR_AMOADD  : this.m_mnemonic = "amoadd.w";
          INSTR_AMOXOR  : this.m_mnemonic = "amoxor.w";
          INSTR_AMOAND  : this.m_mnemonic = "amoand.w";
          INSTR_AMOOR   : this.m_mnemonic = "amoor.w";
          INSTR_AMOMIN  : this.m_mnemonic = "amomin.w";
          INSTR_AMOMAX  : this.m_mnemonic = "amomax.w";
          INSTR_AMOMINU : this.m_mnemonic = "amominu.w";
          INSTR_AMOMAXU : this.m_mnemonic = "amomaxu.w";

          // LOAD STORE
          INSTR_LB  : this.m_mnemonic = "lb";
          INSTR_LH  : this.m_mnemonic = "lh";
          INSTR_LW  : this.m_mnemonic = "lw";
          INSTR_LBU : this.m_mnemonic = "lbu";
          INSTR_LHU : this.m_mnemonic = "lhu";
          INSTR_SB  : this.m_mnemonic = "sb";
          INSTR_SH  : this.m_mnemonic = "sh";
          INSTR_SW  : this.m_mnemonic = "sw";

          // CUSTOM 0
          // Post-Increment Register-Immediate Load
          INSTR_CVLBI  : this.m_mnemonic = "cv.lb";
          INSTR_CVLBUI : this.m_mnemonic = "cv.lbu";
          INSTR_CVLHI  : this.m_mnemonic = "cv.lh";
          INSTR_CVLHUI : this.m_mnemonic = "cv.lhu";
          INSTR_CVLWI  : this.m_mnemonic = "cv.lw";

          // Event Load
          INSTR_CVELW : this.m_mnemonic = "cv.elw";

          // CUSTOM_1
          // Post-Increment Register-Register Load
          INSTR_CVLBR  : this.m_mnemonic = "cv.lb";
          INSTR_CVLBUR : this.m_mnemonic = "cv.lbu";
          INSTR_CVLHR  : this.m_mnemonic = "cv.lh";
          INSTR_CVLHUR : this.m_mnemonic = "cv.lhu";
          INSTR_CVLWR  : this.m_mnemonic = "cv.lw";

          // Register-Register Load
          INSTR_CVLBRR  : this.m_mnemonic = "cv.lb";
          INSTR_CVLBURR : this.m_mnemonic = "cv.lbu";
          INSTR_CVLHRR  : this.m_mnemonic = "cv.lh";
          INSTR_CVLHURR : this.m_mnemonic = "cv.lhu";
          INSTR_CVLWRR  : this.m_mnemonic = "cv.lw";

          // Post-Increment Register-Immediate Store
          INSTR_CVSBI : this.m_mnemonic = "cv.sb";
          INSTR_CVSHI : this.m_mnemonic = "cv.sh";
          INSTR_CVSWI : this.m_mnemonic = "cv.sw";

          // Post-Increment Register-Register Store operations encoding
          INSTR_CVSBR : this.m_mnemonic = "cv.sb";
          INSTR_CVSHR : this.m_mnemonic = "cv.sh";
          INSTR_CVSWR : this.m_mnemonic = "cv.sw";

          // Register-Register Store operations
          INSTR_CVSBRR : this.m_mnemonic = "cv.sb";
          INSTR_CVSHRR : this.m_mnemonic = "cv.sh";
          INSTR_CVSWRR : this.m_mnemonic = "cv.sw";

          // Hardware Loops
          INSTR_CVSTARTI0 : this.m_mnemonic = "cv.starti 0";
          INSTR_CVSTART0  : this.m_mnemonic = "cv.start 0";
          INSTR_CVSENDI0  : this.m_mnemonic = "cv.endi 0";
          INSTR_CVEND0    : this.m_mnemonic = "cv.end 0";
          INSTR_CVCOUNTI0 : this.m_mnemonic = "cv.counti 0";
          INSTR_CVCOUNT0  : this.m_mnemonic = "cv.count 0";
          INSTR_CVSETUPI0 : this.m_mnemonic = "cv.setupi 0";
          INSTR_CVSETUP0  : this.m_mnemonic = "cv.setup 0";
          INSTR_CVSTARTI1 : this.m_mnemonic = "cv..starti 1";
          INSTR_CVSTART1  : this.m_mnemonic = "cv..start 1";
          INSTR_CVSENDI1  : this.m_mnemonic = "cv..endi 1";
          INSTR_CVEND1    : this.m_mnemonic = "cv..end 1";
          INSTR_CVCOUNTI1 : this.m_mnemonic = "cv..counti 1";
          INSTR_CVCOUNT1  : this.m_mnemonic = "cv..count 1";
          INSTR_CVSETUPI1 : this.m_mnemonic = "cv..setupi 1";
          INSTR_CVSETUP1  : this.m_mnemonic = "cv..setup 1";

          // CUSTOM 3
          // SIMD ALU
          INSTR_CVADDH          : this.m_mnemonic = "cv.add.h";
          INSTR_CVADDSCH        : this.m_mnemonic = "cv.add.sc.h";
          INSTR_CVADDSCIH       : this.m_mnemonic = "cv.add.sci.h";
          INSTR_CVADDB          : this.m_mnemonic = "cv.add.b";
          INSTR_CVADDSCB        : this.m_mnemonic = "cv.add.sc.b";
          INSTR_CVADDSCIB       : this.m_mnemonic = "cv.add.sci.b";
          INSTR_CVSUBH          : this.m_mnemonic = "cv.sub.h";
          INSTR_CVSUBSCH        : this.m_mnemonic = "cv.sub.sc.h";
          INSTR_CVSUBSCIH       : this.m_mnemonic = "cv.sub.sci.h";
          INSTR_CVSUBB          : this.m_mnemonic = "cv.sub.b";
          INSTR_CVSUBSCB        : this.m_mnemonic = "cv.sub.sc.b";
          INSTR_CVSUBSCIB       : this.m_mnemonic = "cv.sub.sci.b";
          INSTR_CVAVGH          : this.m_mnemonic = "cv.avg.h";
          INSTR_CVAVGSCH        : this.m_mnemonic = "cv.avg.sc.h";
          INSTR_CVAVGSCIH       : this.m_mnemonic = "cv.avg.sci.h";
          INSTR_CVAVGB          : this.m_mnemonic = "cv.avg.b";
          INSTR_CVAVGSCB        : this.m_mnemonic = "cv.avg.sc.b";
          INSTR_CVAVGSCIB       : this.m_mnemonic = "cv.avg.sci.b";
          INSTR_CVAVGUH         : this.m_mnemonic = "cv.avgu.h";
          INSTR_CVAVGUSCH       : this.m_mnemonic = "cv.avgu.sc.h";
          INSTR_CVAVGUSCIH      : this.m_mnemonic = "cv.avgu.sci.h";
          INSTR_CVAVGUB         : this.m_mnemonic = "cv.avgu.b";
          INSTR_CVAVGUSCB       : this.m_mnemonic = "cv.avgu.sc.b";
          INSTR_CVAVGUSCIB      : this.m_mnemonic = "cv.avgu.sci.b";
          INSTR_CVMINH          : this.m_mnemonic = "cv.min.h";
          INSTR_CVMINSCH        : this.m_mnemonic = "cv.min.sc.h";
          INSTR_CVMINSCIH       : this.m_mnemonic = "cv.min.sci.h";
          INSTR_CVMINB          : this.m_mnemonic = "cv.min.b";
          INSTR_CVMINSCB        : this.m_mnemonic = "cv.min.sc.b";
          INSTR_CVMINSCIB       : this.m_mnemonic = "cv.min.sci.b";
          INSTR_CVMINUH         : this.m_mnemonic = "cv.minu.h";
          INSTR_CVMINUSCH       : this.m_mnemonic = "cv.minu.sc.h";
          INSTR_CVMINUSCIH      : this.m_mnemonic = "cv.minu.sci.h";
          INSTR_CVMINUB         : this.m_mnemonic = "cv.minu.b";
          INSTR_CVMINUSCB       : this.m_mnemonic = "cv.minu.sc.b";
          INSTR_CVMINUSCIB      : this.m_mnemonic = "cv.minu.sci.b";
          INSTR_CVMAXH          : this.m_mnemonic = "cv.max.h";
          INSTR_CVMAXSCH        : this.m_mnemonic = "cv.max.sc.h";
          INSTR_CVMAXSCIH       : this.m_mnemonic = "cv.max.sci.h";
          INSTR_CVMAXB          : this.m_mnemonic = "cv.max.b";
          INSTR_CVMAXSCB        : this.m_mnemonic = "cv.max.sc.b";
          INSTR_CVMAXSCIB       : this.m_mnemonic = "cv.max.sci.b";
          INSTR_CVMAXUH         : this.m_mnemonic = "cv.maxu.h";
          INSTR_CVMAXUSCH       : this.m_mnemonic = "cv.maxu.sc.h";
          INSTR_CVMAXUSCIH      : this.m_mnemonic = "cv.maxu.sci.h";
          INSTR_CVMAXUB         : this.m_mnemonic = "cv.maxu.b";
          INSTR_CVMAXUSCB       : this.m_mnemonic = "cv.maxu.sc.b";
          INSTR_CVMAXUSCIB      : this.m_mnemonic = "cv.maxu.sci.b";
          INSTR_CVSRLH          : this.m_mnemonic = "cv.srl.h";
          INSTR_CVSRLSCH        : this.m_mnemonic = "cv.srl.sc.h";
          INSTR_CVSRLSCIH       : this.m_mnemonic = "cv.srl.sci.h";
          INSTR_CVSRLB          : this.m_mnemonic = "cv.srl.b";
          INSTR_CVSRLSCB        : this.m_mnemonic = "cv.srl.sc.b";
          INSTR_CVSRLSCIB       : this.m_mnemonic = "cv.srl.sci.b";
          INSTR_CVSRAH          : this.m_mnemonic = "cv.sra.h";
          INSTR_CVSRASCH        : this.m_mnemonic = "cv.sra.sc.h";
          INSTR_CVSRASCIH       : this.m_mnemonic = "cv.sra.sci.h";
          INSTR_CVSRAB          : this.m_mnemonic = "cv.sra.b";
          INSTR_CVSRASCB        : this.m_mnemonic = "cv.sra.sc.b";
          INSTR_CVSRASCIB       : this.m_mnemonic = "cv.sra.sci.b";
          INSTR_CVSLLH          : this.m_mnemonic = "cv.sll.h";
          INSTR_CVSLLSCH        : this.m_mnemonic = "cv.sll.sc.h";
          INSTR_CVSLLSCIH       : this.m_mnemonic = "cv.sll.sci.h";
          INSTR_CVSLLB          : this.m_mnemonic = "cv.sll.b";
          INSTR_CVSLLSCB        : this.m_mnemonic = "cv.sll.sc.b";
          INSTR_CVSLLSCIB       : this.m_mnemonic = "cv.sll.sci.b";
          INSTR_CVORH           : this.m_mnemonic = "cv.or.h";
          INSTR_CVORSCH         : this.m_mnemonic = "cv.or.sc.h";
          INSTR_CVORSCIH        : this.m_mnemonic = "cv.or.sci.h";
          INSTR_CVORB           : this.m_mnemonic = "cv.or.b";
          INSTR_CVORSCB         : this.m_mnemonic = "cv.or.sc.b";
          INSTR_CVORSCIB        : this.m_mnemonic = "cv.or.sci.b";
          INSTR_CVXORH          : this.m_mnemonic = "cv.xor.h";
          INSTR_CVXORSCH        : this.m_mnemonic = "cv.xor.sc.h";
          INSTR_CVXORSCIH       : this.m_mnemonic = "cv.xor.sci.h";
          INSTR_CVXORB          : this.m_mnemonic = "cv.xor.b";
          INSTR_CVXORSCB        : this.m_mnemonic = "cv.xor.sc.b";
          INSTR_CVXORSCIB       : this.m_mnemonic = "cv.xor.sci.b";
          INSTR_CVANDH          : this.m_mnemonic = "cv.and.h";
          INSTR_CVANDSCH        : this.m_mnemonic = "cv.and.sc.h";
          INSTR_CVANDSCIH       : this.m_mnemonic = "cv.and.sci.h";
          INSTR_CVANDB          : this.m_mnemonic = "cv.and.b";
          INSTR_CVANDSCB        : this.m_mnemonic = "cv.and.sc.b";
          INSTR_CVANDSCIB       : this.m_mnemonic = "cv.and.sci.b";
          INSTR_CVABSH          : this.m_mnemonic = "cv.abs.h";
          INSTR_CVABSB          : this.m_mnemonic = "cv.abs.b";
          INSTR_CVEXTRACTH      : this.m_mnemonic = "cv.extract.h";
          INSTR_CVEXTRACTB      : this.m_mnemonic = "cv.extract.b";
          INSTR_CVEXTRACTUH     : this.m_mnemonic = "cv.extractu.h";
          INSTR_CVEXTRACTUB     : this.m_mnemonic = "cv.extractu.b";
          INSTR_CVINSERTH       : this.m_mnemonic = "cv.insert.h";
          INSTR_CVINSERTB       : this.m_mnemonic = "cv.insert.b";
          INSTR_CVDOTUPH        : this.m_mnemonic = "cv.dotup.h";
          INSTR_CVDOTUPSCH      : this.m_mnemonic = "cv.dotup.sc.h";
          INSTR_CVDOTUPSCIH     : this.m_mnemonic = "cv.dotup.sci.h";
          INSTR_CVDOTUPB        : this.m_mnemonic = "cv.dotup.b";
          INSTR_CVDOTUPSCB      : this.m_mnemonic = "cv.dotup.sc.b";
          INSTR_CVDOTUPSCIB     : this.m_mnemonic = "cv.dotup.sci.b";
          INSTR_CVDOTUSPH       : this.m_mnemonic = "cv.dotusp.h.h";
          INSTR_CVDOTUSPSCH     : this.m_mnemonic = "cv.dotusp.sc.h.sc.h";
          INSTR_CVDOTUSPSCIH    : this.m_mnemonic = "cv.dotusp.sci.h.sci.h";
          INSTR_CVDOTUSPB       : this.m_mnemonic = "cv.dotusp.b.b";
          INSTR_CVDOTUSPSCB     : this.m_mnemonic = "cv.dotusp.sc.b.sc.b";
          INSTR_CVDOTUSPSCIB    : this.m_mnemonic = "cv.dotusp.sci.b.sci.b";
          INSTR_CVDOTSPH        : this.m_mnemonic = "cv.dotsp.h";
          INSTR_CVDOTSPSCH      : this.m_mnemonic = "cv.dotsp.sc.h";
          INSTR_CVDOTSPSCIH     : this.m_mnemonic = "cv.dotsp.sci.h";
          INSTR_CVDOTSPB        : this.m_mnemonic = "cv.dotsp.b";
          INSTR_CVDOTSPSCB      : this.m_mnemonic = "cv.dotsp.sc.b";
          INSTR_CVDOTSPSCIB     : this.m_mnemonic = "cv.dotsp.sci.b";
          INSTR_CVSDOTUPH       : this.m_mnemonic = "cv.sdotup.h";
          INSTR_CVSDOTUPSCH     : this.m_mnemonic = "cv.sdotup.sc.h";
          INSTR_CVSDOTUPSCIH    : this.m_mnemonic = "cv.sdotup.sci.h";
          INSTR_CVSDOTUPB       : this.m_mnemonic = "cv.sdotup.b";
          INSTR_CVSDOTUPSCB     : this.m_mnemonic = "cv.sdotup.sc.b";
          INSTR_CVSDOTUPSCIB    : this.m_mnemonic = "cv.sdotup.sci.b";
          INSTR_CVSDOTUSPH      : this.m_mnemonic = "cv.sdotusp.h";
          INSTR_CVSDOTUSPSCH    : this.m_mnemonic = "cv.sdotusp.sc.h";
          INSTR_CVSDOTUSPSCIH   : this.m_mnemonic = "cv.sdotusp.sci.h";
          INSTR_CVSDOTUSPB      : this.m_mnemonic = "cv.sdotusp.b";
          INSTR_CVSDOTUSPSCB    : this.m_mnemonic = "cv.sdotusp.sc.b";
          INSTR_CVSDOTUSPSCIB   : this.m_mnemonic = "cv.sdotusp.sci.b";
          INSTR_CVSDOTSPH       : this.m_mnemonic = "cv.sdotsp.h";
          INSTR_CVSDOTSPSCH     : this.m_mnemonic = "cv.sdotsp.sc.h";
          INSTR_CVSDOTSPSCIH    : this.m_mnemonic = "cv.sdotsp.sci.h";
          INSTR_CVSDOTSPB       : this.m_mnemonic = "cv.sdotsp.b";
          INSTR_CVSDOTSPSCB     : this.m_mnemonic = "cv.sdotsp.sc.b";
          INSTR_CVSDOTSPSCIB    : this.m_mnemonic = "cv.sdotsp.sci.b";
          INSTR_CVSHUFFLEH      : this.m_mnemonic = "cv.shuffle.h";
          INSTR_CVSHUFFLESCIH   : this.m_mnemonic = "cv.shuffle.sci.h";
          INSTR_CVSHUFFLEB      : this.m_mnemonic = "cv.shuffle.b";
          INSTR_CVSHUFFLEL0SCIB : this.m_mnemonic = "cv.shufflel0.sci.b";
          INSTR_CVSHUFFLEL1SCIB : this.m_mnemonic = "cv.shufflel1.sci.b";
          INSTR_CVSHUFFLEL2SCIB : this.m_mnemonic = "cv.shufflel2.sci.b";
          INSTR_CVSHUFFLEL3SCIB : this.m_mnemonic = "cv.shufflel3.sci.b";
          INSTR_CVSHUFFLE2H     : this.m_mnemonic = "cv.shuffle2.h";
          INSTR_CVSHUFFLE2B     : this.m_mnemonic = "cv.shuffle2.b";
          INSTR_CVPACK          : this.m_mnemonic = "cv.pack";
          INSTR_CVPACKH         : this.m_mnemonic = "cv.pack.h";
          INSTR_CVPACKHIB       : this.m_mnemonic = "cv.packhi.b";
          INSTR_CVPACKLOB       : this.m_mnemonic = "cv.packlo.b";

          // SIMD COMPARISON
          INSTR_CVCMPEQH     : this.m_mnemonic = "cv.cmpeq.h";
          INSTR_CVCMPEQSCH   : this.m_mnemonic = "cv.cmpeq.sc.h";
          INSTR_CVCMPEQSCIH  : this.m_mnemonic = "cv.cmpeq.sci.h";
          INSTR_CVCMPEQB     : this.m_mnemonic = "cv.cmpeq.b";
          INSTR_CVCMPEQSCB   : this.m_mnemonic = "cv.cmpeq.sc.b";
          INSTR_CVCMPEQSCIB  : this.m_mnemonic = "cv.cmpeq.sci.b";
          INSTR_CVCMPNEH     : this.m_mnemonic = "cv.cmpne.h";
          INSTR_CVCMPNESCH   : this.m_mnemonic = "cv.cmpne.sc.h";
          INSTR_CVCMPNESCIH  : this.m_mnemonic = "cv.cmpne.sci.h";
          INSTR_CVCMPNEB     : this.m_mnemonic = "cv.cmpne.b";
          INSTR_CVCMPNESCB   : this.m_mnemonic = "cv.cmpne.sc.b";
          INSTR_CVCMPNESCIB  : this.m_mnemonic = "cv.cmpne.sci.b";
          INSTR_CVCMPGTH     : this.m_mnemonic = "cv.cmpgt.h";
          INSTR_CVCMPGTSCH   : this.m_mnemonic = "cv.cmpgt.sc.h";
          INSTR_CVCMPGTSCIH  : this.m_mnemonic = "cv.cmpgt.sci.h";
          INSTR_CVCMPGTB     : this.m_mnemonic = "cv.cmpgt.b";
          INSTR_CVCMPGTSCB   : this.m_mnemonic = "cv.cmpgt.sc.b";
          INSTR_CVCMPGTSCIB  : this.m_mnemonic = "cv.cmpgt.sci.b";
          INSTR_CVCMPGEH     : this.m_mnemonic = "cv.cmpge.h";
          INSTR_CVCMPGESCH   : this.m_mnemonic = "cv.cmpge.sc.h";
          INSTR_CVCMPGESCIH  : this.m_mnemonic = "cv.cmpge.sci.h";
          INSTR_CVCMPGEB     : this.m_mnemonic = "cv.cmpge.b";
          INSTR_CVCMPGESCB   : this.m_mnemonic = "cv.cmpge.sc.b";
          INSTR_CVCMPGESCIB  : this.m_mnemonic = "cv.cmpge.sci.b";
          INSTR_CVCMPLTH     : this.m_mnemonic = "cv.cmplt.h";
          INSTR_CVCMPLTSCH   : this.m_mnemonic = "cv.cmplt.sc.h";
          INSTR_CVCMPLTSCIH  : this.m_mnemonic = "cv.cmplt.sci.h";
          INSTR_CVCMPLTB     : this.m_mnemonic = "cv.cmplt.b";
          INSTR_CVCMPLTSCB   : this.m_mnemonic = "cv.cmplt.sc.b";
          INSTR_CVCMPLTSCIB  : this.m_mnemonic = "cv.cmplt.sci.b";
          INSTR_CVCMPLEH     : this.m_mnemonic = "cv.cmple.h";
          INSTR_CVCMPLESCH   : this.m_mnemonic = "cv.cmple.sc.h";
          INSTR_CVCMPLESCIH  : this.m_mnemonic = "cv.cmple.sci.h";
          INSTR_CVCMPLEB     : this.m_mnemonic = "cv.cmple.b";
          INSTR_CVCMPLESCB   : this.m_mnemonic = "cv.cmple.sc.b";
          INSTR_CVCMPLESCIB  : this.m_mnemonic = "cv.cmple.sci.b";
          INSTR_CVCMPGTUH    : this.m_mnemonic = "cv.cmpgtu.h";
          INSTR_CVCMPGTUSCH  : this.m_mnemonic = "cv.cmpgtu.sc.h";
          INSTR_CVCMPGTUSCIH : this.m_mnemonic = "cv.cmpgtu.sci.h";
          INSTR_CVCMPGTUB    : this.m_mnemonic = "cv.cmpgtu.b";
          INSTR_CVCMPGTUSCB  : this.m_mnemonic = "cv.cmpgtu.sc.b";
          INSTR_CVCMPGTUSCIB : this.m_mnemonic = "cv.cmpgtu.sci.b";
          INSTR_CVCMPGEUH    : this.m_mnemonic = "cv.cmpgeu.h";
          INSTR_CVCMPGEUSCH  : this.m_mnemonic = "cv.cmpgeu.sc.h";
          INSTR_CVCMPGEUSCIH : this.m_mnemonic = "cv.cmpgeu.sci.h";
          INSTR_CVCMPGEUB    : this.m_mnemonic = "cv.cmpgeu.b";
          INSTR_CVCMPGEUSCB  : this.m_mnemonic = "cv.cmpgeu.sc.b";
          INSTR_CVCMPGEUSCIB : this.m_mnemonic = "cv.cmpgeu.sci.b";
          INSTR_CVCMPLTUH    : this.m_mnemonic = "cv.cmpltu.h";
          INSTR_CVCMPLTUSCH  : this.m_mnemonic = "cv.cmpltu.sc.h";
          INSTR_CVCMPLTUSCIH : this.m_mnemonic = "cv.cmpltu.sci.h";
          INSTR_CVCMPLTUB    : this.m_mnemonic = "cv.cmpltu.b";
          INSTR_CVCMPLTUSCB  : this.m_mnemonic = "cv.cmpltu.sc.b";
          INSTR_CVCMPLTUSCIB : this.m_mnemonic = "cv.cmpltu.sci.b";
          INSTR_CVCMPLEUH    : this.m_mnemonic = "cv.cmpleu.h";
          INSTR_CVCMPLEUSCH  : this.m_mnemonic = "cv.cmpleu.sc.h";
          INSTR_CVCMPLEUSCIH : this.m_mnemonic = "cv.cmpleu.sci.h";
          INSTR_CVCMPLEUB    : this.m_mnemonic = "cv.cmpleu.b";
          INSTR_CVCMPLEUSCB  : this.m_mnemonic = "cv.cmpleu.sc.b";
          INSTR_CVCMPLEUSCIB : this.m_mnemonic = "cv.cmpleu.sci.b";

          // SIMD CPLX
          INSTR_CVCPLXMULR     : this.m_mnemonic = "cv.cplxmul.r";
          INSTR_CVCPLXMULRDIV2 : this.m_mnemonic = "cv.cplxmul.r.div2";
          INSTR_CVCPLXMULRDIV4 : this.m_mnemonic = "cv.cplxmul.r.div4";
          INSTR_CVCPLXMULRDIV8 : this.m_mnemonic = "cv.cplxmul.r.div8";
          INSTR_CVCPLXMULI     : this.m_mnemonic = "cv.cplxmul.i";
          INSTR_CVCPLXMULIDIV2 : this.m_mnemonic = "cv.cplxmul.i.div2";
          INSTR_CVCPLXMULIDIV4 : this.m_mnemonic = "cv.cplxmul.i.div4";
          INSTR_CVCPLXMULIDIV8 : this.m_mnemonic = "cv.cplxmul.i.div8";
          INSTR_CVCPLXCONJ     : this.m_mnemonic = "cv.cplxconj";
          INSTR_CVSUBROTMJ     : this.m_mnemonic = "cv.subrotmj";
          INSTR_CVSUBROTMJDIV2 : this.m_mnemonic = "cv.subrotmj.div2";
          INSTR_CVSUBROTMJDIV4 : this.m_mnemonic = "cv.subrotmj.div4";
          INSTR_CVSUBROTMJDIV8 : this.m_mnemonic = "cv.subrotmj.div8";
          INSTR_CVADDIV2       : this.m_mnemonic = "cv.add.div2";
          INSTR_CVADDIV4       : this.m_mnemonic = "cv.add.div4";
          INSTR_CVADDIV8       : this.m_mnemonic = "cv.add.div8";
          INSTR_CVSUBIV2       : this.m_mnemonic = "cv.sub.div2";
          INSTR_CVSUBIV4       : this.m_mnemonic = "cv.sub.div4";
          INSTR_CVSUBIV8       : this.m_mnemonic = "cv.sub.div8";

          default              : this.m_mnemonic = "INVALID";
        endcase  // unique case (instr)
      end else begin //Compressed instruction
        unique case (this.m_insn[1:0])
          // C0
          2'b00: begin
            unique case (this.m_insn[15:13])
              3'b000: begin
                // c.addi4spn -> addi rd', x2, imm
                this.m_mnemonic = "c.addi4spn";
              end

              3'b001:  begin this.m_mnemonic = "c.fld"; end
              3'b010:  begin this.m_mnemonic = "c.lw";  end
              3'b011:  begin this.m_mnemonic = "c.flw"; end
              3'b101:  begin this.m_mnemonic = "c.fsd"; end
              3'b110:  begin this.m_mnemonic = "c.sw";  end
              3'b111:  begin this.m_mnemonic = "c.fsw"; end
              default: begin this.m_mnemonic = "INVALID"; end
            endcase
          end

          // C1
          2'b01: begin
            unique case (this.m_insn[15:13])
              3'b000: begin
                // c.addi -> addi rd, rd, nzimm
                // c.nop
                if(this.m_insn[11:7] == '0) begin
                  this.m_mnemonic = "c.nop";
                end else begin
                  this.m_mnemonic = "c.addi";
                end
              end
              3'b001: this.m_mnemonic = "c.jal";
              3'b101: this.m_mnemonic = "c.j";

              3'b010: begin
                if (this.m_insn[11:7] == 5'b0) begin
                    // Hint -> addi x0, x0, nzimm
                    this.m_mnemonic = "HINT";
                end else begin
                    this.m_mnemonic = "c.li";
                end
              end

              3'b011: begin
                if ({this.m_insn[12], this.m_insn[6:2]} == 6'b0) begin
                  this.m_mnemonic = "INVALID";
                end else begin
                  if (this.m_insn[11:7] == 5'h02) begin
                    // c.addi16sp -> addi x2, x2, nzimm
                    this.m_mnemonic = "c.addi16sp";
                  end else if (this.m_insn[11:7] == 5'b0) begin
                    // Hint -> lui x0, imm
                    this.m_mnemonic = "HINT";
                  end else begin
                    this.m_mnemonic = "c.lui";
                  end
                end
              end

              3'b100: begin
                unique case (this.m_insn[11:10])
                  2'b00 : begin
                    // 00: c.srli -> srli rd, rd, shamt
                    // 01: c.srai -> srai rd, rd, shamt
                    if (this.m_insn[12] == 1'b1) begin
                      // Reserved for future custom extensions (instr_o don't care)
                      this.m_mnemonic = "INVALID";
                    end else begin
                      if (this.m_insn[6:2] == 5'b0) begin
                        // Hint
                        this.m_mnemonic = "HINT";
                      end else begin
                        this.m_mnemonic = "c.srli";
                      end
                    end
                  end
                  2'b01 : begin
                    if (this.m_insn[12] == 1'b1) begin
                      // Reserved for future custom extensions (instr_o don't care)
                      this.m_mnemonic = "INVALID";
                    end else begin
                      if (this.m_insn[6:2] == 5'b0) begin
                        // Hint
                        this.m_mnemonic = "HINT";
                      end else begin
                        this.m_mnemonic = "c.srai";
                      end
                    end
                  end

                  2'b10: begin this.m_mnemonic = "c.andi"; end

                  2'b11: begin
                    unique case ({ this.m_insn[12], this.m_insn[6:5] })
                      3'b000: begin this.m_mnemonic = "c.sub"; end
                      3'b001: begin this.m_mnemonic = "c.xor"; end
                      3'b010: begin this.m_mnemonic = "c.or";  end
                      3'b011: begin this.m_mnemonic = "c.and"; end
                      3'b100 : this.m_mnemonic = "c.subw";
                      3'b101 : this.m_mnemonic = "c.addw";

                      3'b110, 3'b111: begin
                        this.m_mnemonic = "INVALID";
                      end

                    endcase
                  end
                endcase
              end

              3'b110: begin this.m_mnemonic = "c.beqz"; end
              3'b111: begin this.m_mnemonic = "c.bnez"; end
            endcase
          end

          // C2
          2'b10: begin
            unique case (this.m_insn[15:13])
              3'b000: begin
                if (this.m_insn[12] == 1'b1) begin
                  // Reserved for future extensions (instr_o don't care)
                  this.m_mnemonic = "TODO";
                end else begin
                  if ((this.m_insn[6:2] == 5'b0) || (this.m_insn[11:7] == 5'b0)) begin
                    // Hint -> slli rd, rd, shamt
                    this.m_mnemonic = "HINT";
                  end else begin
                    this.m_mnemonic = "c.slli";
                  end
                end
              end

              3'b001: begin this.m_mnemonic = "c.fldsp"; end
              3'b010: begin this.m_mnemonic = "c.lwsp";  end
              3'b011: begin this.m_mnemonic = "c.flwsp"; end

              3'b100: begin
                if (this.m_insn[12] == 1'b0) begin
                  if (this.m_insn[6:2] == 5'b0) begin
                    this.m_mnemonic = "c.jr";
                  end else begin
                    if (this.m_insn[11:7] == 5'b0) begin
                      // Hint -> add x0, x0, rs2
                      this.m_mnemonic = "HINT";
                    end else begin
                      this.m_mnemonic = "c.mv";
                    end
                  end
                end else begin
                  if (this.m_insn[6:2] == 5'b0) begin
                    if (this.m_insn[11:7] == 5'b0) begin
                      this.m_mnemonic = "c.ebreak";
                    end else begin
                      this.m_mnemonic = "c.jalr";
                    end
                  end else begin
                    if (this.m_insn[11:7] == 5'b0) begin
                      // Hint -> add x0, x0, rs2
                      this.m_mnemonic = "HINT";
                    end else begin
                      this.m_mnemonic = "c.add";
                    end
                  end
                end
              end

              3'b101: begin this.m_mnemonic = "c.fsdsp"; end
              3'b110: begin this.m_mnemonic = "c.swsp";  end
              3'b111: begin this.m_mnemonic = "c.fswsp"; end
            endcase
          end
        endcase
      end
    endfunction

    function void init_csr();
      `INIT_CSR(mstatus)
      `INIT_CSR(mstatus_fs)
      `INIT_CSR(misa)
      `INIT_CSR(mie)
      `INIT_CSR(mtvec)
      `INIT_CSR(mcountinhibit)
      `INIT_CSR(mscratch)
      `INIT_CSR(mepc)
      `INIT_CSR(mcause)
      `INIT_CSR(mcycle)
      `INIT_CSR(minstret)
      `INIT_CSR(mcycleh)
      `INIT_CSR(minstreth)
      `INIT_CSR(cycle)
      `INIT_CSR(instret)
      `INIT_CSR(cycleh)
      `INIT_CSR(instreth)
      this.m_csr.mhpmcounter_we = '0;
      this.m_csr.mhpmcounter_wmask = '0;
      this.m_csr.mhpmevent_we = '0;
      this.m_csr.mhpmevent_wmask = '0;
      `INIT_CSR(mip)
      `INIT_CSR(tdata1)
      `INIT_CSR(tdata2)
      `INIT_CSR(tinfo)
      `INIT_CSR(dcsr)
      `INIT_CSR(dpc)
      `INIT_CSR(dscratch0)
      `INIT_CSR(dscratch1)
      `INIT_CSR(mvendorid)
      `INIT_CSR(marchid)
      `INIT_CSR(fflags)
      `INIT_CSR(frm   )
      `INIT_CSR(fcsr  )
      `INIT_CSR(lpstart0 )
      `INIT_CSR(lpend0   )
      `INIT_CSR(lpcount0 )
      `INIT_CSR(lpstart1 )
      `INIT_CSR(lpend1   )
      `INIT_CSR(lpcount1 )
    endfunction
    /*
     *
     */
    function void init( insn_trace_t m_source);//logic[31:0] instr_id );
      this.m_valid            = 1'b1;
      this.m_stage            = ID;
      this.m_order            = this.m_order + 64'h1;
      this.m_start_cycle      = cycles;
      this.m_stop_cycle       = 0;
      this.m_start_time       = $time;
      this.m_stop_time        = 0;
      if(this.m_skip_order) begin
        this.m_order            = this.m_order + 64'h1;
      end
      this.m_skip_order             = 1'b0;
      this.m_pc_rdata               = r_pipe_freeze_trace.pc_id;
      this.m_is_illegal             = 1'b0;
      this.m_is_irq                 = 1'b0;
      this.m_is_memory              = 1'b0;
      this.m_is_load                = 1'b0;
      this.m_is_apu                 = 1'b0;
      this.m_is_apu_ok              = 1'b0;
      this.m_apu_req_id             = 0;
      this.m_mem_req_id[0]          = 0;
      this.m_mem_req_id[1]          = 0;
      this.m_mem_req_id_valid       = '0;
      this.m_data_missaligned       = 1'b0;
      this.m_got_first_data         = 1'b0;
      this.m_got_ex_reg             = 1'b0;
      this.m_got_regs_write         = 1'b0;
      this.m_move_down_pipe         = 1'b0;
      this.m_instret_cnt            = 0;
      this.m_instret_smaple_trigger = 0;
      this.m_sample_csr_write_in_ex = 1'b1;
      this.m_rd_addr[0]             = '0;
      this.m_rd_addr[1]             = '0;
      this.m_2_rd_insn              = 1'b0;
      this.m_rs1_addr               = '0;
      this.m_rs2_addr               = '0;
      this.m_rs3_addr               = '0;
      this.m_ex_fw                  = '0;
      this.m_csr.got_minstret       = '0;
      this.m_dbg_taken              = '0;
      this.m_trap                   = 1'b0;
      this.m_fflags_we_non_apu      = 1'b0;
      this.m_frm_we_non_apu         = 1'b0;
      this.m_fcsr_we_non_apu        = 1'b0;
      this.m_csr.mcause_we = '0;
      if (is_compressed_id_i) begin
        this.m_insn[31:16] = '0;
        this.m_insn[15:0]  = m_source.m_insn[15:0];
      end else begin
        this.m_insn = m_source.m_insn;
      end
      this.get_mnemonic();

      this.m_intr      = m_source.m_intr;
      this.m_dbg_taken = m_source.m_dbg_taken;
      this.m_dbg_cause = m_source.m_dbg_cause;
      this.m_trap      = m_source.m_trap;


      this.m_rs1_addr  = r_pipe_freeze_trace.rs1_addr_id;
      this.m_rs2_addr  = r_pipe_freeze_trace.rs2_addr_id;
      this.m_rs3_addr  = r_pipe_freeze_trace.rs3_addr_id;
      this.m_rs1_rdata = r_pipe_freeze_trace.operand_a_fw_id;
      this.m_rs2_rdata = r_pipe_freeze_trace.operand_b_fw_id;
      this.m_rs3_rdata = r_pipe_freeze_trace.operand_c_fw_id;

      this.m_mem.addr    = '0;
      this.m_mem.rmask   = '0;
      this.m_mem.wmask   = '0;
      this.m_mem.rdata   = '0;
      this.m_mem.wdata   = '0;

      init_csr();
    endfunction

    function logic [63:0] get_order_for_trap();
      // this.m_order = this.m_order + 64'h1;
      this.m_skip_order      = 1'b1;
      return (this.m_order + 64'h1);
    endfunction

    function void copy_full(insn_trace_t m_source);
      this.m_valid                  = m_source.m_valid;
      this.m_stage                  = m_source.m_stage;
      this.m_order                  = m_source.m_order;
      this.m_start_cycle            = m_source.m_start_cycle;
      this.m_stop_cycle             = m_source.m_stop_cycle;
      this.m_start_time             = m_source.m_start_time;
      this.m_stop_time              = m_source.m_stop_time;
      this.m_pc_rdata               = m_source.m_pc_rdata;
      this.m_insn                   = m_source.m_insn;
      this.m_mnemonic               = m_source.m_mnemonic;
      this.m_is_memory              = m_source.m_is_memory;
      this.m_is_load                = m_source.m_is_load;
      this.m_is_apu                 = m_source.m_is_apu;
      this.m_is_apu_ok              = m_source.m_is_apu_ok;
      this.m_apu_req_id             = m_source.m_apu_req_id;
      this.m_mem_req_id             = m_source.m_mem_req_id;
      this.m_mem_req_id_valid       = m_source.m_mem_req_id_valid;
      this.m_data_missaligned       = m_source.m_data_missaligned;
      this.m_got_first_data         = m_source.m_got_first_data;
      this.m_got_ex_reg             = m_source.m_got_ex_reg;
      this.m_dbg_taken              = m_source.m_dbg_taken;
      this.m_dbg_cause              = m_source.m_dbg_cause;
      this.m_is_ebreak              = m_source.m_is_ebreak;
      this.m_is_illegal             = m_source.m_is_illegal;
      this.m_is_irq                 = m_source.m_is_irq;
      this.m_instret_cnt            = m_source.m_instret_cnt;
      this.m_instret_smaple_trigger = m_source.m_instret_smaple_trigger;
      this.m_sample_csr_write_in_ex = m_source.m_sample_csr_write_in_ex;
      this.m_rs1_addr               = m_source.m_rs1_addr;
      this.m_rs2_addr               = m_source.m_rs2_addr;
      this.m_rs3_addr               = m_source.m_rs3_addr;
      this.m_rs1_rdata              = m_source.m_rs1_rdata;
      this.m_rs2_rdata              = m_source.m_rs2_rdata;
      this.m_rs3_rdata              = m_source.m_rs3_rdata;

      this.m_ex_fw                  = m_source.m_ex_fw;
      this.m_rd_addr                = m_source.m_rd_addr;
      this.m_2_rd_insn              = m_source.m_2_rd_insn;
      this.m_rd_wdata               = m_source.m_rd_wdata;

      this.m_intr                   = m_source.m_intr;
      this.m_trap                   = m_source.m_trap;
      this.m_fflags_we_non_apu      = m_source.m_fflags_we_non_apu;
      this.m_frm_we_non_apu         = m_source.m_frm_we_non_apu   ;
      this.m_fcsr_we_non_apu        = m_source.m_fcsr_we_non_apu;

      this.m_mem                    = m_source.m_mem;
      //CRS
      `ASSIGN_CSR(mstatus)
      `ASSIGN_CSR(mstatus_fs)
      `ASSIGN_CSR(misa)
      `ASSIGN_CSR(mie)
      `ASSIGN_CSR(mtvec)
      `ASSIGN_CSR(mcountinhibit)
      `ASSIGN_CSR(mscratch)
      `ASSIGN_CSR(mepc)
      `ASSIGN_CSR(mcause)
      `ASSIGN_CSR(mcycle)
      `ASSIGN_CSR(minstret)
      this.m_csr.got_minstret = m_source.m_csr.got_minstret;
      `ASSIGN_CSR(mcycleh)
      `ASSIGN_CSR(minstreth)
      `ASSIGN_CSR(cycle)
      `ASSIGN_CSR(instret)
      // this.m_csr.got_minstret = m_source.m_csr.got_minstret;
      `ASSIGN_CSR(cycleh)
      `ASSIGN_CSR(instreth)
      this.m_csr.mhpmcounter_we = m_source.m_csr.mhpmcounter_we;
      this.m_csr.mhpmcounter_rdata = m_source.m_csr.mhpmcounter_rdata;
      this.m_csr.mhpmcounter_rmask = m_source.m_csr.mhpmcounter_rmask;
      this.m_csr.mhpmcounter_wdata = m_source.m_csr.mhpmcounter_wdata;
      this.m_csr.mhpmcounter_wmask = m_source.m_csr.mhpmcounter_wmask;
      this.m_csr.mhpmevent_we = m_source.m_csr.mhpmevent_we;
      this.m_csr.mhpmevent_rdata = m_source.m_csr.mhpmevent_rdata;
      this.m_csr.mhpmevent_rmask = m_source.m_csr.mhpmevent_rmask;
      this.m_csr.mhpmevent_wdata = m_source.m_csr.mhpmevent_wdata;
      this.m_csr.mhpmevent_wmask = m_source.m_csr.mhpmevent_wmask;
      `ASSIGN_CSR(mip)
      `ASSIGN_CSR(tdata1)
      `ASSIGN_CSR(tdata2)
      `ASSIGN_CSR(tinfo)
      `ASSIGN_CSR(dcsr)
      `ASSIGN_CSR(dpc)
      `ASSIGN_CSR(dscratch0)
      `ASSIGN_CSR(dscratch1)
      `ASSIGN_CSR(mvendorid)
      `ASSIGN_CSR(marchid)

      `ASSIGN_CSR(fflags)
      `ASSIGN_CSR(frm   )
      `ASSIGN_CSR(fcsr  )

      `ASSIGN_CSR(lpstart0)
      `ASSIGN_CSR(lpend0  )
      `ASSIGN_CSR(lpcount0)
      `ASSIGN_CSR(lpstart1)
      `ASSIGN_CSR(lpend1  )
      `ASSIGN_CSR(lpcount1)

    endfunction

    function void move_down_pipe(insn_trace_t m_source);
      this.copy_full(m_source);
      case(this.m_stage)
        IF : this.m_stage = ID;
        ID : this.m_stage = EX;
        EX : this.m_stage = WB;
        WB : this.m_stage = WB_2;
        APU: this.m_stage = APU;
      endcase
    endfunction

    function void set_to_apu();
      this.m_stage = APU;
    endfunction
  endclass
