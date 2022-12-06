// Copyright 2022 Dolphin Design
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

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

  class insn_trace_t;
    bit m_valid;
    logic [63:0] m_order;
    logic [31:0] m_pc_rdata;
    logic [31:0] m_insn;
    logic        m_is_ebreak;
    logic m_data_missaligned;
    logic m_got_first_data;
    logic       m_dbg_taken;
    logic [2:0] m_dbg_cause;
    logic [4:0] m_rs1_addr;
    logic [4:0] m_rs2_addr;
    logic [31:0] m_rs1_rdata;
    logic [31:0] m_rs2_rdata;

    logic [31:0] mem_addr;
    logic [3:0] mem_rmask;
    logic [3:0] mem_wmask;
    logic [31:0] mem_rdata;
    logic [31:0] mem_wdata;

    bit m_got_regs_write;
    bit m_ex_fw;
    logic [4:0] m_rd_addr;
    logic [31:0] m_rd_wdata;

    rvfi_intr_t m_intr;

    bit m_move_down_pipe;

    struct {
      `DEFINE_CSR(mstatus)

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
      `DEFINE_CSR(minstret)
      bit got_minstret;

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
    } m_csr;

    enum logic[2:0] {
      IF, ID, EX, WB, WB_2
    } m_stage;


    function new();
      this.m_order            = 0;
      this.m_valid            = 1'b0;
      this.m_move_down_pipe   = 1'b0;
      this.m_data_missaligned = 1'b0;
      this.m_got_first_data   = 1'b0;
      this.m_intr             = '0;
      this.m_dbg_taken        = 1'b0;
      this.m_dbg_cause        = '0;
      this.m_is_ebreak        = '0;
    endfunction

    /*
     *
     */
    function void init( logic[31:0] instr_id );
      this.m_valid            = 1'b1;
      this.m_stage            = ID;
      this.m_order            = this.m_order + 64'h1;
      this.m_pc_rdata         = r_pipe_freeze.pc_id;
      this.m_data_missaligned = 1'b0;
      this.m_got_first_data   = 1'b0;
      this.m_got_regs_write   = 1'b0;
      this.m_move_down_pipe   = 1'b0;
      this.m_rd_addr          = '0;
      this.m_rs1_addr         = '0;
      this.m_rs2_addr         = '0;
      this.m_ex_fw            = '0;
      this.m_csr.got_minstret = '0;
      this.m_dbg_taken        = '0;

      this.m_csr.mcause_we = '0;
      if (is_compressed_id_i) begin
        this.m_insn[31:16] = '0;
        this.m_insn[15:0]  = instr_id[15:0];
      end else begin
        this.m_insn = instr_id;
      end

      this.m_rs1_addr  = r_pipe_freeze.rs1_addr_id;
      this.m_rs2_addr  = r_pipe_freeze.rs2_addr_id;
      this.m_rs1_rdata = r_pipe_freeze.operand_a_fw_id;
      this.m_rs2_rdata = r_pipe_freeze.operand_b_fw_id;

      this.mem_addr    = '0;
      this.mem_rmask   = '0;
      this.mem_wmask   = '0;
      this.mem_rdata   = '0;
      this.mem_wdata   = '0;
    endfunction

    function void copy_full(insn_trace_t m_source);
      this.m_valid              = m_source.m_valid;
      this.m_stage              = m_source.m_stage;
      this.m_order              = m_source.m_order;
      this.m_pc_rdata           = m_source.m_pc_rdata;
      this.m_insn               = m_source.m_insn;
      this.m_data_missaligned   = m_source.m_data_missaligned;
      this.m_got_first_data     = m_source.m_got_first_data;
      this.m_dbg_taken          = m_source.m_dbg_taken;
      this.m_dbg_cause          = m_source.m_dbg_cause;
      this.m_is_ebreak          = m_source.m_is_ebreak;
      this.m_rs1_addr           = m_source.m_rs1_addr;
      this.m_rs2_addr           = m_source.m_rs2_addr;
      this.m_rs1_rdata          = m_source.m_rs1_rdata;
      this.m_rs2_rdata          = m_source.m_rs2_rdata;

      this.m_ex_fw              = m_source.m_ex_fw;
      this.m_rd_addr            = m_source.m_rd_addr;
      this.m_rd_wdata           = m_source.m_rd_wdata;

      this.m_intr               = m_source.m_intr;

      //CRS
      `ASSIGN_CSR(mstatus)
      `ASSIGN_CSR(misa)
      `ASSIGN_CSR(mie)
      `ASSIGN_CSR(mtvec)
      `ASSIGN_CSR(mcountinhibit)
      `ASSIGN_CSR(mscratch)
      `ASSIGN_CSR(mepc)
      `ASSIGN_CSR(mcause)
      `ASSIGN_CSR(minstret)
      this.m_csr.got_minstret = m_source.m_csr.got_minstret;
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

    endfunction

    function void move_down_pipe(insn_trace_t m_source);
      this.copy_full(m_source);
      case(this.m_stage)
        IF: this.m_stage = ID;
        ID: this.m_stage = EX;
        EX: this.m_stage = WB;
        WB: this.m_stage = WB_2;
      endcase
    endfunction
  endclass
