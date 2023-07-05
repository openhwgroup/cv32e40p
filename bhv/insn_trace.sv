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
    bit          m_skip_order; //next order was used by trap;
    logic [31:0] m_pc_rdata;
    logic [31:0] m_insn;
    logic        m_is_ebreak;
    logic        m_is_illegal;
    logic        m_is_irq;
    logic        m_is_memory;
    logic        m_is_load;
    logic        m_is_apu;
    logic        m_is_apu_ok;
    integer      m_apu_req_id;
    integer      m_mem_req_id[1:0];
    logic        m_data_missaligned;
    logic        m_got_first_data;
    logic        m_got_ex_reg;
    logic       m_dbg_taken;
    logic [2:0] m_dbg_cause;

    logic       m_fflags_we_non_apu;
    logic       m_frm_we_non_apu;
    logic [5:0] m_rs1_addr;
    logic [5:0] m_rs2_addr;
    logic [31:0] m_rs1_rdata;
    logic [31:0] m_rs2_rdata;

    bit m_trap;

    bit m_got_regs_write;
    bit m_ex_fw;
    logic [ 5:0] m_rd_addr [1:0];
    logic [31:0] m_rd_wdata[1:0];
    logic        m_2_rd_insn; //this instruction uses 2 destination registers
    rvfi_intr_t m_intr;

    bit m_move_down_pipe;

    int m_instret_cnt;

    struct {
      logic [31:0] addr ;
      logic [ 3:0] rmask;
      logic [31:0] rdata;
      logic [ 3:0] wmask;
      logic [31:0] wdata;
    } m_mem;

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
      this.m_order             = 0;
      this.m_skip_order        = 1'b0;
      this.m_valid             = 1'b0;
      this.m_move_down_pipe    = 1'b0;
      this.m_data_missaligned  = 1'b0;
      this.m_got_first_data    = 1'b0;
      this.m_got_ex_reg        = 1'b0;
      this.m_intr              = '0;
      this.m_dbg_taken         = 1'b0;
      this.m_dbg_cause         = '0;
      this.m_is_ebreak         = '0;
      this.m_is_illegal        = '0;
      this.m_is_irq            = '0;
      this.m_is_memory         = 1'b0;
      this.m_is_load           = 1'b0;
      this.m_is_apu            = 1'b0;
      this.m_is_apu_ok         = 1'b0;
      this.m_apu_req_id        = 0;
      this.m_mem_req_id[0]     = 0;
      this.m_mem_req_id[1]     = 0;
      this.m_trap              = 1'b0;
      this.m_fflags_we_non_apu = 1'b0;
      this.m_frm_we_non_apu    = 1'b0;
      this.m_instret_cnt       = 0;
    endfunction

    /*
     *
     */
    function void init( insn_trace_t m_source);//logic[31:0] instr_id );
      this.m_valid            = 1'b1;
      this.m_stage            = ID;
      this.m_order            = this.m_order + 64'h1;
      if(this.m_skip_order) begin
        this.m_order            = this.m_order + 64'h1;
      end
      this.m_skip_order        = 1'b0;
      this.m_pc_rdata          = r_pipe_freeze_trace.pc_id;
      this.m_is_illegal        = 1'b0;
      this.m_is_irq            = 1'b0;
      this.m_is_memory         = 1'b0;
      this.m_is_load           = 1'b0;
      this.m_is_apu            = 1'b0;
      this.m_is_apu_ok         = 1'b0;
      this.m_apu_req_id        = 0;
      this.m_mem_req_id[0]     = 0;
      this.m_mem_req_id[1]     = 0;
      this.m_data_missaligned  = 1'b0;
      this.m_got_first_data    = 1'b0;
      this.m_got_ex_reg        = 1'b0;
      this.m_got_regs_write    = 1'b0;
      this.m_move_down_pipe    = 1'b0;
      this.m_instret_cnt       = 0;
      this.m_rd_addr[0]        = '0;
      this.m_rd_addr[1]        = '0;
      this.m_2_rd_insn         = 1'b0;
      this.m_rs1_addr          = '0;
      this.m_rs2_addr          = '0;
      this.m_ex_fw             = '0;
      this.m_csr.got_minstret  = '0;
      this.m_dbg_taken         = '0;
      this.m_trap              = 1'b0;
      this.m_fflags_we_non_apu = 1'b0;
      this.m_frm_we_non_apu    = 1'b0;
      this.m_csr.mcause_we = '0;
      if (is_compressed_id_i) begin
        this.m_insn[31:16] = '0;
        this.m_insn[15:0]  = m_source.m_insn[15:0];
      end else begin
        this.m_insn = m_source.m_insn;
      end

      this.m_intr      = m_source.m_intr;
      this.m_dbg_taken = m_source.m_dbg_taken;
      this.m_dbg_cause = m_source.m_dbg_cause;
      this.m_trap      = m_source.m_trap;


      this.m_rs1_addr  = r_pipe_freeze_trace.rs1_addr_id;
      this.m_rs2_addr  = r_pipe_freeze_trace.rs2_addr_id;
      this.m_rs1_rdata = r_pipe_freeze_trace.operand_a_fw_id;
      this.m_rs2_rdata = r_pipe_freeze_trace.operand_b_fw_id;

      this.m_mem.addr    = '0;
      this.m_mem.rmask   = '0;
      this.m_mem.wmask   = '0;
      this.m_mem.rdata   = '0;
      this.m_mem.wdata   = '0;
    endfunction

    function logic [63:0] get_order_for_trap();
      // this.m_order = this.m_order + 64'h1;
      this.m_skip_order      = 1'b1;
      return (this.m_order + 64'h1);
    endfunction

    function void copy_full(insn_trace_t m_source);
      this.m_valid              = m_source.m_valid;
      this.m_stage              = m_source.m_stage;
      this.m_order              = m_source.m_order;
      this.m_pc_rdata           = m_source.m_pc_rdata;
      this.m_insn               = m_source.m_insn;
      this.m_is_memory          = m_source.m_is_memory;
      this.m_is_load            = m_source.m_is_load;
      this.m_is_apu             = m_source.m_is_apu;
      this.m_is_apu_ok          = m_source.m_is_apu_ok;
      this.m_apu_req_id         = m_source.m_apu_req_id;
      this.m_mem_req_id         = m_source.m_mem_req_id;
      this.m_data_missaligned   = m_source.m_data_missaligned;
      this.m_got_first_data     = m_source.m_got_first_data;
      this.m_got_ex_reg         = m_source.m_got_ex_reg;
      this.m_dbg_taken          = m_source.m_dbg_taken;
      this.m_dbg_cause          = m_source.m_dbg_cause;
      this.m_is_ebreak          = m_source.m_is_ebreak;
      this.m_is_illegal         = m_source.m_is_illegal;
      this.m_is_irq             = m_source.m_is_irq;
      this.m_instret_cnt        = m_source.m_instret_cnt;
      this.m_rs1_addr           = m_source.m_rs1_addr;
      this.m_rs2_addr           = m_source.m_rs2_addr;
      this.m_rs1_rdata          = m_source.m_rs1_rdata;
      this.m_rs2_rdata          = m_source.m_rs2_rdata;

      this.m_ex_fw              = m_source.m_ex_fw;
      this.m_rd_addr            = m_source.m_rd_addr;
      this.m_2_rd_insn          = m_source.m_2_rd_insn;
      this.m_rd_wdata           = m_source.m_rd_wdata;

      this.m_intr               = m_source.m_intr;
      this.m_trap               = m_source.m_trap;
      this.m_fflags_we_non_apu  = m_source.m_fflags_we_non_apu;
      this.m_frm_we_non_apu     = m_source.m_frm_we_non_apu   ;

      this.m_mem                = m_source.m_mem;
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
