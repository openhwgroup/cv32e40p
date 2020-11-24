// Copyright 2020 Silicon Labs, Inc.
//
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License").
//
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
//
// You may obtain a copy of the License at:
//
//     https://solderpad.org/licenses/SHL-2.0/
//
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof distributed under the License
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS
// OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
//
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Steve Richmond - steve.richmond@silabs.com                 //
//                                                                            //
// Design Name:    cv32e40p_tracer data structures                            //
// Project Name:   CV32E40P                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Moves the class definition for instr_trace_t out of the    //
//                 tracer module for readability and code partitioning        //
//                                                                            //
//                 Includes various enhancements to make the instr_trace_t    //
//                 class more comprehensive                                   //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

  typedef struct {
    logic [ 5:0] addr;
    logic [31:0] value;
    bit          filled;
  } reg_t;

  typedef struct {
    logic [31:0] addr;
    logic        we;
    logic [ 3:0] be;
    logic [31:0] wdata;
    logic [31:0] rdata;
  } mem_acc_t;

  class instr_trace_t;
    time         simtime;
    int          cycles;
    logic [31:0] pc;
    logic [31:0] instr;
    bit          compressed;
    bit          wb_bypass;
    bit          misaligned;
    bit          retire;
    bit          ebreak;
    string       str;
    reg_t        regs_read[$];
    reg_t        regs_write[$];
    mem_acc_t    mem_access[$];
    logic        retired;

    function new ();
      str        = "";
      regs_read  = {};
      regs_write = {};
      mem_access = {};
    endfunction

    function void init(int unsigned cycles, bit[31:0] pc, bit compressed, bit[31:0] instr);
      this.simtime    = $time;
      this.cycles     = cycles;
      this.pc         = pc;
      this.compressed = compressed;
      this.instr      = instr;

      // use casex instead of case inside due to ModelSim bug
      casex (instr)
        // Aliases
        32'h00_00_00_13:   this.printMnemonic("nop");
        // Regular opcodes
        INSTR_LUI:        this.printUInstr("lui");
        INSTR_AUIPC:      this.printUInstr("auipc");
        INSTR_JAL:        this.printUJInstr("jal");
        INSTR_JALR:       this.printIInstr("jalr");
        // BRANCH
        INSTR_BEQ:        this.printSBInstr("beq");
        INSTR_BNE:        this.printSBInstr("bne");
        INSTR_BLT:        this.printSBInstr("blt");
        INSTR_BGE:        this.printSBInstr("bge");
        INSTR_BLTU:       this.printSBInstr("bltu");
        INSTR_BGEU:       this.printSBInstr("bgeu");
        INSTR_BEQIMM:     this.printSBallInstr("p.beqimm");
        INSTR_BNEIMM:     this.printSBallInstr("p.bneimm");
        // OPIMM
        INSTR_ADDI:       this.printIInstr("addi");
        INSTR_SLTI:       this.printIInstr("slti");
        INSTR_SLTIU:      this.printIInstr("sltiu");
        INSTR_XORI:       this.printIInstr("xori");
        INSTR_ORI:        this.printIInstr("ori");
        INSTR_ANDI:       this.printIInstr("andi");
        INSTR_SLLI:       this.printIuInstr("slli");
        INSTR_SRLI:       this.printIuInstr("srli");
        INSTR_SRAI:       this.printIuInstr("srai");
        // OP
        INSTR_ADD:        this.printRInstr("add");
        INSTR_SUB:        this.printRInstr("sub");
        INSTR_SLL:        this.printRInstr("sll");
        INSTR_SLT:        this.printRInstr("slt");
        INSTR_SLTU:       this.printRInstr("sltu");
        INSTR_XOR:        this.printRInstr("xor");
        INSTR_SRL:        this.printRInstr("srl");
        INSTR_SRA:        this.printRInstr("sra");
        INSTR_OR:         this.printRInstr("or");
        INSTR_AND:        this.printRInstr("and");
        INSTR_EXTHS:      this.printRInstr("p.exths");
        INSTR_EXTHZ:      this.printRInstr("p.exthz");
        INSTR_EXTBS:      this.printRInstr("p.extbs");
        INSTR_EXTBZ:      this.printRInstr("p.extbz");
        INSTR_PAVG:       this.printRInstr("p.avg");
        INSTR_PAVGU:      this.printRInstr("p.avgu");

        INSTR_PADDN:      this.printAddNInstr("p.addN");
        INSTR_PADDUN:     this.printAddNInstr("p.adduN");
        INSTR_PADDRN:     this.printAddNInstr("p.addRN");
        INSTR_PADDURN:    this.printAddNInstr("p.adduRN");
        INSTR_PSUBN:      this.printAddNInstr("p.subN");
        INSTR_PSUBUN:     this.printAddNInstr("p.subuN");
        INSTR_PSUBRN:     this.printAddNInstr("p.subRN");
        INSTR_PSUBURN:    this.printAddNInstr("p.subuRN");

        INSTR_PADDNR:     this.printR3Instr("p.addNr");
        INSTR_PADDUNR:    this.printR3Instr("p.adduNr");
        INSTR_PADDRNR:    this.printR3Instr("p.addRNr");
        INSTR_PADDURNR:   this.printR3Instr("p.adduRNr");
        INSTR_PSUBNR:     this.printR3Instr("p.subNr");
        INSTR_PSUBUNR:    this.printR3Instr("p.subuNr");
        INSTR_PSUBRNR:    this.printR3Instr("p.subRNr");
        INSTR_PSUBURNR:   this.printR3Instr("p.subuRNr");

        INSTR_PSLET:      this.printRInstr("p.slet");
        INSTR_PSLETU:     this.printRInstr("p.sletu");
        INSTR_PMIN:       this.printRInstr("p.min");
        INSTR_PMINU:      this.printRInstr("p.minu");
        INSTR_PMAX:       this.printRInstr("p.max");
        INSTR_PMAXU:      this.printRInstr("p.maxu");
        INSTR_PABS:       this.printR1Instr("p.abs");
        INSTR_PCLIP:      this.printClipInstr("p.clip");
        INSTR_PCLIPU:     this.printClipInstr("p.clipu");
        INSTR_PBEXT:      this.printBit1Instr("p.extract");
        INSTR_PBEXTU:     this.printBit1Instr("p.extractu");
        INSTR_PBINS:      this.printBit2Instr("p.insert");
        INSTR_PBCLR:      this.printBit1Instr("p.bclr");
        INSTR_PBSET:      this.printBit1Instr("p.bset");
        INSTR_PBREV:      this.printBitRevInstr("p.bitrev");

        INSTR_PCLIPR:     this.printRInstr("p.clipr");
        INSTR_PCLIPUR:    this.printRInstr("p.clipur");
        INSTR_PBEXTR:     this.printRInstr("p.extractr");
        INSTR_PBEXTUR:    this.printRInstr("p.extractur");
        INSTR_PBINSR:     this.printR3Instr("p.insertr");
        INSTR_PBCLRR:     this.printRInstr("p.bclrr");
        INSTR_PBSETR:     this.printRInstr("p.bsetr");


        INSTR_FF1:        this.printR1Instr("p.ff1");
        INSTR_FL1:        this.printR1Instr("p.fl1");
        INSTR_CLB:        this.printR1Instr("p.clb");
        INSTR_CNT:        this.printR1Instr("p.cnt");
        INSTR_ROR:        this.printRInstr("p.ror");

        // FENCE
        INSTR_FENCE:      this.printMnemonic("fence");
        INSTR_FENCEI:     this.printMnemonic("fencei");
        // SYSTEM (CSR manipulation)
        INSTR_CSRRW:      this.printCSRInstr("csrrw");
        INSTR_CSRRS:      this.printCSRInstr("csrrs");
        INSTR_CSRRC:      this.printCSRInstr("csrrc");
        INSTR_CSRRWI:     this.printCSRInstr("csrrwi");
        INSTR_CSRRSI:     this.printCSRInstr("csrrsi");
        INSTR_CSRRCI:     this.printCSRInstr("csrrci");
        // SYSTEM (others)
        INSTR_ECALL:      this.printMnemonic("ecall");
        INSTR_EBREAK:     this.printMnemonic("ebreak");
        INSTR_URET:       this.printMnemonic("uret");
        INSTR_MRET:       this.printMnemonic("mret");
        INSTR_WFI:        this.printMnemonic("wfi");

        INSTR_DRET:       this.printMnemonic("dret");

        // RV32M
        INSTR_PMUL:       this.printRInstr("mul");
        INSTR_PMUH:       this.printRInstr("mulh");
        INSTR_PMULHSU:    this.printRInstr("mulhsu");
        INSTR_PMULHU:     this.printRInstr("mulhu");
        INSTR_DIV:        this.printRInstr("div");
        INSTR_DIVU:       this.printRInstr("divu");
        INSTR_REM:        this.printRInstr("rem");
        INSTR_REMU:       this.printRInstr("remu");
        // PULP MULTIPLIER
        INSTR_PMAC:       this.printR3Instr("p.mac");
        INSTR_PMSU:       this.printR3Instr("p.msu");
        INSTR_PMULS     : this.printMulInstr();
        INSTR_PMULHLSN  : this.printMulInstr();
        INSTR_PMULRS    : this.printMulInstr();
        INSTR_PMULRHLSN : this.printMulInstr();
        INSTR_PMULU     : this.printMulInstr();
        INSTR_PMULUHLU  : this.printMulInstr();
        INSTR_PMULRU    : this.printMulInstr();
        INSTR_PMULRUHLU : this.printMulInstr();
        INSTR_PMACS     : this.printMulInstr();
        INSTR_PMACHLSN  : this.printMulInstr();
        INSTR_PMACRS    : this.printMulInstr();
        INSTR_PMACRHLSN : this.printMulInstr();
        INSTR_PMACU     : this.printMulInstr();
        INSTR_PMACUHLU  : this.printMulInstr();
        INSTR_PMACRU    : this.printMulInstr();
        INSTR_PMACRUHLU : this.printMulInstr();

        // FP-OP
        INSTR_FMADD:      this.printF3Instr("fmadd.s");
        INSTR_FMSUB:      this.printF3Instr("fmsub.s");
        INSTR_FNMADD:     this.printF3Instr("fnmadd.s");
        INSTR_FNMSUB:     this.printF3Instr("fnmsub.s");
        INSTR_FADD:       this.printF2Instr("fadd.s");
        INSTR_FSUB:       this.printF2Instr("fsub.s");
        INSTR_FMUL:       this.printF2Instr("fmul.s");
        INSTR_FDIV:       this.printF2Instr("fdiv.s");
        INSTR_FSQRT:      this.printFInstr("fsqrt.s");
        INSTR_FSGNJS:     this.printF2Instr("fsgnj.s");
        INSTR_FSGNJNS:    this.printF2Instr("fsgnjn.s");
        INSTR_FSGNJXS:    this.printF2Instr("fsgnjx.s");
        INSTR_FMIN:       this.printF2Instr("fmin.s");
        INSTR_FMAX:       this.printF2Instr("fmax.s");
        INSTR_FCVTWS:     this.printFIInstr("fcvt.w.s");
        INSTR_FCVTWUS:    this.printFIInstr("fcvt.wu.s");
        INSTR_FMVXS:      this.printFIInstr("fmv.x.s");
        INSTR_FEQS:       this.printF2IInstr("feq.s");
        INSTR_FLTS:       this.printF2IInstr("flt.s");
        INSTR_FLES:       this.printF2IInstr("fle.s");
        INSTR_FCLASS:     this.printFIInstr("fclass.s");
        INSTR_FCVTSW:     this.printIFInstr("fcvt.s.w");
        INSTR_FCVTSWU:    this.printIFInstr("fcvt.s.wu");
        INSTR_FMVSX:      this.printIFInstr("fmv.s.x");

        // RV32A
        INSTR_LR:         this.printAtomicInstr("lr.w");
        INSTR_SC:         this.printAtomicInstr("sc.w");
        INSTR_AMOSWAP:    this.printAtomicInstr("amoswap.w");
        INSTR_AMOADD:     this.printAtomicInstr("amoadd.w");
        INSTR_AMOXOR:     this.printAtomicInstr("amoxor.w");
        INSTR_AMOAND:     this.printAtomicInstr("amoand.w");
        INSTR_AMOOR:      this.printAtomicInstr("amoor.w");
        INSTR_AMOMIN:     this.printAtomicInstr("amomin.w");
        INSTR_AMOMAX:     this.printAtomicInstr("amomax.w");
        INSTR_AMOMINU:    this.printAtomicInstr("amominu.w");
        INSTR_AMOMAXU:    this.printAtomicInstr("amomaxu.w");

        // opcodes with custom decoding
        {25'b?, OPCODE_LOAD}:       this.printLoadInstr();
        {25'b?, OPCODE_LOAD_FP}:    this.printLoadInstr();
        {25'b?, OPCODE_LOAD_POST}:  this.printLoadInstr();
        {25'b?, OPCODE_STORE}:      this.printStoreInstr();
        {25'b?, OPCODE_STORE_FP}:   this.printStoreInstr();
        {25'b?, OPCODE_STORE_POST}: this.printStoreInstr();
        {25'b?, OPCODE_HWLOOP}:     this.printHwloopInstr();
        {25'b?, OPCODE_VECOP}:      this.printVecInstr();
        default: this.printMnemonic("INVALID");
      endcase // unique case (instr)

    endfunction : init

    function bit is_regs_write_done();
      foreach (regs_write[i])
        if (regs_write[i].value === 'x)
          return 0;

      return 1;
    endfunction : is_regs_write_done

    function string regAddrToStr(input logic [5:0] addr);
      begin
        if (SymbolicRegs) begin // format according to RISC-V ABI
          if (addr >= 42)
            return $sformatf(" f%0d", addr-32);
          else if (addr > 32)
            return $sformatf("  f%0d", addr-32);
          else begin
            if (addr == 0)
              return $sformatf("zero");
            else if (addr == 1)
              return $sformatf("  ra");
            else if (addr == 2)
              return $sformatf("  sp");
            else if (addr == 3)
              return $sformatf("  gp");
            else if (addr == 4)
              return $sformatf("  tp");
            else if (addr >= 5 && addr <= 7)
              return $sformatf("  t%0d", addr-5);
            else if (addr >= 8 && addr <= 9)
              return $sformatf("  s%0d", addr-8);
            else if (addr >= 10 && addr <= 17)
              return $sformatf("  a%0d", addr-10);
            else if (addr >= 18 && addr <= 25)
              return $sformatf("  s%0d", addr-16);
            else if (addr >= 26 && addr <= 27)
              return $sformatf(" s%0d", addr-16);
            else if (addr >= 28 && addr <= 31)
              return $sformatf("  t%0d", addr-25);
            else
              return $sformatf("UNKNOWN %0d", addr);
          end
        end else begin
          if (addr >= 42)
            return $sformatf("f%0d", addr-32);
          else if (addr > 32)
            return $sformatf(" f%0d", addr-32);
          else if (addr < 10)
            return $sformatf(" x%0d", addr);
          else
            return $sformatf("x%0d", addr);
        end
      end
    endfunction

    function void printInstrTrace();
      mem_acc_t mem_acc;
      begin
        string insn_str;  // Accumulate writes into a single string to enable single $fwrite

        insn_str = $sformatf("%t %15d %h %h %-36s", simtime,
                                                    cycles,
                                                    pc,
                                                    instr,
                                                    str);

        foreach(regs_write[i]) begin
          if (regs_write[i].addr != 0)
            insn_str = $sformatf("%s %s=%08x", insn_str, regAddrToStr(regs_write[i].addr), regs_write[i].value);
        end

        foreach(regs_read[i]) begin
          if (regs_read[i].addr != 0)
            insn_str = $sformatf("%s %s:%08x", insn_str, regAddrToStr(regs_read[i].addr), regs_read[i].value);
        end

        if (mem_access.size() > 0) begin
          mem_acc = mem_access.pop_front();

          insn_str = $sformatf("%s  PA:%08x", insn_str, mem_acc.addr);
        end

        $fwrite(f, "%s\n", insn_str);
      end
    endfunction

    function void printMnemonic(input string mnemonic);
      begin
        str = {compressed ? "c." : "", mnemonic};
      end
    endfunction // printMnemonic

    function void printRInstr(input string mnemonic);
      begin
        mnemonic = {compressed ? "c." : "", mnemonic};
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_read.push_back('{rs2, rs2_value,0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s x%0d, x%0d, x%0d", mnemonic, rd, rs1, rs2);
      end
    endfunction // printRInstr

    function void printAddNInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_read.push_back('{rs2, rs2_value,0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s x%0d, x%0d, x%0d, 0x%0d", mnemonic, rd, rs1, rs2, $unsigned(imm_s3_type[4:0]));
      end
    endfunction // printAddNInstr

    function void printR1Instr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s x%0d, x%0d", mnemonic, rd, rs1);
      end
    endfunction // printR1Instr

    function void printR3Instr(input string mnemonic);
      begin
        regs_read.push_back('{rd, rs3_value, 0});
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_read.push_back('{rs2, rs2_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s x%0d, x%0d, x%0d", mnemonic, rd, rs1, rs2);
      end
    endfunction // printR3Instr

    function void printF3Instr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_read.push_back('{rs2, rs2_value, 0});
        regs_read.push_back('{rs4, rs3_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s f%0d, f%0d, f%0d, f%0d", mnemonic, rd-32, rs1-32, rs2-32, rs4-32);
      end
    endfunction // printF3Instr

    function void printF2Instr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_read.push_back('{rs2, rs2_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s f%0d, f%0d, f%0d", mnemonic, rd-32, rs1-32, rs2-32);
      end
    endfunction // printF2Instr

    function void printF2IInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_read.push_back('{rs2, rs2_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s x%0d, f%0d, f%0d", mnemonic, rd, rs1-32, rs2-32);
      end
    endfunction // printF2IInstr

    function void printFInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s f%0d, f%0d", mnemonic, rd-32, rs1-32);
      end
    endfunction // printFInstr

    function void printFIInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s x%0d, f%0d", mnemonic, rd, rs1-32);
      end
    endfunction // printFIInstr

    function void printIFInstr(input string mnemonic);
      begin
        mnemonic = {compressed ? "c." : "", mnemonic};
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s f%0d, x%0d", mnemonic, rd-32, rs1);
      end
    endfunction // printIFInstr

    function void printClipInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s x%0d, x%0d, %0d", mnemonic, rd, rs1, $unsigned(imm_clip_type));
      end
    endfunction // printRInstr

    function void printIInstr(input string mnemonic);
      begin
        mnemonic = {compressed ? "c." : "", mnemonic};
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s x%0d, x%0d, %0d", mnemonic, rd, rs1, $signed(imm_i_type));
      end
    endfunction // printIInstr

    function void printIuInstr(input string mnemonic);
      begin
        mnemonic = {compressed ? "c." : "", mnemonic};
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s x%0d, x%0d, 0x%0x", mnemonic, rd, rs1, imm_i_type);
      end
    endfunction // printIuInstr

    function void printUInstr(input string mnemonic);
      begin
        mnemonic = {compressed ? "c." : "", mnemonic};
        regs_write.push_back('{rd, 'x, 0});
        str = $sformatf("%-16s x%0d, 0x%0h", mnemonic, rd, {imm_u_type[31:12], 12'h000});
      end
    endfunction // printUInstr

    function void printUJInstr(input string mnemonic);
      begin
        mnemonic = {compressed ? "c." : "", mnemonic};
        regs_write.push_back('{rd, 'x, 0});
        str =  $sformatf("%-16s x%0d, %0d", mnemonic, rd, $signed(imm_uj_type));
      end
    endfunction // printUJInstr

    function void printSBInstr(input string mnemonic);
      begin
        mnemonic = {compressed ? "c." : "", mnemonic};
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_read.push_back('{rs2, rs2_value, 0});
        str =  $sformatf("%-16s x%0d, x%0d, %0d", mnemonic, rs1, rs2, $signed(imm_sb_type));
      end
    endfunction // printSBInstr

    function void printSBallInstr(input string mnemonic);
      begin
        mnemonic = {compressed ? "c." : "", mnemonic};
        regs_read.push_back('{rs1, rs1_value, 0});
        str =  $sformatf("%-16s x%0d, %0d", mnemonic, rs1, $signed(imm_sb_type));
      end
    endfunction // printSBInstr

    function void printCSRInstr(input string mnemonic);
      logic [11:0] csr;
      begin
        csr = instr[31:20];

        regs_write.push_back('{rd, 'x, 0});

        if (instr[14] == 1'b0) begin
          regs_read.push_back('{rs1, rs1_value, 0});
          str = $sformatf("%-16s x%0d, x%0d, 0x%h", mnemonic, rd, rs1, csr);
        end else begin
          str = $sformatf("%-16s x%0d, 0x%h, 0x%h", mnemonic, rd, imm_z_type, csr);
        end
      end
    endfunction // printCSRInstr

    function void printBit1Instr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str =  $sformatf("%-16s x%0d, x%0d, %0d, %0d", mnemonic, rd, rs1, imm_s3_type, imm_s2_type);
      end
    endfunction

    function void printBitRevInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str =  $sformatf("%-16s x%0d, x%0d, %0d, %0d", mnemonic, rd, rs1, imm_s2_type, imm_s3_type);
      end
    endfunction

    function void printBit2Instr(input string mnemonic);
      begin
        regs_read.push_back('{rd, rs3_value, 0});
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_write.push_back('{rd, 'x, 0});
        str =  $sformatf("%-16s x%0d, x%0d, %0d, %0d", mnemonic, rd, rs1, imm_s3_type, imm_s2_type);
      end
    endfunction

    function void printAtomicInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_read.push_back('{rs2, rs2_value,0});
        regs_write.push_back('{rd, 'x, 0});
        if (instr[31:27] == AMO_LR) begin
          // Do not print rs2 for load-reserved
          str = $sformatf("%-16s x%0d, (x%0d)", mnemonic, rd, rs1);
        end else begin
          str = $sformatf("%-16s x%0d, x%0d, (x%0d)", mnemonic, rd, rs2, rs1);
        end
      end
    endfunction // printAtomicInstr

    function void printLoadInstr();
      string mnemonic;
      logic [2:0] size;
      begin
        // detect reg-reg load and find size
        size = instr[14:12];
        if (instr[14:12] == 3'b111)
          size = instr[30:28];

        case (size)
          3'b000: mnemonic = "lb";
          3'b001: mnemonic = "lh";
          3'b010: mnemonic = "lw";
          3'b100: mnemonic = "lbu";
          3'b101: mnemonic = "lhu";
          3'b110: mnemonic = "p.elw";
          3'b011,
          3'b111: begin
            printMnemonic("INVALID");
            return;
          end
        endcase
        mnemonic = {compressed ? "c." : "", mnemonic};

        regs_write.push_back('{rd, 'x, 0});

        if (instr[14:12] != 3'b111) begin
          // regular load
          if (instr[6:0] != OPCODE_LOAD_POST) begin
            regs_read.push_back('{rs1, rs1_value, 0});
            str = $sformatf("%-16s x%0d, %0d(x%0d)", mnemonic, rd, $signed(imm_i_type), rs1);
          end else begin
            regs_read.push_back('{rs1, rs1_value, 0});
            regs_write.push_back('{rs1, 'x, 0});
            str = $sformatf("p.%-14s x%0d, %0d(x%0d!)", mnemonic, rd, $signed(imm_i_type), rs1);
          end
        end else begin
          // reg-reg load
          if (instr[6:0] != OPCODE_LOAD_POST) begin
            regs_read.push_back('{rs2, rs2_value,0});
            regs_read.push_back('{rs1, rs1_value, 0});
            str = $sformatf("%-16s x%0d, x%0d(x%0d)", mnemonic, rd, rs2, rs1);
          end else begin
            regs_read.push_back('{rs2, rs2_value,0});
            regs_read.push_back('{rs1, rs1_value, 0});
            regs_write.push_back('{rs1, 'x, 0});
            str = $sformatf("p.%-14s x%0d, x%0d(x%0d!)", mnemonic, rd, rs2, rs1);
          end
        end
      end
    endfunction

    function void printStoreInstr();
      string mnemonic;
      begin

        case (instr[13:12])
          2'b00:  mnemonic = "sb";
          2'b01:  mnemonic = "sh";
          2'b10:  mnemonic = "sw";
          2'b11: begin
            printMnemonic("INVALID");
            return;
          end
        endcase
        mnemonic = {compressed ? "c." : "", mnemonic};

        if (instr[14] == 1'b0) begin
          // regular store
          if (instr[6:0] != OPCODE_STORE_POST) begin
            regs_read.push_back('{rs2, rs2_value, 0});
            regs_read.push_back('{rs1, rs1_value, 0});
            str = $sformatf("%-16s x%0d, %0d(x%0d)", mnemonic, rs2, $signed(imm_s_type), rs1);
          end else begin
            regs_read.push_back('{rs2, rs2_value, 0});
            regs_read.push_back('{rs1, rs1_value, 0});
            regs_write.push_back('{rs1, 'x, 0});
            str = $sformatf("p.%-14s x%0d, %0d(x%0d!)", mnemonic, rs2, $signed(imm_s_type), rs1);
          end
        end else begin
          // reg-reg store
          if (instr[6:0] != OPCODE_STORE_POST) begin
            regs_read.push_back('{rs2, rs2_value, 0});
            regs_read.push_back('{rs3, rs3_value, 0});
            regs_read.push_back('{rs1, rs1_value, 0});
            str = $sformatf("p.%-14s x%0d, x%0d(x%0d)", mnemonic, rs2, rs3, rs1);
          end else begin
            regs_read.push_back('{rs2, rs2_value, 0});
            regs_read.push_back('{rs3, rs3_value, 0});
            regs_read.push_back('{rs1, rs1_value, 0});
            regs_write.push_back('{rs1, 'x, 0});
            str = $sformatf("p.%-14s x%0d, x%0d(x%0d!)", mnemonic, rs2, rs3, rs1);
          end
        end
      end
    endfunction // printSInstr

    function void printHwloopInstr();
      string mnemonic;
      begin
        // set mnemonic
        case (instr[14:12])
          3'b000: mnemonic = "lp.starti";
          3'b001: mnemonic = "lp.endi";
          3'b010: mnemonic = "lp.count";
          3'b011: mnemonic = "lp.counti";
          3'b100: mnemonic = "lp.setup";
          3'b101: mnemonic = "lp.setupi";
          3'b111: begin
            printMnemonic("INVALID");
            return;
          end
        endcase

        // decode and print instruction
        case (instr[14:12])
          // lp.starti and lp.endi
          3'b000,
          3'b001: str = $sformatf("%-16s 0x%0d, 0x%0h", mnemonic, rd, imm_iz_type);
          // lp.count
          3'b010: begin
            regs_read.push_back('{rs1, rs1_value, 0});
            str = $sformatf("%-16s 0x%0d, x%0d", mnemonic, rd, rs1);
          end
          // lp.counti
          3'b011: str = $sformatf("%-16s x%0d, 0x%0h", mnemonic, rd, imm_iz_type);
          // lp.setup
          3'b100: begin
            regs_read.push_back('{rs1, rs1_value, 0});
            str = $sformatf("%-16s 0x%0d, x%0d, 0x%0h", mnemonic, rd, rs1, imm_iz_type);
          end
          // lp.setupi
          3'b101: begin
            str = $sformatf("%-16s 0x%0d, 0x%0h, 0x%0h", mnemonic, rd, imm_iz_type, rs1);
          end
        endcase
      end
    endfunction

    function void printMulInstr();
      string mnemonic;
      string str_suf;
      string str_imm;
      string str_asm;
      begin

        // always read rs1 and rs2 and write rd
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_read.push_back('{rs2, rs2_value,0});
        regs_write.push_back('{rd, 'x, 0});

        if (instr[12])
          regs_read.push_back('{rd, rs3_value, 0});

        case ({instr[31:30], instr[14]})
          3'b000: str_suf = "u";
          3'b001: str_suf = "uR";
          3'b010: str_suf = "hhu";
          3'b011: str_suf = "hhuR";
          3'b100: str_suf = "s";
          3'b101: str_suf = "sR";
          3'b110: str_suf = "hhs";
          3'b111: str_suf = "hhsR";
        endcase

        if (instr[12])
          mnemonic = "p.mac";
        else
          mnemonic = "p.mul";

        if (imm_s3_type[4:0] != 5'b00000)
          str_asm = $sformatf("%s%sN", mnemonic, str_suf);
        else
          str_asm = $sformatf("%s%s", mnemonic, str_suf);

        if (instr[29:25] != 5'b00000)
          str = $sformatf("%-16s x%0d, x%0d, x%0d, %0d", str_asm, rd, rs1, rs2, $unsigned(imm_s3_type[4:0]));
        else
          str = $sformatf("%-16s x%0d, x%0d, x%0d", str_asm, rd, rs1, rs2);
      end
    endfunction

    function void printVecInstr();
      string mnemonic;
      string str_asm;
      string str_args;
      string str_hb;
      string str_sci;
      string str_imm;
      begin

        // always read rs1 and write rd
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_write.push_back('{rd, 'x, 0});

        case (instr[14:13])
          2'b00: str_sci = "";
          2'b10: str_sci = ".sc";
          2'b11: str_sci = ".sci";
        endcase

        if (instr[12])
          str_hb = ".b";
        else
          str_hb = ".h";

        // set mnemonic
        case (instr[31:26])
          6'b000000: begin mnemonic = "pv.add";      str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b000010: begin mnemonic = "pv.sub";      str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b000100: begin mnemonic = "pv.avg";      str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b000110: begin mnemonic = "pv.avgu";     str_imm = $sformatf("0x%0d", imm_vu_type); end
          6'b001000: begin mnemonic = "pv.min";      str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b001010: begin mnemonic = "pv.minu";     str_imm = $sformatf("0x%0d", imm_vu_type); end
          6'b001100: begin mnemonic = "pv.max";      str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b001110: begin mnemonic = "pv.maxu";     str_imm = $sformatf("0x%0d", imm_vu_type); end
          6'b010000: begin mnemonic = "pv.srl";      str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b010010: begin mnemonic = "pv.sra";      str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b010100: begin mnemonic = "pv.sll";      str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b010110: begin mnemonic = "pv.or";       str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b011000: begin mnemonic = "pv.xor";      str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b011010: begin mnemonic = "pv.and";      str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b011100: begin mnemonic = "pv.abs";      str_imm = $sformatf("0x%0d", imm_vs_type); end

          6'b011110: begin mnemonic = "pv.extract";  str_imm = $sformatf("0x%0d", imm_vs_type); str_sci = ""; end
          6'b100100: begin mnemonic = "pv.extractu"; str_imm = $sformatf("0x%0d", imm_vu_type); str_sci = ""; end
          6'b101100: begin mnemonic = "pv.insert";   str_imm = $sformatf("0x%0d", imm_vs_type); end

          // shuffle/pack
          6'b110000: begin
            if (instr[14:12] == 3'b001) begin
                mnemonic = "pv.shuffle";
            end else begin
                mnemonic = "pv.shufflei0";
                str_imm = $sformatf("0x%0d", imm_shuffle_type);
            end
          end
          6'b111010: begin mnemonic = "pv.shufflei1"; str_imm = $sformatf("0x%0d", imm_shuffle_type);  end
          6'b111100: begin mnemonic = "pv.shufflei2"; str_imm = $sformatf("0x%0d", imm_shuffle_type);  end
          6'b111110: begin mnemonic = "pv.shufflei3"; str_imm = $sformatf("0x%0d", imm_shuffle_type);  end

          6'b110010: begin mnemonic = "pv.shuffle2"; end

          6'b110100: begin mnemonic = instr[25] ? "pv.pack.h" : "pv.pack"; end
          6'b110110: begin mnemonic = "pv.packhi";                         end
          6'b111000: begin mnemonic = "pv.packlo";                         end

          // comparisons
          6'b000001: begin mnemonic = "pv.cmpeq";    str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b000011: begin mnemonic = "pv.cmpne";    str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b000101: begin mnemonic = "pv.cmpgt";    str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b000111: begin mnemonic = "pv.cmpge";    str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b001001: begin mnemonic = "pv.cmplt";    str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b001011: begin mnemonic = "pv.cmple";    str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b001101: begin mnemonic = "pv.cmpgtu";   str_imm = $sformatf("0x%0d", imm_vu_type); end
          6'b001111: begin mnemonic = "pv.cmpgeu";   str_imm = $sformatf("0x%0d", imm_vu_type); end
          6'b010001: begin mnemonic = "pv.cmpltu";   str_imm = $sformatf("0x%0d", imm_vu_type); end
          6'b010011: begin mnemonic = "pv.cmpleu";   str_imm = $sformatf("0x%0d", imm_vu_type); end

          // dotproducts
          6'b100000: begin mnemonic = "pv.dotup";    str_imm = $sformatf("0x%0d", imm_vu_type); end
          6'b100010: begin mnemonic = "pv.dotusp";   str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b100110: begin mnemonic = "pv.dotsp";    str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b101000: begin mnemonic = "pv.sdotup";   str_imm = $sformatf("0x%0d", imm_vu_type); end
          6'b101010: begin mnemonic = "pv.sdotusp";  str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b101110: begin mnemonic = "pv.sdotsp";   str_imm = $sformatf("0x%0d", imm_vs_type); end

          6'b010101: begin
            unique case (instr[14:13])
               2'b00: mnemonic = instr[25] == 1'b0 ? "pv.cplxmul.r"      : "pv.cplxmul.i";
               2'b01: mnemonic = instr[25] == 1'b0 ? "pv.cplxmul.r.div2" : "pv.cplxmul.i.div2";
               2'b10: mnemonic = instr[25] == 1'b0 ? "pv.cplxmul.r.div4" : "pv.cplxmul.i.div4";
               2'b11: mnemonic = instr[25] == 1'b0 ? "pv.cplxmul.r.div8" : "pv.cplxmul.i.div8";
            endcase
            str_sci = "";
          end

          6'b011011: begin
            unique case (instr[14:13])
               2'b00: mnemonic = "pv.subrotmj";
               2'b01: mnemonic = "pv.subrotmj.div2";
               2'b10: mnemonic = "pv.subrotmj.div4";
               2'b11: mnemonic = "pv.subrotmj.div8";
            endcase
            str_sci = "";
          end

          6'b010111: begin
            mnemonic = "pv.cplxconj";
            str_sci  = "";
          end

          6'b011101: begin
            unique case (instr[14:13])
               2'b01: mnemonic = "pv.add.div2";
               2'b10: mnemonic = "pv.add.div4";
               2'b11: mnemonic = "pv.add.div8";
            endcase
            str_sci = "";
          end

          6'b011001: begin
            unique case (instr[14:13])
               2'b01: mnemonic = "pv.sub.div2";
               2'b10: mnemonic = "pv.sub.div4";
               2'b11: mnemonic = "pv.sub.div8";
            endcase
            str_sci = "";
          end

          default: begin
            printMnemonic("INVALID");
            return;
          end
        endcase

        if(mnemonic == "pv.cplxconj") begin
            //special case, one operand only
          str_args = $sformatf("x%0d, x%0d", rd, rs1);
        end else begin
            if (str_sci == "") begin
              regs_read.push_back('{rs2, rs2_value,0});
              str_args = $sformatf("x%0d, x%0d, x%0d", rd, rs1, rs2);
            end else if (str_sci == ".sc") begin
              regs_read.push_back('{rs2, rs2_value_vec, 0});
              str_args = $sformatf("x%0d, x%0d, x%0d", rd, rs1, rs2);
            end else if (str_sci == ".sci") begin
              str_args = $sformatf("x%0d, x%0d, %s", rd, rs1, str_imm);
            end
        end

        str_asm = $sformatf("%s%s%s", mnemonic, str_sci, str_hb);

        str = $sformatf("%-16s %s", str_asm, str_args);
      end
    endfunction
  endclass
