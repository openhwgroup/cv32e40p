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

// Tracer data structures and functions
//
// Contributors: Steve Richmond, Silicon Labs <steve.richmond@silabs.com>
//               Pascal Gouedo, Dolphin Design <pascal.gouedo@dolphin.fr>

typedef struct {
  logic [5:0] addr;
  logic [31:0] value;
  bit filled;
} reg_t;

typedef struct {
  logic [31:0] addr;
  logic we;
  logic [3:0] be;
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
  logic        is_apu;
  logic        is_load;
  logic        got_regs_write;

  function new();
    str        = "";
    regs_read  = {};
    regs_write = {};
    mem_access = {};
  endfunction

  function void init(int unsigned cycles, bit [31:0] pc, bit compressed, bit [31:0] instr);
    this.simtime        = $time;
    this.cycles         = cycles;
    this.pc             = pc;
    this.compressed     = compressed;
    this.instr          = instr;
    this.is_apu         = 0;
    this.is_load        = 0;
    this.got_regs_write = 0;

    // use casex instead of case inside due to ModelSim bug
    casex (instr)
      // Aliases
      32'h00_00_00_13: this.printMnemonic("nop");
      // Regular opcodes
      INSTR_LUI:       this.printUInstr("lui");
      INSTR_AUIPC:     this.printUInstr("auipc");
      INSTR_JAL:       this.printUJInstr("jal");
      INSTR_JALR:      this.printIInstr("jalr");
      // BRANCH
      INSTR_BEQ:       this.printSBInstr("beq");
      INSTR_BNE:       this.printSBInstr("bne");
      INSTR_BLT:       this.printSBInstr("blt");
      INSTR_BGE:       this.printSBInstr("bge");
      INSTR_BLTU:      this.printSBInstr("bltu");
      INSTR_BGEU:      this.printSBInstr("bgeu");
      INSTR_BEQIMM:    this.printSBallInstr("cv.beqimm");
      INSTR_BNEIMM:    this.printSBallInstr("cv.bneimm");
      // OPIMM
      INSTR_ADDI:      this.printIInstr("addi");
      INSTR_SLTI:      this.printIInstr("slti");
      INSTR_SLTIU:     this.printIInstr("sltiu");
      INSTR_XORI:      this.printIInstr("xori");
      INSTR_ORI:       this.printIInstr("ori");
      INSTR_ANDI:      this.printIInstr("andi");
      INSTR_SLLI:      this.printIuInstr("slli");
      INSTR_SRLI:      this.printIuInstr("srli");
      INSTR_SRAI:      this.printIuInstr("srai");
      // OP
      INSTR_ADD:       this.printRInstr("add");
      INSTR_SUB:       this.printRInstr("sub");
      INSTR_SLL:       this.printRInstr("sll");
      INSTR_SLT:       this.printRInstr("slt");
      INSTR_SLTU:      this.printRInstr("sltu");
      INSTR_XOR:       this.printRInstr("xor");
      INSTR_SRL:       this.printRInstr("srl");
      INSTR_SRA:       this.printRInstr("sra");
      INSTR_OR:        this.printRInstr("or");
      INSTR_AND:       this.printRInstr("and");
      INSTR_EXTHS:     this.printRInstr("cv.exths");
      INSTR_EXTHZ:     this.printRInstr("cv.exthz");
      INSTR_EXTBS:     this.printRInstr("cv.extbs");
      INSTR_EXTBZ:     this.printRInstr("cv.extbz");
      INSTR_PAVG:      this.printRInstr("cv.avg");
      INSTR_PAVGU:     this.printRInstr("cv.avgu");

      INSTR_PADDN:   this.printAddNInstr("cv.addN");
      INSTR_PADDUN:  this.printAddNInstr("cv.adduN");
      INSTR_PADDRN:  this.printAddNInstr("cv.addRN");
      INSTR_PADDURN: this.printAddNInstr("cv.adduRN");
      INSTR_PSUBN:   this.printAddNInstr("cv.subN");
      INSTR_PSUBUN:  this.printAddNInstr("cv.subuN");
      INSTR_PSUBRN:  this.printAddNInstr("cv.subRN");
      INSTR_PSUBURN: this.printAddNInstr("cv.subuRN");

      INSTR_PADDNR:   this.printR3Instr("cv.addNr");
      INSTR_PADDUNR:  this.printR3Instr("cv.adduNr");
      INSTR_PADDRNR:  this.printR3Instr("cv.addRNr");
      INSTR_PADDURNR: this.printR3Instr("cv.adduRNr");
      INSTR_PSUBNR:   this.printR3Instr("cv.subNr");
      INSTR_PSUBUNR:  this.printR3Instr("cv.subuNr");
      INSTR_PSUBRNR:  this.printR3Instr("cv.subRNr");
      INSTR_PSUBURNR: this.printR3Instr("cv.subuRNr");

      INSTR_PSLET:  this.printRInstr("cv.slet");
      INSTR_PSLETU: this.printRInstr("cv.sletu");
      INSTR_PMIN:   this.printRInstr("cv.min");
      INSTR_PMINU:  this.printRInstr("cv.minu");
      INSTR_PMAX:   this.printRInstr("cv.max");
      INSTR_PMAXU:  this.printRInstr("cv.maxu");
      INSTR_PABS:   this.printR1Instr("cv.abs");
      INSTR_PCLIP:  this.printClipInstr("cv.clip");
      INSTR_PCLIPU: this.printClipInstr("cv.clipu");
      INSTR_PBEXT:  this.printBit1Instr("cv.extract");
      INSTR_PBEXTU: this.printBit1Instr("cv.extractu");
      INSTR_PBINS:  this.printBit2Instr("cv.insert");
      INSTR_PBCLR:  this.printBit1Instr("cv.bclr");
      INSTR_PBSET:  this.printBit1Instr("cv.bset");
      INSTR_PBREV:  this.printBitRevInstr("cv.bitrev");

      INSTR_PCLIPR:  this.printRInstr("cv.clipr");
      INSTR_PCLIPUR: this.printRInstr("cv.clipur");
      INSTR_PBEXTR:  this.printRInstr("cv.extractr");
      INSTR_PBEXTUR: this.printRInstr("cv.extractur");
      INSTR_PBINSR:  this.printR3Instr("cv.insertr");
      INSTR_PBCLRR:  this.printRInstr("cv.bclrr");
      INSTR_PBSETR:  this.printRInstr("cv.bsetr");


      INSTR_FF1: this.printR1Instr("cv.ff1");
      INSTR_FL1: this.printR1Instr("cv.fl1");
      INSTR_CLB: this.printR1Instr("cv.clb");
      INSTR_CNT: this.printR1Instr("cv.cnt");
      INSTR_ROR: this.printRInstr("cv.ror");

      // FENCE
      INSTR_FENCE:  this.printMnemonic("fence");
      INSTR_FENCEI: this.printMnemonic("fencei");
      // SYSTEM (CSR manipulation)
      INSTR_CSRRW:  this.printCSRInstr("csrrw");
      INSTR_CSRRS:  this.printCSRInstr("csrrs");
      INSTR_CSRRC:  this.printCSRInstr("csrrc");
      INSTR_CSRRWI: this.printCSRInstr("csrrwi");
      INSTR_CSRRSI: this.printCSRInstr("csrrsi");
      INSTR_CSRRCI: this.printCSRInstr("csrrci");
      // SYSTEM (others)
      INSTR_ECALL:  this.printMnemonic("ecall");
      INSTR_EBREAK: this.printMnemonic("ebreak");
      INSTR_URET:   this.printMnemonic("uret");
      INSTR_MRET:   this.printMnemonic("mret");
      INSTR_WFI:    this.printMnemonic("wfi");

      INSTR_DRET: this.printMnemonic("dret");

      // RV32M
      INSTR_PMUL:      this.printRInstr("mul");
      INSTR_PMUH:      this.printRInstr("mulh");
      INSTR_PMULHSU:   this.printRInstr("mulhsu");
      INSTR_PMULHU:    this.printRInstr("mulhu");
      INSTR_DIV:       this.printRInstr("div");
      INSTR_DIVU:      this.printRInstr("divu");
      INSTR_REM:       this.printRInstr("rem");
      INSTR_REMU:      this.printRInstr("remu");
      // PULP MULTIPLIER
      INSTR_PMAC:      this.printR3Instr("cv.mac");
      INSTR_PMSU:      this.printR3Instr("cv.msu");
      INSTR_PMULSN:    this.printMulInstr();
      INSTR_PMULHHSN:  this.printMulInstr();
      INSTR_PMULSRN:   this.printMulInstr();
      INSTR_PMULHHSRN: this.printMulInstr();
      INSTR_PMULUN:    this.printMulInstr();
      INSTR_PMULHHUN:  this.printMulInstr();
      INSTR_PMULURN:   this.printMulInstr();
      INSTR_PMULHHURN: this.printMulInstr();
      INSTR_PMACSN:    this.printMulInstr();
      INSTR_PMACHHSN:  this.printMulInstr();
      INSTR_PMACSRN:   this.printMulInstr();
      INSTR_PMACHHSRN: this.printMulInstr();
      INSTR_PMACUN:    this.printMulInstr();
      INSTR_PMACHHUN:  this.printMulInstr();
      INSTR_PMACURN:   this.printMulInstr();
      INSTR_PMACHHURN: this.printMulInstr();

      // FP-OP
      INSTR_FMADD:   begin this.printF3Instr("fmadd.s");   this.is_apu = 1; end
      INSTR_FMSUB:   begin this.printF3Instr("fmsub.s");   this.is_apu = 1; end
      INSTR_FNMADD:  begin this.printF3Instr("fnmadd.s");  this.is_apu = 1; end
      INSTR_FNMSUB:  begin this.printF3Instr("fnmsub.s");  this.is_apu = 1; end
      INSTR_FADD:    begin this.printF2Instr("fadd.s");    this.is_apu = 1; end
      INSTR_FSUB:    begin this.printF2Instr("fsub.s");    this.is_apu = 1; end
      INSTR_FMUL:    begin this.printF2Instr("fmul.s");    this.is_apu = 1; end
      INSTR_FDIV:    begin this.printF2Instr("fdiv.s");    this.is_apu = 1; end
      INSTR_FSQRT:   begin this.printFInstr("fsqrt.s");    this.is_apu = 1; end
      INSTR_FSGNJS:  begin this.printF2Instr("fsgnj.s");   this.is_apu = 1; end
      INSTR_FSGNJNS: begin this.printF2Instr("fsgnjn.s");  this.is_apu = 1; end
      INSTR_FSGNJXS: begin this.printF2Instr("fsgnjx.s");  this.is_apu = 1; end
      INSTR_FMIN:    begin this.printF2Instr("fmin.s");    this.is_apu = 1; end
      INSTR_FMAX:    begin this.printF2Instr("fmax.s");    this.is_apu = 1; end
      INSTR_FCVTWS:  begin this.printFIInstr("fcvt.w.s");  this.is_apu = 1; end
      INSTR_FCVTWUS: begin this.printFIInstr("fcvt.wu.s"); this.is_apu = 1; end
      INSTR_FMVXS:   begin this.printFIInstr("fmv.x.s");   this.is_apu = 1; end
      INSTR_FEQS:    begin this.printF2IInstr("feq.s");    this.is_apu = 1; end
      INSTR_FLTS:    begin this.printF2IInstr("flt.s");    this.is_apu = 1; end
      INSTR_FLES:    begin this.printF2IInstr("fle.s");    this.is_apu = 1; end
      INSTR_FCLASS:  begin this.printFIInstr("fclass.s");  this.is_apu = 1; end
      INSTR_FCVTSW:  begin this.printIFInstr("fcvt.s.w");  this.is_apu = 1; end
      INSTR_FCVTSWU: begin this.printIFInstr("fcvt.s.wu"); this.is_apu = 1; end
      INSTR_FMVSX:   begin this.printIFInstr("fmv.s.x");   this.is_apu = 1; end

      // RV32A
      INSTR_LR:      this.printAtomicInstr("lr.w");
      INSTR_SC:      this.printAtomicInstr("sc.w");
      INSTR_AMOSWAP: this.printAtomicInstr("amoswap.w");
      INSTR_AMOADD:  this.printAtomicInstr("amoadd.w");
      INSTR_AMOXOR:  this.printAtomicInstr("amoxor.w");
      INSTR_AMOAND:  this.printAtomicInstr("amoand.w");
      INSTR_AMOOR:   this.printAtomicInstr("amoor.w");
      INSTR_AMOMIN:  this.printAtomicInstr("amomin.w");
      INSTR_AMOMAX:  this.printAtomicInstr("amomax.w");
      INSTR_AMOMINU: this.printAtomicInstr("amominu.w");
      INSTR_AMOMAXU: this.printAtomicInstr("amomaxu.w");

      // opcodes with custom decoding
      {25'b?, OPCODE_LOAD} :                               begin this.printLoadInstr("");  this.is_load = 1; end
      {25'b?, OPCODE_LOAD_FP} :                            begin this.printLoadInstr("f"); this.is_load = 1; end
      {25'b?, OPCODE_CUSTOM_0} :                           begin this.printLoadInstr("");  this.is_load = 1; end
      {7'b000????, 10'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1} : begin this.printLoadInstr("");  this.is_load = 1; end
      {7'b001????, 10'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1} : this.printStoreInstr("");
      {17'b?, 3'b100, 5'b?, OPCODE_CUSTOM_1}             : this.printHwloopInstr();
      {25'b?, OPCODE_STORE} :                              this.printStoreInstr("");
      {25'b?, OPCODE_STORE_FP} :                           this.printStoreInstr("f");
      {17'b?, 3'b0??, 5'b?, OPCODE_CUSTOM_1} :             this.printStoreInstr("");
      {25'b?, OPCODE_CUSTOM_3} :                           this.printVecInstr();
      default:                                             this.printMnemonic("INVALID");
    endcase  // unique case (instr)

  endfunction : init

  function bit is_regs_write_done();
    foreach (regs_write[i]) if (regs_write[i].value === 'x) return 0;

    return 1;
  endfunction : is_regs_write_done

  function string regAddrToStr(input logic [5:0] addr);
    begin
      if (SymbolicRegs==1 && (FPU==0 || ZFINX==0)) begin // format according to RISC-V ABI
        if (addr == 0) return $sformatf("zero");
        else if (addr ==       1) return $sformatf("  ra");
        else if (addr ==       2) return $sformatf("  sp");
        else if (addr ==       3) return $sformatf("  gp");
        else if (addr ==       4) return $sformatf("  tp");
        else if (addr <=       7) return $sformatf("  t%0d", addr -  5);
        else if (addr <=       9) return $sformatf("  s%0d", addr -  8);
        else if (addr <=      17) return $sformatf("  a%0d", addr - 10);
        else if (addr <=      25) return $sformatf("  s%0d", addr - 16);
        else if (addr <=      27) return $sformatf(" s%0d",  addr - 16);
        else if (addr <=      31) return $sformatf("  t%0d", addr - 25);
        else if (addr <= 32 +  7) return $sformatf(" ft%0d", addr - 32);
        else if (addr <= 32 +  9) return $sformatf(" fs%0d", addr - 40);
        else if (addr <= 32 + 17) return $sformatf(" fa%0d", addr - 42);
        else if (addr <= 32 + 25) return $sformatf(" fs%0d", addr - 48);
        else if (addr <= 32 + 27) return $sformatf("fs%0d",  addr - 48);
        else if (addr <= 32 + 29) return $sformatf(" ft%0d", addr - 52);
        else if (addr <= 32 + 31) return $sformatf("ft%0d",  addr - 52);
        else return $sformatf("UNKNOWN %0d", addr);
      end else begin
        if (addr >= 42)      return $sformatf("f%0d", addr - 32);
        else if (addr >= 32) return $sformatf(" f%0d", addr - 32);
        else if (addr <  10) return $sformatf(" x%0d", addr);
        else                 return $sformatf("x%0d", addr);
      end
    end
  endfunction

  function void printInstrTrace();
    mem_acc_t mem_acc;
    begin
      string insn_str;  // Accumulate writes into a single string to enable single $fwrite

      insn_str = $sformatf("%t %15d %h %h %-36s", simtime, cycles, pc, instr, str);

      foreach (regs_write[i]) begin
        if (regs_write[i].addr != 0)
          insn_str = $sformatf(
              "%s %s=%08x", insn_str, regAddrToStr(regs_write[i].addr), regs_write[i].value
          );
      end

      foreach (regs_read[i]) begin
        if (regs_read[i].addr != 0)
          insn_str = $sformatf(
              "%s %s:%08x", insn_str, regAddrToStr(regs_read[i].addr), regs_read[i].value
          );
      end

      if (mem_access.size() > 0) begin
        mem_acc  = mem_access.pop_front();

        insn_str = $sformatf("%s  PA:%08x", insn_str, mem_acc.addr);
      end

      $fwrite(f, "%s\n", insn_str);
    end
  endfunction

  function void printMnemonic(input string mnemonic);
    begin
      str = {compressed ? "c." : "", mnemonic};
    end
  endfunction  // printMnemonic

  function void printRInstr(input string mnemonic);
    begin
      mnemonic = {compressed ? "c." : "", mnemonic};
      regs_read.push_back('{rs1, rs1_value, 0});
      regs_read.push_back('{rs2, rs2_value, 0});
      regs_write.push_back('{rd, 'x, 0});
      str = $sformatf("%-16s %s, %s, %s", mnemonic, regAddrToStr(rd), regAddrToStr(rs1), regAddrToStr(rs2));
    end
  endfunction  // printRInstr

  function void printAddNInstr(input string mnemonic);
    begin
      regs_read.push_back('{rs1, rs1_value, 0});
      regs_read.push_back('{rs2, rs2_value, 0});
      regs_write.push_back('{rd, 'x, 0});
      str = $sformatf(
          "%-16s %s, %s, %s, 0x%0h", mnemonic, regAddrToStr(rd), regAddrToStr(rs1), regAddrToStr(rs2), $unsigned(imm_s3_type[4:0])
      );
    end
  endfunction  // printAddNInstr

  function void printR1Instr(input string mnemonic);
    begin
      regs_read.push_back('{rs1, rs1_value, 0});
      regs_write.push_back('{rd, 'x, 0});
      str = $sformatf("%-16s %s, %s", mnemonic, regAddrToStr(rd), regAddrToStr(rs1));
    end
  endfunction  // printR1Instr

  function void printR3Instr(input string mnemonic);
    begin
      regs_read.push_back('{rd, rs3_value, 0});
      regs_read.push_back('{rs1, rs1_value, 0});
      regs_read.push_back('{rs2, rs2_value, 0});
      regs_write.push_back('{rd, 'x, 0});
      str = $sformatf("%-16s %s, %s, %s", mnemonic, regAddrToStr(rd), regAddrToStr(rs1), regAddrToStr(rs2));
    end
  endfunction  // printR3Instr

  function void printF3Instr(input string mnemonic);
    begin
      regs_read.push_back('{rs1, rs1_value, 0});
      regs_read.push_back('{rs2, rs2_value, 0});
      regs_read.push_back('{rs4, rs3_value, 0});
      regs_write.push_back('{rd, 'x, 0});
      str = $sformatf(
          "%-16s %s, %s, %s, %s", mnemonic, regAddrToStr(rd), regAddrToStr(rs1), regAddrToStr(rs2), regAddrToStr(rs4)
      );
    end
  endfunction  // printF3Instr

  function void printF2Instr(input string mnemonic);
    begin
      regs_read.push_back('{rs1, rs1_value, 0});
      regs_read.push_back('{rs2, rs2_value, 0});
      regs_write.push_back('{rd, 'x, 0});
      str = $sformatf("%-16s %s, %s, %s", mnemonic, regAddrToStr(rd), regAddrToStr(rs1), regAddrToStr(rs2));
    end
  endfunction  // printF2Instr

  function void printF2IInstr(input string mnemonic);
    begin
      regs_read.push_back('{rs1, rs1_value, 0});
      regs_read.push_back('{rs2, rs2_value, 0});
      regs_write.push_back('{rd, 'x, 0});
      str = $sformatf("%-16s %s, %s, %s", mnemonic, regAddrToStr(rd), regAddrToStr(rs1), regAddrToStr(rs2));
    end
  endfunction  // printF2IInstr

  function void printFInstr(input string mnemonic);
    begin
      regs_read.push_back('{rs1, rs1_value, 0});
      regs_write.push_back('{rd, 'x, 0});
      str = $sformatf("%-16s %s, %s", mnemonic, regAddrToStr(rd), regAddrToStr(rs1));
    end
  endfunction  // printFInstr

  function void printFIInstr(input string mnemonic);
    begin
      regs_read.push_back('{rs1, rs1_value, 0});
      regs_write.push_back('{rd, 'x, 0});
      str = $sformatf("%-16s %s, %s", mnemonic, regAddrToStr(rd), regAddrToStr(rs1));
    end
  endfunction  // printFIInstr

  function void printIFInstr(input string mnemonic);
    begin
      mnemonic = {compressed ? "c." : "", mnemonic};
      regs_read.push_back('{rs1, rs1_value, 0});
      regs_write.push_back('{rd, 'x, 0});
      str = $sformatf("%-16s %s, %s", mnemonic, regAddrToStr(rd), regAddrToStr(rs1));
    end
  endfunction  // printIFInstr

  function void printClipInstr(input string mnemonic);
    begin
      regs_read.push_back('{rs1, rs1_value, 0});
      regs_write.push_back('{rd, 'x, 0});
      str = $sformatf("%-16s %s, %s, %0d", mnemonic, regAddrToStr(rd), regAddrToStr(rs1), $unsigned(imm_clip_type));
    end
  endfunction  // printRInstr

  function void printIInstr(input string mnemonic);
    begin
      mnemonic = {compressed ? "c." : "", mnemonic};
      regs_read.push_back('{rs1, rs1_value, 0});
      regs_write.push_back('{rd, 'x, 0});
      str = $sformatf("%-16s %s, %s, %0d", mnemonic, regAddrToStr(rd), regAddrToStr(rs1), $signed(imm_i_type));
    end
  endfunction  // printIInstr

  function void printIuInstr(input string mnemonic);
    begin
      mnemonic = {compressed ? "c." : "", mnemonic};
      regs_read.push_back('{rs1, rs1_value, 0});
      regs_write.push_back('{rd, 'x, 0});
      str = $sformatf("%-16s %s, %s, 0x%0x", mnemonic, regAddrToStr(rd), regAddrToStr(rs1), imm_i_type);
    end
  endfunction  // printIuInstr

  function void printUInstr(input string mnemonic);
    begin
      mnemonic = {compressed ? "c." : "", mnemonic};
      regs_write.push_back('{rd, 'x, 0});
      str = $sformatf("%-16s %s, 0x%0h", mnemonic, regAddrToStr(rd), {imm_u_type[31:12], 12'h000});
    end
  endfunction  // printUInstr

  function void printUJInstr(input string mnemonic);
    begin
      mnemonic = {compressed ? "c." : "", mnemonic};
      regs_write.push_back('{rd, 'x, 0});
      str = $sformatf("%-16s %s, %0d", mnemonic, regAddrToStr(rd), $signed(imm_uj_type));
    end
  endfunction  // printUJInstr

  function void printSBInstr(input string mnemonic);
    begin
      mnemonic = {compressed ? "c." : "", mnemonic};
      regs_read.push_back('{rs1, rs1_value, 0});
      regs_read.push_back('{rs2, rs2_value, 0});
      str = $sformatf("%-16s %s, %s, %0d", mnemonic, regAddrToStr(rs1), regAddrToStr(rs2), $signed(imm_sb_type));
    end
  endfunction  // printSBInstr

  function void printSBallInstr(input string mnemonic);
    begin
      mnemonic = {compressed ? "c." : "", mnemonic};
      regs_read.push_back('{rs1, rs1_value, 0});
      str =  $sformatf("%-16s %s, %0d", mnemonic, regAddrToStr(rs1), $signed(imm_sb_type));
    end
  endfunction  // printSBInstr

  function void printCSRInstr(input string mnemonic);
    logic [11:0] csr;
    begin
      csr = instr[31:20];

      regs_write.push_back('{rd, 'x, 0});

      if (instr[14] == 1'b0) begin
        regs_read.push_back('{rs1, rs1_value, 0});
        str = $sformatf("%-16s %s, %s, 0x%h", mnemonic, regAddrToStr(rd), regAddrToStr(rs1), csr);
      end else begin
        str = $sformatf("%-16s %s, 0x%h, 0x%h", mnemonic, regAddrToStr(rd), imm_z_type, csr);
      end
    end
  endfunction  // printCSRInstr

  function void printBit1Instr(input string mnemonic);
    begin
      regs_read.push_back('{rs1, rs1_value, 0});
      regs_write.push_back('{rd, 'x, 0});
      str =  $sformatf("%-16s %s, %s, %0d, %0d", mnemonic, regAddrToStr(rd), regAddrToStr(rs1), imm_s3_type, imm_s2_type);
    end
  endfunction

  function void printBitRevInstr(input string mnemonic);
    begin
      regs_read.push_back('{rs1, rs1_value, 0});
      regs_write.push_back('{rd, 'x, 0});
      str =  $sformatf("%-16s %s, %s, %0d, %0d", mnemonic, regAddrToStr(rd), regAddrToStr(rs1), imm_s2_type, imm_s3_type);
    end
  endfunction

  function void printBit2Instr(input string mnemonic);
    begin
      regs_read.push_back('{rd, rs3_value, 0});
      regs_read.push_back('{rs1, rs1_value, 0});
      regs_write.push_back('{rd, 'x, 0});
      str =  $sformatf("%-16s %s, %s, %0d, %0d", mnemonic, regAddrToStr(rd), regAddrToStr(rs1), imm_s3_type, imm_s2_type);
    end
  endfunction

  function void printAtomicInstr(input string mnemonic);
    begin
      regs_read.push_back('{rs1, rs1_value, 0});
      regs_read.push_back('{rs2, rs2_value, 0});
      regs_write.push_back('{rd, 'x, 0});
      if (instr[31:27] == AMO_LR) begin
        // Do not print rs2 for load-reserved
        str = $sformatf("%-16s %s, (%s)", mnemonic, regAddrToStr(rd), regAddrToStr(rs1));
      end else begin
        str = $sformatf("%-16s %s, %s, (%s)", mnemonic, regAddrToStr(rd), regAddrToStr(rs2), regAddrToStr(rs1));
      end
    end
  endfunction  // printAtomicInstr

  function void printLoadInstr(input string fp);
    string mnemonic;
    logic [2:0] size;
    begin
      // find size
      size = instr[14:12];
      if (instr[6:0] == OPCODE_CUSTOM_1) size = {instr[28], instr[26:25]};

      case (size)
        3'b000: mnemonic = "lb";
        3'b001: mnemonic = "lh";
        3'b010: mnemonic = "lw";
        3'b011: mnemonic = "elw";
        3'b100: mnemonic = "lbu";
        3'b101: mnemonic = "lhu";
        default: begin
          printMnemonic("INVALID");
          return;
        end
      endcase
      if (FPU==1 && ZFINX==0) begin
        mnemonic = {fp, mnemonic};
      end
      mnemonic = {compressed ? "c." : "", mnemonic};

      regs_write.push_back('{rd, 'x, 0});

      if (instr[6:0] != OPCODE_CUSTOM_0 && instr[6:0] != OPCODE_CUSTOM_1) begin
        // regular load
        regs_read.push_back('{rs1, rs1_value, 0});
        str = $sformatf("%-16s %s, %0d(x%0d)", mnemonic, regAddrToStr(rd), $signed(imm_i_type), rs1);
      end else if (instr[6:0] == OPCODE_CUSTOM_0 && size == 3'b011) begin
        // cv.elw
        regs_read.push_back('{rs1, rs1_value, 0});
        str = $sformatf("cv.%-13s %s, %0d(x%0d)", mnemonic, regAddrToStr(rd), $signed(imm_i_type), rs1);
      end else if (instr[6:0] == OPCODE_CUSTOM_0) begin
        // immediate post-incremented load
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_write.push_back('{rs1, 'x, 0});
        str = $sformatf("cv.%-13s %s, %0d(x%0d!)", mnemonic, regAddrToStr(rd), $signed(imm_i_type), rs1);
      end else if (instr[6:0] == OPCODE_CUSTOM_1) begin
        if (instr[27] == 1'b0) begin
          // reg-reg post-incremented load
          regs_read.push_back('{rs2, rs2_value, 0});
          regs_read.push_back('{rs1, rs1_value, 0});
          regs_write.push_back('{rs1, 'x, 0});
          str = $sformatf("cv.%-13s %s, %s(x%0d!)", mnemonic, regAddrToStr(rd), regAddrToStr(rs2), rs1);
        end else begin
          // reg-reg indexed load
          regs_read.push_back('{rs2, rs2_value, 0});
          regs_read.push_back('{rs1, rs1_value, 0});
          str = $sformatf("%-16s %s, %s(x%0d)", mnemonic, regAddrToStr(rd), regAddrToStr(rs2), rs1);
        end
      end
    end
  endfunction

  function void printStoreInstr(input string fp);
    string mnemonic;
    logic [2:0] size;
    begin
      // find size
      size = instr[14:12];
      if (instr[6:0] == OPCODE_CUSTOM_1 && instr[14:12] == 3'b011) size = {instr[28], instr[26:25]};

      case (size)
        3'b000: mnemonic = "sb";
        3'b001: mnemonic = "sh";
        3'b010: mnemonic = "sw";
        default: begin
          printMnemonic("INVALID");
          return;
        end
      endcase
      if (FPU==1 && ZFINX==0) begin
        mnemonic = {fp, mnemonic};
      end
      mnemonic = {compressed ? "c." : "", mnemonic};

      if (instr[6:0] != OPCODE_CUSTOM_1) begin
        // regular store
        regs_read.push_back('{rs2, rs2_value, 0});
        regs_read.push_back('{rs1, rs1_value, 0});
        str = $sformatf("%-16s %s, %0d(x%0d)", mnemonic, regAddrToStr(rs2), $signed(imm_s_type), rs1);
      end else if (instr[14:12] != 3'b011 && instr[14] != 1'b1) begin
        // immediate post-incremented store
        regs_read.push_back('{rs2, rs2_value, 0});
        regs_read.push_back('{rs1, rs1_value, 0});
        regs_write.push_back('{rs1, 'x, 0});
        str = $sformatf("cv.%-14s %s, %0d(x%0d!)", mnemonic, regAddrToStr(rs2), $signed(imm_s_type), rs1);
      end else if (instr[31:28] == 4'b0010) begin
        if (instr[27] == 1'b0) begin
          // reg-reg post-incremented store
          regs_read.push_back('{rs2, rs2_value, 0});
          regs_read.push_back('{rs3, rs3_value, 0});
          regs_read.push_back('{rs1, rs1_value, 0});
          regs_write.push_back('{rs1, 'x, 0});
          str = $sformatf("cv.%-13s %s, %s(x%0d!)", mnemonic, regAddrToStr(rs2), regAddrToStr(rs3), rs1);
        end else begin
          // reg-reg indexed store
          regs_read.push_back('{rs2, rs2_value, 0});
          regs_read.push_back('{rs3, rs3_value, 0});
          regs_read.push_back('{rs1, rs1_value, 0});
          str = $sformatf("cv.%-13s %s, %s(x%0d)", mnemonic, regAddrToStr(rs2), regAddrToStr(rs3), rs1);
        end
      end
    end
  endfunction  // printSInstr

  function void printHwloopInstr();
    string mnemonic;
    begin
      // set mnemonic
      case (instr[11:8])
        4'b0000: mnemonic = "cv.starti";
        4'b0001: mnemonic = "cv.start";
        4'b0010: mnemonic = "cv.endi";
        4'b0011: mnemonic = "cv.end";
        4'b0100: mnemonic = "cv.counti";
        4'b0101: mnemonic = "cv.count";
        4'b0110: mnemonic = "cv.setupi";
        4'b0111: mnemonic = "cv.setup";
        4'b1???: begin
          printMnemonic("INVALID");
          return;
        end
      endcase

      // decode and print instruction
      case (instr[11:8])
        // cv.starti, cv.endi
        4'b0000, 4'b0010: str = $sformatf("%-16s %d, 0x%0x", mnemonic, rd[0], imm_iz_type);
        // cv.counti
        4'b0100: str = $sformatf("%-16s %d, %d", mnemonic, rd[0], imm_iz_type);
        // cv.start, cv.end, cv.count
        4'b0001, 4'b0011, 4'b0101: begin
          regs_read.push_back('{rs1, rs1_value, 0});
          str = $sformatf("%-16s %d, %s", mnemonic, rd[0], regAddrToStr(rs1));
        end
        // cv.setupi
        4'b0110: begin
          str = $sformatf("%-16s %d, %d, 0x%0x", mnemonic, rd[0], imm_iz_type, rs1);
        end
        // cv.setup
        4'b0111: begin
          regs_read.push_back('{rs1, rs1_value, 0});
          str = $sformatf("%-16s %d, %s, 0x%0x", mnemonic, rd[0], regAddrToStr(rs1), imm_iz_type);
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
      regs_read.push_back('{rs2, rs2_value, 0});
      regs_write.push_back('{rd, 'x, 0});

      if (instr[13]) regs_read.push_back('{rd, rs3_value, 0});

      case ({instr[12], instr[30], instr[31]})
        3'b000: str_suf = "s";
        3'b001: str_suf = "sR";
        3'b010: str_suf = "hhs";
        3'b011: str_suf = "hhsR";
        3'b100: str_suf = "u";
        3'b101: str_suf = "uR";
        3'b110: str_suf = "hhu";
        3'b111: str_suf = "hhuR";
      endcase

      if (instr[13]) mnemonic = "cv.mac";
      else mnemonic = "cv.mul";

      str_asm = $sformatf("%s%sN", mnemonic, str_suf);

      str = $sformatf("%-16s %s, %s, %s, %0d", str_asm, regAddrToStr(rd), regAddrToStr(rs1), regAddrToStr(rs2), $unsigned(imm_s3_type[4:0]));
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

      if (instr[12]) str_hb = ".b";
      else str_hb = ".h";

      // set mnemonic
      case (instr[31:26])
        6'b000000: begin
          mnemonic = "cv.add";
          str_imm  = $sformatf("0x%0h", imm_vs_type);
        end
        6'b000010: begin
          mnemonic = "cv.sub";
          str_imm  = $sformatf("0x%0h", imm_vs_type);
        end
        6'b000100: begin
          mnemonic = "cv.avg";
          str_imm  = $sformatf("0x%0h", imm_vs_type);
        end
        6'b000110: begin
          mnemonic = "cv.avgu";
          str_imm  = $sformatf("0x%0h", imm_vu_type);
        end
        6'b001000: begin
          mnemonic = "cv.min";
          str_imm  = $sformatf("0x%0h", imm_vs_type);
        end
        6'b001010: begin
          mnemonic = "cv.minu";
          str_imm  = $sformatf("0x%0h", imm_vu_type);
        end
        6'b001100: begin
          mnemonic = "cv.max";
          str_imm  = $sformatf("0x%0h", imm_vs_type);
        end
        6'b001110: begin
          mnemonic = "cv.maxu";
          str_imm  = $sformatf("0x%0h", imm_vu_type);
        end
        6'b010000: begin
          mnemonic = "cv.srl";
          str_imm  = $sformatf("0x%0h", imm_vs_type);
        end
        6'b010010: begin
          mnemonic = "cv.sra";
          str_imm  = $sformatf("0x%0h", imm_vs_type);
        end
        6'b010100: begin
          mnemonic = "cv.sll";
          str_imm  = $sformatf("0x%0h", imm_vs_type);
        end
        6'b010110: begin
          mnemonic = "cv.or";
          str_imm  = $sformatf("0x%0h", imm_vs_type);
        end
        6'b011000: begin
          mnemonic = "cv.xor";
          str_imm  = $sformatf("0x%0h", imm_vs_type);
        end
        6'b011010: begin
          mnemonic = "cv.and";
          str_imm  = $sformatf("0x%0h", imm_vs_type);
        end
        6'b011100: begin
          mnemonic = "cv.abs";
          str_imm  = $sformatf("0x%0h", imm_vs_type);
        end
        // dot products
        6'b100000: begin
          mnemonic = "cv.dotup";
          str_imm  = $sformatf("0x%0h", imm_vu_type);
        end
        6'b100010: begin
          mnemonic = "cv.dotusp";
          str_imm  = $sformatf("0x%0h", imm_vs_type);
        end
        6'b100100: begin
          mnemonic = "cv.dotsp";
          str_imm  = $sformatf("0x%0h", imm_vs_type);
        end
        6'b100110: begin
          mnemonic = "cv.sdotup";
          str_imm  = $sformatf("0x%0h", imm_vu_type);
        end
        6'b101000: begin
          mnemonic = "cv.sdotusp";
          str_imm  = $sformatf("0x%0h", imm_vs_type);
        end
        6'b101010: begin
          mnemonic = "cv.sdotsp";
          str_imm  = $sformatf("0x%0h", imm_vs_type);
        end

        6'b101110: begin
          case (instr[14:13])
            2'b00 : begin
              mnemonic = "cv.extract";
              str_imm  = $sformatf("0x%0h", imm_vs_type);
            end
            2'b01 : begin
              mnemonic = "cv.extractu";
              str_imm  = $sformatf("0x%0h", imm_vu_type);
            end
            2'b10 : begin
              mnemonic = "cv.insert";
              str_imm  = $sformatf("0x%0h", imm_vs_type);
            end
          endcase
          str_sci  = "";
        end
  
        // shuffle/pack
        6'b110000: begin
          if (instr[14:12] == 3'b111) begin
            mnemonic = "cv.shuffleI0";
            str_imm  = $sformatf("0x%8h", imm_shuffle_type);
          end else begin
            mnemonic = "cv.shuffle";
            if (instr[14:12] == 3'b110) begin
              str_imm  = $sformatf("0x%8h", imm_shuffle_type);
            end
          end
        end
        6'b110010: begin
          mnemonic = "cv.shuffleI1";
          str_imm  = $sformatf("0x%8h", imm_shuffle_type);
        end
        6'b110100: begin
          mnemonic = "cv.shuffleI2";
          str_imm  = $sformatf("0x%8h", imm_shuffle_type);
        end
        6'b110110: begin
          mnemonic = "cv.shuffleI3";
          str_imm  = $sformatf("0x%8h", imm_shuffle_type);
        end
        6'b111000: begin
          mnemonic = "cv.shuffle2";
        end
        6'b111100: begin
          mnemonic = "cv.pack";
          if (instr[25] == 1'b0) begin
            str_hb = "";
          end
        end
        6'b111110: begin
          mnemonic = instr[25] ? "cv.packhi" : "cv.packlo";
        end

        // comparisons
        6'b000001: begin
          mnemonic = "cv.cmpeq";
          str_imm  = $sformatf("0x%0h", imm_vs_type);
        end
        6'b000011: begin
          mnemonic = "cv.cmpne";
          str_imm  = $sformatf("0x%0h", imm_vs_type);
        end
        6'b000101: begin
          mnemonic = "cv.cmpgt";
          str_imm  = $sformatf("0x%0h", imm_vs_type);
        end
        6'b000111: begin
          mnemonic = "cv.cmpge";
          str_imm  = $sformatf("0x%0h", imm_vs_type);
        end
        6'b001001: begin
          mnemonic = "cv.cmplt";
          str_imm  = $sformatf("0x%0h", imm_vs_type);
        end
        6'b001011: begin
          mnemonic = "cv.cmple";
          str_imm  = $sformatf("0x%0h", imm_vs_type);
        end
        6'b001101: begin
          mnemonic = "cv.cmpgtu";
          str_imm  = $sformatf("0x%0h", imm_vu_type);
        end
        6'b001111: begin
          mnemonic = "cv.cmpgeu";
          str_imm  = $sformatf("0x%0h", imm_vu_type);
        end
        6'b010001: begin
          mnemonic = "cv.cmpltu";
          str_imm  = $sformatf("0x%0h", imm_vu_type);
        end
        6'b010011: begin
          mnemonic = "cv.cmpleu";
          str_imm  = $sformatf("0x%0h", imm_vu_type);
        end

        6'b010101: begin
          unique case (instr[14:13])
            2'b00: mnemonic = instr[25] == 1'b0 ? "cv.cplxmul.r"      : "cv.cplxmul.i";
            2'b01: mnemonic = instr[25] == 1'b0 ? "cv.cplxmul.r.div2" : "cv.cplxmul.i.div2";
            2'b10: mnemonic = instr[25] == 1'b0 ? "cv.cplxmul.r.div4" : "cv.cplxmul.i.div4";
            2'b11: mnemonic = instr[25] == 1'b0 ? "cv.cplxmul.r.div8" : "cv.cplxmul.i.div8";
          endcase
          str_sci = "";
          str_hb = "";
        end

        6'b010111: begin
          mnemonic = "cv.cplxconj";
          str_sci  = "";
          str_hb = "";
        end

        6'b011001: begin
          unique case (instr[14:13])
            2'b00: mnemonic = "cv.subrotmj";
            2'b01: mnemonic = "cv.subrotmj.div2";
            2'b10: mnemonic = "cv.subrotmj.div4";
            2'b11: mnemonic = "cv.subrotmj.div8";
          endcase
          str_sci = "";
          str_hb = "";
        end

        6'b011011: begin
          unique case (instr[14:13])
            2'b01: mnemonic = "cv.add.div2";
            2'b10: mnemonic = "cv.add.div4";
            2'b11: mnemonic = "cv.add.div8";
          endcase
          str_sci = "";
          str_hb = "";
        end

        6'b011101: begin
          unique case (instr[14:13])
            2'b01: mnemonic = "cv.sub.div2";
            2'b10: mnemonic = "cv.sub.div4";
            2'b11: mnemonic = "cv.sub.div8";
          endcase
          str_sci = "";
          str_hb = "";
        end

        default: begin
          printMnemonic("INVALID");
          return;
        end
      endcase

      if (mnemonic == "cv.cplxconj") begin
        //special case, one operand only
        str_args = $sformatf("%s, %s", regAddrToStr(rd), regAddrToStr(rs1));
      end else begin
        if (str_sci == "") begin
          regs_read.push_back('{rs2, rs2_value, 0});
          str_args = $sformatf("%s, %s, %s", regAddrToStr(rd), regAddrToStr(rs1), regAddrToStr(rs2));
        end else if (str_sci == ".sc") begin
          regs_read.push_back('{rs2, rs2_value_vec, 0});
          str_args = $sformatf("%s, %s, %s", regAddrToStr(rd), regAddrToStr(rs1), regAddrToStr(rs2));
        end else if (str_sci == ".sci") begin
          str_args = $sformatf("%s, %s, %s", regAddrToStr(rd), regAddrToStr(rs1), str_imm);
        end
      end

      str_asm = $sformatf("%s%s%s", mnemonic, str_sci, str_hb);

      str = $sformatf("%-16s %s", str_asm, str_args);
    end
  endfunction
endclass
