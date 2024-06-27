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
// Engineer:       Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Additional contributions by:                                               //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    RISC-V Tracer                                              //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Traces the executed instructions                           //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`ifdef CV32E40P_TRACE_EXECUTION

`include "uvm_macros.svh"

module cv32e40p_tracer
  import cv32e40p_pkg::*;
  import uvm_pkg::*;
#(
    parameter FPU   = 0,
    parameter ZFINX = 0
) (
    // Clock and Reset
    input logic clk_i,
    input logic rst_n,

    input logic [31:0] hart_id_i,


    input logic [31:0] pc,
    input logic [31:0] instr,
    input ctrl_state_e controller_state_i,

    input logic compressed,
    input logic id_valid,
    input logic is_decoding,
    input logic is_illegal,
    input logic trigger_match,

    input logic [31:0] rs1_value,
    input logic [31:0] rs2_value,
    input logic [31:0] rs3_value,

    input logic [31:0] rs2_value_vec,

    input logic rd_is_fp,
    input logic rs1_is_fp,
    input logic rs2_is_fp,
    input logic rs3_is_fp,

    input logic        ex_valid,
    input logic [ 5:0] ex_reg_addr,
    input logic        ex_reg_we,
    input logic [31:0] ex_reg_wdata,

    input logic        ex_data_req,
    input logic        ex_data_gnt,
    input logic        ex_data_we,
    input logic [31:0] ex_data_addr,
    input logic [31:0] ex_data_wdata,
    input logic        data_misaligned,

    input logic ebrk_insn,
    input logic debug_mode,
    input logic ebrk_force_debug_mode,

    input logic wb_bypass,

    input logic        wb_valid,
    input logic [ 5:0] wb_reg_addr,
    input logic        wb_reg_we,
    input logic [31:0] wb_reg_wdata,

    input logic [31:0] imm_u_type,
    input logic [31:0] imm_uj_type,
    input logic [31:0] imm_i_type,
    input logic [11:0] imm_iz_type,
    input logic [31:0] imm_z_type,
    input logic [31:0] imm_s_type,
    input logic [31:0] imm_sb_type,
    input logic [31:0] imm_s2_type,
    input logic [31:0] imm_s3_type,
    input logic [31:0] imm_vs_type,
    input logic [31:0] imm_vu_type,
    input logic [31:0] imm_shuffle_type,
    input logic [ 4:0] imm_clip_type,

    input logic apu_en_i,
    input logic apu_singlecycle_i,
    input logic apu_multicycle_i,
    input logic apu_rvalid_i

);

  import cv32e40p_tracer_pkg::*;

  // Make clock a bit to avoid x->0 transitions in tracer logic
  bit clk_i_d, eval_comb;
  assign #0.01 clk_i_d = clk_i;
  assign eval_comb = ~(clk_i & ~clk_i_d);

  //event   ovp_retire;
  //bit     use_iss;

  integer f;
  string  fn;
  integer cycles;
  logic [5:0] rd, rs1, rs2, rs3, rs4;

  logic [31:0] pc_ex_stage;
  logic [31:0] pc_ex_delay_stage;
  logic [31:0] pc_wb_stage;
  logic [31:0] pc_wb_delay_stage;
  logic [31:0] pc_retire_head_q;

  `include "cv32e40p_instr_trace.svh"

  string               info_tag;

  event                retire;

  instr_trace_t        trace_ex;
  instr_trace_t        trace_wb;
  instr_trace_t        trace_wb_delay;
  instr_trace_t        trace_ex_delay;

  bit                  clear_trace_ex = 0;
  bit                  move_trace_ex_to_trace_wb = 0;
  bit                  clear_trace_wb = 0;
  bit                  move_trace_wb_to_trace_wb_delay = 0;
  bit                  clear_trace_wb_delay = 0;
  bit                  move_trace_ex_to_trace_ex_delay = 0;
  bit                  clear_trace_ex_delay = 0;
  bit                  move_trace_ex_delay_to_trace_wb = 0;

  bit                  trace_new = 0;
  bit                  trace_new_ebreak = 0;
  bit                  trace_ex_misaligned = 0;
  bit                  trace_ex_retire = 0;
  bit                  trace_ex_wb_bypass = 0;
  bit                  trace_wb_retire = 0;
  bit                  trace_wb_delay_retire = 0;

  bit                  trace_ex_is_null = 1;
  bit                  trace_ex_delay_is_null = 1;
  bit                  trace_wb_is_null = 1;
  bit                  trace_wb_delay_is_null = 1;

  bit                  trace_ex_is_delay_instr = 0;
  bit                  trace_wb_is_delay_instr = 0;

  string               insn_disas;
  logic                insn_compressed;
  logic                insn_wb_bypass;
  logic                insn_ebreak;
  logic         [31:0] insn_pc;
  logic         [31:0] insn_val;
  reg_t                insn_regs_write                     [$];

  instr_trace_t        trace_q                             [$];
  instr_trace_t        trace_retire;

  // cycle counter
  always_ff @(posedge clk_i, negedge rst_n) begin
    if (rst_n == 1'b0) cycles <= 0;
    else cycles <= cycles + 1;
  end

  initial begin
    wait(rst_n == 1'b1);
    $sformat(fn, "trace_core_%h.log", hart_id_i);
    $sformat(info_tag, "CORE_TRACER %2d", hart_id_i);
    $display("[%s] Output filename is: %s", info_tag, fn);
    f = $fopen(fn, "w");
    $fwrite(f,
            "            Time           Cycle PC       Instr    Ctx Decoded instruction Register and memory contents\n");
  end

  //initial begin
  //  use_iss = 0;
  //  if ($test$plusargs("USE_ISS")) use_iss = 1;
  //end

  always @(trace_ex or trace_ex_delay or trace_wb or trace_wb_delay or trace_retire) begin
    pc_ex_stage = (trace_ex != null) ? trace_ex.pc : 'x;
    pc_ex_delay_stage = (trace_ex_delay != null) ? trace_ex_delay.pc : 'x;
    pc_wb_stage = (trace_wb != null) ? trace_wb.pc : 'x;
    pc_wb_delay_stage = (trace_wb_delay != null) ? trace_wb_delay.pc : 'x;
    pc_retire_head_q = (trace_retire != null) ? trace_retire.pc : 'x;
  end

  always @(trace_wb)
    trace_wb_is_delay_instr = (trace_wb != null && is_wb_delay_instr(
        trace_wb
    )) ? 1 : 0;

  assign rd  = {rd_is_fp, instr[11:07]};
  assign rs1 = {rs1_is_fp, instr[19:15]};
  assign rs2 = {rs2_is_fp, instr[24:20]};
  assign rs3 = {rs3_is_fp, instr[29:25]};
  assign rs4 = {rs3_is_fp, instr[31:27]};

  function void apply_reg_write(instr_trace_t trace, int unsigned reg_addr, int unsigned wdata);
    foreach (trace.regs_write[i])
      if (trace.regs_write[i].addr == reg_addr) begin
        trace.regs_write[i].value = wdata;
        `uvm_info(info_tag, $sformatf(
                  "Write mapped %0d, %0d:0x%08x pc:0x%08x", i, reg_addr, wdata, trace.pc),
                  UVM_DEBUG)
      end else begin
        `uvm_info(info_tag, $sformatf(
                  "Unmapped write to %0d:0x%08x, expected write to %0d",
                  reg_addr,
                  wdata,
                  trace.regs_write[i].addr
                  ), UVM_DEBUG)
      end
  endfunction : apply_reg_write

  function void apply_mem_access(instr_trace_t trace, bit we, int unsigned addr,
                                 int unsigned wdata);
    mem_acc_t mem_acc;

    mem_acc.addr = addr;
    mem_acc.we   = we;

    if (we) mem_acc.wdata = wdata;
    else mem_acc.wdata = 'x;

    trace.mem_access.push_back(mem_acc);
  endfunction : apply_mem_access

  function instr_trace_t trace_new_instr();
    instr_trace_t trace;

    trace = new();
    trace.init(.cycles(cycles), .pc(pc), .compressed(compressed), .instr(instr));

    return trace;
  endfunction : trace_new_instr

  // Funnel all handoffs to the ISS here, note that this must be automatic
  // as multiple retire events may occur at a time (wb_bypass)
  always begin
    wait(trace_q.size() != 0);
    trace_retire = trace_q.pop_front();
    wait(trace_retire.retire != 0);

    if (trace_retire.ebreak) wait(debug_mode == 1);

    // Write signals and data structures used by step-and-compare
    insn_regs_write = trace_retire.regs_write;
    insn_disas      = trace_retire.str;
    insn_compressed = trace_retire.compressed;
    insn_pc         = trace_retire.pc;
    insn_val        = trace_retire.instr;
    insn_wb_bypass  = trace_retire.wb_bypass;

    trace_retire.printInstrTrace();

    ->retire;
    //  if (use_iss) @(ovp_retire);
    #0.1ns;
  end

  // EX stage
  always @(negedge clk_i_d or negedge rst_n) begin
    if (!rst_n) begin
      trace_ex <= null;
      trace_ex_is_null <= 1;
    end else begin
      if (trace_ex_retire) trace_ex.retire = 1;
      if (trace_ex_wb_bypass) trace_ex.wb_bypass = 1;
      if (trace_ex_misaligned) trace_ex.misaligned = 1;

      if (trace_new_ebreak) begin
        instr_trace_t new_instr;
        new_instr = trace_new_instr();

        // The EBREAK bypasses the pipeline so it retirable immediately upon debug_mode entry
        new_instr.ebreak = 1;
        new_instr.retire = 1;
        trace_q.push_back(new_instr);
      end

      if (trace_new) begin
        instr_trace_t new_instr;
        new_instr = trace_new_instr();
        trace_q.push_back(new_instr);
        trace_ex <= new_instr;
        trace_ex_is_null <= 0;
      end else if (clear_trace_ex) begin
        trace_ex <= null;
        trace_ex_is_null <= 1;
      end
    end
  end

  // EX delay stage
  always @(negedge clk_i_d or negedge rst_n) begin
    if (!rst_n) begin
      trace_ex_delay <= null;
      trace_ex_delay_is_null <= 1;
    end else begin
      if (move_trace_ex_to_trace_ex_delay) begin
        trace_ex_delay <= trace_ex;
        trace_ex_delay_is_null <= (trace_ex == null) ? 1 : 0;
      end else if (clear_trace_ex_delay) begin
        trace_ex_delay <= null;
        trace_ex_delay_is_null <= 1;
      end
    end
  end

  // WB stage
  always @(negedge clk_i_d or negedge rst_n) begin
    if (rst_n) begin
      if (trace_wb_retire) begin
        if (trace_wb != null) begin
          trace_wb.retire = 1;
        end else begin
          `uvm_fatal(info_tag, "Received retire signal with no valid trace_wb instruction");
        end
      end
    end
  end

  always @(negedge clk_i_d or negedge rst_n) begin
    if (!rst_n) begin
      trace_wb <= null;
      trace_wb_is_null <= 1;
    end else begin
      if (move_trace_ex_to_trace_wb) begin
        trace_wb         <= trace_ex;
        trace_wb_is_null <= (trace_ex == null) ? 1 : 0;
      end else if (move_trace_ex_delay_to_trace_wb) begin
        trace_wb         <= trace_ex_delay;
        trace_wb_is_null <= (trace_ex_delay == null) ? 1 : 0;
      end else if (clear_trace_wb) begin
        trace_wb         <= null;
        trace_wb_is_null <= 1;
      end
    end
  end

  // WB delay stage
  always @(negedge clk_i_d or negedge rst_n) begin
    if (!rst_n) begin
      trace_wb_delay <= null;
      trace_wb_delay_is_null <= 1;
    end else begin
      if (trace_wb_delay_retire) trace_wb_delay.retire = 1;

      if (move_trace_wb_to_trace_wb_delay) begin
        trace_wb_delay <= trace_wb;
        trace_wb_delay_is_null <= (trace_wb == null) ? 1 : 0;
      end else if (clear_trace_wb_delay) begin
        trace_wb_delay <= null;
        trace_wb_delay_is_null <= 1;
      end
    end
  end

  function bit is_wb_delay_instr(instr_trace_t trace_wb);
    if (trace_wb.str == "mret" || trace_wb.str == "uret" || trace_wb.str == "ebreak" || trace_wb.str == "c.ebreak")
      return 1;

    return 0;
  endfunction : is_wb_delay_instr

  always @* begin
    trace_new = 0;
    trace_new_ebreak = 0;
    trace_ex_misaligned = 0;
    trace_ex_retire = 0;
    trace_ex_wb_bypass = 0;
    trace_wb_retire = 0;
    trace_wb_delay_retire = 0;

    clear_trace_ex = 0;

    move_trace_ex_to_trace_wb = 0;
    clear_trace_wb = 0;

    move_trace_wb_to_trace_wb_delay = 0;
    clear_trace_wb_delay = 0;

    move_trace_ex_to_trace_ex_delay = 0;
    move_trace_ex_delay_to_trace_wb = 0;
    clear_trace_ex_delay = 0;

    // ----------------------------------------------
    // WB Delay logic
    // ----------------------------------------------
    if (!trace_wb_delay_is_null && eval_comb) begin
      // Always retire
      trace_wb_delay_retire = 1;
      clear_trace_wb_delay  = 1;
    end

    // ----------------------------------------------
    // WB logic
    // ----------------------------------------------
    if (!trace_wb_is_null && eval_comb) begin
      if (wb_valid) begin
        // Some instructons get an extra cycle to retire
        if (trace_wb_is_delay_instr) begin
          move_trace_wb_to_trace_wb_delay = 1;
        end else begin
          trace_wb_retire = 1;
          clear_trace_wb  = 1;
        end
      end
    end

    // ----------------------------------------------
    // EX Delay logic
    // ----------------------------------------------
    // apu_rvalid_i for variable latency apu offloading
    // non apu instructions will always go to wb as fast as possible (i.e. next cycle)
    if (!trace_ex_delay_is_null && eval_comb) begin
      if (apu_rvalid_i || !trace_ex_delay.is_apu) begin
        move_trace_ex_delay_to_trace_wb = 1;
        clear_trace_ex_delay            = 1;
      end
    end

    // ----------------------------------------------
    // EX logic
    // ----------------------------------------------

    // New instruction created if is a legal decoded instruction
    if (id_valid && is_decoding && !is_illegal) begin
      trace_new = 1;
      // Create a new EBREAK instruuction (will bypass pipeline execution)
    end else if (is_decoding && !trigger_match && ebrk_insn && (ebrk_force_debug_mode || debug_mode)) begin
      trace_new_ebreak = 1;
    end

    // Instruction remains in the pipeline for one more cycle if misaligned
    if (!trace_ex_is_null && eval_comb && ex_valid && data_misaligned) begin
      trace_ex_misaligned = 1;
      // Instruction bypasses WB - mark as retirable and do not advance
    end else if (wb_bypass) begin
      trace_ex_retire = 1;
      trace_ex_wb_bypass = 1;
      clear_trace_ex = 1;

      // Some instructons get an extra cycle to retire
      // offload to (potentially) multicycle APU/FPU
    end else if (!trace_ex_is_null && eval_comb && apu_en_i && !apu_rvalid_i) begin
      move_trace_ex_to_trace_ex_delay = 1;
      clear_trace_ex                  = 1;

      // Instruction leaves EX
    end else if (!trace_ex_is_null && eval_comb && ex_valid && !data_misaligned) begin
      // if ex delay is already writing to wb then we also delay this one
      if (move_trace_ex_delay_to_trace_wb) begin
        move_trace_ex_to_trace_ex_delay = 1;
        clear_trace_ex                  = 1;
      end else begin
        move_trace_ex_to_trace_wb = 1;
        clear_trace_ex            = 1;
      end
    end

    if (move_trace_ex_to_trace_wb && move_trace_ex_delay_to_trace_wb) begin
      `uvm_info(info_tag, "ex delay stage and ex stage collide", UVM_DEBUG);
    end
  end

  // Monitors for memory access and register writeback
  always @(negedge clk_i or negedge rst_n) begin
    if (!rst_n) begin
    end else begin
      // Register updates in EX
      // !wb_valid necessary for CSR to GPR write when OBI Data stalled
      if (ex_reg_we && (ex_valid || !wb_valid || apu_rvalid_i)) begin
        `uvm_info(info_tag, $sformatf("EX: Reg WR %02d = 0x%08x", ex_reg_addr, ex_reg_wdata),
                  UVM_DEBUG);
        if (!trace_ex_delay_is_null && !trace_ex_delay.got_regs_write && !trace_ex_delay.is_load &&
            ((!trace_ex_delay.is_apu && (ex_valid || !wb_valid)) ||
             (trace_ex_delay.is_apu && apu_rvalid_i && (apu_singlecycle_i || apu_multicycle_i))
            )
           ) begin
          apply_reg_write(trace_ex_delay, ex_reg_addr, ex_reg_wdata);
          trace_ex_delay.got_regs_write = 1;
        end else if (!trace_ex_is_null) begin
          apply_reg_write(trace_ex, ex_reg_addr, ex_reg_wdata);
          if (trace_ex.got_regs_write) begin
            `uvm_info(info_tag, $sformatf(
                      "EX: Multiple Reg WR %02d = 0x%08x", ex_reg_addr, ex_reg_wdata), UVM_DEBUG);
          end
          trace_ex.got_regs_write = 1;
        end else begin
          `uvm_info(info_tag, $sformatf(
                    "EX: Reg WR %02d:0x%08x but no active EX instruction", ex_reg_addr, ex_reg_wdata
                    ), UVM_DEBUG);
        end
      end

      // Register updates in WB
      if (wb_reg_we) begin
        `uvm_info(info_tag, $sformatf("WB: Reg WR %02d = 0x%08x", wb_reg_addr, wb_reg_wdata),
                  UVM_DEBUG);
        if (!trace_ex_delay_is_null &&
            ((trace_ex_delay.is_load) ||
             (trace_ex_delay.is_apu && apu_rvalid_i && !apu_singlecycle_i && !apu_multicycle_i)
            )
           ) begin
          apply_reg_write(trace_ex_delay, wb_reg_addr, wb_reg_wdata);
          trace_ex_delay.got_regs_write = 1;
        end else if (!trace_wb_is_null && !trace_wb.got_regs_write) begin
          if (!trace_wb.is_load || (trace_wb.is_load && wb_valid)) begin
            apply_reg_write(trace_wb, wb_reg_addr, wb_reg_wdata);
            trace_wb.got_regs_write = 1;
          end
        end else if (!trace_ex_is_null && !trace_ex.got_regs_write && trace_ex.misaligned) begin
          // Do nothing as double load concatenation will be managed by trace_wb
        end else begin
          `uvm_info(info_tag, $sformatf(
                    "WB: Reg WR %02d:0x%08x but no active WB instruction", wb_reg_addr, wb_reg_wdata
                    ), UVM_DEBUG);
        end
      end

      // Memory access in EX
      if (ex_data_req && ex_data_gnt) begin
        if (ex_data_we) begin
          `uvm_info(info_tag, $sformatf("EX: Mem WR 0x%08x = 0x%08x", ex_data_addr, ex_data_wdata),
                    UVM_DEBUG);
        end else begin
          `uvm_info(info_tag, $sformatf("EX: Mem RD 0x%08x", ex_data_addr), UVM_DEBUG);
        end
        if (trace_ex_is_null) begin
          `uvm_info(info_tag, $sformatf(
                    "EX: Mem %s 0x%08x:0x%08x but no active EX instruction",
                    ex_data_we ? "WR" : "RD",
                    ex_data_addr,
                    ex_reg_wdata
                    ), UVM_DEBUG);
        end else apply_mem_access(trace_ex, ex_data_we, ex_data_addr, ex_data_wdata);
      end
    end
  end

endmodule : cv32e40p_tracer


`endif  // CV32E40P_TRACE_EXECUTION
