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
(
  // Clock and Reset
  input  logic        clk_i,
  input  logic        rst_n,

  input  logic [31:0] hart_id_i,


  input  logic [31:0] pc,
  input  logic [31:0] instr,
  input  ctrl_state_e controller_state_i,

  input  logic        compressed,
  input  logic        id_valid,
  input  logic        is_decoding,
  input  logic        is_illegal,

  input  logic [31:0] rs1_value,
  input  logic [31:0] rs2_value,
  input  logic [31:0] rs3_value,

  input  logic [31:0] rs2_value_vec,

  input  logic        rd_is_fp,
  input  logic        rs1_is_fp,
  input  logic        rs2_is_fp,
  input  logic        rs3_is_fp,

  input  logic        ex_valid,
  input  logic [ 5:0] ex_reg_addr,
  input  logic        ex_reg_we,
  input  logic [31:0] ex_reg_wdata,

  input  logic        ex_data_req,
  input  logic        ex_data_gnt,
  input  logic        ex_data_we,
  input  logic [31:0] ex_data_addr,
  input  logic [31:0] ex_data_wdata,
  input  logic        data_misaligned,

  input  logic        wb_bypass,

  input  logic        wb_valid,
  input  logic [ 5:0] wb_reg_addr,
  input  logic        wb_reg_we,
  input  logic [31:0] wb_reg_wdata,

  input  logic [31:0] imm_u_type,
  input  logic [31:0] imm_uj_type,
  input  logic [31:0] imm_i_type,
  input  logic [11:0] imm_iz_type,
  input  logic [31:0] imm_z_type,
  input  logic [31:0] imm_s_type,
  input  logic [31:0] imm_sb_type,
  input  logic [31:0] imm_s2_type,
  input  logic [31:0] imm_s3_type,
  input  logic [31:0] imm_vs_type,
  input  logic [31:0] imm_vu_type,
  input  logic [31:0] imm_shuffle_type,
  input  logic [ 4:0] imm_clip_type
);

  import cv32e40p_tracer_pkg::*;

  wire clk_i_d;
  assign #0.01 clk_i_d = clk_i;

  event ovp_retire;
  integer      f;
  string       fn;
  integer      cycles;
  logic [ 5:0] rd, rs1, rs2, rs3, rs4;

  logic [31:0] pc_id_stage;  
  logic [31:0] pc_ex_stage;

  logic [31:0] pc_wb_stage;
  logic [31:0] pc_wb_stage_d;
  logic [31:0] pc_wb_delay_stage;

`include "cv32e40p_instr_trace.svh"

  string info_tag = "TRACER";

  event         retire;

  instr_trace_t trace_ex;
  instr_trace_t trace_wb_bypass;
  instr_trace_t trace_wb;
  instr_trace_t trace_wb_delay;

  // these signals are for simulator visibility. Don't try to do the nicer way
  // of making instr_trace_t visible to inspect it with your simulator. Some
  // choke for some unknown performance reasons.
  string       insn_disas;
  logic        insn_compressed;
  logic        insn_wb_bypass;
  logic [31:0] insn_pc;
  logic [31:0] insn_val;
  reg_t insn_regs_write[$];

  instr_trace_t trace_ex_q[$];
  instr_trace_t trace_wb_q[$];
  instr_trace_t trace_wb_bypass_q[$];
  instr_trace_t trace_wb_delay_q[$];
  instr_trace_t trace_retire_q[$];

  instr_trace_t trace_retire;

//  instr_trace_t trace;

  bit trace_ex_clear;
  bit trace_wb_clear;
  bit trace_wb_delay_clear;

  // cycle counter
  always_ff @(posedge clk_i, negedge rst_n) begin
    if (rst_n == 1'b0)
      cycles <= 0;
    else
      cycles <= cycles + 1;
  end

  initial begin
    wait(rst_n == 1'b1);
    $sformat(fn, "trace_core_%h.log", hart_id_i);
    f = $fopen(fn, "w");
    $fwrite(f, "Time\tCycle\tPC\tInstr\tDecoded instruction\tRegister and memory contents\n");
  end

  always @(trace_ex or trace_wb or trace_wb_delay) begin
    pc_ex_stage = (trace_ex != null) ? trace_ex.pc : 'x;
    pc_wb_stage = (trace_wb != null) ? trace_wb.pc : 'x;
    pc_wb_delay_stage = (trace_wb_delay != null) ? trace_wb_delay.pc : 'x;
  end

  assign rd  = {rd_is_fp,  instr[11:07]};
  assign rs1 = {rs1_is_fp, instr[19:15]};
  assign rs2 = {rs2_is_fp, instr[24:20]};
  assign rs3 = {rs3_is_fp, instr[29:25]};
  assign rs4 = {rs3_is_fp, instr[31:27]};

  function void apply_reg_write(instr_trace_t trace, int unsigned reg_addr, int unsigned wdata);
    foreach (trace.regs_write[i])
      if (trace.regs_write[i].addr == reg_addr) begin
        trace.regs_write[i].value = wdata;
        `uvm_info(info_tag, $sformatf("Write mapped %0d, %0d:0x%08x pc:0x%08x",
                                       i, reg_addr, wdata, trace.pc), 
                  UVM_DEBUG)
      end
      else begin
        `uvm_info(info_tag, $sformatf("Unmapped write to %0d:0x%08x", reg_addr, wdata), UVM_DEBUG)
      end
  endfunction : apply_reg_write

  function void apply_mem_access(instr_trace_t trace, bit we, int unsigned addr, int unsigned wdata);
    mem_acc_t mem_acc;

    mem_acc.addr = addr;
    mem_acc.we   = we;

    if (we)
      mem_acc.wdata = wdata;
    else
      mem_acc.wdata = 'x;

    trace.mem_access.push_back(mem_acc);
  endfunction : apply_mem_access

  function instr_trace_t trace_new_instr();
      instr_trace_t trace;

      trace = new ();      
      trace.init(.cycles(cycles),
                 .pc(pc),
                 .compressed(compressed),
                 .instr(instr)
                );

    return trace;
  endfunction : trace_new_instr

  // Funnel all handoffs to the ISS here, note that this must be automatic
  // as multiple retire events may occur at a time (wb_bypass)
  always begin
    wait (trace_retire_q.size() != 0);
    trace_retire = trace_retire_q.pop_front();

    // Write signals and data structures used by step-and-compare
    insn_regs_write = trace_retire.regs_write;
    insn_disas      = trace_retire.str;
    insn_compressed = trace_retire.compressed;
    insn_pc         = trace_retire.pc;
    insn_val        = trace_retire.instr;
    insn_wb_bypass  = trace_retire.wb_bypass;

    trace_retire.printInstrTrace();

    ->retire;
    `ifdef ISS
    @(ovp_retire);
    `endif
    #0.1ns;
  end

  // ----------------------------------------------------------
  // Main pipeline model
  // ----------------------------------------------------------
  always @(negedge clk_i_d or negedge rst_n )begin
    if (!rst_n) begin
      
    end
    else begin
      trace_ex_clear = 0;
      trace_wb_clear = 0;
      trace_wb_delay_clear = 0;

      // Trace Writeback Delay stage
      if (trace_wb_delay) begin
        trace_retire_q.push_back(trace_wb_delay);
        trace_wb_delay_clear = 1;
      end

      // Trace Writeback stage
      if (trace_wb) begin
        if (wb_valid) begin
          if (trace_wb.str == "mret" || trace_wb.str == "uret" || trace_wb.str == "ebreak" || trace_wb.str == "c.ebreak") begin
            trace_wb_delay_q.push_back(trace_wb);
          end
          else begin            
            trace_retire_q.push_back(trace_wb);
          end

          trace_wb_clear = 1;
        end
      end

      // Check for advancing the pipe from EX
      if (trace_ex) begin      
        if (ex_valid && data_misaligned) 
          trace_ex.misaligned = 1;

        if (wb_bypass) begin
          trace_wb_bypass_q.push_back(trace_ex);
          trace_ex_clear = 1;          
        end
        else if (ex_valid && !data_misaligned) begin
          trace_wb_q.push_back(trace_ex);
          trace_ex_clear = 1;
        end
      end

      if (id_valid && is_decoding) begin
        if (!is_illegal)
          trace_ex_q.push_back(trace_new_instr());
      end

      // Try to pop queues
      if (trace_wb_delay_clear || trace_wb_delay == null)      
        if (trace_wb_delay_q.size())
          trace_wb_delay <= trace_wb_delay_q.pop_front();
        else
          trace_wb_delay <= null;

      if (trace_wb_clear || trace_wb == null)      
        if (trace_wb_q.size())
          trace_wb <= trace_wb_q.pop_front();
        else
          trace_wb <= null;

      if (trace_ex_clear || trace_ex == null)      
        if (trace_ex_q.size())
          trace_ex <= trace_ex_q.pop_front();
        else
          trace_ex <= null;

      // As a final step, if the wb_bypass queue has an entry and the trace_wb queue is empty,
      // then we also need to retire the trace_wb_bypass_q instruction
      if (trace_wb_bypass_q.size() && 
          !trace_wb_q.size() &&
           (trace_wb == null || trace_wb_clear)) begin
        while (trace_wb_bypass_q.size()) begin
          instr_trace_t trace_wb_bypass;

          trace_wb_bypass = trace_wb_bypass_q.pop_front();

          trace_wb_bypass.wb_bypass = 1;
          trace_retire_q.push_back(trace_wb_bypass);
        end
      end
    end
  end

  // Monitors for memory access and register writeback
  always @(negedge clk_i or negedge rst_n) begin
    if (!rst_n) begin
    end
    else begin
      // Register updates in EX
      if (ex_reg_we) begin
        `uvm_info(info_tag, $sformatf("EX: Reg WR %02d = 0x%08x", ex_reg_addr, ex_reg_wdata), UVM_DEBUG);
        if (trace_ex == null) begin
          `uvm_error(info_tag, $sformatf("EX: Reg WR %02d:0x%08x but no active EX instruction", ex_reg_addr, ex_reg_wdata));
        end
        else 
          apply_reg_write(trace_ex, ex_reg_addr, ex_reg_wdata);
      end

      // Register updates in WB
      if (wb_reg_we) begin
        `uvm_info(info_tag, $sformatf("WB: Reg WR %02d = 0x%08x", wb_reg_addr, wb_reg_wdata), UVM_DEBUG);
        if (trace_wb != null)
          apply_reg_write(trace_wb, wb_reg_addr, wb_reg_wdata);
        else if (trace_ex != null && trace_ex.misaligned)
          apply_reg_write(trace_ex, wb_reg_addr, wb_reg_wdata);
        else begin        
          `uvm_error(info_tag, $sformatf("WB: Reg WR %02d:0x%08x but no active WB instruction", wb_reg_addr, wb_reg_wdata));
        end
      end

      // Memory access in EX
      if (ex_data_req && ex_data_gnt) begin        
        if (ex_data_we) begin
          `uvm_info(info_tag, $sformatf("EX: Mem WR 0x%08x = 0x%08x", ex_data_addr, ex_data_wdata), UVM_DEBUG);
        end
        else begin
          `uvm_info(info_tag, $sformatf("EX: Mem RD 0x%08x = 0x%08x", ex_data_addr, ex_data_wdata), UVM_DEBUG);
        end
        if (trace_ex == null) begin
          `uvm_error(info_tag, $sformatf("EX: Mem %s 0x%08x:0x%08x but no active EX instruction", 
                                         ex_data_we ? "WR" : "RD", ex_data_addr, ex_reg_wdata));
        end
        else
          apply_mem_access(trace_ex, ex_data_we, ex_data_addr, ex_data_wdata);
      end
    end
  end

endmodule : cv32e40p_tracer


`endif // CV32E40P_TRACE_EXECUTION
