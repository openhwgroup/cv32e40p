// Copyright 2024 Dolphin Design
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
// Contributors: Halfdan Bechmann, Silicon Labs <halfdan.bechmann@silabs.com>     //
//               Yoann Pruvost, Dolphin Design <yoann.pruvost@dolphin.fr>         //
//                                                                                //
// Description:  CV32E40P RVFI tracer                                             //
//                                                                                //
////////////////////////////////////////////////////////////////////////////////////

module cv32e40p_rvfi_trace
  import cv32e40p_pkg::*;
  import cv32e40p_rvfi_pkg::*;
#(
    parameter FPU   = 0,
    parameter ZFINX = 0
) (
    input logic clk_i,
    input logic rst_ni,

    input logic [31:0] hart_id_i,

    input logic [31:0] imm_s3_type,

    input logic              rvfi_valid,
    input logic       [31:0] rvfi_insn,
    input integer            rvfi_start_cycle,
    input time               rvfi_start_time,
    input integer            rvfi_stop_cycle,
    input time               rvfi_stop_time,
    input logic       [31:0] rvfi_pc_rdata,
    input rvfi_trap_t        rvfi_trap,

    input logic [ 4:0] rvfi_rd_addr [1:0],
    input logic [31:0] rvfi_rd_wdata[1:0],

    input logic        rvfi_frd_wvalid[1:0],
    input logic [ 4:0] rvfi_frd_addr  [1:0],
    input logic [31:0] rvfi_frd_wdata [1:0],
    input logic        rvfi_2_rd,

    input logic [ 4:0] rvfi_rs1_addr,
    input logic [ 4:0] rvfi_rs2_addr,
    input logic [ 4:0] rvfi_rs3_addr,
    input logic [31:0] rvfi_rs1_rdata,
    input logic [31:0] rvfi_rs2_rdata,
    input logic [31:0] rvfi_rs3_rdata,

    input logic [ 4:0] rvfi_frs1_addr,
    input logic [ 4:0] rvfi_frs2_addr,
    input logic [ 4:0] rvfi_frs3_addr,
    input logic        rvfi_frs1_rvalid,
    input logic        rvfi_frs2_rvalid,
    input logic        rvfi_frs3_rvalid,
    input logic [31:0] rvfi_frs1_rdata,
    input logic [31:0] rvfi_frs2_rdata,
    input logic [31:0] rvfi_frs3_rdata,

    input logic [31:0] rvfi_mem_addr,
    input logic [31:0] rvfi_mem_rmask,
    input logic [31:0] rvfi_mem_wmask,
    input logic [31:0] rvfi_mem_rdata,
    input logic [31:0] rvfi_mem_wdata
);

  import cv32e40p_tracer_pkg::*;

  logic rst_n;
  assign rst_n = rst_ni;

  integer f;  //file pointer
  string fn;
  // integer cycles;
  string info_tag;

  logic is_compressed;
  logic [31:0] decomp_insn;

  logic [5:0] rd, rs1, rs2, rs3, rs4;
  //TODO get from rvfi
  logic [31:0] rs1_value;
  logic [31:0] rs2_value;
  logic [31:0] rs3_value;

  logic [31:0] rs2_value_vec;

  logic [31:0] imm_u_type;
  logic [31:0] imm_uj_type;
  logic [31:0] imm_i_type;
  logic [11:0] imm_iz_type;
  logic [31:0] imm_z_type;
  logic [31:0] imm_s_type;
  logic [31:0] imm_sb_type;
  logic [31:0] imm_s2_type;
  logic [31:0] imm_vs_type;
  logic [31:0] imm_vu_type;
  logic [31:0] imm_shuffle_type;
  logic [ 4:0] imm_clip_type;

  always_comb begin
    if (rvfi_frs1_rvalid) begin
      rs1 = {1'b1, rvfi_frs1_addr};
      rs1_value = rvfi_frs1_rdata;
    end else begin
      rs1 = {1'b0, rvfi_rs1_addr};
      rs1_value = rvfi_rs1_rdata;
    end
    if (rvfi_frs2_rvalid) begin
      rs2 = {1'b1, rvfi_frs2_addr};
      rs2_value = rvfi_frs2_rdata;
    end else begin
      rs2 = {1'b0, rvfi_rs2_addr};
      rs2_value = rvfi_rs2_rdata;
    end

    if (rvfi_frs3_rvalid) begin
      rs3 = {1'b1, rvfi_frs3_addr};
      rs3_value = rvfi_frs3_rdata;
    end else begin
      rs3 = {1'b0, rvfi_rs3_addr};
      rs3_value = rvfi_rs3_rdata;
    end

    if (rvfi_2_rd) begin
      if (rvfi_frd_wvalid[1]) begin
        rd = {1'b1, rvfi_frd_addr[1]};
      end else begin
        rd = {1'b0, rvfi_rd_addr[1]};
      end
    end else if (rvfi_frd_wvalid[0]) begin
      rd = {1'b1, rvfi_frd_addr[0]};
    end else begin
      rd = {1'b0, rvfi_rd_addr[0]};
    end
  end

  assign rs4 = rs3;

  cv32e40p_compressed_decoder #(
      .FPU(FPU)
  ) rvfi_trace_decompress_i (
      .instr_i(rvfi_insn),
      .instr_o(decomp_insn),
      .is_compressed_o(is_compressed)
  );

  assign imm_i_type = {{20{decomp_insn[31]}}, decomp_insn[31:20]};
  assign imm_iz_type = {20'b0, decomp_insn[31:20]};
  assign imm_s_type = {{20{decomp_insn[31]}}, decomp_insn[31:25], decomp_insn[11:7]};
  assign imm_sb_type = {
    {19{decomp_insn[31]}},
    decomp_insn[31],
    decomp_insn[7],
    decomp_insn[30:25],
    decomp_insn[11:8],
    1'b0
  };
  assign imm_u_type = {decomp_insn[31:12], 12'b0};
  assign imm_uj_type = {
    {12{decomp_insn[31]}}, decomp_insn[19:12], decomp_insn[20], decomp_insn[30:21], 1'b0
  };

  assign imm_z_type = '0;  //{27'b0, decomp_insn[REG_S1_MSB:REG_S1_LSB]};

  assign imm_s2_type = {27'b0, decomp_insn[24:20]};
  assign imm_vs_type = '0;
  assign imm_vu_type = '0;
  assign imm_shuffle_type = '0;
  assign imm_clip_type = '0;

  `include "cv32e40p_instr_trace.svh"
instr_trace_t trace_retire;

  function instr_trace_t trace_new_instr();
    instr_trace_t trace;
    trace = new();
    trace.external_time = 1;
    trace.simtime = rvfi_start_time - 1ns;
    trace.stoptime = rvfi_stop_time;
    trace.stopcycles = rvfi_stop_cycle;
    trace.ctx = (rvfi_trap.trap) ? "(C)" : "";
    trace.init(.cycles(rvfi_start_cycle), .pc(rvfi_pc_rdata), .compressed(is_compressed),
               .instr(decomp_insn));
    return trace;
  endfunction : trace_new_instr

  function void apply_reg_write();
    foreach (trace_retire.regs_write[i]) begin
      if (rvfi_frd_wvalid[1] && (trace_retire.regs_write[i].addr == {1'b1, rvfi_frd_addr[1]})) begin
        trace_retire.regs_write[i].value = rvfi_frd_wdata[1];
      end else if (trace_retire.regs_write[i].addr == rvfi_rd_addr[1]) begin
        trace_retire.regs_write[i].value = rvfi_rd_wdata[1];
      end
    end
    foreach (trace_retire.regs_write[i]) begin
      if (rvfi_frd_wvalid[0] && (trace_retire.regs_write[i].addr == {1'b1, rvfi_frd_addr[0]})) begin
        trace_retire.regs_write[i].value = rvfi_frd_wdata[0];
      end else if (trace_retire.regs_write[i].addr == rvfi_rd_addr[0]) begin
        trace_retire.regs_write[i].value = rvfi_rd_wdata[0];
      end
    end
  endfunction : apply_reg_write

  function void apply_mem_access();
    mem_acc_t mem_acc;

    mem_acc.addr = rvfi_mem_addr;
    if (rvfi_mem_wmask) begin
      mem_acc.we    = 1'b1;
      mem_acc.wdata = rvfi_mem_wdata;
      trace_retire.mem_access.push_back(mem_acc);
    end else if (rvfi_mem_rmask) begin
      mem_acc.we = 1'b0;
      mem_acc.wdata = 'x;
      trace_retire.mem_access.push_back(mem_acc);
    end
  endfunction : apply_mem_access

  string        insn_disas;
  logic  [31:0] insn_pc;
  logic  [31:0] insn_val;

  always @(posedge clk_i) begin
    if (rvfi_valid) begin
      trace_retire = trace_new_instr();
      apply_reg_write();
      apply_mem_access();
      trace_retire.printInstrTrace();
      insn_disas = trace_retire.str;
      insn_pc    = trace_retire.pc;
      insn_val   = trace_retire.instr;
    end
  end

  initial begin
    wait(rst_n == 1'b1);
    $sformat(fn, "trace_core.log");
    $sformat(info_tag, "CORE_TRACER %2d", hart_id_i);
    $display("[%s] Output filename is: %s", info_tag, fn);
    f = $fopen(fn, "w");
    $fwrite(f,
            "            Time           Cycle PC       Instr    Ctx Decoded instruction Register and memory contents                                 Stop cycle  Stop time\n");
  end



endmodule
