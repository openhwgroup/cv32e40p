
module cv32e40p_rvfi_trace
  import cv32e40p_pkg::*;
(
    input logic clk_i,
    input logic rst_ni,

    input logic [31:0] hart_id_i,

    input logic [31:0] imm_s3_type,

    input logic        rvfi_valid,
    input logic [31:0] rvfi_insn,
    input logic [31:0] rvfi_pc_rdata,

    input logic [ 4:0] rvfi_rd_addr,
    input logic [31:0] rvfi_rd_wdata,
    input logic [ 4:0] rvfi_rs1_addr,
    input logic [ 4:0] rvfi_rs2_addr,
    input logic [31:0] rvfi_rs1_rdata,
    input logic [31:0] rvfi_rs2_rdata
);

  import cv32e40p_tracer_pkg::*;

  logic rst_n;
  assign rst_n = rst_ni;

  integer f;  //file pointer
  string  fn;
  integer cycles;
  string  info_tag;

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

  assign rd = rvfi_rd_addr;
  assign rs1 = rvfi_rs1_addr;
  assign rs2 = rvfi_rs2_addr;
  assign rs3 = '0;
  assign rs4 = '0;

  assign rs1_value = rvfi_rs1_rdata;
  assign rs2_value = rvfi_rs2_rdata;
  assign rs3_value = rvfi_rd_wdata;

  assign imm_u_typ = '0;
  assign imm_uj_typ = '0;
  assign imm_i_typ = '0;
  assign imm_iz_typ = '0;
  assign imm_z_typ = '0;
  assign imm_s_typ = '0;
  assign imm_sb_typ = '0;
  assign imm_s2_typ = '0;
  assign imm_vs_typ = '0;
  assign imm_vu_typ = '0;
  assign imm_shuffle_typ = '0;
  assign imm_clip_typ = '0;

  localparam FPU = 0;
  localparam PULP_ZFINX = 0;
  `include "cv32e40p_instr_trace.svh"
instr_trace_t trace_retire;

  function instr_trace_t trace_new_instr();
    instr_trace_t trace;

    trace = new();
    trace.init(.cycles(cycles), .pc(rvfi_pc_rdata), .compressed(0), .instr(rvfi_insn));
    return trace;
  endfunction : trace_new_instr

  // cycle counter
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (rst_ni == 1'b0) cycles <= 0;
    else cycles <= cycles + 1;
  end

  always @(posedge clk_i) begin
    if (rvfi_valid) begin
      trace_retire = trace_new_instr();

      trace_retire.printInstrTrace();
    end
  end

  initial begin
    wait(rst_n == 1'b1);
    $sformat(fn, "trace_core.log");
    $sformat(info_tag, "CORE_TRACER %2d", hart_id_i);
    $display("[%s] Output filename is: %s", info_tag, fn);
    f = $fopen(fn, "w");
    $fwrite(f, "Time\tCycle\tPC\tInstr\tDecoded instruction\tRegister and memory contents\n");
  end



endmodule
