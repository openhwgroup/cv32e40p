
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
  string fn;
  integer cycles;
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

  assign rd = rvfi_rd_addr;
  assign rs1 = rvfi_rs1_addr;
  assign rs2 = rvfi_rs2_addr;
  assign rs3 = '0;
  assign rs4 = '0;

  assign rs1_value = rvfi_rs1_rdata;
  assign rs2_value = rvfi_rs2_rdata;
  assign rs3_value = rvfi_rd_wdata;

  assign imm_i_type = {{20{rvfi_insn[31]}}, rvfi_insn[31:20]};
  assign imm_iz_type = {20'b0, rvfi_insn[31:20]};
  assign imm_s_type = {{20{rvfi_insn[31]}}, rvfi_insn[31:25], rvfi_insn[11:7]};
  assign imm_sb_type = {
    {19{rvfi_insn[31]}}, rvfi_insn[31], rvfi_insn[7], rvfi_insn[30:25], rvfi_insn[11:8], 1'b0
  };
  assign imm_u_type = {rvfi_insn[31:12], 12'b0};
  assign imm_uj_type = {
    {12{rvfi_insn[31]}}, rvfi_insn[19:12], rvfi_insn[20], rvfi_insn[30:21], 1'b0
  };

  assign imm_z_type = '0;  //{27'b0, rvfi_insn[REG_S1_MSB:REG_S1_LSB]};

  assign imm_s2_type = {27'b0, rvfi_insn[24:20]};
  assign imm_vs_type = '0;
  assign imm_vu_type = '0;
  assign imm_shuffle_type = '0;
  assign imm_clip_type = '0;

  cv32e40p_compressed_decoder #(
      .FPU(1)
  ) rvfi_trace_decompress_i (
      .instr_i(rvfi_insn),
      .instr_o(decomp_insn),
      .is_compressed_o(is_compressed)
  );

  localparam FPU = 0;
  localparam PULP_ZFINX = 0;
  `include "cv32e40p_instr_trace.svh"
instr_trace_t trace_retire;

  function instr_trace_t trace_new_instr();
    instr_trace_t trace;
    trace = new();
    trace.init(.cycles(cycles), .pc(rvfi_pc_rdata), .compressed(is_compressed),
               .instr(decomp_insn));
    return trace;
  endfunction : trace_new_instr

  function void apply_reg_write();
    foreach (trace_retire.regs_write[i])
      if (trace_retire.regs_write[i].addr == rvfi_rd_addr) begin
        trace_retire.regs_write[i].value = rvfi_rd_wdata;
      end
  endfunction : apply_reg_write

  // cycle counter
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (rst_ni == 1'b0) cycles <= 0;
    else cycles <= cycles + 1;
  end

  always @(posedge clk_i) begin
    if (rvfi_valid) begin
      trace_retire = trace_new_instr();
      apply_reg_write();
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
