// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Wrapper for a fpnew
// Contributor: Davide Schiavone <davide@openhwgroup.org>

module cv32e40p_fp_wrapper
  import cv32e40p_apu_core_pkg::*;
#(
    parameter FPU_ADDMUL_LAT = 3,  // Floating-Point ADDition/MULtiplication computing lane pipeline registers number
    parameter FPU_OTHERS_LAT = 0  // Floating-Point COMParison/CONVersion computing lanes pipeline registers number
) (
    // Clock and Reset
    input logic clk_i,
    input logic rst_ni,

    // APU Side: Master port
    input  logic apu_req_i,
    output logic apu_gnt_o,

    // request channel
    input logic [   APU_NARGS_CPU-1:0][31:0] apu_operands_i,
    input logic [     APU_WOP_CPU-1:0]       apu_op_i,
    input logic [APU_NDSFLAGS_CPU-1:0]       apu_flags_i,
    input logic fpu_en_i,

    // response channel
    output logic                        apu_rvalid_o,
    output logic [                31:0] apu_rdata_o,
    output logic [APU_NUSFLAGS_CPU-1:0] apu_rflags_o
);


  import cv32e40p_pkg::*;
  import fpnew_pkg::*;

  logic [        fpnew_pkg::OP_BITS-1:0] fpu_op;
  logic                                  fpu_op_mod;
  logic                                  fpu_vec_op;

  logic [ fpnew_pkg::FP_FORMAT_BITS-1:0] fpu_dst_fmt;
  logic [ fpnew_pkg::FP_FORMAT_BITS-1:0] fpu_src_fmt;
  logic [fpnew_pkg::INT_FORMAT_BITS-1:0] fpu_int_fmt;
  logic [                      C_RM-1:0] fp_rnd_mode;
  logic [                31:0] intermediate_result_fp16, intermediate_result_fpnew; // type of muxintermediate_result_fp16, intermediate_result_fpnew; // type of mux
  logic apu_rvalid_o_fp16, apu_rvalid_o_fpnew;
  logic apu_gnt_o_fp16, apu_gnt_o_fpnew;



  // assign apu_rID_o = '0;
  assign {fpu_vec_op, fpu_op_mod, fpu_op}                     = apu_op_i;

  assign {fpu_int_fmt, fpu_src_fmt, fpu_dst_fmt, fp_rnd_mode} = apu_flags_i;
// Select the output based on enable_bit
// always_comb begin
//   if(fpu_en_i) begin
//      apu_rdata_o = intermediate_result_fp16;
//      apu_rvalid_o = apu_rvalid_o_fp16;
//      apu_gnt_o = apu_gnt_o_fp16;
//   end
//   else begin
//      apu_rdata_o = intermediate_result_fpnew;
//      apu_rvalid_o = apu_rvalid_o_fpnew;
//      apu_gnt_o = apu_gnt_o_fpnew;
//   end
// end

  // -----------
  // FPU Config
  // -----------
  // Features (enabled formats, vectors etc.)
  localparam fpnew_pkg::fpu_features_t FPU_FEATURES = '{
      Width: C_FLEN,
      EnableVectors: C_XFVEC,
      EnableNanBox: 1'b0,
      FpFmtMask: {
    C_RVF, C_RVD, C_XF16, C_XF8, C_XF16ALT
  }, IntFmtMask: {
    C_XFVEC && C_XF8, C_XFVEC && (C_XF16 || C_XF16ALT), 1'b1, 1'b0
  }};

  // Implementation (number of registers etc)
  localparam fpnew_pkg::fpu_implementation_t FPU_IMPLEMENTATION = '{
      PipeRegs: '{  // FP32, FP64, FP16, FP8, FP16alt
      '{
          FPU_ADDMUL_LAT, C_LAT_FP64, C_LAT_FP16, C_LAT_FP8, C_LAT_FP16ALT
      },  // ADDMUL
      '{default: C_LAT_DIVSQRT},  // DIVSQRT
      '{default: FPU_OTHERS_LAT},  // NONCOMP
      '{default: FPU_OTHERS_LAT}
  },  // CONV
  UnitTypes: '{
      '{default: fpnew_pkg::MERGED},  // ADDMUL
      '{default: fpnew_pkg::MERGED},  // DIVSQRT
      '{default: fpnew_pkg::PARALLEL},  // NONCOMP
      '{default: fpnew_pkg::MERGED}
  },  // CONV
  PipeConfig: fpnew_pkg::AFTER};

  //---------------
  // FPU instance
  //---------------

  // fpnew_top #(
  //     .Features      (FPU_FEATURES),
  //     .Implementation(FPU_IMPLEMENTATION),
  //     .PulpDivsqrt   (1'b0),
  //     .TagType       (logic)
  // ) i_fpnew_bulk (
  //     .clk_i         (clk_i),
  //     .rst_ni        (rst_ni),
  //     .operands_i    (apu_operands_i),
  //     .rnd_mode_i    (fpnew_pkg::roundmode_e'(fp_rnd_mode)),
  //     .op_i          (fpnew_pkg::operation_e'(fpu_op)),
  //     .op_mod_i      (fpu_op_mod),
  //     .src_fmt_i     (fpnew_pkg::fp_format_e'(fpu_src_fmt)),
  //     .dst_fmt_i     (fpnew_pkg::fp_format_e'(fpu_dst_fmt)),
  //     .int_fmt_i     (fpnew_pkg::int_format_e'(fpu_int_fmt)),
  //     .vectorial_op_i(fpu_vec_op),
  //     .tag_i         (1'b0),
  //     .simd_mask_i   (1'b0),
  //     .in_valid_i    (apu_req_i & !fpu_en_i),
  //     .in_ready_o    (apu_gnt_o_fpnew),
  //     .flush_i       (1'b0),
  //     .result_o      (intermediate_result_fpnew),
  //     .status_o      (apu_rflags_o),
  //     .tag_o         (  /* unused */),
  //     .out_valid_o   (apu_rvalid_o_fpnew),
  //     .out_ready_i   (1'b1),
  //     .busy_o         (  /* unused */)
  // );


bf16_accelerator_top i_fp_16_bulk (
      .clk           (clk_i),
      .reset         (rst_ni),
      .enable        (1'b1),
      .operand_a     (apu_operands_i[0]),
      .operand_b     (apu_operands_i[1]),
      .operand_c     (apu_operands_i[2]),
      .operation     (cv32e40p_fpu_pkg::custom_operation_e'(fpu_op)),
      .in_valid_i    (apu_req_i),
      .in_ready_o    (apu_gnt_o),
      .out_ready_i   (1'b1),
      .out_valid_o   (apu_rvalid_o),
      .result        (apu_rdata_o),
      .fpcsr         (apu_rflags_o)
  );
endmodule  // cv32e40p_fp_wrapper

