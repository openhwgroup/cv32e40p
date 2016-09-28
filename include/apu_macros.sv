// Copyright 2015 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// macros for using the APU system; these are intended to move an instruction
// that is implemented in the core into an APU with one line, and be auto-
// deactivated when the corresponding APU is not implemented

`include "apu_defines.sv"

`ifdef SHARED_DSP_MULT
`define USE_APU_DSP_MULT mult_int_en_o = 1'b0;\
                         mult_dot_en_o = 1'b0;\
                         apu_en = 1'b1;\
                         apu_type_o = APUTYPE_DSP2;\
                         apu_flags_src_o = APUTYPE_DSP2;\
                         apu_op_o = mult_operator_o;
`else
`define USE_APU_DSP_MULT
`endif

`ifdef SHARED_DSP_FAST_INTMUL
`define USE_APU_DSP_MULT_FAST mult_int_en_o = 1'b0;\
                              mult_dot_en_o = 1'b0;\
                              apu_en = 1'b1;\
                              apu_type_o = APUTYPE_DSP1;\
                              apu_flags_src_o = APUTYPE_DSP2;\
                              apu_op_o = mult_operator_o;

`else
`define USE_APU_DSP_MULT_FAST `USE_APU_DSP_MULT
`endif

`ifdef SHARED_DSP_ALU
`define USE_APU_DSP_ALU alu_en_o = 1'b0;\
                        apu_en = 1'b1;\
                        apu_type_o = APUTYPE_DSP1;\
                        apu_flags_src_o = APUTYPE_DSP1;\
                        apu_op_o = alu_operator_o;
`else 
`define USE_APU_DSP_ALU
`endif

`ifdef SHARED_DSP_ITER
`define USE_APU_DSP_ALU_ITER alu_en_o = 1'b0;\
                             apu_en = 1'b1;\
                             apu_type_o = APUTYPE_DSP3;\
                             apu_flags_src_o = APUTYPE_DSP3;\
                             apu_op_o = alu_operator_o;
`else 
`define USE_APU_DSP_ALU_ITER
`endif

`ifdef SHARED_DSP_ITER
`define USE_APU_DSP_MULT_ITER mult_int_en_o = 1'b0;\
                              mult_dot_en_o = 1'b0;\
                              apu_en = 1'b1;\
                              apu_type_o = APUTYPE_DSP3;\
                              apu_flags_src_o = APUTYPE_DSP3;\
                              apu_op_o = mult_operator_o;
`else 
`define USE_APU_DSP_MULT_ITER
`endif
