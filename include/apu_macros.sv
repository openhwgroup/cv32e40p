/* Copyright (C) 2017 ETH Zurich, University of Bologna
 * All rights reserved.
 *
 * This code is under development and not yet released to the public.
 * Until it is released, the code is under the copyright of ETH Zurich and
 * the University of Bologna, and may contain confidential and/or unpublished
 * work. Any reuse/redistribution is strictly forbidden without written
 * permission from ETH Zurich.
 *
 * Bug fixes and contributions will eventually be released under the
 * SolderPad open hardware license in the context of the PULP platform
 * (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
 * University of Bologna.
 */

// macros for using the APU system; these are intended to move an instruction
// that is implemented in the core into an APU with one line, and be auto-
// deactivated when the corresponding APU is not implemented

import apu_core_package::*;

// Source/Destination register instruction index
`define REG_S1 19:15
`define REG_S2 24:20
`define REG_S3 29:25
`define REG_D  11:07
// floating point rounding mode
`define REG_RM 14:12

`define USE_APU_DSP_MULT if (SHARED_DSP_MULT) begin\
                            mult_int_en_o   = 1'b0;\
                            mult_dot_en_o   = 1'b0;\
                            apu_en          = 1'b1;\
                            apu_type_o      = APUTYPE_DSP_MULT;\
                            apu_flags_src_o = APU_FLAGS_DSP_MULT;\
                            apu_op_o        = mult_operator_o;\
                            apu_lat_o       = (PIPE_REG_DSP_MULT==1) ? 2'h2 : 2'h1;\
                         end

`define USE_APU_INT_MULT if (SHARED_INT_MULT) begin\
                            mult_int_en_o   = 1'b0;\
                            mult_dot_en_o   = 1'b0;\
                            apu_en          = 1'b1;\
                            apu_flags_src_o = APU_FLAGS_INT_MULT;\
                            apu_op_o        = mult_operator_o;\
                            apu_type_o      = APUTYPE_INT_MULT;\
                            apu_lat_o       = 2'h1;\
                         end

`define USE_APU_INT_DIV if (SHARED_INT_DIV) begin\
                           alu_en_o = 1'b0;\
                           apu_en = 1'b1;\
                           apu_type_o = APUTYPE_INT_DIV;\
                           apu_op_o = alu_operator_o;\
                           apu_lat_o       = 2'h3;\
                         end

`define FP_2OP if (FPU==1) begin\
                 apu_en              = 1'b1;\
                 alu_en_o            = 1'b0;\
                 apu_flags_src_o     = APU_FLAGS_FP;\
                 rega_used_o         = 1'b1;\
                 regb_used_o         = 1'b1;\
                 reg_fp_a_o          = 1'b1;\
                 reg_fp_b_o          = 1'b1;\
                 reg_fp_d_o          = 1'b1;\
               end

`define FP_3OP if (FPU==1) begin\
                 apu_en              = 1'b1;\
                 alu_en_o            = 1'b0;\
                 apu_flags_src_o     = APU_FLAGS_FP;\
                 rega_used_o         = 1'b1;\
                 regb_used_o         = 1'b1;\
                 regc_used_o         = 1'b1;\
                 reg_fp_a_o          = 1'b1;\
                 reg_fp_b_o          = 1'b1;\
                 reg_fp_c_o          = 1'b1;\
                 reg_fp_d_o          = 1'b1;\
                 regc_mux_o          = REGC_S4;\
               end

