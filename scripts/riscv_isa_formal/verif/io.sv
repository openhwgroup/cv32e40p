// Copyright 2024 Siemens
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

	// Data memory interface
	input                 dmem_req_we         ='0, // Data memory request type
	input[3:0]            dmem_req_be         ='0, // Data memory request byte enable
	input[1:0]            dmem_req_size       ='0, // Data memory request size
	input                 dmem_req_sign       ='0, // Data memory request sign

	// Exceptions & Debug
	input                 is_sstep            ='0, // Single stepping of debug mode
	input                 xcpt_bp_if          ='0, // Instruction address breakpoint exception
	input                 xcpt_bp_ld          ='0, // Load address breakpoint exception
	input                 xcpt_bp_samo        ='0, // Store/ AMO address breakpoint exception
	input                 xcpt_dbg_bp_if      ='0, // Debug instruction address breakpoint exception
	input                 xcpt_dbg_bp_ld      ='0, // Debug load address breakpoint exception
	input                 xcpt_dbg_bp_samo    ='0, // Debug Store/ AMO address breakpoint exception
	input                 xcpt_af_instr_1st   ='0, // Instruction access fault exception
	input                 xcpt_af_instr_2nd   ='0, // Instruction second access fault exception
	input                 xcpt_af_ld_1st      ='0, // Load access fault exception
	input                 xcpt_af_ld_2nd      ='0, // Load second access fault exception
	input                 xcpt_af_samo_1st    ='0, // Store/ AMO access fault exception
	input                 xcpt_af_samo_2nd    ='0, // Store/ AMO second access fault exception
	input                 xcpt_pf_instr_1st   ='0, // Instruction page fault exception
	input                 xcpt_pf_instr_2nd   ='0, // Instruction second access page fault exception
	input                 xcpt_pf_ld_1st      ='0, // Load page fault exception
	input                 xcpt_pf_ld_2nd      ='0, // Load second access page fault exception
	input                 xcpt_pf_samo_1st    ='0, // Store/ AMO page fault exception
	input                 xcpt_pf_samo_2nd    ='0, // Store/ AMO second access page fault exception
	input                 xcpt_ma_ld          ='0, // Load address misaligned exception
	input                 xcpt_ma_samo        ='0, // Store/AMO address misaligned exception

	// Multiplication & Division
	input                 mul_op_valid        ='0, // Multiplication operation validity
	input[XLEN-1:0]       mul_op_a            ='0, // Multiplication first source operand
	input[XLEN-1:0]       mul_op_b            ='0, // Multiplication second source operand
	input[XLEN-1:0]       mul_op_c            ='0, // Multiplication third source operand
	input[XLEN-1:0]       mul_result          ='0, // Multiplication operation result
	input                 mul_result_valid    ='0, // Multiplication operation result validity
	input                 div_op_valid        ='0, // Division operation validity
	input[XLEN-1:0]       div_op_a            ='0, // Division first source operand
	input[XLEN-1:0]       div_op_b            ='0, // Division second source operand
	input[$clog2(XLEN):0] div_op_b_shift      ='0, // Division second source operand shift amount
	input[XLEN-1:0]       div_result          ='0, // Division operation result
	input                 div_result_valid    ='0, // Division operation result validity

	// Floating point
	input                 fpu_op_valid        ='0, // FPU operation validity
	input[XLEN-1:0]       fpu_op_a            ='0, // FPU first source operand
	input[XLEN-1:0]       fpu_op_b            ='0, // FPU second source operand
	input[XLEN-1:0]       fpu_op_c            ='0, // FPU third source operand
	input Frm             fpu_rm              ='0, // FPU rounding mode
	input Fflags          fpu_flags           ='0, // FPU flags
	input[XLEN-1:0]       fpu_result          ='0, // FPU operation result
	input                 fpu_result_valid    ='0, // FPU operation result validity

	// Design specific
	input                 is_debug            ='0, // Core is about to enter debug mode
	input                 is_interrupt        ='0, // Core is about to encounter an interrupt
	input[XLEN-1:0]       boot_addr           ='0, // Boot address

	input                 rf_we_lsu           ='0,
	input[5:0]            rf_waddr_lsu        ='0,
	input[1:0]            lsu_data_type       ='0,
	input[1:0]            lsu_data_sign       ='0,
	input[1:0]            lsu_data_offset     ='0,
	input                 fpu_s_cycle         ='0,
	input                 fpu_m_cycle         ='0,
	input[5:0]            fpu_waddr           ='0,
	input[5:0]            fpu_waddr_ex        ='0,
	input[1:0]            fpu_lat_ex          ='0,
	input[5:0]            fpu_op_ex           ='0,
	input[XLEN-1:0]       dot_mul_op_a        ='0,
	input[XLEN-1:0]       dot_mul_op_b        ='0,
	input[XLEN-1:0]       dot_mul_op_c        ='0
