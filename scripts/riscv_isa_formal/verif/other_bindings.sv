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
	.dmem_req_we         (data_we_o),
	.dmem_req_be         (data_be_o),
	.dmem_req_size       (),
	.dmem_req_sign       (),

	// Exceptions & Debug
	.is_sstep            (debug_single_step),
	.xcpt_bp_if          (),
	.xcpt_bp_ld          (),
	.xcpt_bp_samo        (),
	.xcpt_dbg_bp_if      (),
	.xcpt_dbg_bp_ld      (),
	.xcpt_dbg_bp_samo    (),
	.xcpt_af_instr_1st   (),
	.xcpt_af_instr_2nd   (),
	.xcpt_af_ld_1st      (),
	.xcpt_af_ld_2nd      (),
	.xcpt_af_samo_1st    (),
	.xcpt_af_samo_2nd    (),
	.xcpt_pf_instr_1st   (),
	.xcpt_pf_instr_2nd   (),
	.xcpt_pf_ld_1st      (),
	.xcpt_pf_ld_2nd      (),
	.xcpt_pf_samo_1st    (),
	.xcpt_pf_samo_2nd    (),
	.xcpt_ma_ld          (),
	.xcpt_ma_samo        (),

	// Multiplication & Division
	.mul_op_valid        (),
	.mul_op_a            (ex_stage_i.mult_i.op_a_i),
	.mul_op_b            (ex_stage_i.mult_i.op_b_i),
	.mul_op_c            (ex_stage_i.mult_i.op_c_i),
	.mul_result          (ex_stage_i.mult_i.result_o),
	.mul_result_valid    (),
	.div_op_valid        (),
	.div_op_a            (ex_stage_i.alu_i.alu_div_i.OpA_DI),
	.div_op_b            (ex_stage_i.alu_i.alu_div_i.OpB_DI),
	.div_op_b_shift      (ex_stage_i.alu_i.alu_div_i.OpBShift_DI),
	.div_result          (ex_stage_i.alu_i.alu_div_i.Res_DO),
	.div_result_valid    (ex_stage_i.alu_i.div_ready),

	// Floating point
	.fpu_op_valid        (ex_stage_i.apu_req),
	.fpu_op_a            (ex_stage_i.apu_operands_o[0]),
	.fpu_op_b            (ex_stage_i.apu_operands_o[1]),
	.fpu_op_c            (ex_stage_i.apu_operands_o[2]),
	.fpu_rm              (),
	.fpu_flags           (ex_stage_i.fpu_fflags_o),
	.fpu_result          (ex_stage_i.apu_result),
	.fpu_result_valid    (ex_stage_i.apu_valid),

	// Design specific
	.is_debug            (id_stage_i.controller_i.ctrl_fsm_cs inside {DBG_TAKEN_ID,DBG_TAKEN_IF,DBG_FLUSH}),
	.is_interrupt        (id_stage_i.int_controller_i.irq_req_ctrl_o),
	.boot_addr           ({boot_addr_i[31:2],2'b00}),

	.rf_we_lsu           (ex_stage_i.regfile_we_lsu),
	.rf_waddr_lsu        (ex_stage_i.regfile_waddr_lsu),
	.lsu_data_type       (load_store_unit_i.data_type_q),
	.lsu_data_sign       (load_store_unit_i.data_sign_ext_q),
	.lsu_data_offset     (load_store_unit_i.rdata_offset_q),
	.fpu_s_cycle         (ex_stage_i.apu_singlecycle),
	.fpu_m_cycle         (ex_stage_i.apu_multicycle),
	.fpu_waddr           (ex_stage_i.apu_waddr),
	.fpu_waddr_ex        (apu_waddr_ex),
	.fpu_lat_ex          (apu_lat_ex),
	.fpu_op_ex           (apu_op_ex),
	.dot_mul_op_a        (ex_stage_i.mult_dot_op_a_i),
	.dot_mul_op_b        (ex_stage_i.mult_dot_op_b_i),
	.dot_mul_op_c        (ex_stage_i.mult_dot_op_c_i)
