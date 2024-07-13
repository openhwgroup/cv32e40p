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

/*********************/
// CONSTRAINTS
/*********************/

// MAIN CONSTRAINTS //

const_addrs_c   : assume property (##1 $stable({boot_addr,`core.dm_halt_addr_i,`core.dm_exception_addr_i,`core.mtvec_addr_i,`core.hart_id_i}));
const_dm_addr_c : assume property (`core.dm_halt_addr_i==32'h800 && `core.dm_exception_addr_i==32'h808); // **I** To meet app expectations

`ifdef CFG_XP
`ifdef CV_LOOP
	// raising of hwloop illegal currently not modeled
	no_hwloop_illegal_c      : assume property (!id_stage_i.controller_i.is_hwlp_illegal);

    // hwloop must contain 3+ instructions
	hwloop_min_size_c        : assume property (!(id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_counter_q[0]>0&&id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_end_q[0]-id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_start_q[0] inside {32'h0,32'h4,32'h8}) && !(id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_counter_q[1]>0&&id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_end_q[1]-id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_start_q[1] inside {32'h0,32'h4,32'h8}));

	// hwloop must be word-aligned
	hwloop_aligned_c         : assume property (id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_start_q[0][1:0]==0 && id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_end_q[0][1:0]==0 && id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_start_q[1][1:0]==0 && id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_end_q[1][1:0]==0);

	// we must not create loop 0 in the middle of itself (setting count to non-zero at a PC location that would qualify as inside the loop). Also, setting up the registers and then jumping to a location inside loop 0 will likely not work
	loop0_setup_c            : assume property (id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_counter_q[0]==0 ##1 id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_counter_q[0]!=0 |-> id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_start_q[0]==$past(pc_id)+32'd4);

	// we must not create loop 1 in the middle of itself (setting count to non-zero at a PC location that would qualify as inside the loop). Also, setting up the registers and then jumping to a location inside loop 1 will likely not work
	loop1_setup_c            : assume property (id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_counter_q[1]==0 ##1 id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_counter_q[1]!=0 |-> id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_start_q[1]==$past(pc_id)+32'd4);

	// let's not wrap
	lopp_no_wrap_c           : assume property (!(id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_counter_q[0]>0&&id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_end_q[0]<id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_start_q[0]) && !(id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_counter_q[1]>0&&id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_end_q[1]<id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_start_q[1]));

	// do not modify loop 0 inside body 0
	loop0_no_modify_c        : assume property (!(id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_counter_q[0]>0 && pc_id>=id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_start_q[0] && pc_id<id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_end_q[0] && (id_stage_i.controller_i.branch_in_id_dec || id_stage_i.controller_i.jump_in_dec || id_stage_i.hwlp_regid==0 && id_stage_i.hwlp_we)));

	// do not modify loop 1 inside body 1
	loop1_no_modify_c        : assume property (!(id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_counter_q[1]>0 && pc_id>=id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_start_q[1] && pc_id<id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_end_q[1] && (id_stage_i.controller_i.branch_in_id_dec || id_stage_i.controller_i.jump_in_dec || id_stage_i.hwlp_regid==1 && id_stage_i.hwlp_we)));

	// do not setup a count of 1 (not always decrementing to 0 on reaching loop end)
	loop_count_gt1_c         : assume property (!(id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_we_i[2] && id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_cnt_data_i==1));

	// loop 1 is outer loop
	loop1_ouuter_loop_c      : assume property (!(id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_counter_q[0]>0 && id_stage_i.hwlp_regid==1 && id_stage_i.hwlp_we));

	// end addresses 8 apart
	loop_end_min_sitance_c   : assume property (!(id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_counter_q[0]>0 && id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_counter_q[1]>0 && id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_end_q[1]<id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_end_q[0]+33'h8));

	// do not setup illegal end address in inner loop
	loop_inner_address_c     : assume property (!(id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_counter_q[1]>0 && id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_we_i[1] && !id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_regid_i &&id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_end_q[1]<id_stage_i.gen_hwloop_regs.hwloop_regs_i.hwlp_end_data_i+33'h8));

	// memory stalls in hwloops seem problematic (ebreak retires before earlier dmem instruction)
	no_mem_stall_in_hwloop_c : assume property (id_stage_i.controller_i.ctrl_fsm_cs==cv32e40p_pkg::DECODE_HWLOOP && load_store_unit_i.cnt_q>0|->`core.data_rvalid_i);
`else
	no_hwloop_c              : assume property (!id_stage_i.controller_i.is_hwlp_body);
`endif
`endif

`ifdef CFG_XC
	clk_en_c: assume property (`core.pulp_clock_en_i);
`endif

// MEMORY INTERFACE CONSTRAINTS //

//
// The following set of constraints could be used to constrain memory interfaces in case bus protocols implemented are not tool supported.
// **W** Use only in case bus protocols implemented are not tool supported
//

`ifdef CUSTOM_MEM_INTERFACES
	`include "mem_constraints.sv"
	localparam MAX_WAIT=DMEM_MAX_WAIT;
`else
	localparam MAX_WAIT=obi_dmem_checker.MAX_WAIT;
`endif

// PERFORMANCE ENHANCEMENT CONSTRAINTS //

//
// The following set of constraints could be used to enhance properties' runtime.
// **W** If ever used, these constraints have to be removed totally afterwards to achieve full verification.
//

//
// "restrict_regs" restricts instruction source and destination indices to a subset of registers.
// By default, the following register indices are chosen: 0 to 3, and 8 to 9 in presence of compressed extensions.
//
function automatic restrict_regs(input dec_t dec);
	restrict_regs=1'b1;
	foreach (dec.RS[i])
		if (dec.RS[i].valid)
//			restrict_regs&=dec.RS[i].idx<4 || (MISA.C|Zca) && dec.RS[i].idx inside {5'd8,5'd9};
			restrict_regs&=dec.RS[i].idx inside {5'd0, 5'd1, 5'd2, 5'd4, 5'd8, 5'd12, 5'd16};
	foreach (dec.RD[i])
		if (dec.RD[i].valid)
//			restrict_regs&=dec.RD[i].idx<4 || (MISA.C|Zca) && dec.RD[i].idx inside {5'd8,5'd9};
			restrict_regs&=dec.RD[i].idx inside {5'd0, 5'd1, 5'd2, 5'd4, 5'd8, 5'd12, 5'd16};
endfunction

`ifdef RESTRICT_REGS
	// Restrict instruction decoding & register file verification to a subset of registers
	restrict_regs_c: assume property (disable iff (~rst_n)
	restrict_regs(my_dec)
	`ifndef COMPLETENESS
		`ifndef RESTRICT_REGISTER_INDEX
//			&& (reg_idx<4 || (MISA.C|Zca) && reg_idx inside {5'd8,5'd9})
			&& (reg_idx inside {5'd0, 5'd1, 5'd2, 5'd4, 5'd8, 5'd12, 5'd16})
		`endif
	`endif
	);
`endif

// GRADUAL VERIFICATION CONSTRAINTS //

//
// The following set of constraints could be used for a gradual setup of a new core.
// **W** If ever used, these constraints have to be removed totally afterwards to achieve full verification.
//

`ifdef LIMIT_TOTAL_INSTR_COUNT
	// Limit total number of instructions allowed in the pipeline
	limit_total_instr_count_c : assume property (disable iff (~rst_n) full[0] -> id_instr_cnt<`LIMIT_TOTAL_INSTR_COUNT);
`endif
