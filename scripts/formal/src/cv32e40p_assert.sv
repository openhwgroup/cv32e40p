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
// Contributors: Yoann Pruvost, Dolphin Design <yoann.pruvost@dolphin.fr>         //
//               Pascal Gouedo, Dolphin Design <pascal.gouedo@dolphin.fr>         //
//                                                                                //
// Description:  GLobal assume and assert for CV32E40P formal code analysis       //
//                                                                                //
////////////////////////////////////////////////////////////////////////////////////


module cv32e40p_assert import cv32e40p_pkg::*;
(
    input logic clk_i,
    input logic rst_ni,
    input logic scan_cg_en_i,

    input logic [31:0] boot_addr_i,
    input logic [31:0] mtvec_addr_i,
    input logic [31:0] hart_id_i,
    input logic [31:0] dm_halt_addr_i,
    input logic [31:0] dm_exception_addr_i,

    input logic [1:0] data_type_ex_i,

    input logic [31:0] pc_id_i,

    // Taken from controller
    input ctrl_state_e ctrl_fsm_cs,
    input logic        is_hwlp_body,
    input logic        hwlp_end0_eq_pc,
    input logic        hwlp_counter0_gt_1,
    input logic        hwlp_end1_eq_pc,
    input logic        hwlp_counter1_gt_1,
    input logic        jump_done_q
);
    import cv32e40p_tracer_pkg::*;

	/**********
	 * Assume *
	 **********/
    property no_scan;
        @(posedge clk_i) disable iff(!rst_ni)
            scan_cg_en_i == '0;
    endproperty

    property hart_id_0;
        @(posedge clk_i) disable iff(!rst_ni)
            hart_id_i == '0;
    endproperty

    property aligned_boot_address;
        @(posedge clk_i) disable iff(!rst_ni)
            boot_addr_i == 32'h1000_0000;
    endproperty

    property aligned_mtvec_address;
        @(posedge clk_i) disable iff(!rst_ni)
            mtvec_addr_i == 32'h2000_0000;
    endproperty

    property aligned_halt_address;
        @(posedge clk_i) disable iff(!rst_ni)
            dm_halt_addr_i == 32'h3000_0000;
    endproperty

    property aligned_exception_address;
        @(posedge clk_i) disable iff(!rst_ni)
            dm_exception_addr_i == 32'h4000_0000;
    endproperty

	/**********
	 * Assert *
	 **********/
	property data_type_ex_never_11;
	    @(posedge clk_i) disable iff(!rst_ni)
	        data_type_ex_i != 2'b11;
    endproperty

    property never_jump_done_q_when_hwlp_body_and_hwlp_end0_eq_pc_and_hwlp_counter0_gt_1;
	    @(posedge clk_i) disable iff(!rst_ni)
	        (ctrl_fsm_cs == DECODE) & is_hwlp_body & hwlp_end0_eq_pc & hwlp_counter0_gt_1 |-> ~jump_done_q;
    endproperty

    property never_ret_from_int_ecall_ebreak_exceptions_on_HWLoop1_last_inst_with_HWLoop1_counter_not_gt1;
        @(posedge clk_i) disable iff(!rst_ni)
            (ctrl_fsm_cs == DECODE) & is_hwlp_body |-> ~(hwlp_end1_eq_pc & hwlp_counter1_gt_1);
    endproperty

    property pc_id_aligned;
        @(posedge clk_i) disable iff(!rst_ni)
            pc_id_i[2:0] != 2'b00;
    endproperty



    assume_no_scan: assume property(no_scan);
    // assume_hart_id_0: assume property(hart_id_0);
    // assume_aligned_boot_address: assume property(aligned_boot_address);
    // asuume_aligned_mtvec_address: assume property(aligned_mtvec_address);
    // assume_aligned_halt_address: assume property(aligned_halt_address);
    // assume_aligned_exception_address: assume property(aligned_exception_address);

    assert_data_type_ex_never_11:  assert property(data_type_ex_never_11);
    // assert_never_jump_done_q_when_hwlp_body_and_hwlp_end0_eq_pc_and_hwlp_counter0_gt_1: assert property(never_jump_done_q_when_hwlp_body_and_hwlp_end0_eq_pc_and_hwlp_counter0_gt_1);
    // assert_never_ret_from_int_ecall_ebreak_exceptions_on_HWLoop1_last_inst_with_HWLoop1_counter_not_gt1: assert property(never_ret_from_int_ecall_ebreak_exceptions_on_HWLoop1_last_inst_with_HWLoop1_counter_not_gt1);
    // assert_pc_id_aligned: assert property(pc_id_aligned);

endmodule