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
//                                                                                //
// Description:  Assertion for unreachable code in CV32E40P ID stage              //
//                                                                                //
////////////////////////////////////////////////////////////////////////////////////

module cv32e40p_ID_assert import cv32e40p_pkg::*;
(
    input logic clk_i,
    input logic rst_ni,

    input  logic [31:0] instr_rdata_i,
    input  logic        is_compressed_id_i,

    input  logic [ 2:0] alu_op_a_mux_sel,
    input  logic [ 2:0] alu_op_b_mux_sel,
    input  logic [ 1:0] alu_op_c_mux_sel,
    input  logic        alu_bmask_b_mux_sel,
    input  logic [ 1:0] ctrl_transfer_target_mux_sel
);

    property unreachable_id_872;
        @(posedge clk_i) disable iff(!rst_ni)
            (alu_op_c_mux_sel == OP_C_REGC_OR_FWD) && (~(alu_op_b_mux_sel == OP_B_BMASK) && ((alu_op_a_mux_sel != OP_A_REGC_OR_FWD) && (ctrl_transfer_target_mux_sel != JT_JALR)) && ~alu_bmask_b_mux_sel) |-> alu_op_b_mux_sel == OP_B_IMM;
    endproperty

    assert_unreachable_id_872: assert property(unreachable_id_872);
endmodule