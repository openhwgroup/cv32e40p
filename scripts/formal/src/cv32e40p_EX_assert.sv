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
// Description:  Assertion for unreachable code in CV32E40P EX stage              //
//                                                                                //
////////////////////////////////////////////////////////////////////////////////////

module cv32e40p_EX_assert import cv32e40p_pkg::*;
(
    input logic clk_i,
    input logic rst_ni,

    input logic        apu_valid       ,
    input logic        apu_singlecycle ,
    input logic        apu_multicycle  ,
    input logic        regfile_alu_we_i,
    input logic        apu_en_i        ,
    input logic        regfile_we_lsu  ,
    input logic        apu_rvalid_i    ,
    input logic        apu_rvalid_q    ,

    input logic        data_misaligned_i          ,
    input logic        data_misaligned_ex_i       ,
    input logic        data_req_i                 ,
    input logic        data_rvalid_i              ,
    input logic        mulh_active                ,
    input mul_opcode_e mult_operator_i            ,
    input logic [ 1:0] ctrl_transfer_insn_in_dec_i,
    input logic        apu_read_dep_for_jalr_o
);

    property unreachable_ex_211;
        @(posedge clk_i) disable iff(!rst_ni)
            (apu_valid & (apu_singlecycle | apu_multicycle)) |-> !(apu_en_i & regfile_alu_we_i);
    endproperty

    property unreachable_ex_237;
        @(posedge clk_i) disable iff(!rst_ni)
            regfile_we_lsu |-> !(~apu_valid & (!apu_singlecycle & !apu_multicycle));
    endproperty

    property unreachable_ex_387;
        @(posedge clk_i) disable iff(!rst_ni)
            ((apu_rvalid_i && apu_multicycle) && ~(((ctrl_transfer_insn_in_dec_i == 2) && regfile_alu_we_i) && ~apu_read_dep_for_jalr_o) && ~((data_misaligned_i || data_misaligned_ex_i) || ((data_req_i || data_rvalid_i) && regfile_alu_we_i)) && mulh_active)|-> mult_operator_i == MUL_H;
    endproperty

    property unreachable_ex_396;
        @(posedge clk_i) disable iff(!rst_ni)
            (apu_rvalid_q && ~(( ~apu_read_dep_for_jalr_o && (ctrl_transfer_insn_in_dec_i==2)) && regfile_alu_we_i) && ~((data_misaligned_i || data_misaligned_ex_i) || ((data_req_i || data_rvalid_i) && regfile_alu_we_i)) && mulh_active) |-> mult_operator_i == MUL_H;
    endproperty

    assert_unreachable_ex_211: assert property(unreachable_ex_211);
    assert_unreachable_ex_237: assert property(unreachable_ex_237);
    assert_unreachable_ex_387: assert property(unreachable_ex_387);
    assert_unreachable_ex_396: assert property(unreachable_ex_396);

endmodule