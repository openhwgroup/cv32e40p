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
// Description:  Assertion for unreachable code in CV32E40P div sqrt unit         //
//                                                                                //
////////////////////////////////////////////////////////////////////////////////////

module fpnew_divsqrt_th_32_assert (
    input logic clk_i,
    input logic rst_ni,

    input logic op_starting      ,
    input logic unit_ready_q     ,
    input logic ex2_inst_wb      ,
    input logic ex2_inst_wb_vld_q
);

    property unreachable_divsqrt_th_288;
        @(posedge clk_i) disable iff(!rst_ni)
            (op_starting && unit_ready_q) |-> !(ex2_inst_wb && ex2_inst_wb_vld_q);
    endproperty

    assert_unreachable_divsqrt_th_288: assert property(unreachable_divsqrt_th_288);

endmodule