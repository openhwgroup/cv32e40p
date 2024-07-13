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
// Description:  CV32E40P binding for formal code analysis                        //
//                                                                                //
////////////////////////////////////////////////////////////////////////////////////

bind cv32e40p_top insn_assert u_insn_assert (
    .clk_i(clk_i),
    .rst_ni(rst_ni),

    .instr_req_o   (instr_req_o),
    .instr_gnt_i   (instr_gnt_i),
    .instr_rvalid_i(instr_rvalid_i)
);

bind cv32e40p_top data_assert u_data_assert (
    .clk_i(clk_i),
    .rst_ni(rst_ni),

    .data_req_o   (data_req_o   ),
    .data_gnt_i   (data_gnt_i   ),
    .data_rvalid_i(data_rvalid_i)
);
