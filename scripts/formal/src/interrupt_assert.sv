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
// Description:  Debug interface constraints                                      //
//                                                                                //
////////////////////////////////////////////////////////////////////////////////////

module interrput_assert (
    input logic clk_i,
    input logic rst_ni,
    // Interrupt inputs
    input  logic [31:0] irq_i,
    input  logic        irq_ack_o,
    input  logic [ 4:0] irq_id_o
);

	/**********
	 * Assume *
	 **********/
	property no_interrupt;
        @(posedge clk_i) disable iff(!rst_ni)
		    irq_i == '0;
    endproperty

    // Uncomment to disable interrupt interface
    // assume_no_interrupt: assume property(no_interrupt);


endmodule