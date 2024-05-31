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

module debug_assert (
    input logic clk_i,
    input logic rst_ni,
    // Debug Interface
    input  logic debug_req_i,
    input  logic debug_havereset_o,
    input  logic debug_running_o,
    input  logic debug_halted_o
);

	/**********
	 * Assume *
	 **********/
	property no_debug;
        @(posedge clk_i) disable iff(!rst_ni)
		    debug_req_i == '0;
    endproperty

    // Uncomment this line to disable debug interface
    // assume_no_debug: assume property(no_debug);

endmodule