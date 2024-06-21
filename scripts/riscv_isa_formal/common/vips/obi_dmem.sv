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

///////////////////////////////////////////////////////////////////////////////////////////////////////////////
//                                                                                                           //
// General remarks:                                                                                          //
//                                                                                                           //
// Just replace <target_module> below with the name of the module you want to connect the VIP to             //
// and add the appropriate parameter values and DUT signals in braces.                                       //
//                                                                                                           //
// Leave unused signals (and parameters that just have the default value) simply unconnected                 //
// because optional signals are pulled up/down appropriately in the checker file.                            //
//                                                                                                           //
// The VIP uses an active LOW reset.                                                                         //
// If your DUT reset signal, called "rst", is active high, use "!rst" in the instantiation                   //
//                                                                                                           //
// For external interfaces (bus signals are primary inputs/outputs), set parameter ASSUME=1.                 //
// In that case, make sure MASTER=1 in case the DUT is the bus master (driving the address signal output),   //
// or MASTER=0 in case the DUT is the bus slave (address signal is input).                                   //
//                                                                                                           //
// In case you instantiate the VIP several times for different interfaces in the DUT,                        //
// make sure to pick individual instance names (line with comment "non-ambiguous instance name" below)       //
//                                                                                                           //
///////////////////////////////////////////////////////////////////////////////////////////////////////////////

bind cv32e40p_core obi_checker #(
    .ADDR_WIDTH   (), // (default 32) number of bits in addr
    .DATA_WIDTH   (), // (default 32) number of bits in wdata, rdata
    .ASSUME       (1), // (default  0) switch to create assumes
    .MASTER       (1), // (default  0) switch to select master/slave side (when switched off, i.e., slave side, important in case of ASSUME)
    .ASSERT_ON    (), // (default  1) switch to generate assertions,
                      //              useful to switch off (ASSERT_ON=0) together with ASSUME=1 just to constrain a block for Inspect
    .COVER_ON     (), // (default  1) switch to additionally generate cover statements
    .X_CHECKING_ON(), // (default  0) switch to create no-X assertions (to be used in conjunction with x_checking_setup)
    .LIVENESS_ON  (), // (default  0) switch to create liveness assertions
    .MAX_WAIT     (`RESTRICT_DMEM_STALL_CYCLES), // (default  $) number of cycles for waiting period checks (for creating liveness checks in case LIVENESS_ON=1)
    .AUSER_WIDTH  (), // (default 32) number of bits in auser (if used)
    .WUSER_WIDTH  (), // (default 32) number of bits in wuser (if used)
    .RUSER_WIDTH  (), // (default 32) number of bits in ruser (if used)
    .ID_WIDTH     (), // (default 32) number of bits in aid, rid (if used)
    .MAX_OUTSTANDING_TRANSACTIONS(), // (default 2) maximum number of outstanding transactions in the system
    .RESPONSE_PREDICTOR(1) // (default 0) switch to introduce a signal to predict the response at the beginning of the data phase
) obi_dmem_checker ( // non-ambiguous instance name
    .clk    (clk_i),  // required
    .reset_n(rst_ni),  // required
// Address channel
    .req    (data_req_o),  // required
    .gnt    (data_gnt_i),  // required
    .addr   (data_addr_o),  // required /*ADDRESS*/
    .we     (data_we_o),  // optional, default is 1'b0
    .be     (data_be_o),  // optional, default is '1
    .wdata  (data_wdata_o),  // required /*DATA*/
    .auser  (),  // optional, default is '0
    .wuser  (),  // optional, default is '0
    .aid    (),  // optional, default is '0
// Response channel
    .rvalid (data_rvalid_i),  // required
    .rready (),  // optional, default is 1'b1
    .rdata  (data_rdata_i),  // required /*DATA*/
    .err    (),  // optional, default is 1'b0
    .ruser  (),  // optional, default is '0
    .rid    ()   // optional, default is '0
);
