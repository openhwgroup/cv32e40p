// Copyright 2020 Silicon Labs, Inc.
//
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License").
//
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
//
// You may obtain a copy of the License at:
//
//     https://solderpad.org/licenses/SHL-2.0/
//
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof distributed under the License
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS
// OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
//
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Arjan Bink - arjan.bink@silabs.com                         //
//                                                                            //
// Design Name:    cv32e40p_core_log.sv (cv32e40p_core simulation log)        //
// Project Name:   CV32E40P                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Logs the following:                                        //
//                                                                            //
//                 - top level parameter settings                             //
//                 - illegal instructions                                     //
//                                                                            //
// Note:           This code was here from cv32e40p_core.sv and               //
//                 cv32e40p_controller.sv in order to remove the use of       //
//                 global defines in the RTL code.                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40p_core_log #(
    parameter COREV_PULP =  1,  // PULP ISA Extension (incl. custom CSRs and hardware loop, excl. cv.elw)
    parameter COREV_CLUSTER = 0,  // PULP Cluster interface (incl. cv.elw)
    parameter FPU = 0,  // Floating Point Unit (interfaced via APU interface)
    parameter ZFINX = 0,  // Float-in-General Purpose registers
    parameter NUM_MHPMCOUNTERS = 1
) (
    input logic        clk_i,
    input logic        is_decoding_i,
    input logic        illegal_insn_dec_i,
    input logic [31:0] hart_id_i,
    input logic [31:0] pc_id_i
);

  // Log top level parameter values
  initial begin
    $display(
        "[cv32e40p_core]: COREV_PULP = %d, COREV_CLUSTER = %d, FPU %d, ZFINX %d, NUM_MHPMCOUNTERS %d",
        COREV_PULP, COREV_CLUSTER, FPU, ZFINX, NUM_MHPMCOUNTERS);
  end

  // Log illegal instructions
  always_ff @(negedge clk_i) begin
    // print warning in case of decoding errors
    if (is_decoding_i && illegal_insn_dec_i) begin
      $display("%t: Illegal instruction (core %0d) at PC 0x%h:", $time, hart_id_i[3:0], pc_id_i);
    end
  end

endmodule  // cv32e40p_core_log
