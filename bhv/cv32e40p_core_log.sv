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

module cv32e40p_core_log
(
);

  // Log top level parameter values
  initial
  begin
    $display("[cv32e40p_core]: PULP_XPULP = %d, PULP_CLUSTER = %d, FPU %d, PULP_ZFINX %d, NUM_MHPMCOUNTERS %d",
      cv32e40p_core.PULP_XPULP, cv32e40p_core.PULP_CLUSTER, cv32e40p_core.FPU, cv32e40p_core.PULP_ZFINX, cv32e40p_core.NUM_MHPMCOUNTERS);
  end

  // Log illegal instructions
  always_ff @(negedge cv32e40p_core.id_stage_i.clk)
  begin
    // print warning in case of decoding errors
    if (cv32e40p_core.id_stage_i.is_decoding_o && cv32e40p_core.id_stage_i.illegal_insn_dec) begin
      $display("%t: Illegal instruction (core %0d) at PC 0x%h:", $time, cv32e40p_core.hart_id_i[3:0], cv32e40p_core.pc_id);
    end
  end

endmodule // cv32e40p_core_log
