// Copyright 2024 OpenHW Group and Dolphin Design
// Copyright 2020 Silicon Labs, Inc.
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

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Arjan Bink - arjan.bink@silabs.com                         //
// Description:    Logs the following:                                        //
//                 - APU register file write address                          //
//                 - APU register file write data                             //
// Note:           This code was here from cv32e40p_core.sv in order to       //
//                 remove the use of global defines in the RTL code.          //
////////////////////////////////////////////////////////////////////////////////

`ifdef CV32E40P_APU_TRACE

module cv32e40p_apu_tracer (
    input logic        clk_i,
    input logic        rst_n,
    input logic [31:0] hart_id_i,
    input logic        apu_valid_i,
    input logic [ 5:0] apu_waddr_i,
    input logic [31:0] apu_result_i
);

  int    apu_trace;
  string fn;
  string apu_waddr_trace;

  // open/close output file for writing
  initial begin
    wait(rst_n == 1'b1);
    $sformat(fn, "apu_trace_core_%h.log", hart_id_i);
    $display("[APU_TRACER %2d] Output filename is: %s", hart_id_i, fn);
    apu_trace = $fopen(fn, "w");
    $fwrite(apu_trace, "time       register \tresult\n");

    while (1) begin

      @(negedge clk_i);
      if (apu_valid_i == 1'b1) begin
        if (apu_waddr_i > 31) $sformat(apu_waddr_trace, "f%d", apu_waddr_i[4:0]);
        else $sformat(apu_waddr_trace, "x%d", apu_waddr_i[4:0]);
        $fwrite(apu_trace, "%t %s \t\t%h\n", $time, apu_waddr_trace, apu_result_i);
      end
    end

  end

  final begin
    $fclose(apu_trace);
  end

endmodule  // cv32e40p_apu_tracer

`endif  // CV32E40P_APU_TRACE
