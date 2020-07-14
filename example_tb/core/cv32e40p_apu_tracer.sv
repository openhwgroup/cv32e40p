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
// Design Name:    cv32e40p_apu_tracer.sv (APU trace)                         //
// Project Name:   CV32E40P                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Logs the following:                                        //
//                                                                            //
//                 - APU register file write address                          //
//                 - APU register file write data                             //
//                                                                            //
// Note:           This code was here from cv32e40p_core.sv in order to       //
//                 remove the use of global defines in the RTL code.          //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40p_apu_tracer
(
);

   int         apu_trace;
   string      fn;
   string      apu_waddr_trace;

   // open/close output file for writing
   initial
     begin
        wait(cv32e40p_core.rst_ni == 1'b1);
        $sformat(fn, "apu_trace_core_%h.log", cv32e40p_core.hart_id_i);
        $display("[APU_TRACER] Output filename is: %s", fn);
        apu_trace = $fopen(fn, "w");
        $fwrite(apu_trace, "time       register \tresult\n");

        while(1) begin

           @(negedge cv32e40p_core.clk_i);
           if (cv32e40p_core.ex_stage_i.apu_valid == 1'b1) begin
              if (cv32e40p_core.ex_stage_i.apu_waddr>31)
                $sformat(apu_waddr_trace, "f%d", cv32e40p_core.ex_stage_i.apu_waddr[4:0]);
              else
                $sformat(apu_waddr_trace, "x%d", cv32e40p_core.ex_stage_i.apu_waddr[4:0]);
              $fwrite(apu_trace, "%t %s \t\t%h\n", $time, apu_waddr_trace, cv32e40p_core.ex_stage_i.apu_result);
           end
        end

   end

   final
     begin
        $fclose(apu_trace);
     end

endmodule // cv32e40p_apu_tracer
