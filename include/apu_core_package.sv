// Copyright 2015 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    APU-core package                                           //
// Project Name:   RISC-V                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    core package of RISC-V core for shared APU                 //
//                 Important: his package depends on SHARED_FP,               //
//                 SHARED_DSP_MULT, SHARED_INT_MULT, SHARED_INT_DIV           //
//                 the parameters SHARED_FP_DIV, SHARED_FP_SQRT,              //
//                 SHARED_FP_DIVSQRT have to match the ones in apu_cluster.sv //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

package apu_core_package;

   // define these parameters. should match apu_cluster
   parameter SHARED_FP           = 0;
   parameter SHARED_DSP_MULT     = 0;
   parameter SHARED_INT_DIV      = 0;

   // select pipelined divider/square-root blocks
   parameter SHARED_FP_DIV     = 0;
   parameter SHARED_FP_SQRT    = 0;
   // selects one iterative shared divider/square-root block
   parameter SHARED_FP_DIVSQRT = 1;

   // by default set to 0
   parameter SHARED_INT_MULT   = 0;

   parameter APU               = SHARED_DSP_MULT + SHARED_INT_DIV + SHARED_FP;

   
   // CPU side / general params
   parameter NARGS_CPU     = 3;
   parameter WOP_CPU       = 6;
   parameter NUSFLAGS_CPU  = 0;
   parameter NDSFLAGS_CPU  = 15;

   // DSP-general
   parameter DSP_WIDTH    = 32;
   parameter DSP_OP_WIDTH = 3;

   // FP-general
   parameter APUTYPE_FP   = (SHARED_FP) ? SHARED_DSP_MULT + SHARED_INT_MULT + SHARED_INT_DIV : 0;
   parameter APU_FLAGS_FP = 2;
      
   // DSP-Mult
   parameter APUTYPE_DSP_MULT   = (SHARED_DSP_MULT) ? 0 : 0;
   parameter PIPE_REG_DSP_MULT  = 1;
   parameter APU_FLAGS_DSP_MULT = 0;
   
   // Int-Mult
   parameter APUTYPE_INT_MULT   = (SHARED_INT_MULT) ? SHARED_DSP_MULT : 0;
   parameter APU_FLAGS_INT_MULT = 1;
   
   // Int-div
   parameter APUTYPE_INT_DIV    = (SHARED_INT_DIV) ? SHARED_DSP_MULT + SHARED_INT_MULT : 0;
      
   // addsub
   parameter APUTYPE_ADDSUB   = (SHARED_FP) ? APUTYPE_FP   : 0;
   parameter PIPE_REG_ADDSUB  = 1;
         
   // mult
   parameter APUTYPE_MULT  = (SHARED_FP) ? APUTYPE_FP+1  : 0;
   parameter PIPE_REG_MULT = 1;
   
   // casts
   parameter APUTYPE_CAST  = (SHARED_FP) ? APUTYPE_FP+2  : 0;
   parameter PIPE_REG_CAST = 1;
   
   // mac
   parameter APUTYPE_MAC  = (SHARED_FP) ? APUTYPE_FP+3  : 0;
   parameter PIPE_REG_MAC = 2;
   
   // div
   parameter APUTYPE_DIV  = (SHARED_FP_DIV) ? APUTYPE_FP+4 : 0;
   parameter PIPE_REG_DIV = 4;
   
   // sqrt
   parameter APUTYPE_SQRT  = (SHARED_FP_SQRT) ? APUTYPE_FP+5 : 0;
   parameter PIPE_REG_SQRT = 5;

   // iter divsqrt
   parameter APUTYPE_DIVSQRT  = (SHARED_FP_DIVSQRT) ? APUTYPE_FP+4 : 0;

   // generated values
   parameter C_APUTYPES   = (SHARED_FP_SQRT) ? (SHARED_FP_DIV) ? APUTYPE_FP+6 : APUTYPE_FP+5 : (SHARED_FP_DIVSQRT) ? APUTYPE_FP+5 : APUTYPE_FP+4;

   parameter NAPUTYPES    = C_APUTYPES;
   parameter WAPUTYPE     = $clog2(C_APUTYPES);
   
endpackage // apu_core_package
