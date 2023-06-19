/*Copyright 2020-2021 T-Head Semiconductor Co., Ltd.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

// &ModuleBeg; @24
module pa_fpu_src_type(
  inst_double,
  inst_single,
  src_cnan,
  src_id,
  src_in,
  src_inf,
  src_norm,
  src_qnan,
  src_snan,
  src_zero
);

// &Ports; @25
input           inst_double;  
input           inst_single;  
input   [63:0]  src_in;       
output          src_cnan;     
output          src_id;       
output          src_inf;      
output          src_norm;     
output          src_qnan;     
output          src_snan;     
output          src_zero;     

// &Regs; @26

// &Wires; @27
wire            inst_double;  
wire            inst_single;  
wire    [63:0]  src;          
wire            src_cnan;     
wire            src_expn_max; 
wire            src_expn_zero; 
wire            src_frac_msb; 
wire            src_frac_zero; 
wire            src_id;       
wire    [63:0]  src_in;       
wire            src_inf;      
wire            src_norm;     
wire            src_qnan;     
wire            src_snan;     
wire            src_zero;     


// &Depend("cpu_cfig.h"); @29
assign src[63:0] = src_in[63:0];

assign src_cnan  = !(&src[63:32]) && inst_single;

assign src_expn_zero = !(|src[62:52]) && inst_double ||
                       !(|src[30:23]) && inst_single;

assign src_expn_max  =  (&src[62:52]) && inst_double ||
                        (&src[30:23]) && inst_single;

assign src_frac_zero = !(|src[51:0]) && inst_double ||
                       !(|src[22:0]) && inst_single;

assign src_frac_msb  = src[51] && inst_double || src[22] && inst_single;

assign src_snan = src_expn_max  && !src_frac_msb && !src_frac_zero && !src_cnan;
assign src_qnan = src_expn_max  &&  src_frac_msb || src_cnan;
assign src_zero = src_expn_zero &&  src_frac_zero && !src_cnan;
assign src_id   = src_expn_zero && !src_frac_zero && !src_cnan;
assign src_inf  = src_expn_max  &&  src_frac_zero && !src_cnan;
assign src_norm =!(src_expn_zero && src_frac_zero) &&
                 ! src_expn_max  && !src_cnan;

// &Force("output","src_cnan"); @53

// &ModuleEnd; @55
endmodule



