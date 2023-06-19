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

// &ModuleBeg; @23
module pa_fdsu_prepare(
  dp_xx_ex1_rm,
  ex1_div,
  ex1_divisor,
  ex1_expnt_adder_op0,
  ex1_expnt_adder_op1,
  ex1_of_result_lfn,
  ex1_op0_id,
  ex1_op0_sign,
  ex1_op1_id,
  ex1_op1_id_vld,
  ex1_op1_sel,
  ex1_oper_id_expnt,
  ex1_oper_id_expnt_f,
  ex1_oper_id_frac,
  ex1_oper_id_frac_f,
  ex1_remainder,
  ex1_result_sign,
  ex1_rm,
  ex1_sqrt,
  fdsu_ex1_sel,
  idu_fpu_ex1_func,
  idu_fpu_ex1_srcf0,
  idu_fpu_ex1_srcf1
);

// &Ports; @24
input   [2 :0]  dp_xx_ex1_rm;            
input           ex1_op0_id;              
input           ex1_op1_id;              
input           ex1_op1_sel;             
input   [12:0]  ex1_oper_id_expnt_f;     
input   [51:0]  ex1_oper_id_frac_f;      
input           fdsu_ex1_sel;            
input   [9 :0]  idu_fpu_ex1_func;        
input   [31:0]  idu_fpu_ex1_srcf0;       
input   [31:0]  idu_fpu_ex1_srcf1;       
output          ex1_div;                 
output  [23:0]  ex1_divisor;             
output  [12:0]  ex1_expnt_adder_op0;     
output  [12:0]  ex1_expnt_adder_op1;     
output          ex1_of_result_lfn;       
output          ex1_op0_sign;            
output          ex1_op1_id_vld;          
output  [12:0]  ex1_oper_id_expnt;       
output  [51:0]  ex1_oper_id_frac;        
output  [31:0]  ex1_remainder;           
output          ex1_result_sign;         
output  [2 :0]  ex1_rm;                  
output          ex1_sqrt;                

// &Regs; @25
reg     [12:0]  ex1_expnt_adder_op1;     
reg             ex1_of_result_lfn;       

// &Wires; @26
wire            div_sign;                
wire    [2 :0]  dp_xx_ex1_rm;            
wire            ex1_div;                 
wire    [52:0]  ex1_div_noid_nor_srt_op0; 
wire    [52:0]  ex1_div_noid_nor_srt_op1; 
wire    [52:0]  ex1_div_nor_srt_op0;     
wire    [52:0]  ex1_div_nor_srt_op1;     
wire    [12:0]  ex1_div_op0_expnt;       
wire    [12:0]  ex1_div_op1_expnt;       
wire    [52:0]  ex1_div_srt_op0;         
wire    [52:0]  ex1_div_srt_op1;         
wire    [23:0]  ex1_divisor;             
wire            ex1_double;              
wire    [12:0]  ex1_expnt_adder_op0;     
wire            ex1_op0_id;              
wire            ex1_op0_id_nor;          
wire            ex1_op0_sign;            
wire            ex1_op1_id;              
wire            ex1_op1_id_nor;          
wire            ex1_op1_id_vld;          
wire            ex1_op1_sel;             
wire            ex1_op1_sign;            
wire    [63:0]  ex1_oper0;               
wire    [51:0]  ex1_oper0_frac;          
wire    [12:0]  ex1_oper0_id_expnt;      
wire    [51:0]  ex1_oper0_id_frac;       
wire    [63:0]  ex1_oper1;               
wire    [51:0]  ex1_oper1_frac;          
wire    [12:0]  ex1_oper1_id_expnt;      
wire    [51:0]  ex1_oper1_id_frac;       
wire    [51:0]  ex1_oper_frac;           
wire    [12:0]  ex1_oper_id_expnt;       
wire    [12:0]  ex1_oper_id_expnt_f;     
wire    [51:0]  ex1_oper_id_frac;        
wire    [51:0]  ex1_oper_id_frac_f;      
wire    [31:0]  ex1_remainder;           
wire            ex1_result_sign;         
wire    [2 :0]  ex1_rm;                  
wire            ex1_single;              
wire            ex1_sqrt;                
wire            ex1_sqrt_expnt_odd;      
wire            ex1_sqrt_op0_expnt_0;    
wire    [12:0]  ex1_sqrt_op1_expnt;      
wire    [52:0]  ex1_sqrt_srt_op0;        
wire            fdsu_ex1_sel;            
wire    [9 :0]  idu_fpu_ex1_func;        
wire    [31:0]  idu_fpu_ex1_srcf0;       
wire    [31:0]  idu_fpu_ex1_srcf1;       
wire    [59:0]  sqrt_remainder;          
wire            sqrt_sign;               


assign ex1_sqrt                    = idu_fpu_ex1_func[0];
assign ex1_div                     = idu_fpu_ex1_func[1];
assign ex1_oper0[63:0]             = {32'b0, idu_fpu_ex1_srcf0[31:0] & {32{fdsu_ex1_sel}}};
assign ex1_oper1[63:0]             = {32'b0, idu_fpu_ex1_srcf1[31:0] & {32{fdsu_ex1_sel}}};
assign ex1_double                  = 1'b0;
assign ex1_single                  = 1'b1;
// &Force("bus", "idu_fpu_ex1_func", 9, 0); @43
assign ex1_op0_id_nor              = ex1_op0_id;
assign ex1_op1_id_nor              = ex1_op1_id;

//Sign bit prepare
assign ex1_op0_sign                = ex1_double && ex1_oper0[63]
                                  || ex1_single && ex1_oper0[31];
assign ex1_op1_sign                = ex1_double && ex1_oper1[63]
                                  || ex1_single && ex1_oper1[31];
assign div_sign                    = ex1_op0_sign ^ ex1_op1_sign;
assign sqrt_sign                   = ex1_op0_sign;
assign ex1_result_sign             = (ex1_div)
                                   ? div_sign
                                   : sqrt_sign;

//=====================find first one=======================
// this is for the denormal number
assign ex1_oper_frac[51:0] = ex1_op1_sel ? ex1_oper1_frac[51:0]
                                         : ex1_oper0_frac[51:0];

// &Instance("pa_fdsu_ff1", "x_frac_expnt"); @63
pa_fdsu_ff1  x_frac_expnt (
  .fanc_shift_num          (ex1_oper_id_frac[51:0] ),
  .frac_bin_val            (ex1_oper_id_expnt[12:0]),
  .frac_num                (ex1_oper_frac[51:0]    )
);

// &Connect(.frac_num(ex1_oper_frac[51:0])); @64
// &Connect(.frac_bin_val(ex1_oper_id_expnt[12:0])); @65
// &Connect(.fanc_shift_num(ex1_oper_id_frac[51:0])); @66
// &Force("output", "ex1_oper_id_expnt"); &Force("bus", "ex1_oper_id_expnt", 12, 0); @67
// &Force("output", "ex1_oper_id_frac"); &Force("bus", "ex1_oper_id_frac", 51, 0); @68

assign ex1_oper0_id_expnt[12:0] = ex1_op1_sel ? ex1_oper_id_expnt_f[12:0]
                                              : ex1_oper_id_expnt[12:0];
assign ex1_oper0_id_frac[51:0]  = ex1_op1_sel ? ex1_oper_id_frac_f[51:0]
                                              : ex1_oper_id_frac[51:0];
assign ex1_oper1_id_expnt[12:0] = ex1_oper_id_expnt[12:0];
assign ex1_oper1_id_frac[51:0]  = ex1_oper_id_frac[51:0];

assign ex1_oper0_frac[51:0] = {52{ex1_double}} & ex1_oper0[51:0]
                            | {52{ex1_single}} & {ex1_oper0[22:0],29'b0};
assign ex1_oper1_frac[51:0] = {52{ex1_double}} & ex1_oper1[51:0]
                            | {52{ex1_single}} & {ex1_oper1[22:0],29'b0};

//=====================exponent add=========================
//exponent number 0
assign ex1_div_op0_expnt[12:0]     = {13{ex1_double}} & {2'b0,ex1_oper0[62:52]}
                                   | {13{ex1_single}} & {5'b0,ex1_oper0[30:23]};
assign ex1_expnt_adder_op0[12:0]   = ex1_op0_id_nor ? ex1_oper0_id_expnt[12:0]
                                                : ex1_div_op0_expnt[12:0];
//exponent number 1
assign ex1_div_op1_expnt[12:0]  = {13{ex1_double}} & {2'b0,ex1_oper1[62:52]}
                                | {13{ex1_single}} & {5'b0,ex1_oper1[30:23]};
assign ex1_sqrt_op1_expnt[12:0] = {13{ex1_double}} & {3'b0,{10{1'b1}}} //'d1023
                                | {13{ex1_single}} & {6'b0,{7{1'b1}}}; //'d127
// &CombBeg; @93
always @( ex1_oper1_id_expnt[12:0]
       or ex1_div
       or ex1_op1_id_nor
       or ex1_sqrt_op1_expnt[12:0]
       or ex1_sqrt
       or ex1_div_op1_expnt[12:0])
begin
case({ex1_div,ex1_sqrt})
  2'b10:   ex1_expnt_adder_op1[12:0] = ex1_op1_id_nor ? ex1_oper1_id_expnt[12:0]
                                                  : ex1_div_op1_expnt[12:0];
  2'b01:   ex1_expnt_adder_op1[12:0] = ex1_sqrt_op1_expnt[12:0];
  default: ex1_expnt_adder_op1[12:0] = 13'b0;
endcase
// &CombEnd; @100
end

//ex1_sqrt_expnt_odd
//fraction will shift left by 1
// adder_op0/1 timing is bad.
// assign ex1_sqrt_expnt_odd          = ex1_expnt_adder_op0[0] ^ ex1_expnt_adder_op1[0];

// sqrt_odd is only used when is sqrt.
assign ex1_sqrt_op0_expnt_0        = ex1_op0_id_nor ? ex1_oper_id_expnt[0]
                                                    : ex1_div_op0_expnt[0];
// ex1_expnt_adder_op1 is always 1'b1, so adder_op0[0] should be 0.
assign ex1_sqrt_expnt_odd          = !ex1_sqrt_op0_expnt_0;

assign ex1_rm[2:0]       = dp_xx_ex1_rm[2:0];
//RNE : Always inc 1 because round to nearest of 1.111...11
//RTZ : Always not inc 1
//RUP : Always not inc 1 when posetive
//RDN : Always not inc 1 when negative
//RMM : Always inc 1 because round to max magnitude
// &CombBeg; @119
always @( ex1_rm[2:0]
       or ex1_result_sign)
begin
case(ex1_rm[2:0])
  3'b000  : ex1_of_result_lfn = 1'b0;
  3'b001  : ex1_of_result_lfn = 1'b1;
  3'b010  : ex1_of_result_lfn = !ex1_result_sign;
  3'b011  : ex1_of_result_lfn = ex1_result_sign;
  3'b100  : ex1_of_result_lfn = 1'b0;
  default: ex1_of_result_lfn = 1'b0;
endcase
// &CombEnd; @128
end

//EX1 Remainder
//div  : 1/8  <= x < 1/4
//sqrt : 1/16 <= x < 1/4
assign ex1_remainder[31:0] = {32{ex1_div }} & {5'b0,ex1_div_srt_op0[52:28],2'b0} |
                             {32{ex1_sqrt}} & sqrt_remainder[59:28];

//EX1 Divisor
//1/2 <= y < 1
assign ex1_divisor[23:0]   = ex1_div_srt_op1[52:29];

//ex1_div_srt_op0
assign ex1_div_srt_op0[52:0]     = ex1_div_nor_srt_op0[52:0];
//ex1_div_srt_op1
assign ex1_div_srt_op1[52:0]     =  ex1_div_nor_srt_op1[52:0];
//ex1_div_nor_srt_op0
assign ex1_div_noid_nor_srt_op0[52:0] = {53{ex1_double}} & {1'b1,ex1_oper0[51:0]}
                                      | {53{ex1_single}} & {1'b1,ex1_oper0[22:0],29'b0};
assign ex1_div_nor_srt_op0[52:0] = ex1_op0_id_nor ? {ex1_oper0_id_frac[51:0],1'b0}
                                                  : ex1_div_noid_nor_srt_op0[52:0];
//ex1_div_nor_srt_op1
assign ex1_div_noid_nor_srt_op1[52:0] = {53{ex1_double}} & {1'b1,ex1_oper1[51:0]}
                                      | {53{ex1_single}} & {1'b1,ex1_oper1[22:0],29'b0};
assign ex1_div_nor_srt_op1[52:0] = ex1_op1_id_nor ? {ex1_oper1_id_frac[51:0],1'b0}
                                                  : ex1_div_noid_nor_srt_op1[52:0];
//sqrt_remainder
assign sqrt_remainder[59:0]      = (ex1_sqrt_expnt_odd)
                                 ? {5'b0,ex1_sqrt_srt_op0[52:0],2'b0}
                                 : {6'b0,ex1_sqrt_srt_op0[52:0],1'b0};
//ex1_sqrt_srt_op0
assign ex1_sqrt_srt_op0[52:0]    = ex1_div_srt_op0[52:0];

//========================Pipe to EX2=======================
//exponent register cal result
// &Force("output", "ex1_expnt_adder_op0"); &Force("bus", "ex1_expnt_adder_op0", 12, 0); @173
// &Force("output", "ex1_expnt_adder_op1"); &Force("bus", "ex1_expnt_adder_op1", 12, 0); @174
// &Force("output", "ex1_double"); @175
// &Force("output", "ex1_expnt_adder_op0"); &Force("bus", "ex1_expnt_adder_op0", 12, 0); @177
// &Force("output", "ex1_expnt_adder_op1"); &Force("bus", "ex1_expnt_adder_op1", 12, 0); @178
// &Force("output", "ex1_result_sign"); @180
// &Force("output", "ex1_div"); @181
// &Force("output", "ex1_sqrt"); @182
// &Force("output", "ex1_rm"); &Force("bus", "ex1_rm", 2, 0); @183
// &Force("output", "ex1_op0_sign"); @184

assign ex1_op1_id_vld = ex1_op1_id_nor && ex1_div;

// &ModuleEnd; @188
endmodule



