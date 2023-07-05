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
module pa_fdsu_srt_single(
  cp0_fpu_icg_en,
  cp0_yy_clk_en,
  ex1_divisor,
  ex1_expnt_adder_op1,
  ex1_oper_id_frac,
  ex1_oper_id_frac_f,
  ex1_pipedown,
  ex1_pipedown_gate,
  ex1_remainder,
  ex1_save_op0,
  ex1_save_op0_gate,
  ex2_expnt_adder_op0,
  ex2_of,
  ex2_pipe_clk,
  ex2_pipedown,
  ex2_potnt_of,
  ex2_potnt_uf,
  ex2_result_inf,
  ex2_result_lfn,
  ex2_rslt_denorm,
  ex2_srt_expnt_rst,
  ex2_srt_first_round,
  ex2_uf,
  ex2_uf_srt_skip,
  ex3_frac_final_rst,
  ex3_pipedown,
  fdsu_ex3_id_srt_skip,
  fdsu_ex3_rem_sign,
  fdsu_ex3_rem_zero,
  fdsu_ex3_result_denorm_round_add_num,
  fdsu_ex4_frac,
  fdsu_yy_div,
  fdsu_yy_of_rm_lfn,
  fdsu_yy_op0_norm,
  fdsu_yy_op1_norm,
  fdsu_yy_sqrt,
  forever_cpuclk,
  pad_yy_icg_scan_en,
  srt_remainder_zero,
  srt_sm_on,
  total_qt_rt_30
);

// &Ports; @24
input           cp0_fpu_icg_en;                      
input           cp0_yy_clk_en;                       
input   [23:0]  ex1_divisor;                         
input   [12:0]  ex1_expnt_adder_op1;                 
input   [51:0]  ex1_oper_id_frac;                    
input           ex1_pipedown;                        
input           ex1_pipedown_gate;                   
input   [31:0]  ex1_remainder;                       
input           ex1_save_op0;                        
input           ex1_save_op0_gate;                   
input   [9 :0]  ex2_expnt_adder_op0;                 
input           ex2_pipe_clk;                        
input           ex2_pipedown;                        
input           ex2_srt_first_round;                 
input   [25:0]  ex3_frac_final_rst;                  
input           ex3_pipedown;                        
input           fdsu_yy_div;                         
input           fdsu_yy_of_rm_lfn;                   
input           fdsu_yy_op0_norm;                    
input           fdsu_yy_op1_norm;                    
input           fdsu_yy_sqrt;                        
input           forever_cpuclk;                      
input           pad_yy_icg_scan_en;                  
input           srt_sm_on;                           
output  [51:0]  ex1_oper_id_frac_f;                  
output          ex2_of;                              
output          ex2_potnt_of;                        
output          ex2_potnt_uf;                        
output          ex2_result_inf;                      
output          ex2_result_lfn;                      
output          ex2_rslt_denorm;                     
output  [9 :0]  ex2_srt_expnt_rst;                   
output          ex2_uf;                              
output          ex2_uf_srt_skip;                     
output          fdsu_ex3_id_srt_skip;                
output          fdsu_ex3_rem_sign;                   
output          fdsu_ex3_rem_zero;                   
output  [23:0]  fdsu_ex3_result_denorm_round_add_num; 
output  [25:0]  fdsu_ex4_frac;                       
output          srt_remainder_zero;                  
output  [29:0]  total_qt_rt_30;                      

// &Regs; @25
reg     [31:0]  cur_rem;                             
reg     [7 :0]  digit_bound_1;                       
reg     [7 :0]  digit_bound_2;                       
reg     [23:0]  ex2_result_denorm_round_add_num;     
reg             fdsu_ex3_id_srt_skip;                
reg             fdsu_ex3_rem_sign;                   
reg             fdsu_ex3_rem_zero;                   
reg     [23:0]  fdsu_ex3_result_denorm_round_add_num; 
reg     [29:0]  qt_rt_const_shift_std;               
reg     [7 :0]  qtrt_sel_rem;                        
reg     [31:0]  rem_add1_op1;                        
reg     [31:0]  rem_add2_op1;                        
reg     [25:0]  srt_divisor;                         
reg     [31:0]  srt_remainder;                       
reg     [29:0]  total_qt_rt_30;                      
reg     [29:0]  total_qt_rt_30_next;                 
reg     [29:0]  total_qt_rt_minus_30;                
reg     [29:0]  total_qt_rt_minus_30_next;           

// &Wires; @26
wire    [7 :0]  bound1_cmp_result;                   
wire            bound1_cmp_sign;                     
wire    [7 :0]  bound2_cmp_result;                   
wire            bound2_cmp_sign;                     
wire    [3 :0]  bound_sel;                           
wire            cp0_fpu_icg_en;                      
wire            cp0_yy_clk_en;                       
wire    [31:0]  cur_doub_rem_1;                      
wire    [31:0]  cur_doub_rem_2;                      
wire    [31:0]  cur_rem_1;                           
wire    [31:0]  cur_rem_2;                           
wire    [31:0]  div_qt_1_rem_add_op1;                
wire    [31:0]  div_qt_2_rem_add_op1;                
wire    [31:0]  div_qt_r1_rem_add_op1;               
wire    [31:0]  div_qt_r2_rem_add_op1;               
wire    [23:0]  ex1_divisor;                         
wire            ex1_ex2_pipe_clk;                    
wire            ex1_ex2_pipe_clk_en;                 
wire    [12:0]  ex1_expnt_adder_op1;                 
wire    [51:0]  ex1_oper_id_frac;                    
wire    [51:0]  ex1_oper_id_frac_f;                  
wire            ex1_pipedown;                        
wire            ex1_pipedown_gate;                   
wire    [31:0]  ex1_remainder;                       
wire            ex1_save_op0;                        
wire            ex1_save_op0_gate;                   
wire            ex2_div_of;                          
wire            ex2_div_uf;                          
wire    [9 :0]  ex2_expnt_adder_op0;                 
wire    [9 :0]  ex2_expnt_adder_op1;                 
wire            ex2_expnt_of;                        
wire    [9 :0]  ex2_expnt_result;                    
wire            ex2_expnt_uf;                        
wire            ex2_id_nor_srt_skip;                 
wire            ex2_of;                              
wire            ex2_of_plus;                         
wire            ex2_pipe_clk;                        
wire            ex2_pipedown;                        
wire            ex2_potnt_of;                        
wire            ex2_potnt_of_pre;                    
wire            ex2_potnt_uf;                        
wire            ex2_potnt_uf_pre;                    
wire            ex2_result_inf;                      
wire            ex2_result_lfn;                      
wire            ex2_rslt_denorm;                     
wire    [9 :0]  ex2_sqrt_expnt_result;               
wire    [9 :0]  ex2_srt_expnt_rst;                   
wire            ex2_srt_first_round;                 
wire            ex2_uf;                              
wire            ex2_uf_plus;                         
wire            ex2_uf_srt_skip;                     
wire    [25:0]  ex3_frac_final_rst;                  
wire            ex3_pipedown;                        
wire            fdsu_ex2_div;                        
wire    [9 :0]  fdsu_ex2_expnt_rst;                  
wire            fdsu_ex2_of_rm_lfn;                  
wire            fdsu_ex2_op0_norm;                   
wire            fdsu_ex2_op1_norm;                   
wire            fdsu_ex2_result_lfn;                 
wire            fdsu_ex2_sqrt;                       
wire    [25:0]  fdsu_ex4_frac;                       
wire            fdsu_yy_div;                         
wire            fdsu_yy_of_rm_lfn;                   
wire            fdsu_yy_op0_norm;                    
wire            fdsu_yy_op1_norm;                    
wire            fdsu_yy_sqrt;                        
wire            forever_cpuclk;                      
wire            pad_yy_icg_scan_en;                  
wire            qt_clk;                              
wire            qt_clk_en;                           
wire    [29:0]  qt_rt_const_pre_sel_q1;              
wire    [29:0]  qt_rt_const_pre_sel_q2;              
wire    [29:0]  qt_rt_const_q1;                      
wire    [29:0]  qt_rt_const_q2;                      
wire    [29:0]  qt_rt_const_q3;                      
wire    [29:0]  qt_rt_const_shift_std_next;          
wire    [29:0]  qt_rt_mins_const_pre_sel_q1;         
wire    [29:0]  qt_rt_mins_const_pre_sel_q2;         
wire            rem_sign;                            
wire    [31:0]  sqrt_qt_1_rem_add_op1;               
wire    [31:0]  sqrt_qt_2_rem_add_op1;               
wire    [31:0]  sqrt_qt_r1_rem_add_op1;              
wire    [31:0]  sqrt_qt_r2_rem_add_op1;              
wire            srt_div_clk;                         
wire            srt_div_clk_en;                      
wire    [31:0]  srt_remainder_nxt;                   
wire    [31:0]  srt_remainder_shift;                 
wire            srt_remainder_sign;                  
wire            srt_remainder_zero;                  
wire            srt_sm_on;                           
wire    [29:0]  total_qt_rt_pre_sel;                 


assign fdsu_ex2_div             = fdsu_yy_div;
assign fdsu_ex2_sqrt            = fdsu_yy_sqrt;
assign fdsu_ex2_op0_norm        = fdsu_yy_op0_norm;
assign fdsu_ex2_op1_norm        = fdsu_yy_op1_norm;
assign fdsu_ex2_of_rm_lfn       = fdsu_yy_of_rm_lfn;
assign fdsu_ex2_result_lfn      = 1'b0;

//==========================================================
//                    EX2 Expnt Generate
//==========================================================
//expnt0 sub expnt1
assign ex2_expnt_result[9:0] =  ex2_expnt_adder_op0[9:0] -
                                 ex2_expnt_adder_op1[9:0];

//===================sqrt exponent prepare==================
//sqrt exponent prepare
//afert E sub, div E by 2
assign ex2_sqrt_expnt_result[9:0] = {ex2_expnt_result[9],
                                      ex2_expnt_result[9:1]};

assign ex2_srt_expnt_rst[9:0] = (fdsu_ex2_sqrt)
                               ? ex2_sqrt_expnt_result[9:0]
                               : ex2_expnt_result[9:0];
// &Force("output", "ex2_srt_expnt_rst"); &Force("bus", "ex2_srt_expnt_rst", 9, 0); @51
assign fdsu_ex2_expnt_rst[9:0] = ex2_srt_expnt_rst[9:0];


//====================EX2 Expt info=========================
//EX1 only detect of/uf under id condition
//EX2 will deal with other condition

//When input is normal, overflow when E1-E2 > 128/1024
assign ex2_expnt_of = ~fdsu_ex2_expnt_rst[9] && (fdsu_ex2_expnt_rst[8]
                                                      || (fdsu_ex2_expnt_rst[7]  &&
                                                          |fdsu_ex2_expnt_rst[6:0]));
//potential overflow when E1-E2 = 128/1024
assign ex2_potnt_of_pre = ~fdsu_ex2_expnt_rst[9]  &&
                           ~fdsu_ex2_expnt_rst[8]  &&
                            fdsu_ex2_expnt_rst[7]  &&
                          ~|fdsu_ex2_expnt_rst[6:0];
assign ex2_potnt_of      = ex2_potnt_of_pre &&
                           fdsu_ex2_op0_norm &&
                           fdsu_ex2_op1_norm &&
                           fdsu_ex2_div;

//When input is normal, underflow when E1-E2 <= -127/-1023
assign ex2_expnt_uf = fdsu_ex2_expnt_rst[9] &&(fdsu_ex2_expnt_rst[8:0] <= 9'h181);
//potential underflow when E1-E2 = -126/-1022
assign ex2_potnt_uf_pre = &fdsu_ex2_expnt_rst[9:7]   &&
                          ~|fdsu_ex2_expnt_rst[6:2]   &&
                            fdsu_ex2_expnt_rst[1]     &&
                           !fdsu_ex2_expnt_rst[0];
assign ex2_potnt_uf      = (ex2_potnt_uf_pre &&
                            fdsu_ex2_op0_norm &&
                            fdsu_ex2_op1_norm &&
                            fdsu_ex2_div)     ||
                           (ex2_potnt_uf_pre   &&
                            fdsu_ex2_op0_norm);

//========================EX2 Overflow======================
//ex2 overflow when
//  1.op0 & op1 both norm && expnt overflow
//  2.ex1_id_of
// &Force("output","ex2_of"); @91
assign ex2_of      = ex2_of_plus;
assign ex2_of_plus = ex2_div_of  && fdsu_ex2_div;
assign ex2_div_of  = fdsu_ex2_op0_norm &&
                     fdsu_ex2_op1_norm &&
                     ex2_expnt_of;

//=======================EX2 Underflow======================
//ex2 underflow when
//  1.op0 & op1 both norm && expnt underflow
//  2.ex1_id_uf
//  and detect when to skip the srt, here, we have further optmization
assign ex2_uf      = ex2_uf_plus;
assign ex2_uf_plus = ex2_div_uf  && fdsu_ex2_div;
assign ex2_div_uf  = fdsu_ex2_op0_norm &&
                     fdsu_ex2_op1_norm &&
                     ex2_expnt_uf;
assign ex2_id_nor_srt_skip =  fdsu_ex2_expnt_rst[9]
                                     && (fdsu_ex2_expnt_rst[8:0]<9'h16a);
assign ex2_uf_srt_skip            = ex2_id_nor_srt_skip;
assign ex2_rslt_denorm            = ex2_uf;
//===============ex2 round prepare for denormal round======
// &CombBeg; @113
always @( fdsu_ex2_expnt_rst[9:0])
begin
case(fdsu_ex2_expnt_rst[9:0])
  10'h382:ex2_result_denorm_round_add_num[23:0] = 24'h1; //-126 1
  10'h381:ex2_result_denorm_round_add_num[23:0] = 24'h2; //-127 0
  10'h380:ex2_result_denorm_round_add_num[23:0] = 24'h4; //-128 -1
  10'h37f:ex2_result_denorm_round_add_num[23:0] = 24'h8; //-129 -2
  10'h37e:ex2_result_denorm_round_add_num[23:0] = 24'h10; //-130 -3
  10'h37d:ex2_result_denorm_round_add_num[23:0] = 24'h20; //-131 -4
  10'h37c:ex2_result_denorm_round_add_num[23:0] = 24'h40; //-132 -5
  10'h37b:ex2_result_denorm_round_add_num[23:0] = 24'h80; //-133 -6
  10'h37a:ex2_result_denorm_round_add_num[23:0] = 24'h100; //-134 -7
  10'h379:ex2_result_denorm_round_add_num[23:0] = 24'h200; //-135 -8
  10'h378:ex2_result_denorm_round_add_num[23:0] = 24'h400; //-136 -9
  10'h377:ex2_result_denorm_round_add_num[23:0] = 24'h800; //-137 -10
  10'h376:ex2_result_denorm_round_add_num[23:0] = 24'h1000; //-138 -11
  10'h375:ex2_result_denorm_round_add_num[23:0] = 24'h2000; //-139 -12
  10'h374:ex2_result_denorm_round_add_num[23:0] = 24'h4000; //-140 -13
  10'h373:ex2_result_denorm_round_add_num[23:0] = 24'h8000; // -141 -14
  10'h372:ex2_result_denorm_round_add_num[23:0] = 24'h10000;//-142  -15
  10'h371:ex2_result_denorm_round_add_num[23:0] = 24'h20000;//-143 -16
  10'h370:ex2_result_denorm_round_add_num[23:0] = 24'h40000; //-144 -17
  10'h36f:ex2_result_denorm_round_add_num[23:0] = 24'h80000; //-145 -18
  10'h36e:ex2_result_denorm_round_add_num[23:0] = 24'h100000; //-146 -19
  10'h36d:ex2_result_denorm_round_add_num[23:0] = 24'h200000; //-147 -20
  10'h36c:ex2_result_denorm_round_add_num[23:0] = 24'h400000; //-148 -21
  10'h36b:ex2_result_denorm_round_add_num[23:0] = 24'h800000; //-148 -22
  default: ex2_result_denorm_round_add_num[23:0] = 24'h0;  // -23
endcase
// &CombEnd; @141
end

//===================special result========================
assign ex2_result_inf  = ex2_of_plus && !fdsu_ex2_of_rm_lfn;
assign ex2_result_lfn  = fdsu_ex2_result_lfn ||
                         ex2_of_plus &&  fdsu_ex2_of_rm_lfn;



//====================Pipe to EX3===========================
always @(posedge ex1_ex2_pipe_clk)
begin
  if(ex1_pipedown)
  begin
    fdsu_ex3_result_denorm_round_add_num[23:0]
                              <= {14'b0, ex1_expnt_adder_op1[9:0]};
  end
  else if(ex2_pipedown)
  begin
    fdsu_ex3_result_denorm_round_add_num[23:0]
                              <= ex2_result_denorm_round_add_num[23:0];
  end
  else
  begin
    fdsu_ex3_result_denorm_round_add_num[23:0]
                              <= fdsu_ex3_result_denorm_round_add_num[23:0];
  end
end
assign ex2_expnt_adder_op1 = fdsu_ex3_result_denorm_round_add_num[9:0];
// &Force("bus", "ex1_expnt_adder_op1", 12, 0); @193

assign ex1_ex2_pipe_clk_en = ex1_pipedown_gate || ex2_pipedown;
// &Instance("gated_clk_cell", "x_ex1_ex2_pipe_clk"); @196
gated_clk_cell  x_ex1_ex2_pipe_clk (
  .clk_in              (forever_cpuclk     ),
  .clk_out             (ex1_ex2_pipe_clk   ),
  .external_en         (1'b0               ),
  .global_en           (cp0_yy_clk_en      ),
  .local_en            (ex1_ex2_pipe_clk_en),
  .module_en           (cp0_fpu_icg_en     ),
  .pad_yy_icg_scan_en  (pad_yy_icg_scan_en )
);

// &Connect(.clk_in      (forever_cpuclk), @197
//          .external_en (1'b0), @198
//          .global_en   (cp0_yy_clk_en), @199
//          .module_en   (cp0_fpu_icg_en), @200
//          .local_en    (ex1_ex2_pipe_clk_en), @201
//          .clk_out     (ex1_ex2_pipe_clk)); @202

always @(posedge ex2_pipe_clk)
begin
  if(ex2_pipedown)
  begin
    fdsu_ex3_rem_sign        <= srt_remainder_sign;
    fdsu_ex3_rem_zero        <= srt_remainder_zero;
    fdsu_ex3_id_srt_skip     <= ex2_id_nor_srt_skip;
  end
  else
  begin
    fdsu_ex3_rem_sign        <= fdsu_ex3_rem_sign;
    fdsu_ex3_rem_zero        <= fdsu_ex3_rem_zero;
    fdsu_ex3_id_srt_skip    <=  fdsu_ex3_id_srt_skip;
  end
end

// &Force("output","fdsu_ex3_rem_sign"); @243
// &Force("output","fdsu_ex3_rem_zero"); @244
// &Force("output","fdsu_ex3_result_denorm_round_add_num"); @245
// &Force("output","fdsu_ex3_id_srt_skip"); @246

//==========================================================
//    SRT Remainder & Divisor for Quotient/Root Generate
//==========================================================

//===================Remainder Generate=====================
//gate clk
// &Instance("gated_clk_cell","x_srt_rem_clk");
// // &Connect( .clk_in         (forever_cpuclk), @255
// //           .clk_out        (srt_rem_clk),//Out Clock @256
// //           .external_en    (1'b0), @257
// //           .global_en      (cp0_yy_clk_en), @258
// //           .local_en       (srt_rem_clk_en),//Local Condition @259
// //           .module_en      (cp0_fpu_icg_en) @260
// //         ); @261
// assign srt_rem_clk_en = ex1_pipedown ||
//                         srt_sm_on;

always @(posedge qt_clk)
begin
  if (ex1_pipedown)
    srt_remainder[31:0] <= ex1_remainder[31:0];
  else if (srt_sm_on)
    srt_remainder[31:0] <= srt_remainder_nxt[31:0];
  else
    srt_remainder[31:0] <= srt_remainder[31:0];
end

//=====================Divisor Generate=====================
//gate clk
// &Instance("gated_clk_cell","x_srt_div_clk"); @291
gated_clk_cell  x_srt_div_clk (
  .clk_in             (forever_cpuclk    ),
  .clk_out            (srt_div_clk       ),
  .external_en        (1'b0              ),
  .global_en          (cp0_yy_clk_en     ),
  .local_en           (srt_div_clk_en    ),
  .module_en          (cp0_fpu_icg_en    ),
  .pad_yy_icg_scan_en (pad_yy_icg_scan_en)
);

// &Connect( .clk_in         (forever_cpuclk), @292
//           .clk_out        (srt_div_clk),//Out Clock @293
//           .external_en    (1'b0), @294
//           .global_en      (cp0_yy_clk_en), @295
//           .local_en       (srt_div_clk_en),//Local Condition @296
//           .module_en      (cp0_fpu_icg_en) @297
//         ); @298
assign srt_div_clk_en = ex1_pipedown_gate
                     || ex1_save_op0_gate
                     || ex3_pipedown;
// final_rst saved in srt_divisor.
// srt_divisor is 26 bits, final_rst is 24 bits.
always @(posedge srt_div_clk)
begin
  if (ex1_save_op0)
    srt_divisor[25:0] <= {3'b0, {ex1_oper_id_frac[51:29]}};
  else if (ex1_pipedown)
    srt_divisor[25:0] <= {2'b0, ex1_divisor[23:0]};
  else if (ex3_pipedown)
    srt_divisor[25:0] <= ex3_frac_final_rst[25:0];
  else
    srt_divisor[25:0] <= srt_divisor[25:0];
end
assign ex1_oper_id_frac_f[51:0] = {srt_divisor[22:0], 29'b0};
// &Force("bus", "ex1_oper_id_frac", 51, 0); @332
assign fdsu_ex4_frac[25:0] = srt_divisor[25:0];

//=======================Bound Select=======================
//---------------------------------------+
// K   | 8 | 9 | 10| 11| 12| 13| 14|15,16|
//---------------------------------------+
//32S1 | 7 | 7 | 8 | 9 | 9 | 10| 11|  12 |
//---------------------------------------+
//32S2 | 25| 28| 31| 33| 36| 39| 41|  47 |
//---------------------------------------+

//bound_sel[3:0]
//For div,  use divisor high four bit as K
//For sqrt, use 2qi high four bit as K next round and
//          use 1010 as K first round
assign bound_sel[3:0] = (fdsu_ex2_div)
                      ? srt_divisor[23:20]
                      : (ex2_srt_first_round)
                        ? 4'b1010
                        : total_qt_rt_30[28:25];
//Select bound as look up table
//   K = bound_sel[3:0]
//32S1 = digit_bound_1[7:0]
//32s2 = digit_bound_2[7:0]
// &CombBeg; @357
always @( bound_sel[3:0])
begin
case(bound_sel[3:0])
4'b0000:       //when first interation get "10", choose k=16
   begin
     digit_bound_1[7:0] = 8'b11110100;//-12
     digit_bound_2[7:0] = 8'b11010001;//-47
   end
4'b1000:
   begin
     digit_bound_1[7:0] = 8'b11111001;//-7
     digit_bound_2[7:0] = 8'b11100111;//-25
   end
4'b1001:
   begin
     digit_bound_1[7:0] = 8'b11111001;//-7
     digit_bound_2[7:0] = 8'b11100100;//-28
   end
4'b1010:
   begin
     digit_bound_1[7:0] = 8'b11111000;//-8
     digit_bound_2[7:0] = 8'b11100001;//-31
   end
4'b1011:
   begin
     digit_bound_1[7:0] = 8'b11110111;//-9
     digit_bound_2[7:0] = 8'b11011111;//-33
   end
4'b1100:
   begin
     digit_bound_1[7:0] = 8'b11110111;//-9
     digit_bound_2[7:0] = 8'b11011100;//-36
   end
4'b1101:
   begin
     digit_bound_1[7:0] = 8'b11110110;//-10
     digit_bound_2[7:0] = 8'b11011001;//-39
   end
4'b1110:
   begin
     digit_bound_1[7:0] = 8'b11110101;//-11
     digit_bound_2[7:0] = 8'b11010111;//-41
   end
4'b1111:
   begin
     digit_bound_1[7:0] = 8'b11110100;//-12
     digit_bound_2[7:0] = 8'b11010001;//-47
   end
default:
   begin
     digit_bound_1[7:0] = 8'b11111001;//-7
     digit_bound_2[7:0] = 8'b11100111;//-25
   end
endcase
// &CombEnd; @410
end

//==============Prepare for quotient generate===============
assign bound1_cmp_result[7:0] = qtrt_sel_rem[7:0] + digit_bound_1[7:0];
assign bound2_cmp_result[7:0] = qtrt_sel_rem[7:0] + digit_bound_2[7:0];
assign bound1_cmp_sign        = bound1_cmp_result[7];
assign bound2_cmp_sign        = bound2_cmp_result[7];
assign rem_sign               = srt_remainder[29];

//qtrt_sel_rem is use to select quotient
//Only when sqrt first round use 8R0 select quotient(special rule)
//4R0 is used to select quotient on other condition
//For negative remaider, we use ~rem not (~rem + 1)
//Because  bound1 <=  rem   <   bound2, when positive rem
//        -bound2 <=  rem   <  -bound1, when negative rem
//Thus     bound1 <  -rem   <=  bound2, when negative rem
//Thus     bound1 <= -rem-1 <   bound2, when negative rem
//Thus     bound1 <= ~rem   <   bound2, when negative rem
//srt_remainder[29] used as sign bit
// &CombBeg; @429
always @( ex2_srt_first_round
       or fdsu_ex2_sqrt
       or srt_remainder[29:21])
begin
if(ex2_srt_first_round && fdsu_ex2_sqrt)
  qtrt_sel_rem[7:0] = {srt_remainder[29],   srt_remainder[27:21]};
else
  qtrt_sel_rem[7:0] =  srt_remainder[29] ? ~srt_remainder[29:22]
                                         :  srt_remainder[29:22];
// &CombEnd; @435
end

//==========================================================
//     on fly round method to generate total quotient
//==========================================================
//gate clk
// &Instance("gated_clk_cell","x_qt_clk"); @441
gated_clk_cell  x_qt_clk (
  .clk_in             (forever_cpuclk    ),
  .clk_out            (qt_clk            ),
  .external_en        (1'b0              ),
  .global_en          (cp0_yy_clk_en     ),
  .local_en           (qt_clk_en         ),
  .module_en          (cp0_fpu_icg_en    ),
  .pad_yy_icg_scan_en (pad_yy_icg_scan_en)
);

// &Connect( .clk_in         (forever_cpuclk), @442
//           .clk_out        (qt_clk),//Out Clock @443
//           .external_en    (1'b0), @444
//           .global_en      (cp0_yy_clk_en), @445
//           .local_en       (qt_clk_en),//Local Condition @446
//           .module_en      (cp0_fpu_icg_en) @447
//         ); @448
assign qt_clk_en = srt_sm_on ||
                   ex1_pipedown_gate;

//qt_rt_const_shift_std[29:0] is const data for on fly round
//                which is used to record the times of round
//
//total_qt_rt[29:0]       is total quotient
//total_qt_rt_minus[29:0] is total quotient minus
//                which is used to generate quotient rapidly
always @(posedge qt_clk)
begin
  if(ex1_pipedown)
  begin
    qt_rt_const_shift_std[29:0] <= {1'b0,1'b1,28'b0};
    total_qt_rt_30[29:0]        <= 30'b0;
    total_qt_rt_minus_30[29:0]  <= 30'b0;
  end
  else if(srt_sm_on)
  begin
    qt_rt_const_shift_std[29:0] <= qt_rt_const_shift_std_next[29:0];
    total_qt_rt_30[29:0]        <= total_qt_rt_30_next[29:0];
    total_qt_rt_minus_30[29:0]  <= total_qt_rt_minus_30_next[29:0];
  end
  else
  begin
    qt_rt_const_shift_std[29:0] <= qt_rt_const_shift_std[29:0];
    total_qt_rt_30[29:0]        <= total_qt_rt_30[29:0];
    total_qt_rt_minus_30[29:0]  <= total_qt_rt_minus_30[29:0];
  end
end
// &Force("output","total_qt_rt_30"); @508

//qt_rt_const_q1/q2/q3 for shift 1/2/3 in
assign qt_rt_const_q1[29:0] =  qt_rt_const_shift_std[29:0];
assign qt_rt_const_q2[29:0] = {qt_rt_const_shift_std[28:0],1'b0};
assign qt_rt_const_q3[29:0] =  qt_rt_const_q1[29:0] |
                               qt_rt_const_q2[29:0];
//qt_rt_const update value
assign qt_rt_const_shift_std_next[29:0] = {2'b0, qt_rt_const_shift_std[29:2]};

//========total_qt_rt & total_qt_rt_minus update value======
//q(i+1) is the total quotient/root after the (i+1) digit
//is calculated
//                 q(i+1)             qm(i+1)
//d(i+1)=-2     qm(i)+2*shift      qm(i)+1*shift
//d(i+1)=-1     qm(i)+3*shift      qm(i)+2*shift
//d(i+1)=0      q(i)               qm(i)+3*shift
//d(i+1)=1      q(i)+1*shift       q(i)
//d(i+1)=2      q(i)+2*shift       q(i)+1*shift
//Note:
//shift = 4^(-i-1), qm(i+1)=q(i+1)-shift

//pre select for quotient
assign total_qt_rt_pre_sel[29:0]         = (rem_sign) ?
                                           total_qt_rt_minus_30[29:0] :
                                           total_qt_rt_30[29:0];
//when the quotient is 2 or -2
assign qt_rt_const_pre_sel_q2[29:0]      = qt_rt_const_q2[29:0];
assign qt_rt_mins_const_pre_sel_q2[29:0] = qt_rt_const_q1[29:0];
//when the quotient is 1 or -1
assign qt_rt_const_pre_sel_q1[29:0]      = (rem_sign) ?
                                           qt_rt_const_q3[29:0] ://-1
                                           qt_rt_const_q1[29:0]; //1
assign qt_rt_mins_const_pre_sel_q1[29:0] = (rem_sign) ?
                                           qt_rt_const_q2[29:0] : //-1
                                           30'b0;

//After bound compare, the final selection
// &CombBeg; @546
always @( qt_rt_const_q3[29:0]
       or qt_rt_mins_const_pre_sel_q1[29:0]
       or bound1_cmp_sign
       or total_qt_rt_30[29:0]
       or qt_rt_mins_const_pre_sel_q2[29:0]
       or total_qt_rt_minus_30[29:0]
       or bound2_cmp_sign
       or qt_rt_const_pre_sel_q2[29:0]
       or qt_rt_const_pre_sel_q1[29:0]
       or total_qt_rt_pre_sel[29:0])
begin
casez({bound1_cmp_sign,bound2_cmp_sign})
  2'b00:// the quotient is -2 or 2
  begin
    total_qt_rt_30_next[29:0]       = total_qt_rt_pre_sel[29:0] |
                                      qt_rt_const_pre_sel_q2[29:0];
    total_qt_rt_minus_30_next[29:0] = total_qt_rt_pre_sel[29:0] |
                                      qt_rt_mins_const_pre_sel_q2[29:0];
  end
  2'b01:// quotient is -1 or 1
  begin
    total_qt_rt_30_next[29:0]       = total_qt_rt_pre_sel[29:0] |
                                      qt_rt_const_pre_sel_q1[29:0];
    total_qt_rt_minus_30_next[29:0] = total_qt_rt_pre_sel[29:0] |
                                      qt_rt_mins_const_pre_sel_q1[29:0];
  end
  2'b1?: // quotient is 0
  begin
    total_qt_rt_30_next[29:0]       = total_qt_rt_30[29:0];
    total_qt_rt_minus_30_next[29:0] = total_qt_rt_minus_30[29:0] |
                                      qt_rt_const_q3[29:0];
  end
  default:
  begin
    total_qt_rt_30_next[29:0]       = 30'b0;
    total_qt_rt_minus_30_next[29:0] = 30'b0;
  end
endcase
// &CombEnd; @574
end

//==========================================================
//      on fly round method to generate cur remainder
//==========================================================
//Division emainder add value
//Quoit 1
assign div_qt_1_rem_add_op1[31:0]   = ~{3'b0,srt_divisor[23:0],5'b0};
//Quoit 2
assign div_qt_2_rem_add_op1[31:0]   = ~{2'b0,srt_divisor[23:0],6'b0};
//Quoit -1
assign div_qt_r1_rem_add_op1[31:0]  =  {3'b0,srt_divisor[23:0],5'b0};
//Quoit -2
assign div_qt_r2_rem_add_op1[31:0]  =  {2'b0,srt_divisor[23:0],6'b0};

//Sqrt remainder add value op1
//Quoit 1
assign sqrt_qt_1_rem_add_op1[31:0]  = ~({2'b0,total_qt_rt_30[29:0]} |
                                        {3'b0,qt_rt_const_q1[29:1]});
//Quoit 2
assign sqrt_qt_2_rem_add_op1[31:0]  = ~({1'b0,total_qt_rt_30[29:0],1'b0} |
                                        {1'b0,qt_rt_const_q1[29:0],1'b0});
//Quoit -1
assign sqrt_qt_r1_rem_add_op1[31:0] =   {2'b0,total_qt_rt_minus_30[29:0]} |
                                        {1'b0,qt_rt_const_q1[29:0],1'b0}  |
                                        {2'b0,qt_rt_const_q1[29:0]}       |
                                        {3'b0,qt_rt_const_q1[29:1]};
//Quoit -2
assign sqrt_qt_r2_rem_add_op1[31:0] =   {1'b0,
                                         total_qt_rt_minus_30[29:0],1'b0} |
                                        {qt_rt_const_q1[29:0],2'b0}       |
                                        {1'b0,qt_rt_const_q1[29:0],1'b0};
//Remainder Adder select logic
// &CombBeg; @607
always @( div_qt_2_rem_add_op1[31:0]
       or sqrt_qt_r2_rem_add_op1[31:0]
       or sqrt_qt_r1_rem_add_op1[31:0]
       or rem_sign
       or div_qt_r2_rem_add_op1[31:0]
       or div_qt_1_rem_add_op1[31:0]
       or sqrt_qt_2_rem_add_op1[31:0]
       or fdsu_ex2_sqrt
       or div_qt_r1_rem_add_op1[31:0]
       or sqrt_qt_1_rem_add_op1[31:0])
begin
case({rem_sign,fdsu_ex2_sqrt})
  2'b01:
  begin
        rem_add1_op1[31:0] = sqrt_qt_1_rem_add_op1[31:0];
        rem_add2_op1[31:0] = sqrt_qt_2_rem_add_op1[31:0];
  end
  2'b00:
  begin
        rem_add1_op1[31:0] = div_qt_1_rem_add_op1[31:0];
        rem_add2_op1[31:0] = div_qt_2_rem_add_op1[31:0];
  end
  2'b11:
  begin
        rem_add1_op1[31:0] = sqrt_qt_r1_rem_add_op1[31:0];
        rem_add2_op1[31:0] = sqrt_qt_r2_rem_add_op1[31:0];
  end
  2'b10:
  begin
        rem_add1_op1[31:0] = div_qt_r1_rem_add_op1[31:0];
        rem_add2_op1[31:0] = div_qt_r2_rem_add_op1[31:0];
  end
  default :
  begin
        rem_add1_op1[31:0] = 32'b0;
        rem_add2_op1[31:0] = 32'b0;
  end
  endcase
// &CombEnd; @635
end
assign srt_remainder_shift[31:0] = {srt_remainder[31],
                                    srt_remainder[28:0],2'b0};
//Remainder add
assign cur_doub_rem_1[31:0]      = srt_remainder_shift[31:0] +
                                   rem_add1_op1[31:0]    +
                                   {31'b0, ~rem_sign};
assign cur_doub_rem_2[31:0]      = srt_remainder_shift[31:0] +
                                   rem_add2_op1[31:0]    +
                                   {31'b0, ~rem_sign};
assign cur_rem_1[31:0]           = cur_doub_rem_1[31:0];
assign cur_rem_2[31:0]           = cur_doub_rem_2[31:0];
//Generate srt remainder update value
// &CombBeg; @648
always @( cur_rem_2[31:0]
       or bound1_cmp_sign
       or srt_remainder_shift[31:0]
       or bound2_cmp_sign
       or cur_rem_1[31:0])
begin
case({bound1_cmp_sign,bound2_cmp_sign})
  2'b00:   cur_rem[31:0]         = cur_rem_2[31:0];  //+-2
  2'b01:   cur_rem[31:0]         = cur_rem_1[31:0];  //+-1
  default: cur_rem[31:0]         = srt_remainder_shift[31:0]; //0
endcase
// &CombEnd; @654
end
assign srt_remainder_nxt[31:0]   = cur_rem[31:0];

//Remainder is zero signal in EX3
assign srt_remainder_zero        = ~|srt_remainder[31:0];
// &Force("output","srt_remainder_zero"); @659
assign srt_remainder_sign        =   srt_remainder[31];

// &Force("output", "ex2_uf"); @662
// &ModuleEnd; @663
endmodule



