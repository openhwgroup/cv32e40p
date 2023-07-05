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
module pa_fdsu_round_single(
  cp0_fpu_icg_en,
  cp0_yy_clk_en,
  ex3_expnt_adjust_result,
  ex3_frac_final_rst,
  ex3_pipedown,
  ex3_rslt_denorm,
  fdsu_ex3_id_srt_skip,
  fdsu_ex3_rem_sign,
  fdsu_ex3_rem_zero,
  fdsu_ex3_result_denorm_round_add_num,
  fdsu_ex4_denorm_to_tiny_frac,
  fdsu_ex4_nx,
  fdsu_ex4_potnt_norm,
  fdsu_ex4_result_nor,
  fdsu_yy_expnt_rst,
  fdsu_yy_result_inf,
  fdsu_yy_result_lfn,
  fdsu_yy_result_sign,
  fdsu_yy_rm,
  fdsu_yy_rslt_denorm,
  forever_cpuclk,
  pad_yy_icg_scan_en,
  total_qt_rt_30
);

// &Ports; @24
input           cp0_fpu_icg_en;                      
input           cp0_yy_clk_en;                       
input           ex3_pipedown;                        
input           fdsu_ex3_id_srt_skip;                
input           fdsu_ex3_rem_sign;                   
input           fdsu_ex3_rem_zero;                   
input   [23:0]  fdsu_ex3_result_denorm_round_add_num; 
input   [9 :0]  fdsu_yy_expnt_rst;                   
input           fdsu_yy_result_inf;                  
input           fdsu_yy_result_lfn;                  
input           fdsu_yy_result_sign;                 
input   [2 :0]  fdsu_yy_rm;                          
input           fdsu_yy_rslt_denorm;                 
input           forever_cpuclk;                      
input           pad_yy_icg_scan_en;                  
input   [29:0]  total_qt_rt_30;                      
output  [9 :0]  ex3_expnt_adjust_result;             
output  [25:0]  ex3_frac_final_rst;                  
output          ex3_rslt_denorm;                     
output          fdsu_ex4_denorm_to_tiny_frac;        
output          fdsu_ex4_nx;                         
output  [1 :0]  fdsu_ex4_potnt_norm;                 
output          fdsu_ex4_result_nor;                 

// &Regs; @25
reg             denorm_to_tiny_frac;                 
reg             fdsu_ex4_denorm_to_tiny_frac;        
reg             fdsu_ex4_nx;                         
reg     [1 :0]  fdsu_ex4_potnt_norm;                 
reg             fdsu_ex4_result_nor;                 
reg     [25:0]  frac_add1_op1;                       
reg             frac_add_1;                          
reg             frac_orig;                           
reg     [25:0]  frac_sub1_op1;                       
reg             frac_sub_1;                          
reg     [27:0]  qt_result_single_denorm_for_round;   
reg             single_denorm_lst_frac;              

// &Wires; @26
wire            cp0_fpu_icg_en;                      
wire            cp0_yy_clk_en;                       
wire            ex3_denorm_eq;                       
wire            ex3_denorm_gr;                       
wire            ex3_denorm_lst_frac;                 
wire            ex3_denorm_nx;                       
wire            ex3_denorm_plus;                     
wire            ex3_denorm_potnt_norm;               
wire            ex3_denorm_zero;                     
wire    [9 :0]  ex3_expnt_adjst;                     
wire    [9 :0]  ex3_expnt_adjust_result;             
wire    [25:0]  ex3_frac_final_rst;                  
wire            ex3_nx;                              
wire            ex3_pipe_clk;                        
wire            ex3_pipe_clk_en;                     
wire            ex3_pipedown;                        
wire    [1 :0]  ex3_potnt_norm;                      
wire            ex3_qt_eq;                           
wire            ex3_qt_gr;                           
wire            ex3_qt_sing_lo3_not0;                
wire            ex3_qt_sing_lo4_not0;                
wire            ex3_qt_zero;                         
wire            ex3_rslt_denorm;                     
wire            ex3_rst_eq_1;                        
wire            ex3_rst_nor;                         
wire            ex3_single_denorm_eq;                
wire            ex3_single_denorm_gr;                
wire            ex3_single_denorm_zero;              
wire            ex3_single_low_not_zero;             
wire    [9 :0]  fdsu_ex3_expnt_rst;                  
wire            fdsu_ex3_id_srt_skip;                
wire            fdsu_ex3_rem_sign;                   
wire            fdsu_ex3_rem_zero;                   
wire    [23:0]  fdsu_ex3_result_denorm_round_add_num; 
wire            fdsu_ex3_result_inf;                 
wire            fdsu_ex3_result_lfn;                 
wire            fdsu_ex3_result_sign;                
wire    [2 :0]  fdsu_ex3_rm;                         
wire            fdsu_ex3_rslt_denorm;                
wire    [9 :0]  fdsu_yy_expnt_rst;                   
wire            fdsu_yy_result_inf;                  
wire            fdsu_yy_result_lfn;                  
wire            fdsu_yy_result_sign;                 
wire    [2 :0]  fdsu_yy_rm;                          
wire            fdsu_yy_rslt_denorm;                 
wire            forever_cpuclk;                      
wire    [25:0]  frac_add1_op1_with_denorm;           
wire    [25:0]  frac_add1_rst;                       
wire            frac_denorm_rdn_add_1;               
wire            frac_denorm_rdn_sub_1;               
wire            frac_denorm_rmm_add_1;               
wire            frac_denorm_rne_add_1;               
wire            frac_denorm_rtz_sub_1;               
wire            frac_denorm_rup_add_1;               
wire            frac_denorm_rup_sub_1;               
wire    [25:0]  frac_final_rst;                      
wire            frac_rdn_add_1;                      
wire            frac_rdn_sub_1;                      
wire            frac_rmm_add_1;                      
wire            frac_rne_add_1;                      
wire            frac_rtz_sub_1;                      
wire            frac_rup_add_1;                      
wire            frac_rup_sub_1;                      
wire    [25:0]  frac_sub1_op1_with_denorm;           
wire    [25:0]  frac_sub1_rst;                       
wire            pad_yy_icg_scan_en;                  
wire    [29:0]  total_qt_rt_30;                      


assign fdsu_ex3_result_sign     = fdsu_yy_result_sign;
assign fdsu_ex3_expnt_rst[9:0]  = fdsu_yy_expnt_rst[9:0];
assign fdsu_ex3_result_inf      = fdsu_yy_result_inf;
assign fdsu_ex3_result_lfn      = fdsu_yy_result_lfn;
assign fdsu_ex3_rm[2:0]         = fdsu_yy_rm[2:0];
assign fdsu_ex3_rslt_denorm     = fdsu_yy_rslt_denorm;
//=======================Round Rule=========================
//1/8 <= x < 1/4, 1/2 <= y < 1, => 1/8 < z < 1/2
//q[29:0] represent the fraction part result of quotient, q[29] for 1/2
//Thus the first "1" in 30 bit quotient will be in q[28] or q[27]
//For Single Float
//15 round to get 30 bit quotient, 23+1 bit as valid result, other for round
//if q[28] is 1, q[28:5] as 1.xxxx valid result, [4:0] for round
//if q[28] is 0, q[27:4] as 1.xxxx valid result, [3:0] for round
// &Force("bus","total_qt_rt_30",29,0); @42
assign ex3_qt_sing_lo4_not0 = |total_qt_rt_30[3:0];
assign ex3_qt_sing_lo3_not0 = |total_qt_rt_30[2:0];
//the quotient round bits great than "10000"(ronnd bits 10..0)
assign ex3_qt_gr          = (total_qt_rt_30[28])
                            ?  total_qt_rt_30[4] && ex3_qt_sing_lo4_not0
                            :  total_qt_rt_30[3] && ex3_qt_sing_lo3_not0;

//the quotient round bits is equal to "10000"(ronnd bits 10..0)
assign ex3_qt_eq          = (total_qt_rt_30[28])
                            ?  total_qt_rt_30[4] && !ex3_qt_sing_lo4_not0
                            :  total_qt_rt_30[3] && !ex3_qt_sing_lo3_not0;
//the quotient round bits is zero
assign ex3_qt_zero        = (total_qt_rt_30[28])
                            ? ~|total_qt_rt_30[4:0]
                            : ~|total_qt_rt_30[3:0];
//quotient is 1.00000..00 need special dealt with in the following
assign ex3_rst_eq_1    = total_qt_rt_30[28] && ~|total_qt_rt_30[27:5];
// for denormal result, first select the quotation num for rounding
//  specially for the result e=-126 and e=-1022,the denorm depends on the
//  MSB of the quotient
assign ex3_denorm_plus       = !total_qt_rt_30[28] && (fdsu_ex3_expnt_rst[9:0] == 10'h382);
assign ex3_denorm_potnt_norm = total_qt_rt_30[28] && (fdsu_ex3_expnt_rst[9:0] == 10'h381);
assign ex3_rslt_denorm            = ex3_denorm_plus || fdsu_ex3_rslt_denorm;
// &Force("output", "ex3_rslt_denorm"); @66

//denomal result, check for rounding further optimization can be done in
//future
// &CombBeg; @70
always @( total_qt_rt_30[28:0]
       or fdsu_ex3_expnt_rst[9:0])
begin
case(fdsu_ex3_expnt_rst[9:0])
  10'h382:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[4:0],23'b0}; //-126 1
                single_denorm_lst_frac =  total_qt_rt_30[5];
			 		end//-1022 1
  10'h381:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[5:0],22'b0}; //-127 0
                single_denorm_lst_frac =  total_qt_rt_30[6];
			 		end//-1022 1
  10'h380:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[6:0],21'b0}; //-128 -1
                single_denorm_lst_frac =  total_qt_rt_30[7];
			 		end//-1022 1
  10'h37f:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[7:0],20'b0}; //-129 -2
                single_denorm_lst_frac =  total_qt_rt_30[8];
			 		end//-1022 1
  10'h37e:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[8:0],19'b0}; //-130 -3
                single_denorm_lst_frac =  total_qt_rt_30[9];
			 		end//-1022 1
  10'h37d:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[9:0],18'b0}; //-131 -4
                single_denorm_lst_frac =  total_qt_rt_30[10];
			 		end//-1022 1
  10'h37c:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[10:0],17'b0}; //-132 -5
                single_denorm_lst_frac =  total_qt_rt_30[11];
			 		end//-1022 1
  10'h37b:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[11:0],16'b0}; //-133 -6
                single_denorm_lst_frac =  total_qt_rt_30[12];
			 		end//-1022 1
  10'h37a:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[12:0],15'b0}; //-134 -7
                single_denorm_lst_frac =  total_qt_rt_30[13];
			 		end//-1022 1
  10'h379:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[13:0],14'b0}; //-135 -8
                single_denorm_lst_frac =  total_qt_rt_30[14];
			 		end//-1022 1
  10'h378:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[14:0],13'b0}; //-136 -9
                single_denorm_lst_frac =  total_qt_rt_30[15];
			 		end//-1022 1
  10'h377:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[15:0],12'b0}; //-137 -10
                single_denorm_lst_frac =  total_qt_rt_30[16];
			 		end//-1022 1
  10'h376:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[16:0],11'b0}; //-138 -11
                single_denorm_lst_frac =  total_qt_rt_30[17];
			 		end//-1022 1
  10'h375:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[17:0],10'b0}; //-139 -12
                single_denorm_lst_frac =  total_qt_rt_30[18];
			 		end//-1022 1
  10'h374:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[18:0],9'b0}; //-140 -13
                single_denorm_lst_frac =  total_qt_rt_30[19];
			 		end//-1022 1
  10'h373:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[19:0],8'b0}; // -141
                single_denorm_lst_frac =  total_qt_rt_30[20];
			 		end//-1022 1
  10'h372:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[20:0],7'b0};//-142
                single_denorm_lst_frac =  total_qt_rt_30[21];
			 		end//-1022 1
  10'h371:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[21:0],6'b0};//-143
                single_denorm_lst_frac =  total_qt_rt_30[22];
			 		end//-1022 1
  10'h370:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[22:0],5'b0}; //-144
                single_denorm_lst_frac =  total_qt_rt_30[23];
			 		end//-1022 1
  10'h36f:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[23:0],4'b0}; //-145
                single_denorm_lst_frac =  total_qt_rt_30[24];
			 		end//-1022 1
  10'h36e:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[24:0],3'b0}; //-146
                single_denorm_lst_frac =  total_qt_rt_30[25];
			 		end//-1022 1
  10'h36d:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[25:0],2'b0}; //-147
                single_denorm_lst_frac =  total_qt_rt_30[26];
			 		end//-1022 1
  10'h36c:begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[26:0],1'b0}; //-148
                single_denorm_lst_frac =  total_qt_rt_30[27];
			 		end//-1022 1
  10'h36b: begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[27:0]};
                 single_denorm_lst_frac = total_qt_rt_30[28] ;
						end//-1022 1
  default:  begin qt_result_single_denorm_for_round[27:0] = {total_qt_rt_30[28:1]};
                 single_denorm_lst_frac = 1'b0;
						end//-1022 1
endcase
// &CombEnd; @148
end
//rounding evaluation for single denormalize number
assign ex3_single_denorm_eq      = qt_result_single_denorm_for_round[27]
                                   &&  !ex3_single_low_not_zero;
assign ex3_single_low_not_zero   = |qt_result_single_denorm_for_round[26:0];
assign ex3_single_denorm_gr      = qt_result_single_denorm_for_round[27]
                                   &&  ex3_single_low_not_zero;
assign ex3_single_denorm_zero    = !qt_result_single_denorm_for_round[27]
                                   && !ex3_single_low_not_zero;

//rounding check fo denormalize result
assign ex3_denorm_eq             = ex3_single_denorm_eq;
assign ex3_denorm_gr             = ex3_single_denorm_gr;
assign ex3_denorm_zero           = ex3_single_denorm_zero;
assign ex3_denorm_lst_frac       = single_denorm_lst_frac;
//Different Round Mode with different rounding rule
//Here we call rounding bit as "rb", remainder as "rem"
//RNE :
//  1.+1 : rb>10000 || rb==10000 && rem>0
//  2. 0 : Rest Condition
//  3.-1 : Never occur
//RTZ :
//  1.+1 : Never occur
//  2. 0 : Rest Condition
//  3.-1 : rb=10000 && rem<0
//RDN :
//  1.+1 : Q>0 Never occur   ; Q<0 Rest condition
//  2. 0 : Q>0 Rest condition; Q<0 Rem<0 && rb=0
//  3.-1 : Q>0 Rem<0 && rb=0 ; Q<0 Never occur
//RUP :
//  1.+1 : Q>0 Rest Condition; Q<0 Never occur
//  2. 0 : Q>0 Rem<0 && rb=0 ; Q<0 Rest condition
//  3.-1 : Q>0 Never occur   ; Q<0 Rem<0 && rb=0
//RMM :
//  1.+1 : rb>10000 || rb==10000 && rem>0
//  2. 0 : Rest Condition
//  3.-1 : Never occur
assign frac_rne_add_1 = ex3_qt_gr ||
                       (ex3_qt_eq && !fdsu_ex3_rem_sign);
assign frac_rtz_sub_1 = ex3_qt_zero && fdsu_ex3_rem_sign;
assign frac_rup_add_1 = !fdsu_ex3_result_sign &&
                       (!ex3_qt_zero ||
                       (!fdsu_ex3_rem_sign && !fdsu_ex3_rem_zero));
assign frac_rup_sub_1 = fdsu_ex3_result_sign &&
                       (ex3_qt_zero && fdsu_ex3_rem_sign);
assign frac_rdn_add_1 = fdsu_ex3_result_sign &&
                       (!ex3_qt_zero ||
                       (!fdsu_ex3_rem_sign && !fdsu_ex3_rem_zero));
assign frac_rdn_sub_1 = !fdsu_ex3_result_sign &&
                       (ex3_qt_zero && fdsu_ex3_rem_sign);
assign frac_rmm_add_1 = ex3_qt_gr ||
                       (ex3_qt_eq && !fdsu_ex3_rem_sign);
//denormal result
assign frac_denorm_rne_add_1 = ex3_denorm_gr ||
                               (ex3_denorm_eq &&
                               ((fdsu_ex3_rem_zero &&
                                ex3_denorm_lst_frac) ||
                               (!fdsu_ex3_rem_zero &&
                                !fdsu_ex3_rem_sign)));
assign frac_denorm_rtz_sub_1 = ex3_denorm_zero && fdsu_ex3_rem_sign;
assign frac_denorm_rup_add_1 = !fdsu_ex3_result_sign &&
                               (!ex3_denorm_zero ||
                               (!fdsu_ex3_rem_sign && !fdsu_ex3_rem_zero));
assign frac_denorm_rup_sub_1 = fdsu_ex3_result_sign &&
                       (ex3_denorm_zero && fdsu_ex3_rem_sign);
assign frac_denorm_rdn_add_1 = fdsu_ex3_result_sign &&
                       (!ex3_denorm_zero ||
                       (!fdsu_ex3_rem_sign && !fdsu_ex3_rem_zero));
assign frac_denorm_rdn_sub_1 = !fdsu_ex3_result_sign &&
                       (ex3_denorm_zero && fdsu_ex3_rem_sign);
assign frac_denorm_rmm_add_1 = ex3_denorm_gr ||
                       (ex3_denorm_eq && !fdsu_ex3_rem_sign);

//RM select
// &CombBeg; @222
always @( fdsu_ex3_rm[2:0]
       or frac_denorm_rdn_add_1
       or frac_rne_add_1
       or frac_denorm_rdn_sub_1
       or fdsu_ex3_result_sign
       or frac_rup_add_1
       or frac_denorm_rup_sub_1
       or frac_rdn_sub_1
       or frac_rtz_sub_1
       or frac_rdn_add_1
       or fdsu_ex3_id_srt_skip
       or frac_denorm_rtz_sub_1
       or ex3_rslt_denorm
       or frac_rup_sub_1
       or frac_denorm_rmm_add_1
       or frac_denorm_rup_add_1
       or frac_denorm_rne_add_1
       or frac_rmm_add_1)
begin
case(fdsu_ex3_rm[2:0])
  3'b000://round to nearst,ties to even
  begin
    frac_add_1          =  ex3_rslt_denorm ? frac_denorm_rne_add_1 : frac_rne_add_1;
    frac_sub_1          =  1'b0;
    frac_orig           =  ex3_rslt_denorm ? !frac_denorm_rne_add_1 : !frac_rne_add_1;
    denorm_to_tiny_frac =  fdsu_ex3_id_srt_skip ? 1'b0 : frac_denorm_rne_add_1;
  end
  3'b001:// round to 0
  begin
    frac_add_1           =  1'b0;
    frac_sub_1           =  ex3_rslt_denorm ? frac_denorm_rtz_sub_1 : frac_rtz_sub_1;
    frac_orig            =  ex3_rslt_denorm ? !frac_denorm_rtz_sub_1 : !frac_rtz_sub_1;
    denorm_to_tiny_frac  = 1'b0;
  end
  3'b010://round to -inf
  begin
    frac_add_1          =  ex3_rslt_denorm ? frac_denorm_rdn_add_1 : frac_rdn_add_1;
    frac_sub_1          =  ex3_rslt_denorm ? frac_denorm_rdn_sub_1 : frac_rdn_sub_1;
    frac_orig           =  ex3_rslt_denorm ? !frac_denorm_rdn_add_1 && !frac_denorm_rdn_sub_1
                                           : !frac_rdn_add_1 && !frac_rdn_sub_1;
    denorm_to_tiny_frac = fdsu_ex3_id_srt_skip ? fdsu_ex3_result_sign
                                                : frac_denorm_rdn_add_1;
  end
  3'b011://round to +inf
  begin
    frac_add_1          =  ex3_rslt_denorm ? frac_denorm_rup_add_1 : frac_rup_add_1;
    frac_sub_1          =  ex3_rslt_denorm ? frac_denorm_rup_sub_1 : frac_rup_sub_1;
    frac_orig           =  ex3_rslt_denorm ? !frac_denorm_rup_add_1 && !frac_denorm_rup_sub_1
                                           : !frac_rup_add_1 && !frac_rup_sub_1;
    denorm_to_tiny_frac = fdsu_ex3_id_srt_skip ? !fdsu_ex3_result_sign
                                                : frac_denorm_rup_add_1;
  end
  3'b100://round to nearest,ties to max magnitude
  begin
    frac_add_1          = ex3_rslt_denorm ? frac_denorm_rmm_add_1 : frac_rmm_add_1;
    frac_sub_1          = 1'b0;
    frac_orig           = ex3_rslt_denorm ? !frac_denorm_rmm_add_1 : !frac_rmm_add_1;
    denorm_to_tiny_frac = fdsu_ex3_id_srt_skip ? 1'b0 : frac_denorm_rmm_add_1;
  end
  default:
  begin
    frac_add_1          = 1'b0;
    frac_sub_1          = 1'b0;
    frac_orig           = 1'b0;
    denorm_to_tiny_frac = 1'b0;
  end
endcase
// &CombEnd; @271
end
//Add 1 or Sub 1 constant
// &CombBeg; @273
always @( total_qt_rt_30[28])
begin
case(total_qt_rt_30[28])
  1'b0:
  begin
    frac_add1_op1[25:0] = {2'b0,24'b1};
    frac_sub1_op1[25:0] = {2'b11,{24{1'b1}}};
  end
  1'b1:
  begin
    frac_add1_op1[25:0] = {25'b1,1'b0};
    frac_sub1_op1[25:0] = {{25{1'b1}},1'b0};
  end
  default:
  begin
    frac_add1_op1[25:0] = 26'b0;
    frac_sub1_op1[25:0] = 26'b0;
  end
endcase
// &CombEnd; @291
end

//Add 1 or Sub1 final result
//Conner case when quotient is 0.010000...00 and remainder is negative,
//The real quotient is actually 0.00fff..ff,
//The final result will need to sub 1 when
//RN : Never occur
//RP : sign of quotient is -
//RM : sign of quotient is +
assign frac_add1_rst[25:0]             = {1'b0,total_qt_rt_30[28:4]} +
                                         frac_add1_op1_with_denorm[25:0];
assign frac_add1_op1_with_denorm[25:0] = ex3_rslt_denorm ?
                                  {1'b0,fdsu_ex3_result_denorm_round_add_num[23:0],1'b0} :
                                  frac_add1_op1[25:0];
assign frac_sub1_rst[25:0]             = (ex3_rst_eq_1)
                                       ? {3'b0,{23{1'b1}}}
                                       : {1'b0,total_qt_rt_30[28:4]} +
                                         frac_sub1_op1_with_denorm[25:0] + {25'b0, ex3_rslt_denorm};
assign frac_sub1_op1_with_denorm[25:0] = ex3_rslt_denorm ?
                                ~{1'b0,fdsu_ex3_result_denorm_round_add_num[23:0],1'b0} :
                                frac_sub1_op1[25:0];
assign frac_final_rst[25:0]           = (frac_add1_rst[25:0]         & {26{frac_add_1}}) |
                                        (frac_sub1_rst[25:0]         & {26{frac_sub_1}}) |
                                        ({1'b0,total_qt_rt_30[28:4]} & {26{frac_orig}});

//===============Pipe down signal prepare===================
// assign ex3_rst_nor = !fdsu_ex3_result_zero &&
//                      !fdsu_ex3_result_qnan &&
//                      !fdsu_ex3_result_inf  &&
//                      !fdsu_ex3_result_lfn;
assign ex3_rst_nor = !fdsu_ex3_result_inf  &&
                     !fdsu_ex3_result_lfn;
assign ex3_nx      = ex3_rst_nor &&
                    (!ex3_qt_zero || !fdsu_ex3_rem_zero || ex3_denorm_nx);
assign ex3_denorm_nx = ex3_rslt_denorm && (!ex3_denorm_zero ||  !fdsu_ex3_rem_zero);
//Adjust expnt
//Div:Actural expnt should plus 1 when op0 is id, sub 1 when op1 id
assign ex3_expnt_adjst[9:0] = 10'h7f;

assign ex3_expnt_adjust_result[9:0] = fdsu_ex3_expnt_rst[9:0] +
                                       ex3_expnt_adjst[9:0];
//this information is for the packing, which determin the result is normal
//numer or not;
assign ex3_potnt_norm[1:0]    = {ex3_denorm_plus,ex3_denorm_potnt_norm};
//=======================Pipe to EX4========================
//gate clk
// &Instance("gated_clk_cell","x_ex3_pipe_clk"); @337
gated_clk_cell  x_ex3_pipe_clk (
  .clk_in             (forever_cpuclk    ),
  .clk_out            (ex3_pipe_clk      ),
  .external_en        (1'b0              ),
  .global_en          (cp0_yy_clk_en     ),
  .local_en           (ex3_pipe_clk_en   ),
  .module_en          (cp0_fpu_icg_en    ),
  .pad_yy_icg_scan_en (pad_yy_icg_scan_en)
);

// &Connect( .clk_in         (forever_cpuclk), @338
//           .clk_out        (ex3_pipe_clk),//Out Clock @339
//           .external_en    (1'b0), @340
//           .global_en      (cp0_yy_clk_en), @341
//           .local_en       (ex3_pipe_clk_en),//Local Condition @342
//           .module_en      (cp0_fpu_icg_en) @343
//         ); @344
assign ex3_pipe_clk_en = ex3_pipedown;

always @(posedge ex3_pipe_clk)
begin
  if(ex3_pipedown)
  begin
    fdsu_ex4_result_nor      <= ex3_rst_nor;
    fdsu_ex4_nx              <= ex3_nx;
    fdsu_ex4_denorm_to_tiny_frac
                              <= denorm_to_tiny_frac;
    fdsu_ex4_potnt_norm[1:0] <= ex3_potnt_norm[1:0];
  end
  else
  begin
    fdsu_ex4_result_nor      <= fdsu_ex4_result_nor;
    fdsu_ex4_nx              <= fdsu_ex4_nx;
    fdsu_ex4_denorm_to_tiny_frac
                              <= fdsu_ex4_denorm_to_tiny_frac;
    fdsu_ex4_potnt_norm[1:0] <= fdsu_ex4_potnt_norm[1:0];
  end
end

// ex3_frac Pipedown to ex4 use srt_divisor.
assign ex3_frac_final_rst[25:0] = frac_final_rst[25:0];
// &Force("output","fdsu_ex4_result_nor"); @397
// &Force("output","fdsu_ex4_nx"); @398
// &Force("output","fdsu_ex4_denorm_to_tiny_frac"); @399
// &Force("output","fdsu_ex4_potnt_norm"); @400


// &ModuleEnd; @403
endmodule



