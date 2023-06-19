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
module pa_fdsu_ctrl(
  cp0_fpu_icg_en,
  cp0_yy_clk_en,
  cpurst_b,
  ctrl_fdsu_ex1_sel,
  ctrl_xx_ex1_cmplt_dp,
  ctrl_xx_ex1_inst_vld,
  ctrl_xx_ex1_stall,
  ctrl_xx_ex1_warm_up,
  ctrl_xx_ex2_warm_up,
  ctrl_xx_ex3_warm_up,
  ex1_div,
  ex1_expnt_adder_op0,
  ex1_of_result_lfn,
  ex1_op0_id,
  ex1_op0_norm,
  ex1_op1_id_vld,
  ex1_op1_norm,
  ex1_op1_sel,
  ex1_oper_id_expnt,
  ex1_oper_id_expnt_f,
  ex1_pipedown,
  ex1_pipedown_gate,
  ex1_result_sign,
  ex1_rm,
  ex1_save_op0,
  ex1_save_op0_gate,
  ex1_sqrt,
  ex1_srt_skip,
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
  ex3_expnt_adjust_result,
  ex3_pipedown,
  ex3_rslt_denorm,
  fdsu_ex1_sel,
  fdsu_fpu_debug_info,
  fdsu_fpu_ex1_cmplt,
  fdsu_fpu_ex1_cmplt_dp,
  fdsu_fpu_ex1_stall,
  fdsu_fpu_no_op,
  fdsu_frbus_wb_vld,
  fdsu_yy_div,
  fdsu_yy_expnt_rst,
  fdsu_yy_of,
  fdsu_yy_of_rm_lfn,
  fdsu_yy_op0_norm,
  fdsu_yy_op1_norm,
  fdsu_yy_potnt_of,
  fdsu_yy_potnt_uf,
  fdsu_yy_result_inf,
  fdsu_yy_result_lfn,
  fdsu_yy_result_sign,
  fdsu_yy_rm,
  fdsu_yy_rslt_denorm,
  fdsu_yy_sqrt,
  fdsu_yy_uf,
  fdsu_yy_wb_freg,
  forever_cpuclk,
  frbus_fdsu_wb_grant,
  idu_fpu_ex1_dst_freg,
  idu_fpu_ex1_eu_sel,
  pad_yy_icg_scan_en,
  rtu_xx_ex1_cancel,
  rtu_xx_ex2_cancel,
  rtu_yy_xx_async_flush,
  rtu_yy_xx_flush,
  srt_remainder_zero,
  srt_sm_on
);

// &Ports; @24
input           cp0_fpu_icg_en;         
input           cp0_yy_clk_en;          
input           cpurst_b;               
input           ctrl_fdsu_ex1_sel;      
input           ctrl_xx_ex1_cmplt_dp;   
input           ctrl_xx_ex1_inst_vld;   
input           ctrl_xx_ex1_stall;      
input           ctrl_xx_ex1_warm_up;    
input           ctrl_xx_ex2_warm_up;    
input           ctrl_xx_ex3_warm_up;    
input           ex1_div;                
input   [12:0]  ex1_expnt_adder_op0;    
input           ex1_of_result_lfn;      
input           ex1_op0_id;             
input           ex1_op0_norm;           
input           ex1_op1_id_vld;         
input           ex1_op1_norm;           
input   [12:0]  ex1_oper_id_expnt;      
input           ex1_result_sign;        
input   [2 :0]  ex1_rm;                 
input           ex1_sqrt;               
input           ex1_srt_skip;           
input           ex2_of;                 
input           ex2_potnt_of;           
input           ex2_potnt_uf;           
input           ex2_result_inf;         
input           ex2_result_lfn;         
input           ex2_rslt_denorm;        
input   [9 :0]  ex2_srt_expnt_rst;      
input           ex2_uf;                 
input           ex2_uf_srt_skip;        
input   [9 :0]  ex3_expnt_adjust_result; 
input           ex3_rslt_denorm;        
input           forever_cpuclk;         
input           frbus_fdsu_wb_grant;    
input   [4 :0]  idu_fpu_ex1_dst_freg;   
input   [2 :0]  idu_fpu_ex1_eu_sel;     
input           pad_yy_icg_scan_en;     
input           rtu_xx_ex1_cancel;      
input           rtu_xx_ex2_cancel;      
input           rtu_yy_xx_async_flush;  
input           rtu_yy_xx_flush;        
input           srt_remainder_zero;     
output          ex1_op1_sel;            
output  [12:0]  ex1_oper_id_expnt_f;    
output          ex1_pipedown;           
output          ex1_pipedown_gate;      
output          ex1_save_op0;           
output          ex1_save_op0_gate;      
output  [9 :0]  ex2_expnt_adder_op0;    
output          ex2_pipe_clk;           
output          ex2_pipedown;           
output          ex2_srt_first_round;    
output          ex3_pipedown;           
output          fdsu_ex1_sel;           
output  [4 :0]  fdsu_fpu_debug_info;    
output          fdsu_fpu_ex1_cmplt;     
output          fdsu_fpu_ex1_cmplt_dp;  
output          fdsu_fpu_ex1_stall;     
output          fdsu_fpu_no_op;         
output          fdsu_frbus_wb_vld;      
output          fdsu_yy_div;            
output  [9 :0]  fdsu_yy_expnt_rst;      
output          fdsu_yy_of;             
output          fdsu_yy_of_rm_lfn;      
output          fdsu_yy_op0_norm;       
output          fdsu_yy_op1_norm;       
output          fdsu_yy_potnt_of;       
output          fdsu_yy_potnt_uf;       
output          fdsu_yy_result_inf;     
output          fdsu_yy_result_lfn;     
output          fdsu_yy_result_sign;    
output  [2 :0]  fdsu_yy_rm;             
output          fdsu_yy_rslt_denorm;    
output          fdsu_yy_sqrt;           
output          fdsu_yy_uf;             
output  [4 :0]  fdsu_yy_wb_freg;        
output          srt_sm_on;              

// &Regs; @25
reg             ex2_srt_first_round;    
reg     [2 :0]  fdsu_cur_state;         
reg             fdsu_div;               
reg     [9 :0]  fdsu_expnt_rst;         
reg     [2 :0]  fdsu_next_state;        
reg             fdsu_of;                
reg             fdsu_of_rm_lfn;         
reg             fdsu_potnt_of;          
reg             fdsu_potnt_uf;          
reg             fdsu_result_inf;        
reg             fdsu_result_lfn;        
reg             fdsu_result_sign;       
reg     [2 :0]  fdsu_rm;                
reg             fdsu_sqrt;              
reg             fdsu_uf;                
reg     [4 :0]  fdsu_wb_freg;           
reg             fdsu_yy_rslt_denorm;    
reg     [4 :0]  srt_cnt;                
reg     [1 :0]  wb_cur_state;           
reg     [1 :0]  wb_nxt_state;           

// &Wires; @26
wire            cp0_fpu_icg_en;         
wire            cp0_yy_clk_en;          
wire            cpurst_b;               
wire            ctrl_fdsu_ex1_sel;      
wire            ctrl_fdsu_ex1_stall;    
wire            ctrl_fdsu_wb_vld;       
wire            ctrl_iter_start;        
wire            ctrl_iter_start_gate;   
wire            ctrl_pack;              
wire            ctrl_result_vld;        
wire            ctrl_round;             
wire            ctrl_sm_cmplt;          
wire            ctrl_sm_ex1;            
wire            ctrl_sm_idle;           
wire            ctrl_sm_start;          
wire            ctrl_sm_start_gate;     
wire            ctrl_srt_idle;          
wire            ctrl_srt_itering;       
wire            ctrl_wb_idle;           
wire            ctrl_wb_sm_cmplt;       
wire            ctrl_wb_sm_ex2;         
wire            ctrl_wb_sm_idle;        
wire            ctrl_wfi2;              
wire            ctrl_wfwb;              
wire            ctrl_xx_ex1_cmplt_dp;   
wire            ctrl_xx_ex1_inst_vld;   
wire            ctrl_xx_ex1_stall;      
wire            ctrl_xx_ex1_warm_up;    
wire            ctrl_xx_ex2_warm_up;    
wire            ctrl_xx_ex3_warm_up;    
wire            ex1_div;                
wire    [12:0]  ex1_expnt_adder_op0;    
wire            ex1_of_result_lfn;      
wire            ex1_op0_id;             
wire            ex1_op1_id_vld;         
wire            ex1_op1_sel;            
wire    [12:0]  ex1_oper_id_expnt;      
wire    [12:0]  ex1_oper_id_expnt_f;    
wire            ex1_pipe_clk;           
wire            ex1_pipe_clk_en;        
wire            ex1_pipedown;           
wire            ex1_pipedown_gate;      
wire            ex1_result_sign;        
wire    [2 :0]  ex1_rm;                 
wire            ex1_save_op0;           
wire            ex1_save_op0_gate;      
wire            ex1_sqrt;               
wire            ex1_srt_skip;           
wire    [4 :0]  ex1_wb_freg;            
wire    [9 :0]  ex2_expnt_adder_op0;    
wire            ex2_of;                 
wire            ex2_pipe_clk;           
wire            ex2_pipe_clk_en;        
wire            ex2_pipedown;           
wire            ex2_potnt_of;           
wire            ex2_potnt_uf;           
wire            ex2_result_inf;         
wire            ex2_result_lfn;         
wire            ex2_rslt_denorm;        
wire    [9 :0]  ex2_srt_expnt_rst;      
wire            ex2_uf;                 
wire            ex2_uf_srt_skip;        
wire    [9 :0]  ex3_expnt_adjust_result; 
wire            ex3_pipedown;           
wire            ex3_rslt_denorm;        
wire            expnt_rst_clk;          
wire            expnt_rst_clk_en;       
wire            fdsu_busy;              
wire            fdsu_clk;               
wire            fdsu_clk_en;            
wire            fdsu_dn_stall;          
wire            fdsu_ex1_inst_vld;      
wire            fdsu_ex1_res_vld;       
wire            fdsu_ex1_sel;           
wire            fdsu_flush;             
wire    [4 :0]  fdsu_fpu_debug_info;    
wire            fdsu_fpu_ex1_cmplt;     
wire            fdsu_fpu_ex1_cmplt_dp;  
wire            fdsu_fpu_ex1_stall;     
wire            fdsu_fpu_no_op;         
wire            fdsu_frbus_wb_vld;      
wire            fdsu_op0_norm;          
wire            fdsu_op1_norm;          
wire            fdsu_wb_grant;          
wire            fdsu_yy_div;            
wire    [9 :0]  fdsu_yy_expnt_rst;      
wire            fdsu_yy_of;             
wire            fdsu_yy_of_rm_lfn;      
wire            fdsu_yy_op0_norm;       
wire            fdsu_yy_op1_norm;       
wire            fdsu_yy_potnt_of;       
wire            fdsu_yy_potnt_uf;       
wire            fdsu_yy_result_inf;     
wire            fdsu_yy_result_lfn;     
wire            fdsu_yy_result_sign;    
wire    [2 :0]  fdsu_yy_rm;             
wire            fdsu_yy_sqrt;           
wire            fdsu_yy_uf;             
wire    [4 :0]  fdsu_yy_wb_freg;        
wire            forever_cpuclk;         
wire            frbus_fdsu_wb_grant;    
wire    [4 :0]  idu_fpu_ex1_dst_freg;   
wire    [2 :0]  idu_fpu_ex1_eu_sel;     
wire            pad_yy_icg_scan_en;     
wire            rtu_xx_ex1_cancel;      
wire            rtu_xx_ex2_cancel;      
wire            rtu_yy_xx_async_flush;  
wire            rtu_yy_xx_flush;        
wire    [4 :0]  srt_cnt_ini;            
wire            srt_cnt_zero;           
wire            srt_last_round;         
wire            srt_remainder_zero;     
wire            srt_skip;               
wire            srt_sm_on;              


//==========================================================
//                       Input Signal
//==========================================================
assign ex1_wb_freg[4:0] = idu_fpu_ex1_dst_freg[4:0];
assign fdsu_ex1_inst_vld = ctrl_xx_ex1_inst_vld && ctrl_fdsu_ex1_sel;
assign fdsu_ex1_sel      = idu_fpu_ex1_eu_sel[2];
// &Force("input", "idu_fpu_ex1_eu_sel"); &Force("bus", "idu_fpu_ex1_eu_sel", 2, 0); @34

//==========================================================
//                 FDSU Main State Machine
//==========================================================
assign fdsu_ex1_res_vld  = fdsu_ex1_inst_vld && ex1_srt_skip;
assign fdsu_wb_grant = frbus_fdsu_wb_grant;

assign ctrl_iter_start = ctrl_sm_start && !fdsu_dn_stall
                      || ctrl_wfi2;
assign ctrl_iter_start_gate = ctrl_sm_start_gate && !fdsu_dn_stall
                           || ctrl_wfi2;
assign ctrl_sm_start = fdsu_ex1_inst_vld && ctrl_srt_idle
                   && !ex1_srt_skip;
assign ctrl_sm_start_gate = fdsu_ex1_inst_vld && ctrl_srt_idle;

assign srt_last_round = (srt_skip ||
                         srt_remainder_zero ||
                         srt_cnt_zero)      &&
                         ctrl_srt_itering;
assign srt_skip       =  ex2_of ||
                         ex2_uf_srt_skip;
assign srt_cnt_zero   = ~|srt_cnt[4:0];
assign fdsu_dn_stall  = ctrl_sm_start && ex1_op1_id_vld;

parameter IDLE  = 3'b000;
parameter WFI2  = 3'b001;
parameter ITER  = 3'b010;
parameter RND   = 3'b011;
parameter PACK  = 3'b100;
parameter WFWB  = 3'b101;

always @ (posedge fdsu_clk or negedge cpurst_b)
begin
  if (!cpurst_b)
    fdsu_cur_state[2:0] <= IDLE;
  else if (fdsu_flush)
    fdsu_cur_state[2:0] <= IDLE;
  else
    fdsu_cur_state[2:0] <= fdsu_next_state[2:0];
end

// &CombBeg; @76
always @( ctrl_sm_start
       or fdsu_dn_stall
       or srt_last_round
       or fdsu_cur_state[2:0]
       or fdsu_wb_grant)
begin
case (fdsu_cur_state[2:0])
  IDLE:
  begin
    if (ctrl_sm_start)
      if (fdsu_dn_stall)
        fdsu_next_state[2:0] = WFI2;
      else
        fdsu_next_state[2:0] = ITER;
    else
      fdsu_next_state[2:0] = IDLE;
  end
  WFI2:
    fdsu_next_state[2:0] = ITER;
  ITER:
  begin
    if (srt_last_round)
      fdsu_next_state[2:0] = RND;
    else
      fdsu_next_state[2:0] = ITER;
  end
  RND:
    fdsu_next_state[2:0] = PACK;
  PACK:
  begin
    if (fdsu_wb_grant)
      if (ctrl_sm_start)
        if (fdsu_dn_stall)
          fdsu_next_state[2:0] = WFI2;
        else
          fdsu_next_state[2:0] = ITER;
      else
        fdsu_next_state[2:0] = IDLE;
    else
      fdsu_next_state[2:0] = WFWB;
  end
  WFWB:
  begin
    if (fdsu_wb_grant)
      if (ctrl_sm_start)
        if (fdsu_dn_stall)
          fdsu_next_state[2:0] = WFI2;
        else
          fdsu_next_state[2:0] = ITER;
      else
        fdsu_next_state[2:0] = IDLE;
    else
      fdsu_next_state[2:0] = WFWB;
  end
  default:
    fdsu_next_state[2:0] = IDLE;
endcase
// &CombEnd; @128
end

assign ctrl_sm_idle     = fdsu_cur_state[2:0] == IDLE;
assign ctrl_wfi2        = fdsu_cur_state[2:0] == WFI2;
assign ctrl_srt_itering = fdsu_cur_state[2:0] == ITER;
assign ctrl_round       = fdsu_cur_state[2:0] == RND;
assign ctrl_pack        = fdsu_cur_state[2:0] == PACK;
assign ctrl_wfwb        = fdsu_cur_state[2:0] == WFWB;

assign ctrl_sm_cmplt    = ctrl_pack || ctrl_wfwb;
assign ctrl_srt_idle     = ctrl_sm_idle
                       || fdsu_wb_grant;
assign ctrl_sm_ex1      = ctrl_srt_idle || ctrl_wfi2;

//==========================================================
//                    Iteration Counter
//==========================================================
always @ (posedge fdsu_clk)
begin
  if (fdsu_flush)
    srt_cnt[4:0] <= 5'b0;
  else if (ctrl_iter_start)
    srt_cnt[4:0] <= srt_cnt_ini[4:0];
  else if (ctrl_srt_itering)
    srt_cnt[4:0] <= srt_cnt[4:0] - 5'b1;
  else
    srt_cnt[4:0] <= srt_cnt[4:0];
end

//srt_cnt_ini[4:0]
//For Double, initial is 5'b11100('d28), calculate 29 round
//For Single, initial is 5'b01110('d14), calculate 15 round
assign srt_cnt_ini[4:0] = 5'b01110;

//fdsu srt first round signal 
//For srt calculate special use
always @(posedge fdsu_clk or negedge cpurst_b)
begin
  if(!cpurst_b)
    ex2_srt_first_round <= 1'b0;
  else if(fdsu_flush)
    ex2_srt_first_round <= 1'b0;
  else if(ex1_pipedown)
    ex2_srt_first_round <= 1'b1;
  else
    ex2_srt_first_round <= 1'b0;
end

//==========================================================
//                 Write Back State Machine
//==========================================================
parameter WB_IDLE  = 2'b00,
          WB_EX2   = 2'b10,
          WB_CMPLT = 2'b01;

always @ (posedge fdsu_clk or negedge cpurst_b)
begin
  if (!cpurst_b)
    wb_cur_state[1:0] <= WB_IDLE;
  else if (fdsu_flush)
    wb_cur_state[1:0] <= WB_IDLE;
  else
    wb_cur_state[1:0] <= wb_nxt_state[1:0];
end

// &CombBeg; @215
always @( ctrl_fdsu_wb_vld
       or fdsu_dn_stall
       or ctrl_xx_ex1_stall
       or fdsu_ex1_inst_vld
       or ctrl_iter_start
       or fdsu_ex1_res_vld
       or wb_cur_state[1:0])
begin
  case(wb_cur_state[1:0])
    WB_IDLE:
      if (fdsu_ex1_inst_vld)
        if (ctrl_xx_ex1_stall || fdsu_ex1_res_vld || fdsu_dn_stall)
          wb_nxt_state[1:0] = WB_IDLE;
        else
          wb_nxt_state[1:0] = WB_EX2;
      else
        wb_nxt_state[1:0] = WB_IDLE;
    WB_EX2:
      // if (ctrl_xx_ex2_stall)
      //   wb_nxt_state[1:0] = WB_EX2;
      // else
        if (ctrl_fdsu_wb_vld)
          if (ctrl_iter_start && !ctrl_xx_ex1_stall)
            wb_nxt_state[1:0] = WB_EX2;
          else
            wb_nxt_state[1:0] = WB_IDLE;
        else
          wb_nxt_state[1:0] = WB_CMPLT;
    WB_CMPLT:
      if (ctrl_fdsu_wb_vld)
        if (ctrl_iter_start && !ctrl_xx_ex1_stall)
          wb_nxt_state[1:0] = WB_EX2;
        else
          wb_nxt_state[1:0] = WB_IDLE;
      else
        wb_nxt_state[1:0] = WB_CMPLT;
    default:
      wb_nxt_state[1:0] = WB_IDLE;
  endcase
// &CombEnd; @247
end

assign ctrl_wb_idle  = wb_cur_state[1:0] == WB_IDLE
                       || wb_cur_state[1:0] == WB_CMPLT && ctrl_fdsu_wb_vld;
assign ctrl_wb_sm_idle  = wb_cur_state[1:0] == WB_IDLE;
assign ctrl_wb_sm_ex2   = wb_cur_state[1:0] == WB_EX2;
assign ctrl_wb_sm_cmplt = wb_cur_state[1:0] == WB_EX2
                       || wb_cur_state[1:0] == WB_CMPLT;

assign ctrl_result_vld  = ctrl_sm_cmplt && ctrl_wb_sm_cmplt;
assign ctrl_fdsu_wb_vld = ctrl_result_vld && frbus_fdsu_wb_grant;

assign ctrl_fdsu_ex1_stall = fdsu_ex1_inst_vld && !ctrl_sm_ex1 && !ctrl_wb_idle
                          || fdsu_ex1_inst_vld && fdsu_dn_stall;

//==========================================================
//                          Flops
//==========================================================
always @(posedge ex1_pipe_clk)
begin
  if(ex1_pipedown)
  begin
    fdsu_wb_freg[4:0]    <= ex1_wb_freg[4:0];
    fdsu_result_sign     <= ex1_result_sign;
    fdsu_of_rm_lfn       <= ex1_of_result_lfn;
    fdsu_div             <= ex1_div;
    fdsu_sqrt            <= ex1_sqrt;
    fdsu_rm[2:0]         <= ex1_rm[2:0];
  end
  else
  begin
    fdsu_wb_freg[4:0]    <= fdsu_wb_freg[4:0];
    fdsu_result_sign     <= fdsu_result_sign;
    fdsu_of_rm_lfn       <= fdsu_of_rm_lfn;
    fdsu_div             <= fdsu_div;
    fdsu_sqrt            <= fdsu_sqrt;
    fdsu_rm[2:0]         <= fdsu_rm[2:0];
  end
end

// In 906 FDSU, if one op0/1 is not norm, it will not enter EX2.
assign fdsu_op0_norm = 1'b1;
assign fdsu_op1_norm = 1'b1;
// &Force("input", "ex1_op0_norm"); @337
// &Force("input", "ex1_op1_norm"); @338

// fdsu_expnt_rst is used to save:
//  1. op0 denormal expnt;
//  2. op0 expnt;
//  3. result expnt.
// &Force("bus", "ex1_oper_id_expnt", 12, 0); @378
// &Force("bus", "ex1_expnt_adder_op0", 12, 0); @379


always @ (posedge expnt_rst_clk)
begin
  if (ex1_save_op0)
    fdsu_expnt_rst[9:0] <= ex1_oper_id_expnt[9:0];
  else if (ex1_pipedown)
    fdsu_expnt_rst[9:0] <= ex1_expnt_adder_op0[9:0];
  else if (ex2_pipedown)
    fdsu_expnt_rst[9:0] <= ex2_srt_expnt_rst[9:0];
  else if (ex3_pipedown)
    fdsu_expnt_rst[9:0] <= ex3_expnt_adjust_result[9:0];
  else
    fdsu_expnt_rst[9:0] <= fdsu_expnt_rst[9:0];
end

assign ex1_oper_id_expnt_f[12:0] = {3'b1, fdsu_expnt_rst[9:0]};

always @ (posedge expnt_rst_clk)
begin
  if (ex2_pipedown)
    fdsu_yy_rslt_denorm <= ex2_rslt_denorm;
  else if (ex3_pipedown)
    fdsu_yy_rslt_denorm <= ex3_rslt_denorm;
  else
    fdsu_yy_rslt_denorm <= fdsu_yy_rslt_denorm;
end
// &Force("output", "fdsu_yy_rslt_denorm"); @440

// EX2 signal used in EX3 & EX4
always @ (posedge ex2_pipe_clk)
begin
  if (ex2_pipedown)
  begin
    fdsu_result_inf <= ex2_result_inf;
    fdsu_result_lfn <= ex2_result_lfn;
    fdsu_of         <= ex2_of;
    fdsu_uf         <= ex2_uf;
    fdsu_potnt_of   <= ex2_potnt_of;
    fdsu_potnt_uf   <= ex2_potnt_uf;
  end
  else
  begin
    fdsu_result_inf <= fdsu_result_inf;
    fdsu_result_lfn <= fdsu_result_lfn;
    fdsu_of         <= fdsu_of;
    fdsu_uf         <= fdsu_uf;
    fdsu_potnt_of   <= fdsu_potnt_of;
    fdsu_potnt_uf   <= fdsu_potnt_uf;
  end
end

//==========================================================
//                          Flush
//==========================================================
assign fdsu_flush = rtu_xx_ex1_cancel && ctrl_wb_idle
                 || rtu_xx_ex2_cancel && ctrl_wb_sm_ex2
                 || ctrl_xx_ex1_warm_up
                 || rtu_yy_xx_async_flush;

//==========================================================
//                           ICG
//==========================================================
assign fdsu_busy = fdsu_ex1_inst_vld
                || !ctrl_sm_idle
                || !ctrl_wb_sm_idle;
assign fdsu_clk_en = fdsu_busy
                  || !ctrl_sm_idle
                  || rtu_yy_xx_flush;
// &Instance("gated_clk_cell", "x_fdsu_clk"); @514
gated_clk_cell  x_fdsu_clk (
  .clk_in             (forever_cpuclk    ),
  .clk_out            (fdsu_clk          ),
  .external_en        (1'b0              ),
  .global_en          (cp0_yy_clk_en     ),
  .local_en           (fdsu_clk_en       ),
  .module_en          (cp0_fpu_icg_en    ),
  .pad_yy_icg_scan_en (pad_yy_icg_scan_en)
);

// &Connect(.clk_in      (forever_cpuclk), @515
//          .external_en (1'b0), @516
//          .global_en   (cp0_yy_clk_en), @517
//          .module_en   (cp0_fpu_icg_en), @518
//          .local_en    (fdsu_clk_en), @519
//          .clk_out     (fdsu_clk)); @520

assign ex1_pipe_clk_en = ex1_pipedown_gate;
// &Instance("gated_clk_cell","x_ex1_pipe_clk"); @523
gated_clk_cell  x_ex1_pipe_clk (
  .clk_in             (forever_cpuclk    ),
  .clk_out            (ex1_pipe_clk      ),
  .external_en        (1'b0              ),
  .global_en          (cp0_yy_clk_en     ),
  .local_en           (ex1_pipe_clk_en   ),
  .module_en          (cp0_fpu_icg_en    ),
  .pad_yy_icg_scan_en (pad_yy_icg_scan_en)
);

// &Connect( .clk_in         (forever_cpuclk), @524
//           .clk_out        (ex1_pipe_clk),//Out Clock @525
//           .external_en    (1'b0), @526
//           .global_en      (cp0_yy_clk_en), @527
//           .local_en       (ex1_pipe_clk_en),//Local Condition @528
//           .module_en      (cp0_fpu_icg_en) @529
//         ); @530

assign ex2_pipe_clk_en = ex2_pipedown;
// &Instance("gated_clk_cell","x_ex2_pipe_clk"); @533
gated_clk_cell  x_ex2_pipe_clk (
  .clk_in             (forever_cpuclk    ),
  .clk_out            (ex2_pipe_clk      ),
  .external_en        (1'b0              ),
  .global_en          (cp0_yy_clk_en     ),
  .local_en           (ex2_pipe_clk_en   ),
  .module_en          (cp0_fpu_icg_en    ),
  .pad_yy_icg_scan_en (pad_yy_icg_scan_en)
);

// &Connect( .clk_in         (forever_cpuclk), @534
//           .clk_out        (ex2_pipe_clk),//Out Clock @535
//           .external_en    (1'b0), @536
//           .global_en      (cp0_yy_clk_en), @537
//           .local_en       (ex2_pipe_clk_en),//Local Condition @538
//           .module_en      (cp0_fpu_icg_en) @539
//         ); @540
// &Force("output", "ex2_pipe_clk"); @541

assign expnt_rst_clk_en = ex1_save_op0_gate
                       || ex1_pipedown_gate
                       || ex2_pipedown
                       || ex3_pipedown;
// &Instance("gated_clk_cell", "x_expnt_rst_clk"); @547
gated_clk_cell  x_expnt_rst_clk (
  .clk_in             (forever_cpuclk    ),
  .clk_out            (expnt_rst_clk     ),
  .external_en        (1'b0              ),
  .global_en          (cp0_yy_clk_en     ),
  .local_en           (expnt_rst_clk_en  ),
  .module_en          (cp0_fpu_icg_en    ),
  .pad_yy_icg_scan_en (pad_yy_icg_scan_en)
);

// &Connect(.clk_in      (forever_cpuclk), @548
//          .external_en (1'b0), @549
//          .global_en   (cp0_yy_clk_en), @550
//          .module_en   (cp0_fpu_icg_en), @551
//          .local_en    (expnt_rst_clk_en), @552
//          .clk_out     (expnt_rst_clk)); @553

//==========================================================
//                      Output Signal
//==========================================================
assign fdsu_yy_wb_freg[4:0]    = fdsu_wb_freg[4:0];
assign fdsu_yy_result_sign     = fdsu_result_sign;
assign fdsu_yy_op0_norm        = fdsu_op0_norm;
assign fdsu_yy_op1_norm        = fdsu_op1_norm;
assign fdsu_yy_of_rm_lfn       = fdsu_of_rm_lfn;
assign fdsu_yy_div             = fdsu_div;
assign fdsu_yy_sqrt            = fdsu_sqrt;
assign fdsu_yy_rm[2:0]         = fdsu_rm[2:0];

assign fdsu_yy_expnt_rst[9:0] = fdsu_expnt_rst[9:0];
assign ex2_expnt_adder_op0[9:0] = fdsu_expnt_rst[9:0];

assign fdsu_yy_result_inf = fdsu_result_inf;
assign fdsu_yy_result_lfn = fdsu_result_lfn;
assign fdsu_yy_of         = fdsu_of;
assign fdsu_yy_uf         = fdsu_uf;
assign fdsu_yy_potnt_of   = fdsu_potnt_of;
assign fdsu_yy_potnt_uf   = fdsu_potnt_uf;

assign ex1_pipedown = ctrl_iter_start || ctrl_xx_ex1_warm_up;
assign ex1_pipedown_gate = ctrl_iter_start_gate || ctrl_xx_ex1_warm_up;
assign ex2_pipedown = ctrl_srt_itering && srt_last_round || ctrl_xx_ex2_warm_up;
assign ex3_pipedown = ctrl_round || ctrl_xx_ex3_warm_up;
// &Force("output", "ex1_pipedown"); @589
// &Force("output", "ex1_pipedown_gate"); @590
// &Force("output", "ex2_pipedown"); @591
// &Force("output", "ex3_pipedown"); @592

assign srt_sm_on = ctrl_srt_itering;

assign fdsu_fpu_ex1_cmplt = fdsu_ex1_inst_vld;
assign fdsu_fpu_ex1_cmplt_dp =  ctrl_xx_ex1_cmplt_dp && idu_fpu_ex1_eu_sel[2];
assign fdsu_fpu_ex1_stall = ctrl_fdsu_ex1_stall;
assign fdsu_frbus_wb_vld  = ctrl_result_vld;
// &Force("bus","idu_fpu_ex1_eu_sel",2,0); @600
assign fdsu_fpu_no_op = !fdsu_busy;
assign ex1_op1_sel = ctrl_wfi2;
assign ex1_save_op0 = ctrl_sm_start && ex1_op0_id && ex1_op1_id_vld;
assign ex1_save_op0_gate = ctrl_sm_start_gate && ex1_op0_id && ex1_op1_id_vld;
// &Force("output", "ex1_save_op0"); @605
// &Force("output", "ex1_save_op0_gate"); @606

assign fdsu_fpu_debug_info[4:0] = {wb_cur_state[1:0], fdsu_cur_state[2:0]};

// &ModuleEnd; @610
endmodule



