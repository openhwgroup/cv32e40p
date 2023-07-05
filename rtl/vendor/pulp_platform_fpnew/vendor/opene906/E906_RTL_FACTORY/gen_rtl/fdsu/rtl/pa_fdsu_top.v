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
module pa_fdsu_top(
  cp0_fpu_icg_en,
  cp0_fpu_xx_dqnan,
  cp0_yy_clk_en,
  cpurst_b,
  ctrl_fdsu_ex1_sel,
  ctrl_xx_ex1_cmplt_dp,
  ctrl_xx_ex1_inst_vld,
  ctrl_xx_ex1_stall,
  ctrl_xx_ex1_warm_up,
  ctrl_xx_ex2_warm_up,
  ctrl_xx_ex3_warm_up,
  dp_xx_ex1_cnan,
  dp_xx_ex1_id,
  dp_xx_ex1_inf,
  dp_xx_ex1_qnan,
  dp_xx_ex1_rm,
  dp_xx_ex1_snan,
  dp_xx_ex1_zero,
  fdsu_fpu_debug_info,
  fdsu_fpu_ex1_cmplt,
  fdsu_fpu_ex1_cmplt_dp,
  fdsu_fpu_ex1_fflags,
  fdsu_fpu_ex1_special_sel,
  fdsu_fpu_ex1_special_sign,
  fdsu_fpu_ex1_stall,
  fdsu_fpu_no_op,
  fdsu_frbus_data,
  fdsu_frbus_fflags,
  fdsu_frbus_freg,
  fdsu_frbus_wb_vld,
  forever_cpuclk,
  frbus_fdsu_wb_grant,
  idu_fpu_ex1_dst_freg,
  idu_fpu_ex1_eu_sel,
  idu_fpu_ex1_func,
  idu_fpu_ex1_srcf0,
  idu_fpu_ex1_srcf1,
  pad_yy_icg_scan_en,
  rtu_xx_ex1_cancel,
  rtu_xx_ex2_cancel,
  rtu_yy_xx_async_flush,
  rtu_yy_xx_flush
);

// &Ports; @24
input           cp0_fpu_icg_en;                      
input           cp0_fpu_xx_dqnan;                    
input           cp0_yy_clk_en;                       
input           cpurst_b;                            
input           ctrl_fdsu_ex1_sel;                   
input           ctrl_xx_ex1_cmplt_dp;                
input           ctrl_xx_ex1_inst_vld;                
input           ctrl_xx_ex1_stall;                   
input           ctrl_xx_ex1_warm_up;                 
input           ctrl_xx_ex2_warm_up;                 
input           ctrl_xx_ex3_warm_up;                 
input   [2 :0]  dp_xx_ex1_cnan;                      
input   [2 :0]  dp_xx_ex1_id;                        
input   [2 :0]  dp_xx_ex1_inf;                       
input   [2 :0]  dp_xx_ex1_qnan;                      
input   [2 :0]  dp_xx_ex1_rm;                        
input   [2 :0]  dp_xx_ex1_snan;                      
input   [2 :0]  dp_xx_ex1_zero;                      
input           forever_cpuclk;                      
input           frbus_fdsu_wb_grant;                 
input   [4 :0]  idu_fpu_ex1_dst_freg;                
input   [2 :0]  idu_fpu_ex1_eu_sel;                  
input   [9 :0]  idu_fpu_ex1_func;                    
input   [31:0]  idu_fpu_ex1_srcf0;                   
input   [31:0]  idu_fpu_ex1_srcf1;                   
input           pad_yy_icg_scan_en;                  
input           rtu_xx_ex1_cancel;                   
input           rtu_xx_ex2_cancel;                   
input           rtu_yy_xx_async_flush;               
input           rtu_yy_xx_flush;                     
output  [4 :0]  fdsu_fpu_debug_info;                 
output          fdsu_fpu_ex1_cmplt;                  
output          fdsu_fpu_ex1_cmplt_dp;               
output  [4 :0]  fdsu_fpu_ex1_fflags;                 
output  [7 :0]  fdsu_fpu_ex1_special_sel;            
output  [3 :0]  fdsu_fpu_ex1_special_sign;           
output          fdsu_fpu_ex1_stall;                  
output          fdsu_fpu_no_op;                      
output  [31:0]  fdsu_frbus_data;                     
output  [4 :0]  fdsu_frbus_fflags;                   
output  [4 :0]  fdsu_frbus_freg;                     
output          fdsu_frbus_wb_vld;                   

// &Regs; @25

// &Wires; @26
wire            cp0_fpu_icg_en;                      
wire            cp0_fpu_xx_dqnan;                    
wire            cp0_yy_clk_en;                       
wire            cpurst_b;                            
wire            ctrl_fdsu_ex1_sel;                   
wire            ctrl_xx_ex1_cmplt_dp;                
wire            ctrl_xx_ex1_inst_vld;                
wire            ctrl_xx_ex1_stall;                   
wire            ctrl_xx_ex1_warm_up;                 
wire            ctrl_xx_ex2_warm_up;                 
wire            ctrl_xx_ex3_warm_up;                 
wire    [2 :0]  dp_xx_ex1_cnan;                      
wire    [2 :0]  dp_xx_ex1_id;                        
wire    [2 :0]  dp_xx_ex1_inf;                       
wire    [2 :0]  dp_xx_ex1_qnan;                      
wire    [2 :0]  dp_xx_ex1_rm;                        
wire    [2 :0]  dp_xx_ex1_snan;                      
wire    [2 :0]  dp_xx_ex1_zero;                      
wire            ex1_div;                             
wire    [23:0]  ex1_divisor;                         
wire    [12:0]  ex1_expnt_adder_op0;                 
wire    [12:0]  ex1_expnt_adder_op1;                 
wire            ex1_of_result_lfn;                   
wire            ex1_op0_id;                          
wire            ex1_op0_norm;                        
wire            ex1_op0_sign;                        
wire            ex1_op1_id;                          
wire            ex1_op1_id_vld;                      
wire            ex1_op1_norm;                        
wire            ex1_op1_sel;                         
wire    [12:0]  ex1_oper_id_expnt;                   
wire    [12:0]  ex1_oper_id_expnt_f;                 
wire    [51:0]  ex1_oper_id_frac;                    
wire    [51:0]  ex1_oper_id_frac_f;                  
wire            ex1_pipedown;                        
wire            ex1_pipedown_gate;                   
wire    [31:0]  ex1_remainder;                       
wire            ex1_result_sign;                     
wire    [2 :0]  ex1_rm;                              
wire            ex1_save_op0;                        
wire            ex1_save_op0_gate;                   
wire            ex1_sqrt;                            
wire            ex1_srt_skip;                        
wire    [9 :0]  ex2_expnt_adder_op0;                 
wire            ex2_of;                              
wire            ex2_pipe_clk;                        
wire            ex2_pipedown;                        
wire            ex2_potnt_of;                        
wire            ex2_potnt_uf;                        
wire            ex2_result_inf;                      
wire            ex2_result_lfn;                      
wire            ex2_rslt_denorm;                     
wire    [9 :0]  ex2_srt_expnt_rst;                   
wire            ex2_srt_first_round;                 
wire            ex2_uf;                              
wire            ex2_uf_srt_skip;                     
wire    [9 :0]  ex3_expnt_adjust_result;             
wire    [25:0]  ex3_frac_final_rst;                  
wire            ex3_pipedown;                        
wire            ex3_rslt_denorm;                     
wire            fdsu_ex1_sel;                        
wire            fdsu_ex3_id_srt_skip;                
wire            fdsu_ex3_rem_sign;                   
wire            fdsu_ex3_rem_zero;                   
wire    [23:0]  fdsu_ex3_result_denorm_round_add_num; 
wire            fdsu_ex4_denorm_to_tiny_frac;        
wire    [25:0]  fdsu_ex4_frac;                       
wire            fdsu_ex4_nx;                         
wire    [1 :0]  fdsu_ex4_potnt_norm;                 
wire            fdsu_ex4_result_nor;                 
wire    [4 :0]  fdsu_fpu_debug_info;                 
wire            fdsu_fpu_ex1_cmplt;                  
wire            fdsu_fpu_ex1_cmplt_dp;               
wire    [4 :0]  fdsu_fpu_ex1_fflags;                 
wire    [7 :0]  fdsu_fpu_ex1_special_sel;            
wire    [3 :0]  fdsu_fpu_ex1_special_sign;           
wire            fdsu_fpu_ex1_stall;                  
wire            fdsu_fpu_no_op;                      
wire    [31:0]  fdsu_frbus_data;                     
wire    [4 :0]  fdsu_frbus_fflags;                   
wire    [4 :0]  fdsu_frbus_freg;                     
wire            fdsu_frbus_wb_vld;                   
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
wire            fdsu_yy_rslt_denorm;                 
wire            fdsu_yy_sqrt;                        
wire            fdsu_yy_uf;                          
wire    [4 :0]  fdsu_yy_wb_freg;                     
wire            forever_cpuclk;                      
wire            frbus_fdsu_wb_grant;                 
wire    [4 :0]  idu_fpu_ex1_dst_freg;                
wire    [2 :0]  idu_fpu_ex1_eu_sel;                  
wire    [9 :0]  idu_fpu_ex1_func;                    
wire    [31:0]  idu_fpu_ex1_srcf0;                   
wire    [31:0]  idu_fpu_ex1_srcf1;                   
wire            pad_yy_icg_scan_en;                  
wire            rtu_xx_ex1_cancel;                   
wire            rtu_xx_ex2_cancel;                   
wire            rtu_yy_xx_async_flush;               
wire            rtu_yy_xx_flush;                     
wire            srt_remainder_zero;                  
wire            srt_sm_on;                           
wire    [29:0]  total_qt_rt_30;                      



// &Instance("pa_fdsu_special"); @29
pa_fdsu_special  x_pa_fdsu_special (
  .cp0_fpu_xx_dqnan          (cp0_fpu_xx_dqnan         ),
  .dp_xx_ex1_cnan            (dp_xx_ex1_cnan           ),
  .dp_xx_ex1_id              (dp_xx_ex1_id             ),
  .dp_xx_ex1_inf             (dp_xx_ex1_inf            ),
  .dp_xx_ex1_qnan            (dp_xx_ex1_qnan           ),
  .dp_xx_ex1_snan            (dp_xx_ex1_snan           ),
  .dp_xx_ex1_zero            (dp_xx_ex1_zero           ),
  .ex1_div                   (ex1_div                  ),
  .ex1_op0_id                (ex1_op0_id               ),
  .ex1_op0_norm              (ex1_op0_norm             ),
  .ex1_op0_sign              (ex1_op0_sign             ),
  .ex1_op1_id                (ex1_op1_id               ),
  .ex1_op1_norm              (ex1_op1_norm             ),
  .ex1_result_sign           (ex1_result_sign          ),
  .ex1_sqrt                  (ex1_sqrt                 ),
  .ex1_srt_skip              (ex1_srt_skip             ),
  .fdsu_fpu_ex1_fflags       (fdsu_fpu_ex1_fflags      ),
  .fdsu_fpu_ex1_special_sel  (fdsu_fpu_ex1_special_sel ),
  .fdsu_fpu_ex1_special_sign (fdsu_fpu_ex1_special_sign)
);

// &Instance("pa_fdsu_prepare"); @30
pa_fdsu_prepare  x_pa_fdsu_prepare (
  .dp_xx_ex1_rm        (dp_xx_ex1_rm       ),
  .ex1_div             (ex1_div            ),
  .ex1_divisor         (ex1_divisor        ),
  .ex1_expnt_adder_op0 (ex1_expnt_adder_op0),
  .ex1_expnt_adder_op1 (ex1_expnt_adder_op1),
  .ex1_of_result_lfn   (ex1_of_result_lfn  ),
  .ex1_op0_id          (ex1_op0_id         ),
  .ex1_op0_sign        (ex1_op0_sign       ),
  .ex1_op1_id          (ex1_op1_id         ),
  .ex1_op1_id_vld      (ex1_op1_id_vld     ),
  .ex1_op1_sel         (ex1_op1_sel        ),
  .ex1_oper_id_expnt   (ex1_oper_id_expnt  ),
  .ex1_oper_id_expnt_f (ex1_oper_id_expnt_f),
  .ex1_oper_id_frac    (ex1_oper_id_frac   ),
  .ex1_oper_id_frac_f  (ex1_oper_id_frac_f ),
  .ex1_remainder       (ex1_remainder      ),
  .ex1_result_sign     (ex1_result_sign    ),
  .ex1_rm              (ex1_rm             ),
  .ex1_sqrt            (ex1_sqrt           ),
  .fdsu_ex1_sel        (fdsu_ex1_sel       ),
  .idu_fpu_ex1_func    (idu_fpu_ex1_func   ),
  .idu_fpu_ex1_srcf0   (idu_fpu_ex1_srcf0  ),
  .idu_fpu_ex1_srcf1   (idu_fpu_ex1_srcf1  )
);

// &Instance("pa_fdsu_srt"); @32
// &Instance("pa_fdsu_round"); @33
// &Instance("pa_fdsu_pack"); @34
// &Instance("pa_fdsu_srt_single", "x_pa_fdsu_srt"); @36
pa_fdsu_srt_single  x_pa_fdsu_srt (
  .cp0_fpu_icg_en                       (cp0_fpu_icg_en                      ),
  .cp0_yy_clk_en                        (cp0_yy_clk_en                       ),
  .ex1_divisor                          (ex1_divisor                         ),
  .ex1_expnt_adder_op1                  (ex1_expnt_adder_op1                 ),
  .ex1_oper_id_frac                     (ex1_oper_id_frac                    ),
  .ex1_oper_id_frac_f                   (ex1_oper_id_frac_f                  ),
  .ex1_pipedown                         (ex1_pipedown                        ),
  .ex1_pipedown_gate                    (ex1_pipedown_gate                   ),
  .ex1_remainder                        (ex1_remainder                       ),
  .ex1_save_op0                         (ex1_save_op0                        ),
  .ex1_save_op0_gate                    (ex1_save_op0_gate                   ),
  .ex2_expnt_adder_op0                  (ex2_expnt_adder_op0                 ),
  .ex2_of                               (ex2_of                              ),
  .ex2_pipe_clk                         (ex2_pipe_clk                        ),
  .ex2_pipedown                         (ex2_pipedown                        ),
  .ex2_potnt_of                         (ex2_potnt_of                        ),
  .ex2_potnt_uf                         (ex2_potnt_uf                        ),
  .ex2_result_inf                       (ex2_result_inf                      ),
  .ex2_result_lfn                       (ex2_result_lfn                      ),
  .ex2_rslt_denorm                      (ex2_rslt_denorm                     ),
  .ex2_srt_expnt_rst                    (ex2_srt_expnt_rst                   ),
  .ex2_srt_first_round                  (ex2_srt_first_round                 ),
  .ex2_uf                               (ex2_uf                              ),
  .ex2_uf_srt_skip                      (ex2_uf_srt_skip                     ),
  .ex3_frac_final_rst                   (ex3_frac_final_rst                  ),
  .ex3_pipedown                         (ex3_pipedown                        ),
  .fdsu_ex3_id_srt_skip                 (fdsu_ex3_id_srt_skip                ),
  .fdsu_ex3_rem_sign                    (fdsu_ex3_rem_sign                   ),
  .fdsu_ex3_rem_zero                    (fdsu_ex3_rem_zero                   ),
  .fdsu_ex3_result_denorm_round_add_num (fdsu_ex3_result_denorm_round_add_num),
  .fdsu_ex4_frac                        (fdsu_ex4_frac                       ),
  .fdsu_yy_div                          (fdsu_yy_div                         ),
  .fdsu_yy_of_rm_lfn                    (fdsu_yy_of_rm_lfn                   ),
  .fdsu_yy_op0_norm                     (fdsu_yy_op0_norm                    ),
  .fdsu_yy_op1_norm                     (fdsu_yy_op1_norm                    ),
  .fdsu_yy_sqrt                         (fdsu_yy_sqrt                        ),
  .forever_cpuclk                       (forever_cpuclk                      ),
  .pad_yy_icg_scan_en                   (pad_yy_icg_scan_en                  ),
  .srt_remainder_zero                   (srt_remainder_zero                  ),
  .srt_sm_on                            (srt_sm_on                           ),
  .total_qt_rt_30                       (total_qt_rt_30                      )
);

// &Instance("pa_fdsu_round_single", "x_pa_fdsu_round"); @37
pa_fdsu_round_single  x_pa_fdsu_round (
  .cp0_fpu_icg_en                       (cp0_fpu_icg_en                      ),
  .cp0_yy_clk_en                        (cp0_yy_clk_en                       ),
  .ex3_expnt_adjust_result              (ex3_expnt_adjust_result             ),
  .ex3_frac_final_rst                   (ex3_frac_final_rst                  ),
  .ex3_pipedown                         (ex3_pipedown                        ),
  .ex3_rslt_denorm                      (ex3_rslt_denorm                     ),
  .fdsu_ex3_id_srt_skip                 (fdsu_ex3_id_srt_skip                ),
  .fdsu_ex3_rem_sign                    (fdsu_ex3_rem_sign                   ),
  .fdsu_ex3_rem_zero                    (fdsu_ex3_rem_zero                   ),
  .fdsu_ex3_result_denorm_round_add_num (fdsu_ex3_result_denorm_round_add_num),
  .fdsu_ex4_denorm_to_tiny_frac         (fdsu_ex4_denorm_to_tiny_frac        ),
  .fdsu_ex4_nx                          (fdsu_ex4_nx                         ),
  .fdsu_ex4_potnt_norm                  (fdsu_ex4_potnt_norm                 ),
  .fdsu_ex4_result_nor                  (fdsu_ex4_result_nor                 ),
  .fdsu_yy_expnt_rst                    (fdsu_yy_expnt_rst                   ),
  .fdsu_yy_result_inf                   (fdsu_yy_result_inf                  ),
  .fdsu_yy_result_lfn                   (fdsu_yy_result_lfn                  ),
  .fdsu_yy_result_sign                  (fdsu_yy_result_sign                 ),
  .fdsu_yy_rm                           (fdsu_yy_rm                          ),
  .fdsu_yy_rslt_denorm                  (fdsu_yy_rslt_denorm                 ),
  .forever_cpuclk                       (forever_cpuclk                      ),
  .pad_yy_icg_scan_en                   (pad_yy_icg_scan_en                  ),
  .total_qt_rt_30                       (total_qt_rt_30                      )
);

// &Instance("pa_fdsu_pack_single", "x_pa_fdsu_pack"); @38
pa_fdsu_pack_single  x_pa_fdsu_pack (
  .fdsu_ex4_denorm_to_tiny_frac (fdsu_ex4_denorm_to_tiny_frac),
  .fdsu_ex4_frac                (fdsu_ex4_frac               ),
  .fdsu_ex4_nx                  (fdsu_ex4_nx                 ),
  .fdsu_ex4_potnt_norm          (fdsu_ex4_potnt_norm         ),
  .fdsu_ex4_result_nor          (fdsu_ex4_result_nor         ),
  .fdsu_frbus_data              (fdsu_frbus_data             ),
  .fdsu_frbus_fflags            (fdsu_frbus_fflags           ),
  .fdsu_frbus_freg              (fdsu_frbus_freg             ),
  .fdsu_yy_expnt_rst            (fdsu_yy_expnt_rst           ),
  .fdsu_yy_of                   (fdsu_yy_of                  ),
  .fdsu_yy_of_rm_lfn            (fdsu_yy_of_rm_lfn           ),
  .fdsu_yy_potnt_of             (fdsu_yy_potnt_of            ),
  .fdsu_yy_potnt_uf             (fdsu_yy_potnt_uf            ),
  .fdsu_yy_result_inf           (fdsu_yy_result_inf          ),
  .fdsu_yy_result_lfn           (fdsu_yy_result_lfn          ),
  .fdsu_yy_result_sign          (fdsu_yy_result_sign         ),
  .fdsu_yy_rslt_denorm          (fdsu_yy_rslt_denorm         ),
  .fdsu_yy_uf                   (fdsu_yy_uf                  ),
  .fdsu_yy_wb_freg              (fdsu_yy_wb_freg             )
);


// &Instance("pa_fdsu_ctrl"); @41
pa_fdsu_ctrl  x_pa_fdsu_ctrl (
  .cp0_fpu_icg_en          (cp0_fpu_icg_en         ),
  .cp0_yy_clk_en           (cp0_yy_clk_en          ),
  .cpurst_b                (cpurst_b               ),
  .ctrl_fdsu_ex1_sel       (ctrl_fdsu_ex1_sel      ),
  .ctrl_xx_ex1_cmplt_dp    (ctrl_xx_ex1_cmplt_dp   ),
  .ctrl_xx_ex1_inst_vld    (ctrl_xx_ex1_inst_vld   ),
  .ctrl_xx_ex1_stall       (ctrl_xx_ex1_stall      ),
  .ctrl_xx_ex1_warm_up     (ctrl_xx_ex1_warm_up    ),
  .ctrl_xx_ex2_warm_up     (ctrl_xx_ex2_warm_up    ),
  .ctrl_xx_ex3_warm_up     (ctrl_xx_ex3_warm_up    ),
  .ex1_div                 (ex1_div                ),
  .ex1_expnt_adder_op0     (ex1_expnt_adder_op0    ),
  .ex1_of_result_lfn       (ex1_of_result_lfn      ),
  .ex1_op0_id              (ex1_op0_id             ),
  .ex1_op0_norm            (ex1_op0_norm           ),
  .ex1_op1_id_vld          (ex1_op1_id_vld         ),
  .ex1_op1_norm            (ex1_op1_norm           ),
  .ex1_op1_sel             (ex1_op1_sel            ),
  .ex1_oper_id_expnt       (ex1_oper_id_expnt      ),
  .ex1_oper_id_expnt_f     (ex1_oper_id_expnt_f    ),
  .ex1_pipedown            (ex1_pipedown           ),
  .ex1_pipedown_gate       (ex1_pipedown_gate      ),
  .ex1_result_sign         (ex1_result_sign        ),
  .ex1_rm                  (ex1_rm                 ),
  .ex1_save_op0            (ex1_save_op0           ),
  .ex1_save_op0_gate       (ex1_save_op0_gate      ),
  .ex1_sqrt                (ex1_sqrt               ),
  .ex1_srt_skip            (ex1_srt_skip           ),
  .ex2_expnt_adder_op0     (ex2_expnt_adder_op0    ),
  .ex2_of                  (ex2_of                 ),
  .ex2_pipe_clk            (ex2_pipe_clk           ),
  .ex2_pipedown            (ex2_pipedown           ),
  .ex2_potnt_of            (ex2_potnt_of           ),
  .ex2_potnt_uf            (ex2_potnt_uf           ),
  .ex2_result_inf          (ex2_result_inf         ),
  .ex2_result_lfn          (ex2_result_lfn         ),
  .ex2_rslt_denorm         (ex2_rslt_denorm        ),
  .ex2_srt_expnt_rst       (ex2_srt_expnt_rst      ),
  .ex2_srt_first_round     (ex2_srt_first_round    ),
  .ex2_uf                  (ex2_uf                 ),
  .ex2_uf_srt_skip         (ex2_uf_srt_skip        ),
  .ex3_expnt_adjust_result (ex3_expnt_adjust_result),
  .ex3_pipedown            (ex3_pipedown           ),
  .ex3_rslt_denorm         (ex3_rslt_denorm        ),
  .fdsu_ex1_sel            (fdsu_ex1_sel           ),
  .fdsu_fpu_debug_info     (fdsu_fpu_debug_info    ),
  .fdsu_fpu_ex1_cmplt      (fdsu_fpu_ex1_cmplt     ),
  .fdsu_fpu_ex1_cmplt_dp   (fdsu_fpu_ex1_cmplt_dp  ),
  .fdsu_fpu_ex1_stall      (fdsu_fpu_ex1_stall     ),
  .fdsu_fpu_no_op          (fdsu_fpu_no_op         ),
  .fdsu_frbus_wb_vld       (fdsu_frbus_wb_vld      ),
  .fdsu_yy_div             (fdsu_yy_div            ),
  .fdsu_yy_expnt_rst       (fdsu_yy_expnt_rst      ),
  .fdsu_yy_of              (fdsu_yy_of             ),
  .fdsu_yy_of_rm_lfn       (fdsu_yy_of_rm_lfn      ),
  .fdsu_yy_op0_norm        (fdsu_yy_op0_norm       ),
  .fdsu_yy_op1_norm        (fdsu_yy_op1_norm       ),
  .fdsu_yy_potnt_of        (fdsu_yy_potnt_of       ),
  .fdsu_yy_potnt_uf        (fdsu_yy_potnt_uf       ),
  .fdsu_yy_result_inf      (fdsu_yy_result_inf     ),
  .fdsu_yy_result_lfn      (fdsu_yy_result_lfn     ),
  .fdsu_yy_result_sign     (fdsu_yy_result_sign    ),
  .fdsu_yy_rm              (fdsu_yy_rm             ),
  .fdsu_yy_rslt_denorm     (fdsu_yy_rslt_denorm    ),
  .fdsu_yy_sqrt            (fdsu_yy_sqrt           ),
  .fdsu_yy_uf              (fdsu_yy_uf             ),
  .fdsu_yy_wb_freg         (fdsu_yy_wb_freg        ),
  .forever_cpuclk          (forever_cpuclk         ),
  .frbus_fdsu_wb_grant     (frbus_fdsu_wb_grant    ),
  .idu_fpu_ex1_dst_freg    (idu_fpu_ex1_dst_freg   ),
  .idu_fpu_ex1_eu_sel      (idu_fpu_ex1_eu_sel     ),
  .pad_yy_icg_scan_en      (pad_yy_icg_scan_en     ),
  .rtu_xx_ex1_cancel       (rtu_xx_ex1_cancel      ),
  .rtu_xx_ex2_cancel       (rtu_xx_ex2_cancel      ),
  .rtu_yy_xx_async_flush   (rtu_yy_xx_async_flush  ),
  .rtu_yy_xx_flush         (rtu_yy_xx_flush        ),
  .srt_remainder_zero      (srt_remainder_zero     ),
  .srt_sm_on               (srt_sm_on              )
);



// &ModuleEnd; @44
endmodule


