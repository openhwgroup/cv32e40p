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

module pa_fpu_dp(
  cp0_fpu_icg_en,
  cp0_fpu_xx_rm,
  cp0_yy_clk_en,
  ctrl_xx_ex1_inst_vld,
  ctrl_xx_ex1_stall,
  ctrl_xx_ex1_warm_up,
  dp_frbus_ex2_data,
  dp_frbus_ex2_fflags,
  dp_xx_ex1_cnan,
  dp_xx_ex1_id,
  dp_xx_ex1_inf,
  dp_xx_ex1_norm,
  dp_xx_ex1_qnan,
  dp_xx_ex1_snan,
  dp_xx_ex1_zero,
  ex2_inst_wb,
  fdsu_fpu_ex1_fflags,
  fdsu_fpu_ex1_special_sel,
  fdsu_fpu_ex1_special_sign,
  forever_cpuclk,
  idu_fpu_ex1_eu_sel,
  idu_fpu_ex1_func,
  idu_fpu_ex1_gateclk_vld,
  idu_fpu_ex1_rm,
  idu_fpu_ex1_srcf0,
  idu_fpu_ex1_srcf1,
  idu_fpu_ex1_srcf2,
  pad_yy_icg_scan_en
);

input           cp0_fpu_icg_en;             
input   [2 :0]  cp0_fpu_xx_rm;              
input           cp0_yy_clk_en;              
input           ctrl_xx_ex1_inst_vld;       
input           ctrl_xx_ex1_stall;          
input           ctrl_xx_ex1_warm_up;
input   [4 :0]  fdsu_fpu_ex1_fflags;        
input   [7 :0]  fdsu_fpu_ex1_special_sel;   
input   [3 :0]  fdsu_fpu_ex1_special_sign;
input           forever_cpuclk;
input   [2 :0]  idu_fpu_ex1_eu_sel;         
input   [9 :0]  idu_fpu_ex1_func;           
input           idu_fpu_ex1_gateclk_vld;    
input   [2 :0]  idu_fpu_ex1_rm;             
input   [31:0]  idu_fpu_ex1_srcf0;          
input   [31:0]  idu_fpu_ex1_srcf1;          
input   [31:0]  idu_fpu_ex1_srcf2;          
input           pad_yy_icg_scan_en;         
output  [31:0]  dp_frbus_ex2_data;          
output  [4 :0]  dp_frbus_ex2_fflags;
output  [2 :0]  dp_xx_ex1_cnan;             
output  [2 :0]  dp_xx_ex1_id;               
output  [2 :0]  dp_xx_ex1_inf;              
output  [2 :0]  dp_xx_ex1_norm;             
output  [2 :0]  dp_xx_ex1_qnan;
output  [2 :0]  dp_xx_ex1_snan;
output  [2 :0]  dp_xx_ex1_zero;
output          ex2_inst_wb;                

reg     [4 :0]  ex1_fflags;                 
reg     [31:0]  ex1_special_data;           
reg     [8 :0]  ex1_special_sel;            
reg     [3 :0]  ex1_special_sign;           
reg     [4 :0]  ex2_fflags;
reg     [31:0]  ex2_result;
reg     [31:0]  ex2_special_data;           
reg     [6 :0]  ex2_special_sel;            
reg     [3 :0]  ex2_special_sign;

wire            cp0_fpu_icg_en;             
wire    [2 :0]  cp0_fpu_xx_rm;              
wire            cp0_yy_clk_en;              
wire            ctrl_xx_ex1_inst_vld;       
wire            ctrl_xx_ex1_stall;          
wire            ctrl_xx_ex1_warm_up;
wire    [31:0]  dp_frbus_ex2_data;          
wire    [4 :0]  dp_frbus_ex2_fflags;
wire    [2 :0]  dp_xx_ex1_cnan;             
wire    [2 :0]  dp_xx_ex1_id;               
wire    [2 :0]  dp_xx_ex1_inf;              
wire    [2 :0]  dp_xx_ex1_norm;             
wire    [2 :0]  dp_xx_ex1_qnan;
wire    [2 :0]  dp_xx_ex1_snan;
wire    [2 :0]  dp_xx_ex1_zero;
wire    [2 :0]  ex1_decode_rm;              
wire            ex1_double;                 
wire    [2 :0]  ex1_eu_sel;
wire    [9 :0]  ex1_func;                   
wire    [2 :0]  ex1_global_rm;              
wire    [2 :0]  ex1_rm;                     
wire            ex1_single;                 
wire    [31:0]  ex1_special_data_final;     
wire    [63:0]  ex1_src0;                   
wire    [63:0]  ex1_src1;                   
wire    [63:0]  ex1_src2;                   
wire            ex1_src2_vld;               
wire    [2 :0]  ex1_src_cnan;               
wire    [2 :0]  ex1_src_id;                 
wire    [2 :0]  ex1_src_inf;                
wire    [2 :0]  ex1_src_norm;               
wire    [2 :0]  ex1_src_qnan;               
wire    [2 :0]  ex1_src_snan;               
wire    [2 :0]  ex1_src_zero;               
wire            ex2_data_clk;               
wire            ex2_data_clk_en;            
wire            ex2_inst_wb;
wire    [4 :0]  fdsu_fpu_ex1_fflags;        
wire    [7 :0]  fdsu_fpu_ex1_special_sel;   
wire    [3 :0]  fdsu_fpu_ex1_special_sign;
wire            forever_cpuclk;
wire    [2 :0]  idu_fpu_ex1_eu_sel;         
wire    [9 :0]  idu_fpu_ex1_func;           
wire            idu_fpu_ex1_gateclk_vld;    
wire    [2 :0]  idu_fpu_ex1_rm;             
wire    [31:0]  idu_fpu_ex1_srcf0;          
wire    [31:0]  idu_fpu_ex1_srcf1;          
wire    [31:0]  idu_fpu_ex1_srcf2;          
wire            pad_yy_icg_scan_en;         


parameter DOUBLE_WIDTH =64;
parameter SINGLE_WIDTH =32;
parameter FUNC_WIDTH   =10;
//==========================================================
//                     EX1 special data path
//==========================================================
assign ex1_eu_sel[2:0]            = idu_fpu_ex1_eu_sel[2:0];  //3'h4
assign ex1_func[FUNC_WIDTH-1:0]   = idu_fpu_ex1_func[FUNC_WIDTH-1:0];
assign ex1_global_rm[2:0]         = cp0_fpu_xx_rm[2:0];
assign ex1_decode_rm[2:0]         = idu_fpu_ex1_rm[2:0];

assign ex1_rm[2:0]                = (ex1_decode_rm[2:0]==3'b111) 
                                  ?  ex1_global_rm[2:0] : ex1_decode_rm[2:0]; 

assign ex1_src2_vld               = idu_fpu_ex1_eu_sel[1] && ex1_func[0];

assign ex1_src0[DOUBLE_WIDTH-1:0] = { {SINGLE_WIDTH{1'b1}},idu_fpu_ex1_srcf0[SINGLE_WIDTH-1:0]};
assign ex1_src1[DOUBLE_WIDTH-1:0] = { {SINGLE_WIDTH{1'b1}},idu_fpu_ex1_srcf1[SINGLE_WIDTH-1:0]};
assign ex1_src2[DOUBLE_WIDTH-1:0] = ex1_src2_vld ? { {SINGLE_WIDTH{1'b1}},idu_fpu_ex1_srcf2[SINGLE_WIDTH-1:0]}
                                                 : { {SINGLE_WIDTH{1'b1}},{SINGLE_WIDTH{1'b0}} };

assign ex1_double = 1'b0;
assign ex1_single = 1'b1;

//==========================================================
//                EX1 special src data judge
//==========================================================
pa_fpu_src_type  x_pa_fpu_ex1_srcf0_type (
  .inst_double     (ex1_double     ),
  .inst_single     (ex1_single     ),
  .src_cnan        (ex1_src_cnan[0]),
  .src_id          (ex1_src_id[0]  ),
  .src_in          (ex1_src0       ),
  .src_inf         (ex1_src_inf[0] ),
  .src_norm        (ex1_src_norm[0]),
  .src_qnan        (ex1_src_qnan[0]),
  .src_snan        (ex1_src_snan[0]),
  .src_zero        (ex1_src_zero[0])
);

pa_fpu_src_type  x_pa_fpu_ex1_srcf1_type (
  .inst_double     (ex1_double     ),
  .inst_single     (ex1_single     ),
  .src_cnan        (ex1_src_cnan[1]),
  .src_id          (ex1_src_id[1]  ),
  .src_in          (ex1_src1       ),
  .src_inf         (ex1_src_inf[1] ),
  .src_norm        (ex1_src_norm[1]),
  .src_qnan        (ex1_src_qnan[1]),
  .src_snan        (ex1_src_snan[1]),
  .src_zero        (ex1_src_zero[1])
);

pa_fpu_src_type  x_pa_fpu_ex1_srcf2_type (
  .inst_double     (ex1_double     ),
  .inst_single     (ex1_single     ),
  .src_cnan        (ex1_src_cnan[2]),
  .src_id          (ex1_src_id[2]  ),
  .src_in          (ex1_src2       ),
  .src_inf         (ex1_src_inf[2] ),
  .src_norm        (ex1_src_norm[2]),
  .src_qnan        (ex1_src_qnan[2]),
  .src_snan        (ex1_src_snan[2]),
  .src_zero        (ex1_src_zero[2])
);

assign dp_xx_ex1_cnan[2:0] = ex1_src_cnan[2:0];
assign dp_xx_ex1_snan[2:0] = ex1_src_snan[2:0];
assign dp_xx_ex1_qnan[2:0] = ex1_src_qnan[2:0];
assign dp_xx_ex1_norm[2:0] = ex1_src_norm[2:0];
assign dp_xx_ex1_zero[2:0] = ex1_src_zero[2:0];
assign dp_xx_ex1_inf[2:0]  = ex1_src_inf[2:0];
assign dp_xx_ex1_id[2:0]   = ex1_src_id[2:0];

//==========================================================
//                EX1 special result judge
//==========================================================

always @( fdsu_fpu_ex1_special_sign[3:0]
       or fdsu_fpu_ex1_fflags[4:0]
       or ex1_eu_sel[2:0]
       or fdsu_fpu_ex1_special_sel[7:0])
begin
case(ex1_eu_sel[2:0])  //3'h4
   3'b100: begin//FDSU
         ex1_fflags[4:0]       = fdsu_fpu_ex1_fflags[4:0];
         ex1_special_sel[8:0]  ={1'b0,fdsu_fpu_ex1_special_sel[7:0]};
         ex1_special_sign[3:0] = fdsu_fpu_ex1_special_sign[3:0];
         end
default: begin//FDSU
         ex1_fflags[4:0]       = {5{1'b0}};
         ex1_special_sel[8:0]  = {9{1'b0}};
         ex1_special_sign[3:0] = {4{1'b0}};
         end
endcase
end

always @( ex1_special_sel[8:5]
       or ex1_src0[31:0]
       or ex1_src1[31:0]
       or ex1_src2[31:0])
begin
case(ex1_special_sel[8:5])
  4'b0001: ex1_special_data[SINGLE_WIDTH-1:0] = ex1_src0[SINGLE_WIDTH-1:0];
  4'b0010: ex1_special_data[SINGLE_WIDTH-1:0] = ex1_src1[SINGLE_WIDTH-1:0];
  4'b0100: ex1_special_data[SINGLE_WIDTH-1:0] = ex1_src2[SINGLE_WIDTH-1:0];
default  : ex1_special_data[SINGLE_WIDTH-1:0] = ex1_src2[SINGLE_WIDTH-1:0];
endcase
end

assign ex1_special_data_final[SINGLE_WIDTH-1:0] = ex1_special_data[SINGLE_WIDTH-1:0];

//==========================================================
//                     EX1-EX2 data pipedown
//==========================================================
assign ex2_data_clk_en = idu_fpu_ex1_gateclk_vld || ctrl_xx_ex1_warm_up;

gated_clk_cell  x_fpu_data_ex2_gated_clk (
  .clk_in             (forever_cpuclk    ),
  .clk_out            (ex2_data_clk      ),
  .external_en        (1'b0              ),
  .global_en          (cp0_yy_clk_en     ),
  .local_en           (ex2_data_clk_en   ),
  .module_en          (cp0_fpu_icg_en    ),
  .pad_yy_icg_scan_en (pad_yy_icg_scan_en)
);

always @(posedge ex2_data_clk)
begin
  if(ctrl_xx_ex1_inst_vld && !ctrl_xx_ex1_stall || ctrl_xx_ex1_warm_up)
  begin
    ex2_fflags[4:0]       <= ex1_fflags[4:0];
    ex2_special_sign[3:0] <= ex1_special_sign[3:0];
    ex2_special_sel[6:0]  <={ex1_special_sel[8],|ex1_special_sel[7:5],ex1_special_sel[4:0]};
    ex2_special_data[SINGLE_WIDTH-1:0] <= ex1_special_data_final[SINGLE_WIDTH-1:0];
  end
end

assign ex2_inst_wb = (|ex2_special_sel[6:0]);

always @( ex2_special_sel[6:0]
       or ex2_special_data[31:0]
       or ex2_special_sign[3:0])
begin
case(ex2_special_sel[6:0])
  7'b0000_001: ex2_result[SINGLE_WIDTH-1:0]  = { ex2_special_sign[0],ex2_special_data[SINGLE_WIDTH-2:0]};//src2
  7'b0000_010: ex2_result[SINGLE_WIDTH-1:0]  = { ex2_special_sign[1], {31{1'b0}} };//zero
  7'b0000_100: ex2_result[SINGLE_WIDTH-1:0]  = { ex2_special_sign[2], {8{1'b1}},{23{1'b0}} };//inf
  7'b0001_000: ex2_result[SINGLE_WIDTH-1:0]  = { ex2_special_sign[3], {7{1'b1}},1'b0,{23{1'b1}} };//lfn
  7'b0010_000: ex2_result[SINGLE_WIDTH-1:0]  = { 1'b0, {8{1'b1}},1'b1, {22{1'b0}} };//cnan
  7'b0100_000: ex2_result[SINGLE_WIDTH-1:0]  = { ex2_special_data[31],{8{1'b1}}, 1'b1, ex2_special_data[21:0]};//propagate qnan
  7'b1000_000: ex2_result[SINGLE_WIDTH-1:0]  = ex2_special_data[SINGLE_WIDTH-1:0]; //ex1 falu special result
      default: ex2_result[SINGLE_WIDTH-1:0]  = {SINGLE_WIDTH{1'b0}};
endcase
end

assign dp_frbus_ex2_data[SINGLE_WIDTH-1:0]  = ex2_result[SINGLE_WIDTH-1:0];
assign dp_frbus_ex2_fflags[4:0] = ex2_fflags[4:0];

endmodule



