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

module pa_fpu_frbus(
  ctrl_frbus_ex2_wb_req,
  dp_frbus_ex2_data,
  dp_frbus_ex2_fflags,
  fdsu_frbus_data,
  fdsu_frbus_fflags,
  fdsu_frbus_wb_vld,
  fpu_idu_fwd_data,
  fpu_idu_fwd_fflags,
  fpu_idu_fwd_vld
);

input           ctrl_frbus_ex2_wb_req;
input   [31:0]  dp_frbus_ex2_data;        
input   [4 :0]  dp_frbus_ex2_fflags;
input   [31:0]  fdsu_frbus_data;          
input   [4 :0]  fdsu_frbus_fflags;
input           fdsu_frbus_wb_vld;
output  [31:0]  fpu_idu_fwd_data;
output  [4 :0]  fpu_idu_fwd_fflags;
output          fpu_idu_fwd_vld;

reg     [31:0]  frbus_wb_data;            
reg     [4 :0]  frbus_wb_fflags;

wire            ctrl_frbus_ex2_wb_req;
wire    [31:0]  fdsu_frbus_data;          
wire    [4 :0]  fdsu_frbus_fflags;
wire            fdsu_frbus_wb_vld;
wire    [31:0]  fpu_idu_fwd_data;
wire    [4 :0]  fpu_idu_fwd_fflags;
wire            fpu_idu_fwd_vld;
wire            frbus_ex2_wb_vld;
wire            frbus_fdsu_wb_vld;
wire            frbus_wb_vld;
wire    [3 :0]  frbus_source_vld;


//==========================================================
//                   Input Signal Rename
//==========================================================
assign frbus_fdsu_wb_vld = fdsu_frbus_wb_vld;
assign frbus_ex2_wb_vld  = ctrl_frbus_ex2_wb_req;
assign frbus_source_vld[3:0]     = {1'b0, 1'b0, frbus_ex2_wb_vld, frbus_fdsu_wb_vld};
assign frbus_wb_vld = frbus_ex2_wb_vld | frbus_fdsu_wb_vld;

always @( frbus_source_vld[3:0]
       or fdsu_frbus_data[31:0]
       or dp_frbus_ex2_data[31:0]
       or fdsu_frbus_fflags[4:0]
       or dp_frbus_ex2_fflags[4:0])
begin
  case(frbus_source_vld[3:0])
    4'b0001: begin // DIV
      frbus_wb_data[31:0] = fdsu_frbus_data[31:0];
      frbus_wb_fflags[4:0]    = fdsu_frbus_fflags[4:0];
    end
    4'b0010: begin // EX2
      frbus_wb_data[31:0] = dp_frbus_ex2_data[31:0];
      frbus_wb_fflags[4:0]    = dp_frbus_ex2_fflags[4:0];
    end
    default: begin
      frbus_wb_data[31:0] = {31{1'b0}};
      frbus_wb_fflags[4:0]    = 5'b0;
    end
  endcase
end

assign fpu_idu_fwd_vld            = frbus_wb_vld;
assign fpu_idu_fwd_fflags[4:0]    = frbus_wb_fflags[4:0];
assign fpu_idu_fwd_data[31:0] = frbus_wb_data[31:0];

endmodule


