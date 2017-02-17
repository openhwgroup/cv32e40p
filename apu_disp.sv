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
// Engineer:       Lukas Mueller - lukasmue@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Simple APU dispatcher                                      //
// Project Name:   PULP                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Dispatcher for sending instructions to the Marx            //
//                 interconnect.                                              //
////////////////////////////////////////////////////////////////////////////////

`include "apu_macros.sv"

module riscv_apu_disp (
  input logic clk_i,
  input logic rst_ni,

  // request input
  input logic                           enable_i,
  input logic [WAPUTYPE-1:0]            apu_type_i,
  input logic [WOP_CPU-1:0]             apu_op_i,
  input logic [1:0]                     apu_lat_i,
  input logic [WARG-1:0]                apu_operands_i [NARGS_CPU-1:0],
  input logic [NDSFLAGS_CPU-1:0]        apu_flags_i,
  input logic [5:0]                     apu_waddr_i,

  // response output
  output logic                          valid_o,
  output logic [WRESULT-1:0]            apu_result_o,
  output logic [NUSFLAGS_CPU-1:0]       apu_flags_o,
  output logic [5:0]                    apu_waddr_o,
  output logic                          apu_multicycle_o,
  output logic                          apu_singlecycle_o,

  // active signal
  output logic            active_o,

  // stall signals
  output logic            stall_o,

  // dependency checks
  input  logic [2:0][5:0] read_regs_i,
  input  logic [2:0]      read_regs_valid_i,
  output logic            read_dep_o,

  input  logic [1:0][5:0] write_regs_i,
  input  logic [1:0]      write_regs_valid_i,
  output logic            write_dep_o,

  // perf counter stuff
  output logic perf_type_o,
  output logic perf_cont_o,

  // apu-interconnect
  // handshake signals
  output logic                    apu_master_req_o,
  output logic                    apu_master_ready_o,
  input logic                     apu_master_gnt_i,
  // request channel
  output logic [WARG-1:0]         apu_master_operands_o [NARGS_CPU-1:0],
  output logic [WOP_CPU-1:0]      apu_master_op_o,
  output logic [WAPUTYPE-1:0]     apu_master_type_o,
  output logic [WCPUTAG-1:0]      apu_master_tag_o,
  output logic [NUSFLAGS_CPU-1:0] apu_master_flags_o,
  // response channel
  input logic                     apu_master_valid_i,
  input logic [WRESULT-1:0]       apu_master_result_i,
  input logic [NDSFLAGS_CPU-1:0]  apu_master_flags_i

  );

  logic [5:0]         addr_req, addr_inflight, addr_waiting;
  logic [5:0]         addr_inflight_dn, addr_waiting_dn;
  logic               valid_req, valid_inflight, valid_waiting;
  logic               valid_inflight_dn, valid_waiting_dn;
  logic               returned_req, returned_inflight, returned_waiting;

  logic               req_accepted;
  logic               res_valid;
  logic               req_gnt;
  logic               active;
  logic [1:0]         apu_lat;
   
   
  logic [2:0] read_deps_req,  read_deps_inflight,  read_deps_waiting;
  logic [1:0] write_deps_req, write_deps_inflight, write_deps_waiting;
  logic       read_dep_req,   read_dep_inflight,   read_dep_waiting;
  logic       write_dep_req,  write_dep_inflight,  write_dep_waiting;

  logic stall_full, stall_type, stall_nack;

  // Generate request signal; do not generate request if stalled unless it's a nack stall
  assign valid_req = enable_i & !(stall_full | stall_type);
  assign addr_req  = apu_waddr_i;

  assign req_accepted = valid_req & apu_master_gnt_i;
  assign res_valid    = apu_master_valid_i;
  assign req_gnt      = apu_master_gnt_i;
   
  //
  // In-flight instructions
  //
  // Check whether the instructions have returned
  assign returned_req      = valid_req      & apu_master_valid_i & !valid_inflight & !valid_waiting;
  assign returned_inflight = valid_inflight & (apu_master_valid_i) & !valid_waiting;
  assign returned_waiting  = valid_waiting  & (apu_master_valid_i);

  // Inflight and waiting registers
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(~rst_ni) begin
      valid_inflight <= 1'b0;
      valid_waiting  <= 1'b0;
      addr_inflight  <= '0;
      addr_waiting   <= '0;
    end else begin
       valid_inflight <= valid_inflight_dn;
       valid_waiting <= valid_waiting_dn;
       addr_inflight <= addr_inflight_dn;
       addr_waiting <= addr_waiting_dn;
    end
  end

  always_comb begin
     valid_inflight_dn = valid_inflight;
     valid_waiting_dn = valid_waiting;
     addr_inflight_dn = addr_inflight;
     addr_waiting_dn = addr_waiting;

     if (req_accepted & !returned_req) begin // this is a multicycle request
        valid_inflight_dn = 1'b1;
        addr_inflight_dn = addr_req;
        if (valid_inflight & !(returned_inflight)) begin // we already have an inflight instruction!
           valid_waiting_dn = 1'b1;
           addr_waiting_dn = addr_inflight;
        end 
        if (returned_waiting) begin // we have received a new request and waiting goes out of the pipe but will be refilled
           valid_waiting_dn = 1'b1;
           addr_waiting_dn = addr_inflight;
        end 
     end
     else if (returned_inflight) begin // multicycle request has returned
        valid_inflight_dn = 1'b0;
        valid_waiting_dn = 1'b0;
        addr_inflight_dn = '0;
        addr_waiting_dn = '0;
     end
     else if (returned_waiting) begin // multicycle request has returned
        valid_waiting_dn = 1'b0;
        addr_waiting_dn = '0;
     end
  end
   
  //
  // Active type
  //
  // Dispatcher is active when there is an unreturned instruction
  assign active = valid_inflight | valid_waiting;

  // Store the type whenever there is a request
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(~rst_ni) begin
      apu_lat  <= '0;
    end else begin
      if(valid_req) begin
        apu_lat  <= apu_lat_i;
      end
    end
  end

  //
  // Dependency checks
  //
  // There is a dependency if the register is equal to one of the instructions
  // The or reduction at the end is used to exclude the zero register since we
  // don't have to care about writing or reading it in the wrong order
  generate
    for (genvar i = 0; i < 3; i++) begin
      assign read_deps_req[i]      = (read_regs_i[i] == addr_req)      & read_regs_valid_i[i] & |read_regs_i[i];
      assign read_deps_inflight[i] = (read_regs_i[i] == addr_inflight) & read_regs_valid_i[i] & |read_regs_i[i];
      assign read_deps_waiting[i]  = (read_regs_i[i] == addr_waiting)  & read_regs_valid_i[i] & |read_regs_i[i];
    end
  endgenerate

  generate
    for (genvar i = 0; i < 2; i++) begin
      assign write_deps_req[i]      = (write_regs_i[i] == addr_req)      & write_regs_valid_i[i] & |write_regs_i[i];
      assign write_deps_inflight[i] = (write_regs_i[i] == addr_inflight) & write_regs_valid_i[i] & |write_regs_i[i];
      assign write_deps_waiting[i]  = (write_regs_i[i] == addr_waiting)  & write_regs_valid_i[i] & |write_regs_i[i];
    end
  endgenerate

  // Reduce the individual dependency signals into one read and one write dependency
  assign read_dep_req       = |read_deps_req       & valid_req      & !returned_req;
  assign read_dep_inflight  = |read_deps_inflight  & valid_inflight & !returned_inflight;
  assign read_dep_waiting   = |read_deps_waiting   & valid_waiting  & !returned_waiting;
  assign write_dep_req      = |write_deps_req      & valid_req      & !returned_req;
  assign write_dep_inflight = |write_deps_inflight & valid_inflight & !returned_inflight;
  assign write_dep_waiting  = |write_deps_waiting  & valid_waiting  & !returned_waiting;

  assign read_dep_o  = read_dep_req  | read_dep_inflight  | read_dep_waiting;
  assign write_dep_o = write_dep_req | write_dep_inflight | write_dep_waiting;

  //
  // Stall signals
  //
  // Stall if we cannot store any more instructions
  assign stall_full      = valid_inflight & valid_waiting;
  // Stall if there is a type conflict. if apu is active we can only issue requests with a larger latency than
  // the latency of the inflight operation. otherwise operations would overtake each other!
  // so we stall if: (apu_lat_i = 0 & apu_lat = 1) | (apu_lat = 2 & apu_lat_i = 1) | (apu_lat_i = 3 (multicycle))
  assign stall_type      = enable_i & active & ((apu_lat_i==2'h1) | ((apu_lat-apu_lat_i)==2'h1) | (apu_lat_i==2'h3));
  assign stall_nack      = valid_req & !apu_master_gnt_i;
  assign stall_o         = stall_full | stall_type | stall_nack;

  //
  // Generate Apu_master request
  //
  assign apu_master_req_o      = valid_req;
  assign apu_master_type_o     = apu_type_i;
  assign apu_master_op_o       = apu_op_i;
  assign apu_master_operands_o = apu_operands_i;
  assign apu_master_flags_o    = apu_flags_i;
  assign apu_master_tag_o      = '0;

  //
  // Use Apu_master response
  //
  assign apu_master_ready_o     = 1'b1;
  assign valid_o                = apu_master_valid_i;
  assign apu_result_o           = apu_master_result_i;
  assign apu_flags_o            = apu_master_flags_i;

  // Determine write register based on where the instruction returned.
  always_comb begin
    apu_waddr_o = '0;
    if(returned_req)
      apu_waddr_o = addr_req;
    if(returned_inflight)
      apu_waddr_o = addr_inflight;
    if(returned_waiting)
      apu_waddr_o = addr_waiting;
  end

  // Output active signal
  assign active_o = active;

  // Performance counter signals
  assign perf_type_o = stall_type;
  assign perf_cont_o = stall_nack;
   
  assign apu_multicycle_o  = (apu_lat == 2'h3);
  assign apu_singlecycle_o = ~(valid_inflight | valid_waiting);
   
  //
  // Assertions
  //
  
  assert property (
    @(posedge clk_i) (apu_master_valid_i) |-> (valid_req | valid_inflight | valid_waiting))
    else $warning("[APU Dispatcher] instruction returned while no instruction is in-flight");

endmodule