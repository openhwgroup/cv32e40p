// Copyright 2017 Embecosm Limited <www.embecosm.com>
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Top level wrapper for RI5CY
// Contributor: Jeremy Bennett <jeremy.bennett@embecosm.com>
//
// This instantiates memory and (eventually) a debug interface for the core.

module top
#(
  parameter ADDR_WIDTH        =  22,
  parameter BOOT_ADDR         = 'h80,
  parameter PULP_CLUSTER      = 0,
  parameter FPU               = 0,
  parameter PULP_ZFINX        = 0,
  parameter DM_HALTADDRESS    = 32'h1A110800
 )
(
 // Clock and Reset
 input logic           clk_i,
 input logic           rstn_i,

 // Interrupt inputs
 input logic            irq_i, // level sensitive IR lines
 input logic [4:0]      irq_id_i,
 output logic           irq_ack_o,
 output logic [4:0]     irq_id_o,

 // Debug Interface
 input logic            debug_req_i,

 // CPU Control Signals
 input logic            fetch_enable_i,
 output logic           core_busy_o
 );

   // signals connecting core to memory

   logic 	                instr_req;
   logic 	                instr_gnt;
   logic 	                instr_rvalid;
   logic [ADDR_WIDTH-1:0] instr_addr;
   logic [127:0] 	        instr_rdata;

   logic                  data_req;
   logic                  data_gnt;
   logic                  data_rvalid;
   logic [ADDR_WIDTH-1:0] data_addr;
   logic                  data_we;
   logic [3:0]            data_be;
   logic [31:0]           data_rdata;
   logic [31:0]           data_wdata;


   // Instantiate the core

   cv32e40p_core
     #(
        .PULP_CLUSTER(PULP_CLUSTER),
        .FPU(FPU),
        .PULP_ZFINX(PULP_ZFINX)
       )
   core_i
     (
      .clk_i                  ( clk_i                 ),
      .rst_ni                 ( rstn_i                ),

      .clock_en_i             ( 1'b1                  ),
      .scan_cg_en_i           ( 1'b0                  ),

      .boot_addr_i            ( BOOT_ADDR             ),
      .dm_halt_addr_i         ( DM_HALTADDRESS        ),
      .hart_id_i              ( 32'h0                 ),

      .instr_addr_o           ( instr_addr            ),
      .instr_req_o            ( instr_req             ),
      .instr_rdata_i          ( instr_rdata           ),
      .instr_gnt_i            ( instr_gnt             ),
      .instr_rvalid_i         ( instr_rvalid          ),

      .data_addr_o            ( data_addr             ),
      .data_wdata_o           ( data_wdata            ),
      .data_we_o              ( data_we               ),
      .data_req_o             ( data_req              ),
      .data_be_o              ( data_be               ),
      .data_rdata_i           ( data_rdata            ),
      .data_gnt_i             ( data_gnt              ),
      .data_rvalid_i          ( data_rvalid           ),

      .apu_master_req_o       (                       ),
      .apu_master_ready_o     (                       ),
      .apu_master_gnt_i       ( 1'b0                  ),
      .apu_master_operands_o  (                       ),
      .apu_master_op_o        (                       ),
      .apu_master_type_o      (                       ),
      .apu_master_flags_o     (                       ),
      .apu_master_valid_i     ( 1'b0                  ),
      .apu_master_result_i    ( 32'b0                 ),
      .apu_master_flags_i     ( 5'b0                  ),

      .irq_software_i         ( 1'b0                  ),
      .irq_timer_i            ( 1'b0                  ),
      .irq_external_i         ( 1'b0                  ),
      .irq_fast_i             ( 15'b0                 ),
      .irq_ack_o              ( irq_ack_o             ),
      .irq_id_o               ( irq_id_o              ),

      .debug_req_i            ( debug_req_i           ),

      .fetch_enable_i         ( fetch_enable_i        ),
      .core_busy_o            ( core_busy_o           ));

   // Instantiate the memory

   ram
     #(
       .ADDR_WIDTH (ADDR_WIDTH - 2)
       )
   ram_i
     (
      .clk            ( clk_i        ),

      .instr_req_i    ( instr_req    ),
      .instr_addr_i   ( instr_addr   ),
      .instr_rdata_o  ( instr_rdata  ),
      .instr_rvalid_o ( instr_rvalid ),
      .instr_gnt_o    ( instr_gnt    ),

      .data_req_i     ( data_req     ),
      .data_addr_i    ( data_addr    ),
      .data_we_i      ( data_we      ),
      .data_be_i      ( data_be      ),
      .data_wdata_i   ( data_wdata   ),
      .data_rdata_o   ( data_rdata   ),
      .data_rvalid_o  ( data_rvalid  ),
      .data_gnt_o     ( data_gnt     )
      );




  function [31:0] readADDtestPC_IF;
    /* verilator public */
    readADDtestPC_IF = core_i.pc_if;
  endfunction

  function [31:0] readADDtestPC_ID;
    /* verilator public */
    readADDtestPC_ID = core_i.pc_id;
  endfunction

  function [31:0] readADDtestPC_EX;
    /* verilator public */
    readADDtestPC_EX = core_i.pc_ex;
  endfunction

    function [31:0] readREGfile;
    /* verilator public */
    input integer n_reg;
    //readREGfile = core_i.id_stage_i.registers_i.register_file_i.mem[(32*n_reg)+:32];
    readREGfile = core_i.id_stage_i.registers_i.register_file_i.mem[n_reg];
  endfunction

endmodule	// top
