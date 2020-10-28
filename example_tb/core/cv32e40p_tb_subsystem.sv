// Copyright 2018 Robert Balas <balasr@student.ethz.ch>
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Wrapper for a RI5CY testbench, containing RI5CY, Memory and stdout peripheral
// Contributor: Robert Balas <balasr@student.ethz.ch>

module cv32e40p_tb_subsystem
    #(parameter INSTR_RDATA_WIDTH = 32,
      parameter RAM_ADDR_WIDTH = 20,
      parameter BOOT_ADDR = 'h180,
      parameter PULP_XPULP = 0,
      parameter PULP_CLUSTER = 0,
      parameter FPU = 0,
      parameter PULP_ZFINX = 0,
      parameter NUM_MHPMCOUNTERS = 1,
      parameter DM_HALTADDRESS = 32'h1A110800)
    (input logic         clk_i,
     input logic         rst_ni,

     input logic         fetch_enable_i,
     output logic        tests_passed_o,
     output logic        tests_failed_o,
     output logic [31:0] exit_value_o,
     output logic        exit_valid_o);

    import cv32e40p_apu_core_pkg::*;

    // signals connecting core to memory
    logic                         instr_req;
    logic                         instr_gnt;
    logic                         instr_rvalid;
    logic [31:0]                  instr_addr;
    logic [INSTR_RDATA_WIDTH-1:0] instr_rdata;

    logic                         data_req;
    logic                         data_gnt;
    logic                         data_rvalid;
    logic [31:0]                  data_addr;
    logic                         data_we;
    logic [3:0]                   data_be;
    logic [31:0]                  data_rdata;
    logic [31:0]                  data_wdata;
    logic [5:0]                   data_atop = 6'b0;

    // signals to debug unit
    logic                         debug_req_i;

    // irq signals
    logic                         irq_ack;
    logic [4:0]                   irq_id_out;
    logic                         irq_software;
    logic                         irq_timer;
    logic                         irq_external;
    logic [15:0]                  irq_fast;

    logic                         core_sleep_o;

    // APU Core to FP Wrapper
    logic                            apu_req;
    logic [APU_NARGS_CPU-1:0][31:0]  apu_operands;
    logic [APU_WOP_CPU-1:0]          apu_op;
    logic [APU_NDSFLAGS_CPU-1:0]     apu_flags;


    // APU FP Wrapper to Core
    logic                           apu_gnt;
    logic                           apu_rvalid;
    logic [31:0]                    apu_rdata;
    logic [APU_NUSFLAGS_CPU-1:0]    apu_rflags;




    assign debug_req_i = 1'b0;

    // instantiate the core
    cv32e40p_wrapper
        #(
          .PULP_XPULP            ( PULP_XPULP            ),
          .PULP_CLUSTER          ( PULP_CLUSTER          ),
          .FPU                   ( FPU                   ),
          .PULP_ZFINX            ( PULP_ZFINX            ),
          .NUM_MHPMCOUNTERS      ( NUM_MHPMCOUNTERS      ))
    wrapper_i
        (
         .clk_i                  ( clk_i                 ),
         .rst_ni                 ( rst_ni                ),

         .pulp_clock_en_i        ( 1'b1                  ),
         .scan_cg_en_i           ( 1'b0                  ),

         .boot_addr_i            ( BOOT_ADDR             ),
         .mtvec_addr_i           ( 32'h0                 ),
         .dm_halt_addr_i         ( DM_HALTADDRESS        ),
         .hart_id_i              ( 32'h0                 ),
         .dm_exception_addr_i    ( 32'h0                 ),

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

         .apu_req_o              ( apu_req               ),
         .apu_gnt_i              ( apu_gnt               ),
         .apu_operands_o         ( apu_operands          ),
         .apu_op_o               ( apu_op                ),
         .apu_flags_o            ( apu_flags             ),
         .apu_rvalid_i           ( apu_rvalid            ),
         .apu_result_i           ( apu_rdata             ),
         .apu_flags_i            ( apu_rflags            ),

         .irq_i                  ( {irq_fast, 4'b0, irq_external, 3'b0, irq_timer, 3'b0, irq_software, 3'b0 } ),
         .irq_ack_o              ( irq_ack               ),
         .irq_id_o               ( irq_id_out            ),

         .debug_req_i            ( debug_req_i           ),

         .fetch_enable_i         ( fetch_enable_i        ),
         .core_sleep_o           ( core_sleep_o           ));



    generate
        if(FPU) begin
            cv32e40p_fp_wrapper fp_wrapper_i
            (
               .clk_i          ( clk_i        ),
               .rst_ni         ( rst_ni       ),
               .apu_req_i      ( apu_req      ),
               .apu_gnt_o      ( apu_gnt      ),
               .apu_operands_i ( apu_operands ),
               .apu_op_i       ( apu_op       ),
               .apu_flags_i    ( apu_flags    ),
               .apu_rvalid_o   ( apu_rvalid   ),
               .apu_rdata_o    ( apu_rdata    ),
               .apu_rflags_o   ( apu_rflags   )
            );
        end else begin
            assign apu_gnt_o      = '0;
            assign apu_operands_i = '0;
            assign apu_op_i       = '0;
            assign apu_flags_i    = '0;
            assign apu_rvalid_o   = '0;
            assign apu_rdata_o    = '0;
            assign apu_rflags_o   = '0;
        end
    endgenerate

    // this handles read to RAM and memory mapped pseudo peripherals
    mm_ram
        #(.RAM_ADDR_WIDTH (RAM_ADDR_WIDTH),
          .INSTR_RDATA_WIDTH (INSTR_RDATA_WIDTH))
    ram_i
        (.clk_i          ( clk_i                          ),
         .rst_ni         ( rst_ni                         ),

         .instr_req_i    ( instr_req                      ),
         .instr_addr_i   ( instr_addr[RAM_ADDR_WIDTH-1:0] ),
         .instr_rdata_o  ( instr_rdata                    ),
         .instr_rvalid_o ( instr_rvalid                   ),
         .instr_gnt_o    ( instr_gnt                      ),

         .data_req_i     ( data_req                       ),
         .data_addr_i    ( data_addr                      ),
         .data_we_i      ( data_we                        ),
         .data_be_i      ( data_be                        ),
         .data_wdata_i   ( data_wdata                     ),
         .data_rdata_o   ( data_rdata                     ),
         .data_rvalid_o  ( data_rvalid                    ),
         .data_gnt_o     ( data_gnt                       ),
         .data_atop_i    ( data_atop                      ),

         .irq_id_i       ( irq_id_out                     ),
         .irq_ack_i      ( irq_ack                        ),

         // output irq lines to Core
         .irq_software_o ( irq_software                   ),
         .irq_timer_o    ( irq_timer                      ),
         .irq_external_o ( irq_external                   ),
         .irq_fast_o     ( irq_fast                       ),

         .pc_core_id_i   ( wrapper_i.core_i.pc_id         ),

         .tests_passed_o ( tests_passed_o                 ),
         .tests_failed_o ( tests_failed_o                 ),
         .exit_valid_o   ( exit_valid_o                   ),
         .exit_value_o   ( exit_value_o                   ));

endmodule // cv32e40p_tb_subsystem
