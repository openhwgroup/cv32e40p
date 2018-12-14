// Copyright 2017 Embecosm Limited <www.embecosm.com>
// Copyright 2018 Robert Balas <balasr@student.ethz.ch>
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Top level wrapper for a RI5CY testbench
// Contributor: Robert Balas <balasr@student.ethz.ch>
//              Jeremy Bennett <jeremy.bennett@embecosm.com>
//

module tb_top
    #(parameter INSTR_RDATA_WIDTH = 128,
      parameter RAM_ADDR_WIDTH = 16,
      parameter BOOT_ADDR  = 'h0,
      parameter EXCEPTION_OFFSET = 'h80);

    // uncomment to record execution trace
    //`define TRACE_EXECUTION

    const time CLK_PHASE_HI       = 5ns;
    const time CLK_PHASE_LO       = 5ns;
    const time CLK_PERIOD         = CLK_PHASE_HI + CLK_PHASE_LO;
    const time STIM_APPLICATION_DEL = CLK_PERIOD * 0.1;
    const time RESP_ACQUISITION_DEL = CLK_PERIOD * 0.9;
    const time RESET_DEL = STIM_APPLICATION_DEL;
    const int  RESET_WAIT_CYCLES  = 4;


    // clock and reset for tb
    logic                   clk   = 'b1;
    logic                   rst_n = 'b0;

    // testbench result
    logic                   tests_passed;

    // signals connecting core to memory
    logic                        instr_req;
    logic                        instr_gnt;
    logic                        instr_rvalid;
    logic [31:0]                 instr_addr;
    logic [127:0]                instr_rdata;

    logic                        data_req;
    logic                        data_gnt;
    logic                        data_rvalid;
    logic [31:0]                 data_addr;
    logic                        data_we;
    logic [3:0]                  data_be;
    logic [31:0]                 data_rdata;
    logic [31:0]                 data_wdata;

    // signals to debug unit
    logic                        debug_req_i;
    logic                        debug_gnt_o;
    logic                        debug_rvalid_o;
    logic [14:0]                 debug_addr_i;
    logic                        debug_we_i;
    logic [31:0]                 debug_wdata_i;
    logic [31:0]                 debug_rdata_o;
    logic                        debug_halted_o;


    // don't do any debugging
    assign debug_req_i = '0;
    assign debug_addr_i = '0;
    assign debug_we_i = '0;
    assign debug_wdata_i = '0;

    // no interrupts
    assign irq_i = '0;

    // start fetching
    assign fetch_enable_i = '1;

    // allow vcd dump
    initial begin
        if ($test$plusargs("vcd")) begin
            $dumpfile("riscy_tb.vcd");
            $dumpvars(0, tb_top);
        end
    end

    // we either load the provided firmware or execute a small test program that
    // doesn't do more than an infinite loop with some I/O
    initial begin: load_prog
        automatic logic [1023:0] firmware;
        automatic int prog_size = 6;

        if($value$plusargs("firmware=%s", firmware)) begin
            if($test$plusargs("verbose"))
                $display("[TESTBENCH] %t: loading firmware %0s ...", $time, firmware);
            $readmemh(firmware, ram_i.dp_ram_i.mem);

        end else begin
            for (int i = 0; i < prog_size; i++) begin
                // little endian indexing
                {ram_i.dp_ram_i.mem[i*4 + 3 + BOOT_ADDR + EXCEPTION_OFFSET],
                 ram_i.dp_ram_i.mem[i*4 + 2 + BOOT_ADDR + EXCEPTION_OFFSET],
                 ram_i.dp_ram_i.mem[i*4 + 1 + BOOT_ADDR + EXCEPTION_OFFSET],
                 ram_i.dp_ram_i.mem[i*4 + 0 + BOOT_ADDR + EXCEPTION_OFFSET]} =

                         {32'h 3fc00093, //       li      x1,1020
                          32'h 0000a023, //       sw      x0,0(x1)
                          32'h 0000a103, // loop: lw      x2,0(x1)
                          32'h 00110113, //       addi    x2,x2,1
                          32'h 0020a023, //       sw      x2,0(x1)
                          32'h ff5ff06f} //       j       <loop>
                         [(prog_size-1-i)*32 +: 32];
            end
        end
    end

    // clock generation
    initial begin: clock_gen
        forever begin
            #CLK_PHASE_HI clk = 1'b0;
            #CLK_PHASE_LO clk = 1'b1;
        end
    end: clock_gen

    // reset generation
    initial begin: reset_gen
        rst_n = 1'b0;
        // wait a few cycles
        repeat (RESET_WAIT_CYCLES) begin
            @(posedge clk); //TODO: was posedge, see below
        end
        //TODO: think about when the reset sould happen
        #RESET_DEL rst_n = 1'b1;
        if($test$plusargs("verbose"))
            $display("[RESET] %t: reset deasserted", $time);

    end: reset_gen

    // set timing format
    initial begin: timing_format
        $timeformat(-9, 0, "ns", 9);
    end: timing_format

    // instantiate the core
    riscv_core
        #(.INSTR_RDATA_WIDTH (INSTR_RDATA_WIDTH))
    riscv_core_i
        (
         .clk_i                  ( clk                   ),
         .rst_ni                 ( rst_n                 ),

         .clock_en_i             ( '1                    ),
         .test_en_i              ( '1                    ),

         .boot_addr_i            ( BOOT_ADDR             ),
         .core_id_i              ( 4'h0                  ),
         .cluster_id_i           ( 6'h0                  ),

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
         .data_err_i             ( 1'b0                  ),

         .apu_master_req_o       (                       ),
         .apu_master_ready_o     (                       ),
         .apu_master_gnt_i       (                       ),
         .apu_master_operands_o  (                       ),
         .apu_master_op_o        (                       ),
         .apu_master_type_o      (                       ),
         .apu_master_flags_o     (                       ),
         .apu_master_valid_i     (                       ),
         .apu_master_result_i    (                       ),
         .apu_master_flags_i     (                       ),

         .irq_i                  ( irq_i                 ),
         .irq_id_i               ( irq_id_i              ),
         .irq_ack_o              ( irq_ack_o             ),
         .irq_id_o               ( irq_id_o              ),
         .irq_sec_i              ( irq_sec_i             ),

         .sec_lvl_o              ( sec_lvl_o             ),

         .debug_req_i            ( debug_req_i           ),
         .debug_gnt_o            ( debug_gnt_o           ),
         .debug_rvalid_o         ( debug_rvalid_o        ),
         .debug_addr_i           ( debug_addr_i          ),
         .debug_we_i             ( debug_we_i            ),
         .debug_wdata_i          ( debug_wdata_i         ),
         .debug_rdata_o          ( debug_rdata_o         ),
         .debug_halted_o         ( debug_halted_o        ),
         .debug_halt_i           ( 1'b0                  ),     // Not used in
         .debug_resume_i         ( 1'b0                  ),     // single core

         .fetch_enable_i         ( fetch_enable_i        ),
         .core_busy_o            ( core_busy_o           ),

         .ext_perf_counters_i    (                       ),
         .fregfile_disable_i     ( 1'b0                  ));

    // this handles read to RAM and memory mapped pseudo peripherals
    mm_ram
        #(.RAM_ADDR_WIDTH (RAM_ADDR_WIDTH))
    ram_i
        (.clk_i          ( clk                            ),
         .rst_ni         ( rst_n                          ),

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
         .tests_passed_o ( tests_passed                   ));

endmodule // tb_top
