// Copyright 2017 Embecosm Limited <www.embecosm.com>
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// RAM and MM wrapper for RI5CY
// Contributor: Jeremy Bennett <jeremy.bennett@embecosm.com>
//              Robert Balas <balasr@student.ethz.ch>
//
// This maps the dp_ram module to the instruction and data ports of the RI5CY
// processor core and some pseudo peripherals

module mm_ram
    #(parameter RAM_ADDR_WIDTH = 16,
      parameter INSTR_RDATA_WIDTH = 128)
    (input logic                          clk_i,
     input logic                          rst_ni,

     input logic                          instr_req_i,
     input logic [RAM_ADDR_WIDTH-1:0]     instr_addr_i,
     output logic [INSTR_RDATA_WIDTH-1:0] instr_rdata_o,
     output logic                         instr_rvalid_o,
     output logic                         instr_gnt_o,

     input logic                          data_req_i,
     input logic [31:0]                   data_addr_i,
     input logic                          data_we_i,
     input logic [3:0]                    data_be_i,
     input logic [31:0]                   data_wdata_i,
     output logic [31:0]                  data_rdata_o,
     output logic                         data_rvalid_o,
     output logic                         data_gnt_o,

     input logic [4:0]                    irq_id_i,
     input logic                          irq_ack_i,
     output logic [4:0]                   irq_id_o,
     output logic                         irq_o,

     output logic                         tests_passed_o,
     output logic                         tests_failed_o,
     output logic                         exit_valid_o,
     output logic [31:0]                  exit_value_o);

    localparam int                    TIMER_IRQ_ID = 3;

    // mux for read and writes
    enum logic [1:0]{RAM, MM, ERR} select_rdata_d, select_rdata_q;
    logic [31:0]                   data_addr_aligned;

    // signals to ram
    logic                          ram_data_req;
    logic [RAM_ADDR_WIDTH-1:0]     ram_data_addr;
    logic [31:0]                   ram_data_wdata;
    logic [31:0]                   ram_data_rdata;
    logic                          ram_data_we;
    logic [3:0]                    ram_data_be;

    // signals to print peripheral
    logic [31:0]                   print_wdata;
    logic                          print_valid;

    // signals to timer
    logic [31:0]                   timer_irq_mask_q;
    logic [31:0]                   timer_cnt_q;
    logic                          irq_q;
    logic                          timer_reg_valid;
    logic                          timer_val_valid;
    logic [31:0]                   timer_wdata;


    // uhh, align?
    always_comb data_addr_aligned = {data_addr_i[31:2], 2'b0};

    // handle the mapping of read and writes to either memory or pseudo
    // peripherals (currently just a redirection of writes to stdout)
    always_comb begin
        tests_passed_o  = '0;
        tests_failed_o  = '0;
        exit_value_o    = 0;
        exit_valid_o    = '0;
        ram_data_req    = '0;
        ram_data_addr   = '0;
        ram_data_wdata  = '0;
        ram_data_we     = '0;
        ram_data_be     = '0;
        print_wdata     = '0;
        print_valid     = '0;
        timer_wdata     = '0;
        timer_reg_valid = '0;
        timer_val_valid = '0;

        select_rdata_d  = RAM;

        if (data_req_i) begin
            if (data_we_i) begin // handle writes
                if (data_addr_i < 2 ** RAM_ADDR_WIDTH) begin
                    ram_data_req = data_req_i;
                    ram_data_addr = data_addr_i[RAM_ADDR_WIDTH-1:0];
                    ram_data_wdata = data_wdata_i;
                    ram_data_we = data_we_i;
                    ram_data_be = data_be_i;

                end else if (data_addr_i == 32'h1000_0000) begin
                    print_wdata = data_wdata_i;
                    print_valid = '1;

                end else if (data_addr_i == 32'h2000_0000) begin
                    if (data_wdata_i == 123456789)
                        tests_passed_o = '1;
                    else if (data_wdata_i == 1)
                        tests_failed_o = '1;

                end else if (data_addr_i == 32'h2000_0004) begin
                    exit_valid_o = '1;
                    exit_value_o = data_wdata_i;

                end else if (data_addr_i == 32'h1500_0000) begin
                    timer_wdata = data_wdata_i;
                    timer_reg_valid = '1;

                end else if (data_addr_i == 32'h1500_0004) begin
                    timer_wdata = data_wdata_i;
                    timer_val_valid = '1;

                end else begin
                    // out of bounds write
                end

            end else begin // handle reads
                if (data_addr_i < 2 ** RAM_ADDR_WIDTH) begin
                    select_rdata_d = RAM;

                    ram_data_req = data_req_i;
                    ram_data_addr = data_addr_i[RAM_ADDR_WIDTH-1:0];
                    ram_data_wdata = data_wdata_i;
                    ram_data_we = data_we_i;
                    ram_data_be = data_be_i;

                end else
                    select_rdata_d = ERR;

            end
        end
    end

`ifndef VERILATOR
    // signal out of bound writes
    out_of_bounds_write: assert property
    (@(posedge clk_i) disable iff (~rst_ni)
     (data_req_i && data_we_i |-> data_addr_i < 2 ** RAM_ADDR_WIDTH
      || data_addr_i == 32'h1000_0000
      || data_addr_i == 32'h1500_0000
      || data_addr_i == 32'h1500_0004
      || data_addr_i == 32'h2000_0000
      || data_addr_i == 32'h2000_0004))
        else $error("out of bounds write to %08x with %08x",
                    data_addr_i, data_wdata_i);
`endif

    // make sure we select the proper read data
    always_comb begin: read_mux
        data_rdata_o = '0;

        if(select_rdata_q == RAM) begin
            data_rdata_o = ram_data_rdata;
        end else if (select_rdata_q == ERR) begin
            $display("out of bounds read from %08x", data_addr_i);
            $finish;
        end
    end

    // print to stdout pseudo peripheral
    always_ff @(posedge clk_i, negedge rst_ni) begin: print_peripheral
        if(print_valid) begin
            if ($test$plusargs("verbose")) begin
                if (32 <= print_wdata && print_wdata < 128)
                    $display("OUT: '%c'", print_wdata[7:0]);
                else
                    $display("OUT: %3d", print_wdata);

            end else begin
                $write("%c", print_wdata[7:0]);
`ifndef VERILATOR
                $fflush();
`endif
            end
        end
    end

    assign irq_id_o = TIMER_IRQ_ID;
    assign irq_o = irq_q;

    // Control timer. We need one to have some kind of timeout for tests that
    // get stuck in some loop. The riscv-tests also mandate that. Enable timer
    // interrupt by writing 1 to timer_irq_mask_q. Write initial value to
    // timer_cnt_q which gets counted down each cycle. When it transitions from
    // 1 to 0, and interrupt request (irq_q) is made (masked by timer_irq_mask_q).
    always_ff @(posedge clk_i, negedge rst_ni) begin: tb_timer
        if(~rst_ni) begin
            timer_irq_mask_q <= '0;
            timer_cnt_q      <= '0;
            irq_q            <= '0;

        end else begin
            // set timer irq mask
            if(timer_reg_valid) begin
                timer_irq_mask_q <= timer_wdata;

            // write timer value
            end else if(timer_val_valid) begin
                timer_cnt_q <= timer_wdata;

            end else begin
                if(timer_cnt_q > 0)
                    timer_cnt_q <= timer_cnt_q - 1;

                if(timer_cnt_q == 1)
                    irq_q <= 1'b1 && timer_irq_mask_q[TIMER_IRQ_ID];

                if(irq_ack_i == 1'b1 && irq_id_i == TIMER_IRQ_ID)
                    irq_q <= '0;

            end
        end
    end

    // show writes if requested
    always_ff @(posedge clk_i, negedge rst_ni) begin: verbose_writes
        if ($test$plusargs("verbose") && data_req_i && data_we_i)
            $display("write addr=0x%08x: data=0x%08x",
                     data_addr_i, data_wdata_i);
    end

    // instantiate the ram
    dp_ram
        #(.ADDR_WIDTH (RAM_ADDR_WIDTH),
          .INSTR_RDATA_WIDTH(INSTR_RDATA_WIDTH))
    dp_ram_i
        (
         .clk_i     ( clk_i         ),

         .en_a_i    ( instr_req_i   ),
         .addr_a_i  ( instr_addr_i  ),
         .wdata_a_i ( '0            ),	// Not writing so ignored
         .rdata_a_o ( instr_rdata_o ),
         .we_a_i    ( '0            ),
         .be_a_i    ( 4'b1111       ),	// Always want 32-bits

         .en_b_i    ( ram_data_req    ),
         .addr_b_i  ( ram_data_addr   ),
         .wdata_b_i ( ram_data_wdata  ),
         .rdata_b_o ( ram_data_rdata  ),
         .we_b_i    ( ram_data_we     ),
         .be_b_i    ( ram_data_be     ));

    // do the handshacking stuff by assuming we always react in one cycle
    assign data_gnt_o  = data_req_i;
    assign instr_gnt_o = instr_req_i;

    always_ff @(posedge clk_i) begin
    end

    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (~rst_ni) begin
            select_rdata_q <= RAM;
            data_rvalid_o  <= '0;
            instr_rvalid_o <= '0;

        end else begin
            select_rdata_q <= select_rdata_d;
            data_rvalid_o  <= data_req_i;
            instr_rvalid_o <= instr_req_i;

        end
    end

endmodule // ram
