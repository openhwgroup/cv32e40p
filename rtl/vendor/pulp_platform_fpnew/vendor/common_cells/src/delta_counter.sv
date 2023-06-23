// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Up/down counter with variable delta

module delta_counter #(
    parameter int unsigned WIDTH = 4,
    parameter bit STICKY_OVERFLOW = 1'b0
)(
    input  logic             clk_i,
    input  logic             rst_ni,
    input  logic             clear_i, // synchronous clear
    input  logic             en_i,    // enable the counter
    input  logic             load_i,  // load a new value
    input  logic             down_i,  // downcount, default is up
    input  logic [WIDTH-1:0] delta_i,
    input  logic [WIDTH-1:0] d_i,
    output logic [WIDTH-1:0] q_o,
    output logic             overflow_o
);
    logic [WIDTH:0] counter_q, counter_d;
    if (STICKY_OVERFLOW) begin : gen_sticky_overflow
        logic overflow_d, overflow_q;
        always_ff @(posedge clk_i or negedge rst_ni) overflow_q <= ~rst_ni ? 1'b0 : overflow_d;
        always_comb begin
            overflow_d = overflow_q;
            if (clear_i || load_i) begin
                overflow_d = 1'b0;
            end else if (!overflow_q && en_i) begin
                if (down_i) begin
                    overflow_d = delta_i > counter_q[WIDTH-1:0];
                end else begin
                    overflow_d = counter_q[WIDTH-1:0] > ({WIDTH{1'b1}} - delta_i);
                end
            end
        end
        assign overflow_o = overflow_q;
    end else begin : gen_transient_overflow
        // counter overflowed if the MSB is set
        assign overflow_o = counter_q[WIDTH];
    end
    assign q_o = counter_q[WIDTH-1:0];

    always_comb begin
        counter_d = counter_q;

        if (clear_i) begin
            counter_d = '0;
        end else if (load_i) begin
            counter_d = {1'b0, d_i};
        end else if (en_i) begin
            if (down_i) begin
                counter_d = counter_q - delta_i;
            end else begin
                counter_d = counter_q + delta_i;
            end
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
           counter_q <= '0;
        end else begin
           counter_q <= counter_d;
        end
    end
endmodule
