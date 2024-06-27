`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06/04/2024 04:20:00 PM
// Design Name: 
// Module Name: bf16_minmax_readyValid
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 12/02/2023 09:08:55 PM
// Design Name: 
// Module Name: bf16minmax
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

module bf16_minmax(
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [15:0] operand_a,  // BF16 operand A
    input logic [15:0] operand_b,  // BF16 operand B
    input logic [3:0] operation,   // Operation select: 0 for min, 1 for max
    // Input Handshake
    input  logic                     in_valid_i,
    output logic                     in_ready_o,
    // Output handshake
    output logic                     out_valid_o,
    input  logic                     out_ready_i,
    output logic [15:0] result,    // BF16 result
    output logic [3:0] fpcsr       // Floating Point Control and Status Register
);

    // Decompose BF16 operands
    logic operand_a_sign, operand_b_sign;
    logic [7:0] operand_a_exp, operand_b_exp;
    logic [6:0] operand_a_man, operand_b_man;
    logic operand_a_nan, operand_b_nan;
    logic numerical_comparison;
    logic operand_a_smaller;
    logic select_a;
    
    assign operand_a_sign = operand_a[15];
    assign operand_a_exp = operand_a[14:7];
    assign operand_a_man = operand_a[6:0];
    assign operand_b_sign = operand_b[15];
    assign operand_b_exp = operand_b[14:7];
    assign operand_b_man = operand_b[6:0];
    
    logic clkg_en;
    logic valid_pipeline;

//    always_latch begin
//        if (~clk) 
//            clkg_en = enable;
//    end
//   // assign clkg_en = ~clk ? enable : clkg_en;

//Clock gating this way as the enable is being sent from the upper modules after selecting the instructions and cannot sample it on the negedge
    
//    assign gated_clk = clk & clkg_en;
    assign gated_clk = clk && enable;
    
    // Handshake signals
    assign in_ready_o = in_valid_i;
    assign out_valid_o = valid_pipeline ;
    
    always_ff @(posedge gated_clk or negedge reset) begin
        if (!reset) begin
            result = 16'b0;
            fpcsr = 4'b0000;
            valid_pipeline = 0;
        end else if (in_valid_i && out_ready_i) begin
            // Check for NaN
            fpcsr = 0;
            operand_a_nan = (operand_a_exp == 8'hFF) && (operand_a_man != 0);
            operand_b_nan = (operand_b_exp == 8'hFF) && (operand_b_man != 0);
    
            if (operand_a_nan && operand_b_nan) begin
                // Both operands are NaN, return canonical NaN
                result = 16'h7FC0; // Canonical NaN in BF16
                fpcsr[3] = 1; // Invalid flag set
            end else if (operand_a_nan) begin
                // Operand A is NaN, return B
                result = operand_b;
                fpcsr[3] = 1; // Invalid flag set
            end else if (operand_b_nan) begin
                // Operand B is NaN, return A
                result = operand_a;
                fpcsr[3] = 1; // Invalid flag set
            end else begin
                numerical_comparison = operand_a < operand_b;
                // Determine which operand is smaller or larger
                operand_a_smaller = numerical_comparison ^ (operand_a_sign || operand_b_sign);
                // Operation: 0011 for min, 0010 for max
                select_a = (operation == 4'b0011) ? operand_a_smaller : !operand_a_smaller;
                if (select_a) begin
                    // Select A for min or max based on comparison
                    result = operand_a;
                end else begin
                    // Select B for min or max based on comparison
                    result = operand_b;
                end
            end
            valid_pipeline = 1;
        end else begin
            valid_pipeline = 0;
        end
    end
endmodule