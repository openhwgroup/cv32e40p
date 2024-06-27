`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 12/06/2023 03:56:06 PM
// Design Name: 
// Module Name: bf16_accelerator_top
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

module bf16_accelerator_top(
    input logic clk,
    input logic reset,
    input logic enable, // Enable signal for the accelerator
    input logic [31:0] operand_a, // First operand
    input logic [15:0] operand_b, // Second operand
    input logic [31:0] operand_c, // Third operand for FMA operations
    input logic [3:0] operation,  // Operation type
    input logic in_valid_i,       // Input valid signal
    output logic in_ready_o,      // Input ready signal
    input logic out_ready_i,      // Output ready signal
    output logic out_valid_o,     // Output valid signal
    output logic [31:0] result,   // Result of the operation
    output logic [3:0] fpcsr      // Floating-point control and status register
);

// Internal enable signals for submodules
logic conv_enable, maxmin_enable, addmul_enable;

// Internal result and FPCSR signals from submodules
logic [15:0] maxmin_result;
logic [31:0] conv_result, addmul_result;
logic [3:0] conv_fpcsr, maxmin_fpcsr, addmul_fpcsr;

// Handshake signals for maxmin module
logic maxmin_in_valid, maxmin_in_ready;
logic maxmin_out_valid, maxmin_out_ready;

// Handshake signals for conversion module
logic conv_in_valid, conv_in_ready;
logic conv_out_valid, conv_out_ready;

// Handshake signals for conversion module
logic fma_in_valid, fma_in_ready;
logic fma_out_valid, fma_out_ready;

// Instantiate the conversion module
bf16_conversion bf16_fp32_conversion_inst (
    .clk(clk),
    .reset(reset),
    .enable(conv_enable),
    .operation(operation),       // Pass the operation code
    .operand(operand_a),         // Pass the operand
    .in_valid_i(conv_in_valid),
    .in_ready_o(conv_in_ready),
    .out_valid_o(conv_out_valid),
    .out_ready_i(conv_out_ready),
    .result(conv_result),        // Receive the result
    .fpcsr(conv_fpcsr)           // Receive the FPCSR status
);

// Instantiate the max/min module
bf16_minmax maxmin_module (
    .clk(clk),
    .reset(reset),
    .enable(maxmin_enable),
    .operand_a(operand_a[15:0]),
    .operand_b(operand_b),
    .operation(operation),
    // Handshake signals
    .in_valid_i(maxmin_in_valid),
    .in_ready_o(maxmin_in_ready),
    .out_valid_o(maxmin_out_valid),
    .out_ready_i(maxmin_out_ready),
    // Result and FPCSR
    .result(maxmin_result),
    .fpcsr(maxmin_fpcsr)
);

// Instantiate the add/mul module
bf16_fma_op addmul_module (
    .clk(clk),
    .reset(reset),
    .en(addmul_enable),
    .op_a(operand_a),
    .op_b(operand_b),
    .op_c(operand_c),
    .oper(operation),
    // Handshake signals
    .in_valid_i(fma_in_valid),
    .in_ready_o(fma_in_ready),
    .out_valid_o(fma_out_valid),
    .out_ready_i(fma_out_ready),
    // Result and FPCSR
    .result(addmul_result),
    .fpcsr(addmul_fpcsr)
);

// Enable logic for submodules
assign conv_enable = !operation[3] & !operation[2] & !operation[1];
assign maxmin_enable = !operation[3] & !operation[2] & operation[1];
assign addmul_enable = operation[3] | operation[2];

// Handshake logic for maxmin module
assign maxmin_in_valid = in_valid_i & maxmin_enable;
assign maxmin_out_ready = out_ready_i & maxmin_enable;

// Handshake logic for conv module
assign conv_in_valid = in_valid_i & conv_enable;
assign conv_out_ready = out_ready_i & conv_enable;

// Handshake logic for fma module
assign fma_in_valid = in_valid_i & addmul_enable;
assign fma_out_ready = out_ready_i & addmul_enable;



// Result and FPCSR aggregation
assign result = ({32{conv_enable}} & conv_result) | ({32{maxmin_enable}} & {16'b0, maxmin_result}) | ({32{addmul_enable}} & addmul_result);
assign fpcsr = ({4{conv_enable}} & conv_fpcsr) | ({4{maxmin_enable}} & maxmin_fpcsr) | ({4{addmul_enable}} & addmul_fpcsr);

// Valid and ready signals
assign in_ready_o = (maxmin_enable ? maxmin_in_ready : 
                    (conv_enable ? conv_in_ready : 
                    addmul_enable ? fma_in_ready :1'b0));

assign out_valid_o = (maxmin_enable ? maxmin_out_valid : 
                     (conv_enable ? conv_out_valid :
                     addmul_enable ? fma_out_valid : 1'b0));

endmodule