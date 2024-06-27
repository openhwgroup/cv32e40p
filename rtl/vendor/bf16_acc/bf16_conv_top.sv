`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06/11/2024 05:57:21 PM
// Design Name: 
// Module Name: bf16conversion_top_RV
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





module bf16_conversion(
    input logic clk,
    input logic reset,
    input logic enable,  // Enable signal for conversion operations
    input logic [3:0] operation,    // 4-bit operation code
    input logic [31:0] operand,     // Universal operand for both BF16 and FP32
    // Input Handshake
    input  logic                     in_valid_i,
    output logic                     in_ready_o,
    // Output handshake
    output logic                     out_valid_o,
    input  logic                     out_ready_i,
    //result signals
    output logic [31:0] result,     // Result, either BF16 or FP32
    output logic [3:0] fpcsr        // Floating Point Control and Status Register
);

    // Define operation codes for conversions
    localparam BF16_TO_FP32_OP = 4'b0000;
    localparam FP32_TO_BF16_OP = 4'b0001;
    
    logic bf16tofp32_en;
    logic fp32tobf16_en;
    
   

    // Internal signals for the submodules
    wire [15:0] bf16_result;
    wire [31:0] fp32_result;
    wire [3:0] bf16_fpcsr;
    wire [3:0] fp32_fpcsr;
    
     // Ready and valid signals from modules
    logic bf_in_ready;
    logic bf_out_valid;
    logic fp32_in_ready;
    logic fp32_out_valid;
    logic bf_in_valid;
    logic bf_out_ready;
    logic fp32_in_valid;
    logic fp32_out_ready;
    
    
//    assign bf16tofp32_en = enable & (operation == BF16_TO_FP32_OP);
//    assign fp32tobf16_en = enable & (operation == FP32_TO_BF16_OP);
        

    // Instantiate bf16_to_fp32 module
    bf16_to_fp32 bf16_to_fp32_inst (
        .clk(clk),
        .reset(reset),
        .instruction_enable(bf16tofp32_en),
        .operand_a(operand[15:0]),
        // Handshake signals
        .in_valid_i(bf_in_valid),
        .in_ready_o(bf_in_ready),
        .out_valid_o(bf_out_valid),
        .out_ready_i(bf_out_ready),
        //result signals
        .result(fp32_result),
        .fpcsr(bf16_fpcsr)
    );

    // Instantiate fp32_to_bf16 module
    fp32_to_bf16 fp32_to_bf16_inst (
        .clk(clk),
        .reset(reset),
        .instruction_enable(fp32tobf16_en),
        .operand_a(operand),
        // Handshake signals
        .in_valid_i(fp32_in_valid),
        .in_ready_o(fp32_in_ready),
        .out_valid_o(fp32_out_valid),
        .out_ready_i(fp32_out_ready),
        //result signals
        .result(bf16_result),
        .fpcsr(fp32_fpcsr)
    );

    // Logic to select the appropriate output based on operation
    
    assign result = (operation == BF16_TO_FP32_OP) ? fp32_result :
                (operation == FP32_TO_BF16_OP) ? {16'h0000, bf16_result} :
                32'h00000000;

    assign fpcsr = (operation == BF16_TO_FP32_OP) ? bf16_fpcsr :
                (operation == FP32_TO_BF16_OP) ? fp32_fpcsr :
                4'b0000;



//    // Valid and ready signals for bf16tofp32 and fp32tobf16
//    assign in_ready_o = (bf16tofp32_en ? bf_in_ready :
//                        (fp32tobf16_en ? fp32_in_ready : 1'b0));
    
//    assign out_valid_o = (bf16tofp32_en ? bf_out_valid :
//                         (fp32tobf16_en ? fp32_out_valid : 1'b0));
                         
//    // Selection for conv module
//    assign bf_in_valid = in_valid_i & bf16tofp32_en;
//    assign bf_out_ready = out_ready_i & bf16tofp32_en;
    
//    assign fp32_in_valid = in_valid_i & fp32tobf16_en;
//    assign fp32_out_ready = out_ready_i & fp32tobf16_en;

 always_comb begin
        bf16tofp32_en = enable & (operation == BF16_TO_FP32_OP);
        fp32tobf16_en = enable & (operation == FP32_TO_BF16_OP);

        // Valid and ready signals for bf16tofp32 and fp32tobf16
        in_ready_o = (bf16tofp32_en ? bf_in_ready :
                     (fp32tobf16_en ? fp32_in_ready : 1'b0));
    
        out_valid_o = (bf16tofp32_en ? bf_out_valid :
                      (fp32tobf16_en ? fp32_out_valid : 1'b0));

        // Selection for conv module
        bf_in_valid = in_valid_i & bf16tofp32_en;
        bf_out_ready = out_ready_i & bf16tofp32_en;

        fp32_in_valid = in_valid_i & fp32tobf16_en;
        fp32_out_ready = out_ready_i & fp32tobf16_en;
    end

    
    


endmodule


