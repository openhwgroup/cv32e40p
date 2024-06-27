module bf16_to_fp32(
    input logic clk,
    input logic reset,
    input logic instruction_enable, // Enable signal for specific instruction type
    input logic [15:0] operand_a,   // BF16 input
    // Input Handshake
    input  logic                     in_valid_i,
    output logic                     in_ready_o,
    // Output handshake
    output logic                     out_valid_o,
    input  logic                     out_ready_i,
    output logic [31:0] result,     // FP32 output
    output logic [3:0] fpcsr        // Floating Point Control and Status Register
);

    // Internal variables
    logic operand_a_sign;
    logic [7:0] operand_a_exp; 
    logic [6:0] operand_a_man;
    logic operand_a_inf, operand_a_zero, operand_a_nan;
    logic gated_clk;


    
    logic clkg_en;
    logic valid_pipeline;
    
//    always_latch  begin
//        if(~clk) 
//            clkg_en = instruction_enable;
//        end
           
//    assign gated_clk = clk & clkg_en;

    assign gated_clk = clk && instruction_enable;
    
     // Handshake signals
    assign in_ready_o = in_valid_i;
    assign out_valid_o = valid_pipeline;
    //assign valid_pipeline = (reset && instruction_enable && in_valid_i && out_ready_i) ? 1 : 0;
    
    // Only execute logic if enabled for this instruction
    
    always @(posedge gated_clk or negedge reset) begin
        if (!reset) begin
            result = 0;
            fpcsr = 0;
            valid_pipeline = 0;
        end else if (in_valid_i && out_ready_i) begin
            // Decompose operand
            operand_a_sign = operand_a[15];
            operand_a_exp = operand_a[14:7];
            operand_a_man = operand_a[6:0];

            // Special case flags
            operand_a_inf = (operand_a_exp == 8'hFF) && (operand_a_man == 0);
            operand_a_zero = (operand_a_exp == 0) && (operand_a_man == 0);
            operand_a_nan = (operand_a_exp == 8'hFF) && (operand_a_man != 0);

            // Handle special cases and conversion
            if (operand_a_inf) begin
                result = {operand_a_sign, 8'hFF, 23'h000000}; // Infinity
            end else if (operand_a_zero) begin
                result = {operand_a_sign, 8'h00, 23'h000000}; // Zero
            end else if (operand_a_nan) begin
                result = {1'b0, 8'hFF, {1'b1, 22'h00000}}; // NaN
            end else begin
                result = convert_to_fp32(operand_a_sign, operand_a_exp, operand_a_man);
            end

            // Update fpcsr
            fpcsr[3] = operand_a_nan; // Invalid operation flag
            fpcsr[2] = 0;             // Overflow flag
            fpcsr[1] = 0;             // Underflow flag
            fpcsr[0] = 0;             // Inexact flag
            valid_pipeline = 1;
        end else begin
            valid_pipeline = 0;
        end
    end

    function automatic [31:0] convert_to_fp32(
        input logic sign,
        input logic [7:0] exp,
        input logic [6:0] man
    );
        logic [7:0] new_exp;
        logic [22:0] new_man;

        new_exp = exp; // Directly use exponent from BF16
        new_man = {man, 16'h0000}; // Zero-extend mantissa from BF16 to FP32

        convert_to_fp32 = {sign, new_exp, new_man}; // Assemble FP32 number
    endfunction
endmodule
    
  