module fp32_to_bf16(
    input logic clk,
    input logic reset,
    input logic instruction_enable, // Enable signal for specific instruction type
    input logic [31:0] operand_a,   // FP32 input
     // Input Handshake
    input  logic                     in_valid_i,
    output logic                     in_ready_o,
    // Output handshake
    output logic                     out_valid_o,
    input  logic                     out_ready_i,
    output logic [15:0] result,     // BF16 output
    output logic [3:0] fpcsr        // Floating Point Control and Status Register
);

    // Internal variables
    logic operand_a_sign;
    logic [8:0] operand_a_exp;
    logic [22:0] operand_a_man;
    logic operand_a_inf, operand_a_zero, operand_a_nan, operand_a_subnormal;

    
    logic clkg_en;
    logic valid_pipeline;
    
//    always_latch  begin
//        if(~clk) 
//            clkg_en = instruction_enable;
//        end
           
//    assign gated_clk = clk & clkg_en;
    assign gated_clk = clk && instruction_enable;

    //assign valid_pipeline = (reset && instruction_enable && in_valid_i && out_ready_i) ? 1 : 0;
    
    // Handshake signals
    assign in_ready_o = in_valid_i;
    assign out_valid_o = valid_pipeline ;
    
    // Only execute logic if enabled for this instruction
    always @(posedge gated_clk or negedge reset) begin
        if (!reset ) begin
            result = 0;
            fpcsr = 0;
            valid_pipeline = 0;
        end else if (in_valid_i && out_ready_i) begin
            // Decompose operand
            operand_a_sign = operand_a[31];
            operand_a_exp = {1'b0, operand_a[30:23]};
            operand_a_man = operand_a[22:0];

            // Special case flags
            operand_a_inf = (operand_a_exp == 9'h0FF) && (operand_a_man == 0);
            operand_a_zero = (operand_a_exp == 0) && (operand_a_man == 0);
            operand_a_nan = (operand_a_exp == 9'h0FF) && (operand_a_man != 0);
            operand_a_subnormal = (operand_a_exp == 0) && (operand_a_man != 0);

            // Handle special cases and conversion
            if (operand_a_inf) begin
                result = {operand_a_sign, 8'hFF, 7'h00}; // Infinity
                //fpcsr[2] <= 1; // Set overflow flag
            end else if (operand_a_zero) begin
                result = {operand_a_sign, 8'h00, 7'h00}; // Zero
            end else if (operand_a_nan) begin
                result = {1'b0, 8'hFF, 7'hc0}; // NaN
            end else begin
                result = convert_to_bf16(operand_a_sign, operand_a_exp, operand_a_man);
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

    function automatic [15:0] convert_to_bf16(
        input logic sign,
        input logic [9:0] exp,
        input logic [22:0] man
    );
        logic [9:0] new_exp;
        logic [6:0] new_man;
        logic rounding_bit, sticky_bit, guard_bit, round_up;

        // Alignment for BF16 mantissa (truncate 16 LSBs, keep guard bit)
        guard_bit = man[15];
        rounding_bit = man[14];
        sticky_bit = |man[13:0]; // OR all truncated bits for sticky bit

        // Check for rounding using RNE
        round_up = guard_bit & (sticky_bit | rounding_bit | new_man[0]);

        new_exp = exp; // Adjust exponent from FP32 to BF16 bias
        new_man = man[22:16]; // Truncate mantissa to BF16 precision

        // Apply rounding
        if (round_up) begin
            // Check for overflow in mantissa before incrementing
            if (new_man == 7'h7F) begin
                new_exp = new_exp + 1; // Increment exponent due to mantissa overflow
                new_man = 0; // Reset mantissa to 0 because of overflow
            end else begin
                new_man = new_man + 1; // Increment mantissa
            end
        end

        // Check for exponent overflow or underflow
        if (new_exp >= 9'h0FF) begin
            new_exp = 9'h0FF; // Cap at largest normal value
        end else if (new_exp <= 0) begin
            new_exp = 0; // Subnormals and zero
            new_man = 0;
        end

        // Set inexact if any LSBs are truncated or guard, round, sticky bits are set
        fpcsr[0] = guard_bit | rounding_bit | sticky_bit;

        convert_to_bf16 = {sign, new_exp[7:0], new_man[6:0]}; // Assemble BF16 number
    endfunction
endmodule