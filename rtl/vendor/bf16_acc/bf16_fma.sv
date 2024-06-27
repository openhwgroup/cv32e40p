
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06/16/2024 04:46:29 PM
// Design Name: 
// Module Name: fma_RV
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




module bf16_fma_op(
    input logic clk,
    input logic reset,
    input logic en,
    input logic [15:0] op_a,
    input logic [15:0] op_b,
    input logic [15:0] op_c,
    input logic [3:0] oper, // Operation code
    // Input Handshake
    input  logic                     in_valid_i,
    output logic                     in_ready_o,
    // Output handshake
    output logic                     out_valid_o,
    input  logic                     out_ready_i,
    //result signals
    output logic [31:0] result,
    output logic [3:0] fpcsr
);

    // bfloat16 specifications
    localparam EXP_BITS = 8;
    localparam MAN_BITS = 7;
    localparam TOTAL_MAN_BITS = 2 * MAN_BITS + 16 + 2; // Total bits for extended mantissa
    localparam BIAS = 127;
    localparam EXP_WIDTH = EXP_BITS + 2;

    // Decompose operands
    logic [EXP_WIDTH-1:0] exp_a, exp_b;
    logic [MAN_BITS:0] man_a, man_b; // Including implicit bit
    logic [MAN_BITS-1:0] man_c;
//    logic operand_a.sign, operand_b.sign, operand_c.sign;
    logic effective_subtraction;

    
    
    // Product and Sum variables
    logic [TOTAL_MAN_BITS-1:0] aligned_product_mantissa; // Extended product mantissa
    logic [TOTAL_MAN_BITS-1:0] exp_aligned_product_mantissa;
    logic [2*MAN_BITS+1:0] product_mantissa;
    logic [TOTAL_MAN_BITS-1:0] aligned_addend_mantissa;
    logic [TOTAL_MAN_BITS:0] sum_mantissa; // In case of overflow
    logic [TOTAL_MAN_BITS+1:0] aligned_sum_mantissa; // For ground bit
    logic [23:0] result_mantissa; // MSB for overflow
    logic signed [EXP_WIDTH-1:0] product_exp, aligned_addend_exp, sum_exp;
    logic product_sign, sum_sign;
    logic [4:0] count;
    logic [5:0] lzc_cnt;
    logic [5:0] lzc_cnt_one;
    logic [TOTAL_MAN_BITS+1:0] aligned_lzc_mantissa;
    logic [EXP_BITS:0] sum_exp_lzc;
    logic [TOTAL_MAN_BITS:0] current_mantissa;
    logic [EXP_WIDTH-1:0] final_exp;
    logic [EXP_WIDTH-1:0] final_final_exp;
    logic final_sign;
    logic [31:0] final_result_regular;
    
    //pipelined_variables
   logic enable;
   logic [3:0] operation;
   logic [3:0] oper_one;
   logic [TOTAL_MAN_BITS-1:0] aligned_product_mantissa_one; 
   logic [EXP_WIDTH-1:0] product_exp_one;
   logic product_sign_one;
   logic result_is_special_one;
   logic [31:0] special_result_one;
   logic invalid_one;
   logic invalid_two;
   logic is_zero_c_one;
   logic is_sub_c_one;
   logic [TOTAL_MAN_BITS+1:0] aligned_sum_mantissa_one;
   logic [EXP_WIDTH-1:0] sum_exp_one;
   logic is_zero_c_two;
   logic is_sub_c_two;
   logic result_is_special_two;
   logic [31:0] special_result_two;
   logic [31:0] result_regular_one;
   
   
    

    // Rounding variables
    logic guard_bit, round_bit, sticky_bit;
    reg [4:0] i;

    // Special case handling
    logic is_nan_a, is_nan_b, is_nan_c;
    logic is_sub_a, is_sub_b, is_sub_c;
    logic is_inf_a, is_inf_b, is_inf_c;
    logic is_zero_a, is_zero_b, is_zero_c;
    
    logic result_is_special;
    logic [31:0] result_special;
    logic [31:0] result_regular;
    logic [31:0] result_o;
    logic invalid;
    logic overflow;
    logic underflow;
    logic inexact;
    logic clk_one;
    
    logic valid_pipeline;
    logic valid_pipeline_one;
    logic valid_pipeline_two;
    logic valid_pipeline_three;
    
    
    
    //Type definition
    typedef struct packed {
    logic                sign;
    logic [EXP_BITS-1:0] exponent;
    logic [MAN_BITS-1:0] mantissa;
  } fp_t;

    
//    assign clk_one = clk & enable;

    fp_t operand_a, operand_b, operand_c;
    fp_t oper_a, oper_b, oper_c;
    //pipelined fp_t variables
    fp_t operand_c_one;
    
    logic clkg_en;

    always_latch  begin
     if(~clk) 
        clkg_en = enable;
    end
       
    assign gated_clk = clk & clkg_en;

    //assign gated_clk = clk && enable;
    
    assign in_ready_o = valid_pipeline_three;
    assign out_valid_o = valid_pipeline_three;
    
    always @(posedge gated_clk or negedge reset) begin
    
    if(!reset) begin
        oper_a <= 0;
        oper_b <= 0;
        oper_c <= 0;
        oper_one <= 0; 
        valid_pipeline <= 0;
    end
    else if (in_valid_i) begin
        oper_a <= op_a;
        oper_b <= op_b;
        oper_c <= op_c;
        oper_one <= oper;
        enable <= en;
        valid_pipeline <= in_valid_i;
//    
//        operand_a = op_a;
//        operand_b = op_b;
//        operand_c = op_c;
        
    //    exp_a = operand_a.exponent;
    //    exp_b = operand_b.exponent;
    //    exp_c = operand_c.exponent;
    //    man_a = {1'b1, operand_a.mantissa}; // Include implicit bit
    //    man_b = {1'b1, operand_b.mantissa};
    //    man_c = operand_c.mantissa;
    //    i = 0;
    //    fpcsr = 0;
        
        // Adjust operands based on the operation
         
         
       end  
 end
    
  always_comb begin
  
       operand_a = oper_a;
       operand_b = oper_b;
       operand_c = oper_c;
       operation = oper_one;
  
       case (operation)
                4'b0111: ; // FMADD: Do nothing
                4'b1000: operand_c.sign = ~operand_c.sign; // FMSUB: Invert sign of operand C
                4'b1010: operand_a.sign = ~operand_a.sign; // FNMSUB: Invert sign of operand A
                4'b1001: begin // FNMADD: Invert sign of operands A and C
                    operand_a.sign = ~operand_a.sign;
                    operand_c.sign = ~operand_c.sign;
                end
                4'b0100: begin // ADD: Set operand A to +1.0
    //                exp_a = BIAS;
    //                man_a = {1'b1, {MAN_BITS{1'b0}}};
    //                operand_a.sign = 1'b0;
                    operand_a = '{sign: 1'b0, exponent: BIAS, mantissa: '0};
                end
                4'b0110: begin // SUB: Set operand A to +1.0, invert sign of operand C
    //                exp_a = BIAS;
    //                man_a = {1'b1, {MAN_BITS{1'b0}}};
    //                operand_a.sign = 1'b0;
                    operand_c.sign = ~operand_c.sign;
                    operand_a = '{sign: 1'b0, exponent: BIAS, mantissa: '0};
                end
                4'b0101: begin // MUL: Set operand C to +0.0
    //                exp_c = 0;
    //                man_c = {MAN_BITS{1'b0}};
    //                operand_c.sign = 1'b0;
                    operand_c = '{sign: 1'b0, exponent: '0, mantissa: '0};
                end
                default: ; // Other operations: no change
         endcase
    
       man_a = {1'b1, operand_a.mantissa}; // Include implicit bit
       man_b = {1'b1, operand_b.mantissa};
       man_c = operand_c.mantissa;
       
        is_nan_a = operand_a.exponent == 8'hFF && man_a[6:0] != 0;
        is_nan_b = operand_b.exponent == 8'hFF && man_b[6:0]  != 0;
        is_nan_c = operand_c.exponent == 8'hFF && man_c[6:0]  != 0;
    
        is_inf_a = operand_a.exponent == 8'hFF && man_a[6:0]  == 0;
        is_inf_b = operand_b.exponent == 8'hFF && man_b[6:0]  == 0;
        is_inf_c = operand_c.exponent == 8'hFF && man_c[6:0]  == 0;
    
        is_zero_a = operand_a.exponent == 0 && man_a[6:0]  == 0;
        is_zero_b = operand_b.exponent == 0 && man_b[6:0]  == 0;
        is_zero_c = operand_c.exponent == 0 && man_c[6:0]  == 0;
        
        is_sub_a = operand_a.exponent == 0 && man_a[6:0] != 0;
        is_sub_b = operand_b.exponent == 0 && man_b[6:0] != 0;
        is_sub_c = operand_c.exponent == 0 && man_c[6:0] != 0;
        
        if(is_sub_a) begin is_zero_a = 1'b1; end 
        if(is_sub_b) begin is_zero_b = 1'b1; end 
        if(is_sub_c) begin is_zero_c = 1'b1; operand_c = 0; end 
        
            
    end


            // Detect special cases
  always_comb begin
            
           //result_is_special = 1'b0;
           invalid = 1'b0; 

            // Determine if the result should be special (NaN or Infinity or irect jump to operand_c because of 0 operand value)
           result_is_special = is_nan_a || is_nan_b || is_nan_c ||
                                (is_inf_a && is_zero_b) || (is_inf_b && is_zero_a) ||
                                ((is_inf_a || is_inf_b) && is_inf_c && effective_subtraction) || (is_inf_a || is_inf_b || is_inf_c) || (is_sub_a || is_sub_b || is_zero_a || is_zero_b) ; 
           if (is_nan_a || is_nan_b || is_nan_c || ((is_inf_a && is_zero_b) || (is_inf_b && is_zero_a) || ((is_inf_a || is_inf_b) && is_inf_c && effective_subtraction))) begin
                    result_special = 32'h7FC00000; // Canonical qNaN for bfloat16
                    invalid = 1; // NV flag for NaN or invalid operation
           end else if (is_inf_a || is_inf_b || is_inf_c) begin
                    if (is_inf_a || is_inf_b) begin
                        // Result is infinity with the sign of the product
                        result_special = {operand_a.sign ^ operand_b.sign, 8'hFF, 23'h000000}; // Infinity with sign of the product
                    end else if (is_inf_c) begin
                        // Result is infinity with the sign of the addend (= operand_c)
                        result_special = {operand_c.sign, 8'hFF, 23'b000000}; // Infinity with sign of the addend
                    end
            end 
            else if (is_sub_a || is_sub_b || is_zero_a || is_zero_b)
            begin
                 result_special = {operand_c, 16'h0000};
            end
//            else begin
//                result_is_special =1'b0;
//            end
        end

            
   always_comb begin
                // FMA computation logic
     
        
        exp_a = operand_a.exponent;
        exp_b = operand_b.exponent;
        
          
            // Calculate product of a and b with extended mantissa
            product_mantissa = man_a * man_b;
            product_exp = exp_a + exp_b - signed'(BIAS);
            if(product_exp <= 0) begin
                product_exp = 0;
                product_mantissa = 0;
                product_sign = 1;
            end
            if (product_mantissa[2*MAN_BITS+1] == 1) begin
                product_exp = product_exp + 1;
            end
            else begin
                product_mantissa = product_mantissa << 1;
            end
            aligned_product_mantissa = {product_mantissa, 16'b0};
         
        //product_exp = exp_a + exp_b - BIAS;
        product_sign = operand_a.sign ^ operand_b.sign;
        
    end
        
    always @(posedge gated_clk) begin
    
        aligned_product_mantissa_one <= aligned_product_mantissa;
        product_exp_one <= product_exp;
        product_sign_one <= product_sign;
        operand_c_one <=  operand_c;
        special_result_one <= result_special;
        result_is_special_one <= result_is_special;
        is_zero_c_one <= is_zero_c;
        is_sub_c_one <= is_sub_c; 
        invalid_one <= invalid;
        valid_pipeline_one <= valid_pipeline;
        
    
    end
    
    
         
    always_comb begin
        
        if (is_zero_c_one || is_sub_c_one) begin
            result_regular = {product_sign_one, product_exp_one[7:0], aligned_product_mantissa_one[TOTAL_MAN_BITS-1:TOTAL_MAN_BITS-7]};
        end
    
        // Align addend (operand_c) with product
        aligned_addend_exp = operand_c_one.exponent;
        aligned_addend_mantissa = {1'b1, operand_c_one.mantissa, {(TOTAL_MAN_BITS - MAN_BITS - 1){1'b0}}}; // Extend addend mantissa
        exp_aligned_product_mantissa = aligned_product_mantissa_one;
    
        // Align addend exponent with product exponent
        if (aligned_addend_exp != product_exp_one) begin
            if (aligned_addend_exp < product_exp_one) begin
                aligned_addend_mantissa = aligned_addend_mantissa >> (product_exp_one - aligned_addend_exp);
                aligned_addend_exp = product_exp_one;
            end else begin
                exp_aligned_product_mantissa = aligned_product_mantissa_one >> (aligned_addend_exp - product_exp_one);
                //product_exp_one = aligned_addend_exp;
            end
            
        end
        // Determine if operation is effectively a subtraction
        effective_subtraction = (product_sign_one != operand_c_one.sign);
        
        // Add/Subtract product and addend
        

        // Compute sum mantissa and sum sign
        if (effective_subtraction && exp_aligned_product_mantissa < aligned_addend_mantissa) begin
            sum_mantissa = aligned_addend_mantissa - exp_aligned_product_mantissa;
            sum_sign = operand_c_one.sign;
        end else begin
            sum_mantissa = exp_aligned_product_mantissa + aligned_addend_mantissa;
            sum_sign = product_sign_one;
        end
        
        // Update sum exponent
       
        
        
         sum_exp = aligned_addend_exp;
        
        // Shift sum mantissa
        aligned_sum_mantissa = {sum_mantissa, 1'b0};
        if (aligned_sum_mantissa[TOTAL_MAN_BITS+1] == 1'b1) begin
            sum_exp = sum_exp + 1;
            aligned_sum_mantissa = aligned_sum_mantissa >> 1;
        end
        else if (aligned_sum_mantissa == 0) begin
            sum_exp = 0;
        end
        
    end
        
    
        always @(posedge gated_clk)
        begin
            aligned_sum_mantissa_one <= aligned_sum_mantissa;
            final_sign <= sum_sign;
            //current_mantissa_one <= current_mantissa;
            sum_exp_one <= sum_exp;
            special_result_two <= special_result_one;
            result_is_special_two <= result_is_special_one;
            is_zero_c_two <= is_zero_c_one;
            is_sub_c_two <= is_sub_c_one;
            result_regular_one <= result_regular; 
            invalid_two <= invalid_one;
            valid_pipeline_two <= valid_pipeline_one;
            
         
        end
       // assign aligned_lzc_mantissa = (!aligned_sum_mantissa_one[TOTAL_MAN_BITS]) ? (aligned_sum_mantissa_one << (lzc_cnt + 1)) : aligned_sum_mantissa_one;
     //assign final_final_exp = (!aligned_sum_mantissa_one[TOTAL_MAN_BITS]) ? (sum_exp_one - (lzc_cnt + 1)) : sum_exp_one;
        
        clz #(TOTAL_MAN_BITS) u_clz(
         .ref_vector(aligned_sum_mantissa_one[TOTAL_MAN_BITS-1:0]),.dout(lzc_cnt)
     );
     
        
        
        always_comb begin
        final_exp = sum_exp_one; 
        //current_mantissa = aligned_sum_mantissa[TOTAL_MAN_BITS:0];
        lzc_cnt_one = lzc_cnt + 1;
        aligned_lzc_mantissa=aligned_sum_mantissa_one;
        if (!aligned_sum_mantissa_one[TOTAL_MAN_BITS]) begin
        aligned_lzc_mantissa = aligned_sum_mantissa_one << (lzc_cnt_one);
        final_exp = sum_exp_one - (lzc_cnt_one);
        end
    
  
        
        
        //always_comb begin
        
       
        //else begin
//        while (i < TOTAL_MAN_BITS && sum_exp > 0 && !aligned_sum_mantissa[TOTAL_MAN_BITS]) begin
//             aligned_sum_mantissa = aligned_sum_mantissa << 1;
//             sum_exp = sum_exp - 1;
//             i = i + 1;
//        end

//        end
        
//        count = 0;
        
//        for (i = 0; i < TOTAL_MAN_BITS && sum_exp > 0 && !aligned_sum_mantissa[TOTAL_MAN_BITS]; i = i + 1) begin
//        aligned_sum_mantissa = aligned_sum_mantissa << 1;
//        sum_exp = sum_exp - 1;
//        count = count + 1;
//        end
        
        //final_exp = sum_exp_one; 
        final_result_regular = result_regular_one;
     //end
     //end
     

        
//        while (sum_mantissa[TOTAL_MAN_BITS - 1] == 0 && sum_exp > 0 ) begin
//            sum_mantissa = sum_mantissa << 1;
//            sum_exp = sum_exp - 1;
//        end
           
     //always_comb begin      
        guard_bit = aligned_lzc_mantissa[TOTAL_MAN_BITS - 24];
        round_bit = aligned_lzc_mantissa[TOTAL_MAN_BITS - 25];
        sticky_bit = |aligned_lzc_mantissa[TOTAL_MAN_BITS - 26:0]; // OR all bits below round bit
        result_mantissa = aligned_lzc_mantissa[TOTAL_MAN_BITS - 1:TOTAL_MAN_BITS - 23];
        if (guard_bit && (round_bit || sticky_bit) || ((aligned_lzc_mantissa[TOTAL_MAN_BITS - 23]) && guard_bit && !round_bit && !sticky_bit ) ) begin
            
            if (result_mantissa == 23'h7FFFFF) begin
                final_exp = final_exp + 1; // Increment exponent due to mantissa overflow
                result_mantissa = 0; // Reset mantissa to 0 because of overflow
            end else begin
                result_mantissa = result_mantissa + 1; // Increment mantissa
            end 
        end
        
                
        
        
//        // Round (Round to Nearest, ties to Even)
//        round_bit = aligned_sum_mantissa[0];
//        sticky_bit = |aligned_sum_mantissa[TOTAL_MAN_BITS - 1:0]; // OR all bits below round bit
//        result_mantissa = aligned_sum_mantissa[TOTAL_MAN_BITS - 1:TOTAL_MAN_BITS - 7];
//        if (round_bit && (aligned_sum_mantissa[MAN_BITS] || sticky_bit)) begin
//            result_mantissa = result_mantissa + 1;
//   
//         if (result_mantissa[MAN_BITS]) begin               
//                sum_exp = sum_exp + 1;
//            end
//        end
        {overflow, underflow, inexact} = {0,0,0};
        // Handle overflow and underflow
        if (final_exp >= 2**EXP_BITS - 1) begin
            //fpcsr[2]
            overflow = 1'b1;
            final_result_regular = {final_sign, 8'hFF, 23'h000000}; // Infinity
        end else if (final_exp <= 0) begin
            //fpcsr[1]
            underflow = 1'b1;
            inexact = 1'b1;
            final_result_regular = {final_sign, 8'h00, 23'h000000}; // Zero (subnormals flushed to zero)
        end else begin
            final_result_regular = {final_sign, final_exp[7:0], result_mantissa[22:0]};
        end

        // Set inexact flag if any of the lower bits were non-zero
        //fpcsr[0]
         inexact = guard_bit || round_bit || sticky_bit;
        //invalid = 0; // No invalid operation in simple FMA
    
    end
    
    
    
    always_comb begin
        if (result_is_special_two) begin
            result_o = special_result_two;
            end
        else begin
            result_o = final_result_regular;
        end
        if (result_o[30:23] == 8'b0 && result_o[22:0] != 0) begin result_o = 0; end
    end
    
    always @(posedge gated_clk or negedge reset) begin
    if(!reset) begin
        result <= 0;
        fpcsr <= 0;
    end
    else begin
        
        result <= result_o;
        fpcsr <= {invalid_two, overflow, underflow, inexact};
        valid_pipeline_three <= valid_pipeline_two;
    
    end
    end
    
 endmodule  
    
    