module cv32e40p_mult_tb;
 import cv32e40p_pkg::*;
  // Parameters
  localparam DATA_WIDTH = 32;

  // Signals
  reg clk;
  reg rst_n;

  reg        enable_i;
  mul_opcode_e operator_i;

  // integer and short multiplier
  reg        short_subword_i;
  reg [1:0] short_signed_i;

  reg [DATA_WIDTH-1:0] op_a_i;
  reg [DATA_WIDTH-1:0] op_b_i;
  reg [DATA_WIDTH-1:0] op_c_i;

  reg [4:0] imm_i;


  // dot multiplier
  reg [ 1:0] dot_signed_i;
  reg [DATA_WIDTH-1:0] dot_op_a_i;
  reg [DATA_WIDTH-1:0] dot_op_b_i;
  reg [DATA_WIDTH-1:0] dot_op_c_i;
  reg        is_clpx_i;
  reg [ 1:0] clpx_shift_i;
  reg        clpx_img_i;

  wire [DATA_WIDTH-1:0] result_o;

  wire multicycle_o;
  wire mulh_active_o;
  wire ready_o;
  reg  ex_ready_i;

  // Instantiate the module under test
  cv32e40p_mult u_cv32e40p_mult (
    .clk(clk),
    .rst_n(rst_n),
    .enable_i(enable_i),
    .operator_i(operator_i),
    .short_subword_i(short_subword_i),
    .short_signed_i(short_signed_i),
    .op_a_i(op_a_i),
    .op_b_i(op_b_i),
    .op_c_i(op_c_i),
    .imm_i(imm_i),
    .dot_signed_i(dot_signed_i),
    .dot_op_a_i(dot_op_a_i),
    .dot_op_b_i(dot_op_b_i),
    .dot_op_c_i(dot_op_c_i),
    .is_clpx_i(is_clpx_i),
    .clpx_shift_i(clpx_shift_i),
    .clpx_img_i(clpx_img_i),
    .result_o(result_o),
    .multicycle_o(multicycle_o),
    .mulh_active_o(mulh_active_o),
    .ready_o(ready_o),
    .ex_ready_i(ex_ready_i)
  );

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Reset sequence
  initial begin
    rst_n = 0;
    #10;
    rst_n = 1;
  end

  // Helper function to display test case information
  task display_test_case(string test_name);
    $display("================================================================================");
    $display("Test Case: %s", test_name);
    $display("  clk             = %b", clk);
    $display("  rst_n           = %b", rst_n);
    $display("  enable_i        = %b", enable_i);
    $display("  operator_i      = %s", operator_i);
    $display("  short_subword_i = %b", short_subword_i);
    $display("  short_signed_i  = %b", short_signed_i);
    $display("  op_a_i          = %d", op_a_i);
    $display("  op_b_i          = %d", op_b_i);
    $display("  op_c_i          = %d", op_c_i);
    $display("  imm_i           = %d", imm_i);
    $display("  dot_signed_i    = %b", dot_signed_i);
    $display("  dot_op_a_i      = %d", dot_op_a_i);
    $display("  dot_op_b_i      = %d", dot_op_b_i);
    $display("  dot_op_c_i      = %d", dot_op_c_i);
    $display("  is_clpx_i        = %b", is_clpx_i);
    $display("  clpx_shift_i    = %d", clpx_shift_i);
    $display("  clpx_img_i      = %b", clpx_img_i);
    $display("  result_o        = %d", result_o);
    $display("  multicycle_o    = %b", multicycle_o);
    $display("  mulh_active_o    = %b", mulh_active_o);
    $display("  ready_o         = %b", ready_o);
    $display("  ex_ready_i      = %b", ex_ready_i);
  endtask

  // Main testbench logic
  initial begin
    // Initialize signals
    enable_i        = 0;
    operator_i      = MUL_I;
    short_subword_i = 0;
    short_signed_i  = 0;
    op_a_i          = 0;
    op_b_i          = 0;
    op_c_i          = 0;
    imm_i           = 0;
    dot_signed_i    = 0;
    dot_op_a_i      = 0;
    dot_op_b_i      = 0;
    dot_op_c_i      = 0;
    is_clpx_i        = 0;
    clpx_shift_i    = 0;
    clpx_img_i      = 0;
    ex_ready_i      = 1; //default value

    $display("Starting simulation of cv32e40p_mult...");
    rst_n = 0;
    #10;
    rst_n = 1;

    // Test Cases
    // Use the defined enum values.
    // Test Case 1: Basic Integer Multiplication (MUL_I)
    #10;
    display_test_case("Basic Integer Multiplication (MUL_I)");
    enable_i     = 1;
    operator_i   = MUL_I;
    op_a_i       = 5;
    op_b_i       = 10;
    #10;
    enable_i     = 1;
    #20;
    enable_i     = 0;
    #10
    if (result_o == 50) $display("PASS"); else $display("FAIL");

    // Test Case 2: Signed Integer Multiplication (MUL_I)
    #10;
    display_test_case("Signed Integer Multiplication (MUL_I)");
    enable_i     = 1;
    operator_i   = MUL_I;
    op_a_i       = -5;
    op_b_i       = 10;
    #10;
    enable_i     = 0;
    #10;
    if (result_o == -50) $display("PASS"); else $display("FAIL");

    // Test Case 3: Multiplication Accumulate (MUL_MAC32)
    #10;
    display_test_case("Multiplication Accumulate (MUL_MAC32)");
    enable_i     = 1;
    operator_i   = MUL_MAC32;
    op_a_i       = 5;
    op_b_i       = 10;
    op_c_i       = 20;
    #10;
    enable_i     = 0;
    #10;
    if (result_o == 70) $display("PASS"); else $display("FAIL");

    // Test Case 4: Multiplication Subtract (MUL_MSU32)
    #10;
    display_test_case("Multiplication Subtract (MUL_MSU32)");
    enable_i     = 1;
    operator_i   = MUL_MSU32;
    op_a_i       = 5;
    op_b_i       = 10;
    op_c_i       = 100;
    #10;
    enable_i     = 0;
    #10;
    if (result_o == 50) $display("PASS"); else $display("FAIL");

    // Test Case 5: Short Multiplication (MUL_IR)
    #10;
    display_test_case("Short Multiplication (MUL_IR)");
    enable_i        = 1;
    operator_i      = MUL_IR;
    short_subword_i = 1; // Use upper 16 bits
    short_signed_i  = 2'b11;
    op_a_i          = 32'hFFFF_0005;
    op_b_i          = 32'hFFFF_000A;
    imm_i           = 4;
    #10;
    enable_i        = 0;
    #10;
    if(result_o == -80) $display("PASS"); else $display("FAIL");

    // Test Case 6: Half Multiplication (MUL_H)
    #10;
    display_test_case("Half Multiplication (MUL_H)");
    enable_i     = 1;
    operator_i   = MUL_H;
    op_a_i       = 32'h0005_000A;
    op_b_i       = 32'h0014_001E;
    short_signed_i = 2'b00;
    ex_ready_i    = 0;
    #10;
    ex_ready_i = 1;
    enable_i     = 0;
    #10;
    if (result_o == 20) $display("PASS"); else $display("FAIL");

    // Test Case 7: Dot Product 8-bit (MUL_DOT8)
    #10;
    display_test_case("Dot Product 8-bit (MUL_DOT8)");
    enable_i     = 1;
    operator_i   = MUL_DOT8;
    dot_signed_i = 2'b11;
    dot_op_a_i   = 32'h7F_7F_7F_7F;
    dot_op_b_i   = 32'h7F_7F_7F_7F;
    dot_op_c_i   = 32'h00_00_00_0A;
    #10;
    enable_i     = 0;
    #10;
    if (result_o == 8010) $display("PASS"); else $display("FAIL");

    // Test Case 8: Dot Product 16-bit (MUL_DOT16)
    #10;
    display_test_case("Dot Product 16-bit (MUL_DOT16)");
    enable_i     = 1;
    operator_i   = MUL_DOT16;
    dot_signed_i = 2'b11;
    dot_op_a_i   = 32'h7FFF_7FFF;
    dot_op_b_i   = 32'h7FFF_7FFF;
    dot_op_c_i   = 32'h0000_000A;
    #10;
    enable_i     = 0;
    #10;
    if (result_o == 2147483658) $display("PASS"); else $display("FAIL");

    // Test Case 9: Complex Multiplication (MUL_DOT16)
    #10;
    display_test_case("Complex Multiplication (MUL_DOT16)");
    enable_i     = 1;
    operator_i   = MUL_DOT16;
    dot_signed_i = 2'b11;
    dot_op_a_i   = 32'h0003_0002; // a_real, a_imag
    dot_op_b_i   = 32'h0007_0005; // b_real, b_imag
    dot_op_c_i   = 32'h000A_000B; // c_real, c_imag
    is_clpx_i     = 1;
    clpx_shift_i  = 2;
    clpx_img_i    = 1;
    #10;
    enable_i     = 0;
    #10;
    if (result_o == 32'h0001_000B) $display("PASS"); else $display("FAIL"); //Expected result  (a_real * b_imag + a_imag * b_real) + c_imag , (a_real * b_real - a_imag * b_imag) + c_real
    // Add more test cases as needed

    $display("Simulation finished.");
    #10 $finish;
  end

   // This is to create a dump file for offline viewing
   initial
     begin
        $fsdbDumpfile("cv32e40p_mult_tb.fsdb");
        $fsdbDumpvars(0, cv32e40p_mult_tb, "+all");
        $dumpfile("cv32e40p_mult_tb.vcd");
        $dumpvars(0);
     end

endmodule

