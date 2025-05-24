// Testbench module
module clock_gate_tb;

    // Declare signals for the testbench
    logic clk;
    logic enable;
    logic scan_cg_en_i;
    logic gated_clk;

    // Instantiate the clock gating module (DUT)
    cv32e40p_clock_gate dut (
        .clk_i(clk),
        .en_i(enable),
	.scan_cg_en_i(scan_cg_en_i),
        .clk_o(gated_clk)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // Generate a clock with a period of 10 time units
    end

    // Test stimulus and verification
    initial begin
        // Initialize signals
        enable = 0;
	scan_cg_en_i = 0;

        // Display header
        $display("Time\tClk\tEn\tGated_Clk");
        $monitor("%t\t%b\t%b\t%b", $time, clk, enable, gated_clk);

        // Test case 1: enable = 0, gated_clk should be 0
        #20;  // Wait for 2 clock cycles
        enable = 0;
        #10;

        // Test case 2: enable = 1, gated_clk should follow clk
        enable = 1;
        #20;  // Wait for 2 clock cycles

        // Test case 3: enable toggles when clk is high
        enable = 0;
        #5;  //clk is high
        enable = 1;
        #10;

        // Test case 4: enable toggles when clk is low
        enable = 0;
        #5; //clk is low
        enable = 1;
        #10;

        // Test case 5: enable = 0, gated_clk should be 0
        enable = 0;
        #20;

        // Finish simulation
        #10 $finish;
    end

    //Assertions (Optional, but highly recommended for thorough verification)
    initial begin
        //check gated_clk is 0 when enable is 0
        assert property (
            @(posedge clk) disable iff(!clk) enable == 0 -> gated_clk == 0
        ) else $error("Error: gated_clk is not zero when enable is zero");

       //check gated_clk follows clk when enable is 1
        assert property (
            @(posedge clk) disable iff(!clk) enable == 1 -> gated_clk == clk
        ) else $error("Error: gated_clk does not follow clk when enable is one");
    end

    // This is to create a dump file for offline viewing
    initial begin
        $fsdbDumpfile("clock_gate_tb.fsdb");
        $fsdbDumpvars(0, clock_gate_tb);
        $dumpfile("cv32e40p_clock_gate_tb.vcd");
        $dumpvars(0);
     end

endmodule
