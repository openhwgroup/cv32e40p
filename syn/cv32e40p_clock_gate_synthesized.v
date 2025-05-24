/////////////////////////////////////////////////////////////
// Created by: Synopsys DC Ultra(TM) in wire load mode
// Version   : T-2022.03-SP3
// Date      : Sun May 11 17:37:16 2025
/////////////////////////////////////////////////////////////


module cv32e40p_clock_gate ( clk_i, en_i, scan_cg_en_i, clk_o );
  input clk_i, en_i, scan_cg_en_i;
  output clk_o;
  wire   N0, clk_en, N1;

  AND2X1_RVT C19 ( .A1(clk_i), .A2(clk_en), .Y(clk_o) );
  OR2X1_RVT C18 ( .A1(en_i), .A2(scan_cg_en_i), .Y(N0) );
  INVX1_RVT I_0 ( .A(clk_i), .Y(N1) );
  LATCHX1_RVT clk_en_reg ( .CLK(N1), .D(N0), .Q(clk_en) );
endmodule

