
bind cv32e40p_top insn_assert u_insn_assert (
    .clk_i(clk_i),
    .rst_ni(rst_ni),

    .instr_req_o   (instr_req_o),
    .instr_gnt_i   (instr_gnt_i),
    .instr_rvalid_i(instr_rvalid_i)
);

bind cv32e40p_top data_assert u_data_assert (
    .clk_i(clk_i),
    .rst_ni(rst_ni),

    .data_req_o   (data_req_o   ),
    .data_gnt_i   (data_gnt_i   ),
    .data_rvalid_i(data_rvalid_i)
);
