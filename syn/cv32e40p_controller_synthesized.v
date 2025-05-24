/////////////////////////////////////////////////////////////
// Created by: Synopsys DC Ultra(TM) in wire load mode
// Version   : T-2022.03-SP3
// Date      : Sun May 11 16:34:29 2025
/////////////////////////////////////////////////////////////


module cv32e40p_controller ( clk, clk_ungated_i, rst_n, fetch_enable_i, 
        ctrl_busy_o, is_decoding_o, is_fetch_failed_i, deassert_we_o, 
        illegal_insn_i, ecall_insn_i, mret_insn_i, uret_insn_i, dret_insn_i, 
        mret_dec_i, uret_dec_i, dret_dec_i, wfi_i, ebrk_insn_i, fencei_insn_i, 
        csr_status_i, hwlp_mask_o, instr_valid_i, instr_req_o, pc_set_o, 
        pc_mux_o, exc_pc_mux_o, trap_addr_mux_o, pc_id_i, hwlp_start_addr_i, 
        hwlp_end_addr_i, hwlp_counter_i, hwlp_dec_cnt_o, hwlp_jump_o, 
        hwlp_targ_addr_o, data_req_ex_i, data_we_ex_i, data_misaligned_i, 
        data_load_event_i, data_err_i, data_err_ack_o, mult_multicycle_i, 
        apu_en_i, apu_read_dep_i, apu_read_dep_for_jalr_i, apu_write_dep_i, 
        apu_stall_o, branch_taken_ex_i, ctrl_transfer_insn_in_id_i, 
        ctrl_transfer_insn_in_dec_i, irq_req_ctrl_i, irq_sec_ctrl_i, 
        irq_id_ctrl_i, irq_wu_ctrl_i, current_priv_lvl_i, irq_ack_o, irq_id_o, 
        exc_cause_o, debug_mode_o, debug_cause_o, debug_csr_save_o, 
        debug_req_i, debug_single_step_i, debug_ebreakm_i, debug_ebreaku_i, 
        trigger_match_i, debug_p_elw_no_sleep_o, debug_wfi_no_sleep_o, 
        debug_havereset_o, debug_running_o, debug_halted_o, wake_from_sleep_o, 
        csr_save_if_o, csr_save_id_o, csr_save_ex_o, csr_cause_o, 
        csr_irq_sec_o, csr_restore_mret_id_o, csr_restore_uret_id_o, 
        csr_restore_dret_id_o, csr_save_cause_o, regfile_we_id_i, 
        regfile_alu_waddr_id_i, regfile_we_ex_i, regfile_waddr_ex_i, 
        regfile_we_wb_i, regfile_alu_we_fw_i, operand_a_fw_mux_sel_o, 
        operand_b_fw_mux_sel_o, operand_c_fw_mux_sel_o, reg_d_ex_is_reg_a_i, 
        reg_d_ex_is_reg_b_i, reg_d_ex_is_reg_c_i, reg_d_wb_is_reg_a_i, 
        reg_d_wb_is_reg_b_i, reg_d_wb_is_reg_c_i, reg_d_alu_is_reg_a_i, 
        reg_d_alu_is_reg_b_i, reg_d_alu_is_reg_c_i, halt_if_o, halt_id_o, 
        misaligned_stall_o, jr_stall_o, load_stall_o, id_ready_i, id_valid_i, 
        ex_valid_i, wb_ready_i, perf_pipeline_stall_o );
  output [3:0] pc_mux_o;
  output [2:0] exc_pc_mux_o;
  output [1:0] trap_addr_mux_o;
  input [31:0] pc_id_i;
  input [63:0] hwlp_start_addr_i;
  input [63:0] hwlp_end_addr_i;
  input [63:0] hwlp_counter_i;
  output [1:0] hwlp_dec_cnt_o;
  output [31:0] hwlp_targ_addr_o;
  input [1:0] ctrl_transfer_insn_in_id_i;
  input [1:0] ctrl_transfer_insn_in_dec_i;
  input [4:0] irq_id_ctrl_i;
  input [1:0] current_priv_lvl_i;
  output [4:0] irq_id_o;
  output [4:0] exc_cause_o;
  output [2:0] debug_cause_o;
  output [5:0] csr_cause_o;
  input [5:0] regfile_alu_waddr_id_i;
  input [5:0] regfile_waddr_ex_i;
  output [1:0] operand_a_fw_mux_sel_o;
  output [1:0] operand_b_fw_mux_sel_o;
  output [1:0] operand_c_fw_mux_sel_o;
  input clk, clk_ungated_i, rst_n, fetch_enable_i, is_fetch_failed_i,
         illegal_insn_i, ecall_insn_i, mret_insn_i, uret_insn_i, dret_insn_i,
         mret_dec_i, uret_dec_i, dret_dec_i, wfi_i, ebrk_insn_i, fencei_insn_i,
         csr_status_i, instr_valid_i, data_req_ex_i, data_we_ex_i,
         data_misaligned_i, data_load_event_i, data_err_i, mult_multicycle_i,
         apu_en_i, apu_read_dep_i, apu_read_dep_for_jalr_i, apu_write_dep_i,
         branch_taken_ex_i, irq_req_ctrl_i, irq_sec_ctrl_i, irq_wu_ctrl_i,
         debug_req_i, debug_single_step_i, debug_ebreakm_i, debug_ebreaku_i,
         trigger_match_i, regfile_we_id_i, regfile_we_ex_i, regfile_we_wb_i,
         regfile_alu_we_fw_i, reg_d_ex_is_reg_a_i, reg_d_ex_is_reg_b_i,
         reg_d_ex_is_reg_c_i, reg_d_wb_is_reg_a_i, reg_d_wb_is_reg_b_i,
         reg_d_wb_is_reg_c_i, reg_d_alu_is_reg_a_i, reg_d_alu_is_reg_b_i,
         reg_d_alu_is_reg_c_i, id_ready_i, id_valid_i, ex_valid_i, wb_ready_i;
  output ctrl_busy_o, is_decoding_o, deassert_we_o, hwlp_mask_o, instr_req_o,
         pc_set_o, hwlp_jump_o, data_err_ack_o, apu_stall_o, irq_ack_o,
         debug_mode_o, debug_csr_save_o, debug_p_elw_no_sleep_o,
         debug_wfi_no_sleep_o, debug_havereset_o, debug_running_o,
         debug_halted_o, wake_from_sleep_o, csr_save_if_o, csr_save_id_o,
         csr_save_ex_o, csr_irq_sec_o, csr_restore_mret_id_o,
         csr_restore_uret_id_o, csr_restore_dret_id_o, csr_save_cause_o,
         halt_if_o, halt_id_o, misaligned_stall_o, jr_stall_o, load_stall_o,
         perf_pipeline_stall_o;
  wire   N30, N52, N53, N56, N57, N61, N83, N84, n483, data_misaligned_i,
         jump_done_q, jump_in_dec, ebrk_force_debug_mode, illegal_insn_q,
         debug_req_entry_q, debug_force_wakeup_q, N89, N90, N91, N92, N93, N94,
         N96, N97, N98, N99, N100, N101, N102, N103, N104, N107, N108, N110,
         N111, N112, N113, N114, N115, N123, N124, N125, N126, N127, N129,
         N130, N131, N132, N136, N138, N139, N140, N141, N142, N143, N144,
         N145, N146, N148, N150, N151, N152, N153, N156, N157, N159,
         debug_req_pending, N162, N163, N165, N166, N168, N170, N183, N184,
         wfi_active, N187, N196, N260, N261, N262, N308, N326, N332, N347,
         N362, data_err_q, N384, N415, N418, N434, N436, N448, N451, N454,
         N457, N458, N463, N464, N465, N466, N473, N500, N501, N502, N509,
         N515, N517, N519, N520, N522, N525, N526, N527, N530, N535, N536,
         N538, N541, N567, N568, debug_req_q, N571, N573, N574, N575, N578,
         N579, N582, N583, N589, N709, N718, N721, N722, N723, N726, N727,
         N732, N733, N734, N735, N736, N738, N739, N741, N742, N743, N744,
         N745, N746, N748, N749, N750, N751, N752, N753, N754, N755, N756,
         N757, N758, N760, N761, N763, N95, N694, N693, N678, N675, N674, N652,
         N647, N646, N642, N639, N637, N635, N633, N615, N586, N572, N534,
         N531, N529, N528, N524, N518, N516, N514, N425, N378, N377, N376,
         N375, N369, N346, N289, N264, N263, N199, N188, N179, N178, N118, n1,
         n2, n4, n6, n7, n8, n9, n10, n12, n14, n17, n18, n21, n22, n23, n24,
         n25, n26, n29, n30, n31, n33, n34, n35, n36, n37, n38, n39, n40, n41,
         n42, n43, n44, n45, n46, n47, n48, n49, n52, n53, n54, n55, n56, n57,
         n58, n59, n60, n61, n62, n63, n64, n65, n66, n68, n69, n70, n71, n72,
         n73, n74, n75, n77, n78, n79, n80, n81, n82, n83, n84, n85, n86, n88,
         n89, n90, n93, n94, n95, n96, n97, n98, n99, n100, n101, n102,
         csr_save_ex_o, n105, n106, n107, n111, n112, n113, n114, n115, n116,
         n117, n121, n122, n123, n124, n125, n126, n127, n128, n129, n133,
         n135, n136, n138, n139, n141, n142, n143, n144, n145, n148, n150,
         n153, n154, n156, n157, n158, n159, n160, n161, n162, n163, n164,
         n165, n166, n167, n210, n211, n212, n213, n214, n215, n216, n217,
         n218, n219, n220, n221, n222, n223, n224, n225, n226, n227, n228,
         n229, n230, n231, n232, n233, n234, n235, n236, n237, n238, n239,
         n241, n242, n243, n244, n245, n246, n247, n248, n249, n250, n251,
         n252, n253, n254, n255, n256, n257, n258, n259, n260, n261, n262,
         n263, n264, n265, n266, n267, n268, n269, n270, n271, n272, n273,
         n274, n275, n276, n277, n278, n279, n280, n281, n282, n283, n284,
         n285, n286, n287, n288, n289, n290, n291, n292, n293, n294, n295,
         n296, n297, n298, n299, n300, n301, n302, n303, n304, n305, n306,
         n307, n308, n309, n310, n311, n312, n313, n315, n316, n317, n318,
         n319, n320, n321, n322, n323, n324, n325, n326, n327, n328, n329,
         n330, n331, n332, n333, n334, n335, n336, n337, n338, n339, n340,
         n341, n342, n343, n344, n345, n346, n347, n348, n349, n350, n351,
         n352, n353, n354, n355, n356, n357, n358, n359, n360, n361, n362,
         n363, n364, n365, n366, n367, n368, n369, n370, n371, n372, n373,
         n374, n375, n376, n377, n378, n379, n380, n381, n382, n383, n384,
         n385, n386, n387, n388, n389, n390, n391, n392, n393, n394, n395,
         n396, n397, n398, n399, n400, n401, n402, n403, n404, n405, n406,
         n407, n408, n409, n410, n411, n412, n413, n414, n415, n416, n417,
         n418, n419, n420, n421, n422, n423, n424, n425, n426, n427, n428,
         n429, n430, n431, n432, n433, n434, n435, n436, n437, n438, n439,
         n440, n441, n442, n443, n444, n445, n446, n447, n448, n449, n450,
         n451, n452, n453, n454, n455, n456, n457, n458, n459, n460, n461,
         n462, n463, n464, n465, n466, n467, n468, n469, n470, n471, n472,
         n473, n474, n475, n476, n477, n478, n479, n480, n481, n482;
  wire   [3:0] ctrl_fsm_cs;
  wire   [2:0] debug_fsm_ns;
  assign hwlp_jump_o = 1'b0;
  assign trap_addr_mux_o[1] = 1'b0;
  assign exc_pc_mux_o[2] = 1'b0;
  assign hwlp_mask_o = 1'b0;
  assign hwlp_targ_addr_o[31] = hwlp_start_addr_i[31];
  assign hwlp_targ_addr_o[30] = hwlp_start_addr_i[30];
  assign hwlp_targ_addr_o[29] = hwlp_start_addr_i[29];
  assign hwlp_targ_addr_o[28] = hwlp_start_addr_i[28];
  assign hwlp_targ_addr_o[27] = hwlp_start_addr_i[27];
  assign hwlp_targ_addr_o[26] = hwlp_start_addr_i[26];
  assign hwlp_targ_addr_o[25] = hwlp_start_addr_i[25];
  assign hwlp_targ_addr_o[24] = hwlp_start_addr_i[24];
  assign hwlp_targ_addr_o[23] = hwlp_start_addr_i[23];
  assign hwlp_targ_addr_o[22] = hwlp_start_addr_i[22];
  assign hwlp_targ_addr_o[21] = hwlp_start_addr_i[21];
  assign hwlp_targ_addr_o[20] = hwlp_start_addr_i[20];
  assign hwlp_targ_addr_o[19] = hwlp_start_addr_i[19];
  assign hwlp_targ_addr_o[18] = hwlp_start_addr_i[18];
  assign hwlp_targ_addr_o[17] = hwlp_start_addr_i[17];
  assign hwlp_targ_addr_o[16] = hwlp_start_addr_i[16];
  assign hwlp_targ_addr_o[15] = hwlp_start_addr_i[15];
  assign hwlp_targ_addr_o[14] = hwlp_start_addr_i[14];
  assign hwlp_targ_addr_o[13] = hwlp_start_addr_i[13];
  assign hwlp_targ_addr_o[12] = hwlp_start_addr_i[12];
  assign hwlp_targ_addr_o[11] = hwlp_start_addr_i[11];
  assign hwlp_targ_addr_o[10] = hwlp_start_addr_i[10];
  assign hwlp_targ_addr_o[9] = hwlp_start_addr_i[9];
  assign hwlp_targ_addr_o[8] = hwlp_start_addr_i[8];
  assign hwlp_targ_addr_o[7] = hwlp_start_addr_i[7];
  assign hwlp_targ_addr_o[6] = hwlp_start_addr_i[6];
  assign hwlp_targ_addr_o[5] = hwlp_start_addr_i[5];
  assign hwlp_targ_addr_o[4] = hwlp_start_addr_i[4];
  assign hwlp_targ_addr_o[3] = hwlp_start_addr_i[3];
  assign hwlp_targ_addr_o[2] = hwlp_start_addr_i[2];
  assign hwlp_targ_addr_o[1] = hwlp_start_addr_i[1];
  assign hwlp_targ_addr_o[0] = hwlp_start_addr_i[0];
  assign exc_cause_o[4] = irq_id_o[4];
  assign csr_cause_o[4] = irq_id_o[4];
  assign exc_cause_o[3] = irq_id_o[3];
  assign irq_ack_o = csr_cause_o[5];
  assign misaligned_stall_o = data_misaligned_i;
  assign pc_mux_o[3] = 1'b0;
  assign hwlp_dec_cnt_o[1] = 1'b0;
  assign hwlp_dec_cnt_o[0] = 1'b0;
  assign data_err_ack_o = csr_save_ex_o;

  AND2X1_RVT C2254 ( .A1(wfi_i), .A2(n417), .Y(N652) );
  AND2X1_RVT C2248 ( .A1(uret_insn_i), .A2(n416), .Y(N646) );
  AND2X1_RVT C2244 ( .A1(ecall_insn_i), .A2(n416), .Y(N642) );
  AND2X1_RVT C2239 ( .A1(N530), .A2(n265), .Y(N637) );
  AND2X1_RVT C2237 ( .A1(N527), .A2(n413), .Y(N635) );
  AND2X1_RVT C2235 ( .A1(n340), .A2(n413), .Y(N633) );
  OR2X1_RVT C2195 ( .A1(n237), .A2(n238), .Y(N586) );
  INVX1_RVT I_101 ( .A(debug_req_i), .Y(N572) );
  AND2X1_RVT C2165 ( .A1(mult_multicycle_i), .A2(n45), .Y(N567) );
  AND2X1_RVT C2112 ( .A1(N451), .A2(N454), .Y(N458) );
  AND2X1_RVT C2111 ( .A1(debug_single_step_i), .A2(N448), .Y(N536) );
  AND2X1_RVT C2110 ( .A1(debug_req_entry_q), .A2(N534), .Y(N535) );
  AND2X1_RVT C2109 ( .A1(N531), .A2(n225), .Y(N534) );
  INVX1_RVT I_84 ( .A(trigger_match_i), .Y(N531) );
  AND2X1_RVT C2104 ( .A1(N415), .A2(N528), .Y(N529) );
  AND2X1_RVT C2102 ( .A1(is_fetch_failed_i), .A2(N415), .Y(N527) );
  AND2X1_RVT C2101 ( .A1(ex_valid_i), .A2(N454), .Y(N526) );
  AND2X1_RVT C2100 ( .A1(id_ready_i), .A2(N524), .Y(N525) );
  AND2X1_RVT C2097 ( .A1(ebrk_force_debug_mode), .A2(n293), .Y(N522) );
  AND2X1_RVT C2089 ( .A1(n227), .A2(N514), .Y(N170) );
  INVX1_RVT I_80 ( .A(irq_sec_ctrl_i), .Y(N514) );
  OR2X1_RVT C2048 ( .A1(uret_dec_i), .A2(mret_dec_i), .Y(N425) );
  OR2X1_RVT C2013 ( .A1(csr_status_i), .A2(N377), .Y(N378) );
  OR2X1_RVT C2012 ( .A1(dret_insn_i), .A2(N376), .Y(N377) );
  OR2X1_RVT C2011 ( .A1(uret_insn_i), .A2(N375), .Y(N376) );
  OR2X1_RVT C2010 ( .A1(mret_insn_i), .A2(N346), .Y(N375) );
  INVX1_RVT I_62 ( .A(N346), .Y(N347) );
  OR2X1_RVT C1987 ( .A1(ecall_insn_i), .A2(ebrk_insn_i), .Y(N346) );
  OR2X1_RVT C1969 ( .A1(N262), .A2(N263), .Y(N264) );
  OR2X1_RVT C1968 ( .A1(N261), .A2(N260), .Y(N263) );
  OR2X1_RVT C1918 ( .A1(ebrk_insn_i), .A2(jump_in_dec), .Y(N188) );
  OR2X1_RVT C1899 ( .A1(is_fetch_failed_i), .A2(N178), .Y(N179) );
  OR2X1_RVT C1898 ( .A1(data_err_i), .A2(branch_taken_ex_i), .Y(N178) );
  NBUFFX2_RVT B_84 ( .A(n237), .Y(N84) );
  NBUFFX2_RVT B_83 ( .A(n238), .Y(N83) );
  NBUFFX2_RVT B_57 ( .A(N138), .Y(N57) );
  OR2X1_RVT C120 ( .A1(N139), .A2(N140), .Y(N141) );
  AND2X1_RVT C54 ( .A1(N93), .A2(N94), .Y(N95) );
  OR2X1_RVT C2172 ( .A1(N760), .A2(debug_single_step_i), .Y(N761) );
  OR2X1_RVT C2171 ( .A1(N761), .A2(trigger_match_i), .Y(debug_p_elw_no_sleep_o) );
  INVX1_RVT I_91 ( .A(apu_en_i), .Y(N757) );
  AND2X1_RVT C2140 ( .A1(apu_write_dep_i), .A2(N757), .Y(N758) );
  OR2X1_RVT C2139 ( .A1(apu_read_dep_i), .A2(N758), .Y(apu_stall_o) );
  INVX1_RVT I_86 ( .A(is_decoding_o), .Y(N538) );
  AND2X1_RVT C2080 ( .A1(ebrk_force_debug_mode), .A2(ebrk_insn_i), .Y(N739) );
  OR2X1_RVT C1963 ( .A1(mret_insn_i), .A2(uret_insn_i), .Y(N262) );
  AND2X1_RVT C1961 ( .A1(N736), .A2(ebrk_insn_i), .Y(N261) );
  OR2X1_RVT C1960 ( .A1(illegal_insn_i), .A2(ecall_insn_i), .Y(N260) );
  INVX1_RVT I_44 ( .A(jr_stall_o), .Y(N734) );
  AND2X1_RVT C1926 ( .A1(N734), .A2(N735), .Y(N196) );
  OR2X1_RVT C1913 ( .A1(mret_insn_i), .A2(uret_insn_i), .Y(N733) );
  OR2X1_RVT C1912 ( .A1(N733), .A2(dret_insn_i), .Y(N187) );
  AND2X1_RVT C1806 ( .A1(debug_ebreaku_i), .A2(n227), .Y(N727) );
  AND2X1_RVT C1805 ( .A1(debug_ebreakm_i), .A2(N722), .Y(N726) );
  OR2X1_RVT C1804 ( .A1(N726), .A2(N727), .Y(ebrk_force_debug_mode) );
  OR2X1_RVT C1803 ( .A1(n212), .A2(n222), .Y(jump_in_dec) );
  AND2X1_RVT C1588 ( .A1(current_priv_lvl_i[0]), .A2(current_priv_lvl_i[1]), 
        .Y(N722) );
  AND2X1_RVT C1587 ( .A1(ctrl_transfer_insn_in_id_i[0]), .A2(
        ctrl_transfer_insn_in_id_i[1]), .Y(N721) );
  OR2X1_RVT C1346 ( .A1(N582), .A2(debug_running_o), .Y(N583) );
  OR2X1_RVT C1342 ( .A1(debug_halted_o), .A2(N578), .Y(N579) );
  OR2X1_RVT C1338 ( .A1(debug_halted_o), .A2(debug_running_o), .Y(N575) );
  OR2X1_RVT C119 ( .A1(N91), .A2(n278), .Y(N140) );
  OR2X1_RVT C118 ( .A1(n309), .A2(N89), .Y(N139) );
  OR2X1_RVT C92 ( .A1(n301), .A2(n310), .Y(N123) );
  AND2X1_RVT C53 ( .A1(N91), .A2(n313), .Y(N94) );
  AND2X1_RVT C52 ( .A1(N89), .A2(n309), .Y(N93) );
  DFFARX1_RVT ctrl_fsm_cs_reg_1_ ( .D(N464), .CLK(clk), .RSTB(rst_n), .Q(
        ctrl_fsm_cs[1]), .QN(N91) );
  DFFARX1_RVT jump_done_q_reg ( .D(N568), .CLK(clk), .RSTB(rst_n), .Q(
        jump_done_q), .QN(N735) );
  DFFARX1_RVT data_err_q_reg ( .D(data_err_i), .CLK(clk), .RSTB(rst_n), .Q(
        data_err_q), .QN(N415) );
  DFFARX1_RVT debug_req_q_reg ( .D(n160), .CLK(clk_ungated_i), .RSTB(rst_n), 
        .Q(debug_req_q) );
  DFFARX1_RVT debug_req_entry_q_reg ( .D(n159), .CLK(clk), .RSTB(rst_n), .Q(
        debug_req_entry_q) );
  DFFARX1_RVT illegal_insn_q_reg ( .D(n158), .CLK(clk), .RSTB(rst_n), .Q(
        illegal_insn_q), .QN(n336) );
  DFFASX1_RVT debug_fsm_cs_reg_0_ ( .D(debug_fsm_ns[0]), .CLK(clk), .SETB(
        rst_n), .Q(debug_havereset_o), .QN(N574) );
  AO21X1_RVT U5 ( .A1(ebrk_insn_i), .A2(n102), .A3(n2), .Y(n100) );
  OR2X1_RVT U6 ( .A1(csr_cause_o[5]), .A2(csr_save_ex_o), .Y(n2) );
  AO21X1_RVT U13 ( .A1(N530), .A2(n357), .A3(n6), .Y(n123) );
  AO21X1_RVT U15 ( .A1(wfi_i), .A2(n210), .A3(n7), .Y(n122) );
  OR2X1_RVT U16 ( .A1(csr_status_i), .A2(n230), .Y(n7) );
  OR2X1_RVT U18 ( .A1(N526), .A2(data_err_i), .Y(n8) );
  OR2X1_RVT U20 ( .A1(N526), .A2(data_err_i), .Y(n9) );
  AO21X1_RVT U21 ( .A1(illegal_insn_i), .A2(n251), .A3(n10), .Y(n125) );
  OR2X1_RVT U22 ( .A1(n54), .A2(n126), .Y(n10) );
  AND2X1_RVT U36 ( .A1(n430), .A2(n251), .Y(n17) );
  OA21X1_RVT U37 ( .A1(n83), .A2(trigger_match_i), .A3(n18), .Y(n80) );
  AND2X1_RVT U38 ( .A1(n84), .A2(n82), .Y(n18) );
  AND2X1_RVT U39 ( .A1(csr_cause_o[5]), .A2(N170), .Y(trap_addr_mux_o[0]) );
  AO21X1_RVT U41 ( .A1(n234), .A2(n430), .A3(N61), .Y(n21) );
  NAND4X0_RVT U43 ( .A1(n24), .A2(n25), .A3(n26), .A4(N98), .Y(n22) );
  NOR3X0_RVT U45 ( .A1(csr_cause_o[5]), .A2(n29), .A3(n30), .Y(n24) );
  AO22X1_RVT U46 ( .A1(n31), .A2(N56), .A3(N57), .A4(dret_dec_i), .Y(n30) );
  AND3X1_RVT U49 ( .A1(n35), .A2(jump_in_dec), .A3(n430), .Y(n23) );
  NAND2X0_RVT U51 ( .A1(n26), .A2(n37), .Y(n36) );
  NAND2X0_RVT U54 ( .A1(n39), .A2(n25), .Y(n33) );
  NAND2X0_RVT U55 ( .A1(branch_taken_ex_i), .A2(n40), .Y(n25) );
  NAND2X0_RVT U56 ( .A1(N57), .A2(dret_dec_i), .Y(n39) );
  AND4X1_RVT U57 ( .A1(regfile_we_wb_i), .A2(reg_d_wb_is_reg_c_i), .A3(n41), 
        .A4(n42), .Y(operand_c_fw_mux_sel_o[1]) );
  OR2X1_RVT U58 ( .A1(data_misaligned_i), .A2(n233), .Y(n42) );
  AO221X1_RVT U59 ( .A1(n43), .A2(data_misaligned_i), .A3(n43), .A4(n233), 
        .A5(N567), .Y(operand_c_fw_mux_sel_o[0]) );
  INVX0_RVT U60 ( .A(n41), .Y(n43) );
  NAND2X0_RVT U61 ( .A1(regfile_alu_we_fw_i), .A2(reg_d_alu_is_reg_c_i), .Y(
        n41) );
  AND4X1_RVT U62 ( .A1(regfile_we_wb_i), .A2(reg_d_wb_is_reg_b_i), .A3(n44), 
        .A4(n45), .Y(operand_b_fw_mux_sel_o[1]) );
  NAND2X0_RVT U63 ( .A1(regfile_alu_we_fw_i), .A2(reg_d_alu_is_reg_b_i), .Y(
        n44) );
  AND3X1_RVT U64 ( .A1(regfile_alu_we_fw_i), .A2(reg_d_alu_is_reg_b_i), .A3(
        n45), .Y(operand_b_fw_mux_sel_o[0]) );
  INVX0_RVT U65 ( .A(data_misaligned_i), .Y(n45) );
  AND3X1_RVT U66 ( .A1(regfile_we_wb_i), .A2(n46), .A3(reg_d_wb_is_reg_a_i), 
        .Y(operand_a_fw_mux_sel_o[1]) );
  INVX0_RVT U67 ( .A(operand_a_fw_mux_sel_o[0]), .Y(n46) );
  AO21X1_RVT U68 ( .A1(regfile_alu_we_fw_i), .A2(reg_d_alu_is_reg_a_i), .A3(
        data_misaligned_i), .Y(operand_a_fw_mux_sel_o[0]) );
  AND2X1_RVT U70 ( .A1(N519), .A2(N30), .Y(n47) );
  NAND4X0_RVT U74 ( .A1(n56), .A2(n57), .A3(n58), .A4(n59), .Y(n55) );
  INVX0_RVT U75 ( .A(n60), .Y(n56) );
  AO221X1_RVT U77 ( .A1(N57), .A2(mret_dec_i), .A3(N57), .A4(uret_dec_i), .A5(
        n62), .Y(n29) );
  INVX0_RVT U78 ( .A(n63), .Y(n61) );
  NAND3X0_RVT U79 ( .A1(n64), .A2(n63), .A3(n65), .Y(exc_pc_mux_o[0]) );
  INVX0_RVT U84 ( .A(data_we_ex_i), .Y(n68) );
  AND2X1_RVT U85 ( .A1(irq_id_ctrl_i[1]), .A2(csr_cause_o[5]), .Y(irq_id_o[1])
         );
  AO221X1_RVT U86 ( .A1(N56), .A2(N527), .A3(N56), .A4(n340), .A5(irq_id_o[0]), 
        .Y(exc_cause_o[0]) );
  AND2X1_RVT U87 ( .A1(irq_id_ctrl_i[0]), .A2(csr_cause_o[5]), .Y(irq_id_o[0])
         );
  AO222X1_RVT U89 ( .A1(debug_halted_o), .A2(N84), .A3(n69), .A4(
        debug_halted_o), .A5(n241), .A6(n70), .Y(debug_fsm_ns[2]) );
  OA22X1_RVT U90 ( .A1(N83), .A2(N84), .A3(n442), .A4(N84), .Y(n70) );
  OA22X1_RVT U92 ( .A1(N83), .A2(n239), .A3(n239), .A4(n442), .Y(n72) );
  AO221X1_RVT U94 ( .A1(debug_havereset_o), .A2(n75), .A3(n69), .A4(
        debug_havereset_o), .A5(n220), .Y(debug_fsm_ns[0]) );
  INVX0_RVT U96 ( .A(N589), .Y(n74) );
  AND2X1_RVT U97 ( .A1(N84), .A2(n73), .Y(n75) );
  OA21X1_RVT U102 ( .A1(trigger_match_i), .A2(N535), .A3(n78), .Y(n77) );
  INVX0_RVT U103 ( .A(n79), .Y(n78) );
  NAND4X0_RVT U104 ( .A1(n64), .A2(n80), .A3(n57), .A4(n81), .Y(
        debug_cause_o[0]) );
  NAND2X0_RVT U105 ( .A1(debug_mode_o), .A2(N146), .Y(n81) );
  NAND2X0_RVT U107 ( .A1(N150), .A2(debug_force_wakeup_q), .Y(n84) );
  NAND2X0_RVT U108 ( .A1(N150), .A2(n211), .Y(n82) );
  NOR2X0_RVT U110 ( .A1(n85), .A2(n86), .Y(n64) );
  INVX0_RVT U112 ( .A(N103), .Y(n58) );
  OR4X1_RVT U113 ( .A1(illegal_insn_i), .A2(load_stall_o), .A3(jr_stall_o), 
        .A4(N538), .Y(deassert_we_o) );
  NAND2X0_RVT U120 ( .A1(n449), .A2(wake_from_sleep_o), .Y(n88) );
  NOR3X0_RVT U122 ( .A1(N56), .A2(n62), .A3(n85), .Y(n49) );
  NAND2X0_RVT U123 ( .A1(n89), .A2(n90), .Y(n85) );
  NOR4X1_RVT U124 ( .A1(N111), .A2(N57), .A3(N99), .A4(N52), .Y(n90) );
  NOR4X1_RVT U125 ( .A1(N130), .A2(N126), .A3(n40), .A4(n60), .Y(n89) );
  OR2X1_RVT U126 ( .A1(N142), .A2(n430), .Y(n40) );
  NAND2X0_RVT U127 ( .A1(n454), .A2(n83), .Y(n62) );
  INVX0_RVT U128 ( .A(N146), .Y(n83) );
  NAND3X0_RVT U132 ( .A1(n97), .A2(n98), .A3(n79), .Y(n95) );
  INVX0_RVT U133 ( .A(n99), .Y(n97) );
  AO221X1_RVT U135 ( .A1(n355), .A2(n93), .A3(n355), .A4(n99), .A5(
        debug_csr_save_o), .Y(n101) );
  NAND2X0_RVT U136 ( .A1(n454), .A2(n79), .Y(debug_csr_save_o) );
  NAND2X0_RVT U137 ( .A1(N146), .A2(n355), .Y(n79) );
  AND2X1_RVT U144 ( .A1(csr_cause_o[5]), .A2(irq_sec_ctrl_i), .Y(csr_irq_sec_o) );
  AND2X1_RVT U145 ( .A1(csr_cause_o[5]), .A2(irq_id_ctrl_i[4]), .Y(irq_id_o[4]) );
  AND2X1_RVT U147 ( .A1(csr_cause_o[5]), .A2(irq_id_ctrl_i[3]), .Y(irq_id_o[3]) );
  OR2X1_RVT U148 ( .A1(irq_id_o[2]), .A2(csr_save_ex_o), .Y(csr_cause_o[2]) );
  AND2X1_RVT U150 ( .A1(csr_cause_o[5]), .A2(irq_id_ctrl_i[2]), .Y(irq_id_o[2]) );
  AO221X1_RVT U153 ( .A1(n96), .A2(n337), .A3(n96), .A4(n105), .A5(n106), .Y(
        csr_cause_o[1]) );
  AO22X1_RVT U154 ( .A1(data_we_ex_i), .A2(csr_save_ex_o), .A3(
        irq_id_ctrl_i[1]), .A4(csr_cause_o[5]), .Y(n106) );
  INVX0_RVT U155 ( .A(n107), .Y(n96) );
  NAND2X0_RVT U158 ( .A1(n94), .A2(n98), .Y(csr_cause_o[5]) );
  NAND3X0_RVT U159 ( .A1(N520), .A2(N519), .A3(n430), .Y(n98) );
  NAND2X0_RVT U160 ( .A1(N168), .A2(N111), .Y(n94) );
  OAI21X1_RVT U161 ( .A1(n227), .A2(n331), .A3(n346), .Y(n105) );
  NAND2X0_RVT U163 ( .A1(N53), .A2(N526), .Y(n107) );
  AO22X1_RVT U164 ( .A1(N515), .A2(n430), .A3(data_err_i), .A4(n60), .Y(
        csr_save_ex_o) );
  OR2X1_RVT U165 ( .A1(N61), .A2(N53), .Y(n60) );
  AND2X1_RVT U166 ( .A1(N517), .A2(n430), .Y(n93) );
  OR2X1_RVT U167 ( .A1(N573), .A2(debug_req_i), .Y(N571) );
  INVX1_RVT U169 ( .A(N114), .Y(N502) );
  NAND4X0_RVT U170 ( .A1(n59), .A2(N98), .A3(n111), .A4(n112), .Y(N473) );
  NAND2X0_RVT U171 ( .A1(n414), .A2(wfi_i), .Y(n112) );
  NAND3X0_RVT U172 ( .A1(n230), .A2(debug_force_wakeup_q), .A3(n414), .Y(n111)
         );
  AO222X1_RVT U176 ( .A1(n483), .A2(mret_dec_i), .A3(n269), .A4(uret_dec_i), 
        .A5(n269), .A6(n217), .Y(N434) );
  INVX0_RVT U178 ( .A(N530), .Y(n114) );
  OA221X1_RVT U179 ( .A1(n331), .A2(n356), .A3(n346), .A4(n356), .A5(n116), 
        .Y(n113) );
  AO221X1_RVT U188 ( .A1(n38), .A2(n121), .A3(n290), .A4(n122), .A5(n123), .Y(
        N418) );
  AO22X1_RVT U190 ( .A1(ebrk_insn_i), .A2(n357), .A3(ecall_insn_i), .A4(n357), 
        .Y(n121) );
  AO22X1_RVT U195 ( .A1(n35), .A2(n124), .A3(jump_done_q), .A4(n125), .Y(N332)
         );
  AO22X1_RVT U196 ( .A1(jump_done_q), .A2(n127), .A3(jump_in_dec), .A4(N196), 
        .Y(n124) );
  OR3X1_RVT U198 ( .A1(n243), .A2(ebrk_insn_i), .A3(data_load_event_i), .Y(n53) );
  AND2X1_RVT U204 ( .A1(n48), .A2(n440), .Y(n35) );
  INVX0_RVT U205 ( .A(n138), .Y(n133) );
  OA221X1_RVT U208 ( .A1(ctrl_fsm_cs[2]), .A2(n145), .A3(n128), .A4(n145), 
        .A5(n138), .Y(n144) );
  AND3X1_RVT U214 ( .A1(N384), .A2(id_ready_i), .A3(N721), .Y(n142) );
  AO22X1_RVT U217 ( .A1(illegal_insn_i), .A2(n394), .A3(n232), .A4(n235), .Y(
        n143) );
  NAND2X0_RVT U221 ( .A1(id_ready_i), .A2(n52), .Y(n138) );
  OR2X1_RVT U222 ( .A1(N384), .A2(illegal_insn_i), .Y(n52) );
  OR3X1_RVT U226 ( .A1(N187), .A2(ecall_insn_i), .A3(fencei_insn_i), .Y(n154)
         );
  AND2X1_RVT U228 ( .A1(N519), .A2(n482), .Y(n48) );
  AO21X1_RVT U229 ( .A1(N519), .A2(N520), .A3(n139), .Y(n126) );
  OR2X1_RVT U230 ( .A1(n234), .A2(branch_taken_ex_i), .Y(n139) );
  AND2X1_RVT U240 ( .A1(n156), .A2(n273), .Y(N157) );
  MUX21X1_RVT U243 ( .A1(debug_req_q), .A2(debug_req_i), .S0(N571), .Y(n160)
         );
  HADDX1_RVT U247 ( .A0(regfile_alu_waddr_id_i[0]), .B0(regfile_waddr_ex_i[0]), 
        .SO(n167) );
  HADDX1_RVT U248 ( .A0(regfile_alu_waddr_id_i[4]), .B0(regfile_waddr_ex_i[4]), 
        .SO(n166) );
  HADDX1_RVT U249 ( .A0(regfile_alu_waddr_id_i[3]), .B0(regfile_waddr_ex_i[3]), 
        .SO(n165) );
  HADDX1_RVT U250 ( .A0(regfile_alu_waddr_id_i[5]), .B0(regfile_waddr_ex_i[5]), 
        .SO(n163) );
  HADDX1_RVT U251 ( .A0(regfile_alu_waddr_id_i[1]), .B0(regfile_waddr_ex_i[1]), 
        .SO(n162) );
  HADDX1_RVT U252 ( .A0(regfile_alu_waddr_id_i[2]), .B0(regfile_waddr_ex_i[2]), 
        .SO(n161) );
  OR3X1_RVT U253 ( .A1(n163), .A2(n162), .A3(n161), .Y(n164) );
  NOR4X0_RVT U254 ( .A1(n167), .A2(n166), .A3(n165), .A4(n164), .Y(N541) );
  DFFARX1_RVT ctrl_fsm_cs_reg_3_ ( .D(N466), .CLK(clk), .RSTB(rst_n), .Q(
        ctrl_fsm_cs[3]), .QN(N89) );
  AND2X1_RVT C2241 ( .A1(n290), .A2(n409), .Y(N639) );
  NBUFFX2_RVT B_53 ( .A(n224), .Y(N53) );
  DFFARX1_RVT debug_force_wakeup_q_reg ( .D(n157), .CLK(clk), .RSTB(rst_n), 
        .Q(debug_force_wakeup_q), .QN(N448) );
  DFFARX1_RVT debug_fsm_cs_reg_1_ ( .D(debug_fsm_ns[1]), .CLK(clk), .RSTB(
        rst_n), .Q(debug_running_o), .QN(N578) );
  DFFARX1_RVT debug_fsm_cs_reg_2_ ( .D(debug_fsm_ns[2]), .CLK(clk), .RSTB(
        rst_n), .Q(debug_halted_o), .QN(N582) );
  DFFARX1_RVT ctrl_fsm_cs_reg_0_ ( .D(N463), .CLK(clk), .RSTB(rst_n), .Q(
        ctrl_fsm_cs[0]), .QN(N92) );
  AND2X1_RVT C2277 ( .A1(n234), .A2(n436), .Y(N675) );
  INVX1_RVT U191 ( .A(N369), .Y(n38) );
  AND2X1_RVT C2296 ( .A1(n371), .A2(N693), .Y(N694) );
  OR2X1_RVT C67 ( .A1(n425), .A2(n271), .Y(N104) );
  INVX1_RVT U98 ( .A(n241), .Y(n73) );
  DFFARX1_RVT ctrl_fsm_cs_reg_2_ ( .D(N465), .CLK(clk), .RSTB(rst_n), .Q(
        ctrl_fsm_cs[2]), .QN(N90) );
  DFFARX1_RVT debug_mode_q_reg ( .D(N509), .CLK(clk), .RSTB(rst_n), .Q(n483), 
        .QN(n34) );
  INVX1_RVT U241 ( .A(fetch_enable_i), .Y(n156) );
  INVX1_RVT I_7 ( .A(ctrl_transfer_insn_in_dec_i[0]), .Y(N723) );
  AND2X1_RVT C2120 ( .A1(data_req_ex_i), .A2(regfile_we_ex_i), .Y(N742) );
  AND2X1_RVT C2135 ( .A1(regfile_we_ex_i), .A2(reg_d_ex_is_reg_a_i), .Y(N753)
         );
  OR2X1_RVT C2124 ( .A1(reg_d_ex_is_reg_a_i), .A2(reg_d_ex_is_reg_b_i), .Y(
        N745) );
  AND2X1_RVT C2136 ( .A1(regfile_alu_we_fw_i), .A2(reg_d_alu_is_reg_a_i), .Y(
        N755) );
  OR2X1_RVT C2123 ( .A1(N745), .A2(reg_d_ex_is_reg_c_i), .Y(N746) );
  OR2X1_RVT C2133 ( .A1(N752), .A2(N753), .Y(N754) );
  AND2X1_RVT C2121 ( .A1(N709), .A2(regfile_we_wb_i), .Y(N743) );
  AND2X1_RVT C2091 ( .A1(N308), .A2(N454), .Y(N516) );
  AND2X1_RVT C2092 ( .A1(is_fetch_failed_i), .A2(N516), .Y(N517) );
  OR2X1_RVT C2132 ( .A1(N754), .A2(N755), .Y(N756) );
  AND2X1_RVT C2093 ( .A1(N516), .A2(N528), .Y(N518) );
  OR2X1_RVT C2119 ( .A1(N742), .A2(N743), .Y(N744) );
  OR2X1_RVT C126 ( .A1(N91), .A2(n313), .Y(N144) );
  OR2X1_RVT C1904 ( .A1(debug_req_pending), .A2(trigger_match_i), .Y(N732) );
  OR2X1_RVT U30 ( .A1(N517), .A2(N515), .Y(n14) );
  INVX0_RVT I_53 ( .A(ebrk_force_debug_mode), .Y(N736) );
  OR2X1_RVT C94 ( .A1(N123), .A2(N124), .Y(N125) );
  OR2X1_RVT C138 ( .A1(N89), .A2(n288), .Y(N151) );
  OR2X1_RVT C99 ( .A1(n425), .A2(n288), .Y(N127) );
  AO21X1_RVT U29 ( .A1(N30), .A2(N519), .A3(n14), .Y(n54) );
  OR2X1_RVT C139 ( .A1(n267), .A2(n285), .Y(N152) );
  OR2X1_RVT C80 ( .A1(N112), .A2(N113), .Y(N114) );
  AND2X1_RVT C2095 ( .A1(N184), .A2(N289), .Y(N520) );
  INVX1_RVT I_25 ( .A(N114), .Y(N115) );
  INVX1_RVT U106 ( .A(N56), .Y(n57) );
  OA21X1_RVT U33 ( .A1(n251), .A2(n47), .A3(n430), .Y(is_decoding_o) );
  AND2X1_RVT C2126 ( .A1(is_decoding_o), .A2(N748), .Y(N749) );
  OR2X1_RVT U4 ( .A1(csr_cause_o[5]), .A2(n55), .Y(n1) );
  AO21X1_RVT U3 ( .A1(n54), .A2(n430), .A3(n1), .Y(halt_id_o) );
  AND2X1_RVT C2134 ( .A1(regfile_we_wb_i), .A2(reg_d_wb_is_reg_a_i), .Y(N752)
         );
  AND2X1_RVT C2094 ( .A1(instr_valid_i), .A2(N518), .Y(N519) );
  INVX1_RVT I_22 ( .A(N102), .Y(N103) );
  INVX0_RVT I_57 ( .A(branch_taken_ex_i), .Y(N308) );
  OR3X1_RVT U187 ( .A1(uret_insn_i), .A2(mret_insn_i), .A3(dret_insn_i), .Y(
        n117) );
  INVX0_RVT U180 ( .A(n117), .Y(n116) );
  INVX1_RVT I_31 ( .A(N141), .Y(N142) );
  INVX1_RVT I_5 ( .A(ctrl_transfer_insn_in_dec_i[1]), .Y(N718) );
  INVX0_RVT I_83 ( .A(is_fetch_failed_i), .Y(N528) );
  DELLN1X2_RVT U298 ( .A(n290), .Y(n248) );
  INVX0_RVT U299 ( .A(n441), .Y(n329) );
  INVX0_RVT U300 ( .A(N384), .Y(N436) );
  INVX0_RVT U301 ( .A(ctrl_fsm_cs[0]), .Y(n459) );
  INVX1_RVT U302 ( .A(n448), .Y(n447) );
  INVX0_RVT U303 ( .A(N91), .Y(n448) );
  INVX0_RVT U304 ( .A(n449), .Y(n59) );
  INVX0_RVT U305 ( .A(N142), .Y(n433) );
  INVX0_RVT U306 ( .A(n293), .Y(n289) );
  INVX0_RVT U307 ( .A(N463), .Y(n298) );
  INVX0_RVT U308 ( .A(n378), .Y(n328) );
  INVX1_RVT U309 ( .A(N183), .Y(N289) );
  INVX0_RVT U310 ( .A(n139), .Y(n379) );
  INVX1_RVT U311 ( .A(n400), .Y(n399) );
  NOR2X1_RVT U312 ( .A1(debug_single_step_i), .A2(debug_req_pending), .Y(n375)
         );
  INVX1_RVT U313 ( .A(illegal_insn_i), .Y(n440) );
  INVX0_RVT U314 ( .A(N464), .Y(n296) );
  INVX0_RVT U315 ( .A(N466), .Y(n297) );
  OR4X1_RVT U316 ( .A1(n318), .A2(n408), .A3(n319), .A4(N674), .Y(n256) );
  NBUFFX2_RVT U317 ( .A(n414), .Y(N56) );
  NBUFFX2_RVT U318 ( .A(n384), .Y(n430) );
  OAI21X1_RVT U319 ( .A1(n352), .A2(n353), .A3(N110), .Y(n351) );
  NOR2X0_RVT U320 ( .A1(n445), .A2(n429), .Y(n363) );
  AOI21X1_RVT U321 ( .A1(N99), .A2(n210), .A3(n306), .Y(n362) );
  INVX0_RVT U322 ( .A(n434), .Y(N150) );
  NBUFFX2_RVT U323 ( .A(n482), .Y(n250) );
  NBUFFX2_RVT U324 ( .A(n269), .Y(debug_mode_o) );
  INVX0_RVT U325 ( .A(N517), .Y(n353) );
  NBUFFX2_RVT U326 ( .A(n313), .Y(n285) );
  NBUFFX2_RVT U327 ( .A(n420), .Y(n273) );
  NOR2X1_RVT U328 ( .A1(N583), .A2(debug_havereset_o), .Y(n239) );
  INVX1_RVT U329 ( .A(debug_req_pending), .Y(n210) );
  MUX21X1_RVT U330 ( .A1(N473), .A2(debug_force_wakeup_q), .S0(n437), .Y(n157)
         );
  MUX21X1_RVT U331 ( .A1(N332), .A2(jump_done_q), .S0(n463), .Y(N501) );
  MUX21X1_RVT U332 ( .A1(N500), .A2(n337), .S0(n256), .Y(n158) );
  NAND2X0_RVT U333 ( .A1(n135), .A2(n35), .Y(n260) );
  NAND3X0_RVT U334 ( .A1(N56), .A2(N347), .A3(n248), .Y(n65) );
  AOI21X1_RVT U335 ( .A1(n417), .A2(ebrk_insn_i), .A3(n450), .Y(n367) );
  NAND3X0_RVT U336 ( .A1(N56), .A2(debug_mode_o), .A3(n66), .Y(n63) );
  AND4X1_RVT U337 ( .A1(N56), .A2(mret_insn_i), .A3(n355), .A4(n248), .Y(
        csr_restore_mret_id_o) );
  NAND2X0_RVT U338 ( .A1(dret_insn_i), .A2(n415), .Y(n397) );
  NAND3X0_RVT U339 ( .A1(n59), .A2(n407), .A3(n58), .Y(n86) );
  NOR3X1_RVT U340 ( .A1(N118), .A2(n414), .A3(N53), .Y(n339) );
  NAND2X0_RVT U341 ( .A1(n360), .A2(n363), .Y(n263) );
  OR4X1_RVT U342 ( .A1(N130), .A2(N633), .A3(N635), .A4(n432), .Y(n412) );
  OR2X1_RVT U343 ( .A1(N61), .A2(N126), .Y(n405) );
  NOR2X1_RVT U344 ( .A1(N142), .A2(n444), .Y(n218) );
  AOI21X1_RVT U345 ( .A1(n419), .A2(n481), .A3(n471), .Y(n403) );
  INVX1_RVT U346 ( .A(N98), .Y(N99) );
  AO21X1_RVT U347 ( .A1(n126), .A2(n418), .A3(n54), .Y(n422) );
  INVX1_RVT U348 ( .A(N153), .Y(N61) );
  INVX1_RVT U349 ( .A(N115), .Y(n352) );
  OR2X1_RVT U350 ( .A1(N502), .A2(N118), .Y(n445) );
  MUX21X1_RVT U351 ( .A1(n289), .A2(n221), .S0(n402), .Y(N509) );
  OR2X1_RVT U352 ( .A1(N95), .A2(N103), .Y(n306) );
  OR2X1_RVT U353 ( .A1(n252), .A2(wfi_active), .Y(n382) );
  NAND2X0_RVT U354 ( .A1(N129), .A2(N125), .Y(n404) );
  INVX1_RVT U355 ( .A(n250), .Y(n439) );
  OR2X1_RVT U356 ( .A1(N152), .A2(N151), .Y(N153) );
  NAND3X0_RVT U357 ( .A1(N57), .A2(mret_dec_i), .A3(n355), .Y(n37) );
  INVX1_RVT U358 ( .A(n431), .Y(n245) );
  NOR2X1_RVT U359 ( .A1(n285), .A2(n366), .Y(N118) );
  INVX1_RVT U360 ( .A(N129), .Y(N130) );
  OAI21X1_RVT U361 ( .A1(n344), .A2(N741), .A3(1'b1), .Y(N457) );
  AOI22X1_RVT U362 ( .A1(wake_from_sleep_o), .A2(debug_req_pending), .A3(N162), 
        .A4(n301), .Y(N166) );
  OR2X1_RVT U363 ( .A1(n242), .A2(n303), .Y(n462) );
  OR2X1_RVT U364 ( .A1(n288), .A2(n343), .Y(n366) );
  INVX1_RVT U365 ( .A(N125), .Y(N126) );
  OR2X1_RVT U366 ( .A1(N108), .A2(N148), .Y(N110) );
  INVX1_RVT U367 ( .A(n302), .Y(n299) );
  OR2X1_RVT U368 ( .A1(N100), .A2(N101), .Y(N102) );
  INVX1_RVT U369 ( .A(N138), .Y(n281) );
  INVX1_RVT U370 ( .A(N30), .Y(n371) );
  NOR2X1_RVT U371 ( .A1(N132), .A2(N131), .Y(n409) );
  INVX1_RVT U372 ( .A(N145), .Y(N146) );
  INVX1_RVT U373 ( .A(N95), .Y(n407) );
  OR2X1_RVT U374 ( .A1(n379), .A2(n288), .Y(n275) );
  NOR2X1_RVT U375 ( .A1(illegal_insn_i), .A2(n232), .Y(n391) );
  NOR2X1_RVT U376 ( .A1(N143), .A2(N136), .Y(N138) );
  NAND2X0_RVT U377 ( .A1(n329), .A2(n283), .Y(n421) );
  AOI22X1_RVT U378 ( .A1(n418), .A2(debug_req_pending), .A3(n443), .A4(N159), 
        .Y(n476) );
  OAI21X1_RVT U379 ( .A1(n331), .A2(n305), .A3(n223), .Y(n66) );
  OR2X1_RVT U380 ( .A1(n330), .A2(N92), .Y(N132) );
  INVX1_RVT U381 ( .A(wake_from_sleep_o), .Y(N162) );
  INVX1_RVT U382 ( .A(n295), .Y(n322) );
  NOR2X0_RVT U383 ( .A1(n274), .A2(n374), .Y(n317) );
  INVX1_RVT U384 ( .A(n266), .Y(n303) );
  OR2X1_RVT U385 ( .A1(N143), .A2(N144), .Y(N145) );
  OR2X1_RVT U386 ( .A1(n326), .A2(ctrl_fsm_cs[0]), .Y(N148) );
  NOR2X1_RVT U387 ( .A1(ctrl_fsm_cs[0]), .A2(N143), .Y(n358) );
  INVX0_RVT U388 ( .A(N519), .Y(n380) );
  NOR2X0_RVT U389 ( .A1(id_ready_i), .A2(N199), .Y(n373) );
  INVX1_RVT U390 ( .A(n269), .Y(n324) );
  OR2X1_RVT U391 ( .A1(n274), .A2(fetch_enable_i), .Y(N156) );
  INVX1_RVT U392 ( .A(n255), .Y(n325) );
  OR2X1_RVT U393 ( .A1(n301), .A2(n321), .Y(N112) );
  NBUFFX2_RVT U394 ( .A(n279), .Y(n283) );
  NOR2X1_RVT U395 ( .A1(irq_wu_ctrl_i), .A2(debug_req_pending), .Y(n359) );
  INVX1_RVT U396 ( .A(n242), .Y(n457) );
  INVX1_RVT U397 ( .A(n310), .Y(n396) );
  AND2X1_RVT U398 ( .A1(n398), .A2(n156), .Y(n374) );
  AND2X1_RVT U399 ( .A1(n398), .A2(n228), .Y(n369) );
  NOR2X0_RVT U400 ( .A1(n394), .A2(n393), .Y(n392) );
  NOR2X1_RVT U401 ( .A1(current_priv_lvl_i[0]), .A2(current_priv_lvl_i[1]), 
        .Y(n227) );
  INVX1_RVT U402 ( .A(ecall_insn_i), .Y(n331) );
  INVX1_RVT U403 ( .A(data_load_event_i), .Y(n393) );
  INVX1_RVT U404 ( .A(id_ready_i), .Y(n394) );
  NOR2X1_RVT U405 ( .A1(ex_valid_i), .A2(data_err_i), .Y(n228) );
  INVX1_RVT U406 ( .A(ebrk_insn_i), .Y(n346) );
  OR2X1_RVT U407 ( .A1(ebrk_force_debug_mode), .A2(n483), .Y(N199) );
  INVX0_RVT U408 ( .A(n115), .Y(n249) );
  OR2X1_RVT U409 ( .A1(N91), .A2(n285), .Y(N101) );
  INVX0_RVT U410 ( .A(N520), .Y(n370) );
  OR2X1_RVT U411 ( .A1(n284), .A2(n288), .Y(N108) );
  NBUFFX2_RVT U412 ( .A(ctrl_fsm_cs[3]), .Y(n307) );
  NBUFFX2_RVT U413 ( .A(n428), .Y(n255) );
  AND2X1_RVT U414 ( .A1(regfile_we_id_i), .A2(n45), .Y(N748) );
  INVX1_RVT U415 ( .A(data_err_i), .Y(N454) );
  NAND2X0_RVT U416 ( .A1(N434), .A2(n301), .Y(n323) );
  OA21X1_RVT U417 ( .A1(n143), .A2(n150), .A3(n251), .Y(n277) );
  NAND2X0_RVT U418 ( .A1(n133), .A2(n48), .Y(n259) );
  AND2X1_RVT U419 ( .A1(N454), .A2(n224), .Y(N678) );
  INVX1_RVT U420 ( .A(wb_ready_i), .Y(N709) );
  OR2X1_RVT U421 ( .A1(n286), .A2(n285), .Y(N97) );
  OR3X1_RVT U422 ( .A1(n263), .A2(n262), .A3(n261), .Y(N647) );
  OAI22X1_RVT U423 ( .A1(n476), .A2(n267), .A3(n421), .A4(N166), .Y(n478) );
  AND2X1_RVT U424 ( .A1(N749), .A2(N541), .Y(N750) );
  OR2X1_RVT U425 ( .A1(N148), .A2(N151), .Y(n434) );
  AOI22X1_RVT U426 ( .A1(n310), .A2(n457), .A3(n462), .A4(n398), .Y(n402) );
  NOR2X0_RVT U427 ( .A1(n239), .A2(N586), .Y(n220) );
  OR2X1_RVT U428 ( .A1(N746), .A2(N750), .Y(N751) );
  AND2X1_RVT U429 ( .A1(data_err_i), .A2(N308), .Y(N515) );
  AND4X1_RVT U430 ( .A1(N56), .A2(uret_insn_i), .A3(n355), .A4(n248), .Y(
        csr_restore_uret_id_o) );
  NOR2X0_RVT U431 ( .A1(debug_single_step_i), .A2(debug_force_wakeup_q), .Y(
        n211) );
  OR3X1_RVT U432 ( .A1(is_fetch_failed_i), .A2(illegal_insn_q), .A3(data_err_q), .Y(N369) );
  NOR2X0_RVT U433 ( .A1(ctrl_transfer_insn_in_dec_i[0]), .A2(N718), .Y(n212)
         );
  NAND2X0_RVT U434 ( .A1(csr_status_i), .A2(N639), .Y(n213) );
  AOI21X1_RVT U435 ( .A1(n299), .A2(N457), .A3(n283), .Y(n214) );
  OR2X1_RVT U436 ( .A1(n425), .A2(n422), .Y(n215) );
  NAND3X0_RVT U437 ( .A1(N57), .A2(uret_dec_i), .A3(n355), .Y(n216) );
  NOR2X0_RVT U438 ( .A1(dret_dec_i), .A2(N425), .Y(n217) );
  NAND2X0_RVT U439 ( .A1(n210), .A2(N652), .Y(n219) );
  OAI222X1_RVT U440 ( .A1(n399), .A2(n310), .A3(n299), .A4(n324), .A5(n271), 
        .A6(n335), .Y(n221) );
  AND2X1_RVT U441 ( .A1(n212), .A2(N756), .Y(jr_stall_o) );
  NOR2X0_RVT U442 ( .A1(N723), .A2(ctrl_transfer_insn_in_dec_i[1]), .Y(n222)
         );
  NOR2X0_RVT U443 ( .A1(N530), .A2(N527), .Y(n223) );
  AND2X1_RVT U444 ( .A1(n447), .A2(n358), .Y(n224) );
  NAND2X0_RVT U445 ( .A1(ebrk_force_debug_mode), .A2(ebrk_insn_i), .Y(n225) );
  OR2X1_RVT U446 ( .A1(N187), .A2(n383), .Y(n226) );
  AOI22X1_RVT U447 ( .A1(n102), .A2(n105), .A3(irq_id_ctrl_i[0]), .A4(
        csr_cause_o[5]), .Y(n229) );
  NOR2X0_RVT U448 ( .A1(wfi_i), .A2(N378), .Y(n230) );
  NOR2X0_RVT U449 ( .A1(debug_req_pending), .A2(debug_mode_o), .Y(n231) );
  AND2X1_RVT U450 ( .A1(N384), .A2(id_ready_i), .Y(n232) );
  NOR2X0_RVT U451 ( .A1(mult_multicycle_i), .A2(data_misaligned_i), .Y(n233)
         );
  NOR2X0_RVT U452 ( .A1(instr_valid_i), .A2(N179), .Y(n234) );
  NOR2X0_RVT U453 ( .A1(N721), .A2(N264), .Y(n235) );
  OAI21X1_RVT U454 ( .A1(n53), .A2(n52), .A3(n17), .Y(n236) );
  NOR2X0_RVT U455 ( .A1(N579), .A2(debug_havereset_o), .Y(n237) );
  NOR2X0_RVT U456 ( .A1(N575), .A2(N574), .Y(n238) );
  NBUFFX2_RVT U458 ( .A(N509), .Y(n241) );
  INVX0_RVT U459 ( .A(n141), .Y(n300) );
  NBUFFX2_RVT U460 ( .A(ctrl_fsm_cs[1]), .Y(n242) );
  AO22X1_RVT U461 ( .A1(n480), .A2(n401), .A3(n479), .A4(n270), .Y(N466) );
  NBUFFX2_RVT U462 ( .A(N436), .Y(n356) );
  NBUFFX2_RVT U463 ( .A(n129), .Y(n243) );
  NAND2X0_RVT U464 ( .A1(n244), .A2(n403), .Y(n474) );
  AO21X1_RVT U465 ( .A1(n276), .A2(n275), .A3(n245), .Y(n244) );
  AO21X1_RVT U466 ( .A1(n129), .A2(n394), .A3(n246), .Y(n145) );
  OR2X1_RVT U467 ( .A1(data_load_event_i), .A2(n153), .Y(n246) );
  OR2X1_RVT U468 ( .A1(n253), .A2(wfi_active), .Y(n129) );
  AO21X1_RVT U469 ( .A1(n468), .A2(n270), .A3(n247), .Y(N463) );
  AO22X1_RVT U470 ( .A1(n469), .A2(n396), .A3(n470), .A4(n401), .Y(n247) );
  AOI21X1_RVT U471 ( .A1(n126), .A2(n255), .A3(n54), .Y(n258) );
  AO22X1_RVT U472 ( .A1(N362), .A2(n459), .A3(n320), .A4(N418), .Y(n465) );
  OR2X1_RVT U473 ( .A1(n31), .A2(n249), .Y(n291) );
  NBUFFX2_RVT U474 ( .A(n294), .Y(n251) );
  OR2X1_RVT U475 ( .A1(n427), .A2(N647), .Y(n437) );
  OR2X1_RVT U476 ( .A1(n287), .A2(n226), .Y(n252) );
  OR2X1_RVT U477 ( .A1(n154), .A2(csr_status_i), .Y(n253) );
  NBUFFX2_RVT U478 ( .A(n280), .Y(n254) );
  AND2X1_RVT U479 ( .A1(n320), .A2(N162), .Y(N163) );
  AO21X1_RVT U480 ( .A1(N515), .A2(N115), .A3(n257), .Y(n411) );
  NAND2X0_RVT U481 ( .A1(n364), .A2(n365), .Y(n257) );
  OR2X1_RVT U482 ( .A1(n270), .A2(n308), .Y(N100) );
  AOI21X1_RVT U483 ( .A1(n301), .A2(n228), .A3(n8), .Y(n341) );
  AND3X1_RVT U484 ( .A1(n260), .A2(n259), .A3(n258), .Y(n347) );
  NBUFFX2_RVT U485 ( .A(n272), .Y(n355) );
  NAND2X0_RVT U486 ( .A1(n362), .A2(n368), .Y(n261) );
  NAND2X0_RVT U487 ( .A1(n367), .A2(n361), .Y(n262) );
  AO22X1_RVT U488 ( .A1(n458), .A2(n286), .A3(n264), .A4(n457), .Y(n477) );
  OAI22X1_RVT U489 ( .A1(n313), .A2(n342), .A3(n303), .A4(n341), .Y(n264) );
  NBUFFX2_RVT U490 ( .A(n413), .Y(n265) );
  NBUFFX2_RVT U491 ( .A(n443), .Y(n266) );
  NBUFFX2_RVT U492 ( .A(N369), .Y(n305) );
  INVX1_RVT U493 ( .A(N89), .Y(n400) );
  NBUFFX2_RVT U494 ( .A(n330), .Y(n267) );
  OR4X1_RVT U495 ( .A1(N126), .A2(N130), .A3(N675), .A4(N694), .Y(n386) );
  OR2X1_RVT U496 ( .A1(n268), .A2(N738), .Y(N741) );
  OR2X1_RVT U497 ( .A1(data_load_event_i), .A2(N739), .Y(n268) );
  NBUFFX2_RVT U498 ( .A(n483), .Y(n269) );
  NBUFFX2_RVT U499 ( .A(n396), .Y(n270) );
  OR2X1_RVT U500 ( .A1(n283), .A2(n313), .Y(N113) );
  OR2X1_RVT U501 ( .A1(n295), .A2(n438), .Y(n389) );
  NBUFFX2_RVT U502 ( .A(n396), .Y(n271) );
  NBUFFX2_RVT U503 ( .A(data_err_q), .Y(n340) );
  NBUFFX2_RVT U504 ( .A(n280), .Y(n272) );
  AND2X1_RVT U505 ( .A1(n378), .A2(n330), .Y(n148) );
  NBUFFX2_RVT U506 ( .A(n309), .Y(n288) );
  NBUFFX2_RVT U507 ( .A(n418), .Y(n274) );
  OR2X1_RVT U508 ( .A1(n340), .A2(n66), .Y(n4) );
  AO22X1_RVT U509 ( .A1(n478), .A2(n312), .A3(n477), .A4(n301), .Y(n480) );
  AO222X1_RVT U510 ( .A1(ebrk_insn_i), .A2(n289), .A3(N522), .A4(ebrk_insn_i), 
        .A5(ebrk_insn_i), .A6(n373), .Y(n153) );
  AO21X1_RVT U511 ( .A1(n300), .A2(n311), .A3(n380), .Y(n276) );
  NOR2X0_RVT U512 ( .A1(n329), .A2(n328), .Y(n327) );
  OA21X1_RVT U513 ( .A1(n215), .A2(n277), .A3(n214), .Y(n468) );
  NBUFFX2_RVT U514 ( .A(n441), .Y(n278) );
  AO22X1_RVT U515 ( .A1(n474), .A2(n398), .A3(n475), .A4(n401), .Y(N465) );
  NBUFFX2_RVT U516 ( .A(n420), .Y(n279) );
  AO22X1_RVT U517 ( .A1(n401), .A2(n292), .A3(n348), .A4(ctrl_fsm_cs[2]), .Y(
        N464) );
  NBUFFX2_RVT U518 ( .A(n48), .Y(n294) );
  NBUFFX2_RVT U519 ( .A(n34), .Y(n280) );
  NAND3X0_RVT U520 ( .A1(N145), .A2(N153), .A3(n281), .Y(n444) );
  NBUFFX2_RVT U521 ( .A(n428), .Y(n301) );
  NBUFFX2_RVT U522 ( .A(n34), .Y(n282) );
  AO21X1_RVT U523 ( .A1(n290), .A2(ebrk_insn_i), .A3(n4), .Y(n31) );
  NBUFFX2_RVT U524 ( .A(n320), .Y(n295) );
  OA21X1_RVT U525 ( .A1(N97), .A2(N96), .A3(n354), .Y(n364) );
  NBUFFX2_RVT U526 ( .A(n425), .Y(n284) );
  NBUFFX2_RVT U527 ( .A(n326), .Y(n286) );
  OA21X1_RVT U528 ( .A1(n327), .A2(n145), .A3(n138), .Y(n150) );
  OR2X1_RVT U529 ( .A1(fencei_insn_i), .A2(n381), .Y(n287) );
  NAND2X0_RVT U530 ( .A1(n377), .A2(n382), .Y(n378) );
  NBUFFX2_RVT U531 ( .A(n38), .Y(n290) );
  AO21X1_RVT U532 ( .A1(n290), .A2(n7), .A3(n291), .Y(n304) );
  NAND2X0_RVT U533 ( .A1(n333), .A2(n395), .Y(n292) );
  NBUFFX2_RVT U534 ( .A(n254), .Y(n293) );
  AND4X1_RVT U535 ( .A1(n298), .A2(n297), .A3(n296), .A4(N465), .Y(n387) );
  AO22X1_RVT U536 ( .A1(N156), .A2(n461), .A3(n465), .A4(n308), .Y(n467) );
  NAND3X0_RVT U537 ( .A1(wfi_i), .A2(debug_req_pending), .A3(n38), .Y(n115) );
  NBUFFX2_RVT U538 ( .A(n279), .Y(n330) );
  NBUFFX2_RVT U539 ( .A(N90), .Y(n321) );
  AOI22X1_RVT U540 ( .A1(n369), .A2(n329), .A3(n304), .A4(n303), .Y(n316) );
  AO22X1_RVT U541 ( .A1(n419), .A2(n464), .A3(N163), .A4(n461), .Y(n466) );
  NBUFFX2_RVT U542 ( .A(n325), .Y(n302) );
  NBUFFX2_RVT U543 ( .A(N92), .Y(n313) );
  NBUFFX2_RVT U544 ( .A(n321), .Y(n309) );
  NAND2X0_RVT U545 ( .A1(n315), .A2(n457), .Y(n395) );
  NBUFFX2_RVT U546 ( .A(n425), .Y(n308) );
  NBUFFX2_RVT U547 ( .A(N90), .Y(n310) );
  OA21X1_RVT U548 ( .A1(n309), .A2(n370), .A3(n371), .Y(n311) );
  NBUFFX2_RVT U549 ( .A(n438), .Y(n312) );
  OR2X1_RVT U550 ( .A1(N678), .A2(n405), .Y(n319) );
  AO21X1_RVT U551 ( .A1(n461), .A2(N157), .A3(n460), .Y(n315) );
  OR2X1_RVT U552 ( .A1(n435), .A2(n412), .Y(n318) );
  OAI22X1_RVT U553 ( .A1(n245), .A2(n317), .A3(n399), .A4(n316), .Y(n473) );
  NBUFFX2_RVT U554 ( .A(n418), .Y(n320) );
  AO22X1_RVT U555 ( .A1(n302), .A2(n324), .A3(n323), .A4(n322), .Y(n335) );
  NBUFFX2_RVT U556 ( .A(n420), .Y(n326) );
  NBUFFX2_RVT U557 ( .A(N118), .Y(N52) );
  AO22X1_RVT U558 ( .A1(n472), .A2(n286), .A3(n473), .A4(n457), .Y(n475) );
  NAND2X0_RVT U559 ( .A1(n326), .A2(N162), .Y(n332) );
  AO21X1_RVT U560 ( .A1(n332), .A2(n266), .A3(n334), .Y(n333) );
  NAND2X0_RVT U561 ( .A1(n431), .A2(n273), .Y(n334) );
  INVX1_RVT U562 ( .A(n336), .Y(n337) );
  NOR2X0_RVT U563 ( .A1(n337), .A2(n107), .Y(n102) );
  OA21X1_RVT U564 ( .A1(ecall_insn_i), .A2(n337), .A3(n96), .Y(n99) );
  AND2X1_RVT U565 ( .A1(illegal_insn_q), .A2(N529), .Y(N530) );
  AND2X1_RVT U566 ( .A1(N501), .A2(n394), .Y(N568) );
  AND2X1_RVT U567 ( .A1(N519), .A2(n436), .Y(N693) );
  NAND2X0_RVT U568 ( .A1(n338), .A2(n339), .Y(n423) );
  AND4X1_RVT U569 ( .A1(N153), .A2(N141), .A3(n434), .A4(n281), .Y(n338) );
  OA221X1_RVT U570 ( .A1(n113), .A2(n305), .A3(n114), .A4(n357), .A5(n115), 
        .Y(n342) );
  OR2X1_RVT U571 ( .A1(n340), .A2(N527), .Y(n6) );
  AO21X1_RVT U572 ( .A1(n340), .A2(N56), .A3(irq_id_o[2]), .Y(exc_cause_o[2])
         );
  OA222X1_RVT U573 ( .A1(irq_id_o[1]), .A2(n340), .A3(irq_id_o[1]), .A4(N56), 
        .A5(irq_id_o[1]), .A6(n68), .Y(exc_cause_o[1]) );
  AND3X1_RVT U574 ( .A1(N56), .A2(dret_insn_i), .A3(n248), .Y(
        csr_restore_dret_id_o) );
  NAND3X0_RVT U575 ( .A1(N56), .A2(fencei_insn_i), .A3(n248), .Y(n26) );
  OR2X1_RVT U576 ( .A1(N127), .A2(N144), .Y(N129) );
  NAND2X0_RVT U577 ( .A1(n308), .A2(n273), .Y(n343) );
  AND2X1_RVT U578 ( .A1(N102), .A2(n407), .Y(n354) );
  OR2X1_RVT U579 ( .A1(debug_req_entry_q), .A2(data_err_i), .Y(n344) );
  OR2X1_RVT U580 ( .A1(N741), .A2(debug_req_entry_q), .Y(N451) );
  AOI21X1_RVT U581 ( .A1(n272), .A2(n345), .A3(n346), .Y(n136) );
  INVX0_RVT U582 ( .A(N522), .Y(n345) );
  AO21X1_RVT U583 ( .A1(n128), .A2(n255), .A3(n426), .Y(n12) );
  AO21X1_RVT U584 ( .A1(ebrk_insn_i), .A2(N525), .A3(n136), .Y(n426) );
  AO21X1_RVT U585 ( .A1(id_ready_i), .A2(n243), .A3(n12), .Y(n135) );
  AOI222X1_RVT U586 ( .A1(N89), .A2(n347), .A3(N89), .A4(n267), .A5(N91), .A6(
        n285), .Y(n479) );
  AO22X1_RVT U587 ( .A1(n286), .A2(n389), .A3(n388), .A4(n274), .Y(n348) );
  AOI221X1_RVT U588 ( .A1(N92), .A2(n349), .A3(n278), .A4(n350), .A5(N89), .Y(
        n460) );
  NAND2X0_RVT U589 ( .A1(n228), .A2(n267), .Y(n349) );
  OAI221X1_RVT U590 ( .A1(n117), .A2(wfi_i), .A3(n117), .A4(n210), .A5(n38), 
        .Y(n350) );
  INVX0_RVT U591 ( .A(N110), .Y(N111) );
  NAND2X0_RVT U592 ( .A1(n307), .A2(n309), .Y(N143) );
  OR2X1_RVT U593 ( .A1(N97), .A2(N96), .Y(N98) );
  OR2X1_RVT U594 ( .A1(n396), .A2(n284), .Y(N96) );
  NBUFFX2_RVT U595 ( .A(N436), .Y(n357) );
  NOR2X0_RVT U596 ( .A1(n441), .A2(n356), .Y(n458) );
  AND2X1_RVT U597 ( .A1(N736), .A2(n293), .Y(N524) );
  AND2X1_RVT U598 ( .A1(irq_req_ctrl_i), .A2(n282), .Y(N184) );
  NAND2X0_RVT U599 ( .A1(n359), .A2(n272), .Y(wake_from_sleep_o) );
  NAND2X0_RVT U600 ( .A1(n210), .A2(N615), .Y(n360) );
  NAND2X0_RVT U601 ( .A1(N162), .A2(n449), .Y(n361) );
  AND2X1_RVT U602 ( .A1(N107), .A2(wake_from_sleep_o), .Y(N615) );
  NAND2X0_RVT U603 ( .A1(branch_taken_ex_i), .A2(N115), .Y(n365) );
  OR3X1_RVT U604 ( .A1(N107), .A2(n351), .A3(n411), .Y(N674) );
  NBUFFX2_RVT U605 ( .A(N183), .Y(N30) );
  AND2X1_RVT U606 ( .A1(N732), .A2(n254), .Y(N183) );
  NAND2X0_RVT U607 ( .A1(n400), .A2(n321), .Y(N131) );
  NOR3X0_RVT U608 ( .A1(N646), .A2(N642), .A3(n406), .Y(n368) );
  OR3X1_RVT U609 ( .A1(N138), .A2(n415), .A3(N146), .Y(n435) );
  MUX21X1_RVT U610 ( .A1(n384), .A2(debug_req_entry_q), .S0(n372), .Y(n159) );
  OR3X1_RVT U611 ( .A1(N674), .A2(n423), .A3(n386), .Y(n372) );
  NBUFFX2_RVT U612 ( .A(ctrl_fsm_cs[2]), .Y(n398) );
  OR2X1_RVT U613 ( .A1(n398), .A2(wake_from_sleep_o), .Y(N165) );
  NBUFFX2_RVT U614 ( .A(n307), .Y(n425) );
  AO21X1_RVT U615 ( .A1(N165), .A2(n322), .A3(n284), .Y(n472) );
  NBUFFX2_RVT U616 ( .A(ctrl_fsm_cs[3]), .Y(n428) );
  AND2X1_RVT U617 ( .A1(n156), .A2(n255), .Y(N159) );
  INVX1_RVT U618 ( .A(n438), .Y(n419) );
  NAND2X0_RVT U619 ( .A1(n375), .A2(n282), .Y(N763) );
  OR2X1_RVT U620 ( .A1(debug_req_i), .A2(debug_req_q), .Y(debug_req_pending)
         );
  NOR2X0_RVT U621 ( .A1(n376), .A2(debug_wfi_no_sleep_o), .Y(wfi_active) );
  INVX1_RVT U622 ( .A(wfi_i), .Y(n376) );
  INVX1_RVT U623 ( .A(jump_in_dec), .Y(n377) );
  OR2X1_RVT U624 ( .A1(N91), .A2(n278), .Y(N136) );
  AO21X1_RVT U625 ( .A1(n441), .A2(n228), .A3(n9), .Y(N362) );
  OR2X1_RVT U626 ( .A1(N91), .A2(n278), .Y(N124) );
  NAND2X0_RVT U627 ( .A1(n377), .A2(n382), .Y(n128) );
  NBUFFX2_RVT U628 ( .A(ctrl_fsm_cs[0]), .Y(n441) );
  NAND4X0_RVT U629 ( .A1(n398), .A2(n274), .A3(n457), .A4(n312), .Y(n463) );
  OR2X1_RVT U630 ( .A1(n53), .A2(n378), .Y(n127) );
  OR2X1_RVT U631 ( .A1(N763), .A2(trigger_match_i), .Y(debug_wfi_no_sleep_o)
         );
  OR2X1_RVT U632 ( .A1(n483), .A2(trigger_match_i), .Y(N738) );
  AND2X1_RVT U633 ( .A1(debug_mode_o), .A2(N572), .Y(N573) );
  OR2X1_RVT U634 ( .A1(debug_mode_o), .A2(debug_req_q), .Y(N760) );
  OR2X1_RVT U635 ( .A1(N188), .A2(ecall_insn_i), .Y(n381) );
  OR2X1_RVT U636 ( .A1(data_load_event_i), .A2(csr_status_i), .Y(n383) );
  NBUFFX2_RVT U637 ( .A(ctrl_fsm_cs[1]), .Y(n420) );
  NBUFFX2_RVT U638 ( .A(n436), .Y(n384) );
  OR2X1_RVT U639 ( .A1(N52), .A2(N675), .Y(n408) );
  AO22X1_RVT U640 ( .A1(n273), .A2(n126), .A3(n385), .A4(n294), .Y(N326) );
  OR2X1_RVT U641 ( .A1(n142), .A2(n390), .Y(n385) );
  OA21X1_RVT U642 ( .A1(n392), .A2(n148), .A3(n391), .Y(n390) );
  AO22X1_RVT U643 ( .A1(N458), .A2(n284), .A3(N326), .A4(n312), .Y(n388) );
  OR2X1_RVT U644 ( .A1(N509), .A2(n387), .Y(N589) );
  AO22X1_RVT U645 ( .A1(n466), .A2(n286), .A3(n467), .A4(n457), .Y(n470) );
  NBUFFX2_RVT U646 ( .A(ctrl_fsm_cs[0]), .Y(n418) );
  NAND4X0_RVT U647 ( .A1(n213), .A2(n397), .A3(n219), .A4(n218), .Y(n427) );
  NBUFFX2_RVT U648 ( .A(n310), .Y(n401) );
  AO22X1_RVT U649 ( .A1(n73), .A2(N84), .A3(n74), .A4(N83), .Y(n71) );
  AO21X1_RVT U650 ( .A1(n416), .A2(mret_insn_i), .A3(n404), .Y(n406) );
  OR3X1_RVT U651 ( .A1(N633), .A2(N637), .A3(N635), .Y(n450) );
  OA21X1_RVT U652 ( .A1(n410), .A2(n144), .A3(n250), .Y(n141) );
  OR2X1_RVT U653 ( .A1(n142), .A2(n143), .Y(n410) );
  NBUFFX2_RVT U654 ( .A(n409), .Y(n413) );
  NBUFFX2_RVT U655 ( .A(n265), .Y(n414) );
  NBUFFX2_RVT U656 ( .A(n417), .Y(n415) );
  NBUFFX2_RVT U657 ( .A(N639), .Y(n416) );
  NBUFFX2_RVT U658 ( .A(N639), .Y(n417) );
  AO22X1_RVT U659 ( .A1(n73), .A2(n72), .A3(n424), .A4(debug_running_o), .Y(
        debug_fsm_ns[1]) );
  OR2X1_RVT U660 ( .A1(n239), .A2(n71), .Y(n424) );
  OR2X1_RVT U661 ( .A1(n224), .A2(N111), .Y(n429) );
  NBUFFX2_RVT U662 ( .A(n325), .Y(n431) );
  NAND2X0_RVT U663 ( .A1(n434), .A2(n433), .Y(n432) );
  NBUFFX2_RVT U664 ( .A(N502), .Y(n436) );
  NBUFFX2_RVT U665 ( .A(n325), .Y(n438) );
  NOR3X1_RVT U666 ( .A1(n440), .A2(n439), .A3(n352), .Y(N500) );
  AO22X1_RVT U667 ( .A1(n241), .A2(n239), .A3(n74), .A4(N83), .Y(n69) );
  NBUFFX2_RVT U668 ( .A(N589), .Y(n442) );
  NBUFFX2_RVT U669 ( .A(n459), .Y(n443) );
  AND2X1_RVT U670 ( .A1(n266), .A2(n446), .Y(N107) );
  NOR2X0_RVT U671 ( .A1(n447), .A2(N104), .Y(n446) );
  NBUFFX2_RVT U672 ( .A(N107), .Y(n449) );
  AND2X1_RVT U673 ( .A1(data_load_event_i), .A2(n21), .Y(perf_pipeline_stall_o) );
  AO21X1_RVT U674 ( .A1(N196), .A2(n23), .A3(n22), .Y(pc_set_o) );
  NAND3X0_RVT U675 ( .A1(n216), .A2(n451), .A3(n452), .Y(pc_mux_o[1]) );
  INVX1_RVT U676 ( .A(n23), .Y(n451) );
  INVX1_RVT U677 ( .A(n33), .Y(n452) );
  OR2X1_RVT U678 ( .A1(n36), .A2(n33), .Y(pc_mux_o[0]) );
  NAND3X0_RVT U679 ( .A1(n236), .A2(n433), .A3(n453), .Y(halt_if_o) );
  INVX1_RVT U680 ( .A(halt_id_o), .Y(n453) );
  OR2X1_RVT U681 ( .A1(n29), .A2(n61), .Y(exc_pc_mux_o[1]) );
  AND2X1_RVT U682 ( .A1(N150), .A2(N536), .Y(debug_cause_o[2]) );
  AO21X1_RVT U683 ( .A1(N150), .A2(debug_force_wakeup_q), .A3(n77), .Y(
        debug_cause_o[1]) );
  NAND3X0_RVT U684 ( .A1(n407), .A2(n88), .A3(n49), .Y(ctrl_busy_o) );
  NAND3X0_RVT U685 ( .A1(n454), .A2(n94), .A3(n455), .Y(csr_save_if_o) );
  INVX1_RVT U686 ( .A(N150), .Y(n454) );
  INVX1_RVT U687 ( .A(n93), .Y(n455) );
  AO21X1_RVT U688 ( .A1(ebrk_insn_i), .A2(n96), .A3(n95), .Y(csr_save_id_o) );
  OR2X1_RVT U689 ( .A1(n101), .A2(n100), .Y(csr_save_cause_o) );
  AO21X1_RVT U690 ( .A1(ecall_insn_i), .A2(n102), .A3(irq_id_o[3]), .Y(
        csr_cause_o[3]) );
  NAND3X0_RVT U691 ( .A1(n456), .A2(n455), .A3(n229), .Y(csr_cause_o[0]) );
  INVX1_RVT U692 ( .A(csr_save_ex_o), .Y(n456) );
  INVX1_RVT U693 ( .A(n49), .Y(instr_req_o) );
  INVX1_RVT U694 ( .A(n24), .Y(pc_mux_o[2]) );
  AND2X1_RVT U695 ( .A1(n431), .A2(n443), .Y(n461) );
  INVX0_RVT U696 ( .A(n458), .Y(n464) );
  AO222X1_RVT U697 ( .A1(n326), .A2(n308), .A3(n286), .A4(n295), .A5(n329), 
        .A6(n457), .Y(n469) );
  NAND2X0_RVT U698 ( .A1(n274), .A2(n457), .Y(n471) );
  NOR2X0_RVT U699 ( .A1(N451), .A2(data_err_i), .Y(n481) );
  AND2X1_RVT U700 ( .A1(debug_single_step_i), .A2(n282), .Y(N384) );
  NOR2X0_RVT U701 ( .A1(N183), .A2(N184), .Y(n482) );
  AND2X1_RVT U702 ( .A1(N744), .A2(N751), .Y(load_stall_o) );
  AND2X1_RVT U703 ( .A1(irq_req_ctrl_i), .A2(n231), .Y(N168) );
endmodule

