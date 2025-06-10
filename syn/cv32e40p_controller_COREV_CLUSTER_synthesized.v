/////////////////////////////////////////////////////////////
// Created by: Synopsys DC Ultra(TM) in wire load mode
// Version   : T-2022.03-SP3
// Date      : Mon Jun  9 16:58:54 2025
/////////////////////////////////////////////////////////////


module cv32e40p_controller_COREV_CLUSTER ( clk, clk_ungated_i, rst_n, 
        fetch_enable_i, ctrl_busy_o, is_decoding_o, is_fetch_failed_i, 
        deassert_we_o, illegal_insn_i, ecall_insn_i, mret_insn_i, uret_insn_i, 
        dret_insn_i, mret_dec_i, uret_dec_i, dret_dec_i, wfi_i, ebrk_insn_i, 
        fencei_insn_i, csr_status_i, hwlp_mask_o, instr_valid_i, instr_req_o, 
        pc_set_o, pc_mux_o, exc_pc_mux_o, trap_addr_mux_o, pc_id_i, 
        hwlp_start_addr_i, hwlp_end_addr_i, hwlp_counter_i, hwlp_dec_cnt_o, 
        hwlp_jump_o, hwlp_targ_addr_o, data_req_ex_i, data_we_ex_i, 
        data_misaligned_i, data_load_event_i, data_err_i, data_err_ack_o, 
        mult_multicycle_i, apu_en_i, apu_read_dep_i, apu_read_dep_for_jalr_i, 
        apu_write_dep_i, apu_stall_o, branch_taken_ex_i, 
        ctrl_transfer_insn_in_id_i, ctrl_transfer_insn_in_dec_i, 
        irq_req_ctrl_i, irq_sec_ctrl_i, irq_id_ctrl_i, irq_wu_ctrl_i, 
        current_priv_lvl_i, irq_ack_o, irq_id_o, exc_cause_o, debug_mode_o, 
        debug_cause_o, debug_csr_save_o, debug_req_i, debug_single_step_i, 
        debug_ebreakm_i, debug_ebreaku_i, trigger_match_i, 
        debug_p_elw_no_sleep_o, debug_wfi_no_sleep_o, debug_havereset_o, 
        debug_running_o, debug_halted_o, wake_from_sleep_o, csr_save_if_o, 
        csr_save_id_o, csr_save_ex_o, csr_cause_o, csr_irq_sec_o, 
        csr_restore_mret_id_o, csr_restore_uret_id_o, csr_restore_dret_id_o, 
        csr_save_cause_o, regfile_we_id_i, regfile_alu_waddr_id_i, 
        regfile_we_ex_i, regfile_waddr_ex_i, regfile_we_wb_i, 
        regfile_alu_we_fw_i, operand_a_fw_mux_sel_o, operand_b_fw_mux_sel_o, 
        operand_c_fw_mux_sel_o, reg_d_ex_is_reg_a_i, reg_d_ex_is_reg_b_i, 
        reg_d_ex_is_reg_c_i, reg_d_wb_is_reg_a_i, reg_d_wb_is_reg_b_i, 
        reg_d_wb_is_reg_c_i, reg_d_alu_is_reg_a_i, reg_d_alu_is_reg_b_i, 
        reg_d_alu_is_reg_c_i, halt_if_o, halt_id_o, misaligned_stall_o, 
        jr_stall_o, load_stall_o, id_ready_i, id_valid_i, ex_valid_i, 
        wb_ready_i, perf_pipeline_stall_o );
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
  wire   N50, N52, N53, N54, N57, N58, N59, jump_done, jump_done_q,
         jump_in_dec, ebrk_force_debug_mode, debug_mode_n, illegal_insn_q,
         debug_req_entry_q, debug_force_wakeup_q, N88, N89, N90, N91, N92, N93,
         N95, N96, N97, N99, N100, N103, N104, N107, N108, N109, N111, N112,
         N113, N115, N116, N118, N119, N122, N123, N124, N126, N127, N128,
         N130, N131, N134, N135, N138, N139, N140, N143, N146,
         debug_req_pending, N155, N161, N163, N176, N177, wfi_active, N180,
         N189, N253, N254, N255, N301, N325, N340, data_err_q, N363, N375,
         N377, N378, N399, N408, N427, N441, N444, N447, N466, N493, N495,
         N508, N510, N513, N514, N516, N519, N520, N521, N523, N528, N529,
         N530, N531, N534, N560, N561, debug_req_q, N564, N566, N567, N568,
         N571, N572, N575, N576, N582, N698, N699, N700, N701, N702, N707,
         N710, N711, N712, N715, N716, N721, N722, N723, N724, N725, N727,
         N728, N729, N730, N731, N732, N733, N734, N735, N737, N738, N739,
         N740, N741, N742, N743, N744, N745, N746, N747, N748, N749, N750,
         N751, N752, N753, N693, N692, N691, N690, N689, N688, N687, N686,
         N685, N684, N683, N679, N678, N677, N676, N675, N674, N673, N672,
         N671, N670, N669, N668, N667, N666, N665, N664, N663, N662, N661,
         N659, N658, N657, N656, N652, N651, N650, N649, N647, N646, N645,
         N644, N643, N642, N641, N640, N639, N638, N637, N636, N635, N634,
         N633, N632, N631, N630, N629, N628, N627, N626, N625, N624, N623,
         N622, N621, N620, N618, N617, N616, N615, N614, N613, N612, N611,
         N610, N609, N608, N606, N604, N603, N602, N601, N579, N565, N527,
         N524, N522, N518, N512, N511, N509, N507, N418, N371, N370, N369,
         N368, N362, N361, N339, N282, N258, N257, N256, N192, N186, N185,
         N184, N183, N182, N181, N172, N171, n1, n2, n3, n4, n5, n6, n7, n8,
         n9, n10, n11, n12, n13, n14, n16, n17, n18, n19, n22, n23, n24, n25,
         n26, n27, n28, n29, n30, n32, n33, n34, n36, n37, n38, n39, n40, n41,
         n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n55, n56,
         n57, n59, n60, n61, n62, n65, n66, n67, n69, n70, n71, n73, n74, n75,
         n76, n77, n78, n79, n80, n82, n83, n84, n85, n86, n87, n88, n89, n90,
         n91, n92, n93, n94, n95, n96, n97, n98, n99, n100, n101, n102, n103,
         n104, n105, n106, n107, n108, n109, n110, n112, n114, n115, n116,
         n117, n118, n119, n120, n121, n122, n123, n124, n125, n126, n127,
         n128, n129, n130, n131, n132, n133, n134, n135, n136, n137, n138,
         n139, n140, n141, n142, n143, n144, n145, n147, n148, n149, n150,
         n151, n152, n153, n154, n157, n158, n159, n160, n161, n162, n164,
         n165, n167, n168, n169, n170, n173, n174, n176, n177, n178, n179,
         n182, n183, n184, n185, n186, n187, n188, n189, n190, n191, n192,
         n193, n194, n195, n196, n197, n198, n199, n200, n201, n202, n203,
         n230, n231, n232, n233, n234, n235, n236, n237, n238, n239, n240,
         n241, n242, n243, n244, n245, n246, n247, n248, n249, n250, n251,
         n252, n253, n254, n269, n270, n271, n272, n273, n274, n275, n276,
         n277, n278, n279, n280, n281, n282, n283, n284, n285, n286, n287,
         n288, n289, n290, n291, n292, n293, n294, n295, n296, n297, n298,
         n299, n300, n301, n302, n303, n304, n305, n306, n307, n308, n347,
         n348, n349, n350, n351, n352, n353, n354, n355, n356, n357, n358,
         n359, n360, n361, n362, n363;
  wire   [2:0] ctrl_fsm_ns;
  wire   [3:0] ctrl_fsm_cs;
  wire   [2:0] debug_fsm_ns;

  OR2X1_RVT C2275 ( .A1(N690), .A2(N646), .Y(N691) );
  OR2X1_RVT C2273 ( .A1(N688), .A2(N54), .Y(N689) );
  OR2X2_RVT C2271 ( .A1(N686), .A2(N617), .Y(N687) );
  OR2X1_RVT C2269 ( .A1(N665), .A2(N684), .Y(N685) );
  AND2X1_RVT C2268 ( .A1(N282), .A2(N683), .Y(N684) );
  AND2X1_RVT C2267 ( .A1(N513), .A2(N495), .Y(N683) );
  OR2X1_RVT C2263 ( .A1(N678), .A2(N59), .Y(N679) );
  OR2X1_RVT C2260 ( .A1(N675), .A2(N57), .Y(N676) );
  OR2X1_RVT C2257 ( .A1(N672), .A2(N628), .Y(N673) );
  AND2X1_RVT C2253 ( .A1(N447), .A2(N53), .Y(N669) );
  AND2X1_RVT C2250 ( .A1(n253), .A2(N615), .Y(N666) );
  AND2X1_RVT C2248 ( .A1(N510), .A2(N615), .Y(N664) );
  AND2X1_RVT C2246 ( .A1(N508), .A2(N615), .Y(N662) );
  OR2X1_RVT C2243 ( .A1(N658), .A2(N613), .Y(N659) );
  OR2X1_RVT C2242 ( .A1(N657), .A2(N50), .Y(N658) );
  OR2X1_RVT C2241 ( .A1(N656), .A2(n236), .Y(N657) );
  OR2X1_RVT C2240 ( .A1(n306), .A2(N602), .Y(N656) );
  OR2X1_RVT C2235 ( .A1(N649), .A2(N59), .Y(N651) );
  OR2X1_RVT C2231 ( .A1(N645), .A2(N646), .Y(N647) );
  OR2X1_RVT C2229 ( .A1(N643), .A2(N644), .Y(N645) );
  AND2X1_RVT C2226 ( .A1(n118), .A2(N641), .Y(N642) );
  AND2X1_RVT C2225 ( .A1(wfi_i), .A2(N628), .Y(N641) );
  OR2X1_RVT C2224 ( .A1(N638), .A2(N639), .Y(N640) );
  AND2X1_RVT C2223 ( .A1(csr_status_i), .A2(N628), .Y(N639) );
  AND2X1_RVT C2221 ( .A1(dret_insn_i), .A2(N628), .Y(N637) );
  OR2X1_RVT C2220 ( .A1(N634), .A2(N635), .Y(N636) );
  AND2X1_RVT C2219 ( .A1(uret_insn_i), .A2(N628), .Y(N635) );
  AND2X1_RVT C2217 ( .A1(mret_insn_i), .A2(N628), .Y(N633) );
  OR2X1_RVT C2216 ( .A1(N630), .A2(N631), .Y(N632) );
  AND2X1_RVT C2215 ( .A1(ecall_insn_i), .A2(N628), .Y(N631) );
  AND2X1_RVT C2213 ( .A1(ebrk_insn_i), .A2(N628), .Y(N629) );
  AND2X1_RVT C2212 ( .A1(N363), .A2(N54), .Y(N628) );
  OR2X1_RVT C2211 ( .A1(N625), .A2(N626), .Y(N627) );
  AND2X1_RVT C2210 ( .A1(N523), .A2(N621), .Y(N626) );
  AND2X1_RVT C2208 ( .A1(N521), .A2(N621), .Y(N624) );
  OR2X1_RVT C2207 ( .A1(N620), .A2(N622), .Y(N623) );
  AND2X1_RVT C2206 ( .A1(data_err_q), .A2(N54), .Y(N622) );
  OR2X4_RVT C2202 ( .A1(N616), .A2(N617), .Y(N618) );
  OR2X1_RVT C2198 ( .A1(N612), .A2(N613), .Y(N614) );
  AND2X1_RVT C2195 ( .A1(N155), .A2(N50), .Y(N611) );
  OR2X1_RVT C2194 ( .A1(N606), .A2(N609), .Y(N610) );
  AND2X1_RVT C2193 ( .A1(n118), .A2(N608), .Y(N609) );
  AND2X1_RVT C2192 ( .A1(N50), .A2(wake_from_sleep_o), .Y(N608) );
  OR2X1_RVT C2190 ( .A1(N604), .A2(n236), .Y(N606) );
  OR2X1_RVT C2188 ( .A1(n306), .A2(N603), .Y(N604) );
  AND2X1_RVT C2187 ( .A1(n118), .A2(N602), .Y(N603) );
  OR2X1_RVT C2170 ( .A1(n244), .A2(n245), .Y(N579) );
  AND2X1_RVT C2160 ( .A1(n303), .A2(N565), .Y(N566) );
  INVX1_RVT I_99 ( .A(debug_req_i), .Y(N565) );
  AND2X1_RVT C2140 ( .A1(mult_multicycle_i), .A2(n48), .Y(N560) );
  AND2X1_RVT C2087 ( .A1(N444), .A2(N447), .Y(N530) );
  AND2X1_RVT C2086 ( .A1(debug_single_step_i), .A2(N441), .Y(N529) );
  AND2X1_RVT C2085 ( .A1(debug_req_entry_q), .A2(N527), .Y(N528) );
  AND2X1_RVT C2084 ( .A1(N524), .A2(n247), .Y(N527) );
  INVX1_RVT I_82 ( .A(trigger_match_i), .Y(N524) );
  AND2X1_RVT C2080 ( .A1(illegal_insn_q), .A2(N522), .Y(N523) );
  AND2X1_RVT C2079 ( .A1(N408), .A2(N511), .Y(N522) );
  AND2X1_RVT C2078 ( .A1(is_fetch_failed_i), .A2(N408), .Y(N521) );
  AND2X1_RVT C2077 ( .A1(ex_valid_i), .A2(N447), .Y(N520) );
  AND2X1_RVT C2076 ( .A1(id_ready_i), .A2(N518), .Y(N519) );
  AND2X1_RVT C2075 ( .A1(n299), .A2(N725), .Y(N518) );
  AND2X1_RVT C2073 ( .A1(ebrk_force_debug_mode), .A2(n299), .Y(N516) );
  AND2X1_RVT C2064 ( .A1(n251), .A2(N507), .Y(N163) );
  INVX1_RVT I_78 ( .A(irq_sec_ctrl_i), .Y(N507) );
  OR2X1_RVT C2023 ( .A1(uret_dec_i), .A2(mret_dec_i), .Y(N418) );
  NBUFFX2_RVT B_88 ( .A(N362), .Y(N399) );
  OR2X1_RVT C1988 ( .A1(csr_status_i), .A2(N370), .Y(N371) );
  OR2X1_RVT C1987 ( .A1(dret_insn_i), .A2(N369), .Y(N370) );
  OR2X1_RVT C1986 ( .A1(uret_insn_i), .A2(N368), .Y(N369) );
  OR2X1_RVT C1985 ( .A1(mret_insn_i), .A2(N339), .Y(N368) );
  INVX1_RVT I_61 ( .A(N362), .Y(N363) );
  OR2X1_RVT C1969 ( .A1(illegal_insn_q), .A2(N361), .Y(N362) );
  OR2X1_RVT C1968 ( .A1(is_fetch_failed_i), .A2(data_err_q), .Y(N361) );
  INVX1_RVT I_60 ( .A(N339), .Y(N340) );
  OR2X1_RVT C1963 ( .A1(ecall_insn_i), .A2(ebrk_insn_i), .Y(N339) );
  OR2X1_RVT C1946 ( .A1(N710), .A2(N257), .Y(N258) );
  OR2X1_RVT C1945 ( .A1(N255), .A2(N256), .Y(N257) );
  OR2X1_RVT C1944 ( .A1(N254), .A2(N253), .Y(N256) );
  OR2X1_RVT C1909 ( .A1(ebrk_force_debug_mode), .A2(debug_mode_o), .Y(N192) );
  OR2X1_RVT C1899 ( .A1(csr_status_i), .A2(N185), .Y(N186) );
  OR2X1_RVT C1898 ( .A1(N180), .A2(N184), .Y(N185) );
  OR2X1_RVT C1897 ( .A1(fencei_insn_i), .A2(N183), .Y(N184) );
  OR2X1_RVT C1896 ( .A1(ecall_insn_i), .A2(N182), .Y(N183) );
  OR2X1_RVT C1895 ( .A1(wfi_active), .A2(N181), .Y(N182) );
  OR2X1_RVT C1894 ( .A1(ebrk_insn_i), .A2(jump_in_dec), .Y(N181) );
  OR2X1_RVT C1875 ( .A1(is_fetch_failed_i), .A2(N171), .Y(N172) );
  OR2X1_RVT C1874 ( .A1(data_err_i), .A2(branch_taken_ex_i), .Y(N171) );
  NBUFFX2_RVT B_59 ( .A(N650), .Y(N59) );
  NBUFFX2_RVT B_53 ( .A(n248), .Y(N53) );
  AND2X1_RVT C131 ( .A1(N146), .A2(n298), .Y(N652) );
  AND2X1_RVT C54 ( .A1(N92), .A2(N93), .Y(N601) );
  INVX1_RVT I_97 ( .A(debug_wfi_no_sleep_o), .Y(N753) );
  AND2X1_RVT C2152 ( .A1(wfi_i), .A2(N753), .Y(wfi_active) );
  OR2X1_RVT C2148 ( .A1(n303), .A2(debug_req_q), .Y(N749) );
  OR2X1_RVT C2147 ( .A1(N749), .A2(debug_single_step_i), .Y(N750) );
  OR2X1_RVT C2146 ( .A1(N750), .A2(trigger_match_i), .Y(debug_p_elw_no_sleep_o) );
  AND2X1_RVT C2141 ( .A1(jump_done), .A2(n165), .Y(N561) );
  INVX1_RVT I_89 ( .A(apu_en_i), .Y(N746) );
  AND2X1_RVT C2115 ( .A1(apu_write_dep_i), .A2(N746), .Y(N747) );
  OR2X1_RVT C2114 ( .A1(apu_read_dep_i), .A2(N747), .Y(apu_stall_o) );
  INVX0_RVT I_84 ( .A(is_decoding_o), .Y(N531) );
  AND2X1_RVT C2055 ( .A1(ebrk_force_debug_mode), .A2(ebrk_insn_i), .Y(N728) );
  OR2X1_RVT C2054 ( .A1(n303), .A2(trigger_match_i), .Y(N727) );
  OR2X1_RVT C2053 ( .A1(N727), .A2(N728), .Y(N729) );
  OR2X1_RVT C2052 ( .A1(N729), .A2(data_load_event_i), .Y(N730) );
  OR2X1_RVT C2051 ( .A1(N730), .A2(debug_req_entry_q), .Y(N444) );
  OR2X1_RVT C1939 ( .A1(mret_insn_i), .A2(uret_insn_i), .Y(N255) );
  INVX1_RVT I_51 ( .A(ebrk_force_debug_mode), .Y(N725) );
  AND2X1_RVT C1937 ( .A1(N725), .A2(ebrk_insn_i), .Y(N254) );
  OR2X1_RVT C1936 ( .A1(illegal_insn_i), .A2(ecall_insn_i), .Y(N253) );
  INVX1_RVT I_42 ( .A(jr_stall_o), .Y(N723) );
  AND2X1_RVT C1902 ( .A1(N723), .A2(N724), .Y(N189) );
  OR2X1_RVT C1889 ( .A1(mret_insn_i), .A2(uret_insn_i), .Y(N722) );
  OR2X1_RVT C1888 ( .A1(N722), .A2(dret_insn_i), .Y(N180) );
  AND2X1_RVT C1788 ( .A1(debug_ebreaku_i), .A2(n251), .Y(N716) );
  AND2X1_RVT C1787 ( .A1(debug_ebreakm_i), .A2(N711), .Y(N715) );
  OR2X1_RVT C1786 ( .A1(N715), .A2(N716), .Y(ebrk_force_debug_mode) );
  OR2X1_RVT C1785 ( .A1(n240), .A2(n249), .Y(jump_in_dec) );
  INVX0_RVT I_7 ( .A(ctrl_transfer_insn_in_dec_i[0]), .Y(N712) );
  AND2X1_RVT C1570 ( .A1(current_priv_lvl_i[0]), .A2(current_priv_lvl_i[1]), 
        .Y(N711) );
  AND2X1_RVT C1569 ( .A1(ctrl_transfer_insn_in_id_i[0]), .A2(
        ctrl_transfer_insn_in_id_i[1]), .Y(N710) );
  OR2X1_RVT C1334 ( .A1(N575), .A2(debug_running_o), .Y(N576) );
  OR2X1_RVT C1330 ( .A1(debug_halted_o), .A2(N571), .Y(N572) );
  OR2X1_RVT C1326 ( .A1(debug_halted_o), .A2(debug_running_o), .Y(N568) );
  AND2X1_RVT C130 ( .A1(N88), .A2(n269), .Y(N146) );
  OR2X1_RVT C106 ( .A1(N90), .A2(n305), .Y(N131) );
  OR2X1_RVT C105 ( .A1(n286), .A2(N89), .Y(N130) );
  OR2X1_RVT C99 ( .A1(N90), .A2(n305), .Y(N127) );
  AND2X1_RVT C83 ( .A1(n293), .A2(n292), .Y(N116) );
  OR2X4_RVT C73 ( .A1(n293), .A2(n292), .Y(N108) );
  OR2X1_RVT C57 ( .A1(n293), .A2(n161), .Y(N96) );
  AND2X1_RVT C53 ( .A1(N90), .A2(n307), .Y(N93) );
  AND2X1_RVT C52 ( .A1(n286), .A2(n285), .Y(N92) );
  DFFARX1_RVT jump_done_q_reg ( .D(N561), .CLK(clk), .RSTB(rst_n), .Q(
        jump_done_q), .QN(N724) );
  DFFARX1_RVT data_err_q_reg ( .D(data_err_i), .CLK(clk), .RSTB(rst_n), .Q(
        data_err_q), .QN(N408) );
  DFFARX1_RVT debug_req_q_reg ( .D(n196), .CLK(clk_ungated_i), .RSTB(rst_n), 
        .Q(debug_req_q) );
  DFFARX1_RVT ctrl_fsm_cs_reg_1_ ( .D(ctrl_fsm_ns[1]), .CLK(clk), .RSTB(rst_n), 
        .Q(ctrl_fsm_cs[1]), .QN(N90) );
  DFFARX1_RVT debug_req_entry_q_reg ( .D(n195), .CLK(clk), .RSTB(rst_n), .Q(
        debug_req_entry_q) );
  DFFARX1_RVT illegal_insn_q_reg ( .D(n194), .CLK(clk), .RSTB(rst_n), .Q(
        illegal_insn_q) );
  DFFARX1_RVT debug_force_wakeup_q_reg ( .D(n193), .CLK(clk), .RSTB(rst_n), 
        .Q(debug_force_wakeup_q), .QN(N441) );
  DFFASX1_RVT debug_fsm_cs_reg_0_ ( .D(debug_fsm_ns[0]), .CLK(clk), .SETB(
        rst_n), .Q(debug_havereset_o), .QN(N567) );
  DFFARX1_RVT debug_fsm_cs_reg_2_ ( .D(debug_fsm_ns[2]), .CLK(clk), .RSTB(
        rst_n), .Q(debug_halted_o), .QN(N575) );
  DFFARX1_RVT debug_fsm_cs_reg_1_ ( .D(debug_fsm_ns[1]), .CLK(clk), .RSTB(
        rst_n), .Q(debug_running_o), .QN(N571) );
  INVX1_RVT U3 ( .A(n288), .Y(n1) );
  INVX0_RVT U4 ( .A(n291), .Y(n2) );
  AO222X1_RVT U5 ( .A1(n291), .A2(n289), .A3(n291), .A4(N427), .A5(n289), .A6(
        n303), .Y(n3) );
  NAND2X0_RVT U6 ( .A1(n297), .A2(n1), .Y(n4) );
  AO222X1_RVT U7 ( .A1(n291), .A2(n1), .A3(n2), .A4(n303), .A5(n288), .A6(n3), 
        .Y(n5) );
  OA22X1_RVT U8 ( .A1(n297), .A2(n1), .A3(n289), .A4(n4), .Y(n6) );
  MUX21X1_RVT U9 ( .A1(n5), .A2(n303), .S0(n6), .Y(debug_mode_n) );
  NAND4X0_RVT U10 ( .A1(n297), .A2(n289), .A3(n1), .A4(n2), .Y(n7) );
  MUX21X1_RVT U11 ( .A1(N325), .A2(jump_done_q), .S0(n7), .Y(jump_done) );
  AO21X1_RVT U15 ( .A1(ebrk_insn_i), .A2(N519), .A3(n8), .Y(n94) );
  OR2X1_RVT U16 ( .A1(n95), .A2(n96), .Y(n8) );
  AO21X1_RVT U21 ( .A1(ecall_insn_i), .A2(n130), .A3(n11), .Y(n33) );
  OR2X1_RVT U22 ( .A1(N521), .A2(N523), .Y(n11) );
  AO21X1_RVT U23 ( .A1(N50), .A2(N155), .A3(n12), .Y(n145) );
  OR2X1_RVT U24 ( .A1(n147), .A2(n125), .Y(n12) );
  AO21X1_RVT U25 ( .A1(N495), .A2(n148), .A3(n13), .Y(n125) );
  OR2X1_RVT U26 ( .A1(n105), .A2(n149), .Y(n13) );
  AO21X1_RVT U27 ( .A1(ebrk_insn_i), .A2(n179), .A3(n14), .Y(n177) );
  OR2X1_RVT U28 ( .A1(irq_ack_o), .A2(data_err_ack_o), .Y(n14) );
  OA21X1_RVT U33 ( .A1(n67), .A2(trigger_match_i), .A3(n17), .Y(n85) );
  AND2X1_RVT U34 ( .A1(n84), .A2(n87), .Y(n17) );
  OA21X1_RVT U35 ( .A1(N128), .A2(N378), .A3(n18), .Y(n107) );
  AND2X1_RVT U36 ( .A1(n114), .A2(n112), .Y(n18) );
  OA21X1_RVT U37 ( .A1(n133), .A2(n302), .A3(n19), .Y(n121) );
  AND2X1_RVT U38 ( .A1(N495), .A2(N513), .Y(n19) );
  AND2X1_RVT U39 ( .A1(irq_ack_o), .A2(N163), .Y(trap_addr_mux_o[0]) );
  AO21X1_RVT U41 ( .A1(n253), .A2(N495), .A3(N59), .Y(n22) );
  NAND4X0_RVT U43 ( .A1(n25), .A2(n26), .A3(n27), .A4(n28), .Y(n23) );
  NOR4X0_RVT U45 ( .A1(n29), .A2(n30), .A3(irq_ack_o), .A4(n32), .Y(n25) );
  AO22X1_RVT U46 ( .A1(n300), .A2(data_err_q), .A3(n300), .A4(n33), .Y(n30) );
  AO22X1_RVT U47 ( .A1(ebrk_insn_i), .A2(n34), .A3(N644), .A4(dret_dec_i), .Y(
        n29) );
  AND3X1_RVT U50 ( .A1(jump_in_dec), .A2(n38), .A3(n39), .Y(n24) );
  NAND2X0_RVT U52 ( .A1(n28), .A2(n41), .Y(n40) );
  NAND3X0_RVT U53 ( .A1(N644), .A2(mret_dec_i), .A3(n299), .Y(n41) );
  NAND2X0_RVT U54 ( .A1(fencei_insn_i), .A2(n34), .Y(n28) );
  NAND2X0_RVT U55 ( .A1(n42), .A2(n27), .Y(n36) );
  NAND2X0_RVT U56 ( .A1(branch_taken_ex_i), .A2(n43), .Y(n27) );
  NAND2X0_RVT U57 ( .A1(N644), .A2(dret_dec_i), .Y(n42) );
  AND4X1_RVT U58 ( .A1(regfile_we_wb_i), .A2(reg_d_wb_is_reg_c_i), .A3(n44), 
        .A4(n45), .Y(operand_c_fw_mux_sel_o[1]) );
  OR2X1_RVT U59 ( .A1(data_misaligned_i), .A2(n242), .Y(n45) );
  AO221X1_RVT U60 ( .A1(n46), .A2(data_misaligned_i), .A3(n46), .A4(n242), 
        .A5(N560), .Y(operand_c_fw_mux_sel_o[0]) );
  INVX0_RVT U61 ( .A(n44), .Y(n46) );
  NAND2X0_RVT U62 ( .A1(regfile_alu_we_fw_i), .A2(reg_d_alu_is_reg_c_i), .Y(
        n44) );
  AND4X1_RVT U63 ( .A1(regfile_we_wb_i), .A2(reg_d_wb_is_reg_b_i), .A3(n47), 
        .A4(n48), .Y(operand_b_fw_mux_sel_o[1]) );
  NAND2X0_RVT U64 ( .A1(regfile_alu_we_fw_i), .A2(reg_d_alu_is_reg_b_i), .Y(
        n47) );
  AND3X1_RVT U65 ( .A1(regfile_alu_we_fw_i), .A2(reg_d_alu_is_reg_b_i), .A3(
        n48), .Y(operand_b_fw_mux_sel_o[0]) );
  INVX0_RVT U66 ( .A(data_misaligned_i), .Y(n48) );
  AND3X1_RVT U67 ( .A1(regfile_we_wb_i), .A2(n49), .A3(reg_d_wb_is_reg_a_i), 
        .Y(operand_a_fw_mux_sel_o[1]) );
  INVX0_RVT U68 ( .A(operand_a_fw_mux_sel_o[0]), .Y(n49) );
  AO21X1_RVT U69 ( .A1(regfile_alu_we_fw_i), .A2(reg_d_alu_is_reg_a_i), .A3(
        data_misaligned_i), .Y(operand_a_fw_mux_sel_o[0]) );
  AO222X1_RVT U73 ( .A1(n38), .A2(illegal_insn_i), .A3(n38), .A4(N375), .A5(
        n38), .A6(n55), .Y(n53) );
  NAND4X0_RVT U75 ( .A1(n56), .A2(n57), .A3(n290), .A4(n59), .Y(halt_id_o) );
  INVX0_RVT U77 ( .A(irq_ack_o), .Y(n56) );
  AO221X1_RVT U79 ( .A1(N644), .A2(mret_dec_i), .A3(N644), .A4(uret_dec_i), 
        .A5(n66), .Y(n32) );
  NAND2X0_RVT U80 ( .A1(n67), .A2(N140), .Y(n66) );
  INVX0_RVT U81 ( .A(n69), .Y(n65) );
  NAND3X0_RVT U82 ( .A1(n70), .A2(n71), .A3(n69), .Y(exc_pc_mux_o[0]) );
  NAND3X0_RVT U83 ( .A1(n300), .A2(n303), .A3(n33), .Y(n69) );
  NAND2X0_RVT U84 ( .A1(N340), .A2(n34), .Y(n71) );
  AO21X1_RVT U85 ( .A1(data_err_q), .A2(n300), .A3(irq_id_o[2]), .Y(
        exc_cause_o[2]) );
  OA222X1_RVT U86 ( .A1(irq_id_o[1]), .A2(data_err_q), .A3(irq_id_o[1]), .A4(
        n300), .A5(irq_id_o[1]), .A6(n73), .Y(exc_cause_o[1]) );
  INVX0_RVT U87 ( .A(data_we_ex_i), .Y(n73) );
  AND2X1_RVT U88 ( .A1(irq_id_ctrl_i[1]), .A2(irq_ack_o), .Y(irq_id_o[1]) );
  AO221X1_RVT U89 ( .A1(n300), .A2(N521), .A3(n300), .A4(data_err_q), .A5(
        irq_id_o[0]), .Y(exc_cause_o[0]) );
  AND2X1_RVT U90 ( .A1(irq_id_ctrl_i[0]), .A2(irq_ack_o), .Y(irq_id_o[0]) );
  AO222X1_RVT U93 ( .A1(debug_halted_o), .A2(n244), .A3(n74), .A4(
        debug_halted_o), .A5(n75), .A6(debug_mode_n), .Y(debug_fsm_ns[2]) );
  OA22X1_RVT U94 ( .A1(n245), .A2(n244), .A3(N582), .A4(n244), .Y(n75) );
  AO222X1_RVT U95 ( .A1(debug_running_o), .A2(n243), .A3(debug_running_o), 
        .A4(n76), .A5(n77), .A6(n78), .Y(debug_fsm_ns[1]) );
  OA22X1_RVT U96 ( .A1(n245), .A2(n243), .A3(N582), .A4(n243), .Y(n77) );
  AO22X1_RVT U97 ( .A1(n244), .A2(n78), .A3(n245), .A4(n79), .Y(n76) );
  AO221X1_RVT U98 ( .A1(debug_havereset_o), .A2(n80), .A3(n74), .A4(
        debug_havereset_o), .A5(n233), .Y(debug_fsm_ns[0]) );
  INVX0_RVT U100 ( .A(N582), .Y(n79) );
  AND2X1_RVT U101 ( .A1(n244), .A2(n78), .Y(n80) );
  INVX1_RVT U102 ( .A(debug_mode_n), .Y(n78) );
  OA21X1_RVT U106 ( .A1(trigger_match_i), .A2(N528), .A3(n283), .Y(n83) );
  INVX0_RVT U107 ( .A(n84), .Y(n82) );
  NAND4X0_RVT U108 ( .A1(n70), .A2(n85), .A3(n290), .A4(n86), .Y(
        debug_cause_o[0]) );
  NAND2X0_RVT U109 ( .A1(debug_mode_o), .A2(n283), .Y(n86) );
  NAND2X0_RVT U110 ( .A1(N58), .A2(debug_force_wakeup_q), .Y(n84) );
  NAND2X0_RVT U111 ( .A1(N58), .A2(n250), .Y(n87) );
  AND4X1_RVT U112 ( .A1(n59), .A2(n89), .A3(n60), .A4(n88), .Y(n70) );
  OR4X1_RVT U113 ( .A1(illegal_insn_i), .A2(load_stall_o), .A3(jr_stall_o), 
        .A4(N531), .Y(deassert_we_o) );
  NAND3X0_RVT U115 ( .A1(n61), .A2(n92), .A3(n93), .Y(n91) );
  NAND3X0_RVT U116 ( .A1(n51), .A2(n39), .A3(n94), .Y(n93) );
  AO22X1_RVT U117 ( .A1(id_ready_i), .A2(n97), .A3(n98), .A4(n291), .Y(n96) );
  AOI22X1_RVT U118 ( .A1(n99), .A2(n291), .A3(n100), .A4(n51), .Y(n92) );
  NAND4X0_RVT U119 ( .A1(n107), .A2(n108), .A3(n109), .A4(n110), .Y(n106) );
  NAND2X0_RVT U120 ( .A1(N53), .A2(data_err_i), .Y(n110) );
  NAND3X0_RVT U121 ( .A1(N523), .A2(N621), .A3(N377), .Y(n109) );
  INVX0_RVT U123 ( .A(N59), .Y(n114) );
  AO22X1_RVT U124 ( .A1(n34), .A2(n115), .A3(n291), .A4(n116), .Y(n104) );
  OAI222X1_RVT U125 ( .A1(n117), .A2(n118), .A3(n119), .A4(N378), .A5(n120), 
        .A6(N378), .Y(n115) );
  INVX0_RVT U126 ( .A(wfi_i), .Y(n117) );
  AO221X1_RVT U128 ( .A1(N621), .A2(n33), .A3(N54), .A4(n123), .A5(n124), .Y(
        n122) );
  AO221X1_RVT U129 ( .A1(n297), .A2(N50), .A3(n297), .A4(n125), .A5(n126), .Y(
        n124) );
  NAND4X0_RVT U130 ( .A1(n127), .A2(n128), .A3(N128), .A4(n129), .Y(n126) );
  NAND2X0_RVT U131 ( .A1(N59), .A2(n361), .Y(n129) );
  INVX0_RVT U133 ( .A(n102), .Y(n128) );
  AO21X1_RVT U134 ( .A1(N50), .A2(wake_from_sleep_o), .A3(N602), .Y(n102) );
  AO221X1_RVT U135 ( .A1(n130), .A2(n131), .A3(n130), .A4(ebrk_insn_i), .A5(
        n132), .Y(n123) );
  AND2X1_RVT U136 ( .A1(debug_req_pending), .A2(wfi_i), .Y(n131) );
  AO22X1_RVT U137 ( .A1(n297), .A2(N514), .A3(n362), .A4(n134), .Y(n133) );
  NAND3X0_RVT U138 ( .A1(n135), .A2(n136), .A3(n137), .Y(n134) );
  AO221X1_RVT U139 ( .A1(n138), .A2(n139), .A3(n138), .A4(n140), .A5(n100), 
        .Y(n136) );
  AO222X1_RVT U142 ( .A1(n34), .A2(uret_insn_i), .A3(n34), .A4(dret_insn_i), 
        .A5(n34), .A6(mret_insn_i), .Y(n101) );
  NAND3X0_RVT U143 ( .A1(n59), .A2(n142), .A3(n143), .Y(n141) );
  AOI222X1_RVT U144 ( .A1(N59), .A2(N530), .A3(n38), .A4(n144), .A5(n288), 
        .A6(n145), .Y(n143) );
  AND2X1_RVT U145 ( .A1(n306), .A2(n150), .Y(n105) );
  INVX0_RVT U146 ( .A(fetch_enable_i), .Y(n150) );
  NAND3X0_RVT U147 ( .A1(n151), .A2(n152), .A3(n137), .Y(n144) );
  NAND3X0_RVT U148 ( .A1(N375), .A2(id_ready_i), .A3(N710), .Y(n137) );
  NAND4X0_RVT U149 ( .A1(id_ready_i), .A2(data_load_event_i), .A3(n39), .A4(
        n153), .Y(n152) );
  NAND4X0_RVT U150 ( .A1(n288), .A2(n39), .A3(n153), .A4(n98), .Y(n151) );
  AND2X1_RVT U151 ( .A1(N495), .A2(n51), .Y(n38) );
  NAND3X0_RVT U152 ( .A1(n34), .A2(n118), .A3(wfi_i), .Y(n142) );
  INVX0_RVT U153 ( .A(n236), .Y(n59) );
  AO221X1_RVT U156 ( .A1(n159), .A2(n160), .A3(n159), .A4(n161), .A5(n62), .Y(
        n158) );
  OA221X1_RVT U157 ( .A1(n162), .A2(n135), .A3(n232), .A4(n162), .A5(n61), .Y(
        n159) );
  OA21X1_RVT U159 ( .A1(illegal_insn_i), .A2(N375), .A3(id_ready_i), .Y(n100)
         );
  INVX0_RVT U160 ( .A(n98), .Y(n139) );
  AO22X1_RVT U162 ( .A1(ebrk_insn_i), .A2(n359), .A3(n165), .A4(n97), .Y(n164)
         );
  INVX0_RVT U163 ( .A(id_ready_i), .Y(n165) );
  OA21X1_RVT U164 ( .A1(n303), .A2(N516), .A3(ebrk_insn_i), .Y(n95) );
  OA22X1_RVT U165 ( .A1(n39), .A2(id_ready_i), .A3(n153), .A4(N258), .Y(n135)
         );
  NAND2X0_RVT U167 ( .A1(N375), .A2(id_ready_i), .Y(n153) );
  AOI22X1_RVT U168 ( .A1(N59), .A2(N530), .A3(n289), .A4(n116), .Y(n157) );
  AO21X1_RVT U169 ( .A1(N50), .A2(N155), .A3(n149), .Y(n116) );
  AO21X1_RVT U170 ( .A1(N53), .A2(n254), .A3(N52), .Y(n149) );
  NOR4X0_RVT U172 ( .A1(N613), .A2(n283), .A3(N58), .A4(N646), .Y(n127) );
  AO22X1_RVT U174 ( .A1(N644), .A2(N378), .A3(data_err_i), .A4(n273), .Y(n167)
         );
  AO222X1_RVT U175 ( .A1(N54), .A2(N521), .A3(n300), .A4(n132), .A5(n300), 
        .A6(n168), .Y(n154) );
  AO22X1_RVT U176 ( .A1(N378), .A2(N523), .A3(n130), .A4(n169), .Y(n168) );
  AO222X1_RVT U177 ( .A1(n118), .A2(wfi_i), .A3(N378), .A4(ebrk_insn_i), .A5(
        ecall_insn_i), .A6(N378), .Y(n169) );
  INVX0_RVT U178 ( .A(debug_req_pending), .Y(n118) );
  AO221X1_RVT U179 ( .A1(n130), .A2(csr_status_i), .A3(n130), .A4(n252), .A5(
        data_err_q), .Y(n132) );
  NAND3X0_RVT U180 ( .A1(n52), .A2(n89), .A3(n170), .Y(ctrl_busy_o) );
  NAND2X0_RVT U181 ( .A1(n235), .A2(wake_from_sleep_o), .Y(n170) );
  AND4X1_RVT U183 ( .A1(n88), .A2(N124), .A3(n67), .A4(N140), .Y(n52) );
  INVX0_RVT U185 ( .A(N57), .Y(n67) );
  NAND2X0_RVT U189 ( .A1(N113), .A2(n112), .Y(n43) );
  INVX0_RVT U191 ( .A(N615), .Y(n62) );
  AO221X1_RVT U197 ( .A1(n299), .A2(n173), .A3(n299), .A4(n174), .A5(
        debug_csr_save_o), .Y(n178) );
  AO21X1_RVT U198 ( .A1(n283), .A2(n299), .A3(N58), .Y(debug_csr_save_o) );
  OA21X1_RVT U199 ( .A1(ecall_insn_i), .A2(illegal_insn_q), .A3(n176), .Y(n174) );
  AND2X1_RVT U203 ( .A1(N621), .A2(n130), .Y(n34) );
  INVX1_RVT U204 ( .A(N399), .Y(n130) );
  AND2X1_RVT U205 ( .A1(irq_ack_o), .A2(irq_sec_ctrl_i), .Y(csr_irq_sec_o) );
  AND2X1_RVT U206 ( .A1(irq_ack_o), .A2(irq_id_ctrl_i[4]), .Y(csr_cause_o[4])
         );
  AND2X1_RVT U208 ( .A1(irq_ack_o), .A2(irq_id_ctrl_i[3]), .Y(irq_id_o[3]) );
  OR2X1_RVT U209 ( .A1(irq_id_o[2]), .A2(data_err_ack_o), .Y(csr_cause_o[2])
         );
  AND2X1_RVT U211 ( .A1(irq_ack_o), .A2(irq_id_ctrl_i[2]), .Y(irq_id_o[2]) );
  AO221X1_RVT U214 ( .A1(n176), .A2(illegal_insn_q), .A3(n176), .A4(n182), 
        .A5(n183), .Y(csr_cause_o[1]) );
  AO22X1_RVT U215 ( .A1(data_we_ex_i), .A2(data_err_ack_o), .A3(
        irq_id_ctrl_i[1]), .A4(irq_ack_o), .Y(n183) );
  INVX0_RVT U216 ( .A(n108), .Y(n176) );
  AO22X1_RVT U218 ( .A1(n179), .A2(n182), .A3(irq_id_ctrl_i[0]), .A4(irq_ack_o), .Y(n184) );
  AO21X1_RVT U219 ( .A1(N613), .A2(N161), .A3(n147), .Y(irq_ack_o) );
  AND3X1_RVT U220 ( .A1(N495), .A2(N513), .A3(N514), .Y(n147) );
  OAI21X1_RVT U221 ( .A1(n251), .A2(n120), .A3(n119), .Y(n182) );
  INVX0_RVT U222 ( .A(ebrk_insn_i), .Y(n119) );
  INVX0_RVT U223 ( .A(ecall_insn_i), .Y(n120) );
  NOR2X1_RVT U224 ( .A1(illegal_insn_q), .A2(n108), .Y(n179) );
  NAND2X0_RVT U225 ( .A1(N53), .A2(N520), .Y(n108) );
  AO22X1_RVT U226 ( .A1(N495), .A2(N508), .A3(data_err_i), .A4(n273), .Y(
        data_err_ack_o) );
  AND2X1_RVT U228 ( .A1(N495), .A2(N510), .Y(n173) );
  OR2X1_RVT U229 ( .A1(N566), .A2(debug_req_i), .Y(N564) );
  AND3X1_RVT U230 ( .A1(N495), .A2(illegal_insn_i), .A3(n362), .Y(N493) );
  NAND4X0_RVT U231 ( .A1(n26), .A2(n60), .A3(n185), .A4(n186), .Y(N466) );
  NAND2X0_RVT U232 ( .A1(n300), .A2(wfi_i), .Y(n186) );
  NAND3X0_RVT U233 ( .A1(n300), .A2(n252), .A3(debug_force_wakeup_q), .Y(n185)
         );
  INVX0_RVT U234 ( .A(N50), .Y(n60) );
  INVX1_RVT U235 ( .A(N602), .Y(n26) );
  AO222X1_RVT U236 ( .A1(n303), .A2(mret_dec_i), .A3(n303), .A4(uret_dec_i), 
        .A5(n303), .A6(n241), .Y(N427) );
  AO22X1_RVT U237 ( .A1(n187), .A2(n188), .A3(jump_done_q), .A4(n189), .Y(N325) );
  NAND3X0_RVT U238 ( .A1(n61), .A2(n190), .A3(n160), .Y(n189) );
  INVX1_RVT U239 ( .A(n99), .Y(n160) );
  AO21X1_RVT U240 ( .A1(N513), .A2(N514), .A3(n148), .Y(n99) );
  OR2X1_RVT U241 ( .A1(n253), .A2(branch_taken_ex_i), .Y(n148) );
  NAND2X0_RVT U242 ( .A1(n51), .A2(illegal_insn_i), .Y(n190) );
  NOR3X0_RVT U243 ( .A1(n50), .A2(N510), .A3(N508), .Y(n61) );
  AND2X1_RVT U244 ( .A1(N513), .A2(N176), .Y(n50) );
  AO22X1_RVT U245 ( .A1(jump_done_q), .A2(n191), .A3(jump_in_dec), .A4(N189), 
        .Y(n188) );
  OR2X1_RVT U246 ( .A1(n55), .A2(n98), .Y(n191) );
  OR2X1_RVT U247 ( .A1(jump_in_dec), .A2(n360), .Y(n98) );
  OR3X1_RVT U248 ( .A1(n97), .A2(ebrk_insn_i), .A3(data_load_event_i), .Y(n55)
         );
  OR3X1_RVT U249 ( .A1(csr_status_i), .A2(wfi_active), .A3(n192), .Y(n97) );
  OR3X2_RVT U250 ( .A1(ecall_insn_i), .A2(N180), .A3(fencei_insn_i), .Y(n192)
         );
  AND2X1_RVT U251 ( .A1(n51), .A2(n39), .Y(n187) );
  INVX0_RVT U252 ( .A(illegal_insn_i), .Y(n39) );
  INVX0_RVT U253 ( .A(n162), .Y(n51) );
  NAND2X0_RVT U254 ( .A1(N513), .A2(n362), .Y(n162) );
  MUX21X1_RVT U255 ( .A1(debug_req_q), .A2(debug_req_i), .S0(N564), .Y(n196)
         );
  MUX21X1_RVT U258 ( .A1(debug_force_wakeup_q), .A2(N466), .S0(n234), .Y(n193)
         );
  HADDX1_RVT U259 ( .A0(regfile_alu_waddr_id_i[0]), .B0(regfile_waddr_ex_i[0]), 
        .SO(n203) );
  HADDX1_RVT U260 ( .A0(regfile_alu_waddr_id_i[4]), .B0(regfile_waddr_ex_i[4]), 
        .SO(n202) );
  HADDX1_RVT U261 ( .A0(regfile_alu_waddr_id_i[3]), .B0(regfile_waddr_ex_i[3]), 
        .SO(n201) );
  HADDX1_RVT U262 ( .A0(regfile_alu_waddr_id_i[5]), .B0(regfile_waddr_ex_i[5]), 
        .SO(n199) );
  HADDX1_RVT U263 ( .A0(regfile_alu_waddr_id_i[1]), .B0(regfile_waddr_ex_i[1]), 
        .SO(n198) );
  HADDX1_RVT U264 ( .A0(regfile_alu_waddr_id_i[2]), .B0(regfile_waddr_ex_i[2]), 
        .SO(n197) );
  OR3X1_RVT U265 ( .A1(n199), .A2(n198), .A3(n197), .Y(n200) );
  NOR4X0_RVT U266 ( .A1(n203), .A2(n202), .A3(n201), .A4(n200), .Y(N534) );
  OR2X1_RVT C1556 ( .A1(N699), .A2(N700), .Y(N701) );
  OR2X1_RVT U20 ( .A1(n104), .A2(n106), .Y(n10) );
  OR2X1_RVT U18 ( .A1(n101), .A2(n103), .Y(n9) );
  AO21X1_RVT U19 ( .A1(n105), .A2(n291), .A3(n10), .Y(n103) );
  AO21X1_RVT U17 ( .A1(debug_req_pending), .A2(n102), .A3(n9), .Y(n90) );
  OR2X1_RVT C79 ( .A1(n298), .A2(n307), .Y(N112) );
  DFFARX1_RVT ctrl_fsm_cs_reg_0_ ( .D(ctrl_fsm_ns[0]), .CLK(clk), .RSTB(rst_n), 
        .Q(ctrl_fsm_cs[0]), .QN(n161) );
  NBUFFX2_RVT B_46 ( .A(N615), .Y(N495) );
  OR2X1_RVT C2262 ( .A1(N676), .A2(N58), .Y(N678) );
  OR2X1_RVT C2259 ( .A1(N674), .A2(N646), .Y(N675) );
  OR2X1_RVT C2256 ( .A1(N671), .A2(N624), .Y(N672) );
  OR2X1_RVT C2254 ( .A1(N668), .A2(N669), .Y(N670) );
  OR2X1_RVT C2251 ( .A1(N665), .A2(N666), .Y(N667) );
  OR2X1_RVT C2247 ( .A1(N661), .A2(N662), .Y(N663) );
  OR2X1_RVT C2277 ( .A1(N692), .A2(N59), .Y(N693) );
  OR2X1_RVT C2274 ( .A1(N689), .A2(N644), .Y(N690) );
  OR2X1_RVT C2149 ( .A1(N752), .A2(trigger_match_i), .Y(debug_wfi_no_sleep_o)
         );
  INVX1_RVT I_21 ( .A(N97), .Y(N602) );
  NBUFFX2_RVT B_52 ( .A(N617), .Y(N52) );
  INVX1_RVT I_2 ( .A(ctrl_fsm_ns[2]), .Y(N699) );
  OR2X1_RVT C1557 ( .A1(ctrl_fsm_ns[1]), .A2(N701), .Y(N702) );
  OR2X1_RVT C58 ( .A1(N95), .A2(N96), .Y(N97) );
  OR2X1_RVT C92 ( .A1(N88), .A2(n281), .Y(N122) );
  OR2X1_RVT C74 ( .A1(N107), .A2(N108), .Y(N109) );
  OR2X1_RVT C2227 ( .A1(N640), .A2(N642), .Y(N643) );
  OR2X1_RVT C2222 ( .A1(N636), .A2(N637), .Y(N638) );
  OR2X1_RVT C2218 ( .A1(N632), .A2(N633), .Y(N634) );
  OR2X1_RVT C2214 ( .A1(N627), .A2(N629), .Y(N630) );
  OR2X1_RVT C2209 ( .A1(N623), .A2(N624), .Y(N625) );
  OR2X1_RVT C2204 ( .A1(N618), .A2(N53), .Y(N620) );
  OR2X1_RVT C2200 ( .A1(N614), .A2(N615), .Y(N616) );
  OR2X1_RVT C2196 ( .A1(N610), .A2(N611), .Y(N612) );
  OR2X1_RVT C2233 ( .A1(N647), .A2(N57), .Y(N649) );
  OR2X1_RVT C94 ( .A1(N122), .A2(N123), .Y(N124) );
  OR2X1_RVT C2255 ( .A1(N670), .A2(N622), .Y(N671) );
  OR2X1_RVT C2258 ( .A1(N673), .A2(N644), .Y(N674) );
  OR2X1_RVT C2252 ( .A1(N667), .A2(N617), .Y(N668) );
  OR2X1_RVT C86 ( .A1(n271), .A2(n308), .Y(N118) );
  DFFARX1_RVT ctrl_fsm_cs_reg_2_ ( .D(ctrl_fsm_ns[2]), .CLK(clk), .RSTB(rst_n), 
        .Q(ctrl_fsm_cs[2]), .QN(n140) );
  INVX1_RVT I_28 ( .A(N128), .Y(N644) );
  AND2X1_RVT C84 ( .A1(N115), .A2(N116), .Y(N617) );
  INVX1_RVT I_20 ( .A(ctrl_fsm_cs[0]), .Y(N91) );
  OR2X1_RVT C72 ( .A1(n301), .A2(n285), .Y(N107) );
  OR2X1_RVT C2276 ( .A1(N691), .A2(N58), .Y(N692) );
  OR2X1_RVT C2272 ( .A1(N687), .A2(N53), .Y(N688) );
  OR2X1_RVT C2270 ( .A1(N685), .A2(N666), .Y(N686) );
  OR2X1_RVT C2249 ( .A1(N663), .A2(N664), .Y(N665) );
  AND2X1_RVT C82 ( .A1(n296), .A2(n304), .Y(N115) );
  DFFARX1_RVT debug_mode_q_reg ( .D(debug_mode_n), .CLK(clk), .RSTB(rst_n), 
        .Q(debug_mode_o), .QN(n37) );
  DFFARX1_RVT ctrl_fsm_cs_reg_3_ ( .D(N700), .CLK(clk), .RSTB(rst_n), .Q(
        ctrl_fsm_cs[3]), .QN(N88) );
  INVX1_RVT I_18 ( .A(n281), .Y(N89) );
  OR2X1_RVT C56 ( .A1(n296), .A2(n308), .Y(N95) );
  OR2X1_RVT C68 ( .A1(N90), .A2(n292), .Y(N104) );
  OR2X1_RVT C67 ( .A1(n301), .A2(n304), .Y(N103) );
  OR2X1_RVT C2144 ( .A1(irq_wu_ctrl_i), .A2(debug_req_pending), .Y(N748) );
  OR2X1_RVT C2151 ( .A1(debug_mode_o), .A2(debug_req_pending), .Y(N751) );
  INVX1_RVT I_5 ( .A(ctrl_transfer_insn_in_dec_i[1]), .Y(N707) );
  NBUFFX2_RVT B_50 ( .A(n235), .Y(N50) );
  OR2X1_RVT C2150 ( .A1(N751), .A2(debug_single_step_i), .Y(N752) );
  OR2X1_RVT C63 ( .A1(N90), .A2(n161), .Y(N100) );
  OR2X1_RVT C78 ( .A1(ctrl_fsm_cs[3]), .A2(N89), .Y(N111) );
  OR2X2_RVT C93 ( .A1(ctrl_fsm_cs[1]), .A2(N91), .Y(N123) );
  OR2X1_RVT C80 ( .A1(N111), .A2(N112), .Y(N113) );
  OR2X1_RVT C87 ( .A1(n298), .A2(n305), .Y(N119) );
  OR2X1_RVT C126 ( .A1(n298), .A2(n307), .Y(N143) );
  INVX1_RVT I_55 ( .A(branch_taken_ex_i), .Y(N301) );
  INVX1_RVT I_79 ( .A(is_fetch_failed_i), .Y(N511) );
  INVX1_RVT I_77 ( .A(data_err_i), .Y(N447) );
  NBUFFX2_RVT B_54 ( .A(N621), .Y(N54) );
  OR2X1_RVT C1880 ( .A1(debug_req_pending), .A2(trigger_match_i), .Y(N721) );
  OR2X1_RVT C118 ( .A1(n271), .A2(N89), .Y(N138) );
  AND2X1_RVT C2065 ( .A1(data_err_i), .A2(N301), .Y(N508) );
  OR2X1_RVT C98 ( .A1(n271), .A2(n308), .Y(N126) );
  AND2X1_RVT C2067 ( .A1(is_fetch_failed_i), .A2(N509), .Y(N510) );
  OR2X1_RVT C113 ( .A1(N90), .A2(n161), .Y(N135) );
  OR2X1_RVT C112 ( .A1(N88), .A2(n280), .Y(N134) );
  AND2X1_RVT C2069 ( .A1(N509), .A2(N511), .Y(N512) );
  AND2X1_RVT C1882 ( .A1(irq_req_ctrl_i), .A2(n37), .Y(N177) );
  AND2X1_RVT C2070 ( .A1(instr_valid_i), .A2(N512), .Y(N513) );
  AND2X1_RVT C2071 ( .A1(N177), .A2(N282), .Y(N514) );
  AND2X1_RVT C2110 ( .A1(regfile_we_ex_i), .A2(reg_d_ex_is_reg_a_i), .Y(N742)
         );
  AND2X1_RVT C2109 ( .A1(regfile_we_wb_i), .A2(reg_d_wb_is_reg_a_i), .Y(N741)
         );
  AND2X1_RVT C2111 ( .A1(regfile_alu_we_fw_i), .A2(reg_d_alu_is_reg_a_i), .Y(
        N744) );
  OR2X1_RVT C2108 ( .A1(N741), .A2(N742), .Y(N743) );
  OR2X1_RVT C2107 ( .A1(N743), .A2(N744), .Y(N745) );
  INVX0_RVT I_1 ( .A(wb_ready_i), .Y(N698) );
  OR2X1_RVT C2099 ( .A1(reg_d_ex_is_reg_a_i), .A2(reg_d_ex_is_reg_b_i), .Y(
        N734) );
  AND2X1_RVT C2101 ( .A1(is_decoding_o), .A2(N737), .Y(N738) );
  AND2X1_RVT C2095 ( .A1(data_req_ex_i), .A2(regfile_we_ex_i), .Y(N731) );
  OR2X1_RVT C2098 ( .A1(N734), .A2(reg_d_ex_is_reg_c_i), .Y(N735) );
  AND2X1_RVT C2096 ( .A1(N698), .A2(regfile_we_wb_i), .Y(N732) );
  OR2X1_RVT C2094 ( .A1(N731), .A2(N732), .Y(N733) );
  INVX0_RVT U293 ( .A(N652), .Y(n357) );
  NBUFFX2_RVT U294 ( .A(N124), .Y(n290) );
  AOI21X1_RVT U295 ( .A1(n162), .A2(n275), .A3(N113), .Y(is_decoding_o) );
  INVX0_RVT U296 ( .A(n50), .Y(n275) );
  NOR2X1_RVT U297 ( .A1(N135), .A2(N134), .Y(N57) );
  NBUFFX2_RVT U298 ( .A(n37), .Y(n299) );
  NOR3X0_RVT U299 ( .A1(n286), .A2(N143), .A3(n285), .Y(N650) );
  NBUFFX2_RVT U300 ( .A(ctrl_fsm_cs[0]), .Y(n305) );
  NBUFFX2_RVT U301 ( .A(n296), .Y(n291) );
  NBUFFX2_RVT U302 ( .A(n269), .Y(n297) );
  NBUFFX2_RVT U303 ( .A(ctrl_fsm_cs[2]), .Y(n308) );
  AND2X1_RVT U304 ( .A1(regfile_we_id_i), .A2(n48), .Y(N737) );
  AND2X1_RVT U305 ( .A1(N301), .A2(N447), .Y(N509) );
  OR2X1_RVT U306 ( .A1(n291), .A2(n297), .Y(N99) );
  INVX1_RVT U307 ( .A(n302), .Y(N282) );
  AND2X1_RVT U308 ( .A1(N738), .A2(N534), .Y(N739) );
  AND2X1_RVT U309 ( .A1(n295), .A2(n60), .Y(n16) );
  OR2X1_RVT U310 ( .A1(n293), .A2(n305), .Y(N139) );
  OR2X1_RVT U311 ( .A1(N735), .A2(N739), .Y(N740) );
  OA21X1_RVT U312 ( .A1(n62), .A2(n61), .A3(n16), .Y(n57) );
  NBUFFX2_RVT U313 ( .A(N57), .Y(n283) );
  AND4X1_RVT U314 ( .A1(n127), .A2(n157), .A3(n108), .A4(n158), .Y(n230) );
  NAND2X0_RVT U315 ( .A1(N613), .A2(N161), .Y(n231) );
  OAI21X1_RVT U316 ( .A1(n279), .A2(n277), .A3(n276), .Y(n232) );
  NOR2X0_RVT U317 ( .A1(n243), .A2(N579), .Y(n233) );
  NOR2X0_RVT U318 ( .A1(N651), .A2(N652), .Y(n234) );
  NOR2X0_RVT U319 ( .A1(N103), .A2(N104), .Y(n235) );
  NOR2X0_RVT U320 ( .A1(N99), .A2(N100), .Y(n236) );
  OR2X1_RVT U321 ( .A1(N126), .A2(N127), .Y(N128) );
  INVX1_RVT U322 ( .A(N124), .Y(N621) );
  AOI22X1_RVT U323 ( .A1(ebrk_insn_i), .A2(n176), .A3(n283), .A4(n299), .Y(
        n237) );
  NAND3X0_RVT U324 ( .A1(N644), .A2(uret_dec_i), .A3(n299), .Y(n238) );
  AOI221X1_RVT U325 ( .A1(n306), .A2(fetch_enable_i), .A3(n306), .A4(n289), 
        .A5(n167), .Y(n239) );
  NOR2X0_RVT U326 ( .A1(ctrl_transfer_insn_in_dec_i[0]), .A2(N707), .Y(n240)
         );
  NOR2X0_RVT U327 ( .A1(dret_dec_i), .A2(N418), .Y(n241) );
  INVX1_RVT U328 ( .A(N113), .Y(N615) );
  NOR2X0_RVT U329 ( .A1(mult_multicycle_i), .A2(data_misaligned_i), .Y(n242)
         );
  NOR2X0_RVT U330 ( .A1(N576), .A2(debug_havereset_o), .Y(n243) );
  NOR2X0_RVT U331 ( .A1(N572), .A2(debug_havereset_o), .Y(n244) );
  NOR2X0_RVT U332 ( .A1(N568), .A2(N567), .Y(n245) );
  NOR2X0_RVT U333 ( .A1(debug_req_pending), .A2(n303), .Y(n246) );
  OR2X1_RVT U334 ( .A1(N748), .A2(debug_mode_o), .Y(wake_from_sleep_o) );
  AND2X1_RVT U335 ( .A1(N721), .A2(n37), .Y(N176) );
  NBUFFX2_RVT U336 ( .A(N176), .Y(n302) );
  OR2X1_RVT U337 ( .A1(debug_req_i), .A2(debug_req_q), .Y(debug_req_pending)
         );
  NAND2X0_RVT U338 ( .A1(ebrk_force_debug_mode), .A2(ebrk_insn_i), .Y(n247) );
  INVX1_RVT U339 ( .A(N109), .Y(N613) );
  NOR2X0_RVT U340 ( .A1(N118), .A2(N119), .Y(n248) );
  NOR2X0_RVT U341 ( .A1(N712), .A2(ctrl_transfer_insn_in_dec_i[1]), .Y(n249)
         );
  AND2X1_RVT U342 ( .A1(n240), .A2(N745), .Y(jr_stall_o) );
  NOR2X0_RVT U343 ( .A1(debug_single_step_i), .A2(debug_force_wakeup_q), .Y(
        n250) );
  NOR2X0_RVT U344 ( .A1(current_priv_lvl_i[0]), .A2(current_priv_lvl_i[1]), 
        .Y(n251) );
  NOR2X0_RVT U345 ( .A1(wfi_i), .A2(N371), .Y(n252) );
  NBUFFX2_RVT U346 ( .A(debug_mode_o), .Y(n303) );
  NOR2X0_RVT U347 ( .A1(instr_valid_i), .A2(N172), .Y(n253) );
  NOR2X0_RVT U348 ( .A1(ex_valid_i), .A2(data_err_i), .Y(n254) );
  NBUFFX2_RVT U349 ( .A(N677), .Y(N58) );
  INVX1_RVT U350 ( .A(N140), .Y(N677) );
  OR2X1_RVT U351 ( .A1(N138), .A2(N139), .Y(N140) );
  INVX0_RVT U352 ( .A(1'b1), .Y(hwlp_jump_o) );
  INVX0_RVT U354 ( .A(1'b1), .Y(hwlp_dec_cnt_o[0]) );
  INVX0_RVT U356 ( .A(1'b1), .Y(hwlp_dec_cnt_o[1]) );
  INVX0_RVT U358 ( .A(1'b1), .Y(trap_addr_mux_o[1]) );
  INVX0_RVT U360 ( .A(1'b1), .Y(exc_pc_mux_o[2]) );
  INVX0_RVT U362 ( .A(1'b1), .Y(pc_mux_o[3]) );
  INVX0_RVT U364 ( .A(1'b1), .Y(hwlp_mask_o) );
  INVX0_RVT U366 ( .A(n295), .Y(n273) );
  AND2X1_RVT U367 ( .A1(N109), .A2(N128), .Y(n294) );
  NBUFFX2_RVT U368 ( .A(n280), .Y(n269) );
  AO21X1_RVT U369 ( .A1(branch_taken_ex_i), .A2(N495), .A3(N659), .Y(N661) );
  MUX21X1_RVT U370 ( .A1(N495), .A2(debug_req_entry_q), .S0(n270), .Y(n195) );
  OR2X1_RVT U371 ( .A1(N652), .A2(N693), .Y(n270) );
  NOR2X0_RVT U372 ( .A1(n248), .A2(N650), .Y(n295) );
  NBUFFX2_RVT U373 ( .A(N88), .Y(n271) );
  INVX1_RVT U374 ( .A(N97), .Y(n274) );
  NOR4X1_RVT U375 ( .A1(n274), .A2(n273), .A3(n43), .A4(n272), .Y(n88) );
  NAND2X0_RVT U376 ( .A1(n294), .A2(n282), .Y(n272) );
  INVX1_RVT U377 ( .A(N601), .Y(n358) );
  INVX1_RVT U378 ( .A(n100), .Y(n276) );
  INVX1_RVT U379 ( .A(n138), .Y(n277) );
  NOR2X0_RVT U380 ( .A1(n278), .A2(n95), .Y(n138) );
  OR2X1_RVT U381 ( .A1(data_load_event_i), .A2(n164), .Y(n278) );
  NOR2X0_RVT U382 ( .A1(n161), .A2(n139), .Y(n279) );
  NAND3X0_RVT U383 ( .A1(n239), .A2(n351), .A3(n230), .Y(ctrl_fsm_ns[0]) );
  NBUFFX2_RVT U384 ( .A(n304), .Y(n280) );
  NBUFFX2_RVT U385 ( .A(ctrl_fsm_cs[2]), .Y(n281) );
  NBUFFX2_RVT U386 ( .A(n293), .Y(n288) );
  AO22X1_RVT U387 ( .A1(n243), .A2(debug_mode_n), .A3(n79), .A4(n245), .Y(n74)
         );
  AO21X1_RVT U388 ( .A1(N495), .A2(n91), .A3(n90), .Y(N700) );
  INVX0_RVT U389 ( .A(n112), .Y(N646) );
  OR2X1_RVT U390 ( .A1(N131), .A2(N130), .Y(n112) );
  INVX1_RVT U391 ( .A(N52), .Y(n282) );
  MUX21X1_RVT U392 ( .A1(N493), .A2(illegal_insn_q), .S0(n284), .Y(n194) );
  OR2X1_RVT U393 ( .A1(N652), .A2(N679), .Y(n284) );
  NBUFFX2_RVT U394 ( .A(N89), .Y(n285) );
  NBUFFX2_RVT U395 ( .A(N88), .Y(n286) );
  DELLN1X2_RVT U396 ( .A(n52), .Y(n287) );
  NBUFFX2_RVT U397 ( .A(n292), .Y(n289) );
  NBUFFX2_RVT U398 ( .A(ctrl_fsm_cs[1]), .Y(n293) );
  NBUFFX2_RVT U399 ( .A(ctrl_fsm_cs[0]), .Y(n292) );
  OR2X1_RVT U400 ( .A1(n122), .A2(n121), .Y(ctrl_fsm_ns[2]) );
  NBUFFX2_RVT U401 ( .A(n301), .Y(n296) );
  NBUFFX2_RVT U402 ( .A(ctrl_fsm_cs[3]), .Y(n301) );
  NBUFFX2_RVT U403 ( .A(ctrl_fsm_cs[1]), .Y(n298) );
  NBUFFX2_RVT U404 ( .A(N54), .Y(n300) );
  NBUFFX2_RVT U405 ( .A(n308), .Y(n304) );
  INVX1_RVT U406 ( .A(n154), .Y(n351) );
  AND2X1_RVT U407 ( .A1(n357), .A2(n358), .Y(n89) );
  NBUFFX2_RVT U408 ( .A(N91), .Y(n307) );
  NBUFFX2_RVT U409 ( .A(N601), .Y(n306) );
  NBUFFX2_RVT U410 ( .A(hwlp_start_addr_i[31]), .Y(hwlp_targ_addr_o[31]) );
  NBUFFX2_RVT U411 ( .A(hwlp_start_addr_i[30]), .Y(hwlp_targ_addr_o[30]) );
  NBUFFX2_RVT U412 ( .A(hwlp_start_addr_i[29]), .Y(hwlp_targ_addr_o[29]) );
  NBUFFX2_RVT U413 ( .A(hwlp_start_addr_i[28]), .Y(hwlp_targ_addr_o[28]) );
  NBUFFX2_RVT U414 ( .A(hwlp_start_addr_i[27]), .Y(hwlp_targ_addr_o[27]) );
  NBUFFX2_RVT U415 ( .A(hwlp_start_addr_i[26]), .Y(hwlp_targ_addr_o[26]) );
  NBUFFX2_RVT U416 ( .A(hwlp_start_addr_i[25]), .Y(hwlp_targ_addr_o[25]) );
  NBUFFX2_RVT U417 ( .A(hwlp_start_addr_i[24]), .Y(hwlp_targ_addr_o[24]) );
  NBUFFX2_RVT U418 ( .A(hwlp_start_addr_i[23]), .Y(hwlp_targ_addr_o[23]) );
  NBUFFX2_RVT U419 ( .A(hwlp_start_addr_i[22]), .Y(hwlp_targ_addr_o[22]) );
  NBUFFX2_RVT U420 ( .A(hwlp_start_addr_i[21]), .Y(hwlp_targ_addr_o[21]) );
  NBUFFX2_RVT U421 ( .A(hwlp_start_addr_i[20]), .Y(hwlp_targ_addr_o[20]) );
  NBUFFX2_RVT U422 ( .A(hwlp_start_addr_i[19]), .Y(hwlp_targ_addr_o[19]) );
  NBUFFX2_RVT U423 ( .A(hwlp_start_addr_i[18]), .Y(hwlp_targ_addr_o[18]) );
  NBUFFX2_RVT U424 ( .A(hwlp_start_addr_i[17]), .Y(hwlp_targ_addr_o[17]) );
  NBUFFX2_RVT U425 ( .A(hwlp_start_addr_i[16]), .Y(hwlp_targ_addr_o[16]) );
  NBUFFX2_RVT U426 ( .A(hwlp_start_addr_i[15]), .Y(hwlp_targ_addr_o[15]) );
  NBUFFX2_RVT U427 ( .A(hwlp_start_addr_i[14]), .Y(hwlp_targ_addr_o[14]) );
  NBUFFX2_RVT U428 ( .A(hwlp_start_addr_i[13]), .Y(hwlp_targ_addr_o[13]) );
  NBUFFX2_RVT U429 ( .A(hwlp_start_addr_i[12]), .Y(hwlp_targ_addr_o[12]) );
  NBUFFX2_RVT U430 ( .A(hwlp_start_addr_i[11]), .Y(hwlp_targ_addr_o[11]) );
  NBUFFX2_RVT U431 ( .A(hwlp_start_addr_i[10]), .Y(hwlp_targ_addr_o[10]) );
  NBUFFX2_RVT U432 ( .A(hwlp_start_addr_i[9]), .Y(hwlp_targ_addr_o[9]) );
  NBUFFX2_RVT U433 ( .A(data_misaligned_i), .Y(misaligned_stall_o) );
  NBUFFX2_RVT U434 ( .A(irq_id_o[3]), .Y(exc_cause_o[3]) );
  NBUFFX2_RVT U435 ( .A(csr_cause_o[4]), .Y(irq_id_o[4]) );
  NBUFFX2_RVT U436 ( .A(csr_cause_o[4]), .Y(exc_cause_o[4]) );
  NBUFFX2_RVT U437 ( .A(irq_ack_o), .Y(csr_cause_o[5]) );
  NBUFFX2_RVT U438 ( .A(data_err_ack_o), .Y(csr_save_ex_o) );
  NBUFFX2_RVT U439 ( .A(hwlp_start_addr_i[0]), .Y(hwlp_targ_addr_o[0]) );
  NBUFFX2_RVT U440 ( .A(hwlp_start_addr_i[1]), .Y(hwlp_targ_addr_o[1]) );
  NBUFFX2_RVT U441 ( .A(hwlp_start_addr_i[2]), .Y(hwlp_targ_addr_o[2]) );
  NBUFFX2_RVT U442 ( .A(hwlp_start_addr_i[3]), .Y(hwlp_targ_addr_o[3]) );
  NBUFFX2_RVT U443 ( .A(hwlp_start_addr_i[4]), .Y(hwlp_targ_addr_o[4]) );
  NBUFFX2_RVT U444 ( .A(hwlp_start_addr_i[5]), .Y(hwlp_targ_addr_o[5]) );
  NBUFFX2_RVT U445 ( .A(hwlp_start_addr_i[6]), .Y(hwlp_targ_addr_o[6]) );
  NBUFFX2_RVT U446 ( .A(hwlp_start_addr_i[7]), .Y(hwlp_targ_addr_o[7]) );
  NBUFFX2_RVT U447 ( .A(hwlp_start_addr_i[8]), .Y(hwlp_targ_addr_o[8]) );
  NAND3X0_RVT U448 ( .A1(n231), .A2(N140), .A3(n355), .Y(csr_save_if_o) );
  INVX0_RVT U449 ( .A(n287), .Y(instr_req_o) );
  AND2X1_RVT U450 ( .A1(data_load_event_i), .A2(n22), .Y(perf_pipeline_stall_o) );
  AO21X1_RVT U451 ( .A1(N189), .A2(n24), .A3(n23), .Y(pc_set_o) );
  NAND3X0_RVT U452 ( .A1(n238), .A2(n347), .A3(n348), .Y(pc_mux_o[1]) );
  INVX1_RVT U453 ( .A(n24), .Y(n347) );
  INVX1_RVT U454 ( .A(n36), .Y(n348) );
  OR2X1_RVT U455 ( .A1(n40), .A2(n36), .Y(pc_mux_o[0]) );
  NAND3X0_RVT U456 ( .A1(n349), .A2(n112), .A3(n350), .Y(halt_if_o) );
  INVX1_RVT U457 ( .A(n53), .Y(n349) );
  INVX1_RVT U458 ( .A(halt_id_o), .Y(n350) );
  OR2X1_RVT U459 ( .A1(n32), .A2(n65), .Y(exc_pc_mux_o[1]) );
  AND2X1_RVT U460 ( .A1(N58), .A2(N529), .Y(debug_cause_o[2]) );
  AO21X1_RVT U461 ( .A1(n83), .A2(n299), .A3(n82), .Y(debug_cause_o[1]) );
  OR2X1_RVT U462 ( .A1(n101), .A2(n141), .Y(ctrl_fsm_ns[1]) );
  NAND3X0_RVT U463 ( .A1(n352), .A2(n353), .A3(n237), .Y(csr_save_id_o) );
  INVX0_RVT U464 ( .A(n147), .Y(n353) );
  INVX1_RVT U465 ( .A(n174), .Y(n352) );
  OR2X1_RVT U466 ( .A1(n178), .A2(n177), .Y(csr_save_cause_o) );
  AND3X1_RVT U467 ( .A1(uret_insn_i), .A2(n299), .A3(n34), .Y(
        csr_restore_uret_id_o) );
  AND3X1_RVT U468 ( .A1(mret_insn_i), .A2(n299), .A3(n34), .Y(
        csr_restore_mret_id_o) );
  AND2X1_RVT U469 ( .A1(n34), .A2(dret_insn_i), .Y(csr_restore_dret_id_o) );
  AO21X1_RVT U470 ( .A1(ecall_insn_i), .A2(n179), .A3(irq_id_o[3]), .Y(
        csr_cause_o[3]) );
  NAND3X0_RVT U471 ( .A1(n354), .A2(n355), .A3(n356), .Y(csr_cause_o[0]) );
  INVX1_RVT U472 ( .A(n173), .Y(n355) );
  INVX1_RVT U473 ( .A(data_err_ack_o), .Y(n354) );
  INVX1_RVT U474 ( .A(n184), .Y(n356) );
  INVX1_RVT U475 ( .A(n25), .Y(pc_mux_o[2]) );
  NOR2X1_RVT U476 ( .A1(id_ready_i), .A2(N192), .Y(n359) );
  NOR2X0_RVT U477 ( .A1(data_load_event_i), .A2(N186), .Y(n360) );
  INVX1_RVT U478 ( .A(wake_from_sleep_o), .Y(N155) );
  NOR2X1_RVT U479 ( .A1(N444), .A2(data_err_i), .Y(n361) );
  AND2X1_RVT U480 ( .A1(debug_single_step_i), .A2(n299), .Y(N377) );
  INVX1_RVT U481 ( .A(N377), .Y(N378) );
  AND2X1_RVT U482 ( .A1(debug_single_step_i), .A2(n299), .Y(N375) );
  NOR2X0_RVT U483 ( .A1(N177), .A2(N176), .Y(n362) );
  AND2X1_RVT U484 ( .A1(N733), .A2(N740), .Y(load_stall_o) );
  AND2X1_RVT U485 ( .A1(irq_req_ctrl_i), .A2(n246), .Y(N161) );
  NOR2X0_RVT U486 ( .A1(ctrl_fsm_ns[0]), .A2(N702), .Y(n363) );
  OR2X1_RVT U487 ( .A1(debug_mode_n), .A2(n363), .Y(N582) );
endmodule

