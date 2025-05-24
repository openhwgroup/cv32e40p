
module cv32e40p_controller_tb;

import cv32e40p_pkg::*;  // Import the package here!

  // Parameters
  localparam COREV_CLUSTER = 0;
  localparam COREV_PULP    = 0;
  localparam FPU           = 0;

  // Signals
  reg clk;
  reg clk_ungated_i;
  reg rst_n;
  reg fetch_enable_i;
  wire ctrl_busy_o;
  wire is_decoding_o;
  reg is_fetch_failed_i;
  wire deassert_we_o;
  reg illegal_insn_i;
  reg ecall_insn_i;
  reg mret_insn_i;
  reg uret_insn_i;
  reg dret_insn_i;
  reg mret_dec_i;
  reg uret_dec_i;
  reg dret_dec_i;
  reg wfi_i;
  reg ebrk_insn_i;
  reg fencei_insn_i;
  reg csr_status_i;
  wire hwlp_mask_o;
  reg instr_valid_i;
  wire instr_req_o;
  wire pc_set_o;
  wire [3:0] pc_mux_o;
  wire [2:0] exc_pc_mux_o;
  wire [1:0] trap_addr_mux_o;
  reg [31:0] pc_id_i;
  reg [1:0][31:0] hwlp_start_addr_i;
  reg [1:0][31:0] hwlp_end_addr_i;
  reg [1:0][31:0] hwlp_counter_i;
  wire [1:0] hwlp_dec_cnt_o;
  wire hwlp_jump_o;
  wire [31:0] hwlp_targ_addr_o;
  reg data_req_ex_i;
  reg data_we_ex_i;
  reg data_misaligned_i;
  reg data_load_event_i;
  reg data_err_i;
  wire data_err_ack_o;
  reg mult_multicycle_i;
  reg apu_en_i;
  reg apu_read_dep_i;
  reg apu_read_dep_for_jalr_i;
  reg apu_write_dep_i;
  wire apu_stall_o;
  reg branch_taken_ex_i;
  reg [1:0] ctrl_transfer_insn_in_id_i;
  reg [1:0] ctrl_transfer_insn_in_dec_i;
  reg irq_req_ctrl_i;
  reg irq_sec_ctrl_i;
  reg [4:0] irq_id_ctrl_i;
  reg irq_wu_ctrl_i;
  PrivLvl_t current_priv_lvl_i;
  wire irq_ack_o;
  wire [4:0] irq_id_o;
  wire [4:0] exc_cause_o;
  wire debug_mode_o;
  wire [2:0] debug_cause_o;
  wire debug_csr_save_o;
  reg debug_req_i;
  reg debug_single_step_i;
  reg debug_ebreakm_i;
  reg debug_ebreaku_i;
  reg trigger_match_i;
  wire debug_p_elw_no_sleep_o;
  wire debug_wfi_no_sleep_o;
  wire debug_havereset_o;
  wire debug_running_o;
  wire debug_halted_o;
  wire wake_from_sleep_o;
  wire csr_save_if_o;
  wire csr_save_id_o;
  wire csr_save_ex_o;
  wire [5:0] csr_cause_o;
  wire csr_irq_sec_o;
  wire csr_restore_mret_id_o;
  wire csr_restore_uret_id_o;
  wire csr_restore_dret_id_o;
  wire csr_save_cause_o;
  reg regfile_we_id_i;
  reg [5:0] regfile_alu_waddr_id_i;
  reg regfile_we_ex_i;
  reg [5:0] regfile_waddr_ex_i;
  reg regfile_we_wb_i;
  reg regfile_alu_we_fw_i;
  wire [1:0] operand_a_fw_mux_sel_o;
  wire [1:0] operand_b_fw_mux_sel_o;
  wire [1:0] operand_c_fw_mux_sel_o;
  reg reg_d_ex_is_reg_a_i;
  reg reg_d_ex_is_reg_b_i;
  reg reg_d_ex_is_reg_c_i;
  reg reg_d_wb_is_reg_a_i;
  reg reg_d_wb_is_reg_b_i;
  reg reg_d_wb_is_reg_c_i;
  reg reg_d_alu_is_reg_a_i;
  reg reg_d_alu_is_reg_b_i;
  reg reg_d_alu_is_reg_c_i;
  wire halt_if_o;
  wire halt_id_o;
  wire misaligned_stall_o;
  wire jr_stall_o;
  wire load_stall_o;
  reg id_ready_i;
  reg id_valid_i;
  reg ex_valid_i;
  reg wb_ready_i;
  wire perf_pipeline_stall_o;

  // Instantiate the module under test
  cv32e40p_controller #(
    .COREV_CLUSTER(COREV_CLUSTER),
    .COREV_PULP(COREV_PULP),
    .FPU(FPU)
  ) u_cv32e40p_controller (
    .clk(clk),
    .clk_ungated_i(clk_ungated_i),
    .rst_n(rst_n),
    .fetch_enable_i(fetch_enable_i),
    .ctrl_busy_o(ctrl_busy_o),
    .is_decoding_o(is_decoding_o),
    .is_fetch_failed_i(is_fetch_failed_i),
    .deassert_we_o(deassert_we_o),
    .illegal_insn_i(illegal_insn_i),
    .ecall_insn_i(ecall_insn_i),
    .mret_insn_i(mret_insn_i),
    .uret_insn_i(uret_insn_i),
    .dret_insn_i(dret_insn_i),
    .mret_dec_i(mret_dec_i),
    .uret_dec_i(uret_dec_i),
    .dret_dec_i(dret_dec_i),
    .wfi_i(wfi_i),
    .ebrk_insn_i(ebrk_insn_i),
    .fencei_insn_i(fencei_insn_i),
    .csr_status_i(csr_status_i),
    .hwlp_mask_o(hwlp_mask_o),
    .instr_valid_i(instr_valid_i),
    .instr_req_o(instr_req_o),
    .pc_set_o(pc_set_o),
    .pc_mux_o(pc_mux_o),
    .exc_pc_mux_o(exc_pc_mux_o),
    .trap_addr_mux_o(trap_addr_mux_o),
    .pc_id_i(pc_id_i),
    .hwlp_start_addr_i(hwlp_start_addr_i),
    .hwlp_end_addr_i(hwlp_end_addr_i),
    .hwlp_counter_i(hwlp_counter_i),
    .hwlp_dec_cnt_o(hwlp_dec_cnt_o),
    .hwlp_jump_o(hwlp_jump_o),
    .hwlp_targ_addr_o(hwlp_targ_addr_o),
    .data_req_ex_i(data_req_ex_i),
    .data_we_ex_i(data_we_ex_i),
    .data_misaligned_i(data_misaligned_i),
    .data_load_event_i(data_load_event_i),
    .data_err_i(data_err_i),
    .data_err_ack_o(data_err_ack_o),
    .mult_multicycle_i(mult_multicycle_i),
    .apu_en_i(apu_en_i),
    .apu_read_dep_i(apu_read_dep_i),
    .apu_read_dep_for_jalr_i(apu_read_dep_for_jalr_i),
    .apu_write_dep_i(apu_write_dep_i),
    .apu_stall_o(apu_stall_o),
    .branch_taken_ex_i(branch_taken_ex_i),
    .ctrl_transfer_insn_in_id_i(ctrl_transfer_insn_in_id_i),
    .ctrl_transfer_insn_in_dec_i(ctrl_transfer_insn_in_dec_i),
    .irq_req_ctrl_i(irq_req_ctrl_i),
    .irq_sec_ctrl_i(irq_sec_ctrl_i),
    .irq_id_ctrl_i(irq_id_ctrl_i),
    .irq_wu_ctrl_i(irq_wu_ctrl_i),
    .current_priv_lvl_i(current_priv_lvl_i),
    .irq_ack_o(irq_ack_o),
    .irq_id_o(irq_id_o),
    .exc_cause_o(exc_cause_o),
    .debug_mode_o(debug_mode_o),
    .debug_cause_o(debug_cause_o),
    .debug_csr_save_o(debug_csr_save_o),
    .debug_req_i(debug_req_i),
    .debug_single_step_i(debug_single_step_i),
    .debug_ebreakm_i(debug_ebreakm_i),
    .debug_ebreaku_i(debug_ebreaku_i),
    .trigger_match_i(trigger_match_i),
    .debug_p_elw_no_sleep_o(debug_p_elw_no_sleep_o),
    .debug_wfi_no_sleep_o(debug_wfi_no_sleep_o),
    .debug_havereset_o(debug_havereset_o),
    .debug_running_o(debug_running_o),
    .debug_halted_o(debug_halted_o),
    .wake_from_sleep_o(wake_from_sleep_o),
    .csr_save_if_o(csr_save_if_o),
    .csr_save_id_o(csr_save_id_o),
    .csr_save_ex_o(csr_save_ex_o),
    .csr_cause_o(csr_cause_o),
    .csr_irq_sec_o(csr_irq_sec_o),
    .csr_restore_mret_id_o(csr_restore_mret_id_o),
    .csr_restore_uret_id_o(csr_restore_uret_id_o),
    .csr_restore_dret_id_o(csr_restore_dret_id_o),
    .csr_save_cause_o(csr_save_cause_o),
    .regfile_we_id_i(regfile_we_id_i),
    .regfile_alu_waddr_id_i(regfile_alu_waddr_id_i),
    .regfile_we_ex_i(regfile_we_ex_i),
    .regfile_waddr_ex_i(regfile_waddr_ex_i),
    .regfile_we_wb_i(regfile_we_wb_i),
    .regfile_alu_we_fw_i(regfile_alu_we_fw_i),
    .operand_a_fw_mux_sel_o(operand_a_fw_mux_sel_o),
    .operand_b_fw_mux_sel_o(operand_b_fw_mux_sel_o),
    .operand_c_fw_mux_sel_o(operand_c_fw_mux_sel_o),
    .reg_d_ex_is_reg_a_i(reg_d_ex_is_reg_a_i),
    .reg_d_ex_is_reg_b_i(reg_d_ex_is_reg_b_i),
    .reg_d_ex_is_reg_c_i(reg_d_ex_is_reg_c_i),
    .reg_d_wb_is_reg_a_i(reg_d_wb_is_reg_a_i),
    .reg_d_wb_is_reg_b_i(reg_d_wb_is_reg_b_i),
    .reg_d_wb_is_reg_c_i(reg_d_wb_is_reg_c_i),
    .reg_d_alu_is_reg_a_i(reg_d_alu_is_reg_a_i),
    .reg_d_alu_is_reg_b_i(reg_d_alu_is_reg_b_i),
    .reg_d_alu_is_reg_c_i(reg_d_alu_is_reg_c_i),
    .halt_if_o(halt_if_o),
    .halt_id_o(halt_id_o),
    .misaligned_stall_o(misaligned_stall_o),
    .jr_stall_o(jr_stall_o),
    .load_stall_o(load_stall_o),
    .id_ready_i(id_ready_i),
    .id_valid_i(id_valid_i),
    .ex_valid_i(ex_valid_i),
    .wb_ready_i(wb_ready_i),
    .perf_pipeline_stall_o(perf_pipeline_stall_o)
  );

  // Clock generation
  initial begin
    clk = 0;
    clk_ungated_i = 0;
    forever #5 clk = ~clk;
    forever #5 clk_ungated_i = ~clk_ungated_i;
  end

  // Reset sequence
  initial begin
    rst_n = 0;
    #10;
    rst_n = 1;
  end

  // Testbench stimulus
  initial begin
    // Initialize signals
    fetch_enable_i = 0;
    is_fetch_failed_i = 0;
    illegal_insn_i = 0;
    ecall_insn_i = 0;
    mret_insn_i = 0;
    uret_insn_i = 0;
    dret_insn_i = 0;
    mret_dec_i = 0;
    uret_dec_i = 0;
    dret_dec_i = 0;
    wfi_i = 0;
    ebrk_insn_i = 0;
    fencei_insn_i = 0;
    csr_status_i = 0;
    instr_valid_i = 0;
    pc_id_i = 0;
    data_req_ex_i = 0;
    data_we_ex_i = 0;
    data_misaligned_i = 0;
    data_load_event_i = 0;
    data_err_i = 0;
    mult_multicycle_i = 0;
    apu_en_i = 0;
    apu_read_dep_i = 0;
    apu_read_dep_for_jalr_i = 0;
    apu_write_dep_i = 0;
    branch_taken_ex_i = 0;
    ctrl_transfer_insn_in_id_i = 0;
    ctrl_transfer_insn_in_dec_i = 0;
    irq_req_ctrl_i = 0;
    irq_sec_ctrl_i = 0;
    irq_id_ctrl_i = 0;
    irq_wu_ctrl_i = 0;
    current_priv_lvl_i = 0;
    debug_req_i = 0;
    debug_single_step_i = 0;
    debug_ebreakm_i = 0;
    debug_ebreaku_i = 0;
    trigger_match_i = 0;
    regfile_we_id_i = 0;
    regfile_alu_waddr_id_i = 0;
    regfile_we_ex_i = 0;
    regfile_waddr_ex_i = 0;
    regfile_we_wb_i = 0;
    regfile_alu_we_fw_i = 0;
    reg_d_ex_is_reg_a_i = 0;
    reg_d_ex_is_reg_b_i = 0;
    reg_d_ex_is_reg_c_i = 0;
    reg_d_wb_is_reg_a_i = 0;
    reg_d_wb_is_reg_b_i = 0;
    reg_d_wb_is_reg_c_i = 0;
    reg_d_alu_is_reg_a_i = 0;
    reg_d_alu_is_reg_b_i = 0;
    reg_d_alu_is_reg_c_i = 0;
    id_ready_i = 1;
    id_valid_i = 1;
    ex_valid_i = 1;
    wb_ready_i = 1;
    hwlp_start_addr_i[0] = 32'h0;
    hwlp_start_addr_i[1] = 32'h10;
    hwlp_end_addr_i[0] = 32'h8;
    hwlp_end_addr_i[1] = 32'h18;
    hwlp_counter_i[0] = 32'h5;
    hwlp_counter_i[1] = 32'hA;


    $display("Starting simulation...");

    // Test reset
    #20;
    fetch_enable_i = 1;
    #10
    if ( is_decoding_o != 1'b0) begin
           $display("ERROR 1: reset");
          // $finish;
        end
    if ( is_decoding_o == 1'b0) begin
	  $display("Pass 1: reset");
           //$finish;
        end

    // Test basic instruction fetch and decode
    #10;
    instr_valid_i = 1;
    #10;
   if ( is_decoding_o != 1'b1) begin
           $display("ERROR 2: fetch");
          // $finish;
        end
    if ( is_decoding_o == 1'b1) begin
          $display("Pass 2: fetch");
           //$finish;
        end

    instr_valid_i = 0;
    #10
    

    // Test illegal instruction
    #10;
    instr_valid_i = 1;
    illegal_insn_i = 1;
    #10;
    illegal_insn_i = 0;
    instr_valid_i = 0;

     // Test ecall instruction
    #10;
    instr_valid_i = 1;
    ecall_insn_i = 1;
    #10;
    ecall_insn_i = 0;
    instr_valid_i = 0;

    // Test mret instruction
    #10;
    instr_valid_i = 1;
    mret_insn_i = 1;
    #10;
    mret_insn_i = 0;
    instr_valid_i = 0;

    // Test uret instruction
    #10;
    instr_valid_i = 1;
    uret_insn_i = 1;
    #10;
    uret_insn_i = 0;
    instr_valid_i = 0;

    // Test dret instruction
    #10;
    instr_valid_i = 1;
    dret_insn_i = 1;
    #10;
    dret_insn_i = 0;
    instr_valid_i = 0;

    // Test wfi instruction
    #10;
    instr_valid_i = 1;
    wfi_i = 1;
    #10;
    wfi_i = 0;
    instr_valid_i = 0;

    // Test ebreak instruction
    #10;
    instr_valid_i = 1;
    ebrk_insn_i = 1;
    #10;
    ebrk_insn_i = 0;
    instr_valid_i = 0;

    // Test fencei instruction
    #10;
    instr_valid_i = 1;
    fencei_insn_i = 1;
    #10;
    fencei_insn_i = 0;
    instr_valid_i = 0;

    // Test csr_status instruction
    #10;
    instr_valid_i = 1;
    csr_status_i = 1;
    #10;
    csr_status_i = 0;
    instr_valid_i = 0;

    // Test data error
    #10;
    instr_valid_i = 1;
    data_err_i = 1;
    data_we_ex_i = 1;
    #10;
    data_err_i = 0;
    data_we_ex_i = 0;
    instr_valid_i = 0;

    // Test interrupt
    #10;
    irq_req_ctrl_i = 1;
    irq_id_ctrl_i = 5;
    #10;
    irq_req_ctrl_i = 0;
    irq_id_ctrl_i = 0;

    // Test debug request
    #10;
    debug_req_i = 1;
    #10;
    debug_req_i = 0;

    $display("Simulation finished.");
    #10 $finish;
  end

   // This is to create a dump file for offline viewing
   initial begin
        $fsdbDumpfile("cv32e40p_controller_tb.fsdb");
        $fsdbDumpvars(0, cv32e40p_controller_tb);
        $dumpfile("cv32e40p_controller_tb.vcd");
        $dumpvars(0);
     end
endmodule
