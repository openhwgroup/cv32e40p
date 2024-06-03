///////////////////////////////////////////////////////////////////////////////
//                                                                           //
// RISC-V Checker                                                            //
//                                                                           //
// This material contains trade secrets or otherwise confidential            //
// information owned by Siemens Industry Software Inc. or its affiliates     //
// (collectively, "SISW"), or its licensors. Access to and use of this       //
// information is strictly limited as set forth in the Customer's applicable //
// agreements with SISW.                                                     //
//                                                                           //
// This material may not be copied, distributed, or otherwise disclosed      //
// outside of the Customer's facilities without the express written          //
// permission of SISW, and may not be used in any way not expressly          //
// authorized by SISW.                                                       //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////

`include "tidal.sv"
`include "RISCV_ISA.sv"
import RISCV_ISA::*;

/*********************/
// DEBUG GROUPS
/*********************/

(* ONESPIN_APP            = "Processor" *)
(* ONESPIN_VIP_NAME       = "RISC-V" *)
(* ONESPIN_VIP_TYPE       = "cpu" *)
(* ONESPIN_VIP_TRANSACTION= "instr" *)
(* ONESPIN_VIP_GROUP_1    = "{{IF} if_valid}" *)
(* ONESPIN_VIP_GROUP_1_X  = "/instr_addr_o /instr_req_o /instr_gnt_i /instr_rvalid_i /instr_rdata_i /pc_if /if_stage_i.fetch_valid /if_stage_i.fetch_rdata /if_stage_i.fetch_ready /if_stage_i.instr_valid /if_stage_i.instr_aligned /if_stage_i.if_ready /halt_if " *)
(* ONESPIN_VIP_GROUP_2    = "{{ID} id_valid}" *)
(* ONESPIN_VIP_GROUP_2_X  = "/pc_id /instr_valid_id /instr_rdata_id /is_compressed_id /is_fetch_failed_id /clear_instr_valid /id_stage_i.controller_i.ctrl_fsm_cs /id_stage_i.controller_i.ctrl_fsm_ns /id_stage_i.misaligned_stall /id_stage_i.jr_stall /id_stage_i.load_stall /id_stage_i.apu_stall /id_stage_i.csr_apu_stall /id_stage_i.branch_taken_ex /id_ready /id_stage_i.halt_id" *)
(* ONESPIN_VIP_GROUP_3    = "{{EX} ex_valid}" *)
(* ONESPIN_VIP_GROUP_3_X  = "/pc_ex /alu_en_ex /id_stage_i.decoder_i.alu_operator_o /alu_operand_a_ex /alu_operand_b_ex /ex_stage_i.alu_result /ex_stage_i.alu_ready /ex_stage_i.mult_ready mul_op_a mul_op_b mul_op_c mul_result /ex_stage_i.alu_i.div_valid div_result_valid /ex_stage_i.alu_i.result_div div_op_a div_op_b div_result_valid div_result /lsu_ready_ex /ex_ready" *)
(* ONESPIN_VIP_GROUP_4    = "{{MEM} mem_valid}" *)
(* ONESPIN_VIP_GROUP_4_X  = "/data_we_o /data_addr_o /data_req_o /data_be_o /data_sign_ext_ex /data_type_ex /data_wdata_o /data_gnt_i /data_rvalid_i /data_rdata_i /lsu_rdata rf_we_lsu rf_waddr_lsu lsu_data_type lsu_data_sign lsu_data_offset" *)
(* ONESPIN_VIP_GROUP_5    = "{{WB} wb_valid}" *)
(* ONESPIN_VIP_GROUP_5_X  = "/id_stage_i.register_file_i.we_b_i /id_stage_i.register_file_i.waddr_b_i /id_stage_i.register_file_i.wdata_b_i /id_stage_i.register_file_i.we_b_dec /id_stage_i.register_file_i.we_a_i /id_stage_i.register_file_i.waddr_a_i /id_stage_i.register_file_i.wdata_a_i /id_stage_i.register_file_i.we_a_dec /id_stage_i.register_file_i.mem /lsu_ready_wb /ex_stage_i.wb_ready_i" *)
(* ONESPIN_VIP_GROUP_6    = "CSRs" *)
(* ONESPIN_VIP_GROUP_6_X  = "/csr_access_ex /csr_op /csr_addr /csr_wdata /csr_rdata /csr_cause /cs_registers_i.mepc_q /cs_registers_i.mcause_q /cs_registers_i.mstatus_q /cs_registers_i.mie_q /cs_registers_i.mtvec_q /cs_registers_i.fflags_q /cs_registers_i.frm_q" *)
(* ONESPIN_VIP_GROUP_7    = "XCPTs" *)
(* ONESPIN_VIP_GROUP_7_X  = "/current_priv_lvl /pc_set /exc_cause /cs_registers_i.exception_pc /if_stage_i.exc_pc /if_stage_i.fetch_failed /instr_err_pmp /data_err_pmp /data_err_ack /id_stage_i.illegal_insn_dec /illegal_c_insn_id /id_stage_i.fencei_insn_dec /id_stage_i.ebrk_insn_dec /id_stage_i.ecall_insn_dec /id_stage_i.mret_insn_dec /id_stage_i.uret_insn_dec /id_stage_i.dret_insn_dec" *)
(* ONESPIN_VIP_GROUP_8    = "INTRs" *)
(* ONESPIN_VIP_GROUP_8_X  = "/irq_i /irq_id_o /irq_ack_o" *)
(* ONESPIN_VIP_GROUP_9    = "DBG" *)
(* ONESPIN_VIP_GROUP_9_X  = "/debug_mode /debug_req_i /debug_cause /debug_ebreakm /debug_ebreaku /debug_single_step /debug_csr_save /cs_registers_i.dcsr_q /cs_registers_i.depc_q" *)
(* ONESPIN_VIP_GROUP_A    = "FPU" *)
(* ONESPIN_VIP_GROUP_A_X  = "fpu_op_valid fpu_op_a fpu_op_b fpu_op_c fpu_op_ex fpu_lat_ex fpu_waddr_ex fpu_result_valid fpu_s_cycle fpu_m_cycle ex_stage_i.gen_apu.apu_disp_i.apu_lat fpu_waddr fpu_result fpu_flags" *)

/*********************/
// VIP's MODULE
/*********************/

module RISCV_checker  #(
	localparam logic[5:0] ALENX=ALEN<XLEN?ALEN+6'd1:ALEN
) (
	// Clock and reset
	input                  clk,                   // Clock
	input                  rst_n,                 // Active low reset

	// Fetch memory interface
	input                  fetch_req_valid,       // Fetch request presence
	input                  fetch_req_ready,       // Fetch request acknowledgment (by fetch unit)
	input[ALENX-1:0]       fetch_req_PC,          // Fetch request address
	input                  fetch_resp_valid,      // Fetch response presence
	input                  fetch_resp_ready,      // Fetch response acknowledgment (by core)
	input[ALENX-1:0]       fetch_resp_PC,         // Fetch response address (fetched instruction PC)
	(* OSS_TCL_VALUE_PRINTER = "PVE_disass" *) input[31:0] fetch_resp_data, // Fetch response read data (fetched instruction)

	// Data memory interface
	input                  dmem_req_valid,        // Data memory request presence
	input                  dmem_req_ready,        // Data memory request acknowledgment (by data memory unit)
	input[ALENX-1:0]       dmem_req_addr,         // Data memory request address
	input[XLEN-1:0]        dmem_req_data,         // Data memory request written data (stored data)
	input                  dmem_req_cancel,       // Data memory request cancelation (not relevant in case memory requests are not speculatively issued)
	input                  dmem_resp_valid,       // Data memory response presence
	input                  dmem_resp_ready,       // Data memory response acknowledgment (by core)
	input[XLEN-1:0]        dmem_resp_data,        // Data memory response read data (loaded data)

	// Control and status registers
	input[11:0]            csr_addr,              // CSR address signal
	input[XLEN-1:0]        csr_rdata,             // CSR read data signal
	input CSR_struct_t     CSR,                   // Control and status register struct

	// Register files
	input[NUM_XREGS-1:0][XLEN-1:0] pipe_XR,       // Integer register file
	input[31:0][FLEN-1:0]  pipe_FR = '0,          // Floating-point register file

	// Control signals
	input[PIPE_STAGES-1:0] full,                  // Pipeline stage instruction validity
	input[PIPE_STAGES-1:0] stall,                 // Pipeline stage instruction stalling (instruction must not proceed to the next stage)
	input[PIPE_STAGES-1:0] flush,                 // Pipeline stage instruction flushing (instruction causes any later instructions to be flushed)
	input PVE_t PVE='0,                           // Pipeline stage processor verification struct

	// Interrupts & Debug
	input interrupt_in_t   interrupt_in,          // Interrupt struct
	input[XLEN-1:0]        DBG_PC      = 'h800,   // Debug mode entering PC
	input[XLEN-1:0]        DBG_XCPT_PC = 'h808,   // Debug mode exception PC

	// Other IO
	`include "io.sv"
);

default clocking default_clk @(posedge clk); endclocking

/*********************/
// VERIFICATION LOGIC
/*********************/

`define core cv32e40p_core
import cv32e40p_pkg::*;

localparam FPU_LATENCY = `core.FPU_ADDMUL_LAT;

reg[4:0] id_instr_cnt;
always_ff @(posedge clk) begin
	if (~rst_n)
		id_instr_cnt <= 5'h0;
	else if (full[0]&~stall[0]&~flush[0]&(id_instr_cnt<5'h1f))
		id_instr_cnt <= id_instr_cnt + 5'h1;
end

logic[31:0] iword_if, iword_id, iword_wb;
logic[XLEN-1:0] pc_if, pc_id, pc_wb;

assign iword_if = fetch_resp_data;
assign pc_if = fetch_resp_PC;

always_ff @(posedge clk)
	if (fetch_resp_valid & if_stage_i.if_valid)
		{iword_id,pc_id} <= {iword_if,pc_if};

logic[31:0] sboard_FR, sboard_XR;
always_ff @(posedge clk)
	if (~rst_n) begin
		sboard_FR <='0;
		sboard_XR <='0;
	end else begin
	if (fpu_op_valid && (fpu_lat_ex==2'h3 || fpu_lat_ex==2'h2))
		if (fpu_waddr_ex[5])
			sboard_FR[fpu_waddr_ex[4:0]] <= 1'b1;
		else
			sboard_XR[fpu_waddr_ex[4:0]] <= 1'b1;
	if (fpu_result_valid && (fpu_op_valid -> ~(fpu_waddr_ex==fpu_waddr && (MISA.F|Zfinx -> fpu_lat_ex==ex_stage_i.gen_apu.apu_disp_i.apu_lat))))
		if (fpu_waddr[5])
			sboard_FR[fpu_waddr[4:0]] <= 1'b0;
		else
			sboard_XR[fpu_waddr[4:0]] <= 1'b0;
	end

/*********************/
// DEBUG SIGNALS
/*********************/

(* OSS_TCL_VALUE_PRINTER = "PVE_disass" *) logic[32:0] instr;
assign instr = $past({full[0],iword_id});

wire if_valid = if_stage_i.if_valid;
wire id_valid = `core.id_valid;
wire ex_valid = `core.ex_valid;
wire mem_valid = `core.data_req_o;
wire wb_valid = `core.wb_valid;

/*********************/
// ARCHITECTURE STATE
/*********************/

Arch_state_t Arch;
always_comb begin
	foreach (Arch.X[i])
		if (i==0)
			Arch.X[i] <= '{valid: 1'b1, data: '0};
		else
			Arch.X[i] <= '{valid: ~((rf_we_lsu&rf_waddr_lsu==i)|sboard_XR[i]), data: pipe_XR[i]};
	if (MISA.F && ~Zfinx)
		foreach (Arch.F[i])
			Arch.F[i] <= '{valid: ~((rf_we_lsu&rf_waddr_lsu==(i+6'd32))|sboard_FR[i]), data: pipe_FR[i]};

	Arch.CSR <= CSR;
`ifdef CFG_XP
	Arch.CSR.lpstart <= $past(CSR.lpstart);
	Arch.CSR.lpend   <= $past(CSR.lpend);
	Arch.CSR.lpcount <= $past(CSR.lpcount);
`endif
	Arch.PC <= $past(full[0]?pc_id:pc_if);
end

/*********************/
// MODEL
/*********************/

prio_interrupt_t prio_interrupt;
assign prio_interrupt = prioritize_interrupt($past(interrupt_in,WB_OFFSET),Arch.CSR);

execute_t execute;
assign execute = ISA_exe($past(iword_id),
						$past(is_sstep,WB_OFFSET),
						prio_interrupt,
					  '{Fetch_Access_Fault:{xcpt_af_instr_2nd,xcpt_af_instr_1st},
						BreakpointF:        xcpt_bp_if,
						BreakpointL:        xcpt_bp_ld,
						BreakpointS:        xcpt_bp_samo,
						DBGBreakpointF:     $past(Arch.CSR.tdata1[0].typ==2 && Arch.CSR.tdata1[0].execute,WB_OFFSET) && Arch.PC==CSR.tdata2[0] && $past(~Arch.CSR.curDebug,WB_OFFSET),
						DBGBreakpointL:     xcpt_dbg_bp_ld,
						DBGBreakpointS:     xcpt_dbg_bp_samo,
						Load_Addr_Align:    xcpt_ma_ld,
						Load_Access_Fault: {xcpt_af_ld_2nd,xcpt_af_ld_1st},
						SAMO_Addr_Align:    xcpt_ma_samo,
						SAMO_Access_Fault: {xcpt_af_samo_2nd,xcpt_af_samo_1st},
						Fetch_Page_Fault:  {xcpt_pf_instr_2nd,xcpt_pf_instr_1st},
						Load_Page_Fault:   {xcpt_pf_ld_2nd,xcpt_pf_ld_1st},
						SAMO_Page_Fault:   {xcpt_pf_samo_2nd,xcpt_pf_samo_1st}},
						Arch);

/*********************/
// FUNCTIONS
/*********************/

function automatic [1:NUM_RS][1:0] compose_selection(logic[1:0] op_a_sl='0, logic[1:0] op_b_sl='0, logic[1:0] op_c_sl='0);
	compose_selection = '{1: op_a_sl, 2: op_b_sl, default: op_c_sl};
endfunction

function automatic CSR_struct_t CSR_hw_update(input CSR_struct_t cur_CSR, input CSR_struct_t next_CSR, input logic is_retired=1'b0, input fflags_t fflags='{default:'0});
`ifdef SKIP_CSR_CHECK
	CSR_hw_update=next_CSR;
`else
	CSR_hw_update=skip_CSR_update(cur_CSR,next_CSR);
	if (MISA.F|Zfinx) begin
		CSR_hw_update.fflags=next_CSR.fflags; // **I** Skip checking fflags updates
		if (MISA.F)
			CSR_hw_update.mstatus.FS=next_CSR.mstatus.FS; // **I** Skip checking mstatus.FS updates
	end
	if (NUM_COUNTERS>0)
		CSR_hw_update.mcycle=next_CSR.mcycle;
	if (NUM_COUNTERS>2 && is_retired)
		CSR_hw_update.minstret={CSR_hw_update.minstret+64'h1}[63:0];
	if (NUM_COUNTERS>3)
		CSR_hw_update.mhpmcounter=next_CSR.mhpmcounter;
`ifdef CFG_XP
	CSR_hw_update.lpcount=next_CSR.lpcount; // **I** Skip checking lpcount updates
`endif
`endif
endfunction

function automatic pc_check(input logic[XLEN-1:0] expected_pc);
	pc_check=1'b1;
`ifndef SKIP_PC_CHECK
	pc_check&=expected_pc==Arch.PC;
`endif
endfunction

function automatic op_check(input execute_t exe, input op_t rtl_op='0, input [1:NUM_RS][1:0] sl='0);
	op_check=1'b1;
`ifndef SKIP_RF_CHECK
	foreach (rtl_op[i])
		op_check&=(exe.dec.RS[i].valid -> expected_op_data(exe.op[i][XLEN-1:0],sl[i])==rtl_op[i]);
`endif
endfunction

function logic[1:0] data_size_enc(input logic[1:0] data_size);
	case(data_size)
		ms_byte: data_size_enc = ms_word;
		ms_half: data_size_enc = ms_half;
		ms_word: data_size_enc = ms_byte;
		default: data_size_enc = ms_double;
	endcase
endfunction

function reg_t expected_op_data(input reg_t op, input logic[1:0] sl='0);
	case(sl)
		2'h0:    expected_op_data = op;
		2'h1:    expected_op_data = {op[XLEN/2-1:0],op[XLEN/2-1:0]};
		2'h2:    expected_op_data = {op[XLEN/4-1:0],op[XLEN/4-1:0],op[XLEN/4-1:0],op[XLEN/4-1:0]};
		2'h3:    expected_op_data = op<<div_op_b_shift;
		default: expected_op_data = op;
	endcase
endfunction

/*********************/
// SEQUENCES
/*********************/

sequence reset_sequence;
	~rst_n;
endsequence

property pipe_fetch_req(t_start, t_req);
	t_req##0 fetch_req_valid and
`ifndef SKIP_PC_CHECK
	t_req##0 fetch_req_PC==boot_addr and
`endif
	during_excl(t_start,t_req,~fetch_req_valid);
endproperty

property pipe_dmem_no_req(t_start, t_end);
`ifdef SKIP_DMEM_CHECK
	t##0 1'b1;
`else
	during(t_start,t_end,~dmem_req_valid);
`endif
endproperty

sequence pipe_dmem_1st_req(t_req, execute_t exe);
`ifdef SKIP_DMEM_CHECK
	t##0 1'b1;
`else
	t_req##0 dmem_req_valid==exe.mem.valid and
	t_req##0 dmem_req_addr=={encVA(exe.mem.addr)}[ALENX-1:0] and
	t_req##0 dmem_req_we==(exe.mem.cmd inside {mc_store,mc_sc}) and
	t_req##0 dmem_req_be==exe.mem.byte_enable[3:0] and
	t_req##0 (exe.mem.cmd inside {mc_store,mc_sc} -> check_wdata(exe.mem,dmem_req_data));
`endif
endsequence

sequence pipe_dmem_2nd_req(t_req, execute_t exe);
`ifdef SKIP_DMEM_CHECK
	t##0 1'b1;
`else
	t_req##0 dmem_req_valid==exe.mem.valid and
	t_req##0 dmem_req_addr=={encVA({exe.mem.addr[XLEN-1:2],2'b00})+32'd4}[ALENX-1:0] and
	t_req##0 dmem_req_we==(exe.mem.cmd inside {mc_store,mc_sc}) and
	t_req##0 dmem_req_be==exe.mem.byte_enable[7:4] and
	t_req##0 (exe.mem.cmd inside {mc_store,mc_sc} -> check_wdata(exe.mem,dmem_req_data,1'b1));
`endif
endsequence

sequence pipe_reset(t_wb, Arch_state_t cur_Arch=Arch);
	t_wb##0 all_regs_valid(cur_Arch) && cur_Arch.X[0].data=='0 and
	t_wb##0 no_rf_update($past(cur_Arch),cur_Arch) and
	t_wb##0 RISCV_CSR_reset_state(cur_Arch.CSR) and
	t_wb##0 CSR_hw_update($past(cur_Arch.CSR),cur_Arch.CSR)==cur_Arch.CSR and
	t_wb##0 pc_check(boot_addr);
endsequence

sequence pipe_bubble(t_wb, Arch_state_t cur_Arch, Arch_state_t next_Arch=Arch);
	t_wb##1 no_rf_update(cur_Arch,next_Arch) and
	t_wb##1 CSR_hw_update(cur_Arch.CSR,next_Arch.CSR)==next_Arch.CSR and
	t_wb##1 pc_check(cur_Arch.PC);
endsequence

sequence pipe_ret(t_wb, Arch_state_t cur_Arch, execute_t exe, Arch_state_t next_Arch=Arch);
	t_wb##1 no_rf_update(cur_Arch,next_Arch) and
	t_wb##1 CSR_hw_update(exe.next_CSR,next_Arch.CSR,~exe.csr.count_inhibit.IR)==next_Arch.CSR and
	t_wb##1 pc_check(exe.next_pc.ret_PC);
endsequence

sequence pipe_xcpt(t_wb, Arch_state_t cur_Arch, xcpt_t xcpt, Arch_state_t next_Arch=Arch);
	t_wb##1 no_rf_update(cur_Arch,next_Arch) and
	t_wb##1 CSR_hw_update(CSR_xcpt_update(cur_Arch.CSR,xcpt),next_Arch.CSR)==next_Arch.CSR and
	t_wb##1 pc_check(CSR_xcpt_pc(cur_Arch.CSR,xcpt));
endsequence

sequence pipe_instr(t_wb, Arch_state_t cur_Arch, execute_t exe, result_t result='0, logic[1:NUM_RD] check_result='1, Arch_state_t next_Arch=Arch);
	t_wb##1 (~exe.mem.valid & ~exe.fpu.valid) -> no_pending_results_used(exe.dec,cur_Arch) and // **I** don't check registers validity for memory or FPU instructions
	t_wb##1 pipe_rf_check(exe.dec.RD,result,cur_Arch,check_result,next_Arch) and
	t_wb##1 CSR_hw_update(CSR_instr_update(exe.csr,exe.next_CSR,CSR),next_Arch.CSR,~exe.csr.count_inhibit.IR,result.flags)==next_Arch.CSR and
	t_wb##1 pc_check(exe.next_pc.PC);
endsequence

sequence pipe_result(t_ex, execute_t exe, result_t result='0, logic[XLEN-1:0] rtl_result='0);
	t_ex##0 ~((exe.dec.RD[1].idx==0) & (exe.fpu.valid -> Zfinx)) -> result.data[1]==rtl_result and
	t_ex##0 (exe.fpu.valid & exe.fpu.flags_update) -> result.flags==fpu_flags;
endsequence

sequence pipe_operands(t_ex, execute_t exe, op_t rtl_op='0, logic[1:NUM_RS][1:0] select_op_data='0);
	t_ex##0 op_check(exe,rtl_op,select_op_data) and
	t_ex##0 exe.fpu.valid -> exe.fpu.frm==fpu_rm;
endsequence

property pipe_env(t_wb, logic env_cond='1, logic[PIPE_STAGES-1:0] prevent_stage_flush='0, logic[PIPE_STAGES-1:0] prevent_stage_stall='0);
	t_id##0 (prevent_stage_flush[0] -> ~flush[0]) && (prevent_stage_stall[0] -> ~stall[0]) and
	t_wb##0 (prevent_stage_flush[1] -> ~flush[1]) && (prevent_stage_stall[1] -> ~stall[1]) and
	during(t_id,t_wb,env_cond);
endproperty

/*********************/
// CONCEPTUAL STATE
/*********************/

sequence Ready2Execute;
	 ~stall[1] && ~id_stage_i.misaligned_stall && id_stage_i.controller_i.ctrl_fsm_cs inside {DECODE,DECODE_HWLOOP} && ~id_stage_i.branch_taken_ex
`ifndef SKIP_PC_CHECK
	&& (id_stage_i.controller_i.jump_done_q -> (full[0] & id_stage_i.controller_i.jump_in_dec & (id_stage_i.controller_i.pc_mux_o==PC_JUMP) & ~$past(fpu_result_valid) & (~fpu_m_cycle) -> (~id_stage_i.controller_i.jr_stall_o & (pc_if==if_stage_i.aligner_i.branch_addr_i))))
	&& ((full[0] & ~id_stage_i.controller_i.jump_done_q & ~id_stage_i.controller_i.is_hwlp_body & id_stage_i.controller_i.ctrl_fsm_cs==DECODE) -> (pc_if=={pc_id+(iword_id[1:0]==2'b11 ?3'd4: 3'd2)}[31:0]))
`endif
;
endsequence

/*********************/
// TIMEPOINTS
/*********************/

// RESET PROPERTY TIMEPOINTS //

sequence t_if_rst;          nxt(t,2); endsequence;
sequence t_id_rst;          nxt(t_if_rst,2); endsequence;

// PIPELINE STAGE TIMEPOINTS //

sequence t_id;              t; endsequence;
sequence t_ex;              nxt(t_id,1); endsequence;
sequence t_wb;              t_ex; endsequence;
sequence t_ex_ready;        await(t_ex,~stall[1]&&id_stage_i.controller_i.ctrl_fsm_cs inside {DECODE,DECODE_HWLOOP,ELW_EXE},MAX_WAIT+4); endsequence;
sequence t_wb_ready;        t_ex_ready; endsequence;

// MEMORY PROPERTY TIMEPOINTS //

sequence t_dmem_req;        t_ex; endsequence;
sequence t_dmem_gnt;        await(t_dmem_req,dmem_req_ready,MAX_WAIT); endsequence;
sequence t_dmem_2nd_req;    await(nxt(t_dmem_gnt,1),obi_dmem_checker.new_req_allowed,MAX_WAIT); endsequence;
sequence t_dmem_2nd_gnt;    await(t_dmem_2nd_req,dmem_req_ready,MAX_WAIT); endsequence;
sequence t_wb_ready_mem;    t_wb_ready; endsequence;
sequence t_ex_ready_mem_ma; await(t_dmem_2nd_req,~stall[1],MAX_WAIT); endsequence;
sequence t_wb_ready_mem_ma; t_ex_ready_mem_ma; endsequence;

// OTHER PROPERTY TIMEPOINTS //

sequence t_ex_ready_branch; await(nxt(t_ex_ready,1),~stall[1],MAX_WAIT); endsequence;
sequence t_ex_ready_wfi;    await(t_ex,~stall[1]&&id_stage_i.controller_i.ctrl_fsm_cs==DECODE,MAX_WAIT+6); endsequence;
sequence t_ex_ready_div;    await(nxt(t_ex,2),~stall[1]&&id_stage_i.controller_i.ctrl_fsm_cs inside {DECODE},32); endsequence;
sequence t_wb_ready_branch; t_ex_ready_branch; endsequence;
sequence t_wb_ready_wfi;    t_ex_ready_wfi; endsequence;
sequence t_wb_ready_div;    t_ex_ready_div; endsequence;

// MODEL CAPTURING TIMEPOINTS //

sequence t_model;           t_wb; endsequence;
sequence t_arch;            t_wb; endsequence;

// ARCHITECTURE UPDATE TIMEPOINTS //

sequence t_arch_update;        t_wb_ready; endsequence;
sequence t_arch_update_mem;    t_wb_ready_mem; endsequence;
sequence t_arch_update_mem_ma; t_wb_ready_mem_ma; endsequence;
sequence t_arch_update_branch; t_wb_ready_branch; endsequence;
sequence t_arch_update_wfi;    t_wb_ready_wfi; endsequence;
sequence t_arch_update_div;    t_wb_ready_div; endsequence;
sequence t_arch_update_fpu;    await(nxt(t_ex_ready,FPU_LATENCY),fpu_result_valid,MAX_WAIT); endsequence;

// CONCEPTUAL STATE TIMEPOINTS //

sequence t_rd2ex_rst;       t_id_rst; endsequence;
sequence t_rd2ex;           t_ex_ready; endsequence;
sequence t_rd2ex_mem_ma;    t_ex_ready_mem_ma; endsequence;
sequence t_rd2ex_branch;    t_ex_ready_branch; endsequence;
sequence t_rd2ex_wfi;       t_ex_ready_wfi; endsequence;
sequence t_rd2ex_div;       t_ex_ready_div; endsequence;

/*********************/
// PROPERTIES
/*********************/

// RESET PROPERTY //

property RESET_p;
reset_sequence |=>
	t##0 `core.fetch_enable_i and
	during(t,nxt(t_id_rst,WB_OFFSET-1),~interrupt_in.DBGI) and
	during(t,nxt(t_id_rst,WB_OFFSET),rst_n) // [t##0 --> first WB]
implies
	t_rd2ex_rst##0 Ready2Execute and // first ID
	pipe_fetch_req(t,t_if_rst) and // [t##0 --> first IF]
	pipe_reset(nxt(t_id_rst,WB_OFFSET)) and // first WB
	pipe_dmem_no_req(t,t_id_rst) and // [t##0 --> first ID]
	t_rd2ex_rst##0 right_hook;
endproperty

// BUBBLE & PIPELINE SPECIFIC PROPERTIES //

property BUBBLE_p;
	Arch_state_t cur_Arch;
	t_arch##0 set_freeze(cur_Arch,Arch) and
	t_id##0 Ready2Execute and
	t_id##0 ~full[0] | stall[0] and
	pipe_env(t_wb_ready,~(is_interrupt|is_debug))
implies
	t_rd2ex##0 Ready2Execute and
	pipe_bubble(t_arch_update,cur_Arch) and
	pipe_dmem_no_req(t_ex,t_ex_ready) and
	t_rd2ex##0 right_hook;
endproperty

// I, E, C, X PROPERTIES //

property RV_INSTR(insn_set insns);
	execute_t exe;
	Arch_state_t cur_Arch;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
	t_id##0 insns[exe.dec.instr] && (exe.next_pc.conditional -> ~exe.next_pc.non_linear) and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	pipe_env(t_wb_ready,~(is_interrupt|is_debug)) and
	t_id##0 ~exe.xcpt.valid
implies
	t_rd2ex##0 Ready2Execute and
	during(nxt(t_wb,1),nxt(t_wb_ready,1),pc_check(exe.next_pc.PC)) and
	pipe_instr(t_arch_update,cur_Arch,exe,exe.result) and
	pipe_dmem_no_req(t_ex,t_ex_ready) and
	t_rd2ex##0 right_hook;
endproperty

property RV_INSTR_Branch(insn_set insns);
	execute_t exe;
	Arch_state_t cur_Arch;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
	t_id##0 insns[exe.dec.instr] && (exe.next_pc.conditional -> exe.next_pc.non_linear) and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	pipe_env(t_wb_ready_branch,~(is_interrupt|is_debug)) and
	t_id##0 ~exe.xcpt.valid
implies
	t_rd2ex_branch##0 Ready2Execute and
	pipe_instr(t_arch_update_branch,cur_Arch,exe,exe.result) and
	pipe_dmem_no_req(t_ex,t_ex_ready_branch) and
	t_rd2ex_branch##0 right_hook;
endproperty

property RV_INSTR_MEM(insn_set insns);
	execute_t exe;
	Arch_state_t cur_Arch;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
	t_id##0 insns[exe.dec.instr] && exe.mem.byte_enable<=4'hf and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	pipe_env(t_wb_ready_mem,~(is_interrupt|is_debug)) and
	t_id##0 ~exe.xcpt.valid
implies
	t_rd2ex##0 Ready2Execute and
	pipe_instr(t_arch_update_mem,cur_Arch,exe,exe.result,NUM_RD==2?2'b01:1'b0) and
	pipe_dmem_1st_req(t_dmem_gnt,exe) and
	during_excl(nxt(t_dmem_gnt,1),t_wb_ready_mem,~dmem_req_valid) and
	t_arch_update_mem##1 exe.mem.cmd==mc_load -> rf_we_lsu && rf_waddr_lsu=={(exe.dec.RD[1].RF==rf_F)?1'b1:1'b0,exe.dec.RD[1].idx} and
	t_arch_update_mem##1 exe.mem.cmd==mc_load -> lsu_data_type==data_size_enc(exe.mem.size) && lsu_data_sign[0]==((exe.dec.RD[1].RF==rf_X)&exe.mem.signed_data) && lsu_data_offset==exe.mem.addr[1:0] and
	t_rd2ex##0 right_hook;
endproperty

property RV_INSTR_MEM_MA(insn_set insns);
	execute_t exe;
	Arch_state_t cur_Arch;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
	t_id##0 insns[exe.dec.instr] && exe.mem.byte_enable>4'hf and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	pipe_env(t_wb_ready_mem_ma,~(is_interrupt|is_debug)) and
	t_id##0 ~exe.xcpt.valid
implies
	t_rd2ex_mem_ma##0 Ready2Execute and
	pipe_instr(t_arch_update_mem_ma,cur_Arch,exe,exe.result,NUM_RD==2?2'b01:1'b0) and
	pipe_dmem_1st_req(t_dmem_gnt,exe) and
	pipe_dmem_2nd_req(t_dmem_2nd_gnt,exe) and
	during_excl(nxt(t_dmem_gnt,1),t_dmem_2nd_req,~dmem_req_valid) and
	t_arch_update_mem_ma##1 exe.mem.cmd==mc_load -> rf_we_lsu && rf_waddr_lsu=={(exe.dec.RD[1].RF==rf_F)?1'b1:1'b0,exe.dec.RD[1].idx} and
	t_arch_update_mem_ma##1 exe.mem.cmd==mc_load -> lsu_data_type==data_size_enc(exe.mem.size) && lsu_data_sign[0]==((exe.dec.RD[1].RF==rf_X)&exe.mem.signed_data) && lsu_data_offset==exe.mem.addr[1:0] and
	t_rd2ex_mem_ma##0 right_hook;
endproperty

// SYSTEM PROPERTIES //

property FENCE_p(insn_set insns);
	execute_t exe;
	Arch_state_t cur_Arch;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
	t_id##0 insns[exe.dec.instr] and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	pipe_env(t_wb_ready,~(is_interrupt|is_debug)) and
	t_id##0 ~exe.xcpt.valid
implies
	t_rd2ex##0 Ready2Execute and
	pipe_instr(t_arch_update,cur_Arch,exe) and
	pipe_dmem_no_req(t_ex,t_ex_ready) and
	t_rd2ex##0 right_hook;
endproperty

property WFI_p(insn_set insns);
	execute_t exe;
	Arch_state_t cur_Arch;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
	t_id##0 insns[exe.dec.instr] and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	pipe_env(t_wb_ready_wfi,~(is_interrupt|is_debug)) and
	during(nxt(t_ex,3),nxt(t_ex,6), id_stage_i.controller_i.ctrl_fsm_cs==SLEEP -> `core.wake_from_sleep) and
	t_id##0 ~exe.xcpt.valid
implies
	t_rd2ex_wfi##0 Ready2Execute and
	pipe_instr(t_arch_update_wfi,cur_Arch,exe) and
	pipe_dmem_no_req(t_ex,t_ex_ready_wfi) and
	t_rd2ex_wfi##0 right_hook;
endproperty

property xRET_p(insn_set insns);
	execute_t exe;
	Arch_state_t cur_Arch;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
	t_id##0 insns[exe.dec.instr] & ((exe.dec.instr==DRET) | ~cur_Arch.CSR.curDebug) and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	pipe_env(t_wb_ready,~(is_interrupt|is_debug)) and
	t_id##0 ~exe.xcpt.valid
implies
	t_rd2ex##0 Ready2Execute and
	pipe_ret(t_arch_update,cur_Arch,exe) and
	pipe_dmem_no_req(t_ex,t_ex_ready) and
	t_rd2ex##0 right_hook;
endproperty

property ECALL_p(insn_set insns);
	execute_t exe;
	Arch_state_t cur_Arch;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
	t_id##0 insns[exe.dec.instr] and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	during(t_id,t_wb_ready,~is_interrupt&~is_debug) and
	t_id##0 exe.xcpt.valid & ~exe.xcpt.interrupt & exe.xcpt.xcpt_code inside {xcpt_UEnvCall,xcpt_SEnvCall,xcpt_MEnvCall} & ~cur_Arch.CSR.curDebug
implies
	t_rd2ex##0 Ready2Execute and
	pipe_xcpt(t_arch_update,cur_Arch,exe.xcpt) and
	pipe_dmem_no_req(t_ex,t_ex_ready) and
	t_rd2ex##0 right_hook;
endproperty

property EBREAK_BreakPoint_p(insn_set insns);
	execute_t exe;
	Arch_state_t cur_Arch;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
	t_id##0 insns[exe.dec.instr] and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	pipe_env(t_wb_ready,~(is_interrupt|is_debug)) and
	t_id##0 exe.xcpt.valid & ~exe.xcpt.interrupt & ~exe.xcpt.dbg & exe.xcpt.xcpt_code==xcpt_Breakpoint & exe.xcpt.brk inside {brk_instr} & ~cur_Arch.CSR.curDebug
implies
	t_rd2ex##0 Ready2Execute and
	pipe_xcpt(t_arch_update,cur_Arch,exe.xcpt) and
	pipe_dmem_no_req(t_ex,t_ex_ready) and
	t_rd2ex##0 right_hook;
endproperty

property EBREAK_HaltReq_p(insn_set insns);
	execute_t exe;
	Arch_state_t cur_Arch;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
	t_id##0 insns[exe.dec.instr] and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	t_id##0 exe.xcpt.valid & ~exe.xcpt.interrupt & exe.xcpt.xcpt_code==xcpt_Breakpoint & exe.xcpt.brk inside {brk_instr} & cur_Arch.CSR.curDebug
implies
	t_rd2ex##0 Ready2Execute and
	pipe_xcpt(t_arch_update,cur_Arch,exe.xcpt) and
	pipe_dmem_no_req(t_ex,t_ex_ready) and
	t_rd2ex##0 right_hook;
endproperty

property EBREAK_ForcedEntry_p(insn_set insns);
	execute_t exe;
	Arch_state_t cur_Arch;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
	t_id##0 insns[exe.dec.instr] and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	pipe_env(t_wb_ready,~(is_interrupt)) and
	t_id##0 exe.xcpt.valid & ~exe.xcpt.interrupt & exe.xcpt.dbg & exe.xcpt.xcpt_code==xcpt_Breakpoint & exe.xcpt.brk inside {brk_instr} & ~cur_Arch.CSR.curDebug
implies
	t_rd2ex##0 Ready2Execute and
	pipe_xcpt(t_arch_update,cur_Arch,exe.xcpt) and
	pipe_dmem_no_req(t_ex,t_ex_ready) and
	t_rd2ex##0 right_hook;
endproperty

// Zicsr PROPERTIES //

property CSRx_p(insn_set insns);
	execute_t exe;
	Arch_state_t cur_Arch;
	result_t result;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
	t_ex##0 set_freeze(result,compose_result(csr_rdata)) and
	t_id##0 insns[exe.dec.instr] and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	pipe_env(t_wb_ready,~(is_interrupt|is_debug)) and
`ifndef ISSUE_32_FIXED
	t_wb_ready##0 `core.COREV_PULP -> (~id_stage_i.controller_i.hwlp_end1_eq_pc & ~id_stage_i.controller_i.hwlp_end0_eq_pc) and // **Potential ISSUE_32** In case the hwlp end pc is same as next pc expected (pc+4) the next pc is set to a different value than expected
`endif
	t_id##0 ~exe.xcpt.valid
implies
	t_rd2ex##0 Ready2Execute and
	pipe_instr(t_arch_update,cur_Arch,exe,result) and
	pipe_dmem_no_req(t_ex,t_ex_ready) and
	t_ex##0 exe.csr.addr==csr_addr and
	t_ex##0 ~((exe.dec.RD[1].idx==0)|(`core.COREV_PULP?(exe.csr.csr inside {csr_lpcount0, csr_lpcount1}):'0)) -> CSR_read(csr_rdata,exe.csr,cur_Arch.CSR,$past(interrupt_in,1)) and // **I** Skip checking lpcount read
	t_rd2ex##0 right_hook;
endproperty

// Zifencei PROPERTIES //

property FENCE_I_p(insn_set insns);
	execute_t exe;
	Arch_state_t cur_Arch;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
	t_id##0 insns[exe.dec.instr] and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	pipe_env(t_wb_ready,~(is_interrupt|is_debug)) and
	t_id##0 ~exe.xcpt.valid
implies
	t_rd2ex##0 Ready2Execute and
	pipe_instr(t_arch_update,cur_Arch,exe) and
	pipe_dmem_no_req(t_ex,t_ex_ready) and
	t_rd2ex##0 right_hook;
endproperty

// M PROPERTIES //

property RV_INSTR_MUL(insn_set insns);
	execute_t exe;
	Arch_state_t cur_Arch;
	result_t result;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
`ifdef PVE_M_SUPPORT
	t_ex_ready##0 set_freeze(result,exe.result) and
	t_ex_ready##0 restrict_ops(compose_operands(exe.op[1],exe.op[2]),'{default:'h1}) and
`else
	t_ex_ready##0 set_freeze(result,compose_result(mul_result)) and
`endif
	t_id##0 insns[exe.dec.instr] and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	pipe_env(t_wb_ready,~(is_interrupt|is_debug)) and
	t_id##0 ~exe.xcpt.valid
implies
	t_rd2ex##0 Ready2Execute and
`ifdef PVE_M_SUPPORT
	pipe_result(t_ex_ready,exe,result,mul_result) and
`else
	pipe_instr(t_arch_update,cur_Arch,exe,result) and
	pipe_dmem_no_req(t_ex,t_ex_ready) and
	pipe_operands(t_ex_ready,exe,compose_operands(mul_op_a,mul_op_b,mul_op_c)) and
`endif
	t_rd2ex##0 right_hook;
endproperty

property RV_INSTR_DIV(insn_set insns, cycles);
	execute_t exe;
	Arch_state_t cur_Arch;
	result_t result;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
`ifdef PVE_M_SUPPORT
	t_ex##0 set_freeze(result,exe.result) and
	t_ex##0 restrict_ops(exe.op,'{default:'h1}) and
`else
	t_ex##cycles set_freeze(result,compose_result(div_result)) and
`endif
	t_id##0 insns[exe.dec.instr] and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	pipe_env(t_wb_ready_div,~(is_interrupt|is_debug)) and
	during_excl(nxt(t_ex,2),nxt(t_ex,cycles),~div_result_valid) and
	t_ex##cycles div_result_valid and
	t_id##0 ~exe.xcpt.valid
implies
	t_rd2ex_div##0 Ready2Execute and
`ifdef PVE_M_SUPPORT
	pipe_result(t_ex_ready_div,exe,result,div_result) and
`else
	pipe_instr(t_arch_update_div,cur_Arch,exe,result) and
	pipe_dmem_no_req(t_ex,t_ex_ready_div) and
	pipe_operands(t_ex_ready_div,exe,compose_operands(div_op_a,div_op_b),compose_selection('h0,'h3)) and
`endif
	t_rd2ex_div##0 right_hook;
endproperty

// F, D PROPERTIES //

property RV_INSTR_F(insn_set insns);
	execute_t exe;
	Arch_state_t cur_Arch;
	result_t result;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
`ifdef PVE_FPU_SUPPORT
	t_ex_ready##FPU_LATENCY set_freeze(result,exe.result) and
	t_ex_ready##FPU_LATENCY exe.dec.instr inside {FMUL_S,FMADD_S,FNMADD_S,FMSUB_S,FNMSUB_S} -> restrict_fpu_ops(compose_operands(exe.op[1],exe.op[2])) and
`else
	t_ex_ready##FPU_LATENCY set_freeze(result,compose_result(fpu_result,fpu_flags)) and
`endif
	t_id##0 insns[exe.dec.instr] and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	pipe_env(t_arch_update_fpu,~(is_interrupt|is_debug)) and
	t_arch_update_fpu##0 (FPU_LATENCY>0) -> fpu_result_valid and // **I** Otherwise we wait forever in case FPU_LATENCY==2
	t_ex_ready##0 ~stall[1] and // **I** No preceding FDIV/ FSQRT instruction, could use instead t_id##0 ~(fpu_lat_ex=='h3 && (fpu_op_ex=='h4 || fpu_op_ex=='h5)) and
	t_id##0 ~exe.xcpt.valid
implies
	t_rd2ex##0 Ready2Execute and
`ifdef PVE_FPU_SUPPORT
	pipe_result(nxt(t_ex_ready,FPU_LATENCY),exe,result,fpu_result) and
`else
	pipe_instr(t_arch_update,cur_Arch,exe,result,(FPU_LATENCY>0)?'0:'1) and
	pipe_dmem_no_req(t_ex,t_ex_ready) and
`ifdef CFG_F
	t_arch_update_fpu##1 (FPU_LATENCY>0) -> (exe.dec.RD[1].RF==rf_X?((exe.dec.RD[1].idx!=0 -> result.data[1]==Arch.X[exe.dec.RD[1].idx].data)):(result.data[1]==Arch.F[exe.dec.RD[1].idx].data)) and
`else
	t_arch_update_fpu##1 (FPU_LATENCY>0) -> (exe.dec.RD[1].idx!=0 -> result.data[1]==Arch.X[exe.dec.RD[1].idx].data) and
`endif
    t_arch_update_fpu##1 (FPU_LATENCY>0) -> (Arch.CSR.fflags==($past(Arch.CSR.fflags)|result.flags)) and
`endif
	t_rd2ex##0 right_hook;
endproperty

// X PROPERTIES //

property RV_INSTR_DOT(insn_set insns, select);
	execute_t exe;
	Arch_state_t cur_Arch;
	result_t result;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
`ifdef PVE_M_SUPPORT
	t_ex_ready##0 set_freeze(result,exe.result) and
	t_ex_ready##0 restrict_ops(compose_operands(exe.op[1],exe.op[2]),'{default:select}) and
`else
	t_ex_ready##0 set_freeze(result,compose_result(mul_result)) and
`endif
	t_id##0 insns[exe.dec.instr] and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	pipe_env(t_wb_ready,~(is_interrupt|is_debug)) and
	t_id##0 ~exe.xcpt.valid
implies
	t_rd2ex##0 Ready2Execute and
`ifdef PVE_M_SUPPORT
	pipe_result(t_ex_ready,exe,result,mul_result) and
`else
	pipe_instr(t_arch_update,cur_Arch,exe,result) and
	pipe_dmem_no_req(t_ex,t_ex_ready) and
	pipe_operands(t_ex_ready,exe,compose_operands(dot_mul_op_a,dot_mul_op_b,dot_mul_op_c)) and
`endif
	t_rd2ex##0 right_hook;
endproperty

property RV_INSTR_DOT_SC(insn_set insns, select);
	execute_t exe;
	Arch_state_t cur_Arch;
	result_t result;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
`ifdef PVE_M_SUPPORT
	t_ex_ready##0 set_freeze(result,exe.result) and
	t_ex_ready##0 restrict_ops(compose_operands(exe.op[1],exe.op[2]),'{default:select}) and
`else
	t_ex_ready##0 set_freeze(result,compose_result(mul_result)) and
`endif
	t_id##0 insns[exe.dec.instr] and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	pipe_env(t_wb_ready,~(is_interrupt|is_debug)) and
	t_id##0 ~exe.xcpt.valid
implies
	t_rd2ex##0 Ready2Execute and
`ifdef PVE_M_SUPPORT
	pipe_result(t_ex_ready,exe,result,mul_result) and
`else
	pipe_instr(t_arch_update,cur_Arch,exe,result) and
	pipe_dmem_no_req(t_ex,t_ex_ready) and
	pipe_operands(t_ex_ready,exe,compose_operands(dot_mul_op_a,dot_mul_op_b,dot_mul_op_c),compose_selection('h0,select)) and
`endif
	t_rd2ex##0 right_hook;
endproperty

property RV_INSTR_DOT_SCI(insn_set insns, select);
	execute_t exe;
	Arch_state_t cur_Arch;
	result_t result;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
`ifdef PVE_M_SUPPORT
	t_ex##0 set_freeze(result,exe.result) and
	t_ex##0 restrict_ops(compose_operands(exe.op[1],dot_mul_op_b),'{default:select}) and
`else
	t_ex_ready##0 set_freeze(result,compose_result(mul_result)) and
`endif
	t_id##0 insns[exe.dec.instr] and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	pipe_env(t_wb_ready,~(is_interrupt|is_debug)) and
	t_id##0 ~exe.xcpt.valid
implies
	t_rd2ex##0 Ready2Execute and
`ifdef PVE_M_SUPPORT
	pipe_result(t_ex_ready,exe,result,mul_result) and
`else
	pipe_instr(t_arch_update,cur_Arch,exe,result) and
	pipe_dmem_no_req(t_ex,t_ex_ready) and
//	pipe_operands(t_ex_ready,exe,compose_operands(dot_mul_op_a,dot_mul_op_b,dot_mul_op_c),compose_selection('h0,select)) and // operand b manipulation is based on the immediate value
`endif
	t_rd2ex##0 right_hook;
endproperty

property RV_INSTR_MEM_ELW(insn_set insns);
	execute_t exe;
	Arch_state_t cur_Arch;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
	t_id##0 insns[exe.dec.instr] && exe.mem.byte_enable<=4'hf and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	pipe_env(nxt(t_wb_ready_mem,2),~(is_interrupt|is_debug)) and
	t_id##0 ~exe.xcpt.valid
implies
//	t_rd2ex##0 Ready2Execute and
	pipe_instr(t_arch_update_mem,cur_Arch,exe,exe.result,NUM_RD==2?2'b01:1'b0) and
	pipe_dmem_1st_req(t_dmem_gnt,exe) and
	during_excl(nxt(t_dmem_gnt,1),t_wb_ready_mem,~dmem_req_valid) and
	t_arch_update_mem##1 exe.mem.cmd==mc_load -> rf_we_lsu && rf_waddr_lsu=={(exe.dec.RD[1].RF==rf_F)?1'b1:1'b0,exe.dec.RD[1].idx} and
	t_arch_update_mem##1 exe.mem.cmd==mc_load -> lsu_data_type==data_size_enc(exe.mem.size) && lsu_data_sign[0]==((exe.dec.RD[1].RF==rf_X)&exe.mem.signed_data) && lsu_data_offset==exe.mem.addr[1:0] and
	t_rd2ex##0 right_hook;
endproperty

property RV_INSTR_MEM_MA_ELW(insn_set insns);
	execute_t exe;
	Arch_state_t cur_Arch;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
	t_id##0 insns[exe.dec.instr] && exe.mem.byte_enable>4'hf and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	pipe_env(nxt(t_wb_ready_mem_ma,2),~(is_interrupt|is_debug)) and
	t_id##0 ~exe.xcpt.valid
implies
//	t_rd2ex_mem_ma##0 Ready2Execute and
	pipe_instr(t_arch_update_mem_ma,cur_Arch,exe,exe.result,NUM_RD==2?2'b01:1'b0) and
	pipe_dmem_1st_req(t_dmem_gnt,exe) and
	pipe_dmem_2nd_req(t_dmem_2nd_req,exe) and
	during_excl(nxt(t_dmem_gnt,1),t_dmem_2nd_req,~dmem_req_valid) and
	t_arch_update_mem_ma##1 exe.mem.cmd==mc_load -> rf_we_lsu && rf_waddr_lsu=={(exe.dec.RD[1].RF==rf_F)?1'b1:1'b0,exe.dec.RD[1].idx} and
	t_arch_update_mem_ma##1 exe.mem.cmd==mc_load -> lsu_data_type==data_size_enc(exe.mem.size) && lsu_data_sign[0]==((exe.dec.RD[1].RF==rf_X)&exe.mem.signed_data) && lsu_data_offset==exe.mem.addr[1:0] and
	t_rd2ex_mem_ma##0 right_hook;
endproperty

// EXCEPTION PROPERTIES //

property XCPT_IF_ID_p;
	execute_t exe;
	Arch_state_t cur_Arch;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	pipe_env(t_wb_ready,~(is_interrupt|(is_debug & exe.xcpt.xcpt_code inside {xcpt_Illegal_Instr}))) and
	t_id##0 exe.xcpt.valid & ~exe.xcpt.interrupt & exe.xcpt.xcpt_code inside {xcpt_Breakpoint,xcpt_Fetch_Page_Fault,xcpt_Fetch_Access_Fault,xcpt_Illegal_Instr,xcpt_Fetch_Addr_Align} & exe.xcpt.brk inside {brk_none,brk_fetch}
implies
	t_rd2ex##0 Ready2Execute and
	pipe_xcpt(t_arch_update,cur_Arch,exe.xcpt) and
	pipe_dmem_no_req(t_ex,t_ex_ready) and
	t_rd2ex##0 right_hook;
endproperty

property XCPT_WB_p;
	execute_t exe;
	Arch_state_t cur_Arch;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	t_id##0 exe.xcpt.valid & ~exe.xcpt.interrupt & (exe.xcpt.xcpt_code inside {xcpt_Breakpoint,xcpt_SAMO_Addr_Align,xcpt_Load_Addr_Align,xcpt_SAMO_Page_Fault,xcpt_Load_Page_Fault,xcpt_SAMO_Access_Fault,xcpt_Load_Access_Fault}) & exe.xcpt.brk inside {brk_none,brk_dmem}
implies
	t_rd2ex##0 Ready2Execute and
	t_wb_ready##0 no_pending_results_used(exe.dec) and
	pipe_xcpt(t_arch_update,cur_Arch,exe.xcpt) and
	pipe_dmem_no_req(t_ex,t_ex_ready) and
	t_rd2ex##0 right_hook;
endproperty

// INTERRUPT HANDLING PROPERTIES //

property INTR_Handle_p;
	execute_t exe;
	Arch_state_t cur_Arch;
	t_model##0 set_freeze(exe,execute) and
	t_arch##0 set_freeze(cur_Arch,Arch) and
	t_id##0 Ready2Execute and
	t_id##0 full[0] && ~stall[0] and
	t_id##0 exe.xcpt.valid & exe.xcpt.interrupt
implies
	t_rd2ex##0 Ready2Execute and
	pipe_xcpt(t_arch_update,cur_Arch,exe.xcpt) and
	pipe_dmem_no_req(t_ex,t_ex_ready) and
	t_rd2ex##0 right_hook;
endproperty

/*********************/
// NON-TIDAL ASSERTIONs
/*********************/

// COUNTERS //

property mcycle_increment_p;
	Ready2Execute ##1 ~execute.csr.count_inhibit.CY&~execute.xcpt.interrupt |=>
	Arch.CSR.mcycle==$past(Arch.CSR.mcycle+64'h1);
endproperty
mcycle_increment_a : assert property (disable iff(~rst_n) mcycle_increment_p);

property mcycle_no_increment_p;
	Ready2Execute ##1 execute.csr.count_inhibit.CY&Arch.CSR.mcountinhibit.CY&((execute.csr.cmd == cc_none)|(execute.csr.cmd == cc_r)) |=>
	Arch.CSR.mcycle==$past(Arch.CSR.mcycle);
endproperty
mcycle_no_increment_a : assert property (disable iff(~rst_n) mcycle_no_increment_p);

property mhpmcounter3_increment_p;
	Ready2Execute ##1 ~execute.csr.count_inhibit.HPM[3]&~execute.xcpt.interrupt |=>
	Arch.CSR.mhpmcounter[3]==$past(|(Arch.CSR.mhpmevent[3][15:0]&cs_registers_i.hpm_events) ? Arch.CSR.mhpmcounter[3]+64'h1 : Arch.CSR.mhpmcounter[3]);
endproperty
mhpmcounter3_increment_a : assert property (disable iff(~rst_n) mhpmcounter3_increment_p);

property mhpmcounter3_no_increment_p;
	Ready2Execute ##1 execute.csr.count_inhibit.HPM[3]&Arch.CSR.mcountinhibit.HPM[3]&((execute.csr.cmd == cc_none)|(execute.csr.cmd == cc_r)) |=>
	Arch.CSR.mhpmcounter[3]==$past(Arch.CSR.mhpmcounter[3]);
endproperty
mhpmcounter3_no_increment_a : assert property (disable iff(~rst_n) mhpmcounter3_no_increment_p);

// LSU //

property stable_lsu_signals_p;
    rf_we_lsu&~obi_dmem_checker.rvalid |=> $stable({rf_we_lsu,rf_waddr_lsu,lsu_data_type,lsu_data_offset,lsu_data_sign});
endproperty
stable_lsu_signals_a : assert property (disable iff(~rst_n) stable_lsu_signals_p);

property lsu_write_p;
	~rf_waddr_lsu[5]&&rf_we_lsu&&obi_dmem_checker.rvalid &&
	~(fpu_result_valid && fpu_waddr[4:0]==rf_waddr_lsu[4:0]) && // A write on ALU port by next F instruction to same RD overtake LSU port write
	~((data_size_enc(lsu_data_type)==2'h2&&lsu_data_offset>0) || // lw
	  (data_size_enc(lsu_data_type)==2'h1&&lsu_data_offset==2'h3)) // lh
	  |=>
	(obi_dmem_checker.cnt!=$past(obi_dmem_checker.cnt) && rf_waddr_lsu!=$past(rf_waddr_lsu) -> Arch.X[$past(rf_waddr_lsu[4:0])].valid) &&
		($past(rf_waddr_lsu[4:0])!='0 -> Arch.X[$past(rf_waddr_lsu[4:0])].data==
			$unsigned(align_rdata('{size: data_size_enc($past(lsu_data_type)), signed_data: $past(lsu_data_sign[0]),
				addr: $past({30'h0,lsu_data_offset}), default: '0},{32'h0,$past(dmem_resp_data)})));
endproperty
lsu_write_a : assert property (disable iff(~rst_n) lsu_write_p);

property lsu_ma_write_p;
	~rf_waddr_lsu[5]&&rf_we_lsu&&obi_dmem_checker.rvalid&&id_stage_i.register_file_i.we_a_i &&
	~(fpu_result_valid && fpu_waddr[4:0]==rf_waddr_lsu[4:0])&&
	((data_size_enc(lsu_data_type)==2'h2&&lsu_data_offset>0) || (data_size_enc(lsu_data_type)==2'h1&&lsu_data_offset==2'h3))
	|=>
//	Arch.X[$past(rf_waddr_lsu[4:0])].valid &&
		$past(rf_waddr_lsu[4:0])!='0 -> Arch.X[$past(rf_waddr_lsu[4:0])].data==
			$unsigned(align_rdata('{size: data_size_enc($past(lsu_data_type)), signed_data: $past(lsu_data_sign[0]),
				addr: $past({30'h0,lsu_data_offset}), default: '0},{$past(dmem_resp_data),$past(load_store_unit_i.rdata_q)}));
endproperty
lsu_ma_write_a : assert property (disable iff(~rst_n) lsu_ma_write_p);

property lsu_ma_rdata_q_p;
	rf_we_lsu&&obi_dmem_checker.rvalid&&cv32e40p_core.data_misaligned_ex&&
	((data_size_enc(lsu_data_type)==2'h2&&lsu_data_offset>0) || (data_size_enc(lsu_data_type)==2'h1&&lsu_data_offset==2'h3))
	|=>
	load_store_unit_i.rdata_q==$past(dmem_resp_data);
endproperty
lsu_ma_rdata_q_a : assert property (disable iff(~rst_n) lsu_ma_rdata_q_p);

`ifdef CFG_F
property lsu_write_f_p;
	rf_waddr_lsu[5]&&rf_we_lsu&&obi_dmem_checker.rvalid &&
	~(fpu_result_valid && fpu_waddr[4:0]==rf_waddr_lsu[4:0])&&
	~((data_size_enc(lsu_data_type)==2'h2&&lsu_data_offset>0) || (data_size_enc(lsu_data_type)==2'h1&&lsu_data_offset==2'h3))
	|=>
	(obi_dmem_checker.cnt!=$past(obi_dmem_checker.cnt) && rf_waddr_lsu!=$past(rf_waddr_lsu) -> Arch.F[$past(rf_waddr_lsu[4:0])].valid) &&
		(Arch.F[$past(rf_waddr_lsu[4:0])].data==
			$unsigned(align_rdata('{size: data_size_enc($past(lsu_data_type)), signed_data: $past(lsu_data_sign[0]),
				addr: $past({30'h0,lsu_data_offset}), default: '0},{32'h0,$past(dmem_resp_data)})));
endproperty
lsu_write_f_a : assert property (disable iff(~rst_n) lsu_write_f_p);

property lsu_ma_write_f_p;
	rf_waddr_lsu[5]&&rf_we_lsu&&obi_dmem_checker.rvalid&&id_stage_i.register_file_i.we_a_i &&
	~(fpu_result_valid && fpu_waddr[4:0]==rf_waddr_lsu[4:0])&&
	((data_size_enc(lsu_data_type)==2'h2&&lsu_data_offset>0) || (data_size_enc(lsu_data_type)==2'h1&&lsu_data_offset==2'h3))
	|=>
//	Arch.F[$past(rf_waddr_lsu[4:0])].valid &&
		Arch.F[$past(rf_waddr_lsu[4:0])].data==
			$unsigned(align_rdata('{size: data_size_enc($past(lsu_data_type)), signed_data: $past(lsu_data_sign[0]),
				addr: $past({30'h0,lsu_data_offset}), default: '0},{$past(dmem_resp_data),$past(load_store_unit_i.rdata_q)}));
endproperty
lsu_ma_write_f_a : assert property (disable iff(~rst_n) lsu_ma_write_f_p);
`endif

`include `GENERATED_ASSERTIONS_FILE
`include "constraints.sv"

endmodule
