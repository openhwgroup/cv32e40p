# Copyright 2024 Siemens
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
# 
# Licensed under the Solderpad Hardware License v 2.1 (the "License");
# you may not use this file except in compliance with the License, or,
# at your option, the Apache License version 2.0.
# You may obtain a copy of the License at
# 
# https://solderpad.org/licenses/SHL-2.1/
# 
# Unless required by applicable law or agreed to in writing, any work
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# clean up local files (that would be read instead of the one in the include dir due to local folder being first in include list)
file delete RISCV_ISA.sv bind.sv generated_assertions.sv vplan.csv

proc duration {int_time} {
    set timeList [list]
    if {$int_time == 0} {
    	return "0 Sec"
    } else {
    foreach div {86400 3600 60 1} mod {0 24 60 60} name {Day Hour Min Sec} {
        set n [expr {$int_time / $div}]
        if {$mod > 0} {set n [expr {$n % $mod}]}
        if {$n > 1} {
            lappend timeList "$n ${name}s"
        } elseif {$n == 1} {
            lappend timeList "$n $name"
        }
    }
    return [join $timeList]
	}
}

proc quantify_run {{cmd_limit 0} {run 0} {limit_scale 2.0} {effort 4} {skip_effort_level 0} {html_dir {}} {result_file {}} {checks {}} {prev_run_result {}} {skip_files {}}} {

	puts "\n-INFO- Start of Quantify Run ($run)::\n\nChecks Included::\n\n$checks"

	set_limit -command_real_time $cmd_limit
	set run_start_t [clock seconds]
	set cmd [list quantify -assume_hold -additional_args [list -no_cuts -use_single_prover -limit_scale $limit_scale] -effort $effort -skip_effort_level $skip_effort_level -html $html_dir -save $result_file -checks $checks -incremental $prev_run_result -skip_files $skip_files]
	puts "\n-INFO- Launching Quantify Command::\n\n$cmd\n"
	catch $cmd
	set run_end_t [expr [clock seconds] - $run_start_t]
	set_limit -default

	puts "\n-INFO- End of Quantify Run ($run) | Time spent:: [duration $run_end_t]\n"
}

## 0. DESIGN SETUP ##

### SETTING UP THE DESIRED CONFIGURATION, RUN & APP ###
## source the setup.inc as the following: [onespin -i setup.inc <arg1> <arg2> <arg3>]
##       arg1: what configuration to set <DEF:XPXCZF2>.
##       arg2: what processor verification mode to set <DEF,DPM,DPF>.
##       arg3: what app to launch <PRC,QTF,VCI> on top of the processor app.
## ------------------------------------------------------------------------------------------------------------------

set configs [dict create \
	"DEF" [dict create \
		description "RV32IMCZicsr_Zifencei" \
		elab "-verilog_parameter {}" \
		define "" \
		json "" \
	] \
	"F0" [dict create \
		description "RV32IMFCZicsr_Zifencei with FPU latency params set to 0" \
		elab "-verilog_parameter {FPU=1 FPU_ADDMUL_LAT=0 FPU_OTHERS_LAT=0}" \
		define "CFG_F" \
		json "" \
	] \
	"ZF0" [dict create \
		description "RV32IMCZicsr_Zifencei_Zfinx with FPU latency params set to 0" \
		elab "-verilog_parameter {FPU=1 ZFINX=1 FPU_ADDMUL_LAT=0 FPU_OTHERS_LAT=0}" \
		define "CFG_ZFINX" \
		json "" \
	] \
	"XP" [dict create \
		description "RV32IMCZicsr_Zifencei_Xpulp" \
		elab "-verilog_parameter {COREV_PULP=1}" \
		define "CFG_XP" \
		json "Xpulp.json Zfinx.json" \
	] \
	"XPF0" [dict create \
		description "RV32IMFCZicsr_Zifencei_Xpulp with FPU latency params set to 0" \
		elab "-verilog_parameter {FPU=1 COREV_PULP=1 FPU_ADDMUL_LAT=0 FPU_OTHERS_LAT=0}" \
		define "CFG_XP CFG_F" \
		json "Xpulp.json" \
	] \
	"XPF1" [dict create \
		description "RV32IMFCZicsr_Zifencei_Xpulp with FPU latency params set to 1" \
		elab "-verilog_parameter {FPU=1 COREV_PULP=1 FPU_ADDMUL_LAT=1 FPU_OTHERS_LAT=1}" \
		define "CFG_XP CFG_F" \
		json "Xpulp.json" \
	] \
	"XPF2" [dict create \
		description "RV32IMFCZicsr_Zifencei_Xpulp with FPU latency params set to 2" \
		elab "-verilog_parameter {FPU=1 COREV_PULP=1 FPU_ADDMUL_LAT=2 FPU_OTHERS_LAT=2}" \
		define "CFG_XP CFG_F" \
		json "Xpulp.json" \
	] \
	"XPZF0" [dict create \
		description "RV32IMCZicsr_Zifencei_Zfinx_Xpulp with FPU latency params set to 0" \
		elab "-verilog_parameter {FPU=1 ZFINX=1 COREV_PULP=1 FPU_ADDMUL_LAT=0 FPU_OTHERS_LAT=0}" \
		define "CFG_XP CFG_ZFINX" \
		json "Xpulp.json Zfinx.json" \
	] \
	"XPZF1" [dict create \
		description "RV32IMCZicsr_Zifencei_Zfinx_Xpulp with FPU latency params set to 1" \
		elab "-verilog_parameter {FPU=1 ZFINX=1 COREV_PULP=1 FPU_ADDMUL_LAT=1 FPU_OTHERS_LAT=1}" \
		define "CFG_XP CFG_ZFINX" \
		json "Xpulp.json Zfinx.json" \
	] \
	"XPZF2" [dict create \
		description "RV32IMCZicsr_Zifencei_Zfinx_Xpulp with FPU latency params set to 2" \
		elab "-verilog_parameter {FPU=1 ZFINX=1 COREV_PULP=1 FPU_ADDMUL_LAT=2 FPU_OTHERS_LAT=2}" \
		define "CFG_XP CFG_ZFINX" \
		json "Xpulp.json Zfinx.json" \
	] \
	"XPXC" [dict create \
		description "RV32IMCZicsr_Zifencei_Xpulp_Xcluster" \
		elab "-verilog_parameter {COREV_PULP=1 COREV_CLUSTER=1}" \
		define "CFG_XP CFG_XC" \
		json "Xpulp.json Xcluster.json Zfinx.json" \
	] \
	"XPXCZF2" [dict create \
		description "RV32IMCZicsr_Zifencei_Zfinx_Xpulp_Xcluster with FPU latency params set to 2" \
		elab "-verilog_parameter {FPU=1 ZFINX=1 COREV_PULP=1 COREV_CLUSTER=1 FPU_ADDMUL_LAT=2 FPU_OTHERS_LAT=2}" \
		define "CFG_XP CFG_XC CFG_ZFINX" \
		json "Xpulp.json Xcluster.json Zfinx.json" \
	] \
]
		
set pve_modes [dict create \
	"DEF" [dict create \
		description "DEF: Control path verification of all instructions and datapath verification of all instructions except multiplication, division or floating point ones" \
		define "" \
	] \
	"DPM" [dict create \
		description "DPM: Data path verification of multiplication/ division instructions" \
		define "PVE_M_SUPPORT RESTRICT_MUL_OPS_FREE_BITS=1" \
	] \
	"DPF" [dict create \
		description "DPF: Data path verification of floating-point instructions" \
		define "PVE_FPU_SUPPORT RESTRICT_MUL_OPS_FREE_BITS=1" \
	] \
]

set apps [dict create \
	"PRC" [dict create \
		description "PRC: Property Checking" \
		compile "-dontcare_handling any -signal_domain {{scan_cg_en_i} 0}" \
	] \
	"QTF" [dict create \
		description "QTF: Quantify" \
		compile "-dontcare_handling any -signal_domain {{scan_cg_en_i} 0} -constant [list [list core_i.id_stage_i.register_file_i.rst_n 1] ]" \
	] \
	"VCI" [dict create \
		description "VCI: Verification Coverage Integration" \
		compile "-dontcare_handling any -signal_domain {{scan_cg_en_i} 0}" \
	] \
]

if {$::argc>0} {
	lassign $::argv cfg pve_mode app prev_run
	if {$cfg ni [dict keys $configs]} {
		onespin::message -error "Only configurations [join [dict keys $configs] ,] are supported!"
		return -code error
	}
	if {$pve_mode ni [dict keys $pve_modes]} {
		onespin::message -error "Only processor verification modes [join [dict keys $pve_modes] ,] are supported!"
		return -code error
	} elseif {$pve_mode eq "DPF" && $cfg in {"DEF" "XP" "XPXC"} } {
		onespin::message -error "Floating-point configuration must be selected in order to perform data path verification!"
		return -code error
	}
	if {$app ni [dict keys $apps]} {
		onespin::message -error "Only apps [join [dict keys $apps] ,] are supported!"
		return -code error
	}
} else  {
	if {[get_tool_info -gui]} {
		set cfg [lindex [onespin::ask_user -default DEF -alternatives [lmap {k d} $configs {string cat "$k - " [dict get $d description]}] "Select which RISC-V configuration to set up:"] 0]
		set pve_mode [lindex [onespin::ask_user -default "DEF" -alternatives [lmap {k d} $pve_modes {string cat "$k - " [dict get $d description]}] "Select which processor verification mode to set:"] 0]
		set app [lindex [onespin::ask_user -default "PRC" -alternatives [lmap {k d} $apps {string cat "$k - " [dict get $d description]}] "Select which app to launch:"] 0]
	} else {
		set cfg "DEF"
		set pve_mode "DEF"
		set app "PRC"
	}
}
##

### ADJUST TO READ-IN THE NEW DESIGN ###
onespin::set_parameter disable_intermediate_arithmetic_signals 1
set cwd [pwd]
set_session_option -naming_style sv
set target cv32e40p_top
if {$target=="cv32e40p_top"} {
	set core_inst core_i
	set prefix ${core_inst}.
}
set_compile_option {*}[dict get $apps $app compile]
set_elaborate_option {*}[dict get $configs $cfg elab] -top $target
# The RTL directory cloned from GitHub, where tag cv32e40p_v1.8.0 is checked out
cd cv32e40p
source setup_mv.tcl
set_reset_sequence -low rst_ni
cd $cwd

set cfg_dir $cwd/$cfg
set pve_mode_dir $cwd/$cfg/$pve_mode
set app_dir $cwd/$cfg/$pve_mode/$app
file mkdir $cfg_dir
file mkdir $pve_mode_dir
file mkdir $app_dir
##


### PROCESSOR APP FLOW ###

## ---------------------------------------------------------------------------------------------------------------------------------
##          1        >     2      >        3        >      4       >          5           >       6       >          7
## ---------------------------------------------------------------------------------------------------------------------------------
##    PRE-ANALYSIS   |   DESIGN   |  POST-ANALYSIS  |  ASSERTION   |      ASSERTION       |  PERFORMANCE  |       ASSERTION
##    CONFIGURATION  |  ANALYSIS  |  CONFIGURATION  |  GENERATION  |  READING & RETUNING  |  ENHANCEMENT  |  RUNNING & DEBUGGING
## ---------------------------------------------------------------------------------------------------------------------------------

## ---------------------------------------------------------------------------------------------------------------------------------
## processor_integrity::<CMD>     | DESCRIPTION
## ---------------------------------------------------------------------------------------------------------------------------------
## extract_ISA                    | Extract ISA from a RISC-V based processor core and store data in a processor database.
##    -core_instance <>           | Specify instance name of the core in the DUV to instantiate the VIP on.
##    -csr_addr <>                | Specify CSR address signal that might be used to assist extraction.
##    -csr_rdata <>               | Specify CSR read data signal that might be used to assist extraction.
## merge_data                     | Merge JSON data into the database.
##    -file <>                    | Specify JSON file to be merged.
##    -configuration <>           | Specify predefined JSON configuration to be merged.
## generate_assertions            | Generate assertions for verifying the RISC-V core based on the database.
##   -create_individual_checks <> | Specify extensions for which assertions are generated per instruction.
##   -exclude_extensions <>       | Specify extensions for which assertions generation is supressed.
##   -include_extensions <>       | Specify extensions only for which assertions are generated.
## generate_IVA                   | Perform initial value abstraction of architecture state.
##   -candidates <>               | Specify architecture register fields to be abstracted.
## analyze_trace                  | Perform detailed trace analysis of run assertions.
## save_data                      | Write the processor database, or part of it, to a JSON file.
## clear_data                     | Clear JSON data from the processor database.
## ---------------------------------------------------------------------------------------------------------------------------------
## For full app documentation run "help *processor_integrity::<CMD>*" or refer to Chapter 14. of the User Manual.
## ---------------------------------------------------------------------------------------------------------------------------------

## 0. APP SETUP ##

package require processor_integrity
processor_integrity::clear_data -core_checker_version 2024.2

### APPEND THE FOLLOWING SET OF DEFINES (ONLY IF NECESSARY) ###
## ---------------------------------------------------------------------------------------------------------------------------------
## DEFINE                     | USE CASE IF SET
## ---------------------------------------------------------------------------------------------------------------------------------
## GRADUAL VERIFICATION      ##
## SKIP_PC_CHECK              | Skip checking PC register updates.
## SKIP_RF_CHECK              | Skip checking register file updates.
## SKIP_CSR_CHECK             | Skip checking CSR updates and reads.
## SKIP_DMEM_CHECK            | Skip checking data memory requests.
## LIMIT_TOTAL_INSTR_COUNT    | Limit total # of instructions allowed in the pipeline.
## PERFORMANCE ENHANCEMENT   ##
## RESTRICT_REGS              | Restrict instruction decoding & register file verification to a subset of registers.
## RESTRICT_REGISTER_INDEX    | Restrict register file verification to one register only, instruction decoding is not affected.
## RESTRICT_CHECK_DATA_SLICE  | Restrict register file data and memory write data verification to a slice or even a bit.
## RESTRICT_MUL_OPS_FREE_BITS | Restrict # of operand bits allowed to toggle checking multiplication/ division instruction datapath.
## RESTRICT_DMEM_STALL_CYCLES | Restrict data memory stall cycles to specific number. Has an effect w/ protocol VIPs' usage.
## TAILORED VERIFICATION     ##
## PVE_M_SUPPORT              | Enable checking M extension data path. By default, only the control path is checked.
## PVE_FPU_SUPPORT            | Enable checking F extension data path. By default, only the control path is checked.
## CHECK_ACCESS_FAULTS        | Enable checking all access faults fully according to the privileged specification or Smepmp.
## CUSTOM_MEM_INTERFACES      | Constrain memory interfaces. Use only in case bus protocols implemented are not tool supported.
## ---------------------------------------------------------------------------------------------------------------------------------
lappend defines {*}[dict get $configs $cfg define] {*}[dict get $pve_modes $pve_mode define] RESTRICT_REGS RESTRICT_DMEM_STALL_CYCLES=2
##

### RE-SET THE FOLLOWING SET OF VARIABLES (ONLY IF NECESSARY) ###
lappend pre_analysis_json_files_to_merge spec.json {*}[dict get $configs $cfg json]
set csr_addr_to_assist_analysis {}
set csr_rdata_to_assist_analysis {}
set core_instance_to_instantiate_vip_on ${core_inst}
lappend post_analysis_json_files_to_merge spec.json {*}[dict get $configs $cfg json] core.json
lappend extensions_to_generate_individual_checks_for F Zfinx
set extensions_to_exclude_assertion_generation_for {}
if {"CV_LOOP" in $defines} {
	lappend pre_analysis_json_files_to_merge Xpulp_hwlp.json
	lappend post_analysis_json_files_to_merge Xpulp_hwlp.json
}
##

### EXTEND THE FOLLOWING LISTS BY THE RESPECTIVE RTL SIGNALS (ONLY IF NECESSARY) ###
lappend mul_signals_to_cut ${prefix}ex_stage_i.mult_i.result_o ${prefix}ex_stage_i.alu_i.alu_div_i.Res_DO ${prefix}ex_stage_i.alu_i.alu_div_i.Cnt_DP
lappend fpu_signals_to_cut ${prefix}apu_result_i ${prefix}apu_flags_i
lappend rtl_signals_to_cut
lappend rtl_signals_to_disassemble ${prefix}instr_rdata_i ${prefix}instr_rdata_id ${prefix}if_stage_i.instr_aligned
##

if {![info exists reuse_files] || !$reuse_files} {

## 1. PRE-ANALYSIS CONFIGURATION ##

	foreach i ${pre_analysis_json_files_to_merge} {
		processor_integrity::merge_data -file ${i}
	}

## 2. DESIGN ANALYSIS ##

	processor_integrity::extract_ISA -csr_addr $csr_addr_to_assist_analysis -csr_rdata $csr_rdata_to_assist_analysis -core_instance $core_instance_to_instantiate_vip_on

## 3. POST-ANALYSIS CONFIGURATION ##

	foreach i ${post_analysis_json_files_to_merge} {
		processor_integrity::merge_data -file ${i}
	}

	if {"CFG_ZFINX" in $defines} {
		onespin::data::set ISA/Z/Zfinx true
	}

	if {$pve_mode ne "DEF"} {
		onespin::data::set PVE/checker_instance "RV_chk_DP"
	}

## 4. ASSERTION GENERATION ##

	cd $pve_mode_dir
	processor_integrity::generate_assertions -create_individual_checks $extensions_to_generate_individual_checks_for -exclude_extensions $extensions_to_exclude_assertion_generation_for -force
	cd $cwd
} else {
	puts "-W- Re-using previously generated files! Make sure to re-generate all files on adopting a new tool version or changing the JSON configuration!"
	source $pve_mode_dir/RISCV_disass.tcl
	source RISCV_disass.tcl
}

## 5. ASSERTION READING & RETUNING ##

### USE TO CONSTRAIN MEMORY INTERFACES (ONLY IF BUS PROTOCOLS IMPLEMENTED ARE TOOL SUPPORTED) ###
## Instantiate the respective bus protocol VIP for each of the fetch and data memory interfaces
## The VIPs in this case are used to check and more importantly constrain memory interfaces
## Read in the instantiated VIPs, my_{}.sv, using the read_sva command below
#instantiate_vip -addr_sig instr_addr_o -generated_instance_name obi_imem_checker -filename obi_imem.sv obi
#instantiate_vip -addr_sig data_addr_o  -generated_instance_name obi_dmem_checker -filename obi_dmem.sv obi
##

read_sva -define $defines -include_path $pve_mode_dir {core_checker.sv $pve_mode_dir/bind.sv vips/obi_?mem.sv}

## 7.1 ASSERTION RUNNING & DEBUGGING ##

### USE TO RUN INITIAL SET OF ASSERTIONS ###
set_check_option -prover_exec_order { { approver1 approver4 prover2:0 prover2:8 prover2:11 disprover1 disprover3 } } -disprover1_steps 40 -disprover3_steps 40
check [get_checks -filter name=~"*invariant_a"||name=~"*legal_CSR_reset_state_a"||name=~"*RESET_a"]
##

## 6. PERFORMANCE ENHANCEMENT ##

### USE TO COMPUTE INVARIANTS (IF NECESSARY) ###
compute_invariants
##

if {$app eq "PRC"} {
	### USE TO PERFORM AUTOMATIC INITIAL VALUE ABSTRACTION (IVA) OF ARCHITECTURE STATE (IF NECESSARY) ###
	lappend candidates X F frm
	if {"CFG_XP" in $defines} {
		lappend candidates lpstart0 lpstart1 lpend0 lpend1
	}
	processor_integrity::generate_IVA -candidates $candidates
	##
}

### USE TO CUT DESIGN COMPLEX SIGNALS (IF NECESSARY) ###
if {$pve_mode ne "DPM"} {
	lappend rtl_signals_to_cut {*}$mul_signals_to_cut
}
if {($pve_mode ne "DPF") && ("CFG_F" in $defines || "CFG_ZFINX" in $defines)} {
	lappend rtl_signals_to_cut {*}$fpu_signals_to_cut
}
add_cut_signals $rtl_signals_to_cut
cut_signals
##

## 7.2 ASSERTION RUNNING & DEBUGGING ##

### USE TO EASE DEBUGGING BY DISASSEMBLING VALUES OF RTL SIGNALS HOLDING INSTRUCTION WORDS & RUN THE OTHER ASSERTIONS ###
foreach i ${rtl_signals_to_disassemble} {
  use_value_printer ${i} PVE_disass
}
##

exclude_check [get_checks -filter name=~"*hdl*"||name=~"*FSQRT_S_a*"||name=~"**FDIV_S_a*"]
check_consistency -category model_building -effort maximum

set DEF_checks [lsort -dictionary [get_checks -filter excluded==false&&(type==property||type==assertion)]]
set DPM_checks [lsort -dictionary [get_checks -filter excluded==false&&(name=~"*RV32M.*"||name=~"*RV32X.CV_XDOT*"||name=~"*RV32X.CV_MUL*"||name=~"*RV32X.CV_MAC*"||name=~"*RV32X.CV_CPLXMUL*")]]
set DPF_checks [lsort -dictionary [get_checks -filter excluded==false&&(name=~"*RV32F.*"||name=~"*RV32Zfinx.*")]]

set group_1_checks [lsort -dictionary [concat core_i.RV_chk.ops.RESET_a [get_checks -filter excluded==false&&type==assertion]]]
set group_2_checks [lsort -dictionary [list core_i.RV_chk.xcpt.XCPT_IF_ID_a core_i.RV_chk.RV32C.ARITH_a core_i.RV_chk.RV32C.BRANCH_Taken_a core_i.RV_chk.RV32C.BRANCH_a core_i.RV_chk.RV32C.JUMP_a core_i.RV_chk.xcpt.EBREAK_a core_i.RV_chk.RV32I.MEM_MultiAccess_a core_i.RV_chk.RV32I.RETURN_a core_i.RV_chk.RV32X.CV_ADD_X_a core_i.RV_chk.RV32X.CV_BITMAN_OTHER_a core_i.RV_chk.RV32X.CV_EXTRACTX_X_a core_i.RV_chk.RV32X.CV_INSERTX_a core_i.RV_chk.RV32X.CV_PACKXX_X_a core_i.RV_chk.RV32X.CV_SETUPX_a core_i.RV_chk.RV32X.CV_SHUFFLE2_X_a core_i.RV_chk.RV32Zicsr.CSRx_a]]
set group_3_checks [lsort -dictionary [list core_i.RV_chk.ops.BUBBLE_a core_i.RV_chk.RV32I.ARITH_a core_i.RV_chk.xcpt.ECALL_a core_i.RV_chk.RV32I.FENCE_a core_i.RV_chk.RV32I.WFI_a core_i.RV_chk.RV32X.CV_ABS_X_a core_i.RV_chk.RV32X.CV_CLIPXX_a core_i.RV_chk.RV32X.CV_CMPEQ_X_a core_i.RV_chk.RV32X.CV_EXTRACTXX_a core_i.RV_chk.RV32X.CV_EXTXX_a core_i.RV_chk.RV32X.CV_INSERT_X_a core_i.RV_chk.RV32X.CV_SX_I_a core_i.RV_chk.RV32X.CV_SX_RI_a core_i.RV_chk.RV32X.CV_ADDXXNR_a core_i.RV_chk.RV32X.CV_SHUFFLEIX_SCI_B_a core_i.RV_chk.RV32X.CV_BSETX_a core_i.RV_chk.RV32X.CV_BXXIMM_Taken_a core_i.RV_chk.RV32X.CV_ENDX_a core_i.RV_chk.RV32X.CV_LXX_I_a core_i.RV_chk.RV32X.CV_LXX_RI_a core_i.RV_chk.RV32X.CV_SLL_X_a core_i.RV_chk.RV32X.CV_STARTX_a core_i.RV_chk.RV32X.CV_ADD_DIVX_a core_i.RV_chk.RV32X.CV_ADDXXN_a core_i.RV_chk.RV32X.CV_AVGU_X_a core_i.RV_chk.RV32X.CV_BCLRX_a core_i.RV_chk.RV32X.CV_SUB_DIVX_a core_i.RV_chk.RV32X.CV_SUBROTMJ_X_a core_i.RV_chk.RV32X.CV_SUBXXN_a core_i.RV_chk.RV32X.CV_SUBXXNR_a core_i.RV_chk.RV32X.CV_MAXU_X_a]]
set group_4_checks [lsort -dictionary [concat [get_checks -filter excluded==false&&name=~"*RV32X.CV_ELW*"] core_i.RV_chk.RV32X.CV_COUNTX_a core_i.RV_chk.RV32X.CV_LXX_R_a core_i.RV_chk.RV32X.CV_MAXX_a core_i.RV_chk.RV32X.CV_SX_R_a core_i.RV_chk.RV32C.MEM_a core_i.RV_chk.RV32C.MEM_MultiAccess_a core_i.RV_chk.RV32I.BRANCH_a core_i.RV_chk.RV32I.BRANCH_Taken_a core_i.RV_chk.RV32I.JUMP_a core_i.RV_chk.RV32I.MEM_a core_i.RV_chk.RV32X.CV_ABS_a core_i.RV_chk.RV32X.CV_AND_X_a core_i.RV_chk.RV32X.CV_AVG_X_a core_i.RV_chk.RV32X.CV_BXXIMM_a core_i.RV_chk.RV32X.CV_CMPGE_X_a core_i.RV_chk.RV32X.CV_CMPGEU_X_a core_i.RV_chk.RV32X.CV_CMPGT_X_a core_i.RV_chk.RV32X.CV_CMPGTU_X_a core_i.RV_chk.RV32X.CV_CMPLE_X_a core_i.RV_chk.RV32X.CV_CMPLEU_X_a core_i.RV_chk.RV32X.CV_CMPLT_X_a core_i.RV_chk.RV32X.CV_CMPLTU_X_a core_i.RV_chk.RV32X.CV_CMPNE_X_a core_i.RV_chk.RV32X.CV_CPLXCONJ_a core_i.RV_chk.RV32X.CV_LXX_I_MultiAccess_a core_i.RV_chk.RV32X.CV_LXX_R_MultiAccess_a core_i.RV_chk.RV32X.CV_LXX_RI_MultiAccess_a core_i.RV_chk.RV32X.CV_MAX_X_a core_i.RV_chk.RV32X.CV_MIN_X_a core_i.RV_chk.RV32X.CV_MINU_X_a core_i.RV_chk.RV32X.CV_MINX_a core_i.RV_chk.RV32X.CV_OR_X_a core_i.RV_chk.RV32X.CV_SHUFFLE_X_a core_i.RV_chk.RV32X.CV_SLEX_a core_i.RV_chk.RV32X.CV_SRA_X_a core_i.RV_chk.RV32X.CV_SRL_X_a core_i.RV_chk.RV32X.CV_SUB_X_a core_i.RV_chk.RV32X.CV_SX_I_MultiAccess_a core_i.RV_chk.RV32X.CV_SX_R_MultiAccess_a core_i.RV_chk.RV32X.CV_SX_RI_MultiAccess_a core_i.RV_chk.RV32X.CV_XOR_X_a core_i.RV_chk.RV32Zifencei.FENCE_I_a]]
set group_5_checks [lsort -dictionary [get_checks -filter excluded==false&&(name=~"*RV32M.DIV16_a*"||name=~"*RV32M.DIV32_a*"||name=~"*RV32M.MUL_a*"||name=~"*RV32X.CV_XDOT*"||name=~"*RV32X.CV_MUL*"||name=~"*RV32X.CV_MAC*"||name=~"*RV32X.CV_CPLXMUL*")]]
set group_6_checks [lsort -dictionary [get_checks -filter excluded==false&&(name=~"*RV32F.*"||name=~"*RV32Zfinx.*")]]

set skipped_files "*/fpnew_* {} */gated_clk_cell* {} */lzc* {} */pa_fdsu_* {} */pa_fpu_* {} */rr_arb_tree* {}"

puts "\n-INFO- Compile options::\n\n\t[dict get $apps $app compile]\n"
puts "\n-INFO- Elaborate options::\n\n\t[dict get $configs $cfg elab]\n"
puts "\n-INFO- Defines::\n\n\t$defines\n"
puts "\n-INFO- Cut signals::\n\n\t$rtl_signals_to_cut\n"

if {$app eq "PRC"} {

	set_check_option -prover_exec_order { { approver1 approver4 prover2:0 prover2:8 prover2:11 } }
	check [set ${pve_mode}_checks]
	report_result -signoff -details

}

if {$app eq "QTF"} {

	set_check_option -prover_exec_order { { disprover1 disprover3 } } -disprover1_steps 20 -disprover3_steps 20

	set html "${app_dir}/html_results_${cfg}_${pve_mode}"
	set results "${app_dir}/qtf_results_${cfg}_${pve_mode}_R"
	set log "${app_dir}/${app}_${cfg}_${pve_mode}_R"

	if {$pve_mode eq "DEF"} {

		for {set i 1} {$i < 7} {incr i} {
			puts "\nGroup (${i}) checks:\n\nTotal number of checks is: [llength [set group_${i}_checks]] \n"
			foreach j [set group_${i}_checks] {
				puts "$j"
			}
		}

		for {set i 1} {$i < 7} {incr i} {
			puts "Group (${i}) checks: Total number of checks is: [llength [set group_${i}_checks]]"
		}

		for {set i 1} {$i < 7} {incr i} {
			
			start_message_log -force ${log}${i}.log
			if {$i == 1} {
				quantify_run 0 $i 1.0 2 1 ${html}_L2_S1_R${i} ${results}${i} $group_1_checks {}	{}
			} elseif {$i == 2} {
				quantify_run 0 $i 4.0 4 3 ${html}_L4_S4_R${i} ${results}${i} $group_2_checks ${results}[expr $i-1] $skipped_files
			} elseif {$i == 3} {
				quantify_run 0 $i 2.0 4 3 ${html}_L4_S2_R${i} ${results}${i} $group_3_checks ${results}[expr $i-1] $skipped_files
			} elseif {$i == 4} {
				quantify_run 0 $i 2.0 4 3 ${html}_L4_S2_R${i} ${results}${i} $group_4_checks ${results}[expr $i-1] $skipped_files
			} elseif {$i == 5} {
				quantify_run 0 $i 4.0 4 3 ${html}_L4_S4_R${i} ${results}${i} $group_5_checks ${results}[expr $i-1] $skipped_files
			} elseif {($i == 6) && ("CFG_F" in $defines || "CFG_ZFINX" in $defines)} {
				quantify_run 0 $i 4.0 4 3 ${html}_L4_S4_R${i} ${results}${i} $group_6_checks ${results}[expr $i-1] {}
			}
			stop_message_log
		}

	} elseif {$pve_mode eq "DPM"} {

		if {("CFG_F" in $defines || "CFG_ZFINX" in $defines)} {
			set i 7
		} else {
			set i 6
		}

		start_message_log ${log}${i}.log
		quantify_run 0 $i 4.0 4 3 ${html}_L4_S4_R${i} ${results}${i} $group_5_checks ${cfg_dir}/DEF/QTF/qtf_results_${cfg}_DEF_R[expr $i-1] $skipped_files
		stop_message_log

	} elseif {$pve_mode eq "DPF"} {

		set i 8

		start_message_log ${log}${i}.log
		quantify_run 0 $i 2.0 4 3 ${html}_L4_S4_R${i} ${results}${i} $group_6_checks ${cfg_dir}/DPM/QTF/qtf_results_${cfg}_DPM_R[expr $i-1] {}
		stop_message_log

	}

}

if {$app eq "VCI"} {

	set_check_option -prover_exec_order { { disprover1 disprover3 } } -disprover1_steps 20 -disprover3_steps 20

	set output_dir "${app_dir}/qtf_coverage_${cfg}_${pve_mode}"
	set checks "[set ${pve_mode}_checks]"
	set results "${cfg_dir}/${pve_mode}/QTF/qtf_results_${cfg}_${pve_mode}_R"
	set log "${app_dir}/${app}_${cfg}_${pve_mode}"

	if {$pve_mode eq "DEF"} {
		if {("CFG_F" in $defines || "CFG_ZFINX" in $defines)} {
			set i 6
		} else {
			set i 5
		}
	} elseif {$pve_mode eq "DPM"} {
		if {("CFG_F" in $defines || "CFG_ZFINX" in $defines)} {
			set i 7
		} else {
			set i 6
		}
	} elseif {$pve_mode eq "DPF"} {
		set i 8
	}

	start_message_log ${log}.log
	puts "\n-INFO- Launching VCI Command::\nexport_quantify_coverage -call_script t.sh -generate_flist -output_dir $output_dir -checks $checks ${results}${i}\n"
	export_quantify_coverage -call_script t.sh -generate_flist -output_dir $output_dir -checks $checks ${results}${i}
	stop_message_log

}
