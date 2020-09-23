# add fc execution trace
set rvcores [find instances -recursive -bydu cv32e40p_core -nodu]
set tracer [find instances -recursive -bydu cv32e40p_tracer -nodu]
set fpuprivate [find instances -recursive -bydu fpu_private]

if {$rvcores ne ""} {

    add wave -group "Software Debugging" $rvcores/clk_i
    add wave -group "Software Debugging" -divider "Instructions at ID stage, sampled half a cycle later"

if {$tracer ne ""} {
    add wave -group "Software Debugging" $tracer/insn_disas
    add wave -group "Software Debugging" $tracer/insn_pc
    add wave -group "Software Debugging" $tracer/insn_val
}

    add wave -group "Software Debugging" -divider "Program counter at ID and IF stage"
    add wave -group "Software Debugging" $rvcores/pc_id
    add wave -group "Software Debugging" $rvcores/pc_if
    add wave -group "Software Debugging" -divider "Register File contents"
    add wave -group "Software Debugging" $rvcores/id_stage_i/register_file_i/mem
    if {$fpuprivate ne ""} {
	add wave -group "Software Debugging" $rvcores/id_stage_i/register_file_i/mem_fp
    }

}

configure wave -namecolwidth  250
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -timelineunits ns
