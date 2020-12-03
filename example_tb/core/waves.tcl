# Copyright 2020 ETH Zurich
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.


# Author: Davide Schiavone <pschiavo@iis.ee.ethz.ch>
#         Robert Balas <balasr@iis.ee.ethz.ch>

# catch {
#     if {$trdb_all ne ""} {
#	foreach inst $trdb_all {
#	    add wave -group [file tail $inst] $inst/*
#	}
#     }
# } err

# if {$err ne ""} {
#     puts "\[TCL\]: Suppressed error: $err"
# }

# add fc
set rvcores [find instances -recursive -bydu cv32e40p_core -nodu]
set fpuprivate [find instances -recursive -bydu fpu_private]
set tb_top [find instances -recursive -bydu tb_top -nod]
set mm_ram [find instances -recursive -bydu mm_ram -nod]
set dp_ram [find instances -recursive -bydu dp_ram -nod]
set riscv_random_stall [find instances -recursive -bydu riscv_random_stall -nod]

if {$tb_top ne ""} {
    foreach inst $tb_top {
	add wave -group [file tail $inst] $inst/*
    }
}

if {$mm_ram ne ""} {
    foreach inst $mm_ram {
	add wave -group [file tail $inst] $inst/*
    }
}

if {$dp_ram ne ""} {
    foreach inst $dp_ram {
	add wave -group [file tail $inst] $inst/*
    }
}

if {$riscv_random_stall ne ""} {
    foreach inst $riscv_random_stall {
	add wave -group [file tail $inst] $inst/*
    }
}

if {$rvcores ne ""} {

  set hwlp [find instances -recursive -bydu cv32e40p_hwloop_controller -nodu]

  add wave -group "Core"                                                    $rvcores/*

  add wave -group "Sleep Unit"                               $rvcores/sleep_unit_i/*

  add wave -group "IF Stage" -group "Prefetch"                              $rvcores/if_stage_i/prefetch_buffer_i/*
  add wave -group "IF Stage" -group "Prefetch" -group "FIFO"                $rvcores/if_stage_i/prefetch_buffer_i/fifo_i/*
  add wave -group "IF Stage" -group "Prefetch" -group "OBI"                 $rvcores/if_stage_i/prefetch_buffer_i/instruction_obi_i/*
  add wave -group "IF Stage" -group "Prefetch" -group "Prefetch Controller" $rvcores/if_stage_i/prefetch_buffer_i/prefetch_controller_i/*
  add wave -group "IF Stage"                                                $rvcores/if_stage_i/*
  add wave -group "Aligner"                                                 $rvcores/if_stage_i/aligner_i/*
  add wave -group "RVCDecoder"                                              $rvcores/if_stage_i/compressed_decoder_i/*

  add wave -group "ID Stage"                                                $rvcores/id_stage_i/*
  add wave -group "RF"                                                      $rvcores/id_stage_i/register_file_i/mem
  add wave -group "RF_FP"                                                   $rvcores/id_stage_i/register_file_i/mem_fp

  add wave -group "Decoder"                                                 $rvcores/id_stage_i/decoder_i/*
  add wave -group "Controller"                                              $rvcores/id_stage_i/controller_i/*
  add wave -group "Int Ctrl"                                                $rvcores/id_stage_i/int_controller_i/*

  set hwlp [find instances -recursive -bydu riscv_hwloop_regs -nodu]
  if {$hwlp ne ""} {
      add wave -group "HWloop"   -group "Hwloop Regs"                       $rvcores/id_stage_i/HWLOOP_REGS/hwloop_regs_i/*
  }

  add wave -group "EX Stage" -group "ALU"                                   $rvcores/ex_stage_i/alu_i/*
  add wave -group "EX Stage" -group "ALU_DIV"                               $rvcores/ex_stage_i/alu_i/alu_div_i/*
  add wave -group "EX Stage" -group "MUL"                                   $rvcores/ex_stage_i/mult_i/*
  if {$fpuprivate ne ""} {
    add wave -group "EX Stage" -group "APU_DISP"                            $rvcores/ex_stage_i/genblk1/apu_disp_i/*
    add wave -group "EX Stage" -group "FPU"                                 $rvcores/ex_stage_i/genblk1/genblk1/fpu_i/*
  }
  add wave -group "EX Stage"                                                $rvcores/ex_stage_i/*
  add wave -group "LSU"                                                     $rvcores/load_store_unit_i/*
  add wave -group "LSU" -group "OBI"                                        $rvcores/load_store_unit_i/data_obi_i/*
  add wave -group "CSR"                                                     $rvcores/cs_registers_i/*
  add wave -group "MM RAM"                                                  $mm_ram/*
}

configure wave -namecolwidth  250
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -timelineunits ns
