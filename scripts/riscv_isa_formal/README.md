# RISC-V ISA Formal Verification

RISC-V ISA Formal Verification methodology has been used with Siemens Questa Processor tool and its RISC-V ISA Processor Verification app.

## Configurations

  | Top Parameters     | XP     | XPF0     | XPF1     | XPF2     | XPZF0     | XPZF1     | XPZF2     |
  | :----------------- | :----: |:-------: | :------: | :------: | :-------: | :-------: | :-------: |
  | COREV_PULP         | 1      | 1        | 1        | 1        | 1         | 1         | 1         |
  | COREV_CLUSTER      | 0      | 0        | 0        | 0        | 0         | 0         | 0         |
  | FPU                | 0      | 1        | 1        | 1        | 1         | 1         | 1         |
  | ZFINX              | 0      | 0        | 0        | 0        | 1         | 1         | 1         |
  | FPU_ADDMUL_LAT     | 0      | 0        | 1        | 2        | 0         | 1         | 2         |
  | FPU_OTHERS_LAT     | 0      | 0        | 1        | 2        | 0         | 1         | 2         |

## Tool apps

- PRC : Property Checking
- QTF : Quantify
- VCI : Verification Coverage Integration

## Prove modes

- DEF : Control path verification of all instructions and datapath verification of all instructions except multiplication, division or floating point ones
- DPM : Data path verification of multiplication/ division instructions
- DPF : Data path verification of floating-point instructions

## Directory Structure of this Repo

- Makefile
- launch_command_example

### verif
Contains all files to create assertions and to launch different tool apps on different configurations and using different modes.

> [!CAUTION]
> core_checker.sv contains proprietary information and is only available to Siemens Questa Processor customers.
> Once Questa Processor licenses have been purchased, this file can be requested to Siemens support center.

## How to launch a run

> [!CAUTION]
> Siemens Questa Processor 2024.2 and above must be used.

- Locally clone cv32e40p github repository or make a symbolic link to an existing repo.
- launch following command:<br>
  make GUI=1 APP=PRC CONF=XP MODE=DEF NAME=v1_8_0 VERBOSE=1 PREPARE=1 all >&! run_gui-PRC-cfg_XP-mode_DEF-v1_8_0.log
- or use launch_command_example to launch different runs in parallel.

## Commands to launch assertion checks for each configuration

- XP : PRC app with DEF and DPM modes
- XPF[0,1,2] and XPZF[0,1,2] : PRC app with DEF, DPM and DPF modes
