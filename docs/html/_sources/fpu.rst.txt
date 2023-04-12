..
   Copyright (c) 2023 OpenHW Group
   
   Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at
  
   https://solderpad.org/licenses/
  
   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
  
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

.. _fpu:

Floating Point Unit (FPU)
=========================

The RV32F ISA extension for floating-point support in the form of IEEE-754 single
precision can be enabled by setting the parameter **FPU** of the ``cv32e40p_top`` top level module
to 1. This will extend the CV32E40P decoder accordingly and will instantiate the FPU.
The FPU repository used by the CV32E40P is available at `https://github.com/openhwgroup/cvfpu <https://github.com/openhwgroup/cvfpu/tree/3116391bf66660f806b45e212b9949c528b4e270>`_ and
its documentation can be found `here <https://github.com/openhwgroup/cvfpu/blob/3116391bf66660f806b45e212b9949c528b4e270/docs/README.md>`_.
CVFPU v1.0.0 release has been copied in CV32E40P repository inside rtl/vendor (used for verification and implementation) so all core and FPU RTL files should be taken from CV32E40P repository.

cv32e40p_fpu_manifest file is listing all necessary files for both the Core and CVFPU.

CVFPU parameters
----------------

As CVFPU is an highly configurable IP, here is the list of its parameters and their actual value used when CVFPU is intantiated through a wrapper in ``cv32e40p_top`` module.

.. table:: CVFPU Features parameter
  :name: CVFPU Features parameter
  :widths: 17 15 17 51
  :class: no-scrollbar-table

  +------------------------------+----------------+------------------+--------------------------------------------------------------------------+
  | **Name**                     | **Type/Range** | **Value**        | **Description**                                                          |
  +==============================+================+==================+==========================================================================+
  | ``Width``                    | int            | 32               | **Datapath Width**                                                       |
  |                              |                |                  |                                                                          |
  |                              |                |                  | Specifies the width of the input and output data ports and               |
  |                              |                |                  | of the datapath.                                                         |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------------+
  | ``EnableVectors``            | logic          | 0                | **Vectorial Hardware Generation**                                        |
  |                              |                |                  |                                                                          |
  |                              |                |                  | Controls the generation of packed-SIMD computation units.                |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------------+
  | ``EnableNanBox``             | logic          | 0                | **NaN-Boxing Check Control**                                             |
  |                              |                |                  |                                                                          |
  |                              |                |                  | Controls whether input value NaN-boxing is enforced.                     |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------------+
  | ``FpFmtMask``                | fmt_logic_t    | {1, 0, 0, 0, 0}  | **Enabled Floating-Point Formats**                                       |
  |                              |                |                  |                                                                          |
  |                              |                |                  | Enables respectively:                                                    |
  |                              |                |                  |                                                                          |
  |                              |                |                  | IEEE Single-Precision format                                             |
  |                              |                |                  |                                                                          |
  |                              |                |                  | IEEE Double-Precision format                                             |
  |                              |                |                  |                                                                          |
  |                              |                |                  | IEEE Half-Precision format                                               |
  |                              |                |                  |                                                                          |
  |                              |                |                  | Custom Byte-Precision format                                             |
  |                              |                |                  |                                                                          |
  |                              |                |                  | Custom Alternate Half-Precision format                                   |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------------+
  | ``IntFmtMask``               | ifmt_logic_t   | {0, 0, 1, 0}     | **Enabled Integer Formats**                                              |
  |                              |                |                  |                                                                          |
  |                              |                |                  | Enables respectively:                                                    |
  |                              |                |                  |                                                                          |
  |                              |                |                  | Byte format                                                              |
  |                              |                |                  |                                                                          |
  |                              |                |                  | Half-Word format                                                         |
  |                              |                |                  |                                                                          |
  |                              |                |                  | Word format                                                              |
  |                              |                |                  |                                                                          |
  |                              |                |                  | Double-Word format                                                       |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------------+

.. table:: CVFPU Implementation parameter
  :name: CVFPU Implementation parameter
  :widths: 13 21 30 36
  :class: no-scrollbar-table

  +------------------------------+------------------------+-------------------------------------+----------------------------------------------------------------------------+
  | **Name**                     | **Type/Range**         | **Value**                           | **Description**                                                            |
  +==============================+========================+=====================================+============================================================================+
  | ``PipeRegs``                 | opgrp_fmt_unsigned_t   | {                                   | **Number of Pipelining Stages**                                            |
  |                              |                        |                                     |                                                                            |
  |                              |                        | {``FPU_ADDMUL_LAT``, 0, 0, 0, 0},   | This parameter sets a number of pipeline stages to be inserted into the    |
  |                              |                        |                                     | computational units per operation group, per FP format. As such,           |
  |                              |                        | {default: 1},                       | latencies for different operations and different formats can be freely     |
  |                              |                        |                                     | configured.                                                                |
  |                              |                        | {default: ``FPU_OTHERS_LAT``},      |                                                                            |
  |                              |                        |                                     | Respectively:                                                              |
  |                              |                        | {default: ``FPU_OTHERS_LAT``}       |                                                                            |
  |                              |                        |                                     | ADDition/MULtiplication operation group                                    |
  |                              |                        | }                                   |                                                                            |
  |                              |                        |                                     | DIVision/SQuare RooT operation group                                       |
  |                              |                        |                                     |                                                                            |
  |                              |                        |                                     | NON COMPuting operation group                                              |
  |                              |                        |                                     |                                                                            |
  |                              |                        |                                     | CONVersion operation group                                                 |
  |                              |                        |                                     |                                                                            |
  |                              |                        |                                     | ``FPU_ADDMUL_LAT`` and ``FPU_OTHERS_LAT`` are ``cv32e40p_top`` parameters. |
  +------------------------------+------------------------+-------------------------------------+----------------------------------------------------------------------------+
  | ``UnitTypes``                | opgrp_fmt_unit_types_t | {                                   | **HW Unit Implementation**                                                 |
  |                              |                        |                                     |                                                                            |
  |                              |                        | {default: MERGED},                  | This parameter allows to control resources by either removing operation    |
  |                              |                        |                                     | units for certain formats and operations,                                  |
  |                              |                        | {default: MERGED},                  | or merging multiple formats into one.                                      |
  |                              |                        |                                     |                                                                            |
  |                              |                        | {default: PARALLEL},                | Respectively:                                                              |
  |                              |                        |                                     |                                                                            |
  |                              |                        | {default: MERGED}                   | ADDition/MULtiplication operation group                                    |
  |                              |                        |                                     |                                                                            |
  |                              |                        | }                                   | DIVision/SQuare RooT operation group                                       |
  |                              |                        |                                     |                                                                            |
  |                              |                        |                                     | NON COMPuting operation group                                              |
  |                              |                        |                                     |                                                                            |
  |                              |                        |                                     | CONVersion operation group                                                 |
  +------------------------------+------------------------+-------------------------------------+----------------------------------------------------------------------------+
  | ``PipeConfig``               | pipe_config_t          | AFTER                               | **Pipeline Register Placement**                                            |
  |                              |                        |                                     |                                                                            |
  |                              |                        |                                     | This parameter controls where pipeling registers (number defined by        |
  |                              |                        |                                     | ``PipeRegs``) are placed in each operational unit.                         |
  |                              |                        |                                     |                                                                            |
  |                              |                        |                                     | AFTER means they are all placed at the output of each operational unit.    |
  |                              |                        |                                     |                                                                            |
  |                              |                        |                                     | See :ref:`synthesis_with_fpu` advices to get best synthesis results.       |
  +------------------------------+------------------------+-------------------------------------+----------------------------------------------------------------------------+

.. table:: Other CVFPU parameters
  :name: Other CVFPU parameters
  :widths: 20 15 10 55
  :class: no-scrollbar-table

  +------------------------------+----------------+------------------+--------------------------------------------------------------------------+
  | **Name**                     | **Type/Range** | **Value**        | **Description**                                                          |
  +==============================+================+==================+==========================================================================+
  | ``TagType``                  |                | logic            | The SystemVerilog data type of the operation tag input and output ports. |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------------+
  | ``TrueSIMDClass``            | int            | 0                | Vectorial mode classify operation RISC-V compliancy.                     |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------------+
  | ``EnableSIMDMask``           | int            | 0                | Inactive vectorial lanes floating-point status flags masking.            |
  +------------------------------+----------------+------------------+--------------------------------------------------------------------------+

FP Register File
----------------

By default a dedicated register file consisting of 32
floating-point registers, ``f0``-``f31``, is instantiated. This default behavior
can be overruled by setting the parameter **ZFINX** of the ``cv32e40p_top`` top level
module to 1, in which case the dedicated register file is
not included and the general purpose register file is used instead to
host the floating-point operands.

The latency of the individual instructions are explained in :ref:`instructions_latency_table` table.

To allow FPU unit to be put in sleep mode at the same time the core is doing so, a clock gating cell is instantiated in ``cv32e40p_top`` top level module as well
with its enable signal being inverted ``core_sleep_o`` core output.

FP CSR
------

When using floating-point extensions the standard specifies a
floating-point status and control register (:ref:`csr-fcsr`) which contains the
exceptions that occurred since it was last reset and the rounding mode.
:ref:`csr-fflags` and :ref:`csr-frm` can be accessed directly or via :ref:`csr-fcsr` which is mapped to
those two registers.

Reminder for programmers
------------------------

As mentioned in RISC-V Privileged Architecture specification, ``mstatus``.FS should be set to Initial to be able to use FP instructions.
If ``mstatus``.FS = Off (reset value), any instruction that attempts to read or write the Floating-Point state (F registers or F CSRs) will cause an illegal instruction exception. 

Upon interrupt or context switch events, ``mstatus``.SD should be read to see if Floating-Point state has been altered.
If following executed program (interrupt routine or whatsover) is going to use FP instructions and only if ``mstatus``.SD = 1 (means FS = Dirty),
then the whole FP state (F registers and F CSRs) should be saved in memory and program should set ``mstatus``.FS to Clean.
When returning to interrupted or main program, if ``mstatus``.FS = Clean then the whole FP state should be restored from memory.
