..
   Copyright (c) 2020 OpenHW Group
   
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

.. _register-file:

Register File
=============

Source files: :file:`rtl/cv32e40p_register_file_ff.sv` :file:`rtl/cv32e40p_register_file_latch.sv`

CV32E40P has 31 32-bit wide registers which form registers ``x1`` to ``x31``.
Register ``x0`` is statically bound to 0 and can only be read, it does not
contain any sequential logic.

The register file has three read ports and two write ports. Register file reads are performed in the ID stage.
Register file writes are performed in the WB stage.

There are two flavors of register file available.

 * Flip-flop based (:file:`rtl/cv32e40p_register_file_ff.sv`)
 * Latch-based (:file:`rtl/cv32e40p_register_file_latch.sv`)

Both flavors have their own benefits and trade-offs.
While the latch-based register file is recommended for ASICs, the
flip-flop based register file is recommended for FPGA synthesis,
although both are compatible with either synthesis target. Note the
flip-flop based register file is significantly larger than the
latch-based register-file for an ASIC implementation.


Flip-Flop-Based Register File
-----------------------------

The flip-flop-based register file uses regular, positive-edge-triggered flip-flops to implement the registers.
This makes it the **first choice when simulating the design using Verilator**.
To select the flip-flop-based register file, make sure to use the source file ``cv32e40p_register_file_ff.sv`` in your project.

Latch-based Register File
-------------------------

The latch-based register file uses level-sensitive latches to implement the registers.

This allows for significant area savings compared to an implementation using regular flip-flops and
thus makes the latch-based register file the **first choice for ASIC implementations**.
Simulation of the latch-based register file is possible using commercial tools.

.. note:: The latch-based register file cannot be simulated using Verilator.

The latch-based register file can also be used for FPGA synthesis, but this is not recommended as FPGAs usually do not well support latches.

To select the latch-based register file, make sure to use the source file ``cv32e40p_register_file_latch.sv`` in your project.
In addition, a technology-specific clock gating cell must be provided to keep the clock inactive when the latches are not written.
This cell must be wrapped in a module called ``cv32e40p_clock_gate``.
For more information regarding the clock gating cell, checkout :ref:`getting-started`.

FPU Register File
-----------------

In case the optional FPU is instantiated, the register file is extended
with an additional register bank of 32 registers ``f0``-``f31``. These registers
are stacked on top of the existing register file and can be accessed
concurrently with the limitation that a maximum of three operands per
cycle can be read. Each of the three operands addresses is extended with
an fp_reg_sel signal which is generated in the instruction decoder
when a FP instruction is decoded. This additional signals determines if
the operand is located in the integer or the floating point register
file.

Forwarding paths, and write-back logic are shared for the integer and
floating point operations and are not replicated.
