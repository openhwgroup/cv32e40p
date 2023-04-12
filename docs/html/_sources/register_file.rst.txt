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

.. _register-file:

Register File
=============

Source files: :file:`rtl/cv32e40p_register_file_ff.sv`

CV32E40P has 31 32-bit wide registers which form registers ``x1`` to ``x31``.
Register ``x0`` is statically bound to 0 and can only be read, it does not
contain any sequential logic.

The register file has three read ports and two write ports. Register file reads are performed in the ID stage.
Register file writes are performed in the WB stage.

Floating-Point Register File
----------------------------

If the optional FPU is instantiated, unless ``ZFINX`` is configured, the register file is extended
with an additional register bank of 32 registers ``f0``-``f31``. These registers
are stacked on top of the existing register file and can be accessed
concurrently with the limitation that a maximum of three operands per
cycle can be read. Each of the three operands addresses is extended with
an register file select signal which is generated in the instruction decoder
when a FP instruction is decoded. This additional signals determines if
the operand is located in the integer or the floating point register
file.

Forwarding paths, and write-back logic are shared for the integer and
floating point operations and are not replicated.

If ``ZFINX`` parameter is set, there is no additional register bank and FPU instructions are using
the same register file than for integer instructions.
