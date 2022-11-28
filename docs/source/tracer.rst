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

.. _tracer:

Tracer
======

The module ``cv32e40p_tracer`` can be used to create a log of the executed instructions.
It is a behavioral, non-synthesizable, module instantiated in the example testbench that is provided for
the ``cv32e40p_core``. It can be enabled during simulation by defining **CV32E40P_TRACE_EXECUTION**.

Output file
-----------

All traced instructions are written to a log file.
The log file is named ``trace_core_<HARTID>.log``, with ``<HARTID>`` being the 32 digit hart ID of the core being traced.

Trace output format
-------------------

The trace output is in tab-separated columns.

1. **Time**: The current simulation time.
2. **Cycle**: The number of cycles since the last reset.
3. **PC**: The program counter
4. **Instr**: The executed instruction (base 16).
   32 bit wide instructions (8 hex digits) are uncompressed instructions, 16 bit wide instructions (4 hex digits) are compressed instructions.
5. **Decoded instruction**: The decoded (disassembled) instruction in a format equal to what objdump produces when calling it like ``objdump -Mnumeric -Mno-aliases -D``.
   - Unsigned numbers are given in hex (prefixed with ``0x``), signed numbers are given as decimal numbers.
   - Numeric register names are used (e.g. ``x1``).
   - Symbolic CSR names are used.
   - Jump/branch targets are given as absolute address if possible (PC + immediate).
6. **Register and memory contents**: For all accessed registers, the value before and after the instruction execution is given. Writes to registers are indicated as ``registername=value``, reads as ``registername:value``. For memory accesses, the address and the loaded and stored data are given.

.. code-block:: text

  Time          Cycle      PC       Instr    Decoded instruction Register and memory contents
            130         61 00000150 4481     c.li    x9,0        x9=0x00000000
            132         62 00000152 00008437 lui     x8,0x8      x8=0x00008000
            134         63 00000156 fff40413 addi    x8,x8,-1    x8:0x00008000  x8=0x00007fff
            136         64 0000015a 8c65     c.and   x8,x9       x8:0x00007fff  x9:0x00000000  x8=0x00000000
            142         67 0000015c c622     c.swsp  x8,12(x2)   x2:0x00002000  x8:0x00000000 PA:0x0000200c store:0x00000000  load:0xffffffff
