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

.. _hwloop-specs:

CORE-V Hardware Loop Extensions
===============================

To increase the efficiency of small loops, CV32E40P supports hardware
loops (HWLoop) optionally. They can be enabled by setting
the ``PULP_XPULP`` parameter.
Hardware loops make executing a piece of code
multiple times possible, without the overhead of branches or updating a counter.
Hardware loops involve zero stall cycles for jumping to the first
instruction of a loop.

A hardware loop is defined by its start address (pointing to the first
instruction in the loop), its end address (pointing to the instruction
that will be executed last in the loop) and a counter that is
decremented every time the loop body is executed. CV32E40P contains two
hardware loop register sets to support nested hardware loops, each of
them can store these three values in separate flip flops which are
mapped in the CSR address space.
Loop number 0 has higher priority than loop number 1 in a nested loop
configuration, meaning that loop 0 represents the inner loop.

Hardware Loop constraints
^^^^^^^^^^^^^^^^^^^^^^^^^

The HWLoop constraints are:

-  Start and End address of an HWLoop must be word aligned

-  HWLoop body must contain at least 3 instructions.
   An illegal exception is raised otherwise.

-  No Compressed instructions (RVC) allowed in the HWLoop body.
   An illegal exception is raised otherwise.

-  No uncoditional jump instructions allowed in the HWLoop body.
   An illegal exception is raised otherwise.

-  No coditional branch instructions allowed in the HWLoop body.
   An illegal exception is raised otherwise.

-  No privileged instructions (mret, dret, ecall, wfi) allowed in the HWLoop body, except for ebreak.
   An illegal exception is raised otherwise.

-  No memory ordering instructions (fence, fence.i) allowed in the HWLoop body.
   An illegal exception is raised otherwise.

-  The End address of the outermost HWLoop (#1) must be at least 2
   instructions further than the End address innermost HWLoop (#0),
   i.e. HWLoop[1].endaddress >= HWLoop[0].endaddress + 8
   An illegal exception is raised otherwise.

In order to use hardware loops, the compiler needs to setup the loop
beforehand with the following instructions. Note that the minimum loop
size is 3 instructions and the last instruction cannot be any jump or
branch instruction.

For debugging and context switches, the hardware loop registers are
mapped into the CSR address space and thus it is possible to read and
write them via csrr and csrw instructions. Since hardware loop registers
could be overwritten in when processing interrupts, the registers have
to be saved in the interrupt routine together with the general purpose
registers. The CS HWLoop registers are described in the :ref:`cs-registers`
section.

The CORE-V GCC compiler uses HWLoop automatically without the need of assembly.
The mainline GCC does not generate any CORE-V instructions as for the other custom extensions.

Below an assembly code example of an nested HWLoop that computes
a matrix addition.

.. code-block:: c
   :linenos:

   asm volatile (
       ".option norvc;"
       "add %[j],x0, x0;"
       "add %[j],x0, x0;"
       "cv.count  x1, %[N];"
       "cv.endi   x1, endO;"
       "cv.starti x1, startO;"
           "startO:   cv.count  x0, %[N];"
           "cv.endi   x0, endZ;"
           "cv.starti x0, startZ;"
               "startZ: addi %[i], x0, 1;"
               "        addi %[i], x0, 1;"
               "endZ:   addi %[i], x0, 1;"
           "addi %[j],x0, 2;"
           "endO:   addi %[j], x0, 2;"
       : [i] "+r" (i), [j] "+r" (j)
       : [N] "r" (10)
   );


At the beginning of the HWLoop, the registers %[i] and %[j] are 0.
The innermost loop, from start0 to end0, adds to %[i] three times 1 and
it is executed 10x10 times. Whereas the outermost loop, from startO to endO,
executes 10 times the innermost loop and adds two times 2 to the register %[j].
At the end of the loop, the register %[i] contains 300 and the register %[j] contains 40.

