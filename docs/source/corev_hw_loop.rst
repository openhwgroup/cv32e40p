..
   Copyright 2024 OpenHW Group and Dolphin Design
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
  
   Licensed under the Solderpad Hardware License v 2.1 (the "License");
   you may not use this file except in compliance with the License, or,
   at your option, the Apache License version 2.0.
   You may obtain a copy of the License at
  
   https://solderpad.org/licenses/SHL-2.1/
  
   Unless required by applicable law or agreed to in writing, any work
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

.. _hwloop-specs:

CORE-V Hardware Loop feature
============================

To increase the efficiency of small loops, CV32E40P supports hardware
loops (HWLoop). They can be enabled by setting the ``COREV_PULP`` parameter.
Hardware loops make executing a piece of code
multiple times possible, without the overhead of branches penalty or updating a counter.
Hardware loops involve zero stall cycles for jumping to the first
instruction of a loop.

A hardware loop is defined by its start address (pointing to the first
instruction in the loop), its end address (pointing to the instruction
just after the last one executed by the loop) and a counter that is
decremented every time the last instruction of the loop body is executed.

CV32E40P contains two hardware loop register sets to support nested hardware loops,
each of them can store these three values in separate flip flops which are
mapped in the CSR address space.
Loop number 0 has higher priority than loop number 1 in a nested loop
configuration, meaning that loop 0 represents the inner loop and loop 1 is the outer loop.

Hardware Loop constraints
^^^^^^^^^^^^^^^^^^^^^^^^^

Following constraints must be respected by any toolchain compiler or by hand-written assembly code.
``Violation of these constraints will not generate any hardware exception`` and behaviour is undefined.

In order to catch **as early as possible** those software exceptions when executing a program either
on a verification Reference Model or on a virtual platform Instruction Set Simulator, ``those model/simulation platforms
should generate an error`` with a meaningfull message related to Hardware Loops constraints violation.
Those constraint checks could be done only for each instruction in the hardware loop body, meaning when (lpstartX <= PC <= lpendX - 4) and (lpcountX > 0).

The HWLoop constraints are:

-  HWLoop starti, endi, setupi and setup instructions addresses must be 32-bit aligned (PC-related instructions).

-  Start and End addresses of an HWLoop body must be 32-bit aligned.

-  End Address must be strictly greater than Start Address.

-  HWLoop #0 (resp. #1) start and end addresses **must not be modified** if HWLoop #0 (resp. #1) count is different than 0.

-  End address of an HWLoop must point to the instruction just after the last one of the HWLoop body.

-  HWLoop body must contain at least 3 instructions.

-  When both loops are nested, at least 1 instruction should be present between last innermost HWLoop (must be #0) instruction and
   last outermost HWLoop (must be #1) instruction. In other words the End address of the outermost HWLoop must be at least 8
   bytes further than the End address of the innermost HWLoop (HWLoop[1].endaddress >= HWLoop[0].endaddress + 8).

   In the example below the first "addi %[j], %[j], 2;" instruction is the one added due to this constraint.
   The code could have been simpler by using only one "addi %[j], %[j], 4;" instruction but to respect this constraint it has been split in two instructions.

-  HWLoop must always be entered from its start location (no branch/jump to a location inside a HWLoop body).

-  No HWLoop #0 (resp. #1) CSR should be modified inside the HWLoop #0 (resp. #1) body.

-  No Compressed instructions (RVC) allowed in the HWLoop body.

-  No jump or branch instructions allowed in the HWLoop body.

-  No memory ordering instructions (fence, fence.i) allowed in the HWLoop body.

-  No privileged instructions (mret, dret, wfi) allowed in the HWLoop body, except for ebreak and ecall.

The rationale of NOT generating any hardware exception when violating any of those constraints is that it would add resources
(32-bit adders and substractors needed for the third and fourth rules) which are costly in area and power consumption.
These additional (and costly) resources would be present just to catch situations that should never happen. 
This in an architectural choice in order to keep CV32E40P area and power consumption to its lowest level.

The rationale of putting the end-of-loop label to the first instruction after the last one of the loop body
is that it greatly simplifies compiler optimization (relative to basic blocks management).

In order to use hardware loops, the compiler needs to setup the loops beforehand with cv.start/i, cv.end/i, cv.count/i or cv.setup/i instructions.
The compiler will use HWLoop automatically whenever possible without the need of assembly.

For debugging, interrupts and context switches, the hardware loop registers are mapped into the CSR custom read-only address space.
To read them csrr instructions should be used and to write them register flavour of hardware loop instructions should be used.
Using csrw instructions to write hardware loop registers will generate an illegal instruction exception.
The CSR HWLoop registers are described in the :ref:`cs-registers` section.

Below an assembly code example of a nested HWLoop that computes a matrix addition.

.. code-block:: c
   :linenos:

   asm volatile (
       "add %[i],x0, x0;"
       "add %[j],x0, x0;"
       ".balign 4;"
       "cv.starti 1, start1;"
       "cv.endi   1, end1;"
       "cv.count  1, %[N];"
       "any instructions here"
       ".balign 4;"
       "cv.starti 0, start0;"
       "cv.endi   0, end0;"
       "any instructions here"
       ".balign 4;"
       ".option norvc;"
       "start1:;"
       "    cv.count 0, %[N];"
       "    start0:;"
       "        addi %[i], %[i], 1;"
       "        addi %[i], %[i], 1;"
       "        addi %[i], %[i], 1;"
       "    end0:;"
       "    addi %[j], %[j], 2;"
       "    addi %[j], %[j], 2;"
       "end1:;"
       : [i] "+r" (i), [j] "+r" (j)
       : [N] "r" (10)
   );

As HWLoop feature is enabled as soon as lpcountX > 0, lpstartX and lpendX **must** be programmed **before** lpcountX to avoid unexpected behavior.
For HWLoop where body contains up to 30 instructions, it is always better to use cv.setup* instructions which are updating all 3 HWLoop CSRs in the same cycle.

At the beginning of the HWLoop, the registers %[i] and %[j] are 0.
The innermost loop, from start0 to (end0 - 4), adds to %[i] three times 1 and
it is executed 10x10 times. Whereas the outermost loop, from start1 to (end1 - 4),
executes 10 times the innermost loop and adds two times 2 to the register %[j].
At the end of the loop, the register %[i] contains 300 and the register %[j] contains 40.

.. _hwloop-exceptions_handlers:

Hardware loops impact on application, exception handlers and debug program
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Application and ebreak/ecall exception handlers
-----------------------------------------------

When an ebreak or an ecall instruction is used in an application, special care should be given for their respective exception handler in case those instructions are the last one of an HWLoop.
Those handlers should manage MEPC and lpcountX CSRs updates because an hw loop early-exit could happen if not done.

At the end of the handlers after restoring the context/CSRs, a piece of smart code should be added with following highest to lowest order of priority:

1. if MEPC = lpend0 - 4 and lpcount0 > 1 then MEPC should be set to lpstart0 and lpcount0 should be decremented by 1,
2. else if MEPC = lpend0 - 4 and lpcount0 = 1 then MEPC should be incremented by 4 and lpcount0 should be decremented by 1,
3. else if MEPC = lpend1 - 4 and lpcount1 > 1 then MEPC should be set to lpstart1 and lpcount1 should be decremented by 1,
4. else if MEPC = lpend1 - 4 and lpcount1 = 1 then MEPC should be incremented by 4 and lpcount1 should be decremented by 1,
5. else if (lpstart0 <= MEPC < lpend0 - 4) or (lpstart1 <= MEPC < lpend1 - 4) then MEPC should be incremented by 4,
6. else if instruction at MEPC location is either ecall or ebreak then MEPC should be incremented by 4,
7. else if instruction at MEPC location location is c.ebreak then MEPC should be incremented by 2.

The 2 last cases are the standard ones when ebreak/ecall are not inside an HWLopp.

Interrupt handlers
------------------

When an interrupt is happening on the last HWLoop instruction, its execution is cancelled, its address is saved in MEPC and its execution will be resumed when returning from interrupt handler.
There is nothing special to be done in those interrupt handlers with respect to MEPC and lpcountX updates (except HWloop CSRs save/restore mentioned below), they will be correctly managed by design when executing this last HWLoop instruction after interrupt handler execution.

Illegal instruction exception handler
-------------------------------------

Depending if an application is going to resume or not after Illegal instruction exception handler, same MEPC/HWLoops CSRs management than ebreak/ecall could be necessary.

Debugger
--------

If ebreak is used to enter in Debug Mode (:ref:`ebreak_scenario_2`) and put at the last instruction location of an HWLoop, same management than above should be done but on DPC rather than on MEPC.

When ebreak instruction is used as Software Breakpoint by a debugger when in debug mode and is placed at the last instruction location of an HWLoop in instruction memory, no special management is foreseen.
When executing the Software Breakpoint/ebreak instruction, control is given back to the debugger which will manage the different cases.
For instance in Single-Step case, original instruction is put back in instruction memory, a Single-Step command is executed on this last instruction (with design updating PC and lpcountX to correct values) and Software Breakpoint/ebreak is put back by the debugger in memory.
 
When ecall instruction is used by a debugger to execute System Calls and is placed at the last instruction location of an HWLoop in instruction memory, debugger ecall handler in debug program should do the same than described above for application case.

HWloop CSRs save and restore
----------------------------

As synchronous/asynchronous exception or a debug event happening during HWloop execution is interrupting the normal HWloop execution, special care should be given to HWloop CSRs in case any exception handler or debug program is going to use HWloop feature (or even just call functions using them like memmove, memcpy...).

So HWloop CSRs save/restore should be added together with the general purpose registers to exception handlers or debug program.
