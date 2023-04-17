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

.. _exceptions-interrupts:

Exceptions and Interrupts
=========================

CV32E40P implements trap handling for interrupts and exceptions according to the RISC-V Privileged Specification, version 1.11.
The ``irq_i[31:16]`` interrupts are a custom extension.

When entering an interrupt/exception handler, the core sets the ``mepc`` CSR to the current program counter and saves ``mstatus``.MIE to ``mstatus``.MPIE.
All exceptions cause the core to jump to the base address of the vector table in the ``mtvec`` CSR.
Interrupts are handled in either direct mode or vectored mode depending on the value of ``mtvec``.MODE. In direct mode the core
jumps to the base address of the vector table in the ``mtvec`` CSR. In vectored mode the core jumps to the base address
plus four times the interrupt ID. Upon executing an MRET instruction, the core jumps to the program counter previously saved in the
``mepc`` CSR and restores ``mstatus``.MPIE to ``mstatus``.MIE.

The base address of the vector table must be aligned to 256 bytes (i.e., its least significant byte must be 0x00) and can be programmed
by writing to the ``mtvec`` CSR. For more information, see the :ref:`cs-registers` documentation.

The core starts fetching at the address defined by ``boot_addr_i``. It is assumed that the boot address is supplied via a register
to avoid long paths to the instruction fetch unit.

Interrupt Interface
-------------------

:numref:`Interrupt interface signals` describes the interrupt interface.

.. table:: Interrupt interface signals
  :name: Interrupt interface signals
  :widths: 20 15 65
  :class: no-scrollbar-table

  +-------------------------+---------------+--------------------------------------------------+
  | **Signal**              | **Direction** | **Description**                                  |
  +=========================+===============+==================================================+
  | ``irq_i[31:0]``         | input         | Level sensistive active high interrupt inputs.   |
  |                         |               | Not all interrupt inputs can be used on          |
  |                         |               | CV32E40P. Specifically irq_i[15:12],             |
  |                         |               | irq_i[10:8], irq_i[6:4] and irq_i[2:0] shall be  |
  |                         |               | tied to 0 externally as they are reserved for    |
  |                         |               | future standard use (or for cores which are not  |
  |                         |               | Machine mode only) in the RISC-V Privileged      |
  |                         |               | specification.                                   |
  |                         |               |                                                  |
  |                         |               | irq_i[11], irq_i[7], and irq_i[3]                |
  |                         |               | correspond to the Machine External               |
  |                         |               | Interrupt (MEI), Machine Timer Interrupt (MTI),  |
  |                         |               | and Machine Software Interrupt (MSI)             |
  |                         |               | respectively.                                    |
  |                         |               |                                                  |
  |                         |               | The irq_i[31:16] interrupts                      |
  |                         |               | are a CV32E40P specific extension to the RISC-V  |
  |                         |               | Basic (a.k.a. CLINT) interrupt scheme.           |
  +-------------------------+---------------+--------------------------------------------------+
  | ``irq_ack_o``           | output        | Interrupt acknowledge                            |
  |                         |               |                                                  |
  |                         |               | Set to 1 for one cycle                           |
  |                         |               | when the interrupt with ID ``irq_id_o[4:0]`` is  |
  |                         |               | taken.                                           |
  +-------------------------+---------------+--------------------------------------------------+
  | ``irq_id_o[4:0]``       | output        | Interrupt index for taken interrupt              |
  |                         |               |                                                  |
  |                         |               | Only valid when ``irq_ack_o`` = 1.               |
  +-------------------------+---------------+--------------------------------------------------+

Interrupts
----------

The ``irq_i[31:0]`` interrupts are controlled via the ``mstatus``, ``mie`` and ``mip`` CSRs. CV32E40P uses the upper 16 bits of ``mie`` and ``mip`` for custom interrupts (``irq_i[31:16]``),
which reflects an intended custom extension in the RISC-V Basic (a.k.a. CLINT) interrupt architecture.
After reset, all interrupts are disabled.
To enable interrupts, both the global interrupt enable (MIE) bit in the ``mstatus`` CSR and the corresponding individual interrupt enable bit in the ``mie`` CSR need to be set.
For more information, see the :ref:`cs-registers` documentation.

If multiple interrupts are pending, they are handled in the fixed priority order defined by the RISC-V Privileged Specification, version 1.11 (see Machine Interrupt Registers, Section 3.1.9).
The highest priority is given to the interrupt with the highest ID, except for the Machine Timer Interrupt, which has the lowest priority. So from high to low priority the interrupts are
ordered as follows: ``irq_i[31]``, ``irq_i[30]``, ..., ``irq_i[16]``, ``irq_i[11]``, ``irq_i[3]``, ``irq_i[7]``.

All interrupt lines are level-sensitive. There are two supported mechanisms by which interrupts can be cleared at the external source.

* A software-based mechanism in which the interrupt handler signals completion of the handling routine to the interrupt source, e.g., through a memory-mapped register, which then deasserts the corresponding interrupt line.
* A hardware-based mechanism in which the ``irq_ack_o`` and ``irq_id_o[4:0]`` signals are used to clear the interrupt sourcee, e.g. by an external interrupt controller. ``irq_ack_o`` is a 1 ``clk_i`` cycle pulse during which ``irq_id_o[4:0]`` reflects the index in ``irq_id[*]`` of the taken interrupt.

In Debug Mode, all interrupts are ignored independent of ``mstatus``.MIE and the content of the ``mie`` CSR.

Exceptions
----------

CV32E40P can trigger an exception due to the following exception causes:

.. table:: Exceptions
  :name: Exceptions
  :widths: 20 80
  :class: no-scrollbar-table

  +--------------------+---------------------------------------------------------------+
  | **Exception Code** | **Description**                                               |
  +====================+===============================================================+
  | 2                  | Illegal instruction                                           |
  +--------------------+---------------------------------------------------------------+
  | 3                  | Breakpoint                                                    |
  +--------------------+---------------------------------------------------------------+
  | 11                 | Environment call from M-Mode (ECALL)                          |
  +--------------------+---------------------------------------------------------------+

The illegal instruction exception and M-Mode ECALL instruction exceptions cannot be disabled and are always active.
The core raises an illegal instruction exception for any instruction in the RISC-V privileged and unprivileged specifications that is explicitly defined as being illegal according to the ISA implemented by the core, as well as for any instruction that is left undefined in these specifications unless the instruction encoding is configured as a custom CV32E40P instruction for specific parameter settings as defined in (see :ref:`custom-isa-extensions`).
For example, in case the parameter ``FPU`` is set to 0, the CV32E40P raises an illegal instruction exception for any RVF instruction or CSR instruction trying to access F CSRs.
The same concerns PULP extensions everytime both parameters ``COREV_PULP`` and ``CORE_CLUSTER`` are set to 0 (see :ref:`core-integration`).

.. only:: PMP

  +----------------+---------------------------------------------------------------+
  | Exception Code | Description                                                   |
  +----------------+---------------------------------------------------------------+
  |              1 | Instruction access fault                                      |
  +----------------+---------------------------------------------------------------+
  |              5 | Load access fault                                             |
  +----------------+---------------------------------------------------------------+
  |              7 | Store access fault                                            |
  +----------------+---------------------------------------------------------------+

  The instruction access fault and load-store access faults cannot be disabled and are always active. The PMP
  itself can be disabled.

.. only:: USER

  +----------------+---------------------------------------------------------------+
  | Exception Code | Description                                                   |
  +----------------+---------------------------------------------------------------+
  |              8 | Environment call from U-Mode (ECALL)                          |
  +----------------+---------------------------------------------------------------+

  The U-Mode ECALL instruction exception cannot be disabled and is always active.

Nested Interrupt/Exception Handling
-----------------------------------

CV32E40P does support nested interrupt/exception handling in software.
The hardware automatically disables interrupts upon entering an interrupt/exception handler.
Otherwise, interrupts/exceptions during the critical part of the handler, i.e. before software has saved the ``mepc`` and ``mstatus`` CSRs, would cause those CSRs to be overwritten.
If desired, software can explicitly enable interrupts by setting ``mstatus``.MIE to 1 from within the handler.
However, software should only do this after saving ``mepc`` and ``mstatus``.
There is no limit on the maximum number of nested interrupts.
Note that, after enabling interrupts by setting ``mstatus``.MIE to 1, the current handler will be interrupted also by lower priority interrupts.
To allow higher priority interrupts only, the handler must configure ``mie`` accordingly.

The following pseudo-code snippet visualizes how to perform nested interrupt handling in software.

.. code-block:: c
   :linenos:

   isr_handle_nested_interrupts(id) {
     // Save mpec and mstatus to stack
     mepc_bak = mepc;
     mstatus_bak = mstatus;

     // Save mie to stack (optional)
     mie_bak = mie;

     // Keep lower-priority interrupts disabled (optional)
     mie = mie & ~((1 << (id + 1)) - 1);

     // Re-enable interrupts
     mstatus.MIE = 1;

     // Handle interrupt
     // This code block can be interrupted by other interrupts.
     // ...

     // Restore mstatus (this disables interrupts) and mepc
     mstatus = mstatus_bak;
     mepc = mepc_bak;

     // Restore mie (optional)
     mie = mie_bak;
   }

Nesting of interrupts/exceptions in hardware is not supported.
