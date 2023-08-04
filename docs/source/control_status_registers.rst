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

.. _cs-registers:

Control and Status Registers
============================

CV32E40P does not implement all control and status registers specified in
the RISC-V privileged specifications, but is limited to the registers
that were needed for the PULP system. The reason for this is that we
wanted to keep the footprint of the core as low as possible and avoid
any overhead that we do not explicitly need.

CSR Map
-------

:numref:`Control and Status Register Map` lists all
implemented CSRs.  Two columns in :numref:`Control and Status Register Map` may require additional explanation:

The **Privilege** column indicates the access mode of a CSR. The first letter
indicates the lowest privilege level required to access the CSR. Attempts to
access a CSR with a higher privilege level than the core is currently running
in will throw an illegal instruction exception.  This is largely a moot point
for the CV32E40P as it only supports machine and debug modes. The remaining
letters indicate the read and/or write behavior of the CSR when accessed by
the indicated or higher privilge level:

* **RW**: CSR is **read-write**.  That is, CSR instructions (e.g. csrrw) may
  write any value and that value will be returned on a subsequent read (unless
  a side-effect causes the core to change the CSR value).

* **RO**: CSR is **read-only**.  Writes by CSR instructions raise an illegal
  instruction exception.

Writes of a non-supported value to **WLRL** bitfields of a **RW** CSR do not result in an illegal
instruction exception. The exact bitfield access types, e.g. **WLRL** or **WARL**, can be found in the RISC-V
privileged specification.

In the **Description** column there is a specific comment which identifies those CSRs that are dependent on the value
of specific parameters. If these parameters are not set as
indicated in :numref:`Control and Status Register Map` then the associated CSR is not implemented. If the column does not
mention any parameter then the associated CSR is always implemented.

Reads or writes to a CSR that is not implemented will result in an illegal
instruction exception.

.. table:: Control and Status Register Map
  :name: Control and Status Register Map
  :widths: 13 17 15 55
  :class: no-scrollbar-table

  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | **CSR Address** | **Name**          | **Privilege** | **Description**                                                    |
  +=================+===================+===============+====================================================================+
  | **User CSRs**                                                                                                            |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x001           | ``fflags``        | URW           | Floating-point accrued exceptions.                                 |
  |                 |                   |               |                                                                    |
  |                 |                   |               | Only present if ``FPU`` = 1                                        |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x002           | ``frm``           | URW           | Floating-point dynamic rounding mode.                              |
  |                 |                   |               |                                                                    |
  |                 |                   |               | Only present if ``FPU`` = 1                                        |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x003           | ``fcsr``          | URW           | Floating-point control and status register.                        |
  |                 |                   |               |                                                                    |
  |                 |                   |               | Only present if ``FPU`` = 1                                        |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xC00           | ``cycle``         | URO           | (HPM) Cycle Counter                                                |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xC02           | ``instret``       | URO           | (HPM) Instructions-Retired Counter                                 |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xC03           | ``hpmcounter3``   | URO           | (HPM) Performance-Monitoring Counter 3                             |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | .                 .                   .               .                                                                  |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xC1F           | ``hpmcounter31``  | URO           | (HPM) Performance-Monitoring Counter 31                            |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xC80           | ``cycleh``        | URO           | (HPM) Upper 32 bits Cycle Counter                                  |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xC82           | ``instreth``      | URO           | (HPM) Upper 32 bits Instructions-Retired Counter                   |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xC83           | ``hpmcounterh3``  | URO           | (HPM) Upper 32 bits Performance-Monitoring Counter 3               |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | .                 .                   .               .                                                                  |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xC9F           | ``hpmcounterh31`` | URO           | (HPM) Upper 32 bits Performance-Monitoring Counter 31              |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | **User Custom CSRs**                                                                                                     |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xCC0           | ``lpstart0``      | URO           | Hardware Loop 0 Start.                                             |
  |                 |                   |               |                                                                    |
  |                 |                   |               | Only present if ``COREV_PULP`` = 1                                 |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xCC1           | ``lpend0``        | URO           | Hardware Loop 0 End.                                               |
  |                 |                   |               |                                                                    |
  |                 |                   |               | Only present if ``COREV_PULP`` = 1                                 |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xCC2           | ``lpcount0``      | URO           | Hardware Loop 0 Counter.                                           |
  |                 |                   |               |                                                                    |
  |                 |                   |               | Only present if ``COREV_PULP`` = 1                                 |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xCC4           | ``lpstart1``      | URO           | Hardware Loop 1 Start.                                             |
  |                 |                   |               |                                                                    |
  |                 |                   |               | Only present if ``COREV_PULP`` = 1                                 |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xCC5           | ``lpend1``        | URO           | Hardware Loop 1 End.                                               |
  |                 |                   |               |                                                                    |
  |                 |                   |               | Only present if ``COREV_PULP`` = 1                                 |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xCC6           | ``lpcount1``      | URO           | Hardware Loop 1 Counter.                                           |
  |                 |                   |               |                                                                    |
  |                 |                   |               | Only present if ``COREV_PULP`` = 1                                 |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xCD0           | ``uhartid``       | URO           | Hardware Thread ID                                                 |
  |                 |                   |               |                                                                    |
  |                 |                   |               | Only present if ``COREV_PULP`` = 1                                 |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xCD1           | ``privlv``        | URO           | Privilege Level                                                    |
  |                 |                   |               |                                                                    |
  |                 |                   |               | Only present if ``COREV_PULP`` = 1                                 |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xCD2           | ``zfinx``         | URO           | ``ZFINX`` ISA                                                      |
  |                 |                   |               |                                                                    |
  |                 |                   |               | Only present if                                                    |
  |                 |                   |               | ``COREV_PULP`` = 1 & (``FPU`` = 0 | (``FPU`` = 1 & ``ZFINX`` = 1)) |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | **Machine CSRs**                                                                                                         |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x300           | ``mstatus``       | MRW           | Machine Status                                                     |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x301           | ``misa``          | MRW           | Machine ISA                                                        |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x304           | ``mie``           | MRW           | Machine Interrupt Enable register                                  |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x305           | ``mtvec``         | MRW           | Machine Trap-Handler Base Address                                  |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x320           | ``mcountinhibit`` | MRW           | (HPM) Machine Counter-Inhibit register                             |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x323           | ``mhpmevent3``    | MRW           | (HPM) Machine Performance-Monitoring Event Selector 3              |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | .                 .                   .               .                                                                  |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x33F           | ``mhpmevent31``   | MRW           | (HPM) Machine Performance-Monitoring Event Selector 31             |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x340           | ``mscratch``      | MRW           | Machine Scratch                                                    |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x341           | ``mepc``          | MRW           | Machine Exception Program Counter                                  |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x342           | ``mcause``        | MRW           | Machine Trap Cause                                                 |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x343           | ``mtval``         | MRW           | Machine Trap Value                                                 |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x344           | ``mip``           | MRW           | Machine Interrupt Pending register                                 |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x7A0           | ``tselect``       | MRW           | Trigger Select register                                            |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x7A1           | ``tdata1``        | MRW           | Trigger Data register 1                                            |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x7A2           | ``tdata2``        | MRW           | Trigger Data register 2                                            |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x7A3           | ``tdata3``        | MRW           | Trigger Data register 3                                            |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x7A4           | ``tinfo``         | MRO           | Trigger Info                                                       |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x7A8           | ``mcontext``      | MRW           | Machine Context register                                           |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x7AA           | ``scontext``      | MRW           | Machine Context register                                           |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x7B0           | ``dcsr``          | DRW           | Debug Control and Status                                           |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x7B1           | ``dpc``           | DRW           | Debug PC                                                           |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x7B2           | ``dscratch0``     | DRW           | Debug Scratch register 0                                           |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0x7B3           | ``dscratch1``     | DRW           | Debug Scratch register 1                                           |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xB00           | ``mcycle``        | MRW           | (HPM) Machine Cycle Counter                                        |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xB02           | ``minstret``      | MRW           | (HPM) Machine Instructions-Retired Counter                         |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xB03           | ``mhpmcounter3``  | MRW           | (HPM) Machine Performance-Monitoring Counter 3                     |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | .                 .                   .               .                                                                  |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xB1F           | ``mhpmcounter31`` | MRW           | (HPM) Machine Performance-Monitoring Counter 31                    |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xB80           | ``mcycleh``       | MRW           | (HPM) Upper 32 bits Machine Cycle Counter                          |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xB82           | ``minstreth``     | MRW           | (HPM) Upper 32 bits Machine Instructions-Retired Counter           |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xB83           | ``mhpmcounterh3`` | MRW           | (HPM) Upper 32 bits Machine Performance-Monitoring Counter 3       |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | .                 .                   .               .                                                                  |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xB9F           | ``mhpmcounterh31``| MRW           | (HPM) Upper 32 bits Machine Performance-Monitoring Counter 31      |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xF11           | ``mvendorid``     | MRO           | Machine Vendor ID                                                  |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xF12           | ``marchid``       | MRO           | Machine Architecture ID                                            |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xF13           | ``mimpid``        | MRO           | Machine Implementation ID                                          |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+
  | 0xF14           | ``mhartid``       | MRO           | Hardware Thread ID                                                 |
  +-----------------+-------------------+---------------+--------------------------------------------------------------------+

.. only:: USER

  .. table:: Control and Status Register Map (additional CSRs for User mode)
    :name: Control and Status Register Map (additional CSRs for User mode)

    +-------------------+----------------+---------------+------------------------------------------+
    | **CSR address**   | **Name**       | **Privilege** | **Description**                          |
    +-------------------+----------------+---------------+------------------------------------------+
    |                   |                |               |                                          |
    +===================+================+===============+==========================================+
    | 0x000             | ``ustatus``    | URW           | User Status                              |
    +-------------------+----------------+---------------+------------------------------------------+
    | 0x005             | ``utvec``      | URW           | User Trap-Handler Base Address           |
    +-------------------+----------------+---------------+------------------------------------------+
    | 0x041             | ``uepc``       | URW           | User Exception Program Counter           |
    +-------------------+----------------+---------------+------------------------------------------+
    | 0x042             | ``ucause``     | URW           | User Trap Cause                          |
    +-------------------+----------------+---------------+------------------------------------------+
    | 0x306             | ``mcounteren`` | MRW           | Machine Counter Enable                   |
    +-------------------+----------------+---------------+------------------------------------------+

CSR Descriptions
-----------------

What follows is a detailed definition of each of the CSRs listed above. The
**Mode** column defines the access mode behavior of each bit field when
accessed by the privilege level specified in :numref:`Control and Status Register Map` (or a higher privilege
level):

* **RO**: **read-only** fields are not affect by CSR write instructions.  Such
  fields either return a fixed value, or a value determined by the operation of
  the core.

* **RW**: **read/write** fields store the value written by CSR writes. Subsequent
  reads return either the previously written value or a value determined by the
  operation of the core.

Floating-point CSRs
:::::::::::::::::::

.. _csr-fflags:

Floating-point accrued exceptions (``fflags``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x001 (only present if ``FPU`` = 1)

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+-------------------------------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                                         |
  +=============+===========+=========================================================================+
  | 31:5        | RO        | Writes are ignored; reads return 0.                                     |
  +-------------+-----------+-------------------------------------------------------------------------+
  | 4           | RW        | NV - Invalid Operation                                                  |
  +-------------+-----------+-------------------------------------------------------------------------+
  | 3           | RW        | DZ - Divide by Zero                                                     |
  +-------------+-----------+-------------------------------------------------------------------------+
  | 2           | RW        | OF - Overflow                                                           |
  +-------------+-----------+-------------------------------------------------------------------------+
  | 1           | RW        | UF - Underflow                                                          |
  +-------------+-----------+-------------------------------------------------------------------------+
  | 0           | RW        | NX - Inexact                                                            |
  +-------------+-----------+-------------------------------------------------------------------------+

.. _csr-frm:

Floating-point dynamic rounding mode (``frm``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x002 (only present if ``FPU`` = 1)

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+--------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                      |
  +=============+===========+======================================+
  | 31:3        | RO        | Writes are ignored; reads return 0.  |
  +-------------+-----------+--------------------------------------+
  | 2:0         | RW        | Rounding mode:                       |
  |             |           |                                      |
  |             |           | 000 = RNE                            |
  |             |           |                                      |
  |             |           | 001 = RTZ                            |
  |             |           |                                      |
  |             |           | 010 = RDN                            |
  |             |           |                                      |
  |             |           | 011 = RUP                            |
  |             |           |                                      |
  |             |           | 100 = RMM                            |
  |             |           |                                      |
  |             |           | 101 = Invalid                        |
  |             |           |                                      |
  |             |           | 110 = Invalid                        |
  |             |           |                                      |
  |             |           | 111 = DYN                            |
  +-------------+-----------+--------------------------------------+

.. _csr-fcsr:

Floating-point control and status register (``fcsr``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x003 (only present if ``FPU`` = 1)

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+------------------------------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                                        |
  +=============+===========+========================================================================+
  | 31:8        | RO        | Reserved. Writes are ignored; reads return 0.                          |
  +-------------+-----------+------------------------------------------------------------------------+
  | 7:5         | RW        | Rounding Mode (``frm``)                                                |
  +-------------+-----------+------------------------------------------------------------------------+
  | 4:0         | RW        | Accrued Exceptions (``fflags``)                                        |
  +-------------+-----------+------------------------------------------------------------------------+

Hardware Loops CSRs
:::::::::::::::::::

HWLoop Start Address 0/1 (``lpstart0/1``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xCC0/0xCC4 (only present if ``COREV_PULP`` = 1)

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+-------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                           |
  +=============+===========+===========================================+
  | 31:2        | URO       | Start Address of the HWLoop 0/1.          |
  +-------------+-----------+-------------------------------------------+
  | 1:0         | URO       | 0                                         |
  +-------------+-----------+-------------------------------------------+

HWLoop End Address 0/1 (``lpend0/1``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xCC1/0xCC5 (only present if ``COREV_PULP`` = 1)

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+-------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                           |
  +=============+===========+===========================================+
  | 31:2        | URO       | End Address of the HWLoop 0/1.            |
  +-------------+-----------+-------------------------------------------+
  | 1:0         | URO       | 0                                         |
  +-------------+-----------+-------------------------------------------+

HWLoop Count Address 0/1 (``lpcount0/1``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xCC2/0xCC6 (only present if ``COREV_PULP`` = 1)

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+-------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                           |
  +=============+===========+===========================================+
  | 31:0        | URO       | Number of iteration of HWLoop 0/1.        |
  +-------------+-----------+-------------------------------------------+

Other CSRs
::::::::::

Machine Status (``mstatus``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x300

Reset Value: 0x0000_1800

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+-------------------------------------------------------------------------------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                                                                                         |
  +=============+===========+=========================================================================================================================+
  | 31          | RO        | **SD:** State Dirty                                                                                                     |
  |             |           |                                                                                                                         |
  |             |           | SD set to 1 if **FS** = 11 meaning Floating point State is dirty so save/restore is needed in case of context switch.   |
  |             |           |                                                                                                                         |
  |             |           | 0 if ``FPU`` = 0 or (``FPU`` = 1 and ``ZFINX`` = 1).                                                                    |
  +-------------+-----------+-------------------------------------------------------------------------------------------------------------------------+
  | 30:15       | RO        | 0, Unimplemented.                                                                                                       |
  +-------------+-----------+-------------------------------------------------------------------------------------------------------------------------+
  | 14:13       | RW        | **FS:** Floating point State                                                                                            |
  |             |           |                                                                                                                         |
  |             |           | 00 = Off                                                                                                                |
  |             |           |                                                                                                                         |
  |             |           | 01 = Initial                                                                                                            |
  |             |           |                                                                                                                         |
  |             |           | 10 = Clean                                                                                                              |
  |             |           |                                                                                                                         |
  |             |           | 11 = Dirty                                                                                                              |
  |             |           |                                                                                                                         |
  |             |           | 0 if ``FPU`` = 0 or (``FPU`` = 1 and ``ZFINX`` = 1).                                                                    |
  +-------------+-----------+-------------------------------------------------------------------------------------------------------------------------+
  | 12:11       | RO        | **MPP:** Machine Previous Priviledge mode                                                                               |
  |             |           |                                                                                                                         |
  |             |           | 11 when the user mode is not enabled.                                                                                   |
  +-------------+-----------+-------------------------------------------------------------------------------------------------------------------------+
  | 10:8        | RO        | 0, Unimplemented.                                                                                                       |
  +-------------+-----------+-------------------------------------------------------------------------------------------------------------------------+
  | 7           | RO        | **MPIE:** Machine Previous Interrupt Enable                                                                             |
  |             |           |                                                                                                                         |
  |             |           | When an exception is encountered, MPIE will be set to MIE.                                                              |
  |             |           | When the mret instruction is executed, the value of MPIE will be stored to MIE.                                         |
  +-------------+-----------+-------------------------------------------------------------------------------------------------------------------------+
  | 6:4         | RO        | 0, Unimplemented.                                                                                                       |
  +-------------+-----------+-------------------------------------------------------------------------------------------------------------------------+
  | 3           | RW        | **MIE:** Machine Interrupt Enable                                                                                       |
  |             |           |                                                                                                                         |
  |             |           | If you want to enable interrupt handling in your exception handler,                                                     |
  |             |           | set the Interrupt Enable MIE to 1 inside your handler code.                                                             |
  +-------------+-----------+-------------------------------------------------------------------------------------------------------------------------+
  | 2:0         | RO        | 0, Unimplemented.                                                                                                       |
  +-------------+-----------+-------------------------------------------------------------------------------------------------------------------------+

.. only:: USER

  User Status (``ustatus``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x000

  Reset Value: 0x0000_0000

  Detailed:

  +-------------+-----------+-------------------------------------------------------------------------------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                                                                                         |
  +=============+===========+=========================================================================================================================+
  | 4           | RW        | **Previous User Interrupt Enable:** If user mode is enabled, when an exception is encountered, UPIE will be set to UIE. |
  |             |           | When the uret instruction is executed, the value of UPIE will be stored to UIE.                                         |
  +-------------+-----------+-------------------------------------------------------------------------------------------------------------------------+
  | 0           | RW        | **User Interrupt Enable:** If you want to enable user level interrupt handling in your exception handler,               |
  |             |           | set the Interrupt Enable UIE to 1 inside your handler code.                                                             |
  +-------------+-----------+-------------------------------------------------------------------------------------------------------------------------+

Machine Interrupt Enable register (``mie``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x304

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+------------------------------------------------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                                                          |
  +=============+===========+==========================================================================================+
  | 31:16       | RW        | Machine Fast Interrupt Enables                                                           |
  |             |           |                                                                                          |
  |             |           | Set bit x to enable interrupt irq_i[x] (x between 16 and 31).                            |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  | 15:12       | RO        | 0                                                                                        |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  | 11          | RW        | **MEIE:** Machine External Interrupt Enable                                              |
  |             |           |                                                                                          |
  |             |           | If set, irq_i[11] is enabled.                                                            |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  | 10:8        | RO        | 0                                                                                        |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  | 7           | RW        | **MTIE:** Machine Timer Interrupt Enable                                                 |
  |             |           |                                                                                          |
  |             |           | If set, irq_i[7] is enabled.                                                             |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  | 6:4         | RO        | 0                                                                                        |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  | 3           | RW        | **MSIE:** Machine Software Interrupt Enable                                              |
  |             |           |                                                                                          |
  |             |           | If set, irq_i[3] is enabled.                                                             |
  +-------------+-----------+------------------------------------------------------------------------------------------+
  | 2:0         | RO        | 0                                                                                        |
  +-------------+-----------+------------------------------------------------------------------------------------------+

.. _csr-mtvec:

Machine Trap-Vector Base Address (``mtvec``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x305

Reset Value: Defined

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+---------------------------------------------------------------------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                                                                               |
  +=============+===========+===============================================================================================================+
  | 31 : 8      |   RW      | BASE[31:8]                                                                                                    |
  |             |           |                                                                                                               |
  |             |           | The trap-handler base address, always aligned to 256 bytes.                                                   |
  +-------------+-----------+---------------------------------------------------------------------------------------------------------------+
  |  7 : 2      |   RO      | BASE[7:2]                                                                                                     |
  |             |           |                                                                                                               |
  |             |           | The trap-handler base address, always aligned to 256 bytes, i.e., mtvec[7:2] is always set to 0.              |
  +-------------+-----------+---------------------------------------------------------------------------------------------------------------+
  |  1          |   RO      | MODE[1]                                                                                                       |
  |             |           |                                                                                                               |
  |             |           | 0                                                                                                             |
  +-------------+-----------+---------------------------------------------------------------------------------------------------------------+
  |  0          |   RW      | MODE[0]                                                                                                       |
  |             |           |                                                                                                               |
  |             |           | 0 = Direct mode                                                                                               |
  |             |           |                                                                                                               |
  |             |           | 1 = Vectored mode.                                                                                            |
  +-------------+-----------+---------------------------------------------------------------------------------------------------------------+

The initial value of ``mtvec`` is equal to {**mtvec_addr_i[31:8]**, 6'b0, 2'b01}.

When an exception or an interrupt is encountered, the core jumps to the corresponding
handler using the content of the MTVEC[31:8] as base address. Only
8-byte aligned addresses are allowed. Both direct mode and vectored mode
are supported.

Machine Scratch (``mscratch``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x340

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+------------------------------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                                        |
  +=============+===========+========================================================================+
  | 31:0        | RW        | Scratch value                                                          |
  +-------------+-----------+------------------------------------------------------------------------+

Machine Exception PC (``mepc``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x341

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+------------------------------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                                        |
  +=============+===========+========================================================================+
  | 31:1        | RW        | **MEPC:** Machine Exception Program Counter                            |
  +-------------+-----------+------------------------------------------------------------------------+
  | 0           | R0        | 0                                                                      |
  +-------------+-----------+------------------------------------------------------------------------+

When an exception is encountered, the current program counter is saved
in MEPC, and the core jumps to the exception address. When a mret
instruction is executed, the value from MEPC replaces the current
program counter.

Machine Cause (``mcause``)
~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x342

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+----------------------------------------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                                                  |
  +=============+===========+==================================================================================+
  | 31          |   RW      | **Interrupt:** This bit is set when the exception was triggered by an interrupt. |
  +-------------+-----------+----------------------------------------------------------------------------------+
  | 30:5        |   RO (0)  | 0                                                                                |
  +-------------+-----------+----------------------------------------------------------------------------------+
  | 4:0         |   RW      | **Exception Code**   (See note below)                                            |
  +-------------+-----------+----------------------------------------------------------------------------------+

**NOTE**: software accesses to `mcause[4:0]` must be sensitive to the WLRL field specification of this CSR. For example,
when `mcause[31]` is set, writing 0x1 to `mcause[1]` (Supervisor software interrupt) will result in UNDEFINED behavior.


Machine Trap Value (``mtval``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x343

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+------------------------------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                                        |
  +=============+===========+========================================================================+
  | 31:0        | RO        | Writes are ignored; reads return 0.                                    |
  +-------------+-----------+------------------------------------------------------------------------+

Machine Interrupt Pending register (``mip``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x344

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+---------------------------------------------------------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                                                                   |
  +=============+===========+===================================================================================================+
  | 31:16       | RO        | Machine Fast Interrupts Pending                                                                   |
  |             |           |                                                                                                   |
  |             |           | If bit x is set, interrupt irq_i[x] is pending (x between 16 and 31).                             |
  +-------------+-----------+---------------------------------------------------------------------------------------------------+
  | 15:12       | RO        | 0                                                                                                 |
  +-------------+-----------+---------------------------------------------------------------------------------------------------+
  | 11          | RO        | **MEIP:** Machine External Interrupt Pending                                                      |
  |             |           |                                                                                                   |
  |             |           | If set, irq_i[11] is pending.                                                                     |
  +-------------+-----------+---------------------------------------------------------------------------------------------------+
  | 10:8        | RO        | 0                                                                                                 |
  +-------------+-----------+---------------------------------------------------------------------------------------------------+
  | 7           | RO        | **MTIP:** Machine Timer Interrupt Pending                                                         |
  |             |           |                                                                                                   |
  |             |           | If set, irq_i[7] is pending.                                                                      |
  +-------------+-----------+---------------------------------------------------------------------------------------------------+
  | 6:4         | RO        | 0                                                                                                 |
  +-------------+-----------+---------------------------------------------------------------------------------------------------+
  | 3           | RO        | **MSIP:** Machine Software Interrupt Pending                                                      |
  |             |           |                                                                                                   |
  |             |           | If set, irq_i[3] is pending.                                                                      |
  +-------------+-----------+---------------------------------------------------------------------------------------------------+
  | 2:0         | RO        | 0                                                                                                 |
  +-------------+-----------+---------------------------------------------------------------------------------------------------+

Trigger CSRs
::::::::::::

.. _csr-tselect:

Trigger Select register (``tselect``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7A0

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+----------------------------------------------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                                                        |
  +=============+===========+========================================================================================+
  | 31:0        | RO        | CV32E40P implements a single trigger, therefore this register will always read as zero.|
  +-------------+-----------+----------------------------------------------------------------------------------------+

Accessible in Debug Mode or M-Mode.

.. _csr-tdata1:

Trigger Data register 1 (``tdata1``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7A1

Reset Value: 0x2800_1040

Detailed:

Accessible in Debug Mode or M-Mode.
Since native triggers are not supported, writes to this register from M-Mode will be ignored.

.. note::

   CV32E40P only implements one type of trigger, Match Control. Most fields of this register will read as a fixed value to
   reflect the single mode that is supported, in particular, instruction address match as described in the Debug Specification
   0.13.2 section 5.2.2 & 5.2.9. The **type**, **dmode**, **hit**, **select**, **timing**, **sizelo**, **action**, **chain**,
   **match**, **m**, **s**, **u**,  **store** and  **load** bitfields of this CSR, which are marked as R/W in Debug Specification
   0.13.2, are therefore implemented as WARL bitfields (corresponding to how these bitfields will be specified in the forthcoming
   Debug Specification 0.14.0).

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-----------+----------+------------------------------------------------------------------+
  | **Bit #** | **Mode** | **Description**                                                  |
  +===========+==========+==================================================================+
  | 31:28     | RO (0x2) | **type:** 2 = Address/Data match trigger type.                   |
  +-----------+----------+------------------------------------------------------------------+
  | 27        | RO (0x1) | **dmode:** 1 = Only debug mode can write tdata registers         |
  +-----------+----------+------------------------------------------------------------------+
  | 26:21     | RO (0x0) | **maskmax:** 0 = Only exact matching supported.                  |
  +-----------+----------+------------------------------------------------------------------+
  | 20        | RO (0x0) | **hit:** 0 = Hit indication not supported.                       |
  +-----------+----------+------------------------------------------------------------------+
  | 19        | RO (0x0) | **select:** 0 = Only address matching is supported.              |
  +-----------+----------+------------------------------------------------------------------+
  | 18        | RO (0x0) | **timing:** 0 = Break before the instruction at the specified    |
  |           |          | address.                                                         |
  +-----------+----------+------------------------------------------------------------------+
  | 17:16     | RO (0x0) | **sizelo:** 0 = Match accesses of any size.                      |
  +-----------+----------+------------------------------------------------------------------+
  | 15:12     | RO (0x1) | **action:** 1 = Enter debug mode on match.                       |
  +-----------+----------+------------------------------------------------------------------+
  | 11        | RO (0x0) | **chain:** 0 = Chaining not supported.                           |
  +-----------+----------+------------------------------------------------------------------+
  | 10:7      | RO (0x0) | **match:** 0 = Match the whole address.                          |
  +-----------+----------+------------------------------------------------------------------+
  | 6         | RO (0x1) | **m:** 1 = Match in M-Mode.                                      |
  +-----------+----------+------------------------------------------------------------------+
  | 5         | RO (0x0) | zero.                                                            |
  +-----------+----------+------------------------------------------------------------------+
  | 4         | RO (0x0) | **s:** 0 = S-Mode not supported.                                 |
  +-----------+----------+------------------------------------------------------------------+
  | 3         | RO (0x0) | **u:** 0 = U-Mode not supported.                                 |
  +-----------+----------+------------------------------------------------------------------+
  | 2         | RW       | **execute:** Enable matching on instruction address.             |
  +-----------+----------+------------------------------------------------------------------+
  | 1         | RO (0x0) | **store:** 0 = Store address / data matching not supported.      |
  +-----------+----------+------------------------------------------------------------------+
  | 0         | RO (0x0) | **load:** 0 = Load address / data matching not supported.        |
  +-----------+----------+------------------------------------------------------------------+

.. _csr-tdata2:

Trigger Data register 2 (``tdata2``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7A2

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-----------+----------+------------------------------------------------------------------+
  | **Bit #** | **Mode** | **Description**                                                  |
  +===========+==========+==================================================================+
  | 31:0      | RW       | **data**                                                         |
  +-----------+----------+------------------------------------------------------------------+

Accessible in Debug Mode or M-Mode. Since native triggers are not supported, writes to this register from M-Mode will be ignored.
This register stores the instruction address to match against for a breakpoint trigger.

Trigger Data register 3 (``tdata3``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7A3

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-----------+----------+------------------------------------------------------------------+
  | **Bit #** | **Mode** | **Description**                                                  |
  +===========+==========+==================================================================+
  | 31:0      | RO       | 0                                                                |
  +-----------+----------+------------------------------------------------------------------+

Accessible in Debug Mode or M-Mode.
CV32E40P does not support the features requiring this register. Writes are ignored and reads will always return zero.

.. _csr-tinfo:

Trigger Info (``tinfo``)
~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7A4

Reset Value: 0x0000_0004

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-----------+----------+------------------------------------------------------------------+
  | **Bit #** | **Mode** | **Description**                                                  |
  +===========+==========+==================================================================+
  | 31:16     | RO       | 0                                                                |
  +-----------+----------+------------------------------------------------------------------+
  | 15:0      | RO (0x4) | **info**. Only type 2 is supported.                              |
  +-----------+----------+------------------------------------------------------------------+

The **info** field contains one bit for each possible `type` enumerated in
`tdata1`.  Bit N corresponds to type N.  If the bit is set, then that type is
supported by the currently selected trigger.  If the currently selected trigger
does not exist, this field contains 1.

Accessible in Debug Mode or M-Mode.

Machine Context register (``mcontext``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7A8

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-----------+----------+------------------------------------------------------------------+
  | **Bit #** | **Mode** | **Description**                                                  |
  +===========+==========+==================================================================+
  | 31:0      | RO       | 0                                                                |
  +-----------+----------+------------------------------------------------------------------+

Accessible in Debug Mode or M-Mode.
CV32E40P does not support the features requiring this register. Writes are ignored and
reads will always return zero.

.. only:: SUPERVISOR

  Supervisor Context register (``scontext``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x7AA

  Reset Value: 0x0000_0000

  Detailed:

  +-----------+----------+------------------------------------------------------------------+
  | **Bit #** | **Mode** | **Description**                                                  |
  +===========+==========+==================================================================+
  | 31:0      | RO       | 0                                                                |
  +-----------+----------+------------------------------------------------------------------+

  Accessible in Debug Mode or M-Mode.
  CV32E40P does not support the features requiring this register. Writes are ignored and
  reads will always return zero.

Debug CSRs
::::::::::

.. _csr-dcsr:

Debug Control and Status (``dcsr``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7B0

Reset Value: 0x4000_0003

.. note::

   The **ebreaks**, **ebreaku** and **prv** bitfields of this CSR are marked as R/W in Debug Specification 0.13.2. However,
   as CV32E40P only supports machine mode, these bitfields are implemented as WARL bitfields (corresponding to how these bitfields will
   be specified in the forthcoming Debug Specification 0.14.0).

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-----------+-----------+-------------------------------------------------------------------------------------------------+
  | **Bit #** | **Mode**  | **Description**                                                                                 |
  +===========+===========+=================================================================================================+
  | 31:28     | RO (0x4)  | **xdebugver:** returns 4 - External debug support exists as it is described in this document.   |
  +-----------+-----------+-------------------------------------------------------------------------------------------------+
  | 27:16     | RO (0x0)  | Reserved                                                                                        |
  +-----------+-----------+-------------------------------------------------------------------------------------------------+
  | 15        | RW        | **ebreakm**                                                                                     |
  +-----------+-----------+-------------------------------------------------------------------------------------------------+
  | 14        | RO (0x0)  | Reserved                                                                                        |
  +-----------+-----------+-------------------------------------------------------------------------------------------------+
  | 13        | RO (0x0)  | **ebreaks**. Always 0.                                                                          |
  +-----------+-----------+-------------------------------------------------------------------------------------------------+
  | 12        | RO (0x0)  | **ebreaku**. Always 0.                                                                          |
  +-----------+-----------+-------------------------------------------------------------------------------------------------+
  | 11        | RW        | **stepie**                                                                                      |
  +-----------+-----------+-------------------------------------------------------------------------------------------------+
  | 10        | RO (0x0)  | **stopcount**. Always 0.                                                                        |
  +-----------+-----------+-------------------------------------------------------------------------------------------------+
  | 9         | RO (0x0)  | **stoptime**. Always 0.                                                                         |
  +-----------+-----------+-------------------------------------------------------------------------------------------------+
  | 8:6       | RO        | **cause**                                                                                       |
  +-----------+-----------+-------------------------------------------------------------------------------------------------+
  | 5         | RO (0x0)  | Reserved                                                                                        |
  +-----------+-----------+-------------------------------------------------------------------------------------------------+
  | 4         | RO (0x0)  | **mprven**. Always 0.                                                                           |
  +-----------+-----------+-------------------------------------------------------------------------------------------------+
  | 3         | RO (0x0)  | **nmip**. Always 0.                                                                             |
  +-----------+-----------+-------------------------------------------------------------------------------------------------+
  | 2         | RW        | **step**                                                                                        |
  +-----------+-----------+-------------------------------------------------------------------------------------------------+
  | 1:0       | RO (0x3)  | **prv:** returns the current priviledge mode                                                    |
  +-----------+-----------+-------------------------------------------------------------------------------------------------+

.. _csr-dpc:

Debug PC (``dpc``)
~~~~~~~~~~~~~~~~~~

CSR Address: 0x7B1

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+-------------------------------------------------------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                                                                 |
  +=============+===========+=================================================================================================+
  | 31:1        | RO        | zero                                                                                            |
  +-------------+-----------+-------------------------------------------------------------------------------------------------+
  | 0           | RO        | DPC                                                                                             |
  +-------------+-----------+-------------------------------------------------------------------------------------------------+

When the core enters in Debug Mode, DPC contains the virtual address of
the next instruction to be executed.

Debug Scratch register 0/1 (``dscratch0/1``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x7B2/0x7B3

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+-------------------------------------------------------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                                                                 |
  +=============+===========+=================================================================================================+
  | 31:0        | RW        | DSCRATCH0/1                                                                                     |
  +-------------+-----------+-------------------------------------------------------------------------------------------------+

Performances counters
:::::::::::::::::::::

.. only:: USER

  Machine Counter Enable (``mcounteren``)
  ---------------------------------------

  CSR Address: 0x306

  Reset Value: 0x0000_0000

  Detailed:

  +-----------+----------+------------------------------------------------------------------+
  | **Bit #** | **Mode** | **Description**                                                  |
  +===========+==========+==================================================================+
  | 31:4      | RW       | Dependent on number of counters implemented in design parameter  |
  +-----------+----------+------------------------------------------------------------------+
  | 3         | RW       | **selectors:** hpmcounter3 enable for user mode                  |
  +-----------+----------+------------------------------------------------------------------+
  | 2         | RW       | instret enable for user mode                                     |
  +-----------+----------+------------------------------------------------------------------+
  | 1         | RO       | 0                                                                |
  +-----------+----------+------------------------------------------------------------------+
  | 0         | RW       | cycle enable for user mode                                       |
  +-----------+----------+------------------------------------------------------------------+

  Each bit in the machine counter-enable register allows the associated read-only
  unprivileged shadow performance register to be read from user mode. If the bit
  is clear an attempt to read the register in user mode will trigger an illegal
  instruction exception.

Machine Counter-Inhibit register (``mcountinhibit``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x320

Reset Value: 0x0000_000D

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-----------+----------+------------------------------------------------------------------+
  | **Bit #** | **Mode** | **Description**                                                  |
  +===========+==========+==================================================================+
  | 31:4      | RW       | Dependent on number of counters implemented in design parameter  |
  +-----------+----------+------------------------------------------------------------------+
  | 3         | RW       | **selectors:** mhpmcounter3 inhibit                              |
  +-----------+----------+------------------------------------------------------------------+
  | 2         | RW       | minstret inhibit                                                 |
  +-----------+----------+------------------------------------------------------------------+
  | 1         | RO       | 0                                                                |
  +-----------+----------+------------------------------------------------------------------+
  | 0         | RW       | mcycle inhibit                                                   |
  +-----------+----------+------------------------------------------------------------------+

The performance counter inhibit control register. The default value is to inihibit counters out of reset.
The bit returns a read value of 0 for non implemented counters. This reset value
shows the result using the default number of performance counters to be 1.

Machine Performance Monitoring Event Selector (``mhpmevent3 .. mhpmevent31``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x323 - 0x33F

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-----------+----------+------------------------------------------------------------------+
  | **Bit #** | **Mode** | **Description**                                                  |
  +===========+==========+==================================================================+
  | 31:16     | RO       | 0                                                                |
  +-----------+----------+------------------------------------------------------------------+
  | 15:0      | RW       | **selectors:** Each bit represent a unique event to count        |
  +-----------+----------+------------------------------------------------------------------+

The event selector fields are further described in Performance Counters section.
Non implemented counters always return a read value of 0.

Machine Cycle Counter (``mcycle``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xB00

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-----------+----------+------------------------------------------------------------------+
  | **Bit #** | **Mode** | **Description**                                                  |
  +===========+==========+==================================================================+
  | 31:0      | RW       | The lower 32 bits of the 64 bit machine mode cycle counter.      |
  +-----------+----------+------------------------------------------------------------------+


Machine Instructions-Retired Counter (``minstret``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xB02

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-----------+----------+---------------------------------------------------------------------------+
  | **Bit #** | **Mode** | **Description**                                                           |
  +===========+==========+===========================================================================+
  | 31:0      | RW       | The lower 32 bits of the 64 bit machine mode instruction retired counter. |
  +-----------+----------+---------------------------------------------------------------------------+


Machine Performance Monitoring Counter (``mhpmcounter3 .. mhpmcounter31``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xB03 - 0xB1F

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-----------+----------+------------------------------------------------------------------+
  | **Bit #** | **Mode** | **Description**                                                  |
  +===========+==========+==================================================================+
  | 31:0      | RW       | Machine performance-monitoring counter                           |
  +-----------+----------+------------------------------------------------------------------+

The lower 32 bits of the 64 bit machine performance-monitoring counter(s).
The number of machine performance-monitoring counters is determined by the parameter ``NUM_MHPMCOUNTERS`` with a range from 0 to 29 (default value of 1). Non implemented counters always return a read value of 0.

Upper 32 bits Machine Cycle Counter (``mcycleh``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xB80

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-----------+----------+------------------------------------------------------------------+
  | **Bit #** | **Mode** | **Description**                                                  |
  +===========+==========+==================================================================+
  | 31:0      | RW       | The upper 32 bits of the 64 bit machine mode cycle counter.      |
  +-----------+----------+------------------------------------------------------------------+


Upper 32 bits Machine Instructions-Retired Counter (``minstreth``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xB82

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-----------+----------+---------------------------------------------------------------------------+
  | **Bit #** | **Mode** | **Description**                                                           |
  +===========+==========+===========================================================================+
  | 31:0      | RW       | The upper 32 bits of the 64 bit machine mode instruction retired counter. |
  +-----------+----------+---------------------------------------------------------------------------+


Upper 32 bits Machine Performance Monitoring Counter (``mhpmcounter3h .. mhpmcounter31h``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xB83 - 0xB9F

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-----------+----------+------------------------------------------------------------------+
  | **Bit #** | **Mode** | **Description**                                                  |
  +===========+==========+==================================================================+
  | 31:0      | RW       | Machine performance-monitoring counter                           |
  +-----------+----------+------------------------------------------------------------------+

The upper 32 bits of the 64 bit machine performance-monitoring counter(s).
The number of machine performance-monitoring counters is determined by the parameter ``NUM_MHPMCOUNTERS`` with a range from 0 to 29 (default value of 1). Non implemented counters always return a read value of 0.

Cycle Counter (``cycle``)
~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xC00

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-----------+----------+------------------------------------------------------------------+
  | **Bit #** | **Mode** | **Description**                                                  |
  +===========+==========+==================================================================+
  | 31:0      | RO       | 0                                                                |
  +-----------+----------+------------------------------------------------------------------+

Read-only unprivileged shadow of the lower 32 bits of the 64 bit machine mode cycle counter.

Instructions-Retired Counter (``instret``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xC02

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-----------+----------+------------------------------------------------------------------+
  | **Bit #** | **Mode** | **Description**                                                  |
  +===========+==========+==================================================================+
  | 31:0      | RO       | 0                                                                |
  +-----------+----------+------------------------------------------------------------------+

Read-only unprivileged shadow of the lower 32 bits of the 64 bit machine mode instruction retired counter.

Performance Monitoring Counter (``hpmcounter3 .. hpmcounter31``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xC03 - 0xC1F

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-----------+----------+------------------------------------------------------------------+
  | **Bit #** | **Mode** | **Description**                                                  |
  +===========+==========+==================================================================+
  | 31:0      | RO       | 0                                                                |
  +-----------+----------+------------------------------------------------------------------+

Read-only unprivileged shadow of the lower 32 bits of the 64 bit machine mode
performance counter. Non implemented counters always return a read value of 0.

Upper 32 bits Cycle Counter (``cycleh``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xC80

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-----------+----------+------------------------------------------------------------------+
  | **Bit #** | **Mode** | **Description**                                                  |
  +===========+==========+==================================================================+
  | 31:0      | RO       | 0                                                                |
  +-----------+----------+------------------------------------------------------------------+

Read-only unprivileged shadow of the upper 32 bits of the 64 bit machine mode cycle counter.

Upper 32 bits Instructions-Retired Counter (``instreth``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xC82

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-----------+----------+------------------------------------------------------------------+
  | **Bit #** | **Mode** | **Description**                                                  |
  +===========+==========+==================================================================+
  | 31:0      | RO       | 0                                                                |
  +-----------+----------+------------------------------------------------------------------+

Read-only unprivileged shadow of the upper 32 bits of the 64 bit machine mode instruction retired counter.

Upper 32 bits Performance Monitoring Counter (``hpmcounter3h .. hpmcounter31h``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xC83 - 0xC9F

Reset Value: 0x0000_0000

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-----------+----------+------------------------------------------------------------------+
  | **Bit #** | **Mode** | **Description**                                                  |
  +===========+==========+==================================================================+
  | 31:0      | RO       | 0                                                                |
  +-----------+----------+------------------------------------------------------------------+

Read-only unprivileged shadow of the upper 32 bits of the 64 bit machine mode
performance counter. Non implemented counters always return a read value of 0.

ID CSRs
:::::::

Machine ISA (``misa``)
~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0x301

Reset Value: defined

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+------------+------------------------------------------------------------------------+
  | **Bit #**   | **Mode**   | **Description**                                                        |
  +=============+============+========================================================================+
  | 31:30       | RO   (0x1) | **MXL** (Machine XLEN)                                                 |
  +-------------+------------+------------------------------------------------------------------------+
  | 29:26       | RO   (0x0) | (Reserved)                                                             |
  +-------------+------------+------------------------------------------------------------------------+
  | 25          | RO   (0x0) | **Z** (Reserved)                                                       |
  +-------------+------------+------------------------------------------------------------------------+
  | 24          | RO   (0x0) | **Y** (Reserved)                                                       |
  +-------------+------------+------------------------------------------------------------------------+
  | 23          | RO         | **X** (Non-standard extensions present)                                |
  +-------------+------------+------------------------------------------------------------------------+
  | 22          | RO   (0x0) | **W** (Reserved)                                                       |
  +-------------+------------+------------------------------------------------------------------------+
  | 21          | RO   (0x0) | **V** (Tentatively reserved for Vector extension)                      |
  +-------------+------------+------------------------------------------------------------------------+
  | 20          | RO   (0x0) | **U** (User mode implemented)                                          |
  +-------------+------------+------------------------------------------------------------------------+
  | 19          | RO   (0x0) | **T** (Tentatively reserved for Transactional Memory extension)        |
  +-------------+------------+------------------------------------------------------------------------+
  | 18          | RO   (0x0) | **S** (Supervisor mode implemented)                                    |
  +-------------+------------+------------------------------------------------------------------------+
  | 17          | RO   (0x0) | **R** (Reserved)                                                       |
  +-------------+------------+------------------------------------------------------------------------+
  | 16          | RO   (0x0) | **Q** (Quad-precision floating-point extension)                        |
  +-------------+------------+------------------------------------------------------------------------+
  | 15          | RO   (0x0) | **P** (Tentatively reserved for Packed-SIMD extension)                 |
  +-------------+------------+------------------------------------------------------------------------+
  | 14          | RO   (0x0) | **O** (Reserved)                                                       |
  +-------------+------------+------------------------------------------------------------------------+
  | 13          | RO   (0x0) | **N** (User-level interrupts supported)                                |
  +-------------+------------+------------------------------------------------------------------------+
  | 12          | RO   (0x1) | **M** (Integer Multiply/Divide extension)                              |
  +-------------+------------+------------------------------------------------------------------------+
  | 11          | RO   (0x0) | **L** (Tentatively reserved for Decimal Floating-Point extension)      |
  +-------------+------------+------------------------------------------------------------------------+
  | 10          | RO   (0x0) | **K** (Reserved)                                                       |
  +-------------+------------+------------------------------------------------------------------------+
  | 9           | RO   (0x0) | **J** (Tentatively reserved for Dynamically Translated Languages       |
  |             |            | extension)                                                             |
  +-------------+------------+------------------------------------------------------------------------+
  | 8           | RO   (0x1) | **I** (RV32I/64I/128I base ISA)                                        |
  +-------------+------------+------------------------------------------------------------------------+
  | 7           | RO   (0x0) | **H** (Hypervisor extension)                                           |
  +-------------+------------+------------------------------------------------------------------------+
  | 6           | RO   (0x0) | **G** (Additional standard extensions present)                         |
  +-------------+------------+------------------------------------------------------------------------+
  | 5           | RO         | **F** (Single-precision floating-point extension)                      |
  +-------------+------------+------------------------------------------------------------------------+
  | 4           | RO   (0x0) | **E** (RV32E base ISA)                                                 |
  +-------------+------------+------------------------------------------------------------------------+
  | 3           | RO   (0x0) | **D** (Double-precision floating-point extension)                      |
  +-------------+------------+------------------------------------------------------------------------+
  | 2           | RO   (0x1) | **C** (Compressed extension)                                           |
  +-------------+------------+------------------------------------------------------------------------+
  | 1           | RO   (0x0) | **B** (Tentatively reserved for Bit-Manipulation extension)            |
  +-------------+------------+------------------------------------------------------------------------+
  | 0           | RO   (0x0) | **A** (Atomic extension)                                               |
  +-------------+------------+------------------------------------------------------------------------+

Writes are ignored and all bitfields in the ``misa`` CSR area read as 0 except for the following:

* **C** = 1
* **F** = 1 if ``FPU`` = 1 and ``ZFINX`` = 0
* **I** = 1
* **M** = 1
* **X** = 1 if ``COREV_PULP`` = 1 or ``COREV_CLUSTER`` = 1
* **MXL** = 1 (i.e. XLEN = 32)

Machine Vendor ID (``mvendorid``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xF11

Reset Value: 0x0000_0602

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+------------------------------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                                        |
  +=============+===========+========================================================================+
  | 31:7        | RO        | 0xC. Number of continuation codes in JEDEC manufacturer ID.            |
  +-------------+-----------+------------------------------------------------------------------------+
  | 6:0         | RO        | 0x2. Final byte of JEDEC manufacturer ID, discarding the parity bit.   |
  +-------------+-----------+------------------------------------------------------------------------+

The ``mvendorid`` encodes the OpenHW JEDEC Manufacturer ID, which is 2 decimal (bank 13).

Machine Architecture ID (``marchid``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xF12

Reset Value: 0x0000_0004

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+------------------------------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                                        |
  +=============+===========+========================================================================+
  | 31:0        | RO        | Machine Architecture ID of CV32E40P is 4                               |
  +-------------+-----------+------------------------------------------------------------------------+

Machine Implementation ID (``mimpid``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xF13

Reset Value: Defined

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+-------------------------------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                                         |
  +=============+===========+=========================================================================+
  | 31 : 1      | RO        | 0                                                                       |
  +-------------+-----------+-------------------------------------------------------------------------+
  | 0           | RO        | 1 if ``FPU`` = 1 or ``COREV_PULP`` = 1 or ``COREV_CLUSTER`` = 1 else 0. |
  +-------------+-----------+-------------------------------------------------------------------------+

.. _csr-mhartid:

Hardware Thread ID (``mhartid``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xF14

Reset Value: Defined

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+----------------------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                                |
  +=============+===========+================================================================+
  | 31:0        | RO        | Hardware Thread ID **hart_id_i**, see  :ref:`core-integration` |
  +-------------+-----------+----------------------------------------------------------------+

.. Comment: no attempt has been made to update these "USER" CSR descriptions
.. only:: USER

  User Trap-Vector Base Address (``utvec``)
  -----------------------------------------

  CSR Address: 0x005

  +-------------+-----------+---------------------------------------------------------------------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                                                                               |
  +=============+===========+===============================================================================================================+
  | 31 : 2      |   RW      | BASE: The trap-handler base address, always aligned to 256 bytes, i.e., utvec[7:2] is always set to 0.        |
  +-------------+-----------+---------------------------------------------------------------------------------------------------------------+
  |  1          |   RO      | MODE[1]: Always 0                                                                                             |
  +-------------+-----------+---------------------------------------------------------------------------------------------------------------+
  |  0          |   RW      | MODE[0]: 0 = direct mode, 1 = vectored mode.                                                                  |
  +-------------+-----------+---------------------------------------------------------------------------------------------------------------+

  When an exception is encountered in user-mode, the core jumps to the
  corresponding handler using the content of the UTVEC[31:8] as base
  address. Only 8-byte aligned addresses are allowed. Both direct mode
  and vectored mode are supported.

  User Exception PC (``uepc``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x041

  Reset Value: 0x0000_0000

  Detailed:

  +------+-------+
  | 31   | 30: 0 |
  +======+=======+
  | UEPC |       |
  +------+-------+

  When an exception is encountered in user mode, the current program
  counter is saved in UEPC, and the core jumps to the exception address.
  When a uret instruction is executed, the value from UEPC replaces the
  current program counter.

  User Cause (``ucause``)
  ~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x042

  Reset Value: 0x0000_0000

  Detailed:

  +-------------+-----------+------------------------------------------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                                                    |
  +=============+===========+====================================================================================+
  | 31          |   RW      | **Interrupt:** This bit is set when the exception was triggered by an interrupt.   |
  +-------------+-----------+------------------------------------------------------------------------------------+
  | 30:5        |   RO (0)  | Always 0                                                                           |
  +-------------+-----------+------------------------------------------------------------------------------------+
  | 4:0         |   RW      | **Exception Code**   (See note below)                                              |
  +-------------+-----------+------------------------------------------------------------------------------------+

  **NOTE**: software accesses to `ucause[4:0]` must be sensitive to the WLRL field specification of this CSR.  For example,
  when `ucause[31]` is set, writing 0x1 to `ucause[1]` (Supervisor software interrupt) will result in UNDEFINED behavior.


.. only:: PMP

  PMP Configuration (``pmpcfgx``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x3A{0,1,2,3}

  Reset Value: 0x0000_0000

  Detailed:

  +----------+
  | 31 : 0   |
  +==========+
  | PMPCFGx  |
  +----------+

  If the PMP is enabled, these four registers contain the configuration of
  the PMP as specified by the official privileged spec 1.10.

  PMP Address (``pmpaddrx``)
  ~~~~~~~~~~~~~~~~~~~~~~~~~~

  CSR Address: 0x3B{0x0, 0x1, …. 0xF}

  Reset Value: 0x0000_0000

  Detailed:

  +----------+
  | 31 : 0   |
  +==========+
  | PMPADDRx |
  +----------+

  If the PMP is enabled, these sixteen registers contain the addresses of
  the PMP as specified by the official privileged spec 1.10.

Non-RISC-V CSRs
:::::::::::::::

.. _csr-uhartid:

User Hardware Thread ID (``uhartid``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xCD0 (only present if ``COREV_PULP`` = 1)

Reset Value: Defined

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+----------------------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                                |
  +=============+===========+================================================================+
  | 31:0        | RO        | Hardware Thread ID **hart_id_i**, see  :ref:`core-integration` |
  +-------------+-----------+----------------------------------------------------------------+

Similar to ``mhartid`` the ``uhartid`` provides the Hardware Thread ID. It differs from ``mhartid`` only in the required privilege level.
On CV32E40P, as it is a machine mode only implementation, this difference is not noticeable.

Privilege Level (``privlv``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xCD1 (only present if ``COREV_PULP`` = 1)

Reset Value: 0x0000_0003

Detailed:

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+--------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                  |
  +=============+===========+==================================================+
  | 31:2        | RO        | Reads as 0.                                      |
  +-------------+-----------+--------------------------------------------------+
  | 1:0         | RO        | Current Privilege Level                          |
  |             |           |                                                  |
  |             |           | 00 = User                                        |
  |             |           |                                                  |
  |             |           | 01 = Supervisor                                  |
  |             |           |                                                  |
  |             |           | 10 = Hypervisor                                  |
  |             |           |                                                  |
  |             |           | 11 = Machine                                     |
  |             |           |                                                  |
  |             |           | CV32E40P only supports Machine mode.             |
  +-------------+-----------+--------------------------------------------------+

.. _csr-zfinx:

ZFINX ISA (``zfinx``)
~~~~~~~~~~~~~~~~~~~~~

CSR Address: 0xCD2 (only present if ``COREV_PULP`` = 1 & (``FPU`` = 0 | (``FPU`` = 1 & ``ZFINX`` = 1)) )

Reset Value: Defined

.. table::
  :widths: 15 15 70
  :class: no-scrollbar-table

  +-------------+-----------+---------------------------------------------------+
  | **Bit #**   | **Mode**  | **Description**                                   |
  +=============+===========+===================================================+
  | 31:1        | RO        | 0                                                 |
  +-------------+-----------+---------------------------------------------------+
  | 0           | RO        | 1 if ``FPU`` = 1 and ``ZFINX`` = 1 else 0.        |
  +-------------+-----------+---------------------------------------------------+
