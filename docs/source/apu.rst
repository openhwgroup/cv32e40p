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

.. _apu:

Auxiliary Processing Unit (APU)
===============================

Auxiliary Processing Unit Interface
-----------------------------------

:numref:`Auxiliary Processing Unit interface signals` describes the signals of the Auxiliary Processing Unit interface.

.. table:: Auxiliary Processing Unit interface signals
  :name: Auxiliary Processing Unit interface signals

  +---------------------------------+---------------+------------------------------------------------------------------------------------------------------------------------------+
  | **Signal**                      | **Direction** | **Description**                                                                                                              |
  +=================================+===============+==============================================================================================================================+
  | ``apu_req_o``                   | output        | Request valid, will stay high until ``apu_gnt_i`` is high for one cycle                                                      |
  +---------------------------------+---------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``apu_gnt_i``                   | input         | The other side accepted the request.  ``apu_operands_o``, ``apu_op_o``, ``apu_flags_o`` may change in the next cycle.        |
  +---------------------------------+---------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``apu_operands_o[2:0][31:0]``   | output        | APU's operands                                                                                                               |
  +---------------------------------+---------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``apu_op_o[5:0]``               | output        | APU's operation                                                                                                              |
  +---------------------------------+---------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``apu_flags_o[14:0]``           | output        | APU's flags                                                                                                                  |
  +---------------------------------+---------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``apu_rvalid_i``                | input         | ``apu_result_i`` holds valid data when ``apu_valid_i`` is high. This signal will be high for exactly one cycle per request   |
  +---------------------------------+---------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``apu_result_i[31:0]``          | input         | APU's result                                                                                                                 |
  +---------------------------------+---------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``apu_flags_i[4:0]``            | input         | APU's flag result                                                                                                            |
  +---------------------------------+---------------+------------------------------------------------------------------------------------------------------------------------------+


Protocol
--------

The apu bus interface is derived from to the OBI (Open Bus Interface) protocol.
See https://github.com/openhwgroup/core-v-docs/blob/master/cores/cv32e40p/OBI-v1.0.pdf
for details about the protocol.
The CV32E40P apu interface uses the ``apu_operands_o``, ``apu_op_o``, and ``apu_flags_o`` as the address signal during the Address phase, indicating its validity with the ``apu_req_o`` signal. It uses the ``apu_result_i`` and ``apu_flags_i`` as the rdata of the response phase. It does not implement the OBI signals: we, be, wdata, auser, wuser, aid,
rready, err, ruser, rid. These signals can be thought of as being tied off as
specified in the OBI specification.
The CV32E40P apu interface can cause up to two outstanding transactions.

Connection with the FPU
-----------------------

The CV32E40P sends FP operands over the ``apu_operands_o`` bus; the decoded RV32F operation as ADD, SUB, MUL, etc through the ``apu_op_o`` bus; the cast, destination and source formats as well as rounding mode through the ``apu_flags_o`` bus. The respose is the FPU result and relative output flags as Overflow, Underflow, etc.


APU Tracer
----------

The module ``cv32e40p_apu_tracer`` can be used to create a log of the APU interface.
It is a behavioral, non-synthesizable, module instantiated in the example testbench that is provided for
the ``cv32e40p_core``. It can be enabled during simulation by defining **CV32E40P_APU_TRACE**.

Output file
-----------

The APU trace is written to a log file which is named ``apu_trace_core_<HARTID>.log``, with ``<HARTID>`` being
the 32 digit hart ID of the core being traced.

Trace output format
-------------------

The trace output is in tab-separated columns.

1. **Time**: The current simulation time.
2. **Register**: The register file write address.
3. **Result**: The register file write data.
