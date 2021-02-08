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

Core Versions and RTL Freeze Rules
==================================

The CV32E40P is defined by the ``marchid`` and ``mimpid`` tuple.
The tuple identify which sets of parameters have been verified
by OpenHW Group, and once RTL Freeze is achieved, no further
non-logically equivalent changes are allowed on that set of parameters.

The RTL Freeze version of the core is indentified by a GitHub
tag with the format cv32e40p_vMAJOR.MINOR.PATCH (e.g. cv32e40p_v1.0.0).
In addition, the release date is reported in the documentation.

What happens after RTL Freeze?
------------------------------

A bug is found
^^^^^^^^^^^^^^

If a bug is found that affect the already frozen parameter set,
the RTL changes required to fix such bug are non-logically equivalent by definition.
Therefore, the RTL changes are applied only on a different  ``mimpid``
value and the bug and the fix must be documented.
These changes are visible by software as the ``mimpid`` has a different value.
Every bug or set of bugs found must be followed by another RTL Freeze release and a new GitHub tag.

RTL changes on non-verified yet parameters
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If changes affecting the core on a non-frozen parameter set are required,
as for example, to fix bugs found in the communication to the FPU (e.g., affecting the core only if ``FPU=1``),
or to change the ISA Extensions decoding of PULP instructions (e.g., affecting the core only if ``PULP_XPULP=1``),
then such changes must remain logically equivalent for the already frozen set of parameters (except for the required mimpid update), and they must be applied on a different ``mimpid`` value. They can be non-logically equivalent to a non-frozen set of parameters.
These changes are visible by software as the ``mimpid`` has a different value.
Once the new set of parameters is verified and achieved the sign-off for RTL freeze,
a new GitHub tag and version of the core is released.

PPA optimizations and new features
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Non-logically equivalent PPA optimizations and new features are not allowed on a given set
of RTL frozen parameters (e.g., a faster divider).
If PPA optimizations are logically-equivalent instead, they can be applied without
changing the ``mimpid`` value (as such changes are not visible in software).
However, a new GitHub tag should be release and changes documented.

:numref:`rtl_freeze_rules` shows the aforementioned rules.

.. figure:: ../images/rtl_freeze_rules.png
   :name: rtl_freeze_rules
   :align: center
   :alt:

   Versions control of CV32E40P


Released core versions
----------------------

The verified parameter sets of the core, their implementation version, GitHub tags,
and dates are reported here.

``mimpid=0``
------------

The ``mimpid=0`` refers to the CV32E40P core verified with the following parameters:

+---------------------------+-------+
| Name                      | Value |
+===========================+=======+
| ``FPU``                   |   0   |
+---------------------------+-------+
| ``NUM_MHPMCOUNTERS``      |   1   |
+---------------------------+-------+
| ``PULP_CLUSTER``          |   0   |
+---------------------------+-------+
| ``PULP_XPULP``            |   0   |
+---------------------------+-------+
| ``PULP_ZFINX``            |   0   |
+---------------------------+-------+

Following, all the GitHub tags related to ``mimpid=0``.

+--------------------+-------------------+------------+--------------------+---------+
| Git Tag            | Tagged By         | Date       | Reason for Release | Comment |
+====================+===================+============+====================+=========+
| cv32e40p_v1.0.0    | Arjan Bink        | 2020-12-10 | RTL Freeze         |         |
+--------------------+-------------------+------------+--------------------+---------+

The list of open (waived) issues at the time of applying the cv32e40p_v1.0.0 tag can be found at:

* https://github.com/openhwgroup/core-v-docs/blob/master/program/milestones/CV32E40P/RTL_Freeze_v1.0.0/Design_openissues.md
* https://github.com/openhwgroup/core-v-docs/blob/master/program/milestones/CV32E40P/RTL_Freeze_v1.0.0/Verification_openissues.md
* https://github.com/openhwgroup/core-v-docs/blob/master/program/milestones/CV32E40P/RTL_Freeze_v1.0.0/Documentation_openissues.md
