# Logic Equivalence Checking (LEC)

This folder contains a LEC script that runs on
Cadence Design Systems CONFORMAL.

This script allows to catch non-logical equivalent changes on the RTL which are forbidden
on the verified paramter set.

Please have a look at: https://cv32e40p.readthedocs.io/en/latest/core_versions/

The `cv32e40p_v1.0.0` tag refers to the frozen RTL. The RTL has been verified and frozen on a given value of the input parameter of the design. Unless a bug is found, it is forbidden to change the RTL
in a non-logical equivalent manner for PPA optimizations of any other change.
Instead, it is possible to change the RTL on a different value of the parameter set, which has not been verified yet.
For example, it is possible to change the RTL design when the `FPU` parameter is set to 1 as this configuration has not been verified yet. However, the design must be logically equivalent when the parameter is set back to 0.
It is possible to change the `apu` interface and the `pulp_clock_en_i` signal on the frozen parameter set as these
signals are not used when the parameter `FPU` and `PULP_CLUSTER` are set to 0, respectively.

Please, always refer to the `cv32e40p_v1.0.0` tag for the `GOLDEN_RTL model`.

The current scripts have been tried on version 20.10 on a 64 bit executable.

The `cv32e40p_lec_cmp.csh` runs on C-shell.

Before executing it, please define the GOLDEN_RTL and REVISED_RTL
paths as enviromental variables.


```
setenv GOLDEN_RTL  YOUR_GOLDEN_CORE_RTL_PATH
setenv REVISED_RTL YOUR_REVISED_CORE_RTL_PATH
```

Then, execute the `cv32e40p_lec_cmp.csh` script.
It returns 0 on success (i.e. the designs are logically equivalent), otherwise -1.

The `cv32e40p_lec_conformal.sh` is executed on the Cadence Conformal tool and performs RTL to RTL logic equivalence checking.



