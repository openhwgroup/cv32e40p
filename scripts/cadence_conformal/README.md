# Logic Equivalence Checking (LEC)

This folder contains a LEC script that runs on 
Cadence Design Systems CONFORMAL.

The current scripts have been tried on version 20.10 on a 64 bit executable.

The `cv32e40p_lec_cmp.csh` runs on C-shell.

Before executing it, please define the GOLDEN_RTL and REVISED_RTL 
paths as enviromental variables.


```
setenv GOLDEN_RTL=YOUR_GOLDEN_CORE_RTL_PATH
setenv REVISED_RTL=YOUR_REVISED_CORE_RTL_PATH
```

Then, execute the `cv32e40p_lec_cmp.csh` script.
It returns 0 on success (i.e. the designs are logically equivalent), otherwise -1.

The `cv32e40p_lec_conformal.sh` is executed on the Cadence Conformal tool and performs RTL to RTL logic equivalence checking.



