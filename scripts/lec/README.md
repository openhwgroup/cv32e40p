# Logic Equivalence Checking (LEC)

This folder contains a LEC script that runs on both 
Synopsys Formality and Cadence Design Systems Conformal.

This script allows to catch non-logical equivalent changes on the RTL which are forbidden
on the verified paramter set.

Please have a look at: https://cv32e40p.readthedocs.io/en/latest/core_versions/

The `cv32e40p_v1.0.0` tag refers to the frozen RTL. The RTL has been verified and frozen on a given value of the input parameter of the design. Unless a bug is found, it is forbidden to change the RTL
in a non-logical equivalent manner for PPA optimizations of any other change.
Instead, it is possible to change the RTL on a different value of the parameter set, which has not been verified yet.
For example, it is possible to change the RTL design when the `FPU` parameter is set to 1 as this configuration has not been verified yet. However, the design must be logically equivalent when the parameter is set back to 0.
It is possible to change the `apu` interface and the `pulp_clock_en_i` signal on the frozen parameter set as these
signals are not used when the parameter `FPU` and `PULP_CLUSTER` are set to 0, respectively.

The current scripts have been tried on Synopsys Formality `2021.06-SP5` and Cadence Design Systems Conformal `20.20` on a 64 bit executable.

### Running the script

From a bash shell, please execute:

```
./lec.sh synopsys
```
 or

```
./lec.sh cadence
```

to use one of the tools. synopsys is used by default if no tool is specified,.

Use `sh ./les.sh {synopsys, cadence}` if you run it from a tcsh shell.

The script clones the `cv32e40p_v1.0.0` tag of the core as a golden reference, and uses the current repository's `rtl` as revised version.

If you want to use another golden reference rtl, Set the `GOLDEN_RTL` enviromental variable to the new rtl before calling the `lec.sh` script.

```
export GOLDEN_RTL=YOUR_GOLDEN_CORE_RTL_PATH
```
or 

```
setenv GOLDEN_RTL  YOUR_GOLDEN_CORE_RTL_PATH
```
If the script succeeds, it returns 0, otherwise -1.

The `check_lec.tcl` scripts in the tool specific folders are executed on the tools to perform `RTL to RTL` logic equivalence checking.
