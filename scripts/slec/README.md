# Sequential Logic Equivalence Checking (SLEC)

This folder contains a SLEC script that runs:

- LEC: Synopsys Formality and Cadence Design Systems Conformal.
- SEC: Siemens SLEC App

Please have a look at: https://cv32e40p.readthedocs.io/en/latest/core_versions/

The `cv32e40p_v1.0.0` tag refers to the frozen RTL. The RTL has been verified
and frozen on a given value of the input parameter of the design. Unless a bug
is found, it is forbidden to change the RTL in a non-logical equivalent manner
for PPA optimizations of any other change.
Instead, it is possible to change the RTL on a different value of the parameter
set, which has not been verified yet.
For example, it is possible to change the RTL design when the `FPU` parameter is
set to 1 as this configuration has not been verified yet. However, the design
must be logically equivalent when the parameter is set back to 0.
It is possible to change the `apu` interface and the `pulp_clock_en_i` signal on
the frozen parameter set as these signals are not used when the parameter `FPU`
and `PULP_CLUSTER` are set to 0, respectively.

The current scripts have been tried on Synopsys Formality `2021.06-SP5` ,
Cadence Design Systems Conformal `20.20` and Siemens SLEC App `2023.4`.

### Running the script

From a bash shell using LEC, please execute:

```
./run.sh -t synopsys -p lec
```
 or

 ```
 ./run.sh -t cadence -p lec
 ```

 From a bash  shell to use SEC, please execute:
 ```
 ./run.sh -t siemens -p sec
 ```

 By default `cv32e40p_core` is used as a top module, if you want to use
 another one set the `TOP_MODULE` environment variable.

 The script clones the `cv32e40p_v1.0.0` tag of the core as a golden reference,
 and uses the current repository's `rtl` as revised version.

 If you want to use another golden reference RTL, set the `GOLDEN_RTL`
 environmental variable to the new RTL before calling the `run.sh` script.

 ```
 export GOLDEN_RTL=YOUR_GOLDEN_CORE_RTL_PATH
 ```
 or

 ```
 setenv GOLDEN_RTL  YOUR_GOLDEN_CORE_RTL_PATH
 ```

### Additional improvements for v2

To be able to make LEC checks between v2 versions, the scripts have been augmented with additional optional switches:
* for RTL version                 : -v v1 or v2
* for PULP instructions selection : -x 0 or 1
* for FPU instructions selection  : -f 0 or 1
* for ZFINX selection             : -z 0 or 1

When those options are not used, present behavior is happenning, meaning verifying local RTL files with `cv32e40p_v1.0.0` tag.
When v2 option is selected, `cv32e40p_top` is used as a top module, including both `cv32e40p_core` and `CVFPU`.
CAUTION : Right now dev branch is cloned as a golden reference when v2 version is used. It will have to be changed to `cv32e40p_v2.0.0` tag after CV32E40Pv2 RTL freeze.

From a bash shell using LEC, please execute:

```
./run.sh -t synopsys -p lec -v v2 -x 1 -f 1
```

