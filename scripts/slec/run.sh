#!/bin/bash

# Copyright 2021 OpenHW Group
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://solderpad.org/licenses/
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

if [[ -z "${GOLDEN_RTL}" ]]; then
  echo "The env variable GOLDEN_RTL is empty."
  echo "Cloning Golden Design...."
  sh clone_reference.sh
  export GOLDEN_RTL=$(pwd)/golden_reference_design/cv32e40p/rtl
else
  echo "Using ${GOLDEN_RTL} as reference design"
fi

REVISED_RTL=$(pwd)/../../rtl


var_golden_rtl=$(awk '{ if ($0 ~ "sv" && $0 !~ "incdir" && $0 !~ "wrapper" && $0 !~ "tracer") print $0 }' $GOLDEN_RTL/../cv32e40p_manifest.flist | awk -v rtlpath=$GOLDEN_RTL -F "/" '{$1=rtlpath} OFS="/"')

var_revised_rtl=$(awk '{ if ($0 ~ "sv" && $0 !~ "incdir" && $0 !~ "wrapper" && $0 !~ "_top" && $0 !~ "tracer") print $0 }' $REVISED_RTL/../cv32e40p_manifest.flist | awk -v rtlpath=$REVISED_RTL -F "/" '{$1=rtlpath} OFS="/"')

echo $var_golden_rtl > golden.src
echo $var_revised_rtl > revised.src

if [[ $# -gt 0 ]]; then 
    if [[ $1 == "cadence" ]]; then
        echo "Using Cadence Conformal"
        if [[  -d ./cadence_conformal/reports ]]; then
            rm -rf ./cadence_conformal/reports
            mkdir ./cadence_conformal/reports
        else
            mkdir ./cadence_conformal/reports
        fi
    else
        echo "Using Synopsys Formality"
        if [[  -d ./synopsys_formality/reports ]]; then
            rm -rf ./synopsys_formality/reports
            mkdir ./synopsys_formality/reports
        else
            mkdir ./synopsys_formality/reports
        fi
    fi
else
    echo "No tool specified...."
    echo "Using Synopsys Formality"
    if [[  -d ./synopsys_formality/reports ]]; then
        rm -rf ./synopsys_formality/reports
        mkdir ./synopsys_formality/reports
    else
        mkdir ./synopsys_formality/reports
    fi
fi

if [[ $1 == "cadence" ]]; then
    echo "Running Cadence Conformal"
    cd ./cadence_conformal
    lec -Dofile check_lec.tcl -TclMode -LOGfile cv32e40p_lec_log.log -NoGUI -xl
    if [ -f "./reports/result.rpt" ]; then
        NonLec=$(awk '{ if ($0 ~ "Hierarchical compare : Equivalent") print "0"}' ./reports/result.rpt)
    else
        echo "FATAL: could not find reports..."
        NonLec="-1"
    fi
    cd ../
else
    echo "Running Synopsys Formality"
    cd ./synopsys_formality
    fm_shell -f check_lec.tcl |& tee cv32e40p_lec_log.log
    if [ -f "./reports/verify.rpt" ]; then
        NonLec=$(awk '{ if ($0 ~ "Verification SUCCEEDED") print "0"}' ./reports/verify.rpt)
    else
        echo "FATAL: could not find reports..."
        NonLec="-1"
    fi
    cd ../
fi

if [[ $NonLec == "0" ]]; then
    echo "The DESIGN IS LOGICALLY EQUIVALENT"
else
    NonLec="-1"
    echo "The DESIGN IS NOT LOGICALLY EQUIVALENT"
fi

echo "$0 returns $NonLec"

exit $NonLec
