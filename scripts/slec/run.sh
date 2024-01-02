#!/bin/bash

# Copyright 2023 OpenHW Group
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

REF_REPO=https://github.com/openhwgroup/cv32e40p.git
REF_FOLDER=ref_design
REF_BRANCH=master

RTL_FOLDER=$(readlink -f ../..)

FLIST=cv32e40p_manifest.flist
TOP_MODULE=cv32e40p_core

usage() {                                 # Function: Print a help message.
  echo "Usage: $0 [ -t {cadence,synopsys,siemens} -p {sec,lec} ]" 1>&2
}
exit_abnormal() {                         # Function: Exit with error.
  usage
  exit 1
}

not_implemented() {
    echo "$1 does not have yet $2 implemented"
    exit 1
}

while getopts "t:p:" flag
do
    case "${flag}" in
        t)
        target_tool=${OPTARG}
        ;;
        p)
        target_process=${OPTARG}
        ;;
        :)
        exit_abnormal
        ;;
        *)
        exit_abnormal
        ;;
        ?)
        exit_abnormal
        ;;
    esac
done

if [ ! -d ./reports/ ]; then
    mkdir -p ./reports/
fi

if [[ "${target_tool}" != "cadence" && "${target_tool}" != "synopsys" && "${target_tool}" != "siemens" ]]; then
    exit_abnormal
fi

if [[ "${target_process}" != "sec" && "${target_process}" != "lec" ]]; then
    exit_abnormal
fi

if [[ -z "${GOLDEN_RTL}" ]]; then
    echo "The env variable GOLDEN_RTL is empty."
    if [ ! -d "./${REF_FOLDER}" ]; then
        echo "Cloning Golden Design...."
        git clone $REF_REPO --single-branch -b $REF_BRANCH $REF_FOLDER;
        git -C ${REF_FOLDER} checkout $REF_COMMIT
    fi
    export GOLDEN_RTL=$(pwd)/${REF_FOLDER}/rtl
else
    echo "${target_process^^}: Using ${GOLDEN_RTL} as reference design"
fi

REVISED_DIR=$RTL_FOLDER
REVISED_FLIST=$(pwd)/revised.src

GOLDEN_DIR=$(readlink -f ./${REF_FOLDER}/)
GOLDEN_FLIST=$(pwd)/golden.src

var_golden_rtl=$(awk '{ if ($0 ~ "{DESIGN_RTL_DIR}" && $0 !~ "#" && $0 !~ "tracer" && $0 !~ "wrapper") print $0 }' ${GOLDEN_DIR}/$FLIST | sed 's|${DESIGN_RTL_DIR}|'"${GOLDEN_DIR}"'/rtl/|')

var_revised_rtl=$(awk '{ if ($0 ~ "{DESIGN_RTL_DIR}" && $0 !~ "#" && $0 !~ "tracer" && $0 !~ "wrapper") print $0 }' ${REVISED_DIR}/$FLIST | sed 's|${DESIGN_RTL_DIR}|'"${REVISED_DIR}"'/rtl/|')

echo "Generating GOLDEN flist in path: ${GOLDEN_FLIST}"
echo $var_golden_rtl > ${GOLDEN_FLIST}
echo "Generating REVISED flist in path: ${REVISED_FLIST}"
echo $var_revised_rtl > ${REVISED_FLIST}

export report_dir=$(readlink -f $(dirname "${BASH_SOURCE[0]}"))/reports/$(date +%Y-%m-%d)/

if [[ -d ${report_dir} ]]; then
    rm -rf ${report_dir}
fi
mkdir -p ${report_dir}

export tcl_script=$(readlink -f $(dirname "${BASH_SOURCE[0]}"))/${target_tool}/${target_process}.tcl
export output_log=${report_dir}/output.${target_tool}.log
export summary_log=${report_dir}/summary.${target_tool}.log

export expected_grep_exit_code=1

if [[ "${target_tool}" == "cadence" ]]; then

    if [[ "${target_process}" == "lec" ]]; then
        lec -Dofile ${tcl_script} -TclMode -NoGUI -xl | tee ${output_log}
        regex_string="Hierarchical compare : Equivalent"
    elif [[ "${target_process}" == "sec" ]]; then
        jg -sec -proj ${report_dir} -batch -tcl ${tcl_script} -define report_dir ${report_dir} | tee ${output_log}
        regex_string="Overall SEC status[ ]+- Complete"
    fi

elif [[ "${target_tool}" == "synopsys" ]]; then

    if [[ "${target_process}" == "lec" ]]; then
        fm_shell -work_path $report_dir/work/ -f ${tcl_script} | tee ${output_log}
        regex_string="Verification SUCCEEDED"
    elif [[ "${target_process}" == "sec" ]]; then
        not_implemented ${target_tool} ${target_process}
    fi

elif [[ "${target_tool}" == "siemens" ]]; then

    if [[ "${target_process}" == "lec" ]]; then
        not_implemented ${target_tool} ${target_process}
    elif [[ "${target_process}" == "sec" ]]; then
        make -C siemens/ run_sec_vl SPEC_FLIST=${GOLDEN_FLIST} IMPL_FLIST=${REVISED_FLIST} TOP_MODULE=${TOP_MODULE} SUMMARY_LOG=${summary_log} | tee ${output_log}
        regex_string="^Fired"
        expected_grep_exit_code=0
    fi

fi

if [[ ! -f ${output_log} || ! -f ${summary_log} ]]; then
    echo "Something went wrong during the process"
    exit 1
fi

grep -Eq "${regex_string}" ${summary_log}; grep_exit_code=$?

[[ ${grep_exit_code} == ${expected_grep_exit_code} ]] && export EQ_STR="NOT"

echo "${target_process^^}: The DESIGN IS ${EQ_STR} EQUIVALENT"
exit ${exit_code}

