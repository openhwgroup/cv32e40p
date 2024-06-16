#!/bin/bash

# Copyright 2024 OpenHW Group and Dolphin Design
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#
# Licensed under the Solderpad Hardware License v 2.1 (the “License”);
# you may not use this file except in compliance with the License, or,
# at your option, the Apache License version 2.0.
# You may obtain a copy of the License at
#
# https://solderpad.org/licenses/SHL-2.1/
#
# Unless required by applicable law or agreed to in writing, any work
# distributed under the License is distributed on an “AS IS” BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

usage() {                                 # Function: Print a help message.
  echo "Usage: $0 -t {cadence,synopsys,siemens} -p {sec,lec} [-v {v1,v2}] [-x {0,1}] [-f {0,1}] [-z {0,1}] [-l {0,1,2}]]" 1>&2
  echo "For v2 : if f or z is 1 then p must be 1" 1>&2
  echo "         if z is 1 then f must be 1" 1>&2
  echo "         l only 1 or 2 if f is 1" 1>&2
}

exit_abnormal() {                         # Function: Exit with error.
  usage
  exit 1
}

not_implemented() {
    echo "$1 does not have yet $2 implemented"
    exit 1
}

print_log() {
    echo "[LOG] $1"
}

VERSION=v1
PULP_CFG=0
FPU_CFG=0
ZFINX_CFG=0
LATENCY_CFG=0

while getopts "t:p:v:x:f:z:l:" flag
do
    case "${flag}" in
        t)
        target_tool=${OPTARG}
        ;;
        p)
        target_process=${OPTARG}
        ;;
        v)
        VERSION=${OPTARG}
        ;;
        x)
        PULP_CFG=${OPTARG}
        ;;
        f)
        FPU_CFG=${OPTARG}
        ;;
        z)
        ZFINX_CFG=${OPTARG}
        ;;
        l)
        LATENCY_CFG=${OPTARG}
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

if [[ "${target_tool}" != "cadence" && "${target_tool}" != "synopsys" && "${target_tool}" != "siemens" ]]; then
    exit_abnormal
fi

if [[ "${target_process}" != "sec" && "${target_process}" != "lec" ]]; then
    exit_abnormal
fi

if [[ "${VERSION}" != "v1" && "${VERSION}" != "v2" ]]; then
    exit_abnormal
elif [[ "${VERSION}" == "v1" && ("${PULP_CFG}" != "0" || "${FPU_CFG}" != "0" || "${ZFINX_CFG}" != "0") ]]; then
    exit_abnormal
fi

if [[ "${PULP_CFG}" != 0 && "${PULP_CFG}" != 1 ]]; then
    exit_abnormal
fi

if [[ "${FPU_CFG}" != 0 && "${FPU_CFG}" != 1 ]]; then
    exit_abnormal
fi

if [[ "${ZFINX_CFG}" != 0 && "${ZFINX_CFG}" != 1 ]]; then
    exit_abnormal
fi

if [[ (("${PULP_CFG}" == 0 && ("${FPU_CFG}" == 1 || "${ZFINX_CFG}" == 1)) || ("${PULP_CFG}" == 1 && "${FPU_CFG}" == 0 && "${ZFINX_CFG}" == 1)) ]]; then
    exit_abnormal
fi

if [[ ("${FPU_CFG}" == 0 && ("${LATENCY_CFG}" == 1 || "${LATENCY_CFG}" == 2)) ]]; then
    exit_abnormal
fi

if [[ "${VERSION}" == "v1" ]]; then
    REF_BRANCH=cv32e40p_v1.0.0
    TOP_MODULE=cv32e40p_core
else
    echo "version 2"
    REF_BRANCH=dev
    TOP_MODULE=cv32e40p_top
fi

export top_module=${TOP_MODULE}
export version=${VERSION}
export pulp_cfg=${PULP_CFG}
export fpu_cfg=${FPU_CFG}
export zfinx_cfg=${ZFINX_CFG}
export latency_cfg=${LATENCY_CFG}

if [ -z "${REF_REPO}" ]; then
    print_log "Empty REF_REPO env variable"
    REF_REPO=https://github.com/openhwgroup/cv32e40p.git
    REF_FOLDER=ref_design
    print_log "  * Setting REF_REPO   ${REF_REPO}"
    print_log "  * Setting REF_FOLDER ${REF_FOLDER}"
    print_log "  * Setting REF_BRANCH ${REF_BRANCH}"
    print_log "  * Setting TOP_MODULE ${TOP_MODULE}"
fi

RTL_FOLDER=$(readlink -f ../..)

if [[ "${PULP_CFG}" == 0 && "${ZFINX_CFG}" == 0 ]]; then
    FLIST=cv32e40p_manifest.flist
else
    FLIST=cv32e40p_fpu_manifest.flist
fi

if [[ -z "${TOP_MODULE}" ]]; then
    print_log "Empty TOP_MODULE env variable"
    print_log "  * Setting TOP_MODULE ${TOP_MODULE}"
fi

if [ ! -d ./reports/ ]; then
    mkdir -p ./reports/
fi

if [[ -z "${GOLDEN_RTL}" ]]; then
    print_log "The env variable GOLDEN_RTL is empty."
    \rm -rf "./${REF_FOLDER}"
    print_log "  * Cloning Golden Design...."
    git clone $REF_REPO --single-branch -b $REF_BRANCH $REF_FOLDER;
    git -C ${REF_FOLDER} checkout $REF_COMMIT
    export GOLDEN_RTL=$(pwd)/${REF_FOLDER}/rtl
else
    print_log "${target_process^^}: Using ${GOLDEN_RTL} as reference design"
fi

REVISED_DIR=$RTL_FOLDER
REVISED_FLIST=$(pwd)/revised.src
TB_SRC_DIR=$(pwd)/tb_src
GOLDEN_DIR=$(readlink -f ./${REF_FOLDER}/)
GOLDEN_FLIST=$(pwd)/golden.src
TB_FLIST=cv32e40p_tb_src.flist

var_golden_rtl=$(awk '{ if ($0 ~ "{DESIGN_RTL_DIR}" && $0 !~ "#" && $0 !~ "tracer" && $0 !~ "tb_wrapper" && $0 !~ "cv32e40p_wrapper") print $0 }' ${GOLDEN_DIR}/$FLIST | sed 's|${DESIGN_RTL_DIR}|'"${GOLDEN_DIR}"'/rtl/|')

if [[ "${VERSION}" == "v1" ]]; then
  var_revised_rtl=$(awk '{ if ($0 ~ "{DESIGN_RTL_DIR}" && $0 !~ "#" && $0 !~ "tracer" && $0 !~ "tb_wrapper" && $0 !~ "cv32e40p_wrapper" && $0 !~ "top") print $0 }' ${REVISED_DIR}/$FLIST | sed 's|${DESIGN_RTL_DIR}|'"${REVISED_DIR}"'/rtl/|')
else
  var_revised_rtl=$(awk '{ if ($0 ~ "{DESIGN_RTL_DIR}" && $0 !~ "#" && $0 !~ "tracer" && $0 !~ "tb_wrapper") print $0 }' ${REVISED_DIR}/$FLIST | sed 's|${DESIGN_RTL_DIR}|'"${REVISED_DIR}"'/rtl/|')
  var_tb=$(awk '{ if ($0 ~ "{TB_SRC_DIR}" && $0 !~ "#" && $0 !~ "tracer" && $0 !~ "tb_wrapper") print $0 }'   ${TB_SRC_DIR}/$TB_FLIST | sed 's|${TB_SRC_DIR}|'"${TB_SRC_DIR}"'|')
fi

print_log "Generating GOLDEN flist in path: ${GOLDEN_FLIST}"
echo $var_golden_rtl > ${GOLDEN_FLIST}
print_log "Generating REVISED flist in path: ${REVISED_FLIST}"
echo $var_revised_rtl > ${REVISED_FLIST}
echo $var_tb   >> ${REVISED_FLIST}

export report_dir=$(readlink -f $(dirname "${BASH_SOURCE[0]}"))/reports/${target_tool}/$(date +%Y-%m-%d-%Hh%Mm%Ss)

if [[ -d ${report_dir} ]]; then
    rm -rf ${report_dir}
fi
mkdir -p ${report_dir}

export tcl_script=$(readlink -f $(dirname "${BASH_SOURCE[0]}"))/${target_tool}/${target_process}.tcl
export output_log=${report_dir}/output.${target_tool}-${target_process}.log
export summary_log=${report_dir}/summary.${target_tool}-${target_process}.log

export expected_grep_exit_code=1

if [[ "${target_tool}" == "cadence" ]]; then

    if [[ "${target_process}" == "lec" ]]; then
        lec -Dofile ${tcl_script} -TclMode -NoGUI -xl | tee ${output_log}
        regex_string="Hierarchical compare : Equivalent"
    elif [[ "${target_process}" == "sec" ]]; then
        jg -sec -proj ${report_dir} -tcl ${tcl_script} -define report_dir ${report_dir} | tee ${output_log}
        regex_string="Overall SEC status[ ]+- Complete"
    fi

elif [[ "${target_tool}" == "synopsys" ]]; then

    if [[ "${target_process}" == "lec" ]]; then
        fm_shell -work_path ${report_dir} -f ${tcl_script} | tee ${output_log}
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
    print_log "Something went wrong during the process"
    exit 1
fi

grep -Eq "${regex_string}" ${summary_log}; grep_exit_code=$?

if [[ ${grep_exit_code} != ${expected_grep_exit_code} ]]; then
    print_log "${target_process^^}: THE DESIGN IS EQUIVALENT"
else
    print_log "${target_process^^}: THE DESIGN IS NOT EQUIVALENT"
fi

exit ${exit_code}
