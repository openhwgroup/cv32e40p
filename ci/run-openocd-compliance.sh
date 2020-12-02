#!/usr/bin/env bash

# Copyright 2020 ETH Zurich
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# Author: Robert Balas <balasr@iis.ee.ethz.ch>

set -e

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

if [ -z "${RISCV}" ]
then
    echo "RISCV is empty"
    exit 1
fi

function cleanup {
  echo "cleaning up processes and tmp files"
  sleep 2
  echo "vsim pid is:${vsim_pid} pgid:${vsim_pgid}"
  if ps -p "${vsim_pid}" > /dev/null
  then
      echo "vsim pid exists, killing it"
      kill -- -"${vsim_pgid}"
  fi
  rm "${vsim_out}"
}

trap cleanup EXIT

vsim_out=$(mktemp)
openocd_out=openocd.log

make -C "${ROOT}"/tb/dm vsim-run &> "${vsim_out}"&
# record vsim pid/pgid to kill it if it survives this script
vsim_pid=$!
vsim_pgid=$(ps -o pgid= ${vsim_pid} | grep -o [0-9]*)

# block until we get "Listening on port" so that we are safe to connect openocd
coproc grep -m 1 "Listening on port"
tail -f -n0 "${vsim_out}" --pid "$COPROC_PID" >&"${COPROC[1]}"

echo "Starting openocd"
"${RISCV}"/bin/openocd -f "${ROOT}"/tb/dm/pulpissimo_compliance_test.cfg |& tee "${openocd_out}"


if grep -q "ALL TESTS PASSED" "${openocd_out}"; then
    exit 0
fi
exit 1

