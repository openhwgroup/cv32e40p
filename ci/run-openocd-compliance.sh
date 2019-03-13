#!/usr/bin/env bash

set -e

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

vsim_out=$(mktemp)
openocd_out=$(mktemp)

function clean_up {
    rm ${vsim_out}
    rm ${openocd_out}
    kill 0
}

# kill all children if this script exits
trap "exit" INT TERM
trap clean_up EXIT

make -C ${ROOT}/tb/dm clean
make -C ${ROOT}/tb/dm tb-all
make -C ${ROOT}/tb/dm prog/test.hex
make -C ${ROOT}/tb/dm prog-run &> ${vsim_out}&

( tail -f -n0 ${vsim_out} & ) | grep -m 1 "Listening on port"

echo "Starting openocd"
${RISCV}/bin/openocd -f ${ROOT}/tb/dm/pulpissimo_compliance_test.cfg |& tee ${openocd_out}

if grep -q "ALL TESTS PASSED" ${openocd_out}; then
    exit 0
fi
exit 1
