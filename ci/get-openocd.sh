#!/bin/bash

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

set -e

VERSION="af3a034b57279d2a400d87e7508c9a92254ec165"

mkdir -p $RISCV/
cd $RISCV

check_version() {
    $1 --version | awk "NR==1 {if (\$NF>$2) {exit 0} exit 1}" || (
	echo $3 requires at least version $2 of $1. Aborting.
	exit 1
    )
}


if [ -z ${NUM_JOBS} ]; then
    NUM_JOBS=1
fi

if ! [ -e $RISCV/bin/openocd ]; then
    if ! [ -e $RISCV/riscv-openocd ]; then
	git clone https://github.com/riscv/riscv-openocd.git
    fi
    check_version automake 1.14 "OpenOCD build"
    check_version autoconf 2.64 "OpenOCD build"

    cd riscv-openocd
    git checkout $VERSION
    git submodule update --init --recursive

    echo "Compiling OpenOCD"
    ./bootstrap
    ./configure --prefix=$RISCV --disable-werror --disable-wextra --enable-remote-bitbang
    make -j${NUM_JOBS}
    make install
    echo "Compilation Finished"
fi

