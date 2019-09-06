#!/bin/bash
# call with first argument = 0 to checkout only
set -o pipefail
set -e

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
VERSION="a03290eab661e2aa58288ad164f908bbbcc2169c"

mkdir -p $RISCV

cd $RISCV

if [ -z ${NUM_JOBS} ]; then
    NUM_JOBS=1
fi


if ! [ -e $RISCV/bin ]; then
    if ! [ -e $RISCV/riscv-gnu-toolchain ]; then
        git clone https://github.com/riscv/riscv-gnu-toolchain.git
    fi

    cd riscv-gnu-toolchain
    git checkout $VERSION
    git submodule update --init --recursive

    if [[ $1 -ne "0" || -z ${1} ]]; then
      echo "Compiling RISC-V Toolchain"
      ./configure --disable-linux --disable-multilib --disable-gdb --prefix=$RISCV --with-arch=rv32gc --with-abi=ilp32
      make -j${NUM_JOBS} | tail
      echo "Compilation Finished"
    fi
fi
