#!/usr/bin/env bash

set -e

VERSION="bb41926cb5a62e6cbe4b659ded6ff52c70b2baf1"


mkdir -p $RISCV/

cd $RISCV

if [ -z ${NUM_JOBS} ]; then
    NUM_JOBS=1
fi

if ! [ -e $RISCV/bin/riscv32-unknown-elf-gcc ]; then
    if ! [ -e $RISCV/riscv-gnu-toolchain ]; then
	git clone https://github.com/riscv/riscv-gnu-toolchain.git
    fi

    cd riscv-gnu-toolchain
    git checkout $VERSION
    git submodule update --init --recursive

    if [[ $1 -ne "0" || -z ${1} ]]; then
      echo "Compiling RISC-V Toolchain"
      ./configure --prefix=$RISCV --with-arch=rv32gc --with-abi=ilp32
      make -j${NUM_JOBS}
      make install
      echo "Compilation Finished"
    fi
fi
