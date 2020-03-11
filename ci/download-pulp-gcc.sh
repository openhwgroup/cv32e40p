#!/bin/bash
set -o pipefail
set -e

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
VERSION="v1.0.16"

# mkdir -p $RISCV

wget https://github.com/pulp-platform/pulp-riscv-gnu-toolchain/releases/download/$VERSION/$VERSION-pulp-riscv-gcc-ubuntu-16.tar.bz2
echo "unpacking pulp gcc"
tar -xvf $VERSION-pulp-riscv-gcc-ubuntu-16.tar.bz2
echo "moving pulp gcc to $RISCV"
mv $VERSION-pulp-riscv-gcc-ubuntu-16.tar.bz2 "$RISCV"
