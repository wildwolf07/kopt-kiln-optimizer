#!/bin/sh
# Build kopt. Needs only a C++17 compiler (g++ 11 or newer, or clang).
set -e
cd "$(dirname "$0")"
mkdir -p build
CXX="${CXX:-g++}"
"$CXX" -std=c++17 -O2 -Wall -Wextra -o build/kopt-bin src/*.cpp
