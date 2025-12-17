#!/bin/bash
set -e

cd /Users/ahle/repos/verilator/build

# Use homebrew LLVM for C++ compilation, but SDK headers for FlexLexer
export PATH="/opt/homebrew/bin:/opt/homebrew/opt/llvm/bin:/usr/bin:/bin:/usr/sbin:/sbin"
export CC=/opt/homebrew/opt/llvm/bin/clang
export CXX=/opt/homebrew/opt/llvm/bin/clang++
export SDKROOT=/Library/Developer/CommandLineTools/SDKs/MacOSX15.5.sdk

# Include SDK's FlexLexer.h which has size_t signatures
export CXXFLAGS="-isysroot $SDKROOT -I/Library/Developer/CommandLineTools/usr/include"
export CFLAGS="-isysroot $SDKROOT"

# Link against homebrew LLVM's libc++
export LDFLAGS="-L/opt/homebrew/opt/llvm/lib/c++ -Wl,-rpath,/opt/homebrew/opt/llvm/lib/c++"

cmake .. -DFLEX_INCLUDE_DIR=/Library/Developer/CommandLineTools/usr/include

make -j8
