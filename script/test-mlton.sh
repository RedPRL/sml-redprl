#!/bin/bash

echo "Building RedPRL with MLton..."
./script/mlton-tc.sh >build.log 2>&1 || { echo "build failed!"; cat build.log; exit 1; }
echo "done!"

# exec ./script/test-no-build.sh
