#!/bin/bash

echo "Building RedPRL with MLton..."
if [ -n "${TRAVIS}" ]; then
  ./script/mlton.sh || exit 1;
else
  ./script/mlton.sh >build.log 2>&1 || { echo "build failed!"; cat build.log; exit 1; };
fi
echo "done!"

exec ./script/test-no-build.sh
