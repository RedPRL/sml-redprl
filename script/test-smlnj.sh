#!/bin/bash

echo "Building RedPRL with SML/NJ..."
if [ -n "${TRAVIS}" ]; then
  ./script/smlnj.sh || exit 1;
else
  ./script/smlnj.sh >build.log 2>&1 || { echo "build failed!"; cat build.log; exit 1; };
fi
echo "done!"

exec ./script/test-no-build.sh
