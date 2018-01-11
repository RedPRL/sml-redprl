#!/bin/bash

# Requires 'chronic' and 'ts' from the 'moreutils' package.

echo "Building RedPRL with SML/NJ..."
if [ -n "${TRAVIS}" ]; then
  ./script/smlnj.sh || exit 1;
else
  chronic ./script/smlnj.sh || { echo "Build failed!"; exit 1; };
fi
echo "Done!"

exec ./script/run-tests.sh | ts -i "[%.ss]"
