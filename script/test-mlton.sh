#!/bin/bash

# Requires 'chronic' and 'ts' from the 'moreutils' package.

set -o pipefail

echo "Building RedPRL with MLton..."
if [ -n "${TRAVIS}" ]; then
  ./script/mlton.sh || exit 1;
else
  chronic ./script/mlton.sh || { echo "Build failed!"; exit 1; };
fi
echo "Done!"

exec ./script/run-tests.sh | ts -i "[%.ss]"
