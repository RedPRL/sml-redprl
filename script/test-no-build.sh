#!/bin/bash

# Requires 'ts' from the 'moreutils' package.

set -o pipefail
exec ./script/run-tests.sh | ts -i "[%.ss]"
