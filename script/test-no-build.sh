#!/bin/bash

# Requires 'ts' from the 'moreutils' package.

exec ./script/run-tests.sh | ts -i "[%.ss]"
exit "${PIPESTATUS[0]}"
