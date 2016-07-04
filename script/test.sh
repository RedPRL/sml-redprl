#!/bin/bash

LIBS=$(pwd)/lib

mlton -mlb-path-var "LIBS $LIBS" testsuite/test.mlb
./testsuite/test
