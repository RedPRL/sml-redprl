#!/bin/bash

LIBS=$(pwd)/lib

mlyacc src/redprl/redprl.grm
mllex src/redprl/redprl.lex

mlton -mlb-path-var "LIBS $LIBS" test/test.mlb
./test/test
