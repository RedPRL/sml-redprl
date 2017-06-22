#!/bin/bash

LIBS=$(pwd)/lib

mlyacc src/redprl/redprl.grm
mllex src/redprl/redprl.lex

mkdir -p bin
mlton -profile time -mlb-path-var "LIBS $LIBS" -output bin/redprl-profile src/frontend.mlb
