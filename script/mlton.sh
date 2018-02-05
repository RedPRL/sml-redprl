#!/bin/bash

LIBS=$(pwd)/lib

mlyacc src/redprl/redprl.grm
mllex src/redprl/redprl.lex

mkdir -p bin
mlton -verbose 2 -polyvariance false -drop-pass deepFlatten -mlb-path-var "LIBS $LIBS" -output bin/redprl src/frontend.mlb
