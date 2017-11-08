#!/bin/bash

LIBS=$(pwd)/lib

mlyacc src/redprl/redprl.grm
mllex src/redprl/redprl.lex

mkdir -p bin
mlton -native-live-transfer 0 -verbose 1 -mlb-path-var "LIBS $LIBS" -output bin/redprl src/frontend.mlb
