#!/bin/bash

LIBS=$(pwd)/lib

mlyacc src/redprl/redprl.grm
mllex src/redprl/redprl.lex

mkdir -p bin
mlton -prefer-abs-paths true -show-def-use frontend.du -stop tc -verbose 1 -mlb-path-var "LIBS $LIBS" -output bin/redprl src/frontend.mlb
