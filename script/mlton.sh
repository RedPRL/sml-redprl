#!/bin/bash

LIBS=$(pwd)/lib

mkdir -p bin
mlton -mlb-path-var "LIBS $LIBS" -output bin/redprl src/frontend.mlb
