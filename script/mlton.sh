#!/bin/sh

mkdir -p bin
mlton @MLton fixed-heap 0.5g -- -mlb-path-map mlb-path-map -output bin/jonprl src/frontend.mlb
