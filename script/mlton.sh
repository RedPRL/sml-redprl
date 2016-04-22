#!/bin/sh

mkdir -p bin
mlton -mlb-path-map mlb-path-map -output bin/jonprl src/frontend.mlb
