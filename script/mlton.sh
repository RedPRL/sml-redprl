#!/bin/sh

mkdir -p bin
mlton -mlb-path-map mlb-path-map -output bin/redprl src/frontend.mlb
