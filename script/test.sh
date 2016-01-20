#!/bin/sh

mlton -mlb-path-map mlb-path-map testsuite/test.mlb
./testsuite/test
