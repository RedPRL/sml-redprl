#!/usr/bin/env bash

mkdir -p ./bin
sml script/go-nj.sml
script/mkexec.sh `which sml` `pwd` redprl

