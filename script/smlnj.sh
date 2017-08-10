#!/usr/bin/env bash

mkdir -p ./bin
sml script/go-nj.sml < /dev/null
script/mkexec.sh `which sml` `pwd` redprl

