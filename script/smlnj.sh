#!/usr/bin/env bash

mkdir -p ./bin
sml script/go-nj.sml < /dev/null || exit 1
script/mkexec.sh `which sml` `pwd` redprl || exit 1
