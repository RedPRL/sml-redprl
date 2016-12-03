#!/usr/bin/env bash

sml script/go-nj.sml
script/mkexec.sh `which sml` `pwd` redprl

