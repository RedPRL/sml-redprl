#!/bin/bash
pushd doc
latexmk -pdf definition.tex
popd
