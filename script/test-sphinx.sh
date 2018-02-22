#!/bin/bash

set -o pipefail

echo "Building the documentation of RedPRL with Sphinx..."
cd doc;
make html || exit 1;
echo "Done!"
