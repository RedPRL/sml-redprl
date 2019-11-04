#!/bin/bash

set -o pipefail

echo "Building the documentation of RedPRL with Sphinx..."
cd doc;
if [ -n "${TRAVIS}" ]; then
  pip install --user --upgrade requests[security] || exit 1;
  python -m easy_install --upgrade pyOpenSSL || exit 1;
  pip install --user --upgrade Sphinx sphinx-rtd-theme || exit 1;
  make SPHINXOPTS="-n -W" html || exit 1;
else
  make html || exit 1;
fi
echo "Done!"
