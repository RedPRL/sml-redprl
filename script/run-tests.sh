#!/bin/bash

REDPRL=./bin/redprl
PROBLEM=0

# Ensure that all succeeding tests and examples type-check
for f in test/success/*.prl example/*.prl ; do
    if ! $REDPRL $f >/dev/null 2>&1 ; then
        PROBLEM=1
        echo "FAIL: $f should succeed!"
    else
        echo "Checked $f"
    fi
done

# Ensure that failing tests fail
for f in test/failure/*.prl ; do
    if $REDPRL $f >/dev/null 2>&1 ; then
        PROBLEM=1
        echo "FAIL: $f should fail!"
    fi
done

if [ $PROBLEM -eq 0 ] ; then
    echo "All tests ran as expected!"
fi

exit $PROBLEM
