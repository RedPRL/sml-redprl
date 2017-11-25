#!/bin/bash

REDPRL=./bin/redprl
PROBLEM=0

# Ensure that all succeeding tests and examples type-check
for f in test/success/*.prl example/*.prl ; do
    echo "Testing $f"
    if ! $REDPRL $f >$f.log 2>&1 ; then
        PROBLEM=1
        echo "Test $f should succeed but failed!"
    fi
done


# Ensure that failing tests fail
for f in test/failure/*.prl ; do
    if $REDPRL $f >$f.log 2>&1 ; then
        PROBLEM=1
        echo "Test $f should fail but succeeded!"
    fi
done

if [ $PROBLEM -eq 0 ] ; then
    echo "All tests ran as expected!"
fi

exit $PROBLEM
