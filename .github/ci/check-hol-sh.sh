#!/bin/bash
# Check 'hol.sh -version' and 'hol.sh -help'.
# Usage: check-hol-sh.sh [expected value of 'hol.sh -use-module']
set -xe

./hol.sh -version
# -version must report the checked-out commit.
./hol.sh -version | grep -F "(commit $(git rev-parse HEAD))"
./hol.sh -help

if [ "$#" -ge 1 ]; then
  test "$(./hol.sh -use-module)" = "$1"
fi
