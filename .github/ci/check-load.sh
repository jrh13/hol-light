#!/bin/bash
# Load update_database.ml in hol.sh and check that HOL Light started properly.
# Usage: check-load.sh <Camlp5 banner that hol.sh must print>
set -xe

(echo 'loadt "update_database.ml";;') | ./hol.sh 2>&1 | tee log.txt
grep "Error" log.txt && exit 1
grep -F "$1" log.txt
