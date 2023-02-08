#!/bin/sh

for v in 6.04  6.06  6.07  6.11  6.12  6.13  6.14  6.15  6.16 6.17  7.00  7.01  7.03  7.05  7.06  7.06.10-g84ce6cc4 7.08  7.09  7.10  7.11  7.12  7.13  7.14  8.00~alpha01 8.00~alpha02  8.00~alpha03  8.00~alpha04  8.00~alpha05 8.00~alpha06  8.00  8.00.01  8.00.02  8.00.03  8.00.04
do
    echo -n "camlp5.$v "
    opam info camlp5.$v | grep depends
done
