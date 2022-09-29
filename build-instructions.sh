#!/bin/sh

# Get the latest version of the 64-bit CakeML compiler from our Github releases
# page:
curl -OL https://github.com/CakeML/cakeml/releases/download/v1985/cake-x64-64.tar.gz
tar xvzf cake-x64-64.tar.gz

# By default, the CakeML compiler reserves a few kilobytes for constants and
# code produced by the dynamic compiler. Using Candle requires setting these
# to some megabytes:
patch cake-x64-64/cake.S cake.S.patch

# Build the compiler binary
cd cake-x64-64 && make && cd ..

# Copy the compiler binary and the exported compiler state into this directory:
cp cake-x64-64/cake cake-x64-64/config_enc_str.txt .

# You can now run Candle by writing:
#   $ ./cake --candle
# or:
#   $ ./candle
# (without the $) at your prompt. Load the HOL Light sources by writing:
#   > #use "hol.ml";;
# (without > and with double semicolons) in the REPL.
#
