#!/bin/bash
# Check that the HOLLIGHT_USE_MODULE setting saved in config.mk is handled
# correctly. Run after a HOLLIGHT_USE_MODULE=1 build.
set -xe

# Changing the setting must regenerate hol.sh even if hol.sh looks newer than
# config.mk, as happens with same-second timestamps on macOS. Dating hol.sh an
# hour into the future reproduces that on any platform.
make hol.sh HOLLIGHT_USE_MODULE=0
test "$(./hol.sh -use-module)" = 0
touch -d "@$(( $(date +%s) + 3600 ))" hol.sh
make hol.sh HOLLIGHT_USE_MODULE=1
test "$(./hol.sh -use-module)" = 1

# Previewing or querying a build must not change the saved setting.
make -n HOLLIGHT_USE_MODULE=0 > /dev/null
make -q hol.sh HOLLIGHT_USE_MODULE=0 || true
grep -x "HOLLIGHT_USE_MODULE=1" config.mk

# A plain make keeps using the saved setting.
make hol.sh
test "$(./hol.sh -use-module)" = 1
