#!/bin/sh
# The machine-wide build queue. Every Lean build goes through it, so the machine runs
# at most SLOTS lakes at once, each held to JOBS lean workers, however many callers
# want one, first come first served. Run it from a tree's lean/ directory in place of lake:
#
#   ../tools/build.sh +PEqualNP.Library.L007        (same arguments as: lake build)
#   ../tools/build.sh --lake env lean Foo.lean      (any lake command, through the same queue)
#
# tools/bin/lake (first in PATH) sends every bare `lake build|env|exe` here, so this
# is the only door. SLOTS: $PEQUALNP_HOME/build-slots.conf (default 3). JOBS:
# $PEQUALNP_HOME/build-jobs.conf (default 3), set as LEAN_NUM_THREADS, which sizes lake's task
# pool (so at most JOBS lean processes per slot) and each lean's threads. Runs under nice -n 5.
# A slot is a directory under $PEQUALNP_HOME/build-slots; a slot whose holder is gone is
# taken over. Waiting prints one line a minute.
#
# SHARED COMPILED RESULTS. Lake's local artifact cache is on, one dir for every tree: a module
# whose input hash (its source, its transitive imports' outputs, toolchain, options) matches one
# compiled in any tree before is not compiled again; its outputs are hardlinked into this tree's
# .lake/build (LAKE_RESTORE_ARTIFACTS, so `lake env lean` finds the oleans).
set -u
HOME_DIR=${PEQUALNP_HOME:-$HOME/.pequalnp}
SLOTS=$( [ -f "$HOME_DIR/build-slots.conf" ] && cat "$HOME_DIR/build-slots.conf" || echo "${PEQUALNP_BUILD_SLOTS:-3}" )
JOBS=$( [ -f "$HOME_DIR/build-jobs.conf" ] && cat "$HOME_DIR/build-jobs.conf" || echo 3 )
if [ "${LAKE_ARTIFACT_CACHE:-}" != false ]; then   # the checker passes false: no shared cache for it
  export LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true LAKE_CACHE_DIR="$HOME_DIR/lake-cache"
fi
export LEAN_NUM_THREADS="$JOBS" PEQUALNP_IN_QUEUE=1
if [ "${1:-}" = "--lake" ]; then shift; else set -- build "$@"; fi
D=$HOME_DIR/build-slots
mkdir -p "$D"
mine=""
waited=0
while [ -z "$mine" ]; do
  i=1
  while [ "$i" -le "$SLOTS" ]; do
    s=$D/$i
    if mkdir "$s" 2>/dev/null; then echo $$ >"$s/pid"; mine=$s; break; fi
    holder=$(cat "$s/pid" 2>/dev/null || echo "")
    if [ -n "$holder" ] && ! kill -0 "$holder" 2>/dev/null; then rm -rf "$s"; continue; fi
    i=$((i + 1))
  done
  [ -n "$mine" ] && break
  sleep 2; waited=$((waited + 2))
  [ $((waited % 60)) -eq 0 ] && echo "build queue: waiting ${waited}s for one of $SLOTS slots" >&2
done
trap 'rm -rf "$mine"' EXIT INT TERM
nice -n 5 "$(dirname "$0")/bin/lake" "$@"
