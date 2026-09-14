#!/bin/sh
# One-time setup for scripts/comparator/run.sh: clone and build the comparator (with the toolchain
# it pins, downloaded by elan) and lean4export at the tag matching this project's Lean (v4.33.0).
set -e
TOOLS="${LEAN_TOOLS:-$HOME/.local/lean-tools}"; mkdir -p "$TOOLS"
LEANV=$(sed 's/.*://' "$(dirname "$0")/../../lean-toolchain")   # e.g. v4.33.0
[ -d "$TOOLS/comparator" ] || git clone --depth 1 https://github.com/leanprover/comparator "$TOOLS/comparator"
[ -d "$TOOLS/lean4export" ] || git clone https://github.com/leanprover/lean4export "$TOOLS/lean4export"
(cd "$TOOLS/lean4export" && git checkout -q "$LEANV" && lake build)
(cd "$TOOLS/comparator" && lake build comparator)
echo "comparator: $TOOLS/comparator/.lake/build/bin/comparator"
echo "lean4export ($LEANV): $TOOLS/lean4export/.lake/build/bin/lean4export"
