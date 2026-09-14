#!/bin/sh
# Check the main theorems with the Lean comparator (https://github.com/leanprover/comparator):
# `Solution.lean` proves exactly the statements of `Challenge.lean` with only the permitted axioms.
#
# One-time setup (`scripts/comparator/setup.sh`): the comparator is built with its own toolchain;
# `lean4export` must match this project's Lean (v4.33.0), so it is built separately at that tag.
# Then, from the repository root, with the project fully built (`scripts/kernel_build/build_all.sh`,
# so that the comparator's own `lake build Solution` has nothing expensive left to do):
#   scripts/comparator/run.sh
# On Linux the README's `systemd-run … landrun` sandbox should be used instead of
# `fake-landrun.sh` (macOS has no landrun; here the Solution is our own code, so the sandbox is
# not what we rely on — the comparison and the axiom check are).
set -e
cd "$(dirname "$0")/../.."
TOOLS="${LEAN_TOOLS:-$HOME/.local/lean-tools}"
COMPARATOR_DIR="${COMPARATOR_DIR:-$TOOLS/comparator}"
LEAN4EXPORT_DIR="${LEAN4EXPORT_DIR:-$TOOLS/lean4export}"
if [ ! -x "$COMPARATOR_DIR/.lake/build/bin/comparator" ]; then
  echo "comparator not built: run scripts/comparator/setup.sh (COMPARATOR_DIR=$COMPARATOR_DIR)"; exit 2
fi
export COMPARATOR_LANDRUN="${COMPARATOR_LANDRUN:-$COMPARATOR_DIR/scripts/fake-landrun.sh}"
export COMPARATOR_LEAN4EXPORT="${COMPARATOR_LEAN4EXPORT:-$LEAN4EXPORT_DIR/.lake/build/bin/lean4export}"
exec lake env "$COMPARATOR_DIR/.lake/build/bin/comparator" comparator.json
