#!/bin/sh
# Independent re-verification: replay every declaration of the development through a fresh Lean
# kernel with `leanchecker` (shipped with the toolchain; the successor of `lean4checker`).  This
# re-runs all `decide +kernel` certificates (≈ 30 CPU-hours) and must not run alongside a build.
# Usage: scripts/leanchecker/check.sh            # all modules of `Complete`, one at a time
#        scripts/leanchecker/check.sh Thomson.Main   # one module, with --fresh
cd "$(dirname "$0")/../.."
if [ -n "$1" ]; then exec lake env leanchecker --fresh "$1"; fi
mods=$(grep -rh "^import Thomson" Thomson Thomson.lean --include='*.lean' | sed 's/import //' | sort -u; echo Thomson.Complete)
fail=0
for m in $mods; do
  echo "== $m $(date +%H:%M)"
  lake env leanchecker "$m" || { echo "LEANCHECKER FAILED: $m"; fail=1; }
done
exit $fail
