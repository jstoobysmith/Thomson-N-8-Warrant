#!/bin/sh
# Memory-throttled build of the expensive `decide +kernel` libraries (this Lake has no `-j`):
# one `lake build <module>` per worker, at most N at once, launched only while ≥ MINAVAIL GB
# of memory is available and swap is quiet.  Run from the repository root after `lake build`
# of the default library's cheap part; the last two steps rebuild the default library and
# `Complete` with lake's own parallelism (nothing expensive is left for them).
# Stage lists (dependency order): TriangleLocal CFData (25 GB, alone) → Type* → Face* → Glue/Final/Tasks → Task1b tables
# → Task1b check → Tri5b covering pieces → Tri5b final.  Faces of type 3 need ~13 GB each: run
# them with N=1 (or use the serialiser idea in the README).
D=$(cd "$(dirname "$0")" && pwd); cd "$D/../.."; mkdir -p "$D/logs"
run() { echo "== stage $1 N=$2 minavail=$3 $(date)"; python3 "$D/sched.py" "$D/$1" $2 $3 "$D/logs/$1" $4 || { echo "STAGE $1 FAILED"; exit 1; }; }
run s0_cfdata.txt 1 14 force
run s1_types.txt 2 14 force
run s2_faces.txt 1 14 force
run s3_glue.txt 1 14 force
run s5_kt.txt 5 14
run s6_t1b.txt 1 14 force
run s9_kparts.txt 8 14
run s10_tri5b.txt 1 8 force
lake build Thomson || exit 1
lake build Complete || exit 1
lake env lean test/Axioms.lean
