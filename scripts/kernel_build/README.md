# Building the kernel-checked certificates without exhausting memory

`lake build Tri5b` / `TriLocalCert` / `Task1b` would start one `lean` per core, and a kernel
check of one covering piece or one Task 5a face takes 2–13 GB; 14 of them exhaust 64 GB and the
machine swaps to death (it did, 2026-09-12).  This Lake version has no `-j`, so `build_all.sh`
builds the expensive modules one `lake build <module>` at a time through `sched.py`, which keeps
at most `N` workers and launches a new one only while at least `MINAVAIL` GB are free/inactive and
swap is not growing.  Measured 2026-09-13 on a 14-core, 64 GB Mac: Task 5a faces 112 min
(serially for the three type-3 faces), Task 1b tables 42 min at 5 workers, the 637 covering
pieces 228 min at ≤ 8 workers (about 4 s of kernel time per leaf), everything else minutes.
`test/Axioms.lean` prints the axioms of the final theorems: only `propext`, `Classical.choice`,
`Quot.sound`.
