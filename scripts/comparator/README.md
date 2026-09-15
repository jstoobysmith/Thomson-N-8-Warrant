# The Lean comparator

[leanprover/comparator](https://github.com/leanprover/comparator) is the judge used, for example,
for the FLT formalisation announcement: it builds `Challenge.lean` (statements with `sorry`,
importing only definitions) and `Solution.lean` (the same statements, proved), exports both with
`lean4export`, and confirms that every theorem in `comparator.json` has *the same statement* in
both and depends on no axiom beyond `propext`, `Quot.sound`, `Classical.choice`, with the kernel
as the only judge (optionally also an external kernel such as `nanoda`).

* `Challenge.lean` — imports `Thomson.Antiprism.Family` only (which brings the definitions
  `energy`, `Admissible`, `thomsonInf`, `antiprism`, `antiprismEnergy`, `uStar`); four statements.
* `Solution.lean` — imports `Thomson.Complete`; the same four statements, proved.
* `comparator.json` — the configuration.
* `setup.sh` — one-time: clones and builds the comparator and `lean4export` (at this project's
  Lean version) under `~/.local/lean-tools/`.
* `run.sh` — runs the comparator from the repository root.  The project must be fully built first
  (`scripts/kernel_build/build_all.sh`), because the comparator's own `lake build Solution` would
  otherwise start the 30-CPU-hour certificates unthrottled.

On macOS the sandbox `landrun` is not available; `run.sh` uses the comparator's
`fake-landrun.sh`, which is fine when — as here — the solution is not adversarial: the statement
comparison and the axiom check are what the certificate of this repository rests on.  On Linux,
follow the comparator README's `systemd-run … landrun` invocation instead.

## Measured run (2026-09-14/15)

`run.sh` on this project, after a full build: **"Your solution is okay!"**, exit code 0, in
81 759 s wall (22.7 h; 80 636 s CPU, single-threaded), peak resident memory 47.3 GB on a 64 GB
machine.  The comparator replays every declaration the four theorems depend on through its own
kernel, including all the `decide +kernel` certificates, which is where the time and the memory
go; keep other memory users off the machine while it runs.
