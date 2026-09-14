# The `N = 8` Thomson problem, formalised in Lean 4

`Thomson.thomson_eight : thomsonInf 8 = antiprismEnergy uStar` and
`Thomson.thomson_eight_unique` (`Thomson/Complete.lean`): eight unit charges minimise their
Coulomb energy exactly at the square antiprism with the optimal twist, uniquely up to isometry.
Axioms: `propext`, `Classical.choice`, `Quot.sound` only — no `sorry`, no `native_decide`
(`test/Axioms.lean`).

* `organisation.md` — the layout of the proof and the conventions; each directory of `Thomson/`
  has a `README.md` naming its literature source.
* `docs/blueprint.md`, `docs/uniqueness.md` — the mathematics; `docs/history/` — the task plans.
* `scripts/threepoint/` — the certificate design and every generator of a GENERATED file;
  `scripts/kernel_build/` — how to build the expensive kernel-checked libraries without
  exhausting memory (`build_all.sh`).

Build: `lake exe cache get`, `lake build` (the default library, minutes), then
`scripts/kernel_build/build_all.sh` for `Pivots`, `TriangleLocal`, `TriangleGlobal` and `Complete`
(about seven hours on a 14-core, 64 GB machine).  Do not `lake build TriangleGlobal` directly.
