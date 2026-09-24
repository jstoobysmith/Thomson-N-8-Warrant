# A warrant for the `N = 8` Thomson problem, in Lean 4

This repository is a **warrant** for the Thomson problem at `n = 8`: it confirms that eight unit
charges minimise their Coulomb energy exactly at the **square antiprism** with the optimal twist,
uniquely up to isometry — the configuration long known numerically.  The warrant was found by
**Joseph Tooby-Smith** and **Alex Zughaid**.

`Thomson.thomson_eight : thomsonInf 8 = antiprismEnergy uStar` and
`Thomson.thomson_eight_unique` (`Thomson/Complete.lean`) are the statements.
Axioms: `propext`, `Classical.choice`, `Quot.sound` only — no `sorry`, no `native_decide`
(`test/Axioms.lean`).

## Warrant, not proof

We use "warrant" in the sense set out in [Dinosaurs, warrants and finding AI resolutions to
conjectures](https://josephtoobysmith.com/math/2026/09/18/Warrants-dinosaur-bones-AI.html): a
machine-checked object that licenses belief in a result without supplying human understanding of
it, as distinct from a proof, which is a human-written and human-readable argument that convinces
a human.  A warrant can afterwards be *digested* into a proof.

**A digest of this warrant is in progress** and is not part of this repository.

## Layout

* `organisation.md` — the layout of the proof and the conventions; each directory of `Thomson/`
  has a `README.md` naming its literature source.
* `docs/blueprint.md`, `docs/uniqueness.md` — the mathematics; `docs/history/` — the task plans.
* `scripts/threepoint/` — the certificate design and every generator of a GENERATED file;
  `scripts/kernel_build/` — how to build the expensive kernel-checked libraries without
  exhausting memory (`build_all.sh`).

## Build

`lake exe cache get`, `lake build` (the default library, minutes), then
`scripts/kernel_build/build_all.sh` for `Pivots`, `TriangleLocal`, `TriangleGlobal` and `Complete`
(about seven hours on a 14-core, 64 GB machine).  Do not `lake build TriangleGlobal` directly.
