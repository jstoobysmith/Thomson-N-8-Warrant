/-
The N = 8 Thomson problem — Lean 4 formalisation.  See N8-Thomson-Blueprint.md.

This is the umbrella module of a standalone Lake project (`lakefile.toml` in this directory;
`lake exe cache get` once, then `lake build`).  The development is split into modules:

  Thomson/Basic.lean            §1–4   definitions, elementary facts, existence of a minimiser
  Thomson/Cube.lean             §5
  Thomson/Antiprism.lean        §6–8   the square-antiprism family, certified upper bound, `uStar`
  Thomson/ForceBalance.lean     §9     `energy_eq_half`, force balance
  Thomson/Derivative.lean       §10–11 `E′`, pinning `u*`, `antiprismEnergy'_uStar : E′(u*) = 0`
  Thomson/Yudin.lean            §12–13 Yudin's LP bounds, Schoenberg positivity (slow to compile)
  Thomson/Reduction.lean        §14    covering radius, the reduction to local + global steps
  Thomson/Separation.lean       §15    slack rigidity: `E ≤ 19.6753 ⟹` all distances `> 0.962`
  Thomson/ThreePoint/BV.lean           Bachoc–Vallentin three-point positivity for `S²` — PROVED
  Thomson/ThreePoint/Bound.lean        `ThreePointCert`, `three_point_bound` — PROVED
  Thomson/ThreePoint/Toolkit.lean      constants `rStar, s2Star, s4Star`, structure lemmas, Bernstein/Hessian toolkit — PROVED
  Thomson/ThreePoint/MinPoly.lean      Task 0: the degree-12 minimal polynomial of `u*` — PROVED
  Thomson/ThreePoint/CertData.lean     GENERATED data tables (kernel bases, fixed rationals, pivot slots, `pivotsNum`)
  Thomson/ThreePoint/Linear.lean       THE CERTIFICATE, defined implicitly: `pivots := pivotMatrix⁻¹ *ᵥ pivotRhs`;
                                       the 24 tightness rows are affine in the pivots and vanish by definition — PROVED
  Thomson/ThreePoint/Slack.lean        the slack identity along the antiprism family (Task 1c)
  Thomson/ThreePoint/Kernel*.lean      GENERATED: the kernel lemma, 310 polynomial identities (Task 1c)
  Thomson/ThreePoint/Redundant.lean    Task 1c: the two dropped tightness rows — PROVED
  Thomson/Pair/, Thomson/PSD/          Tasks 4 and 2 (`decide +kernel`) — PROVED
  Thomson/ThreePoint/Tasks.lean        THE TASKS: status table; the only `sorry` is Task 5a
  Thomson/Main.lean                    `thomson_eight_lower_of_tasks`, proved from the Tasks
  Thomson/Complete.lean                `thomson_eight_lower` outright (library `Complete`; builds the
                                       `native_decide` libraries `Task1b` and `Tri5b`)

Status: `thomson_eight_lower : antiprismEnergy uStar ≤ thomsonInf 8` (`Thomson/Complete.lean`) is
proved from `exists_threePointCert_of_tasks`, which is assembled from the Tasks of
`Thomson/ThreePoint/Tasks.lean`.  All of them are proved except Task 5a (local positivity of the
triangle polynomial at the five touching types), the one remaining `sorry`.  Tasks 1a, 1b and 5b
use `native_decide` and live in the separate libraries `Task1b` and `Tri5b`; the default build takes
them as hypotheses (`thomson_eight_lower_of_tasks`).  The previous
monolithic file is kept as `Thomson8_monolithic_backup.lean.txt`.
-/

import Thomson
