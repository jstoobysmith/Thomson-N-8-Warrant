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
  Thomson/ThreePoint/Tasks.lean        THE EIGHT OPEN TASKS (the only `sorry`s), with proof sketches
  Thomson/Main.lean                    `thomson_eight_lower`, proved from the Tasks

Status: `thomson_eight_lower : antiprismEnergy uStar ≤ thomsonInf 8` is proved from
`exists_threePointCert`, which is assembled from the Tasks: `det ≠ 0` of the pivot system (1a), an
enclosure of the pivots (1b), two redundant tightness rows (1c), positive semidefiniteness of the
blocks (2), the pair inequality (4) and the triangle inequality (5a, 5b).  Tasks 0, 3, 6 are proved.
Everything else, including Bachoc–Vallentin positivity, the three-point bound, and the exact
tightness of the certificate at the antiprism (modulo 1a), is proved without `sorry`.  The previous
monolithic file is kept as `Thomson8_monolithic_backup.lean.txt`.
-/

import Thomson
