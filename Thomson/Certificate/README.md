# `Thomson/Certificate` — the concrete certificate

**Reference.** Ours throughout: blueprint §12.3–12.7 (`docs/blueprint.md`).  The certificate is
the numerically sharp three-point certificate for `N = 8`, restricted by the separation theorem to
inner products `≤ 0.5373`; it is *defined implicitly* — 95 fixed rationals and 24 pivots solved
from the 24 tightness rows — because its exact coordinates in `ℚ(√2, u*, r, s₂, s₄)` have
15 000-digit coefficients.  Design scripts: `scripts/threepoint/task1_*.py`.

| file | content |
|---|---|
| `Data.lean` | GENERATED (`task1_emit_lean.py`): the kernel bases `B k` as polynomials in `u*`, the fixed rationals, the pivot slots, `pivotsNum` |
| `Linear.lean` | `Fh`, `Hp`, the rows `rowSpec`/`rowFun`, `pivotMatrix`, `pivots`, `rows_vanish`; everything is affine in the pivots (`IsAff`) |
| `Perturb.lean` | replacing the true pivots by `pivotsNum` costs at most `‖p − pivotsNum‖∞` times an explicit ℓ¹ quantity |
| `Slack.lean` | the three-point bound as an identity along the antiprism family |
| `Kernel.lean`, `Kernel/` | GENERATED (`kernel_lean.py`): the entries of `Acomb_k(u)` and their double zero at `u*` |
| `Redundant.lean` | the two tightness rows that follow from the others |
| `Assemble.lean` | the numeric obligations as named propositions (`Task1a`, `Task1b`, `Task5a`, `Task5b`, …) and `exists_threePointCert_of_tasks` |

The obligations are discharged in the libraries `Pivots`, `PSD`, `Pair`, `TriangleLocal`,
`TriangleGlobal`.  Namespace `Thomson`.
