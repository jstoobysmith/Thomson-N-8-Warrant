# `Thomson/LP` — linear-programming bounds and separation

**Reference.** Delsarte–Goethals–Seidel (1977) for the LP method on spheres, Yudin (1992) for the
energy version with the touching-point construction, Schoenberg (1942) for the positivity of
Legendre sums on `S²`.  The *slack form* of Yudin's bound and the separation theorem it gives
(`E ≤ 19.6753 ⟹` every chord `> 0.9619`) are ours: blueprint §8.1, §12–15.

| file | content |
|---|---|
| `Yudin.lean` | Schoenberg positivity for `P₁…P₄, P₇, P₁₂` (from real solid harmonics), Yudin's bound at degrees 3, 7 (`thomsonInf_ge_yudin7 : 19.6462 < thomsonInf 8`) and 12 |
| `Separation.lean` | the bound as an identity; `separation_of_energy_le` |
| `Reduction.lean` | the finite reductions of the problem (`NearAntiprism`, the two-step split); kept for the record |

Namespace `Thomson`.
