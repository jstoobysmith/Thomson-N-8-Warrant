# `Thomson/ThreePoint` — the three-point bound

**Reference.** Bachoc–Vallentin, *New upper bounds for kissing numbers from semidefinite
programming* (J. AMS 2008) for the three-point positivity; Cohn–Woo, *Three-point bounds for energy
minimization* (J. AMS 2012) for the energy version.  The derivation for `S²`, degree 8, `k ≤ 5`
(`bv_positivity`, `three_point_bound`) is worked out here from the addition theorem on `S¹` and is
*not copied from a paper*: blueprint §12.2.  The bound as an identity and its equality case
(`Identity.lean`) are ours (`docs/uniqueness.md`, U1).

| file | content |
|---|---|
| `BachocVallentin.lean` | the matrices `S_k`, `bv_positivity` |
| `Certificate.lean` | `ThreePointCert`, `three_point_bound`, `thomson_eight_lower_of_cert`, `pair_of_poly`, `tri_of_poly` |
| `Toolkit.lean` | data-independent constants and structure lemmas used by the certificate |
| `Identity.lean` | `three_point_identity`, `three_point_tight` (every slack vanishes at equality) |

Namespace `Thomson`.
