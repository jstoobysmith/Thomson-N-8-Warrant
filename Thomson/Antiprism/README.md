# `Thomson/Antiprism` — the candidate and its constants

**Reference.** The square antiprism as the `N = 8` minimiser: Erber–Hockney (1991), Ashby–Stucki
(1993) (numerical); the closed-form energy of the family, the equation `E′(u*) = 0` for the optimal
twist and everything below it is ours — blueprint §3–4, §6–11.

| file | content |
|---|---|
| `Family.lean` | `antiprism h`, the four chord lengths, the closed-form energy `antiprism_energy_eq'`, `thomson_eight_upper` |
| `Derivative.lean` | `E′` on the family, strict monotonicity, `uStar` and `antiprismEnergy'_uStar`, local minimality in the family |
| `Cube.lean` | the cube: `cube_energy`, `cube_not_minimal` |
| `Enclosure.lean` | `u*` to 13 digits and `√2` to 28, by the sign of `E′` at two rationals |
| `SharpChords.lean` | the four chords to 25 digits |
| `UStarSharp.lean` | `u*` to 32 digits (what the box covering needs) |
| `MinPoly.lean` | the degree-12 minimal polynomial of `u*` over `ℚ(√2)` (`uStar_minpoly`) |

Namespace `Thomson`.
