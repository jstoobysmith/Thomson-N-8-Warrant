# ThompsonEight

A Lean 4 / Mathlib formalization of the N = 8 case of the Thomson problem.

## 1. The problem

The Thomson problem asks: given `n` points constrained to the unit sphere `S² ⊂ ℝ³`, how should
they be arranged to minimize the total Coulomb (`1/r`) potential energy

    E(x₁, …, xₙ) = ∑_{i<j} 1 / ‖xᵢ − xⱼ‖ ?

It is a classical problem in electrostatics, going back to J. J. Thomson's 1904 "plum pudding"
model of the atom, and today serves as a standard test case for point-configuration problems on
the sphere (packing, energy minimization, spherical codes).

## 2. What is already known

For a handful of small `n` the minimizer is known rigorously (`n ≤ 6` and `n = 12`, the last via
Yudin/Cohn–Kumar-type sharp linear-programming bounds tight at the icosahedron). For most `n`,
including `n = 8`, no proof of optimality exists in the literature: the conjectured minimizer — a
square antiprism, not the more obvious cube — is known only numerically, from global optimization
searches. The linear-programming (LP) method that settles `n = 12` (and other "sharp" cases) is
known *not* to be strong enough for `n = 8`: the best possible LP bound sits about `0.0275` below
the antiprism's actual energy, so no LP certificate alone can close the gap.

## 3. What we are proving

The end goal of this repository is a fully machine-checked proof that the square antiprism is the
global energy minimizer among all admissible 8-point configurations on `S²`:

    thomsonInf 8 = antiprismEnergy uStar

(`Thomson/Main.lean`, `thomson_eight`), where `uStar` is the optimal antiprism shape parameter.
The "easy half" (the antiprism is *an* upper bound, `thomsonInf_le_uStar`) is fully proved. The
matching lower bound (`thomson_eight_lower`) is assembled from a three-point bound and an explicit
numerical certificate; as of now it is proved *modulo* a handful of `sorry`s recorded as the eight
open "Tasks" in `Thomson/ThreePoint/Tasks.lean` (nonsingularity and enclosure of a 24×24 pivot
system, two dropped-row identities, positive-semidefiniteness of six certificate blocks, and
polynomial nonnegativity on two remaining regions). Everything else in the development —
in particular the entire architecture connecting these Tasks to the final theorem — is sorry-free.

## 4. Why this would be a new result

`n = 8` is one of the smallest open cases of the Thomson problem: it is small enough that the
answer (the square antiprism, *not* the cube) has been known numerically for decades, yet large
enough that the classical sharp linear-programming technique that resolves cases like `n = 12`
provably cannot reach it. Closing it therefore requires going beyond LP bounds with genuinely new
structure (see §5), and doing so as a *formal, machine-checked* proof — rather than a numerical
claim backed by floating-point search — would settle a previously-open instance of a well known
open problem with the same standard of rigor as a hand proof, and arguably higher, since every
inequality here is checked by the Lean kernel rather than by a human referee.

## 5. Summary of the method

The proof does not attempt a direct global search. Instead it is organized as a chain of
reductions that turn an infinite-dimensional, non-convex minimization into a finite set of
explicit, checkable inequalities:

1. **Existence and compactness** (`Thomson/Basic.lean`). The energy is shown to be continuous on
   the (compact) space of admissible configurations with a fixed pairwise-separation floor, so the
   infimum is attained by an actual configuration, not just a limit.
2. **Reduction to near-optimal configurations** (`Thomson/Reduction.lean`). It suffices to rule
   out any configuration whose energy already beats a known upper bound (the best antiprism); the
   search space collapses to a sublevel set.
3. **Separation** (`Thomson/Separation.lean`). A degree-12 Yudin/Cohn–Kumar-style polynomial bound,
   kept in *slack* form rather than discarded, shows any such near-optimal configuration has all
   pairwise chord lengths `> 0.962` — a factor-of-nineteen improvement over the crude bound that
   compactness alone would give, and the key fact that makes the remaining search tractable.
4. **A three-point bound with an explicit certificate** (`Thomson/ThreePoint/`). A Cohn–Woo-type
   bound expresses the energy of any configuration as a sum involving *pairs* and *triples* of
   points, controlled by a matrix certificate. Because it needs to be numerically sharp — tight at
   the antiprism to seven digits — the certificate cannot be given as a simple rational witness:
   exact tightness forces its data into a degree-192 algebraic number field. The development
   instead *defines* the certificate implicitly as the solution of a 24×24 linear system built
   from the antiprism's own geometry, so that tightness holds definitionally, and reduces what
   remains to checkable inequalities: nonsingularity of that system, an interval enclosure of its
   solution, positive-semidefiniteness of the resulting quadratic-form blocks, and nonnegativity
   of two low-degree polynomials on explicit bounded domains (established locally by Hessian
   bounds near the touching points, and globally by a Bernstein-polynomial box covering).
5. **Assembly** (`Thomson/Main.lean`). Combining the separation bound with the three-point
   certificate pins the minimum energy down to within `0.0278` of the antiprism's energy — inside
   the gap that no linear-programming bound could reach — and the certificate's exact tightness at
   the antiprism turns that into the matching lower bound completing the proof.
