import Thomson.ThreePoint.Certificate

/-! # Task 5b, step 0: the domain of the triangle inequality is `[0.9619, 2]³`, not `[0.96, 2]³`

**Task 5 as first stated (on `[24/25, 2]³`) was false.**  At the chord triple

`(a, b, c) = (1.682, 24/25, 24/25)`,  `gram = +5.6·10⁻³ > 0`,  all three chords in `[24/25, 2]`,

the certificate's triangle polynomial is `triP pivots (1.682) (24/25) (24/25) = −3.7·10⁻⁶ < 0`
(and `−1.68·10⁻⁵` at `a = 1.684`; the reference vector `pivotsNum` and the true pivots differ by
`< 10⁻²⁰`, and the value is `10⁻¹⁶`-stable in `u*`, so the sign is not in doubt).  The point is at
distance `≥ 0.21` from all five touching types, so it also refuted Task 5b, and it lies well inside
the Gram region, so it is not a boundary artefact.

The cause was the rounding of the chord bound.  `separation_of_energy_le` gives inner products
`t ≤ 5373/10000`, i.e. chords `s = √(2−2t) ≥ √(2 − 2·0.5373) = 0.9619771…`, and `tri_of_poly`
used to weaken that to the friendlier `24/25 = 0.96`.  For the *pair* inequality the weakening is
harmless (`pairP pivots (24/25) = +2.5·10⁻⁴`), but the triangle polynomial dips negative on the
sliver `0.96 ≤ b, c < 0.96099…`: the certificate was designed on the true range and has no slack to
spare there.  On the true range the minimum is `+1.475·10⁻⁵`, at `(1.6865, 0.96198, 0.96198)`.

**Repaired**: `Thomson.tri_of_poly` (`Bound.lean`) and the Task 5 statements of
`Thomson.Certificate.Assemble` now use `9619/10000` (`(9619/10000)² = 0.92525161 ≤ 0.9254`).
`tri_of_poly'` is kept as the name this library uses. -/

namespace Thomson.Tri5b

open Thomson

/-- The true lower bound on a chord length: `√(2 − 2·0.5373) = 0.9619771…`, rounded down. -/
noncomputable def chordLo : ℝ := 9619 / 10000

/-- `Thomson.tri_of_poly`, with the chord bound written `chordLo`. -/
theorem tri_of_poly' (L : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ)
    (D : (k : Fin 6) → Fin (9 - (k : ℕ)) → ℝ) (lam : ℝ)
    (h : ∀ p q r : ℝ, chordLo ≤ p → chordLo ≤ q → chordLo ≤ r → p ≤ 2 → q ≤ 2 → r ≤ 2 →
      0 ≤ 1 + 2 * (1 - p ^ 2 / 2) * (1 - q ^ 2 / 2) * (1 - r ^ 2 / 2)
          - (1 - p ^ 2 / 2) ^ 2 - (1 - q ^ 2 / 2) ^ 2 - (1 - r ^ 2 / 2) ^ 2 →
      0 ≤ lam * (q * r + p * r + p * q)
          - p * q * r * Fsum L D (1 - p ^ 2 / 2) (1 - q ^ 2 / 2) (1 - r ^ 2 / 2)) :
    ∀ u v t : ℝ, -1 ≤ u → -1 ≤ v → -1 ≤ t →
      u ≤ 5373 / 10000 → v ≤ 5373 / 10000 → t ≤ 5373 / 10000 →
      0 ≤ 1 + 2 * u * v * t - u ^ 2 - v ^ 2 - t ^ 2 →
      Fsum L D u v t ≤ lam * ((Real.sqrt (2 - 2 * u))⁻¹ + (Real.sqrt (2 - 2 * v))⁻¹
        + (Real.sqrt (2 - 2 * t))⁻¹) :=
  tri_of_poly L D lam h

end Thomson.Tri5b
