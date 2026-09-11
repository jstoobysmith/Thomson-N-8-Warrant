import Thomson.ThreePoint.Bound

/-! # Task 5b, step 0: the domain of the triangle inequality is `[0.9619, 2]³`, not `[0.96, 2]³`

**Task 5 as stated in `Thomson.ThreePoint.Tasks` is false.**  At the chord triple

`(a, b, c) = (1.682, 24/25, 24/25)`,  `gram = +5.6·10⁻³ > 0`,  all three chords in `[24/25, 2]`,

the certificate's triangle polynomial is `triP pivots (1.682) (24/25) (24/25) = −3.7·10⁻⁶ < 0`
(and `−1.68·10⁻⁵` at `a = 1.684`; the reference vector `pivotsNum` and the true pivots differ by
`< 10⁻²⁰`, and the value is `10⁻¹⁶`-stable in `u*`, so the sign is not in doubt).  The point is at
distance `≥ 0.21` from all five touching types, so it also refutes Task 5b, and it lies well inside
the Gram region, so it is not a boundary artefact.

The cause is the rounding of the chord bound.  `separation_of_energy_le` gives inner products
`t ≤ 5373/10000`, i.e. chords `s = √(2−2t) ≥ √(2 − 2·0.5373) = 0.9619771…`, and
`tri_of_poly` weakens that to the friendlier `24/25 = 0.96`.  For the *pair* inequality the
weakening is harmless (`pairP pivots (24/25) = +2.5·10⁻⁴`), but the triangle polynomial dips
negative on the sliver `0.96 ≤ b, c < 0.96099…`: the certificate was designed on the true range and
has no slack to spare there.  On the true range the minimum is `+1.475·10⁻⁵`, at
`(1.6865, 0.96198, 0.96198)`.

The repair is one constant.  `tri_of_poly'` below is `tri_of_poly` with `24/25` replaced by
`9619/10000` — the same proof, since `(9619/10000)² = 0.92525161 ≤ 0.9254 = 2 − 2·(5373/10000)`.
`Thomson.ThreePoint.Tasks` needs the matching change in `triP_nonneg`, `triP_global` and the
`tri` field of `exists_threePointCert` (`pairP_nonneg` may keep `24/25`).  Everything downstream is
unaffected: the certificate is only ever applied to configurations produced by the separation
theorem. -/

namespace Thomson.Tri5b

open Thomson

/-- The true lower bound on a chord length: `√(2 − 2·0.5373) = 0.9619771…`, rounded down. -/
noncomputable def chordLo : ℝ := 9619 / 10000

/-- **The corrected form of `tri_of_poly`.**  Identical to `Thomson.tri_of_poly` except that the
polynomial obligation is only imposed on `[chordLo, 2]³`, which is what the separation theorem
actually delivers. -/
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
        + (Real.sqrt (2 - 2 * t))⁻¹) := by
  intro u v t hu1 hv1 ht1 hu2 hv2 ht2 hdet
  set p := Real.sqrt (2 - 2 * u) with hp
  set q := Real.sqrt (2 - 2 * v) with hq
  set r := Real.sqrt (2 - 2 * t) with hr
  have hp2 : p ^ 2 = 2 - 2 * u := Real.sq_sqrt (by linarith)
  have hq2 : q ^ 2 = 2 - 2 * v := Real.sq_sqrt (by linarith)
  have hr2 : r ^ 2 = 2 - 2 * t := Real.sq_sqrt (by linarith)
  have hpp : 0 < p := Real.sqrt_pos.mpr (by linarith)
  have hqp : 0 < q := Real.sqrt_pos.mpr (by linarith)
  have hrp : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hu : u = 1 - p ^ 2 / 2 := by linarith
  have hv : v = 1 - q ^ 2 / 2 := by linarith
  have ht : t = 1 - r ^ 2 / 2 := by linarith
  have lo : ∀ w : ℝ, w ≤ 5373 / 10000 → chordLo ≤ Real.sqrt (2 - 2 * w) := fun w hw => by
    rw [chordLo, Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hi : ∀ w : ℝ, -1 ≤ w → Real.sqrt (2 - 2 * w) ≤ 2 := fun w hw => by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  have key := h p q r (lo u hu2) (lo v hv2) (lo t ht2) (hi u hu1) (hi v hv1) (hi t ht1)
    (by rw [← hu, ← hv, ← ht]; exact hdet)
  rw [← hu, ← hv, ← ht] at key
  have hpqr : 0 < p * q * r := by positivity
  rw [inv_eq_one_div, inv_eq_one_div, inv_eq_one_div]
  rw [show lam * (1 / p + 1 / q + 1 / r) = lam * (q * r + p * r + p * q) / (p * q * r) by
    field_simp]
  rw [le_div_iff₀ hpqr]
  linarith

end Thomson.Tri5b
