import Thomson.Enclosure
import Thomson.ThreePoint.Toolkit
import Thomson.ThreePoint.Linear

namespace Thomson

/-! # Sharp enclosures of the chord lengths (Task 1b)

The 25-digit companions of `rStar_bounds`, `s2Star_bounds`, `s4Star_bounds`, obtained from
`uStar_mem_Icc_sharp` and `sqrt2_bounds_sharp` by the same two-line argument.  Task 1b needs the
row residual at `pivotsNum` to `≈ 10⁻¹⁰`; these enclosures are what makes that possible. -/

theorem rStar_bounds_sharp :
    (1656394436250858698228889 / 2000000000000000000000000 : ℝ) < rStar ∧
      rStar < 1656394436250979442416157 / 2000000000000000000000000 := by
  have h1 := uStar_lower; have h2 := uStar_upper
  constructor
  · rw [rStar, Real.lt_sqrt (by norm_num)]; nlinarith
  · rw [rStar, Real.sqrt_lt' (by norm_num)]; nlinarith

theorem s2Star_bounds_sharp :
    (12876935261433149305702437 / 10000000000000000000000000 : ℝ) < s2Star ∧
      s2Star < 1609616907679309376826577 / 1250000000000000000000000 := by
  have h1 := uStar_lower; have h2 := uStar_upper
  obtain ⟨w1, w2⟩ := sqrt2_bounds_sharp
  have hu0 : (0:ℝ) ≤ 1 - uStar := by linarith
  have hp1 : (0:ℝ) ≤ Real.sqrt 2 - 7071067811865475244008443621 / 5000000000000000000000000000 := by
    linarith
  have hp2 : (0:ℝ) ≤ 14142135623730950488016887243 / 10000000000000000000000000000 - Real.sqrt 2 := by
    linarith
  constructor
  · rw [s2Star, Real.lt_sqrt (by norm_num)]; nlinarith [mul_nonneg hp2 hu0]
  · rw [s2Star, Real.sqrt_lt' (by norm_num)]; nlinarith [mul_nonneg hp1 hu0]

theorem s4Star_bounds_sharp :
    (18968929475026775762949503 / 10000000000000000000000000 : ℝ) < s4Star ∧
      s4Star < 3793785895005386033955051 / 2000000000000000000000000 := by
  have h1 := uStar_lower; have h2 := uStar_upper
  obtain ⟨w1, w2⟩ := sqrt2_bounds_sharp
  have hu0 : (0:ℝ) ≤ 1 - uStar := by linarith
  have hp1 : (0:ℝ) ≤ Real.sqrt 2 - 7071067811865475244008443621 / 5000000000000000000000000000 := by
    linarith
  have hp2 : (0:ℝ) ≤ 14142135623730950488016887243 / 10000000000000000000000000000 - Real.sqrt 2 := by
    linarith
  constructor
  · rw [s4Star, Real.lt_sqrt (by norm_num)]; nlinarith [mul_nonneg hp1 hu0]
  · rw [s4Star, Real.sqrt_lt' (by norm_num)]; nlinarith [mul_nonneg hp2 hu0]

/-! ## The chord arguments, in the field `ℚ(uStar, √2)`

Task 1a needs every entry of `pivotMatrix` as an explicit polynomial in the constants.  By
`pivotMatrix_pairVal_row` etc. (`Thomson.ThreePoint.Perturb`) an entry is a chord prefactor times
`Gh j u v t`, whose *arguments* are the inner products `1 − s²/2`.  These are not new irrationals:
each is a degree-one polynomial in `uStar` and `√2`.  Only the prefactors are genuinely irrational,
and those are enclosed by the `_sharp` bounds above. -/

theorem chord_zero : chord 0 = Real.sqrt 2 * rStar := by simp [chord]
theorem chord_one : chord 1 = 2 * rStar := by simp [chord]
theorem chord_two : chord 2 = s2Star := by simp [chord]
theorem chord_three : chord 3 = s4Star := by simp [chord]

theorem sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

/-- The inner product at the square edge `A = √2·r` is `u*` itself. -/
theorem chord_inner_zero : 1 - (chord 0) ^ 2 / 2 = uStar := by
  rw [chord_zero, mul_pow, sqrt2_sq, rStar_sq]; ring

/-- The inner product at the square diagonal `D = 2r` is `2u* − 1`. -/
theorem chord_inner_one : 1 - (chord 1) ^ 2 / 2 = 2 * uStar - 1 := by
  rw [chord_one, mul_pow, rStar_sq]; ring

/-- The inner product at the near cross chord `N = s₂`. -/
theorem chord_inner_two :
    1 - (chord 2) ^ 2 / 2 = -uStar + Real.sqrt 2 * (1 - uStar) / 2 := by
  rw [chord_two, s2Star_sq]; ring

/-- The inner product at the far cross chord `F = s₄`. -/
theorem chord_inner_three :
    1 - (chord 3) ^ 2 / 2 = -uStar - Real.sqrt 2 * (1 - uStar) / 2 := by
  rw [chord_three, s4Star_sq]; ring

/-- The five touching types are triples of chords, so the four lemmas above cover them. -/
theorem touchType_zero : touchType 0 = (chord 3, chord 3, chord 0) := by
  simp [touchType, chord]
theorem touchType_one : touchType 1 = (chord 3, chord 1, chord 2) := by
  simp [touchType, chord]
theorem touchType_two : touchType 2 = (chord 3, chord 2, chord 0) := by
  simp [touchType, chord]
theorem touchType_three : touchType 3 = (chord 1, chord 0, chord 0) := by
  simp [touchType, chord]
theorem touchType_four : touchType 4 = (chord 2, chord 2, chord 0) := by
  simp [touchType, chord]

end Thomson
