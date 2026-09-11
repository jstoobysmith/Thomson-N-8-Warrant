import Thomson.Task1b.Check

/-! # Task 1b (and Task 1a)

`estimates` gives `‖I − N·M‖∞ ≤ η = 10⁻¹¹` and `‖N·r‖∞ ≤ ρ = 10⁻²¹`, `M = pivotMatrix`,
`r = rowFun · pivotsNum`.  The rest is the standard contraction argument, done with explicit sums:

* `M y = 0` gives `y = E y`, so `‖y‖ ≤ η‖y‖` and `y = 0`: `M` is injective, **Task 1a**;
* then `x := pivots − pivotsNum` has `M x = −r`, so `x = E x − N r` and
  `‖x‖ ≤ ρ/(1 − η) < 2·10⁻²¹`: **Task 1b**, at `2·10⁻²¹` — far inside the `10⁻¹²` Task 5b needs. -/

namespace Thomson.Task1b

open Thomson Thomson.Tri5b Matrix

/-- **The contraction estimate.** -/
theorem abs_le_of_fixed {E : Matrix (Fin 24) (Fin 24) ℝ} {η β : ℝ} (hη : η < 1)
    (hE : ∀ i, ∑ j, |E i j| ≤ η) {x b : Fin 24 → ℝ} (hx : ∀ i, x i = (E *ᵥ x) i + b i)
    (hb : ∀ i, |b i| ≤ β) : ∀ i, |x i| ≤ β / (1 - η) := by
  obtain ⟨i0, -, hi0⟩ :=
    Finset.exists_max_image Finset.univ (fun i => |x i|) Finset.univ_nonempty
  have hmax : ∀ j, |x j| ≤ |x i0| := fun j => hi0 j (Finset.mem_univ j)
  have hEx : |(E *ᵥ x) i0| ≤ (∑ j, |E i0 j|) * |x i0| := by
    simp only [mulVec, dotProduct]
    calc |∑ j, E i0 j * x j| ≤ ∑ j, |E i0 j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |E i0 j| * |x i0| := Finset.sum_le_sum fun j _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hmax j) (abs_nonneg _)
      _ = (∑ j, |E i0 j|) * |x i0| := (Finset.sum_mul _ _ _).symm
  have key : |x i0| ≤ η * |x i0| + β := by
    have h1 : |x i0| ≤ |(E *ᵥ x) i0| + |b i0| := by rw [hx i0]; exact abs_add_le _ _
    have h2 : (∑ j, |E i0 j|) * |x i0| ≤ η * |x i0| :=
      mul_le_mul_of_nonneg_right (hE i0) (abs_nonneg _)
    linarith [hb i0]
  have h1 : 0 < 1 - η := by linarith
  intro i
  calc |x i| ≤ |x i0| := hmax i
    _ ≤ β / (1 - η) := by rw [le_div_iff₀ h1]; linarith

/-- `y = E y + N (M y)`, `E = I − N M`. -/
theorem E_decomp (y : Fin 24 → ℝ) :
    y = ((1 : Matrix (Fin 24) (Fin 24) ℝ) - Nmat * pivotMatrix) *ᵥ y
      + Nmat *ᵥ (pivotMatrix *ᵥ y) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
  abel

theorem eta_lt_one : (ETA : ℝ) / SCALE < 1 := by unfold ETA SCALE; norm_num

/-- **Task 1a — the pivot system is nonsingular.** -/
theorem pivotMatrix_det_isUnit : IsUnit pivotMatrix.det := by
  obtain ⟨hE, -⟩ := estimates
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro y z hyz
  have h0 : pivotMatrix *ᵥ (y - z) = 0 := by rw [Matrix.mulVec_sub, hyz, sub_self]
  have hx : ∀ i, (y - z) i
      = (((1 : Matrix (Fin 24) (Fin 24) ℝ) - Nmat * pivotMatrix) *ᵥ (y - z)) i + 0 := by
    intro i
    have h := congrFun (E_decomp (y - z)) i
    rw [h0, Matrix.mulVec_zero, add_zero] at h
    rw [add_zero]; exact h
  have hb := abs_le_of_fixed eta_lt_one hE hx (β := 0) (fun _ => by simp)
  funext i
  have h := hb i
  rw [zero_div] at h
  have : (y - z) i = 0 := abs_nonpos_iff.mp h
  simpa [sub_eq_zero] using this

/-- **Task 1b — the pivots are within `2·10⁻²¹` of `pivotsNum`.** -/
theorem pivots_close_sharp : ∀ j, |pivots j - pivotsNum j| ≤ 2 / 10 ^ 21 := by
  have hdet := pivotMatrix_det_isUnit
  obtain ⟨hE, hR⟩ := estimates
  have hMx : pivotMatrix *ᵥ (pivots - pivotsNum) = -(fun k => rowFun k pivotsNum) := by
    funext i
    have h1 := rows_vanish hdet i
    rw [rowFun_eq_mulVec] at h1
    have h2 := rowFun_eq_mulVec i pivotsNum
    simp only [Matrix.mulVec_sub, Pi.sub_apply, Pi.neg_apply]
    linarith
  have hx : ∀ i, (pivots - pivotsNum) i
      = (((1 : Matrix (Fin 24) (Fin 24) ℝ) - Nmat * pivotMatrix) *ᵥ (pivots - pivotsNum)) i
        + (-(Nmat *ᵥ fun k => rowFun k pivotsNum)) i := by
    intro i
    have h := congrFun (E_decomp (pivots - pivotsNum)) i
    rw [hMx, Matrix.mulVec_neg] at h
    exact h
  have hb : ∀ i, |(-(Nmat *ᵥ fun k => rowFun k pivotsNum)) i| ≤ (RHO : ℝ) / SCALE := by
    intro i; rw [Pi.neg_apply, abs_neg]; exact hR i
  have h := abs_le_of_fixed eta_lt_one hE hx hb
  intro j
  calc |pivots j - pivotsNum j| = |(pivots - pivotsNum) j| := rfl
    _ ≤ ((RHO : ℝ) / SCALE) / (1 - (ETA : ℝ) / SCALE) := h j
    _ ≤ 2 / 10 ^ 21 := by unfold RHO ETA SCALE; norm_num

/-- Task 1b at the precision Task 5b needs. -/
theorem pivots_close_12 : ∀ j, |pivots j - pivotsNum j| ≤ 1 / 10 ^ 12 := fun j =>
  le_trans (pivots_close_sharp j) (by norm_num)

end Thomson.Task1b
