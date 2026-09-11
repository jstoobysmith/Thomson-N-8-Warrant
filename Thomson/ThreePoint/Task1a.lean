import Thomson.ThreePoint.Perturb
import Thomson.ThreePoint.Sharp

namespace Thomson
open Finset Matrix

/-! # Task 1a: the bound row of the pivot system

`S3 k (1,1,1)` is the all-ones matrix for `k = 0` and *zero* for `1 ≤ k ≤ 5`
(`S3_all_one_apply`).  So the bound row of `pivotMatrix` sees only the `k = 0` block: every pivot
whose slot lies in a block `k ≥ 1` contributes exactly `0`.  That is 17 of the 24 entries of the
row, obtained exactly, with no interval arithmetic. -/

theorem S3_all_one_eq_zero {k : ℕ} (hk1 : k ≠ 0) (hk : k ≤ 5) :
    S3 k 1 1 1 = 0 := by
  ext i l
  rw [S3_all_one_apply _ hk]
  simp [hk1]

/-- A pivot whose slot lies in a block `k ≥ 1` has no effect on `F(1,1,1)`. -/
theorem Gh_all_one_eq_zero {j : Fin 24} (h : (slot j).1 ≠ 0) : Gh j 1 1 1 = 0 := by
  unfold Gh
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases eq_or_ne ((k : ℕ)) 0 with hk | hk
  · refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    have hz : eH j (k : ℕ) (a : ℕ) (b : ℕ) = 0 := by
      unfold eH
      rw [if_neg]
      rintro (h1 | h1) <;> exact h (by rw [h1]; exact hk)
    rw [hz, zero_mul]
  · have hz : S3 (k : ℕ) 1 1 1 = 0 := S3_all_one_eq_zero hk (by omega)
    simp [hz]

/-- The bound row of `pivotMatrix` vanishes at every pivot outside the `k = 0` block. -/
theorem pivotMatrix_bound_row_eq_zero {j : Fin 24} (h : (slot j).1 ≠ 0) :
    pivotMatrix 0 j = 0 := by
  rw [pivotMatrix_bound_row, Gh_all_one_eq_zero h, mul_zero]

/-- The seventeen zero entries of the bound row, explicitly. -/
theorem pivotMatrix_bound_row_zeros (j : Fin 24) (hj : 7 ≤ (j : ℕ)) : pivotMatrix 0 j = 0 := by
  refine pivotMatrix_bound_row_eq_zero ?_
  fin_cases j <;> revert hj <;> decide

end Thomson
