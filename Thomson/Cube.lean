import Mathlib
import Thomson.Basic

namespace Thomson
open Finset
open scoped RealInnerProductSpace

/-! ## 5. The cube -/

noncomputable def c3 : ℝ := (Real.sqrt 3)⁻¹
theorem c3_sq : c3 ^ 2 = 1 / 3 := by
  rw [c3, inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num
theorem c3_pos : 0 < c3 := by rw [c3]; positivity
noncomputable def cube : Fin 8 → EuclideanSpace ℝ (Fin 3) :=
  ![ !₂[c3, c3, c3],   !₂[c3, c3, -c3],   !₂[c3, -c3, c3],   !₂[c3, -c3, -c3],
     !₂[-c3, c3, c3],  !₂[-c3, c3, -c3],  !₂[-c3, -c3, c3],  !₂[-c3, -c3, -c3] ]

theorem cube0 : cube 0 = !₂[c3, c3, c3] := rfl
theorem cube1 : cube 1 = !₂[c3, c3, -c3] := rfl
theorem cube2 : cube 2 = !₂[c3, -c3, c3] := rfl
theorem cube3 : cube 3 = !₂[c3, -c3, -c3] := rfl
theorem cube4 : cube 4 = !₂[-c3, c3, c3] := rfl
theorem cube5 : cube 5 = !₂[-c3, c3, -c3] := rfl
theorem cube6 : cube 6 = !₂[-c3, -c3, c3] := rfl
theorem cube7 : cube 7 = !₂[-c3, -c3, -c3] := rfl

theorem sqrt4 : Real.sqrt 4 = 2 := by
  rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
theorem inv_sqrt_43 : (Real.sqrt (4 / 3))⁻¹ = Real.sqrt 3 / 2 := by
  rw [Real.sqrt_div (by norm_num), sqrt4, inv_div]
theorem inv_sqrt_83 : (Real.sqrt (8 / 3))⁻¹ = Real.sqrt 6 / 4 := by
  apply inv_eq_of_mul_eq_one_right
  rw [mul_div_assoc', ← Real.sqrt_mul (by norm_num), show (8:ℝ) / 3 * 6 = 4 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  norm_num

theorem cube_energy : energy cube = 6 * Real.sqrt 3 + 3 * Real.sqrt 6 + 2 := by
  have i0 : Finset.Ioi (0 : Fin 8) = {1, 2, 3, 4, 5, 6, 7} := by decide
  have i1 : Finset.Ioi (1 : Fin 8) = {2, 3, 4, 5, 6, 7} := by decide
  have i2 : Finset.Ioi (2 : Fin 8) = {3, 4, 5, 6, 7} := by decide
  have i3 : Finset.Ioi (3 : Fin 8) = {4, 5, 6, 7} := by decide
  have i4 : Finset.Ioi (4 : Fin 8) = {5, 6, 7} := by decide
  have i5 : Finset.Ioi (5 : Fin 8) = {6, 7} := by decide
  have i6 : Finset.Ioi (6 : Fin 8) = {7} := by decide
  have i7 : Finset.Ioi (7 : Fin 8) = ∅ := by decide
  simp only [energy, Fin.sum_univ_eight, i0, i1, i2, i3, i4, i5, i6, i7,
    Finset.sum_empty, Finset.sum_singleton]
  repeat rw [Finset.sum_insert (by decide)]
  simp only [Finset.sum_singleton, cube0, cube1, cube2, cube3, cube4, cube5, cube6, cube7,
    sub_e3, norm_e3]
  ring_nf
  simp only [c3_sq]
  norm_num [inv_sqrt_43, inv_sqrt_83, sqrt4]
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8:ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have h6 : Real.sqrt 6 = Real.sqrt 3 * Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have key : (2 * Real.sqrt 2)⁻¹ = Real.sqrt 2 / 4 := by
    field_simp; nlinarith [h2]
  rw [h8, h6]; simp only [div_eq_mul_inv, key]; ring

theorem cube_onSphere : OnSphere cube := by
  intro i
  fin_cases i <;> simp [cube, norm_e3] <;> ring_nf <;> simp [c3_sq] <;> norm_num

theorem cube_injective : Function.Injective cube := by
  have hc := c3_pos
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp only [cube0, cube1, cube2, cube3, cube4, cube5, cube6, cube7] at h <;>
    first
    | rfl
    | (obtain ⟨h0, h1, h2⟩ := e3_inj h; linarith)

theorem cube_admissible : Admissible cube := ⟨cube_onSphere, cube_injective⟩

end Thomson
