import Mathlib
import Thomson.Antiprism.Cube

namespace Thomson
open Finset
open scoped RealInnerProductSpace

/-! ## 6. The square antiprism -/

noncomputable def antiprism (h : ℝ) : Fin 8 → EuclideanSpace ℝ (Fin 3) :=
  let r : ℝ := Real.sqrt (1 - h ^ 2)
  let s : ℝ := r * Real.sqrt 2 / 2
  ![ !₂[r, 0, h],   !₂[0, r, h],    !₂[-r, 0, h],   !₂[0, -r, h],
     !₂[s, s, -h],  !₂[-s, s, -h],  !₂[-s, -s, -h], !₂[s, -s, -h] ]

noncomputable def antiprismEnergy (u : ℝ) : ℝ :=
  (4 * Real.sqrt 2 + 2) * (Real.sqrt (1 - u))⁻¹
    + 8 * (Real.sqrt ((2 - Real.sqrt 2) + (2 + Real.sqrt 2) * u))⁻¹
    + 8 * (Real.sqrt ((2 + Real.sqrt 2) + (2 - Real.sqrt 2) * u))⁻¹

section ap
variable (h : ℝ)
local notation "r" => Real.sqrt (1 - h ^ 2)
local notation "s" => Real.sqrt (1 - h ^ 2) * Real.sqrt 2 / 2
theorem ap0 : antiprism h 0 = !₂[r, 0, h] := rfl
theorem ap1 : antiprism h 1 = !₂[0, r, h] := rfl
theorem ap2 : antiprism h 2 = !₂[-r, 0, h] := rfl
theorem ap3 : antiprism h 3 = !₂[0, -r, h] := rfl
theorem ap4 : antiprism h 4 = !₂[s, s, -h] := rfl
theorem ap5 : antiprism h 5 = !₂[-s, s, -h] := rfl
theorem ap6 : antiprism h 6 = !₂[-s, -s, -h] := rfl
theorem ap7 : antiprism h 7 = !₂[s, -s, -h] := rfl
end ap

theorem antiprism_energy_eq' {h : ℝ} (h1 : h ^ 2 < 1) :
    energy (antiprism h) = antiprismEnergy (h ^ 2) := by
  have hu : 0 < 1 - h ^ 2 := by linarith
  have hr2 : Real.sqrt (1 - h ^ 2) ^ 2 = 1 - h ^ 2 := Real.sq_sqrt hu.le
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
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
  simp only [Finset.sum_singleton, ap0, ap1, ap2, ap3, ap4, ap5, ap6, ap7, sub_e3, norm_e3,
    antiprismEnergy]
  ring_nf
  simp only [hr2, h2]
  ring_nf
  have hr : 0 < Real.sqrt (1 - h ^ 2) := Real.sqrt_pos.mpr hu
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have e1 : Real.sqrt (2 - h ^ 2 * 2) = Real.sqrt 2 * Real.sqrt (1 - h ^ 2) := by
    rw [← Real.sqrt_mul (by norm_num)]; ring_nf
  have e2 : Real.sqrt (4 - h ^ 2 * 4) = 2 * Real.sqrt (1 - h ^ 2) := by
    rw [show (4:ℝ) - h ^ 2 * 4 = 2 ^ 2 * (1 - h ^ 2) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have hi : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    field_simp; linarith [h22]
  have key : (Real.sqrt 2 * Real.sqrt (1 - h ^ 2))⁻¹ * 8 + (2 * Real.sqrt (1 - h ^ 2))⁻¹ * 4
      = Real.sqrt 2 * (Real.sqrt (1 - h ^ 2))⁻¹ * 4 + (Real.sqrt (1 - h ^ 2))⁻¹ * 2 := by
    rw [mul_inv, mul_inv, hi]; ring
  rw [e1, e2]
  linarith [key]

theorem antiprism_energy_eq {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    energy (antiprism h) = antiprismEnergy (h ^ 2) :=
  antiprism_energy_eq' (by nlinarith)

theorem norm_e3_eq_one {a b c : ℝ} (habc : a ^ 2 + b ^ 2 + c ^ 2 = 1) :
    ‖(!₂[a, b, c] : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
  rw [norm_e3, habc, Real.sqrt_one]

theorem antiprism_onSphere {h : ℝ} (h0 : 0 < h) (h1 : h < 1) : OnSphere (antiprism h) := by
  have hu : 0 < 1 - h ^ 2 := by nlinarith
  have hr2 : Real.sqrt (1 - h ^ 2) ^ 2 = 1 - h ^ 2 := Real.sq_sqrt hu.le
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  intro i
  fin_cases i
  · show ‖antiprism h 0‖ = 1; rw [ap0]; exact norm_e3_eq_one (by linear_combination hr2)
  · show ‖antiprism h 1‖ = 1; rw [ap1]; exact norm_e3_eq_one (by linear_combination hr2)
  · show ‖antiprism h 2‖ = 1; rw [ap2]; exact norm_e3_eq_one (by linear_combination hr2)
  · show ‖antiprism h 3‖ = 1; rw [ap3]; exact norm_e3_eq_one (by linear_combination hr2)
  · show ‖antiprism h 4‖ = 1; rw [ap4]
    exact norm_e3_eq_one (by linear_combination (Real.sqrt 2 ^ 2 / 2) * hr2 + ((1 - h ^ 2) / 2) * h2)
  · show ‖antiprism h 5‖ = 1; rw [ap5]
    exact norm_e3_eq_one (by linear_combination (Real.sqrt 2 ^ 2 / 2) * hr2 + ((1 - h ^ 2) / 2) * h2)
  · show ‖antiprism h 6‖ = 1; rw [ap6]
    exact norm_e3_eq_one (by linear_combination (Real.sqrt 2 ^ 2 / 2) * hr2 + ((1 - h ^ 2) / 2) * h2)
  · show ‖antiprism h 7‖ = 1; rw [ap7]
    exact norm_e3_eq_one (by linear_combination (Real.sqrt 2 ^ 2 / 2) * hr2 + ((1 - h ^ 2) / 2) * h2)

theorem antiprism_injective {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    Function.Injective (antiprism h) := by
  have hu : 0 < 1 - h ^ 2 := by nlinarith
  have hr : 0 < Real.sqrt (1 - h ^ 2) := Real.sqrt_pos.mpr hu
  have hs : 0 < Real.sqrt (1 - h ^ 2) * Real.sqrt 2 / 2 := by positivity
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [ap0, ap1, ap2, ap3, ap4, ap5, ap6, ap7] at hij <;>
    first
    | rfl
    | (obtain ⟨e0, e1, e2⟩ := e3_inj hij; linarith)

theorem antiprism_admissible {h : ℝ} (h0 : 0 < h) (h1 : h < 1) : Admissible (antiprism h) :=
  ⟨antiprism_onSphere h0 h1, antiprism_injective h0 h1⟩

/-! ## 7. Certified upper bound; the cube is not optimal -/

theorem sqrt2_bounds : (141421356 / 100000000 : ℝ) < Real.sqrt 2 ∧
    Real.sqrt 2 < 141421357 / 100000000 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem inv_sqrt_lt {X y : ℝ} (hy : 0 < y) (hX : y ^ 2 < X) : (Real.sqrt X)⁻¹ < y⁻¹ := by
  have hlt : y < Real.sqrt X := (Real.lt_sqrt hy.le).mpr hX
  have hX0 : 0 < Real.sqrt X := lt_trans hy hlt
  exact (inv_lt_inv₀ hX0 hy).mpr hlt

theorem antiprismEnergy_bound : antiprismEnergy ((14 / 25) ^ 2) < 19.6753 := by
  obtain ⟨s2l, s2u⟩ := sqrt2_bounds
  unfold antiprismEnergy
  have t1 : (4 * Real.sqrt 2 + 2) * (Real.sqrt (1 - (14 / 25) ^ 2))⁻¹
      < (191421357 / 25000000) * (4142463 / 5000000)⁻¹ :=
    mul_lt_mul'' (by linarith) (inv_sqrt_lt (by norm_num) (by norm_num))
      (by positivity) (by positivity)
  have t2 : 8 * (Real.sqrt ((2 - Real.sqrt 2) + (2 + Real.sqrt 2) * (14 / 25) ^ 2))⁻¹
      < 8 * (6435223 / 5000000)⁻¹ := by
    apply mul_lt_mul_of_pos_left _ (by norm_num)
    apply inv_sqrt_lt (by norm_num)
    nlinarith [s2u]
  have t3 : 8 * (Real.sqrt ((2 + Real.sqrt 2) + (2 - Real.sqrt 2) * (14 / 25) ^ 2))⁻¹
      < 8 * (94840869 / 50000000)⁻¹ := by
    apply mul_lt_mul_of_pos_left _ (by norm_num)
    apply inv_sqrt_lt (by norm_num)
    nlinarith [s2l]
  have total : (191421357 / 25000000 : ℝ) * (4142463 / 5000000)⁻¹ + 8 * (6435223 / 5000000)⁻¹
      + 8 * (94840869 / 50000000)⁻¹ < 19.6753 := by norm_num
  linarith

theorem thomson_eight_upper : thomsonInf 8 < 19.6753 := by
  have hadm := antiprism_admissible (h := 14 / 25) (by norm_num) (by norm_num)
  have hle : thomsonInf 8 ≤ energy (antiprism (14 / 25)) := by
    apply csInf_le
    · exact ⟨0, by rintro e ⟨x, -, rfl⟩; exact energy_nonneg x⟩
    · exact ⟨_, hadm, rfl⟩
  rw [antiprism_energy_eq (by norm_num) (by norm_num)] at hle
  exact lt_of_le_of_lt hle antiprismEnergy_bound

theorem cube_not_minimal : thomsonInf 8 < energy cube := by
  have h3 : (1732 / 1000 : ℝ) < Real.sqrt 3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h6 : (2449 / 1000 : ℝ) < Real.sqrt 6 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  rw [cube_energy]
  linarith [thomson_eight_upper]

/-! ## 8. The optimal parameter `uStar`, and the easy half of the main theorem -/

/-- The parameter window `[1/4, 1/2]` for `u = h²`; the conjectured optimum `u* ≈ 0.314` lies inside. -/
def window : Set ℝ := Set.Icc (1 / 4) (1 / 2)

theorem antiprismEnergy_continuousOn : ContinuousOn antiprismEnergy window := by
  unfold antiprismEnergy window
  have hs2 : (0:ℝ) < Real.sqrt 2 := by positivity
  have hs2' : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  refine ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_
  · refine ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ (by fun_prop) ?_)
    intro u hu; exact (Real.sqrt_pos.mpr (by linarith [hu.2])).ne'
  · refine ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ (by fun_prop) ?_)
    intro u hu; exact (Real.sqrt_pos.mpr (by nlinarith [hu.1, hs2, hs2'])).ne'
  · refine ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ (by fun_prop) ?_)
    intro u hu; exact (Real.sqrt_pos.mpr (by nlinarith [hu.1, hs2, hs2'])).ne'

theorem exists_uStar : ∃ u ∈ window, IsMinOn antiprismEnergy window u :=
  isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr (by norm_num)) antiprismEnergy_continuousOn

/-- The optimal antiprism parameter: a minimiser of `antiprismEnergy` on the window. -/
noncomputable def uStar : ℝ := Classical.choose exists_uStar
theorem uStar_mem : uStar ∈ window := (Classical.choose_spec exists_uStar).1
theorem uStar_isMinOn : IsMinOn antiprismEnergy window uStar := (Classical.choose_spec exists_uStar).2

/-- The easy half of the main theorem: the family's best member is an upper bound. -/
theorem thomsonInf_le_uStar : thomsonInf 8 ≤ antiprismEnergy uStar := by
  obtain ⟨hlo, hhi⟩ := uStar_mem
  have hu0 : 0 < uStar := by linarith
  set h := Real.sqrt uStar with hh
  have h0 : 0 < h := Real.sqrt_pos.mpr hu0
  have h1 : h < 1 := by rw [hh, Real.sqrt_lt' (by norm_num)]; linarith
  have hsq : h ^ 2 = uStar := Real.sq_sqrt hu0.le
  have hle : thomsonInf 8 ≤ energy (antiprism h) := by
    apply csInf_le
    · exact ⟨0, by rintro e ⟨x, -, rfl⟩; exact energy_nonneg x⟩
    · exact ⟨_, antiprism_admissible h0 h1, rfl⟩
  rwa [antiprism_energy_eq h0 h1, hsq] at hle


/-- The *equilateral* square antiprism: the parameter `u_e = (2√2 − 1)/7` at which the square
edge and the lateral edge coincide, so that all sixteen short edges have the common length
`√((16 − 4√2)/7) = 1.2155625…`.

This configuration is the one the linear-programming dual points at (its ideal pair-distance
distribution asks for sixteen equal shortest edges), and it is also the Tammes optimum for
eight points — no eight points on `S²` have a larger shortest distance.  It is therefore the
natural analytic candidate for a counterexample.  It is not one: it loses to the Thomson
antiprism by `0.0499`, twice the entire linear-programming gap. -/
noncomputable def uEquilateral : ℝ := (2 * Real.sqrt 2 - 1) / 7

theorem uEquilateral_mem : uEquilateral ∈ window := by
  obtain ⟨hlo, hhi⟩ := sqrt2_bounds
  rw [window, Set.mem_Icc, uEquilateral]
  constructor <;> linarith

/-- The equilateral (Tammes) antiprism does not beat the Thomson antiprism. -/
theorem equilateral_not_better : antiprismEnergy uStar ≤ antiprismEnergy uEquilateral :=
  uStar_isMinOn uEquilateral_mem

end Thomson
