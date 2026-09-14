import Mathlib
import Thomson.Antiprism.Family

namespace Thomson
open Finset
open scoped RealInnerProductSpace

/-! ## 10. The derivative of the family energy; pinning `uStar` -/

/-- Derivative of `antiprismEnergy`. -/
noncomputable def antiprismEnergy' (u : ℝ) : ℝ :=
  (2 * Real.sqrt 2 + 1) / (Real.sqrt (1 - u)) ^ 3
    - 4 * (2 + Real.sqrt 2) / (Real.sqrt ((2 - Real.sqrt 2) + (2 + Real.sqrt 2) * u)) ^ 3
    - 4 * (2 - Real.sqrt 2) / (Real.sqrt ((2 + Real.sqrt 2) + (2 - Real.sqrt 2) * u)) ^ 3

theorem sqrt2_lt_two : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
theorem sqrt2_pos : 0 < Real.sqrt 2 := by positivity

/-- `d/du (c * (√(p + q u))⁻¹) = -(c q / 2) / (√(p+qu))^3`. -/
theorem hasDerivAt_c_inv_sqrt_affine (c p q u : ℝ) (hpos : 0 < p + q * u) :
    HasDerivAt (fun v => c * (Real.sqrt (p + q * v))⁻¹)
      (-(c * q / 2) / (Real.sqrt (p + q * u)) ^ 3) u := by
  have h1 : HasDerivAt (fun v => p + q * v) q u := by
    simpa using ((hasDerivAt_id u).const_mul q).const_add p
  have h2 := (h1.sqrt hpos.ne').inv (Real.sqrt_pos.mpr hpos).ne'
  have h3 := h2.const_mul c
  refine h3.congr_deriv ?_
  have hs : 0 < Real.sqrt (p + q * u) := Real.sqrt_pos.mpr hpos
  field_simp

theorem hasDerivAt_antiprismEnergy {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    HasDerivAt antiprismEnergy (antiprismEnergy' u) u := by
  have hs2 := sqrt2_pos; have hs2' := sqrt2_lt_two
  have e1 := hasDerivAt_c_inv_sqrt_affine (4 * Real.sqrt 2 + 2) 1 (-1) u (by linarith)
  have e2 := hasDerivAt_c_inv_sqrt_affine 8 (2 - Real.sqrt 2) (2 + Real.sqrt 2) u (by nlinarith)
  have e3 := hasDerivAt_c_inv_sqrt_affine 8 (2 + Real.sqrt 2) (2 - Real.sqrt 2) u (by nlinarith)
  have := (e1.add e2).add e3
  refine (this.congr_deriv ?_).congr_of_eventuallyEq ?_
  · unfold antiprismEnergy'
    simp only [show (1:ℝ) + -1 * u = 1 - u by ring]
    ring
  · exact Filter.Eventually.of_forall fun v => by
      simp only [Pi.add_apply, antiprismEnergy]; ring_nf

/-- `C / (√·)^3` is strictly decreasing on positives. -/
theorem div_cube_sqrt_lt {C x y : ℝ} (hC : 0 < C) (hx : 0 < x) (hxy : x < y) :
    C / (Real.sqrt y) ^ 3 < C / (Real.sqrt x) ^ 3 := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hlt : Real.sqrt x < Real.sqrt y := Real.sqrt_lt_sqrt hx.le hxy
  have hcube : (Real.sqrt x) ^ 3 < (Real.sqrt y) ^ 3 := by gcongr
  exact div_lt_div_of_pos_left hC (by positivity) hcube

/-- `antiprismEnergy'` is strictly increasing on `[0, 1)`. -/
theorem antiprismEnergy'_strictMonoOn : StrictMonoOn antiprismEnergy' (Set.Ico 0 1) := by
  intro u hu v hv huv
  have hs2 := sqrt2_pos; have hs2' := sqrt2_lt_two
  unfold antiprismEnergy'
  have t1 : (2 * Real.sqrt 2 + 1) / (Real.sqrt (1 - u)) ^ 3
      < (2 * Real.sqrt 2 + 1) / (Real.sqrt (1 - v)) ^ 3 :=
    div_cube_sqrt_lt (by positivity) (by linarith [hv.2]) (by linarith)
  have t2 : 4 * (2 + Real.sqrt 2) / (Real.sqrt ((2 - Real.sqrt 2) + (2 + Real.sqrt 2) * v)) ^ 3
      < 4 * (2 + Real.sqrt 2) / (Real.sqrt ((2 - Real.sqrt 2) + (2 + Real.sqrt 2) * u)) ^ 3 :=
    div_cube_sqrt_lt (by positivity) (by nlinarith [hu.1]) (by nlinarith)
  have t3 : 4 * (2 - Real.sqrt 2) / (Real.sqrt ((2 + Real.sqrt 2) + (2 - Real.sqrt 2) * v)) ^ 3
      < 4 * (2 - Real.sqrt 2) / (Real.sqrt ((2 + Real.sqrt 2) + (2 - Real.sqrt 2) * u)) ^ 3 :=
    div_cube_sqrt_lt (by nlinarith) (by nlinarith [hu.1]) (by nlinarith)
  linarith

theorem term_lt {coeff c X y : ℝ} (hc : coeff ≤ c) (hc0 : 0 < c) (hy : 0 < y) (hX : y ^ 2 < X) :
    coeff / (Real.sqrt X) ^ 3 < c / y ^ 3 := by
  have hlt : y < Real.sqrt X := (Real.lt_sqrt hy.le).mpr hX
  have hsX : 0 < Real.sqrt X := lt_trans hy hlt
  have hcube : y ^ 3 < (Real.sqrt X) ^ 3 := by gcongr
  calc coeff / (Real.sqrt X) ^ 3 ≤ c / (Real.sqrt X) ^ 3 :=
        div_le_div_of_nonneg_right hc (by positivity)
    _ < c / y ^ 3 := div_lt_div_of_pos_left hc0 (by positivity) hcube

theorem lt_term {coeff c X z : ℝ} (hc : c ≤ coeff) (hc0 : 0 < c) (hX0 : 0 < X) (hz : 0 < z)
    (hX : X < z ^ 2) : c / z ^ 3 < coeff / (Real.sqrt X) ^ 3 := by
  have hlt : Real.sqrt X < z := by rw [Real.sqrt_lt' hz]; exact hX
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hcube : (Real.sqrt X) ^ 3 < z ^ 3 := by gcongr
  calc c / z ^ 3 < c / (Real.sqrt X) ^ 3 := div_lt_div_of_pos_left hc0 (by positivity) hcube
    _ ≤ coeff / (Real.sqrt X) ^ 3 := div_le_div_of_nonneg_right hc (by positivity)

theorem antiprismEnergy'_neg : antiprismEnergy' (157 / 500) < 0 := by
  obtain ⟨s2l, s2u⟩ := sqrt2_bounds
  unfold antiprismEnergy'
  have t1 := term_lt (coeff := 2 * Real.sqrt 2 + 1) (c := 191421357 / 50000000)
    (X := 1 - 157 / 500) (y := 828251169 / 1000000000) (by linarith) (by norm_num) (by norm_num)
    (by norm_num)
  have t2 := lt_term (coeff := 4 * (2 + Real.sqrt 2)) (c := 85355339 / 6250000)
    (X := (2 - Real.sqrt 2) + (2 + Real.sqrt 2) * (157 / 500)) (z := 643787523 / 500000000)
    (by linarith) (by norm_num) (by nlinarith) (by norm_num) (by nlinarith)
  have t3 := lt_term (coeff := 4 * (2 - Real.sqrt 2)) (c := 58578643 / 25000000)
    (X := (2 + Real.sqrt 2) + (2 - Real.sqrt 2) * (157 / 500)) (z := 37937583 / 20000000)
    (by linarith) (by norm_num) (by nlinarith) (by norm_num) (by nlinarith)
  have hnum : (191421357 / 50000000 : ℝ) / (828251169 / 1000000000) ^ 3
      - 85355339 / 6250000 / (643787523 / 500000000) ^ 3
      - 58578643 / 25000000 / (37937583 / 20000000) ^ 3 < 0 := by norm_num
  linarith

theorem antiprismEnergy'_pos : 0 < antiprismEnergy' (1571 / 5000) := by
  obtain ⟨s2l, s2u⟩ := sqrt2_bounds
  unfold antiprismEnergy'
  have t1 := lt_term (coeff := 2 * Real.sqrt 2 + 1) (c := 47855339 / 12500000)
    (X := 1 - 1571 / 5000) (z := 33125217 / 40000000) (by linarith) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have t2 := term_lt (coeff := 4 * (2 + Real.sqrt 2)) (c := 341421357 / 25000000)
    (X := (2 - Real.sqrt 2) + (2 + Real.sqrt 2) * (1571 / 5000)) (y := 1287840181 / 1000000000)
    (by linarith) (by norm_num) (by norm_num) (by nlinarith)
  have t3 := term_lt (coeff := 4 * (2 - Real.sqrt 2)) (c := 14644661 / 6250000)
    (X := (2 + Real.sqrt 2) + (2 - Real.sqrt 2) * (1571 / 5000)) (y := 1896910029 / 1000000000)
    (by linarith) (by norm_num) (by norm_num) (by nlinarith)
  have hnum : (0:ℝ) < 47855339 / 12500000 / (33125217 / 40000000) ^ 3
      - 341421357 / 25000000 / (1287840181 / 1000000000) ^ 3
      - 14644661 / 6250000 / (1896910029 / 1000000000) ^ 3 := by norm_num
  linarith

theorem uStar_mem_Icc : uStar ∈ Set.Icc (157 / 500 : ℝ) (1571 / 5000) := by
  obtain ⟨hlo, hhi⟩ := uStar_mem
  have hmin := uStar_isMinOn
  have hmono := antiprismEnergy'_strictMonoOn
  constructor
  · by_contra hlt; push_neg at hlt
    have hanti : StrictAntiOn antiprismEnergy (Set.Icc (1 / 4) (157 / 500)) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      · exact antiprismEnergy_continuousOn.mono (Set.Icc_subset_Icc le_rfl (by norm_num))
      · intro x hx
        rw [interior_Icc] at hx
        rw [(hasDerivAt_antiprismEnergy (by linarith [hx.1]) (by linarith [hx.2])).deriv]
        have := hmono ⟨by linarith [hx.1], by linarith [hx.2]⟩ ⟨by norm_num, by norm_num⟩ hx.2
        linarith [antiprismEnergy'_neg]
    have h1 : antiprismEnergy (157 / 500) < antiprismEnergy uStar :=
      hanti ⟨hlo, hlt.le⟩ ⟨by norm_num, le_rfl⟩ hlt
    have h2 : antiprismEnergy uStar ≤ antiprismEnergy (157 / 500) :=
      hmin (show (157 / 500 : ℝ) ∈ window from ⟨by norm_num, by norm_num⟩)
    linarith
  · by_contra hlt; push_neg at hlt
    have hmono' : StrictMonoOn antiprismEnergy (Set.Icc (1571 / 5000) (1 / 2)) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      · exact antiprismEnergy_continuousOn.mono (Set.Icc_subset_Icc (by norm_num) le_rfl)
      · intro x hx
        rw [interior_Icc] at hx
        rw [(hasDerivAt_antiprismEnergy (by linarith [hx.1]) (by linarith [hx.2])).deriv]
        have := hmono ⟨by norm_num, by norm_num⟩ ⟨by linarith [hx.1], by linarith [hx.2]⟩ hx.1
        linarith [antiprismEnergy'_pos]
    have h2 : antiprismEnergy uStar ≤ antiprismEnergy (1571 / 5000) :=
      hmin (show (1571 / 5000 : ℝ) ∈ window from ⟨by norm_num, by norm_num⟩)
    have h3 : antiprismEnergy (1571 / 5000) < antiprismEnergy uStar :=
      hmono' ⟨le_rfl, by norm_num⟩ ⟨hlt.le, hhi⟩ hlt
    linarith

/-- The algebraic handle on `u*`: it is an interior minimiser, so the derivative vanishes.  This
is the equation `E′(u*) = 0` over which any exact three-point certificate (§16) is built. -/
theorem antiprismEnergy'_uStar : antiprismEnergy' uStar = 0 := by
  obtain ⟨hlo, hhi⟩ := uStar_mem_Icc
  have hd := hasDerivAt_antiprismEnergy (u := uStar) (by linarith) (by linarith)
  have hloc : IsLocalMin antiprismEnergy uStar := by
    have hmem : window ∈ nhds uStar := by
      apply Icc_mem_nhds <;> norm_num <;> linarith
    exact (uStar_isMinOn).isLocalMin hmem
  exact hloc.hasDerivAt_eq_zero hd

/-! ## 10b. Six digits of the family optimum -/

theorem lt_inv_sqrt {X z : ℝ} (hz : 0 < z) (hX0 : 0 < X) (hX : X < z ^ 2) :
    z⁻¹ < (Real.sqrt X)⁻¹ := by
  have hlt : Real.sqrt X < z := by rw [Real.sqrt_lt' hz]; exact hX
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  exact (inv_lt_inv₀ hz hsX).mpr hlt

theorem antiprismEnergy_lower_u1 : (196752879 / 10000000 : ℝ) < antiprismEnergy (157 / 500) := by
  obtain ⟨s2l, s2u⟩ := sqrt2_bounds
  unfold antiprismEnergy
  have t1 : (47855339 / 6250000 : ℝ) * (82825117 / 100000000)⁻¹
      < (4 * Real.sqrt 2 + 2) * (Real.sqrt (1 - 157 / 500))⁻¹ :=
    mul_lt_mul'' (by linarith) (lt_inv_sqrt (by norm_num) (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
  have t2 : 8 * (643787523 / 500000000 : ℝ)⁻¹
      < 8 * (Real.sqrt ((2 - Real.sqrt 2) + (2 + Real.sqrt 2) * (157 / 500)))⁻¹ := by
    apply mul_lt_mul_of_pos_left _ (by norm_num)
    exact lt_inv_sqrt (by norm_num) (by nlinarith) (by nlinarith)
  have t3 : 8 * (37937583 / 20000000 : ℝ)⁻¹
      < 8 * (Real.sqrt ((2 + Real.sqrt 2) + (2 - Real.sqrt 2) * (157 / 500)))⁻¹ := by
    apply mul_lt_mul_of_pos_left _ (by norm_num)
    exact lt_inv_sqrt (by norm_num) (by nlinarith) (by nlinarith)
  have hnum : (196752879 / 10000000 : ℝ) < (47855339 / 6250000) * (82825117 / 100000000)⁻¹
      + 8 * (643787523 / 500000000)⁻¹ + 8 * (37937583 / 20000000)⁻¹ := by norm_num
  linarith

theorem antiprismEnergy'_ge : -(1 / 250 : ℝ) < antiprismEnergy' (157 / 500) := by
  obtain ⟨s2l, s2u⟩ := sqrt2_bounds
  unfold antiprismEnergy'
  have t1 := lt_term (coeff := 2 * Real.sqrt 2 + 1) (c := 47855339 / 12500000)
    (X := 1 - 157 / 500) (z := 82825117 / 100000000) (by linarith) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have t2 := term_lt (coeff := 4 * (2 + Real.sqrt 2)) (c := 341421357 / 25000000)
    (X := (2 - Real.sqrt 2) + (2 + Real.sqrt 2) * (157 / 500)) (y := 643787521 / 500000000)
    (by linarith) (by norm_num) (by norm_num) (by nlinarith)
  have t3 := term_lt (coeff := 4 * (2 - Real.sqrt 2)) (c := 14644661 / 6250000)
    (X := (2 + Real.sqrt 2) + (2 - Real.sqrt 2) * (157 / 500)) (y := 474219787 / 250000000)
    (by linarith) (by norm_num) (by norm_num) (by nlinarith)
  have hnum : -(1 / 250 : ℝ) < 47855339 / 12500000 / (82825117 / 100000000) ^ 3
      - 341421357 / 25000000 / (643787521 / 500000000) ^ 3
      - 14644661 / 6250000 / (474219787 / 250000000) ^ 3 := by norm_num
  linarith

/-- Six digits of the conjectured optimum: `19.675287 < E(u*) < 19.6753`. -/
theorem antiprismEnergy_uStar_gt : (19675287 / 1000000 : ℝ) < antiprismEnergy uStar := by
  obtain ⟨hlo, hhi⟩ := uStar_mem_Icc
  have hmono := antiprismEnergy'_strictMonoOn
  have key := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc (157 / 500 : ℝ) (1571 / 5000))
    (antiprismEnergy_continuousOn.mono (Set.Icc_subset_Icc (by norm_num) (by norm_num)))
    (fun x hx => by
      rw [interior_Icc] at hx
      exact (hasDerivAt_antiprismEnergy (by linarith [hx.1])
        (by linarith [hx.2])).differentiableAt.differentiableWithinAt)
    (C := -(1 / 250)) (fun x hx => by
      rw [interior_Icc] at hx
      rw [(hasDerivAt_antiprismEnergy (by linarith [hx.1]) (by linarith [hx.2])).deriv]
      have := hmono ⟨by norm_num, by norm_num⟩ ⟨by linarith [hx.1], by linarith [hx.2]⟩ hx.1
      linarith [antiprismEnergy'_ge])
    (157 / 500) ⟨le_rfl, by norm_num⟩ uStar ⟨hlo, hhi⟩ hlo
  have h1 := antiprismEnergy_lower_u1
  nlinarith [key, h1, hlo, hhi]

theorem antiprismEnergy_uStar_lt : antiprismEnergy uStar < 19.6753 := by
  have h : antiprismEnergy uStar ≤ antiprismEnergy (196 / 625) :=
    uStar_isMinOn (show (196 / 625 : ℝ) ∈ window from ⟨by norm_num, by norm_num⟩)
  have h2 : antiprismEnergy ((14 / 25) ^ 2) < 19.6753 := antiprismEnergy_bound
  rw [show ((14:ℝ) / 25) ^ 2 = 196 / 625 by norm_num] at h2
  exact lt_of_le_of_lt h h2

/-! ## 11. Local minimality within the family -/

/-- Local minimality within the antiprism family: every antiprism whose parameter is within
`1/20` of `uStar` has energy at least `antiprismEnergy uStar`. -/
theorem antiprism_local_min : ∃ ε > 0, ∃ u₀ ∈ Set.Ioo (0:ℝ) 1,
    ∀ x : Fin 8 → EuclideanSpace ℝ (Fin 3), Admissible x →
      (∃ h, |h ^ 2 - u₀| < ε ∧ x = antiprism h) → antiprismEnergy u₀ ≤ energy x := by
  obtain ⟨hlo, hhi⟩ := uStar_mem_Icc
  refine ⟨1 / 20, by norm_num, uStar, ⟨by linarith, by linarith⟩, ?_⟩
  rintro x _ ⟨h, hh, rfl⟩
  rw [abs_lt] at hh
  have h1 : h ^ 2 < 1 := by linarith
  rw [antiprism_energy_eq' h1]
  exact uStar_isMinOn (show h ^ 2 ∈ window from ⟨by linarith, by linarith⟩)

end Thomson
