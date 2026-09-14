import Thomson.Antiprism.Derivative

namespace Thomson

/-! # Sharp enclosures of the algebraic constants (Task 1b)

`Thomson.Certificate.Assemble`, Task 1b: the residual bound for the pivot enclosure is limited only by
the accuracy of the enclosures of `u*` and `√2`; thirteen digits of `u*` suffice.  This file
sharpens `sqrt2_bounds` to 28 digits and `uStar_mem_Icc` to thirteen, by exactly the argument of
`Thomson.Antiprism.Derivative` (the sign of `antiprismEnergy'` at two rationals straddling `u*`). -/

/-- `√2` to 28 digits. -/
theorem sqrt2_bounds_sharp :
    (7071067811865475244008443621 / 5000000000000000000000000000 : ℝ) < Real.sqrt 2 ∧
      Real.sqrt 2 < 14142135623730950488016887243 / 10000000000000000000000000000 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem antiprismEnergy'_neg_sharp :
    antiprismEnergy' (785223419723 / 2500000000000) < 0 := by
  obtain ⟨s2l, s2u⟩ := sqrt2_bounds_sharp
  unfold antiprismEnergy'
  have t1 := term_lt (coeff := 2 * Real.sqrt 2 + 1)
    (c := 2 * (14142135623730950488016887243 / 10000000000000000000000000000) + 1)
    (X := 1 - 785223419723 / 2500000000000)
    (y := 517623261328431075755049 / 625000000000000000000000)
    (by linarith) (by norm_num) (by norm_num) (by norm_num)
  have t2 := lt_term (coeff := 4 * (2 + Real.sqrt 2))
    (c := 8 + 4 * (7071067811865475244008443621 / 5000000000000000000000000000))
    (X := (2 - Real.sqrt 2) + (2 + Real.sqrt 2) * (785223419723 / 2500000000000))
    (z := 6438467630716574652851219 / 5000000000000000000000000)
    (by linarith) (by norm_num) (by nlinarith) (by norm_num) (by nlinarith)
  have t3 := lt_term (coeff := 4 * (2 - Real.sqrt 2))
    (c := 8 - 4 * (14142135623730950488016887243 / 10000000000000000000000000000))
    (X := (2 + Real.sqrt 2) + (2 - Real.sqrt 2) * (785223419723 / 2500000000000))
    (z := 148194761523646685648043 / 78125000000000000000000)
    (by linarith) (by norm_num) (by nlinarith) (by norm_num) (by nlinarith)
  have hnum : (2 * (14142135623730950488016887243 / 10000000000000000000000000000) + 1)
        / (517623261328431075755049 / 625000000000000000000000 : ℝ) ^ 3
      - (8 + 4 * (7071067811865475244008443621 / 5000000000000000000000000000))
        / (6438467630716574652851219 / 5000000000000000000000000 : ℝ) ^ 3
      - (8 - 4 * (14142135623730950488016887243 / 10000000000000000000000000000))
        / (148194761523646685648043 / 78125000000000000000000 : ℝ) ^ 3 < 0 := by norm_num
  linarith

theorem antiprismEnergy'_pos_sharp :
    0 < antiprismEnergy' (3140893678893 / 10000000000000) := by
  obtain ⟨s2l, s2u⟩ := sqrt2_bounds_sharp
  unfold antiprismEnergy'
  have t1 := lt_term (coeff := 2 * Real.sqrt 2 + 1)
    (c := 2 * (7071067811865475244008443621 / 5000000000000000000000000000) + 1)
    (X := 1 - 3140893678893 / 10000000000000)
    (z := 4140986090627146745572223 / 5000000000000000000000000)
    (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t2 := term_lt (coeff := 4 * (2 + Real.sqrt 2))
    (c := 8 + 4 * (14142135623730950488016887243 / 10000000000000000000000000000))
    (X := (2 - Real.sqrt 2) + (2 + Real.sqrt 2) * (3140893678893 / 10000000000000))
    (y := 2575387052286895002922523 / 2000000000000000000000000)
    (by linarith) (by norm_num) (by norm_num) (by nlinarith)
  have t3 := term_lt (coeff := 4 * (2 - Real.sqrt 2))
    (c := 8 - 4 * (7071067811865475244008443621 / 5000000000000000000000000000))
    (X := (2 + Real.sqrt 2) + (2 - Real.sqrt 2) * (3140893678893 / 10000000000000))
    (y := 9484464737513465084887627 / 5000000000000000000000000)
    (by linarith) (by norm_num) (by norm_num) (by nlinarith)
  have hnum : (0:ℝ) < (2 * (7071067811865475244008443621 / 5000000000000000000000000000) + 1)
        / (4140986090627146745572223 / 5000000000000000000000000 : ℝ) ^ 3
      - (8 + 4 * (14142135623730950488016887243 / 10000000000000000000000000000))
        / (2575387052286895002922523 / 2000000000000000000000000 : ℝ) ^ 3
      - (8 - 4 * (7071067811865475244008443621 / 5000000000000000000000000000))
        / (9484464737513465084887627 / 5000000000000000000000000 : ℝ) ^ 3 := by norm_num
  linarith

/-- **Thirteen digits of `u*`**: `u* = 0.3140893678892…`.  Same argument as `uStar_mem_Icc`. -/
theorem uStar_mem_Icc_sharp :
    uStar ∈ Set.Icc (785223419723 / 2500000000000 : ℝ) (3140893678893 / 10000000000000) := by
  obtain ⟨hlo, hhi⟩ := uStar_mem_Icc
  have hmin := uStar_isMinOn
  have hmono := antiprismEnergy'_strictMonoOn
  constructor
  · by_contra hlt; push Not at hlt
    have hanti : StrictAntiOn antiprismEnergy
        (Set.Icc (157 / 500) (785223419723 / 2500000000000)) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      · exact antiprismEnergy_continuousOn.mono
          (Set.Icc_subset_Icc (by norm_num) (by norm_num))
      · intro x hx
        rw [interior_Icc] at hx
        rw [(hasDerivAt_antiprismEnergy (by linarith [hx.1]) (by linarith [hx.2])).deriv]
        have := hmono ⟨by linarith [hx.1], by linarith [hx.2]⟩
          (show (785223419723 / 2500000000000 : ℝ) ∈ Set.Ico (0:ℝ) 1 from
            ⟨by norm_num, by norm_num⟩) hx.2
        linarith [antiprismEnergy'_neg_sharp]
    have h1 : antiprismEnergy (785223419723 / 2500000000000) < antiprismEnergy uStar :=
      hanti (Set.mem_Icc.mpr ⟨hlo, hlt.le⟩)
        (Set.mem_Icc.mpr ⟨by norm_num, le_rfl⟩) hlt
    have h2 : antiprismEnergy uStar ≤ antiprismEnergy (785223419723 / 2500000000000) :=
      hmin (show (785223419723 / 2500000000000 : ℝ) ∈ window from
        Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
    linarith
  · by_contra hlt; push Not at hlt
    have hmono' : StrictMonoOn antiprismEnergy
        (Set.Icc (3140893678893 / 10000000000000) (1571 / 5000)) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      · exact antiprismEnergy_continuousOn.mono
          (Set.Icc_subset_Icc (by norm_num) (by norm_num))
      · intro x hx
        rw [interior_Icc] at hx
        rw [(hasDerivAt_antiprismEnergy (by linarith [hx.1]) (by linarith [hx.2])).deriv]
        have := hmono (show (3140893678893 / 10000000000000 : ℝ) ∈ Set.Ico (0:ℝ) 1 from
            ⟨by norm_num, by norm_num⟩) ⟨by linarith [hx.1], by linarith [hx.2]⟩ hx.1
        linarith [antiprismEnergy'_pos_sharp]
    have h2 : antiprismEnergy uStar ≤ antiprismEnergy (3140893678893 / 10000000000000) :=
      hmin (show (3140893678893 / 10000000000000 : ℝ) ∈ window from
        Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
    have h3 : antiprismEnergy (3140893678893 / 10000000000000) < antiprismEnergy uStar :=
      hmono' (Set.mem_Icc.mpr ⟨le_rfl, by norm_num⟩)
        (Set.mem_Icc.mpr ⟨hlt.le, hhi⟩) hlt
    linarith

theorem uStar_lower : (785223419723 / 2500000000000 : ℝ) ≤ uStar := uStar_mem_Icc_sharp.1
theorem uStar_upper : uStar ≤ 3140893678893 / 10000000000000 := uStar_mem_Icc_sharp.2

end Thomson
