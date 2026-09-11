import Thomson.Derivative

/-! # Task 5b, step 4: `u*` to thirty-two digits

The box covering evaluates the certificate at rational points, and every coefficient of the
certificate is a polynomial in `u*` (`Bpoly`).  The margin to be certified is as small as
`10⁻⁹` (at the face of a `rhoLocal`-cube), and the entries of the constant matrices `M_k` move by
`O(10)` per unit of `u*`, so the thirteen digits of `Thomson.uStar_mem_Icc_sharp` leave an
uncertainty of order `10⁻¹¹` — only two orders below the margin, and interval arithmetic loses that
in the first few operations.  This file removes the issue: `u*` to `3·10⁻³²`, by exactly the
argument of `Thomson.Enclosure` (the sign of `antiprismEnergy'` at two rationals straddling `u*`,
plus the strict monotonicity of `antiprismEnergy'`), with `√2` to `45` digits.

The same digits are what a sharpened Task 1b needs (see `Thomson.Tri5b.Reduce`). -/

namespace Thomson.Tri5b

open Thomson

/-- `√2` to 45 digits. -/
theorem sqrt2_bounds_45 :
    (90509667991878083123308078349420677028459 / 64000000000000000000000000000000000000000 : ℝ) < Real.sqrt 2 ∧
      Real.sqrt 2 < 353553390593273762200422181052424519642417969 / 250000000000000000000000000000000000000000000 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem antiprismEnergy'_neg_sharper : antiprismEnergy' (7852234197230046684530831549019 / 25000000000000000000000000000000) < 0 := by
  obtain ⟨s2l, s2u⟩ := sqrt2_bounds_45
  unfold antiprismEnergy'
  have t1 := term_lt (coeff := 2 * Real.sqrt 2 + 1)
    (c := 478553390593273762200422181052424519642417969 / 125000000000000000000000000000000000000000000) (X := 1 - 7852234197230046684530831549019 / 25000000000000000000000000000000)
    (y := 414098609062744296915465897778944068640455843 / 500000000000000000000000000000000000000000000)
    (by linarith) (by norm_num) (by norm_num) (by linarith)
  have t2 := lt_term (coeff := 4 * (2 + Real.sqrt 2))
    (c := 218509667991878083123308078349420677028459 / 16000000000000000000000000000000000000000) (X := (2 - Real.sqrt 2) + (2 + Real.sqrt 2) * (7852234197230046684530831549019 / 25000000000000000000000000000000))
    (z := 643846763071658703087091694785174213040840737 / 500000000000000000000000000000000000000000000)
    (by linarith) (by norm_num) (by linarith) (by norm_num) (by linarith)
  have t3 := lt_term (coeff := 4 * (2 - Real.sqrt 2))
    (c := 146446609406726237799577818947575480357582031 / 62500000000000000000000000000000000000000000) (X := (2 + Real.sqrt 2) + (2 - Real.sqrt 2) * (7852234197230046684530831549019 / 25000000000000000000000000000000))
    (z := 189689294750267786463135902396479680031758457 / 100000000000000000000000000000000000000000000)
    (by linarith) (by norm_num) (by linarith) (by norm_num) (by linarith)
  have hnum : (478553390593273762200422181052424519642417969 / 125000000000000000000000000000000000000000000 : ℝ) / (414098609062744296915465897778944068640455843 / 500000000000000000000000000000000000000000000 : ℝ) ^ 3
      - (218509667991878083123308078349420677028459 / 16000000000000000000000000000000000000000 : ℝ) / (643846763071658703087091694785174213040840737 / 500000000000000000000000000000000000000000000 : ℝ) ^ 3
      - (146446609406726237799577818947575480357582031 / 62500000000000000000000000000000000000000000 : ℝ) / (189689294750267786463135902396479680031758457 / 100000000000000000000000000000000000000000000 : ℝ) ^ 3 < 0 := by norm_num
  linarith

theorem antiprismEnergy'_pos_sharper : 0 < antiprismEnergy' (31408936788920186738123326196079 / 100000000000000000000000000000000) := by
  obtain ⟨s2l, s2u⟩ := sqrt2_bounds_45
  unfold antiprismEnergy'
  have t1 := lt_term (coeff := 2 * Real.sqrt 2 + 1)
    (c := 122509667991878083123308078349420677028459 / 32000000000000000000000000000000000000000) (X := 1 - 31408936788920186738123326196079 / 100000000000000000000000000000000)
    (z := 828197218125488593830931795557870025652821521 / 1000000000000000000000000000000000000000000000)
    (by linarith) (by norm_num) (by linarith) (by norm_num) (by linarith)
  have t2 := term_lt (coeff := 4 * (2 + Real.sqrt 2))
    (c := 853553390593273762200422181052424519642417969 / 62500000000000000000000000000000000000000000) (X := (2 - Real.sqrt 2) + (2 + Real.sqrt 2) * (31408936788920186738123326196079 / 100000000000000000000000000000000))
    (y := 160961690767914675771772923696298524668623351 / 125000000000000000000000000000000000000000000)
    (by linarith) (by norm_num) (by norm_num) (by linarith)
  have t3 := term_lt (coeff := 4 * (2 - Real.sqrt 2))
    (c := 37490332008121916876691921650579322971541 / 16000000000000000000000000000000000000000) (X := (2 + Real.sqrt 2) + (2 - Real.sqrt 2) * (31408936788920186738123326196079 / 100000000000000000000000000000000))
    (y := 1896892947502677864631359023964801432522357099 / 1000000000000000000000000000000000000000000000)
    (by linarith) (by norm_num) (by norm_num) (by linarith)
  have hnum : (0:ℝ) < (122509667991878083123308078349420677028459 / 32000000000000000000000000000000000000000 : ℝ) / (828197218125488593830931795557870025652821521 / 1000000000000000000000000000000000000000000000 : ℝ) ^ 3
      - (853553390593273762200422181052424519642417969 / 62500000000000000000000000000000000000000000 : ℝ) / (160961690767914675771772923696298524668623351 / 125000000000000000000000000000000000000000000 : ℝ) ^ 3
      - (37490332008121916876691921650579322971541 / 16000000000000000000000000000000000000000 : ℝ) / (1896892947502677864631359023964801432522357099 / 1000000000000000000000000000000000000000000000 : ℝ) ^ 3 := by norm_num
  linarith

/-- **Thirty-two digits of `u*`**: `u* = 0.31408936788920186738123326196079…`. -/
theorem uStar_mem_Icc_sharper :
    uStar ∈ Set.Icc (7852234197230046684530831549019 / 25000000000000000000000000000000 : ℝ) (31408936788920186738123326196079 / 100000000000000000000000000000000) := by
  obtain ⟨hlo, hhi⟩ := uStar_mem_Icc
  have hmin := uStar_isMinOn
  have hmono := antiprismEnergy'_strictMonoOn
  constructor
  · by_contra hlt; push_neg at hlt
    have hanti : StrictAntiOn antiprismEnergy
        (Set.Icc (157 / 500) (7852234197230046684530831549019 / 25000000000000000000000000000000)) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      · exact antiprismEnergy_continuousOn.mono
          (Set.Icc_subset_Icc (by norm_num) (by norm_num))
      · intro x hx
        rw [interior_Icc] at hx
        rw [(hasDerivAt_antiprismEnergy (by linarith [hx.1]) (by linarith [hx.2])).deriv]
        have := hmono ⟨by linarith [hx.1], by linarith [hx.2]⟩
          (show (7852234197230046684530831549019 / 25000000000000000000000000000000 : ℝ) ∈ Set.Ico (0:ℝ) 1 from ⟨by norm_num, by norm_num⟩) hx.2
        linarith [antiprismEnergy'_neg_sharper]
    have h1 : antiprismEnergy (7852234197230046684530831549019 / 25000000000000000000000000000000) < antiprismEnergy uStar :=
      hanti (Set.mem_Icc.mpr ⟨hlo, hlt.le⟩) (Set.mem_Icc.mpr ⟨by norm_num, le_rfl⟩) hlt
    have h2 : antiprismEnergy uStar ≤ antiprismEnergy (7852234197230046684530831549019 / 25000000000000000000000000000000) :=
      hmin (show (7852234197230046684530831549019 / 25000000000000000000000000000000 : ℝ) ∈ window from Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
    linarith
  · by_contra hlt; push_neg at hlt
    have hmono' : StrictMonoOn antiprismEnergy
        (Set.Icc (31408936788920186738123326196079 / 100000000000000000000000000000000) (1571 / 5000)) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      · exact antiprismEnergy_continuousOn.mono
          (Set.Icc_subset_Icc (by norm_num) (by norm_num))
      · intro x hx
        rw [interior_Icc] at hx
        rw [(hasDerivAt_antiprismEnergy (by linarith [hx.1]) (by linarith [hx.2])).deriv]
        have := hmono (show (31408936788920186738123326196079 / 100000000000000000000000000000000 : ℝ) ∈ Set.Ico (0:ℝ) 1 from ⟨by norm_num, by norm_num⟩)
          ⟨by linarith [hx.1], by linarith [hx.2]⟩ hx.1
        linarith [antiprismEnergy'_pos_sharper]
    have h2 : antiprismEnergy uStar ≤ antiprismEnergy (31408936788920186738123326196079 / 100000000000000000000000000000000) :=
      hmin (show (31408936788920186738123326196079 / 100000000000000000000000000000000 : ℝ) ∈ window from Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
    have h3 : antiprismEnergy (31408936788920186738123326196079 / 100000000000000000000000000000000) < antiprismEnergy uStar :=
      hmono' (Set.mem_Icc.mpr ⟨le_rfl, by norm_num⟩) (Set.mem_Icc.mpr ⟨hlt.le, hhi⟩) hlt
    linarith

theorem uStar_lo : (7852234197230046684530831549019 / 25000000000000000000000000000000 : ℝ) ≤ uStar := uStar_mem_Icc_sharper.1
theorem uStar_hi : uStar ≤ 31408936788920186738123326196079 / 100000000000000000000000000000000 := uStar_mem_Icc_sharper.2

end Thomson.Tri5b
