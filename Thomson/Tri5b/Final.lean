import Thomson.Tri5b.Certificate

/-! # Task 5b — the theorem

Everything assembled: the box covering (`Certificate.cert_cover`), the tensor of `F` for the true
certificate (`CFTable.ITMem_CFtab`, `Bridge.ev_cF_eq_Fh`), the images of the five local cubes
(`CubeData.cubeSound`), and Task 5a. -/

namespace Thomson.Tri5b

open Thomson

/-- **Task 5 on the corrected chord range**, from Task 5a and a `10⁻¹²` pivot enclosure.

The chord bound is `chordLo = 9619/10000`, not `24/25`: on `[24/25, 2]³` the statement is *false*
(`Thomson.Tri5b.Domain`). -/
theorem tri_nonneg (hloc : TriLocal (fun _ => 1 / 500))
    (hclose : ∀ j, |pivots j - pivotsNum j| ≤ 1 / 10 ^ 12) :
    ∀ a b c : ℝ, chordLo ≤ a → chordLo ≤ b → chordLo ≤ c → a ≤ 2 → b ≤ 2 → c ≤ 2 →
      0 ≤ gram a b c → 0 ≤ triP pivots a b c := by
  have hc : ∀ j, |pivots j - pivotsNum j| ≤ (EPS : ℝ) / SCALE := by
    intro j
    have h := hclose j
    have e : (EPS : ℝ) / SCALE = 1 / 10 ^ 12 := by
      unfold EPS SCALE; norm_num
    rwa [e]
  exact task5_of_data (mg := MG) (ev_cF_eq_Fh pivots) (by unfold MG; norm_num) rootBx
    (cert_cover (ITMem_CFtab hc) cubeSound) (le_refl _) (le_refl _) (le_refl _) (le_refl _)
    (le_refl _) (le_refl _) hloc

/-- **Task 5b**, in the shape of `Thomson.triP_global` (with the corrected chord bound).  The
hypothesis excluding the five cubes is not needed once the triple is sorted, so it is discharged. -/
theorem triP_global (hloc : TriLocal (fun _ => 1 / 500))
    (hclose : ∀ j, |pivots j - pivotsNum j| ≤ 1 / 10 ^ 12) :
    ∀ a b c : ℝ, chordLo ≤ a → chordLo ≤ b → chordLo ≤ c → a ≤ 2 → b ≤ 2 → c ≤ 2 →
      0 ≤ 1 + 2 * (1 - a ^ 2 / 2) * (1 - b ^ 2 / 2) * (1 - c ^ 2 / 2)
          - (1 - a ^ 2 / 2) ^ 2 - (1 - b ^ 2 / 2) ^ 2 - (1 - c ^ 2 / 2) ^ 2 →
      (∀ m : Fin 5, 1 / 500 < |a - (touchType m).1| ∨ 1 / 500 < |b - (touchType m).2.1|
        ∨ 1 / 500 < |c - (touchType m).2.2|) →
      0 ≤ triP pivots a b c :=
  fun a b c h1 h2 h3 h4 h5 h6 hg _ => tri_nonneg hloc hclose a b c h1 h2 h3 h4 h5 h6 hg

end Thomson.Tri5b
