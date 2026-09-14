import Thomson.TriangleGlobal.Covering.Certificate

/-! # Task 5b — the theorem

Everything assembled: the box covering, checked by the kernel (`KCertificate.kcert_cover`), the
tensor of `F` for the true certificate (`KTable.Mem3_CFtabL`, `Bridge.ev_cF_eq_Fh`), the images of
the five local cubes (`CubeData.cubeSound`), and Task 5a. -/

namespace Thomson.Tri5b

open Thomson

/-- **Task 5 on the corrected chord range**, from Task 5a and a `10⁻¹²` pivot enclosure.

The chord bound is `chordLo = 9619/10000`, not `24/25`: on `[24/25, 2]³` the statement is *false*
(`Thomson.TriangleGlobal.Domain`). -/
theorem tri_nonneg (hloc : TriLocal (fun _ => 1 / 500))
    (hclose : ∀ j, |pivots j - pivotsNum j| ≤ 1 / 10 ^ 12) :
    ∀ a b c : ℝ, chordLo ≤ a → chordLo ≤ b → chordLo ≤ c → a ≤ 2 → b ≤ 2 → c ≤ 2 →
      0 ≤ gram a b c → 0 ≤ triP pivots a b c := by
  exact task5_of_data (mg := MG) (ev_cF_eq_Fh pivots) (by unfold MG; norm_num) rootBx
    (kcert_cover (Mem3_CFtabL hclose) cubeSound) (le_refl _) (le_refl _) (le_refl _) (le_refl _)
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

/-- **The covering's margin, exported** (uniqueness, `docs/uniqueness.md` U4): on the sorted region
outside the five `1/500`-cubes the slack is at least `MG / SCALE = 10⁻¹⁰`.  This is the `hnum` of
`task5_of_data`, for the data of `tri_nonneg`. -/
theorem numCertU_final (hclose : ∀ j, |pivots j - pivotsNum j| ≤ 1 / 10 ^ 12) :
    NumCertU (fun _ => 1 / 500) (1 / 10 ^ 10) := by
  have h := numCertU_of_covers (ev_cF_eq_Fh pivots) rootBx
    (kcert_cover (Mem3_CFtabL hclose) cubeSound) (le_refl _) (le_refl _) (le_refl _) (le_refl _)
    (le_refl _) (le_refl _)
  have e : (MG : ℝ) / SCALE = 1 / 10 ^ 10 := by
    unfold MG SCALE; norm_num
  rwa [e] at h

end Thomson.Tri5b
