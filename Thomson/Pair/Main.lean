import Thomson.Pair.SweepFl
import Thomson.Pair.SweepFr
import Thomson.Pair.SweepDl
import Thomson.Pair.SweepDr
import Thomson.Pair.SweepNl
import Thomson.Pair.SweepNr
import Thomson.Pair.SweepAl
import Thomson.Pair.SweepAr
import Thomson.Antiprism.SharpChords

/-! # Task 4: the pair inequality

`pairP pivots s ≥ 0` on `[24/25, 2]`, from the double zeros at the four chords (Tasks 1a, 1c) and
the enclosure of the pivots to `10⁻¹²` (Task 1b).

In `w = 1 − s²/2 ∈ [−1, 337/625]` it is enough to show `Φ(w) = α² − (2 − 2w) R(w)² ≥ 0`
(`Thomson.Pair.Coeff`).  `Φ` has double zeros at the four chord values
`w_F < w_D < w_N < w_A` and eight sweeps (`Thomson.Pair.Sweep`, data in `SweepXx.lean`) integrate a
lower bound for `Φ''` outwards from each of them:

| sweep | from | to |
|---|---|---|
| `Fl`, `Fr` | `w_F = −0.7991` | `−1`, `−0.6024` |
| `Dl`, `Dr` | `w_D = −0.3718` | `−0.6024`, `−0.0235` |
| `Nl`, `Nr` | `w_N = 0.1709` | `−0.0235`, `0.2508` |
| `Al`, `Ar` | `w_A = u* = 0.3141` | `0.2508`, `337/625` |

The meeting points are near the maxima of `Φ` between the chords (`≈ 4·10⁻⁶ … 10⁻⁴` there), where
every sweep still has most of its margin.  The left sweeps run on `Φ(−w)` (`ralt`).

Why a sweep: just beside a chord `pairP ≈ ½P''·d² ≈ 10⁻⁶`, and between `A` and `N` it never
exceeds `5·10⁻⁶`.  A direct enclosure of `pairP` with the pivots known to `ε` is `ε·Σⱼ|Gⱼ| ≈ 30ε`
wide, so at `ε = 10⁻⁶` (the `pivotEps` of `Tasks.lean`) no pointwise check can work there.  The
sweep uses the pivots only through `Φ''`, which is `10⁻²` at the chords; but even so the interval
enclosure of `Φ''` needs `ε = 10⁻¹²` near the chord `F` (at `10⁻⁶` its width is comparable to
`Φ''(w_F)`), which is what Task 1b provides.

Everything is checked by `decide +kernel`: no `native_decide`, so no `Lean.ofReduceBool`. -/

namespace Thomson.Pair

open Thomson Thomson.Tri5b

/-! ## The chords in `w`, on the grid (32 digits) -/

theorem wA_bounds :
    ((3140893678892018673812332619607600000000 : ℤ) : ℝ) ≤ (1 - chord 0 ^ 2 / 2) * SCALE ∧
      (1 - chord 0 ^ 2 / 2) * SCALE ≤ ((3140893678892018673812332619607900000000 : ℤ) : ℝ) := by
  rw [chord_inner_zero]
  have h1 := uStar_lo; have h2 := uStar_hi
  constructor <;> simp only [SCALE] <;> push_cast <;> linarith

theorem wD_bounds :
    ((-3718212642215962652375334760784800000000 : ℤ) : ℝ) ≤ (1 - chord 1 ^ 2 / 2) * SCALE ∧
      (1 - chord 1 ^ 2 / 2) * SCALE ≤ ((-3718212642215962652375334760784200000000 : ℤ) : ℝ) := by
  rw [chord_inner_one]
  have h1 := uStar_lo; have h2 := uStar_hi
  constructor <;> simp only [SCALE] <;> push_cast <;> linarith

/-- `√2·(1 − u*)`, enclosed. -/
theorem sqrt2_one_sub_bounds :
    (90509667991878083123308078349420677028459 / 64000000000000000000000000000000000000000 : ℝ)
        * (1 - 31408936788920186738123326196079 / 100000000000000000000000000000000)
      ≤ Real.sqrt 2 * (1 - uStar) ∧
    Real.sqrt 2 * (1 - uStar) ≤
      (353553390593273762200422181052424519642417969 / 250000000000000000000000000000000000000000000 : ℝ)
        * (1 - 7852234197230046684530831549019 / 25000000000000000000000000000000) := by
  obtain ⟨s1, s2⟩ := sqrt2_bounds_45
  have h1 := uStar_lo; have h2 := uStar_hi
  constructor
  · exact mul_le_mul s1.le (by linarith) (by norm_num) (by positivity)
  · exact mul_le_mul s2.le (by linarith) (by linarith) (by positivity)

theorem wN_bounds :
    ((1709226913642947658961216814572272673902 : ℤ) : ℝ) ≤ (1 - chord 2 ^ 2 / 2) * SCALE ∧
      (1 - chord 2 ^ 2 / 2) * SCALE ≤ ((1709226913642947658961216814572784805937 : ℤ) : ℝ) := by
  rw [chord_inner_two]
  have h1 := uStar_lo; have h2 := uStar_hi
  obtain ⟨p1, p2⟩ := sqrt2_one_sub_bounds
  constructor <;> simp only [SCALE] <;> push_cast <;> linarith

theorem wF_bounds :
    ((-7991014271426985006585882053788284805937 : ℤ) : ℝ) ≤ (1 - chord 3 ^ 2 / 2) * SCALE ∧
      (1 - chord 3 ^ 2 / 2) * SCALE ≤ ((-7991014271426985006585882053787772673902 : ℤ) : ℝ) := by
  rw [chord_inner_three]
  have h1 := uStar_lo; have h2 := uStar_hi
  obtain ⟨p1, p2⟩ := sqrt2_one_sub_bounds
  constructor <;> simp only [SCALE] <;> push_cast <;> linarith

/-- The meeting points and the ends, on the grid. -/
theorem grid_vals :
    ((-6024000000000000000000000000000000000000 : ℤ) : ℝ) / SCALE = -6024 / 10000 ∧
    ((6024000000000000000000000000000000000000 : ℤ) : ℝ) / SCALE = 6024 / 10000 ∧
    ((-235000000000000000000000000000000000000 : ℤ) : ℝ) / SCALE = -235 / 10000 ∧
    ((235000000000000000000000000000000000000 : ℤ) : ℝ) / SCALE = 235 / 10000 ∧
    ((2508000000000000000000000000000000000000 : ℤ) : ℝ) / SCALE = 2508 / 10000 ∧
    ((-2508000000000000000000000000000000000000 : ℤ) : ℝ) / SCALE = -2508 / 10000 ∧
    ((5392000000000000000000000000000000000000 : ℤ) : ℝ) / SCALE = 337 / 625 ∧
    ((10000000000000000000000000000000000000000 : ℤ) : ℝ) / SCALE = 1 := by
  simp only [SCALE]; norm_num

/-! ## The theorem -/

/-- **Task 4 — the pair inequality**, from the double zeros at the chords (`pairP_tight`, i.e.
Tasks 1a and 1c(i)) and Task 1b at `10⁻¹²`. -/
theorem pairP_nonneg_of
    (htight : ∀ X : Fin 4, pairP pivots (chord X) = 0 ∧ deriv (pairP pivots) (chord X) = 0)
    (hclose : ∀ j, |pivots j - pivotsNum j| ≤ 1 / 10 ^ 12) :
    ∀ s : ℝ, 24 / 25 ≤ s → s ≤ 2 → 0 ≤ pairP pivots s := by
  have hS : (0 : ℝ) < SCALE := SCALE_pos'
  intro s hs1 hs2
  refine pairP_nonneg_of_Phi ?_
  set q := rPhi (Rcert pivots) with hq
  -- the tables enclose `Φ` and its mirror image
  have hL : LMem (IPhi (IR IDtab)) q := by rw [IDtab_eq]; exact LMem_IPhi_cert hclose
  obtain ⟨e2, e3, e4, f2, f3, f4⟩ := tabs_eq
  have hF2 : LMem F2tab (rder (rder q)) := by rw [e2]; exact LMem_lder (LMem_lder hL)
  have hF3 : LMem F3tab (rder (rder (rder q))) := by rw [e3]; exact LMem_lder hF2
  have hF4 : LMem F4tab (rder (rder (rder (rder q)))) := by rw [e4]; exact LMem_lder hF3
  have hG2 : LMem G2tab (rder (rder (ralt q))) := by
    rw [f2]; exact LMem_lder (LMem_lder (LMem_lalt hL))
  have hG3 : LMem G3tab (rder (rder (rder (ralt q)))) := by rw [f3]; exact LMem_lder hG2
  have hG4 : LMem G4tab (rder (rder (rder (rder (ralt q))))) := by rw [f4]; exact LMem_lder hG3
  -- the double zeros
  have tz : ∀ X : Fin 4, reval q (1 - chord X ^ 2 / 2) = 0 ∧
      reval (rder q) (1 - chord X ^ 2 / 2) = 0 := fun X => Phi_tight (htight X).1 (htight X).2
  have tm : ∀ X : Fin 4, reval (ralt q) (-(1 - chord X ^ 2 / 2)) = 0 ∧
      reval (rder (ralt q)) (-(1 - chord X ^ 2 / 2)) = 0 := fun X => ralt_tight (tz X).1 (tz X).2
  obtain ⟨gv1, gv2, gv3, gv4, gv5, gv6, gv7, gv8⟩ := grid_vals
  obtain ⟨a1, a2⟩ := wA_bounds
  obtain ⟨d1, d2⟩ := wD_bounds
  obtain ⟨n1, n2⟩ := wN_bounds
  obtain ⟨f1', f2'⟩ := wF_bounds
  -- the eight sweeps
  have sFl := sweep_sound hG2 hG3 hG4 sweepFl (x0 := -(1 - chord 3 ^ 2 / 2))
    (by push_cast at f2' ⊢; linarith) (by push_cast at f1' ⊢; linarith) (tm 3).1 (tm 3).2
  have sFr := sweep_sound hF2 hF3 hF4 sweepFr f1' f2' (tz 3).1 (tz 3).2
  have sDl := sweep_sound hG2 hG3 hG4 sweepDl (x0 := -(1 - chord 1 ^ 2 / 2))
    (by push_cast at d2 ⊢; linarith) (by push_cast at d1 ⊢; linarith) (tm 1).1 (tm 1).2
  have sDr := sweep_sound hF2 hF3 hF4 sweepDr d1 d2 (tz 1).1 (tz 1).2
  have sNl := sweep_sound hG2 hG3 hG4 sweepNl (x0 := -(1 - chord 2 ^ 2 / 2))
    (by push_cast at n2 ⊢; linarith) (by push_cast at n1 ⊢; linarith) (tm 2).1 (tm 2).2
  have sNr := sweep_sound hF2 hF3 hF4 sweepNr n1 n2 (tz 2).1 (tz 2).2
  have sAl := sweep_sound hG2 hG3 hG4 sweepAl (x0 := -(1 - chord 0 ^ 2 / 2))
    (by push_cast at a2 ⊢; linarith) (by push_cast at a1 ⊢; linarith) (tm 0).1 (tm 0).2
  have sAr := sweep_sound hF2 hF3 hF4 sweepAr a1 a2 (tz 0).1 (tz 0).2
  rw [gv8] at sFl; rw [gv1] at sFr; rw [gv2] at sDl; rw [gv3] at sDr
  rw [gv4] at sNl; rw [gv5] at sNr; rw [gv6] at sAl; rw [gv7] at sAr
  -- cover `w ∈ [−1, 337/625]`
  set w := 1 - s ^ 2 / 2 with hw
  have hw1 : -1 ≤ w := by rw [hw]; nlinarith
  have hw2 : w ≤ 337 / 625 := by rw [hw]; nlinarith
  have mirror : ∀ y : ℝ, 0 ≤ reval (ralt q) (-y) → 0 ≤ reval q y := fun y h => by
    rwa [reval_ralt, neg_neg] at h
  rcases le_total w (-6024 / 10000) with h1 | h1
  · rcases le_total w (1 - chord 3 ^ 2 / 2) with h | h
    · exact mirror w (sFl (-w) (by linarith) (by linarith))
    · exact sFr w h h1
  rcases le_total w (-235 / 10000) with h2 | h2
  · rcases le_total w (1 - chord 1 ^ 2 / 2) with h | h
    · exact mirror w (sDl (-w) (by linarith) (by linarith))
    · exact sDr w h h2
  rcases le_total w (2508 / 10000) with h3 | h3
  · rcases le_total w (1 - chord 2 ^ 2 / 2) with h | h
    · exact mirror w (sNl (-w) (by linarith) (by linarith))
    · exact sNr w h h3
  · rcases le_total w (1 - chord 0 ^ 2 / 2) with h | h
    · exact mirror w (sAl (-w) (by linarith) (by linarith))
    · exact sAr w h hw2

end Thomson.Pair
