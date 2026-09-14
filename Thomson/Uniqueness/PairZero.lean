import Thomson.Uniqueness.PairStrictCerts
import Thomson.Pair.Main
import Thomson.Certificate.Assemble

/-! # Uniqueness, step U3: the pair polynomial vanishes only at the four chords

`docs/uniqueness.md`, U3.  On `[24/25, 2]`, `pairP pivots s > 0` unless `s` is one of the four
chords `A, D, N, F`.  The proof is that of `Thomson.Pair.pairP_nonneg_of` with the strict sweeps
(`Thomson.Uniqueness.PairStrict`, `Thomson.Uniqueness.PairStrictCerts`): `Φ > 0` on each side of the chord
of each sub-interval, and `Φ = (α − sR)(α + sR)` with `α > 0` turns `Φ > 0` into `pairP > 0`.

* `pairP_pos_of` — strict positivity away from the chords (hypotheses as `pairP_nonneg_of`);
* `pairP_eq_zero_iff_of`, `pairP_eq_zero_iff` — the zeros on `[9619/10000, 2]` are exactly the
  chords (the second from Tasks 1a, 1b). -/

namespace Thomson.Pair

open Thomson Thomson.Tri5b

/-- **`Φ > 0` gives strict positivity of the pair polynomial.** -/
theorem pairP_pos_of_Phi {p : Fin 24 → ℝ} {s : ℝ}
    (h : 0 < reval (rPhi (Rcert p)) (1 - s ^ 2 / 2)) : 0 < pairP p s := by
  rw [reval_rPhi] at h
  rw [pairP_eq]
  set R := reval (Rcert p) (1 - s ^ 2 / 2)
  have ha := alpha_pos
  have e : (2 - 2 * (1 - s ^ 2 / 2)) * R ^ 2 = (s * R) ^ 2 := by ring
  rw [e] at h
  by_contra hneg
  push Not at hneg
  nlinarith

theorem chord_pos (X : Fin 4) : 0 < chord X := by
  fin_cases X
  · show 0 < chord 0
    rw [chord_zero]; exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) rStar_pos
  · show 0 < chord 1
    rw [chord_one]; linarith [rStar_pos]
  · show 0 < chord 2
    rw [chord_two]; exact s2Star_pos
  · show 0 < chord 3
    rw [chord_three]; exact s4Star_pos

/-- **Task 4, strict — the pair polynomial is positive away from the chords.** -/
theorem pairP_pos_of
    (htight : ∀ X : Fin 4, pairP pivots (chord X) = 0 ∧ deriv (pairP pivots) (chord X) = 0)
    (hclose : ∀ j, |pivots j - pivotsNum j| ≤ 1 / 10 ^ 12) :
    ∀ s : ℝ, 24 / 25 ≤ s → s ≤ 2 → (∀ X : Fin 4, s ≠ chord X) → 0 < pairP pivots s := by
  have hS : (0 : ℝ) < SCALE := SCALE_pos'
  intro s hs1 hs2 hne
  refine pairP_pos_of_Phi ?_
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
  -- the eight strict sweeps
  have sFl := sweep_sound_pos hG2 hG3 hG4 sweepFl_strict (x0 := -(1 - chord 3 ^ 2 / 2))
    (by push_cast at f2' ⊢; linarith) (by push_cast at f1' ⊢; linarith) (tm 3).1 (tm 3).2
  have sFr := sweep_sound_pos hF2 hF3 hF4 sweepFr_strict f1' f2' (tz 3).1 (tz 3).2
  have sDl := sweep_sound_pos hG2 hG3 hG4 sweepDl_strict (x0 := -(1 - chord 1 ^ 2 / 2))
    (by push_cast at d2 ⊢; linarith) (by push_cast at d1 ⊢; linarith) (tm 1).1 (tm 1).2
  have sDr := sweep_sound_pos hF2 hF3 hF4 sweepDr_strict d1 d2 (tz 1).1 (tz 1).2
  have sNl := sweep_sound_pos hG2 hG3 hG4 sweepNl_strict (x0 := -(1 - chord 2 ^ 2 / 2))
    (by push_cast at n2 ⊢; linarith) (by push_cast at n1 ⊢; linarith) (tm 2).1 (tm 2).2
  have sNr := sweep_sound_pos hF2 hF3 hF4 sweepNr_strict n1 n2 (tz 2).1 (tz 2).2
  have sAl := sweep_sound_pos hG2 hG3 hG4 sweepAl_strict (x0 := -(1 - chord 0 ^ 2 / 2))
    (by push_cast at a2 ⊢; linarith) (by push_cast at a1 ⊢; linarith) (tm 0).1 (tm 0).2
  have sAr := sweep_sound_pos hF2 hF3 hF4 sweepAr_strict a1 a2 (tz 0).1 (tz 0).2
  rw [gv8] at sFl; rw [gv1] at sFr; rw [gv2] at sDl; rw [gv3] at sDr
  rw [gv4] at sNl; rw [gv5] at sNr; rw [gv6] at sAl; rw [gv7] at sAr
  -- cover `w ∈ [−1, 337/625]`, away from the chords
  set w := 1 - s ^ 2 / 2 with hw
  have hw1 : -1 ≤ w := by rw [hw]; nlinarith
  have hw2 : w ≤ 337 / 625 := by rw [hw]; nlinarith
  have hwne : ∀ X : Fin 4, w ≠ 1 - chord X ^ 2 / 2 := by
    intro X hX
    apply hne X
    have hsq : s ^ 2 = chord X ^ 2 := by rw [hw] at hX; linarith
    exact (pow_left_inj₀ (by linarith) (chord_pos X).le two_ne_zero).mp hsq
  have mirror : ∀ y : ℝ, 0 < reval (ralt q) (-y) → 0 < reval q y := fun y h => by
    rwa [reval_ralt, neg_neg] at h
  rcases le_total w (-6024 / 10000) with h1 | h1
  · rcases lt_or_gt_of_ne (hwne 3) with h | h
    · exact mirror w (sFl (-w) (by linarith) (by linarith))
    · exact sFr w h h1
  rcases le_total w (-235 / 10000) with h2 | h2
  · rcases lt_or_gt_of_ne (hwne 1) with h | h
    · exact mirror w (sDl (-w) (by linarith) (by linarith))
    · exact sDr w h h2
  rcases le_total w (2508 / 10000) with h3 | h3
  · rcases lt_or_gt_of_ne (hwne 2) with h | h
    · exact mirror w (sNl (-w) (by linarith) (by linarith))
    · exact sNr w h h3
  · rcases lt_or_gt_of_ne (hwne 0) with h | h
    · exact mirror w (sAl (-w) (by linarith) (by linarith))
    · exact sAr w h hw2

/-- **The zeros of the pair polynomial on `[9619/10000, 2]` are exactly the four chords**, under
the hypotheses of `pairP_nonneg_of`. -/
theorem pairP_eq_zero_iff_of
    (htight : ∀ X : Fin 4, pairP pivots (chord X) = 0 ∧ deriv (pairP pivots) (chord X) = 0)
    (hclose : ∀ j, |pivots j - pivotsNum j| ≤ 1 / 10 ^ 12) {s : ℝ} (hs1 : 9619 / 10000 ≤ s)
    (hs2 : s ≤ 2) : pairP pivots s = 0 ↔ ∃ X : Fin 4, s = chord X := by
  constructor
  · intro h0
    by_contra hno
    push Not at hno
    have := pairP_pos_of htight hclose s (le_trans (by norm_num) hs1) hs2 hno
    linarith
  · rintro ⟨X, rfl⟩
    exact (htight X).1

end Thomson.Pair

namespace Thomson

/-- **The zeros of the pair polynomial on `[9619/10000, 2]` are exactly the four chords**
(from Tasks 1a, 1b; `docs/uniqueness.md`, U3). -/
theorem pairP_eq_zero_iff (h1a : Task1a) (h1b : Task1b) {s : ℝ} (hs1 : 9619 / 10000 ≤ s)
    (hs2 : s ≤ 2) : pairP pivots s = 0 ↔ ∃ X : Fin 4, s = chord X :=
  Pair.pairP_eq_zero_iff_of (pairP_tight h1a) h1b hs1 hs2

/-- The pair polynomial is positive on `[24/25, 2]` away from the four chords (from Tasks 1a, 1b). -/
theorem pairP_pos (h1a : Task1a) (h1b : Task1b) :
    ∀ s : ℝ, 24 / 25 ≤ s → s ≤ 2 → (∀ X : Fin 4, s ≠ chord X) → 0 < pairP pivots s :=
  Pair.pairP_pos_of (pairP_tight h1a) h1b

end Thomson
