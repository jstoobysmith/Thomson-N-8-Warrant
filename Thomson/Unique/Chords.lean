import Thomson.Tri5b.Main
import Thomson.ThreePoint.Toolkit
import Thomson.Unique.Defs

/-! # Uniqueness, step U4: the triangle polynomial is positive at every non-type chord triple

`UniquenessPlan.md`, U4.  The Task 5b covering certifies the slack `triP/(abc)` to be at least
`10⁻¹⁰` on the sorted region outside the five `1/500`-cubes (`Tri5b.NumCertU` with margin
`10⁻¹⁰`; exported as `Thomson.Tri5b.numCertU_final` / `Thomson.Tri5b.task5bStrict` in the `Tri5b`
library).  Here that strict statement is a hypothesis, `Task5bStrict`, and we conclude: if `triP`
vanishes at a (realisable) triple of antiprism chords, the triple is one of the five types.

Colours: `A = 0, D = 1, N = 2, F = 3` (`Thomson.chord`); in length `A < N < D < F`. -/

namespace Thomson.Unique

open Thomson

/-- **Task 5b with its margin**: the covering's slack is `≥ 10⁻¹⁰` on the sorted region outside
the five cubes (proved in the `Tri5b` library as `Thomson.Tri5b.task5bStrict`). -/
def Task5bStrict : Prop := Tri5b.NumCertU (fun _ => 1 / 500) (1 / 10 ^ 10)

/-! ## Enclosures of the four chords -/

theorem chord_zero_bounds : (1171 / 1000 : ℝ) < chord 0 ∧ chord 0 < 11715 / 10000 := by
  obtain ⟨r1, r2⟩ := rStar_bounds
  obtain ⟨w1, w2⟩ := sqrt2_bounds
  have e : chord 0 = Real.sqrt 2 * rStar := rfl
  rw [e]
  constructor <;> nlinarith

theorem chord_one_bounds : (16562 / 10000 : ℝ) < chord 1 ∧ chord 1 < 16566 / 10000 := by
  obtain ⟨r1, r2⟩ := rStar_bounds
  have e : chord 1 = 2 * rStar := rfl
  rw [e]
  constructor <;> linarith

theorem chord_two_bounds : (12875 / 10000 : ℝ) < chord 2 ∧ chord 2 < 12879 / 10000 :=
  s2Star_bounds

theorem chord_three_bounds : (18967 / 10000 : ℝ) < chord 3 ∧ chord 3 < 18971 / 10000 :=
  s4Star_bounds

/-- Distinct chords differ by more than the cube radius `1/500` (the gaps are `≥ 0.116`). -/
theorem chord_gaps : ∀ X Y : Fin 4, X ≠ Y → 1 / 500 < |chord X - chord Y| := by
  obtain ⟨a1, a2⟩ := chord_zero_bounds
  obtain ⟨d1, d2⟩ := chord_one_bounds
  obtain ⟨n1, n2⟩ := chord_two_bounds
  obtain ⟨f1, f2⟩ := chord_three_bounds
  intro X Y hXY
  rw [lt_abs]
  fin_cases X <;> fin_cases Y <;> simp at hXY ⊢
  all_goals first
    | (left; linarith)
    | (right; linarith)

/-- The rank of a colour by chord length: `A < N < D < F`. -/
def rk : Fin 4 → ℕ := ![0, 2, 1, 3]

theorem chord_mono : ∀ {X Y : Fin 4}, rk X ≤ rk Y → chord X ≤ chord Y := by
  obtain ⟨a1, a2⟩ := chord_zero_bounds
  obtain ⟨d1, d2⟩ := chord_one_bounds
  obtain ⟨n1, n2⟩ := chord_two_bounds
  obtain ⟨f1, f2⟩ := chord_three_bounds
  intro X Y h
  fin_cases X <;> fin_cases Y <;> simp [rk] at h ⊢ <;> linarith

theorem chord_lo : ∀ X : Fin 4, 9619 / 10000 ≤ chord X := by
  obtain ⟨a1, a2⟩ := chord_zero_bounds
  obtain ⟨d1, d2⟩ := chord_one_bounds
  obtain ⟨n1, n2⟩ := chord_two_bounds
  obtain ⟨f1, f2⟩ := chord_three_bounds
  intro X
  fin_cases X <;> simp <;> linarith

theorem chord_hi : ∀ X : Fin 4, chord X ≤ 2 := by
  obtain ⟨a1, a2⟩ := chord_zero_bounds
  obtain ⟨d1, d2⟩ := chord_one_bounds
  obtain ⟨n1, n2⟩ := chord_two_bounds
  obtain ⟨f1, f2⟩ := chord_three_bounds
  intro X
  fin_cases X <;> simp <;> linarith

/-! ## The five types as colour triples -/

/-- The colours of `touchType m`: `FFA, FDN, FNA, DAA, NNA`. -/
def touchCol : Fin 5 → Fin 4 × Fin 4 × Fin 4 :=
  ![(3, 3, 0), (3, 1, 2), (3, 2, 0), (1, 0, 0), (2, 2, 0)]

theorem touchType_eq_chord (m : Fin 5) :
    touchType m = (chord (touchCol m).1, chord (touchCol m).2.1, chord (touchCol m).2.2) := by
  fin_cases m <;> rfl

theorem allowedTri_touchCol (m : Fin 5) :
    allowedTri (touchCol m).1 (touchCol m).2.1 (touchCol m).2.2 = true := by
  revert m; decide

/-- A non-type colour triple is outside every `1/500`-cube, coordinatewise by a whole chord gap. -/
theorem out_of_not_allowed {X Y Z : Fin 4} (hna : ¬ allowedTri X Y Z = true) (m : Fin 5) :
    1 / 500 < |chord X - (touchType m).1| ∨ 1 / 500 < |chord Y - (touchType m).2.1|
      ∨ 1 / 500 < |chord Z - (touchType m).2.2| := by
  rw [touchType_eq_chord m]
  dsimp only
  by_cases hX : X = (touchCol m).1
  · by_cases hY : Y = (touchCol m).2.1
    · by_cases hZ : Z = (touchCol m).2.2
      · exact absurd (hX ▸ hY ▸ hZ ▸ allowedTri_touchCol m) hna
      · exact Or.inr (Or.inr (chord_gaps _ _ hZ))
    · exact Or.inr (Or.inl (chord_gaps _ _ hY))
  · exact Or.inl (chord_gaps _ _ hX)

/-! ## Positivity of `triP` from the strict covering -/

/-- **`triP > 0` away from the cubes**, on the sorted region: `triP = abc · slack ≥ abc · 10⁻¹⁰`. -/
theorem triP_pos_of_numCertU (h : Task5bStrict) {a b c : ℝ} (hsort : c ≤ b ∧ b ≤ a)
    (hrange : 9619 / 10000 ≤ c ∧ a ≤ 2) (hg : 0 ≤ Tri5b.gram a b c)
    (hout : ∀ m : Fin 5, 1 / 500 < |a - (touchType m).1| ∨ 1 / 500 < |b - (touchType m).2.1|
      ∨ 1 / 500 < |c - (touchType m).2.2|) :
    0 < triP pivots a b c := by
  obtain ⟨hcb, hba⟩ := hsort
  obtain ⟨hc, ha2⟩ := hrange
  have hc0 : 0 < c := by linarith
  have hb0 : 0 < b := by linarith
  have ha0 : 0 < a := by linarith
  have hau : Real.sqrt (2 - 2 * (1 - a ^ 2 / 2)) = a := Tri5b.sqrt_two_sub_two_mul a ha0.le
  have hbv : Real.sqrt (2 - 2 * (1 - b ^ 2 / 2)) = b := Tri5b.sqrt_two_sub_two_mul b hb0.le
  have hct : Real.sqrt (2 - 2 * (1 - c ^ 2 / 2)) = c := Tri5b.sqrt_two_sub_two_mul c hc0.le
  have h1 : -1 ≤ 1 - a ^ 2 / 2 := by nlinarith
  have h2 : 1 - a ^ 2 / 2 ≤ 1 - b ^ 2 / 2 := by nlinarith
  have h3 : 1 - b ^ 2 / 2 ≤ 1 - c ^ 2 / 2 := by nlinarith
  have h4 : 1 - c ^ 2 / 2 ≤ Tri5b.uHi := by
    unfold Tri5b.uHi Tri5b.chordLo; nlinarith
  have h5 : 0 ≤ Tri5b.gramU (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c ^ 2 / 2) := by
    rw [← Tri5b.gram_eq_gramU]; exact hg
  have key := h _ _ _ h1 h2 h3 h4 h5 (by rw [hau, hbv, hct]; exact hout)
  rw [hau, hbv, hct] at key
  rw [Tri5b.triP_eq_mul_slack pivots ha0 hb0 hc0]
  have hpos : 0 < a * b * c := by positivity
  exact mul_pos hpos (lt_of_lt_of_le (by norm_num) key)

/-! ## Sorting colour triples -/

/-- Any predicate on colour triples invariant under the two transpositions holds everywhere once
it holds on the triples sorted decreasingly by `rk`. -/
theorem of_sorted_fin {P : Fin 4 → Fin 4 → Fin 4 → Prop}
    (h12 : ∀ x y z, P x y z → P y x z) (h23 : ∀ x y z, P x y z → P x z y)
    (hs : ∀ x y z, rk z ≤ rk y → rk y ≤ rk x → P x y z) (a b c : Fin 4) : P a b c := by
  rcases le_total (rk a) (rk b) with hab | hab <;> rcases le_total (rk b) (rk c) with hbc | hbc <;>
    rcases le_total (rk a) (rk c) with hac | hac
  · exact h12 _ _ _ (h23 _ _ _ (h12 _ _ _ (hs c b a hab hbc)))
  · exact h12 _ _ _ (h23 _ _ _ (h12 _ _ _ (hs c b a hab hbc)))
  · exact h12 _ _ _ (h23 _ _ _ (hs b c a hac hbc))
  · exact h12 _ _ _ (hs b a c hac hab)
  · exact h23 _ _ _ (h12 _ _ _ (hs c a b hab hac))
  · exact h23 _ _ _ (hs a c b hbc hac)
  · exact hs a b c hbc hab
  · exact hs a b c hbc hab

/-- **U4.**  If `triP` vanishes at a realisable triple of antiprism chords, the triple is one of
the five antiprism triangle types. -/
theorem allowedTri_of_triP_eq_zero (h : Task5bStrict) (X Y Z : Fin 4)
    (hg : 0 ≤ Tri5b.gram (chord X) (chord Y) (chord Z))
    (h0 : triP pivots (chord X) (chord Y) (chord Z) = 0) : allowedTri X Y Z = true := by
  revert hg h0
  refine of_sorted_fin (P := fun X Y Z => 0 ≤ Tri5b.gram (chord X) (chord Y) (chord Z) →
    triP pivots (chord X) (chord Y) (chord Z) = 0 → allowedTri X Y Z = true) ?_ ?_ ?_ X Y Z
  · intro x y z hP hg h0
    rw [allowedTri_perm12]
    exact hP (by rwa [Tri5b.gram_swap12]) (by rwa [triP_swap12])
  · intro x y z hP hg h0
    rw [allowedTri_perm23]
    exact hP (by rwa [Tri5b.gram_swap23]) (by rwa [triP_swap23])
  · intro x y z hzy hyx hg h0
    by_contra hna
    have hpos := triP_pos_of_numCertU h ⟨chord_mono hzy, chord_mono hyx⟩
      ⟨chord_lo z, chord_hi x⟩ hg (out_of_not_allowed hna)
    linarith

end Thomson.Unique
