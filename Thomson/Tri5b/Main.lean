import Thomson.Tri5b.Reduce
import Thomson.Tri5b.MForm

/-! # Task 5b: the top of the chain

`triP` lives in chord variables, the box covering lives in inner-product variables.  This file is
the dictionary, and it states the one remaining obligation, `NumCertU`, in the form the covering
produces it. -/

namespace Thomson.Tri5b

open Thomson

/-- The upper end of the inner-product range: the image of `chordLo`. -/
noncomputable def uHi : ℝ := 1 - chordLo ^ 2 / 2

/-- The Gram polynomial in inner-product variables. -/
noncomputable def gramU (u v t : ℝ) : ℝ := 1 + 2 * u * v * t - u ^ 2 - v ^ 2 - t ^ 2

theorem gram_eq_gramU (a b c : ℝ) :
    gram a b c = gramU (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c ^ 2 / 2) := rfl

/-- **The remaining obligation.**  The certificate's slack, in inner-product variables, is at
least `margin` on the sorted region minus the five cubes.  This is what the box covering of
`Thomson.Tri5b.Engine` establishes: `triP pivots a b c = a·b·c · (slack)`. -/
def NumCertU (ρ : Fin 5 → ℝ) (margin : ℝ) : Prop :=
  ∀ u v t : ℝ, -1 ≤ u → u ≤ v → v ≤ t → t ≤ uHi → 0 ≤ gramU u v t →
    (∀ m : Fin 5, ρ m < |Real.sqrt (2 - 2 * u) - (touchType m).1|
      ∨ ρ m < |Real.sqrt (2 - 2 * v) - (touchType m).2.1|
      ∨ ρ m < |Real.sqrt (2 - 2 * t) - (touchType m).2.2|) →
    margin ≤ lamFix * ((Real.sqrt (2 - 2 * u))⁻¹ + (Real.sqrt (2 - 2 * v))⁻¹
        + (Real.sqrt (2 - 2 * t))⁻¹) - Fh (Hp pivots) u v t

/-- The chord/inner-product dictionary: `triP` is `abc` times the slack. -/
theorem triP_eq_mul_slack (p : Fin 24 → ℝ) {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    triP p a b c = a * b * c * (lamFix * (a⁻¹ + b⁻¹ + c⁻¹)
      - Fh (Hp p) (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c ^ 2 / 2)) := by
  unfold triP
  field_simp

theorem sqrt_two_sub_two_mul (a : ℝ) (ha : 0 ≤ a) : Real.sqrt (2 - 2 * (1 - a ^ 2 / 2)) = a := by
  rw [show (2 - 2 * (1 - a ^ 2 / 2) : ℝ) = a ^ 2 by ring, Real.sqrt_sq ha]

/-- **The dictionary.**  The numeric certificate in inner-product variables gives the sorted
statement of Task 5b. -/
theorem triSorted_of_numCertU {ρ : Fin 5 → ℝ} {margin : ℝ} (hm : 0 ≤ margin)
    (h : NumCertU ρ margin) : TriSorted ρ := by
  intro a b c hc hcb hba ha2 hg hout
  have hlo : (0:ℝ) < chordLo := by norm_num [chordLo]
  have hc0 : 0 < c := lt_of_lt_of_le hlo hc
  have hb0 : 0 < b := lt_of_lt_of_le hc0 hcb
  have ha0 : 0 < a := lt_of_lt_of_le hb0 hba
  have hb : chordLo ≤ b := le_trans hc hcb
  have ha : chordLo ≤ a := le_trans hb hba
  set u := 1 - a ^ 2 / 2 with hu
  set v := 1 - b ^ 2 / 2 with hv
  set t := 1 - c ^ 2 / 2 with ht
  have hau : Real.sqrt (2 - 2 * u) = a := sqrt_two_sub_two_mul a ha0.le
  have hbv : Real.sqrt (2 - 2 * v) = b := sqrt_two_sub_two_mul b hb0.le
  have hct : Real.sqrt (2 - 2 * t) = c := sqrt_two_sub_two_mul c hc0.le
  have h1 : -1 ≤ u := by rw [hu]; nlinarith
  have h2 : u ≤ v := by rw [hu, hv]; nlinarith
  have h3 : v ≤ t := by rw [hv, ht]; nlinarith
  have h4 : t ≤ uHi := by rw [ht, uHi]; nlinarith
  have h5 : 0 ≤ gramU u v t := by rw [← gram_eq_gramU]; exact hg
  have h6 : ∀ m : Fin 5, ρ m < |Real.sqrt (2 - 2 * u) - (touchType m).1|
      ∨ ρ m < |Real.sqrt (2 - 2 * v) - (touchType m).2.1|
      ∨ ρ m < |Real.sqrt (2 - 2 * t) - (touchType m).2.2| := by
    intro m; rw [hau, hbv, hct]; exact hout m
  have key := h u v t h1 h2 h3 h4 h5 h6
  rw [hau, hbv, hct] at key
  rw [triP_eq_mul_slack pivots ha0 hb0 hc0]
  have hpos : 0 < a * b * c := by positivity
  have : 0 ≤ lamFix * (a⁻¹ + b⁻¹ + c⁻¹) - Fh (Hp pivots) u v t := le_trans hm key
  positivity

/-- **Task 5, from the numeric certificate**, on the corrected chord range. -/
theorem tri_nonneg_of_numCertU {ρ : Fin 5 → ℝ} {margin : ℝ} (hm : 0 ≤ margin)
    (hloc : TriLocal ρ) (h : NumCertU ρ margin) :
    ∀ a b c : ℝ, chordLo ≤ a → chordLo ≤ b → chordLo ≤ c → a ≤ 2 → b ≤ 2 → c ≤ 2 →
      0 ≤ gram a b c → 0 ≤ triP pivots a b c :=
  tri_nonneg_of hloc (triSorted_of_numCertU hm h)

end Thomson.Tri5b
