import Thomson.Certificate.Perturb
import Thomson.TriangleGlobal.Domain

/-! # Task 5b, step 1: the symmetry reduction

`triP` is invariant under permutations of the three chord lengths (`triP_swap12`, `triP_swap23`),
and so is the domain — but the *hypothesis* of Task 5b (being outside the five cubes around the
touching types) is not: the five types are listed as ordered triples, so the permuted images of a
touching point lie in the region Task 5b speaks about, and there `triP` vanishes.  A box covering
with a positive margin can therefore never prove the statement as it stands.

The fix is to sort first.  All five touching types are already listed in decreasing order
(`touchType_antitone`), so on the sorted cone `c ≤ b ≤ a` the five listed points are the *only*
zeros of `triP`.  Sorting also divides the volume to be covered by six.

This file reduces Task 5b — in fact all of Task 5 — to the sorted statement `TriSorted`,
given Task 5a (`TriLocal`).  Nothing here depends on the certificate data.

The chord range is `[chordLo, 2]` with `chordLo = 9619/10000`, not `[24/25, 2]`: see
`Thomson.TriangleGlobal.Domain` — on `[24/25, 2]³` the statement is false. -/

namespace Thomson.Tri5b

open Thomson

/-- The local radii of Task 5a, one per touching type (`Thomson.rhoLocal`, or the per-type
`rho0` of the plan).  Everything below is uniform in them. -/
noncomputable def rho : Fin 5 → ℝ := fun _ => 1 / 500

/-- The Gram polynomial in the chord variables: the domain of Task 5. -/
noncomputable def gram (a b c : ℝ) : ℝ :=
  1 + 2 * (1 - a ^ 2 / 2) * (1 - b ^ 2 / 2) * (1 - c ^ 2 / 2)
    - (1 - a ^ 2 / 2) ^ 2 - (1 - b ^ 2 / 2) ^ 2 - (1 - c ^ 2 / 2) ^ 2

theorem gram_swap12 (a b c : ℝ) : gram a b c = gram b a c := by unfold gram; ring
theorem gram_swap23 (a b c : ℝ) : gram a b c = gram a c b := by unfold gram; ring

/-! ## Sorting -/

/-- Any symmetric predicate that holds on the decreasing cone holds everywhere. -/
theorem of_sorted {P : ℝ → ℝ → ℝ → Prop}
    (h12 : ∀ x y z, P x y z → P y x z) (h23 : ∀ x y z, P x y z → P x z y)
    (hs : ∀ x y z, z ≤ y → y ≤ x → P x y z) (a b c : ℝ) : P a b c := by
  rcases le_total a b with hab | hab <;> rcases le_total b c with hbc | hbc <;>
    rcases le_total a c with hac | hac
  -- a ≤ b, b ≤ c, a ≤ c : sorted is (c, b, a)
  · exact h12 _ _ _ (h23 _ _ _ (h12 _ _ _ (hs c b a hab hbc)))
  -- a ≤ b, b ≤ c, c ≤ a : then a = b = c
  · exact h12 _ _ _ (h23 _ _ _ (h12 _ _ _ (hs c b a hab hbc)))
  -- a ≤ b, c ≤ b, a ≤ c : sorted is (b, c, a)
  · exact h12 _ _ _ (h23 _ _ _ (hs b c a hac hbc))
  -- a ≤ b, c ≤ b, c ≤ a : sorted is (b, a, c)
  · exact h12 _ _ _ (hs b a c hac hab)
  -- b ≤ a, b ≤ c, a ≤ c : sorted is (c, a, b)
  · exact h23 _ _ _ (h12 _ _ _ (hs c a b hab hac))
  -- b ≤ a, b ≤ c, c ≤ a : sorted is (a, c, b)
  · exact h23 _ _ _ (hs a c b hbc hac)
  -- b ≤ a, c ≤ b, a ≤ c : then a = b = c
  · exact hs a b c hbc hab
  -- b ≤ a, c ≤ b, c ≤ a : sorted is (a, b, c)
  · exact hs a b c hbc hab

/-! ## The two leaves -/

/-- Task 5a, as a hypothesis: local nonnegativity on the cube of radius `rho` at each type. -/
def TriLocal (ρ : Fin 5 → ℝ) : Prop := ∀ (m : Fin 5) (a b c : ℝ),
  |a - (touchType m).1| ≤ ρ m → |b - (touchType m).2.1| ≤ ρ m → |c - (touchType m).2.2| ≤ ρ m →
  0 ≤ triP pivots a b c

/-- The sorted form of Task 5b: nonnegativity on the decreasing cone, away from the five types. -/
def TriSorted (ρ : Fin 5 → ℝ) : Prop :=
  ∀ a b c : ℝ, chordLo ≤ c → c ≤ b → b ≤ a → a ≤ 2 → 0 ≤ gram a b c →
  (∀ m : Fin 5, ρ m < |a - (touchType m).1| ∨ ρ m < |b - (touchType m).2.1|
    ∨ ρ m < |c - (touchType m).2.2|) →
  0 ≤ triP pivots a b c

/-- **The reduction.**  From Task 5a and the sorted statement, the *whole* of Task 5 follows —
the hypothesis of Task 5b (being outside the five cubes) is not needed once the triple is
sorted. -/
theorem tri_nonneg_of {ρ : Fin 5 → ℝ} (hloc : TriLocal ρ) (hsort : TriSorted ρ) :
    ∀ a b c : ℝ, chordLo ≤ a → chordLo ≤ b → chordLo ≤ c → a ≤ 2 → b ≤ 2 → c ≤ 2 →
      0 ≤ gram a b c → 0 ≤ triP pivots a b c := by
  intro a b c
  revert a b c
  have key : ∀ a b c : ℝ, (chordLo ≤ a → chordLo ≤ b → chordLo ≤ c → a ≤ 2 → b ≤ 2 → c ≤ 2 →
      0 ≤ gram a b c → 0 ≤ triP pivots a b c) := by
    refine of_sorted (P := fun a b c => chordLo ≤ a → chordLo ≤ b → chordLo ≤ c → a ≤ 2 →
      b ≤ 2 → c ≤ 2 → 0 ≤ gram a b c → 0 ≤ triP pivots a b c) ?_ ?_ ?_
    · intro x y z h hx hy hz hx2 hy2 hz2 hg
      rw [triP_swap12]
      exact h hy hx hz hy2 hx2 hz2 (by rw [gram_swap12] at hg; exact hg)
    · intro x y z h hx hy hz hx2 hy2 hz2 hg
      rw [triP_swap23]
      exact h hx hz hy hx2 hz2 hy2 (by rw [gram_swap23] at hg; exact hg)
    · intro x y z hzy hyx hx hy hz hx2 hy2 hz2 hg
      by_cases hc : ∃ m : Fin 5, |x - (touchType m).1| ≤ ρ m ∧ |y - (touchType m).2.1| ≤ ρ m
          ∧ |z - (touchType m).2.2| ≤ ρ m
      · obtain ⟨m, h1, h2, h3⟩ := hc
        exact hloc m x y z h1 h2 h3
      · push_neg at hc
        refine hsort x y z hz hzy hyx hx2 hg fun m => ?_
        by_contra hcon
        push_neg at hcon
        exact absurd (hc m hcon.1 hcon.2.1) (not_lt.mpr hcon.2.2)
  exact key

end Thomson.Tri5b
