import Thomson.ThreePoint.Cert.TriLocalDeriv

/-! # Task 5a, Step 3: assembly

Combines the generic Taylor lemma (`Cert/TriLocalBox.lean`) with the `triP`-specific derivative
chain (`Cert/TriLocalDeriv.lean`) into a single theorem with exactly the shape of one instance of
`Thomson.Task5a` (as restructured: `Task5a : Prop := ∀ m : Fin 5, ∀ a b c : ℝ, ... → 0 ≤ triP
pivots a b c`), for a fixed type `m`, taking as hypotheses:

* `hval`/`hder`: the "vanishes to second order" facts — exactly what `Thomson.triP_tight m h1a`
  provides once `Task1a` is discharged (not assumed or reproved here, kept fully general over `p`);
* `hhess`/`hrem`/`hmargin`: the numeric Hessian-margin and third-derivative-bound certificate —
  **still open**, see the file docstring of `TriLocalDeriv.lean` and the final status report. No
  numeric values are asserted here; they are universally-quantified hypotheses the caller must
  supply (from a generated certificate, once it exists).

This file is the "one-shot instantiation" the status report describes: once someone supplies
`hhess`/`hrem` with concrete `lam`, `K` (and, for `pivots` specifically, folds in the
`pivotEps`-perturbation from `pivotsNum`), `triP_local_of` closes `triP_local`/`Task5a` for that
`m` directly — no further calculus is needed. -/

namespace Thomson.ThreePoint.Cert

open Thomson Set

/-- **Task 5a for a fixed touching type `m`, modulo the numeric certificate.**  This is the
"one-shot instantiation" lemma: give it (1) that `triP p` vanishes to second order at
`touchType m` (`hval`, `hder` — exactly `Thomson.triP_tight m h1a`), and (2) a Hessian margin
`lam` and a cube-`ρ` third-derivative bound `K` with `K ≤ 3·lam` for `triP p`'s *own* second and
third ray-derivatives (`rayφ2`, `rayφ3` — not `pivotsNum`'s, so if `p = pivots`, the caller's
`hhess`/`hrem` must already have absorbed the `pivots`-vs-`pivotsNum` perturbation, e.g. via
`Thomson.triP_sub_pivotsNum_le`-style bounds), and it produces the exact conclusion of one branch
of `Thomson.Task5a`. -/
theorem triP_local_of (p : Fin 24 → ℝ) (m : Fin 5) (ρ lam K : ℝ)
    (hval : triP p (touchType m).1 (touchType m).2.1 (touchType m).2.2 = 0)
    (hder : ∀ c : Fin 3, deriv (triD p m c) 0 = 0)
    (hhess : ∀ δ : Fin 3 → ℝ, lam * (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) ≤ rayφ2 p (touchType m) δ 0)
    (hrem : ∀ δ : Fin 3 → ℝ, (∀ i, |δ i| ≤ ρ) → ∀ x ∈ Icc (0 : ℝ) 1,
      |rayφ3 p (touchType m) δ x| ≤ K * (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2))
    (hmargin : K ≤ 3 * lam) :
    ∀ a b c : ℝ, |a - (touchType m).1| ≤ ρ → |b - (touchType m).2.1| ≤ ρ →
      |c - (touchType m).2.2| ≤ ρ → 0 ≤ triP p a b c := by
  set τ := touchType m with hτ
  intro a b c ha hb hc
  set δ : Fin 3 → ℝ := ![a - τ.1, b - τ.2.1, c - τ.2.2] with hδdef
  have hδ0 : δ 0 = a - τ.1 := by simp [hδdef]
  have hδ1 : δ 1 = b - τ.2.1 := by simp [hδdef]
  have hδ2 : δ 2 = c - τ.2.2 := by simp [hδdef]
  have hδbound : ∀ i, |δ i| ≤ ρ := by
    intro i
    fin_cases i <;> simp only [hδdef]
    · exact ha
    · exact hb
    · exact hc
  have hrayeq : rayP p τ δ 1 = triP p a b c := by
    unfold rayP
    rw [hδ0, hδ1, hδ2]
    ring_nf
  have hzero : ∀ δ' : Fin 3 → ℝ, rayP p τ δ' 0 = 0 := by
    intro δ'; rw [rayP_zero]; exact hval
  have hgrad : ∀ δ' : Fin 3 → ℝ, rayφ1 p τ δ' 0 = 0 := by
    intro δ'
    rw [rayφ1_zero_eq p m δ']
    rw [hder 0, hder 1, hder 2]
    ring
  have := local_nonneg_of_hessian_box (φ := rayP p τ) (φ1 := rayφ1 p τ) (φ2 := rayφ2 p τ)
    (φ3 := rayφ3 p τ) (lam := lam) (K := K) (ρ := ρ)
    (rayP_hasDerivAt p τ) (rayφ1_hasDerivAt p τ) (rayφ2_hasDerivAt p τ)
    hzero hgrad hhess hrem hmargin (δ := δ) hδbound
  rwa [hrayeq] at this

end Thomson.ThreePoint.Cert
