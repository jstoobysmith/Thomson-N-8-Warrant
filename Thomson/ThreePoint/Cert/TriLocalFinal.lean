import Thomson.ThreePoint.Cert.TriLocal4Box
import Thomson.ThreePoint.Cert.TriLocalDeriv4
import Thomson.ThreePoint.Cert.TriLocalHC3

/-! # Task 5a: the final assembly, modulo the peer session's numeric certificate

Combines `rayP_taylor4_lower` (`TriLocalDeriv4.lean`) with the coefficient bridges
`rayφ2_eq_sum`/`rayφ3_eq_sum` (`TriLocalHC.lean`/`TriLocalHC3.lean`) into a theorem with exactly
`Thomson.Task5a`'s shape, taking the numeric patch-covering certificate
(`Thomson/TriLocalCert/Patch.lean`, a peer session's separate, still-in-progress work in the main
tree — not importable from this worktree, so `Qf`/`Kf`/`N2`/`bracket` are restated here verbatim,
matching their exact definitions/names field-for-field so their `bracket_nonneg` can be plugged in
by name once it lands) as explicit hypotheses, exactly the way `Task1a`/`Task1b` are taken as
hypotheses elsewhere in `Tasks.lean` rather than waited on. No numeric claim is asserted here — only
the calculus assembly; `hbracket`/`hrem4` are the honest "someone still has to prove this" seams. -/

namespace Thomson.ThreePoint.Cert

open Thomson Finset Set

/-! ## `Qf`, `Kf`, `N2`, `bracket` — restated to match `Thomson.TriLocalCert.Patch` field-for-field -/

noncomputable def Qf (H : Fin 3 → Fin 3 → ℝ) (e : Fin 3 → ℝ) : ℝ := ∑ a, ∑ b, H a b * e a * e b

noncomputable def Kf (C : Fin 3 → Fin 3 → Fin 3 → ℝ) (e : Fin 3 → ℝ) : ℝ :=
  ∑ a, ∑ b, ∑ c, C a b c * e a * e b * e c

noncomputable def N2 (e : Fin 3 → ℝ) : ℝ := e 0 ^ 2 + e 1 ^ 2 + e 2 ^ 2

noncomputable def bracket (H : Fin 3 → Fin 3 → ℝ) (C : Fin 3 → Fin 3 → Fin 3 → ℝ) (M : ℝ)
    (δ : Fin 3 → ℝ) : ℝ :=
  Qf H δ / 2 + Kf C δ / 6 - M * N2 δ ^ 2 / 24

theorem rayφ2_eq_Qf (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    rayφ2 p τ δ 0 = Qf (H p τ) δ := by
  rw [rayφ2_eq_sum]
  simp only [Qf, Fin.sum_univ_three]
  ring

theorem rayφ3_eq_Kf (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    rayφ3 p τ δ 0 = Kf (C p τ) δ := by
  rw [rayφ3_eq_sum]
  unfold Kf
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl
    fun c _ => ?_
  ring

/-! ## The assembly -/

/-- **Task 5a for a fixed touching type `m`, modulo the numeric certificate.** `hval`/`hder` are
exactly `Thomson.triP_tight m h1a`'s two components; `hbracket` is exactly the conclusion of
`Thomson.TriLocalCert.bracket_nonneg` once it exists; `hrem4` is the raw quartic remainder bound
their certificate's `M` must also satisfy (the ingredient `rayP_taylor4_lower` needs beyond
`bracket ≥ 0`). Radius `1/500` matches `Tasks.lean`'s `rhoLocal` and the peer's `bracket_nonneg`
literally (not imported, to keep this file free of the read-only `Tasks.lean` dependency). -/
theorem triP_local_of_bracket (p : Fin 24 → ℝ) (m : Fin 5) (M : ℝ)
    (hval : triP p (touchType m).1 (touchType m).2.1 (touchType m).2.2 = 0)
    (hder : ∀ c : Fin 3, deriv (triD p m c) 0 = 0)
    (hbracket : ∀ δ : Fin 3 → ℝ, (∀ i, |δ i| ≤ 1 / 500) →
      0 ≤ bracket (H p (touchType m)) (C p (touchType m)) M δ)
    (hrem4 : ∀ δ : Fin 3 → ℝ, (∀ i, |δ i| ≤ 1 / 500) → ∀ x ∈ Icc (0 : ℝ) 1,
      |rayφ4 p (touchType m) δ x| ≤ M * (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) ^ 2) :
    ∀ a b c : ℝ, |a - (touchType m).1| ≤ 1 / 500 → |b - (touchType m).2.1| ≤ 1 / 500 →
      |c - (touchType m).2.2| ≤ 1 / 500 → 0 ≤ triP p a b c := by
  set τ := touchType m with hτ
  intro a b c ha hb hc
  set δ : Fin 3 → ℝ := ![a - τ.1, b - τ.2.1, c - τ.2.2] with hδdef
  have hδbound : ∀ i, |δ i| ≤ 1 / 500 := by
    intro i
    fin_cases i <;> simp only [hδdef]
    · exact ha
    · exact hb
    · exact hc
  have hzero : ∀ δ' : Fin 3 → ℝ, rayP p τ δ' 0 = 0 := fun δ' => by rw [rayP_zero]; exact hval
  have hgrad : ∀ δ' : Fin 3 → ℝ, rayφ1 p τ δ' 0 = 0 := by
    intro δ'
    rw [rayφ1_zero_eq]
    rw [hder 0, hder 1, hder 2]
    ring
  have hlow := rayP_taylor4_lower p τ hzero hgrad δ (hrem4 δ hδbound)
  rw [rayφ2_eq_Qf, rayφ3_eq_Kf] at hlow
  have hbrk := hbracket δ hδbound
  unfold bracket N2 at hbrk
  have hrayeq : rayP p τ δ 1 = triP p a b c := by
    unfold rayP
    have e0 : τ.1 + 1 * δ 0 = a := by simp [hδdef]
    have e1 : τ.2.1 + 1 * δ 1 = b := by simp [hδdef]
    have e2 : τ.2.2 + 1 * δ 2 = c := by simp [hδdef]
    rw [e0, e1, e2]
  rw [hrayeq] at hlow
  linarith [hlow, hbrk]

/-- **Task 5a, all five types, modulo the numeric certificate.** Exactly `Thomson.Task5a`'s shape
(`∀ m : Fin 5, ∀ a b c, ... → 0 ≤ triP pivots a b c`), for a general `p`, given the per-type
certificate data `M`. -/
theorem triP_local_of_bracket_all (p : Fin 24 → ℝ) (M : Fin 5 → ℝ)
    (hval : ∀ m : Fin 5, triP p (touchType m).1 (touchType m).2.1 (touchType m).2.2 = 0)
    (hder : ∀ m : Fin 5, ∀ c : Fin 3, deriv (triD p m c) 0 = 0)
    (hbracket : ∀ m : Fin 5, ∀ δ : Fin 3 → ℝ, (∀ i, |δ i| ≤ 1 / 500) →
      0 ≤ bracket (H p (touchType m)) (C p (touchType m)) (M m) δ)
    (hrem4 : ∀ m : Fin 5, ∀ δ : Fin 3 → ℝ, (∀ i, |δ i| ≤ 1 / 500) → ∀ x ∈ Icc (0 : ℝ) 1,
      |rayφ4 p (touchType m) δ x| ≤ M m * (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) ^ 2) :
    ∀ m : Fin 5, ∀ a b c : ℝ, |a - (touchType m).1| ≤ 1 / 500 →
      |b - (touchType m).2.1| ≤ 1 / 500 → |c - (touchType m).2.2| ≤ 1 / 500 →
      0 ≤ triP p a b c :=
  fun m => triP_local_of_bracket p m (M m) (hval m) (hder m) (hbracket m) (hrem4 m)

end Thomson.ThreePoint.Cert
