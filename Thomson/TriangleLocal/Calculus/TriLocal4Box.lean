import Thomson.TriangleLocal.Calculus.TriLocal4

/-! # Task 5a, redesign: a quartic-remainder lower bound with the cubic term kept exact

The 3-variable assembly analogue of `TriLocalBox.lean`'s `local_nonneg_of_hessian_box`, but one
order deeper: keeps the cubic term `φ3 δ 0` *exact* (signed) rather than absorbing it into a crude
absolute bound, and only bounds the *quartic* remainder crudely. This is the calculus core the
redesign needs: independently confirmed (two sessions) that absorbing the whole cubic term into a
flat `K‖δ‖²` bound (`local_nonneg_of_hessian_box`'s approach) is too lossy at `rhoLocal = 1/500` —
the margin only survives to roughly a quarter of that radius. Keeping `φ3 δ 0` exact recovers real
margin (the peer session's numbers: the bracket `q(e) − ρ|c3(e)| − ρ²·T4(e)` stays `≥ 0.83·q(e)`
across all five types), at the cost of needing a genuine sign/case analysis of `φ3 δ 0` against
`φ2 δ 0` per direction `δ` — a numeric ("patch covering") task this lemma does not attempt; it only
produces the *lower bound formula* a patch-covering argument would need to show is `≥ 0`
everywhere on the cube. See the file docstring of `TriLocal4.lean` and the status report for what
is and is not done. -/

namespace Thomson.ThreePoint.Cert

open Set

/-- **Quartic lower bound from a double zero, cubic term exact.**  `φ δ` vanishes to second order
at `0` in every direction `δ` (`hzero`, `hgrad`, exactly as in `local_nonneg_of_hessian_box`); given
a crude bound `M` on the *fourth* directional derivative on `[0,1]` along the ray to `τ + δ`
(`hrem4` — homogeneous quartic in `δ`, i.e. `M · ‖δ‖⁴`, the crude ingredient), the target function at
`τ + δ` is bounded below by the *exact* quadratic-plus-cubic Taylor terms minus the quartic
remainder. No nonnegativity is asserted here — that is left to the caller, who must show the
right-hand side is `≥ 0` for every admissible `δ` (the surface/patch-covering step). -/
theorem taylor4_lower {φ φ1 φ2 φ3 φ4 : (Fin 3 → ℝ) → ℝ → ℝ} {M : ℝ}
    (h1 : ∀ δ x, HasDerivAt (φ δ) (φ1 δ x) x)
    (h2 : ∀ δ x, HasDerivAt (φ1 δ) (φ2 δ x) x)
    (h3 : ∀ δ x, HasDerivAt (φ2 δ) (φ3 δ x) x)
    (h4 : ∀ δ x, HasDerivAt (φ3 δ) (φ4 δ x) x)
    (hzero : ∀ δ, φ δ 0 = 0)
    (hgrad : ∀ δ, φ1 δ 0 = 0)
    (δ : Fin 3 → ℝ)
    (hrem4 : ∀ x ∈ Icc (0 : ℝ) 1, |φ4 δ x| ≤ M * (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) ^ 2) :
    φ2 δ 0 / 2 + φ3 δ 0 / 6 - M * (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) ^ 2 / 24 ≤ φ δ 1 := by
  set S : ℝ := δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2 with hS
  have hl : ∀ x ∈ Icc (0 : ℝ) 1, -(M * S ^ 2) ≤ φ4 δ x := fun x hx => by
    have := hrem4 x hx
    rw [abs_le] at this
    linarith [this.1]
  have hbase := taylor4_right (h1 δ) (h2 δ) (h3 δ) (h4 δ) (a := 0) (b := 1) (l := -(M * S ^ 2)) hl
    1 ⟨zero_le_one, le_refl 1⟩
  obtain ⟨-, -, -, hfourth⟩ := hbase
  rw [hzero δ, hgrad δ] at hfourth
  linarith [hfourth]

end Thomson.ThreePoint.Cert
