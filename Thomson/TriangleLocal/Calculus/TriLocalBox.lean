import Thomson.TriangleLocal.Calculus.TriLocal

/-! # Task 5a, continued: a cube-restricted version of `local_nonneg_of_hessian`

**Why this file exists, and why it does not just edit `TriLocal.lean`.**  `TriLocal.lean`'s
`local_nonneg_of_hessian` is correct as proved, but on reflection its `hrem` hypothesis is stated
as `∀ δ : Fin 3 → ℝ, ...` — literally for *every* direction, with no bound on `‖δ‖`.  For an actual
polynomial third derivative `φ3 δ x` (a *cubic* form in `δ`, homogeneous of degree 3), no fixed `K`
can make `|φ3 δ x| ≤ K·(δ0²+δ1²+δ2²)` (a *quadratic* bound) hold for unboundedly large `δ` — cubic
growth eventually beats quadratic growth for any fixed `K`.  So the honest statement anyone
instantiating this for `triP` can actually prove only holds on a bounded cube (matching
`docs/history/T5a-TriLocal.md`, which always bounds the remainder "on the cube `touchType m ± ρ`").  The
previous file is left untouched (per the task's own instruction, and because `taylor3_right` /
`taylor3_left` / `centred3_lower` there are all still correct and reused here); this file adds the
corrected, cube-restricted assembly lemma that is actually usable.  Note `hhess` needs no such
restriction: `φ2 δ 0` is *exactly* `δᵀ H δ` for the (δ-independent) Hessian matrix `H` at the base
point, a genuinely homogeneous-degree-2 form, so a margin `lam·‖δ‖² ≤ φ2 δ 0` valid for all `δ` is
the correct, provable statement (and is what an LDL certificate on `H` gives directly). -/

namespace Thomson.ThreePoint.Cert

open Set

/-- **Taylor-to-second-order nonnegativity, from a double zero, in three variables, on a cube.**
Same as `local_nonneg_of_hessian`, except the cubic remainder bound `hrem` (and the conclusion) are
only required/given for directions `δ` inside the cube `|δ i| ≤ ρ` — the version that can actually
be instantiated for a genuine polynomial third derivative. -/
theorem local_nonneg_of_hessian_box {φ φ1 φ2 φ3 : (Fin 3 → ℝ) → ℝ → ℝ} {lam K ρ : ℝ}
    (h1 : ∀ δ x, HasDerivAt (φ δ) (φ1 δ x) x)
    (h2 : ∀ δ x, HasDerivAt (φ1 δ) (φ2 δ x) x)
    (h3 : ∀ δ x, HasDerivAt (φ2 δ) (φ3 δ x) x)
    (hzero : ∀ δ, φ δ 0 = 0)
    (hgrad : ∀ δ, φ1 δ 0 = 0)
    (hhess : ∀ δ : Fin 3 → ℝ, lam * (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) ≤ φ2 δ 0)
    (hrem : ∀ δ : Fin 3 → ℝ, (∀ i, |δ i| ≤ ρ) → ∀ x ∈ Icc (0 : ℝ) 1,
      |φ3 δ x| ≤ K * (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2))
    (hmargin : K ≤ 3 * lam) {δ : Fin 3 → ℝ} (hδ : ∀ i, |δ i| ≤ ρ) :
    0 ≤ φ δ 1 := by
  set S : ℝ := δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2 with hS
  have hSnn : 0 ≤ S := by positivity
  have hl : ∀ x ∈ Icc (0 : ℝ) 1, -(K * S) ≤ φ3 δ x := fun x hx => by
    have := hrem δ hδ x hx
    rw [abs_le] at this
    linarith [this.1]
  have hbase := taylor3_right (h1 δ) (h2 δ) (h3 δ) (a := 0) (b := 1) (l := -(K * S)) hl 1
    ⟨le_refl 0 |>.trans zero_le_one, le_refl 1⟩
  obtain ⟨-, -, hthird⟩ := hbase
  rw [hzero δ, hgrad δ] at hthird
  have hhess' := hhess δ
  rw [← hS] at hhess'
  nlinarith [hthird, hhess', hmargin, hSnn]

end Thomson.ThreePoint.Cert
