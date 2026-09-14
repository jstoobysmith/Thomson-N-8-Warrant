import Thomson.TriangleLocal.Calculus.TriLocalHC

/-! # Task 5a, bridge: explicit cubic-form coefficients `C i j k` for `rayφ3`

One Fréchet-derivative level deeper than `TriLocalHC.lean`'s `H`/`rayφ2_eq_sum`, same technique:
`rayφ3 p τ δ 0` is the third Fréchet derivative of `triPF p` at `τ`, applied three times to `δ` —
a genuine trilinear form, hence expandable into `Σ_{i,j,k} C i j k · δ_i δ_j δ_k` with
`C i j k := rayC p τ (e_i) (e_j) (e_k)` (unsymmetrized, matching `H`'s convention). -/

namespace Thomson.ThreePoint.Cert

open Thomson
open scoped ContDiff

/-- **`rayφ2` at a general point `t`**, generalizing `rayφ2_eq_rayH` (`t = 0` there); needed as the
next link in the chain-rule tower. No point-alignment rewrite is needed here (unlike
`rayφ2_eq_rayH`) because `x0` is defined to be exactly `curve t`. -/
theorem rayφ2_eq_fderiv (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) (t : ℝ) :
    rayφ2 p τ δ t =
      rayH p (τ.1 + t * δ 0, τ.2.1 + t * δ 1, τ.2.2 + t * δ 2) (δ 0, δ 1, δ 2) (δ 0, δ 1, δ 2) := by
  set x0 : ℝ × ℝ × ℝ := (τ.1 + t * δ 0, τ.2.1 + t * δ 1, τ.2.2 + t * δ 2) with hx0
  set δ' : ℝ × ℝ × ℝ := (δ 0, δ 1, δ 2) with hδ'
  have hDfx0 : HasFDerivAt (fun x => fderiv ℝ (triPF p) x) (rayH p x0) x0 := hasFDerivAt_Df p x0
  have hG : HasFDerivAt (fun x => fderiv ℝ (triPF p) x δ') ((rayH p x0).flip δ') x0 := by
    have := hDfx0.clm_apply (hasFDerivAt_const δ' x0)
    simpa using this
  have hcurve := hasDerivAt_ray_curve τ δ t
  have hcomp : HasDerivAt
      ((fun x => fderiv ℝ (triPF p) x δ') ∘ (fun s : ℝ => (τ.1 + s * δ 0, τ.2.1 + s * δ 1, τ.2.2 + s * δ 2)))
      (((rayH p x0).flip δ') δ') t :=
    HasFDerivAt.comp_hasDerivAt (hl := hG) (hf := hcurve)
  have hfun : ((fun x => fderiv ℝ (triPF p) x δ') ∘
      (fun s : ℝ => (τ.1 + s * δ 0, τ.2.1 + s * δ 1, τ.2.2 + s * δ 2))) = rayφ1 p τ δ := by
    funext s
    unfold Function.comp
    exact (rayφ1_eq_fderiv p τ δ s).symm
  rw [hfun] at hcomp
  have hval := hcomp.deriv
  unfold rayφ2
  rw [hval, ContinuousLinearMap.flip_apply]

/-- The third Fréchet derivative of `triPF p` at `τ`: a bundled trilinear form. -/
noncomputable def rayC (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) :
    (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  fderiv ℝ (fun x => rayH p x) τ

theorem D2_contDiff (p : Fin 24 → ℝ) : ContDiff ℝ ∞ (fun x : ℝ × ℝ × ℝ => rayH p x) :=
  (contDiff_infty_iff_fderiv.mp (Df_contDiff p)).2

theorem hasFDerivAt_D2 (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) :
    HasFDerivAt (fun x => rayH p x) (rayC p τ) τ :=
  ((D2_contDiff p).differentiable (by simp)).differentiableAt.hasFDerivAt

theorem hasFDerivAt_D2a (p : Fin 24 → ℝ) (τ δ' : ℝ × ℝ × ℝ) :
    HasFDerivAt (fun x => rayH p x δ') ((rayC p τ).flip δ') τ := by
  have := (hasFDerivAt_D2 p τ).clm_apply (hasFDerivAt_const δ' τ)
  simpa using this

theorem hasFDerivAt_G2 (p : Fin 24 → ℝ) (τ δ' : ℝ × ℝ × ℝ) :
    HasFDerivAt (fun x => rayH p x δ' δ') (((rayC p τ).flip δ').flip δ') τ := by
  have := (hasFDerivAt_D2a p τ δ').clm_apply (hasFDerivAt_const δ' τ)
  simpa using this

/-- **The bridge**: `rayφ3` at the base point is the third-derivative trilinear form applied to
`(δ, δ, δ)`. -/
theorem rayφ3_eq_rayC (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    rayφ3 p τ δ 0 = rayC p τ (δ 0, δ 1, δ 2) (δ 0, δ 1, δ 2) (δ 0, δ 1, δ 2) := by
  set δ' : ℝ × ℝ × ℝ := (δ 0, δ 1, δ 2) with hδ'
  have hG2 : HasFDerivAt (fun x => rayH p x δ' δ') (((rayC p τ).flip δ').flip δ') τ :=
    hasFDerivAt_G2 p τ δ'
  have hcurve := hasDerivAt_ray_curve τ δ 0
  have heq : τ = (fun s : ℝ => (τ.1 + s * δ 0, τ.2.1 + s * δ 1, τ.2.2 + s * δ 2)) 0 := by simp
  have hG2' := hG2
  nth_rewrite 2 [heq] at hG2'
  have hcomp : HasDerivAt
      ((fun x => rayH p x δ' δ') ∘ (fun s : ℝ => (τ.1 + s * δ 0, τ.2.1 + s * δ 1, τ.2.2 + s * δ 2)))
      ((((rayC p τ).flip δ').flip δ') δ') 0 :=
    HasFDerivAt.comp_hasDerivAt (hl := hG2') (hf := hcurve)
  have hfun : ((fun x => rayH p x δ' δ') ∘
      (fun s : ℝ => (τ.1 + s * δ 0, τ.2.1 + s * δ 1, τ.2.2 + s * δ 2))) = rayφ2 p τ δ := by
    funext s
    unfold Function.comp
    exact (rayφ2_eq_fderiv p τ δ s).symm
  rw [hfun] at hcomp
  have hval := hcomp.deriv
  unfold rayφ3
  rw [hval]
  simp only [ContinuousLinearMap.flip_apply]

/-- The explicit cubic-form coefficients (unsymmetrized, matching `H`'s convention). -/
noncomputable def C (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (i j k : Fin 3) : ℝ :=
  rayC p τ (basis3 i) (basis3 j) (basis3 k)

/-- **The cubic-form expansion.** `rayφ3` at the base point, in coordinates: `27` terms, one per
`(i, j, k) ∈ Fin 3 × Fin 3 × Fin 3`. -/
theorem rayφ3_eq_sum (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    rayφ3 p τ δ 0 = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, C p τ i j k * (δ i * δ j * δ k) := by
  rw [rayφ3_eq_rayC]
  have hδ : (δ 0, δ 1, δ 2) = δ 0 • basis3 0 + δ 1 • basis3 1 + δ 2 • basis3 2 := by
    simp [basis3]
  rw [hδ]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, C]
  simp only [Fin.sum_univ_three]
  ring

end Thomson.ThreePoint.Cert
