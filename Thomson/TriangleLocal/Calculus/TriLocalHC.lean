import Thomson.TriangleLocal.Calculus.TriLocalDeriv
import Thomson.TriangleLocal.Calculus.TriLocalPerturb

/-! # Task 5a, bridge: explicit Hessian coefficients `H i j` for `rayφ2`

The peer session building the numeric patch-covering certificate (`Thomson/TriangleLocal/`, their
own interval enclosures `HI_m`/`CI_m` of the Hessian/cubic-form coefficients) needs `rayφ2`
(`TriLocalDeriv.lean`) unfolded into explicit real coefficients `H i j` with
`rayφ2 p τ δ 0 = Σ_{i,j} H i j * δ i * δ j`, together with the `pivots`-vs-`pivotsNum` perturbation
bound on each `H i j` (extending `TriLocalPerturb.lean`'s affine-in-`p` technique). This file does
the `H i j` half; the analogous `C i j k` for `rayφ3` (needing a *third* Fréchet derivative) is
**not attempted** here — see the status report for why (budget), and the identical technique
below generalizes to it directly.

**The construction.** `rayφ2 p τ δ 0` is the second derivative, at the base point, of `triP p`
restricted to the ray `t ↦ τ + tδ`. This is a *second directional derivative*, hence the value
`⟨δ, Hδ⟩` of the second Fréchet derivative (Hessian) of `triPF p` at `τ`, applied twice to `δ`.
Mathlib gives this cleanly: `contDiff_infty_iff_fderiv` peels off one order of `ContDiff` into
`fderiv`, exactly like `contDiff_infty_iff_deriv` did for `deriv` in `TriLocalDeriv.lean`; then
`HasFDerivAt.clm_apply` (product/evaluation rule) plus `HasFDerivAt.comp_hasDerivAt` (the same
chain-rule tool `rayφ1_zero_eq` used) identifies `rayφ2 p τ δ 0` with the bundled second derivative
`rayH p τ` (a `ℝ×ℝ×ℝ →L[ℝ] ℝ×ℝ×ℝ →L[ℝ] ℝ`, i.e. a bona fide bilinear form) applied to `(δ, δ)`.
From there the `Σ H i j δ_i δ_j` expansion is pure bilinearity (`map_add`/`map_smul`, exactly as
`rayφ1_zero_eq` used linearity of `fderiv`). -/

namespace Thomson.ThreePoint.Cert

open Thomson
open scoped ContDiff

/-- **The ray-derivative-at-`t`, in terms of the Fréchet derivative at the moving point.**
Generalizes `rayφ1_zero_eq_fderiv` (`t = 0` there) to every `t`; same proof, no rewriting needed
since the point `curve t` is already syntactically the argument of `fderiv`. -/
theorem rayφ1_eq_fderiv (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) (t : ℝ) :
    rayφ1 p τ δ t =
      fderiv ℝ (triPF p) (τ.1 + t * δ 0, τ.2.1 + t * δ 1, τ.2.2 + t * δ 2) (δ 0, δ 1, δ 2) := by
  set x0 : ℝ × ℝ × ℝ := (τ.1 + t * δ 0, τ.2.1 + t * δ 1, τ.2.2 + t * δ 2) with hx0
  have hfd : HasFDerivAt (triPF p) (fderiv ℝ (triPF p) x0) x0 :=
    ((triPF_contDiff p).differentiable (by simp)).differentiableAt (x := x0) |>.hasFDerivAt
  have hcurve := hasDerivAt_ray_curve τ δ t
  have hcomp : HasDerivAt
      (triPF p ∘ (fun s : ℝ => (τ.1 + s * δ 0, τ.2.1 + s * δ 1, τ.2.2 + s * δ 2)))
      (fderiv ℝ (triPF p) x0 (δ 0, δ 1, δ 2)) t :=
    HasFDerivAt.comp_hasDerivAt (hl := hfd) (hf := hcurve)
  unfold rayφ1
  rw [rayP_eq_comp p τ δ]
  exact hcomp.deriv

/-- The Hessian (second Fréchet derivative) of `triPF p` at `τ`, as a bundled bilinear form. -/
noncomputable def rayH (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) :
    (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  fderiv ℝ (fun x => fderiv ℝ (triPF p) x) τ

theorem Df_contDiff (p : Fin 24 → ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ × ℝ × ℝ => fderiv ℝ (triPF p) x) :=
  (contDiff_infty_iff_fderiv.mp (triPF_contDiff p)).2

theorem hasFDerivAt_Df (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) :
    HasFDerivAt (fun x => fderiv ℝ (triPF p) x) (rayH p τ) τ :=
  ((Df_contDiff p).differentiable (by simp)).differentiableAt.hasFDerivAt

/-- **The bridge**: `rayφ2` at the base point is the Hessian bilinear form applied to `(δ, δ)`. -/
theorem rayφ2_eq_rayH (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    rayφ2 p τ δ 0 = rayH p τ (δ 0, δ 1, δ 2) (δ 0, δ 1, δ 2) := by
  set δ' : ℝ × ℝ × ℝ := (δ 0, δ 1, δ 2) with hδ'
  set Df : ℝ × ℝ × ℝ → (ℝ × ℝ × ℝ →L[ℝ] ℝ) := fun x => fderiv ℝ (triPF p) x with hDf
  have hDfτ : HasFDerivAt Df (rayH p τ) τ := hasFDerivAt_Df p τ
  have hconst : HasFDerivAt (fun _ : ℝ × ℝ × ℝ => δ') (0 : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ)) τ :=
    hasFDerivAt_const δ' τ
  have hG : HasFDerivAt (fun x => Df x δ') ((rayH p τ).flip δ') τ := by
    have := hDfτ.clm_apply hconst
    simpa using this
  have hcurve := hasDerivAt_ray_curve τ δ 0
  have heq : τ = (fun s : ℝ => (τ.1 + s * δ 0, τ.2.1 + s * δ 1, τ.2.2 + s * δ 2)) 0 := by simp
  have hG' := hG
  nth_rewrite 2 [heq] at hG'
  have hcomp : HasDerivAt
      ((fun x => Df x δ') ∘ (fun s : ℝ => (τ.1 + s * δ 0, τ.2.1 + s * δ 1, τ.2.2 + s * δ 2)))
      (((rayH p τ).flip δ') δ') 0 :=
    HasFDerivAt.comp_hasDerivAt (hl := hG') (hf := hcurve)
  have hfun : ((fun x => Df x δ') ∘ (fun s : ℝ => (τ.1 + s * δ 0, τ.2.1 + s * δ 1, τ.2.2 + s * δ 2)))
      = rayφ1 p τ δ := by
    funext t
    unfold Df Function.comp
    exact (rayφ1_eq_fderiv p τ δ t).symm
  rw [hfun] at hcomp
  have hval := hcomp.deriv
  unfold rayφ2
  rw [hval, ContinuousLinearMap.flip_apply]

/-- The standard basis of `ℝ × ℝ × ℝ`, indexed by `Fin 3` (matching `rayP`'s coordinate order). -/
def basis3 : Fin 3 → ℝ × ℝ × ℝ := ![(1, 0, 0), (0, 1, 0), (0, 0, 1)]

/-- The explicit matrix entries (unsymmetrized: `H i j` need not equal `H j i`, which is fine —
see the file docstring, the peer's consumer does not need symmetry). -/
noncomputable def H (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (i j : Fin 3) : ℝ :=
  rayH p τ (basis3 i) (basis3 j)

/-- **The quadratic-form expansion.** `rayφ2` at the base point, in coordinates. -/
theorem rayφ2_eq_sum (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    rayφ2 p τ δ 0 =
      H p τ 0 0 * δ 0 * δ 0 + H p τ 0 1 * δ 0 * δ 1 + H p τ 0 2 * δ 0 * δ 2 +
      H p τ 1 0 * δ 1 * δ 0 + H p τ 1 1 * δ 1 * δ 1 + H p τ 1 2 * δ 1 * δ 2 +
      H p τ 2 0 * δ 2 * δ 0 + H p τ 2 1 * δ 2 * δ 1 + H p τ 2 2 * δ 2 * δ 2 := by
  rw [rayφ2_eq_rayH]
  have hδ : (δ 0, δ 1, δ 2) = δ 0 • basis3 0 + δ 1 • basis3 1 + δ 2 • basis3 2 := by
    simp [basis3]
  rw [hδ]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, H]
  ring

end Thomson.ThreePoint.Cert
