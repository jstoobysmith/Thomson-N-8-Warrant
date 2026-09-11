import Thomson.ThreePoint.Linear
import Thomson.ThreePoint.Cert.TriLocalBox

/-! # Task 5a, Step 1: the `HasDerivAt` chain for `triP pivots` along a ray

This is item (1) of the remaining work flagged in the Task 5a status report: producing, for the
polynomial `triP p` (`Thomson.ThreePoint.Linear`, read-only), the `HasDerivAt` chain that
`local_nonneg_of_hessian_box` (`Cert/TriLocalBox.lean`) needs, together with the fact that it
vanishes to second order at a touching type in *every* direction (not just the coordinate
directions `triD` already covers) — the multivariable chain-rule step the task plan calls
`E.hasDerivAt_curve`.

No numeric certificate (Hessian margin `lam`, third-derivative bound `K`) is built here — those are
still open (`plans/T5a-TriLocal.md` §4/§5/§7); this file only builds the calculus scaffolding they
plug into, matching the file's own note that this piece is "mechanical but fiddly". -/

namespace Thomson.ThreePoint.Cert

open Thomson Matrix
open scoped ContDiff

/-! ## Step 1a: `triP p` is `C^∞` (jointly, and along any polynomial ray)

Mirrors `Q3_differentiable_comp`/`Fh_differentiable_comp` (`Linear.lean`), but for `ContDiff` and
over an arbitrary normed space `E` (not just `E = ℝ`) — we need both the one-variable ray
restriction (`E = ℝ`) and the joint three-variable function (`E = ℝ × ℝ × ℝ`) below. -/

theorem Q3_contDiff (k : ℕ) : ContDiff ℝ ∞ (fun x : ℝ × ℝ × ℝ => Q3 k x.1 x.2.1 x.2.2) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 => simp only [Q3]; fun_prop
  | k + 6 => simp only [Q3]; fun_prop

@[fun_prop]
theorem Q3_contDiff_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ)
    {f g h : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ fun s => Q3 k (f s) (g s) (h s) :=
  (Q3_contDiff k).comp (hf.prodMk (hg.prodMk hh))

@[fun_prop]
theorem Fh_contDiff_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ) {f g h : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ fun s => Fh H (f s) (g s) (h s) := by
  unfold Fh
  simp only [Matrix.mul_apply, S3, Y3, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply,
    Matrix.transpose_apply, smul_eq_mul]
  fun_prop

/-- `triP p` as a joint function of the point in `ℝ × ℝ × ℝ`. -/
noncomputable def triPF (p : Fin 24 → ℝ) : ℝ × ℝ × ℝ → ℝ := fun x => triP p x.1 x.2.1 x.2.2

theorem triPF_contDiff (p : Fin 24 → ℝ) : ContDiff ℝ ∞ (triPF p) := by
  unfold triPF triP; fun_prop

/-- `triP p` restricted to the ray `t ↦ τ + t·δ` from a point `τ`, in the direction `δ`. -/
noncomputable def rayP (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  triP p (τ.1 + t * δ 0) (τ.2.1 + t * δ 1) (τ.2.2 + t * δ 2)

theorem rayP_contDiff (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    ContDiff ℝ ∞ (rayP p τ δ) := by
  unfold rayP triP; fun_prop

/-! ## Step 1b: the `HasDerivAt` chain, from `C^∞`

`contDiff_infty_iff_deriv : ContDiff 𝕜 ∞ f ↔ Differentiable 𝕜 f ∧ ContDiff 𝕜 ∞ (deriv f)` lets us
peel off differentiability one order at a time without any `n+1`-numeral bookkeeping. -/

noncomputable def rayφ1 (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) : ℝ → ℝ :=
  deriv (rayP p τ δ)

noncomputable def rayφ2 (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) : ℝ → ℝ :=
  deriv (rayφ1 p τ δ)

noncomputable def rayφ3 (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) : ℝ → ℝ :=
  deriv (rayφ2 p τ δ)

theorem rayφ1_contDiff (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    ContDiff ℝ ∞ (rayφ1 p τ δ) :=
  (contDiff_infty_iff_deriv.mp (rayP_contDiff p τ δ)).2

theorem rayφ2_contDiff (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    ContDiff ℝ ∞ (rayφ2 p τ δ) :=
  (contDiff_infty_iff_deriv.mp (rayφ1_contDiff p τ δ)).2

/-- The `HasDerivAt` chain `rayP ⤳ rayφ1 ⤳ rayφ2 ⤳ rayφ3`, for every direction and every point of
the ray — exactly the `h1, h2, h3` hypotheses of `local_nonneg_of_hessian_box`. -/
theorem rayP_hasDerivAt (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) (x : ℝ) :
    HasDerivAt (rayP p τ δ) (rayφ1 p τ δ x) x :=
  (contDiff_infty_iff_deriv.mp (rayP_contDiff p τ δ)).1.differentiableAt.hasDerivAt

theorem rayφ1_hasDerivAt (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) (x : ℝ) :
    HasDerivAt (rayφ1 p τ δ) (rayφ2 p τ δ x) x :=
  (contDiff_infty_iff_deriv.mp (rayφ1_contDiff p τ δ)).1.differentiableAt.hasDerivAt

theorem rayφ2_hasDerivAt (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) (x : ℝ) :
    HasDerivAt (rayφ2 p τ δ) (rayφ3 p τ δ x) x :=
  (contDiff_infty_iff_deriv.mp (rayφ2_contDiff p τ δ)).1.differentiableAt.hasDerivAt

/-! ## Step 1c: vanishing to second order in every direction

`rayP p τ δ 0 = triP p τ.1 τ.2.1 τ.2.2` is immediate.  The gradient identity
`rayφ1 p τ δ 0 = Σ_i δ_i · deriv (triD p m i) 0` needs the multivariable chain rule
(`HasFDerivAt.comp_hasDerivAt`): identify the Fréchet derivative of `triPF p` at `τ` on each
standard basis vector with `deriv (triD p m i) 0` (since `triD p m i` *is* the ray in direction
`e_i`), then use linearity of the Fréchet derivative to extend to a general direction `δ`. -/

theorem rayP_zero (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    rayP p τ δ 0 = triP p τ.1 τ.2.1 τ.2.2 := by
  unfold rayP; norm_num

/-- The curve `t ↦ τ + t • (δ 0, δ 1, δ 2)`, componentwise. -/
theorem hasDerivAt_ray_curve (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => (τ.1 + t * δ 0, τ.2.1 + t * δ 1, τ.2.2 + t * δ 2))
      (δ 0, δ 1, δ 2) t₀ := by
  have h0 : HasDerivAt (fun t : ℝ => τ.1 + t * δ 0) (δ 0) t₀ :=
    (((hasDerivAt_id' t₀).mul_const (δ 0)).const_add τ.1).congr_deriv (by ring)
  have h1 : HasDerivAt (fun t : ℝ => τ.2.1 + t * δ 1) (δ 1) t₀ :=
    (((hasDerivAt_id' t₀).mul_const (δ 1)).const_add τ.2.1).congr_deriv (by ring)
  have h2 : HasDerivAt (fun t : ℝ => τ.2.2 + t * δ 2) (δ 2) t₀ :=
    (((hasDerivAt_id' t₀).mul_const (δ 2)).const_add τ.2.2).congr_deriv (by ring)
  exact h0.prodMk (h1.prodMk h2)

/-- `rayP` is `triPF` composed with the ray curve. -/
theorem rayP_eq_comp (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    rayP p τ δ = triPF p ∘ (fun t : ℝ => (τ.1 + t * δ 0, τ.2.1 + t * δ 1, τ.2.2 + t * δ 2)) := by
  funext t; unfold rayP triPF; simp

/-- The ray derivative at `0` is the Fréchet derivative of `triPF p` at `τ`, applied to `δ`. -/
theorem rayφ1_zero_eq_fderiv (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    rayφ1 p τ δ 0 = fderiv ℝ (triPF p) τ (δ 0, δ 1, δ 2) := by
  have hfd : HasFDerivAt (triPF p) (fderiv ℝ (triPF p) τ) τ :=
    ((triPF_contDiff p).differentiable (by simp)).differentiableAt (x := τ) |>.hasFDerivAt
  have hcurve := hasDerivAt_ray_curve τ δ 0
  have hcomp : HasDerivAt (triPF p ∘ (fun t : ℝ =>
      (τ.1 + t * δ 0, τ.2.1 + t * δ 1, τ.2.2 + t * δ 2)))
      (fderiv ℝ (triPF p) τ (δ 0, δ 1, δ 2)) 0 := by
    have heq : τ = (fun t : ℝ => (τ.1 + t * δ 0, τ.2.1 + t * δ 1, τ.2.2 + t * δ 2)) 0 := by simp
    nth_rewrite 2 [heq] at hfd
    exact HasFDerivAt.comp_hasDerivAt (hl := hfd) (hf := hcurve)
  unfold rayφ1
  rw [rayP_eq_comp p τ δ]
  exact hcomp.deriv

/-- Along the direction `e_0 = (1,0,0)` (the standard basis vector `![1,0,0] : Fin 3 → ℝ`), the ray
function is exactly `triD p m 0`: both move only the first coordinate, from `touchType m`. -/
theorem rayP_e0_eq_triD (p : Fin 24 → ℝ) (m : Fin 5) :
    rayP p (touchType m) ![1, 0, 0] = triD p m 0 := by
  funext d; unfold rayP triD; simp

theorem rayP_e1_eq_triD (p : Fin 24 → ℝ) (m : Fin 5) :
    rayP p (touchType m) ![0, 1, 0] = triD p m 1 := by
  funext d; unfold rayP triD; simp

theorem rayP_e2_eq_triD (p : Fin 24 → ℝ) (m : Fin 5) :
    rayP p (touchType m) ![0, 0, 1] = triD p m 2 := by
  funext d; unfold rayP triD; simp

/-- The gradient identity: the ray derivative at `0` in direction `δ` is the linear combination,
by `δ`, of the coordinate derivatives (i.e. of `triD`'s derivatives). -/
theorem rayφ1_zero_eq (p : Fin 24 → ℝ) (m : Fin 5) (δ : Fin 3 → ℝ) :
    rayφ1 p (touchType m) δ 0 =
      δ 0 * deriv (triD p m 0) 0 + δ 1 * deriv (triD p m 1) 0 + δ 2 * deriv (triD p m 2) 0 := by
  set τ := touchType m
  have hb0 := rayφ1_zero_eq_fderiv p τ ![1, 0, 0]
  have hb1 := rayφ1_zero_eq_fderiv p τ ![0, 1, 0]
  have hb2 := rayφ1_zero_eq_fderiv p τ ![0, 0, 1]
  unfold rayφ1 at hb0 hb1 hb2
  rw [rayP_e0_eq_triD] at hb0
  rw [rayP_e1_eq_triD] at hb1
  rw [rayP_e2_eq_triD] at hb2
  simp at hb0 hb1 hb2
  rw [rayφ1_zero_eq_fderiv p τ δ]
  have hlin : (δ 0, δ 1, δ 2) = δ 0 • ((1:ℝ), (0:ℝ), (0:ℝ)) + δ 1 • ((0:ℝ), (1:ℝ), (0:ℝ))
      + δ 2 • ((0:ℝ), (0:ℝ), (1:ℝ)) := by
    simp
  rw [hlin, map_add, map_add]
  simp only [map_smul, smul_eq_mul]
  rw [hb0, hb1, hb2]

end Thomson.ThreePoint.Cert
