import Thomson.Pair.Taylor

/-! # Task 5a — the reusable Taylor-to-second-order lemma

This file is a **new, additive** file for Task 5a (`triP_local` in `Thomson/ThreePoint/Tasks.lean`).
It does not import or modify `Thomson/ThreePoint/Tasks.lean`, `Linear.lean`, `Perturb.lean` or
`Sharp.lean` — see the module docstring of each section below for exactly what is (and is not) done
here, and the final report for how to wire this into the `triP_local` sorry once the companion
numeric certificates (Hessian positivity + third-derivative bounds at the five touching types,
`pivotsNum`-relative) exist.

## What this file proves

`plans/T5a-TriLocal.md` §6 ("Step 4 — assembly") isolates a purely calculus statement, independent
of everything specific to `triP`: given a scalar function `φ` along a ray from a double zero, a
quadratic lower bound on `φ''(0)` (the Hessian margin `lam`) and a cubic bound on `φ'''` on `[0,1]`
(the remainder, `K`), if `K ≤ 3·lam` then `φ(1) ≥ 0`.  This is exactly the "reusable general lemma"
the task plan calls out as the single biggest complexity reduction available (§0/§4 of
`plans/T5a-TriLocal.md`): prove it once, in general, then instantiate it five times (once per
touching type `m : Fin 5`) by supplying, for each `m`:

* the `HasDerivAt` chain `φ, φ', φ'', φ'''` along the ray `t ↦ touchType m + t • δ` for
  `triP pivots` (from `triP`'s explicit polynomial formula, e.g. by `fun_prop`/`HasDerivAt.comp`
  chains mirroring `triD`'s existing differentiability proof in `Linear.lean`);
* `φ δ 0 = 0` and `φ1 δ 0 = 0` for every direction `δ`, which is exactly `triP_tight m` (vanishing
  to second order — proved in `Tasks.lean` conditional on the Task 1c rows);
* a rational Hessian-margin certificate `lam m` (positive-definiteness of the Hessian of
  `triP pivotsNum` at `touchType m`, with a safety margin absorbing the `pivots`-vs-`pivotsNum`
  perturbation `pivotEps` and interval-rounding error — a `decide +kernel`/`norm_num` computation
  on rational data, generated offline);
* a rational third-derivative bound `K m` on the cube `touchType m ± rhoLocal` (again a
  `decide +kernel` computation on rational/interval data).

The last two bullets are numeric certificates that need to be *generated* (Python, mirroring
`threepoint/tri_local.py` in the task plan) and *checked* (a `Thomson.Tri5b.Itv`-based interval
evaluator for `triP`'s Hessian and third partials over the five touching-type cubes). That
generation + checking infrastructure is the bulk of the remaining work for Task 5a and is **not**
attempted in this pass (it needs the `E`-expression-language infrastructure "T0" that
`plans/README.md` notes does not exist yet, or an equivalent bespoke development for `triP`
specifically); see the final report for exactly what is left. -/

namespace Thomson.ThreePoint.Cert

open Set

/-! ## Step 1: a third-order (cubic) one-sided Taylor lower bound

One derivative deeper than `Thomson.Pair.taylor2_right`, which already gives us (as its two
conclusions) a first-order bound on `f1` and a second-order bound on `f` from a bound on `f2` on
`[a, b]`.  Applying it to the triple `(f1, f2, f3)` gives the first two conjuncts below for free;
the third is one more monotonicity argument, exactly mirroring the proof of the second conjunct of
`taylor2_right` itself. -/

/-- **Third-order lower bound, to the right.** From a lower bound `l ≤ f3` on `[a, b]`, get
matching lower bounds on `f2`, `f1` (as in `taylor2_right`) and now also a cubic lower bound on
`f` itself. -/
theorem taylor3_right {f f1 f2 f3 : ℝ → ℝ} (h1 : ∀ x, HasDerivAt f (f1 x) x)
    (h2 : ∀ x, HasDerivAt f1 (f2 x) x) (h3 : ∀ x, HasDerivAt f2 (f3 x) x) {a b l : ℝ}
    (hl : ∀ x ∈ Icc a b, l ≤ f3 x) :
    ∀ x ∈ Icc a b,
      f2 a + l * (x - a) ≤ f2 x ∧
      f1 a + f2 a * (x - a) + l * (x - a) ^ 2 / 2 ≤ f1 x ∧
      f a + f1 a * (x - a) + f2 a * (x - a) ^ 2 / 2 + l * (x - a) ^ 3 / 6 ≤ f x := by
  -- The first two conjuncts are `taylor2_right` applied one level up, to `(f1, f2, f3)`.
  have base := Thomson.Pair.taylor2_right h2 h3 hl
  -- One further monotonicity argument for the third conjunct, exactly as in `taylor2_right`'s
  -- own proof of its second conjunct from its first.
  have hg1 : ∀ x, HasDerivAt
      (fun y => f y - f1 a * y - f2 a * (y - a) ^ 2 / 2 - l * (y - a) ^ 3 / 6)
      (f1 x - f1 a - f2 a * (x - a) - l * (x - a) ^ 2 / 2) x := fun x => by
    have hq : HasDerivAt (fun y => (y - a) ^ 2) (2 * (x - a)) x :=
      (((hasDerivAt_id' x).sub_const a).fun_pow 2).congr_deriv (by norm_num)
    have hc : HasDerivAt (fun y => (y - a) ^ 3) (3 * (x - a) ^ 2) x :=
      (((hasDerivAt_id' x).sub_const a).fun_pow 3).congr_deriv (by norm_num)
    exact ((((h1 x).fun_sub ((hasDerivAt_id' x).const_mul (f1 a))).fun_sub
      ((hq.const_mul (f2 a)).div_const 2)).fun_sub ((hc.const_mul l).div_const 6)).congr_deriv
      (by ring)
  have hg : MonotoneOn
      (fun y => f y - f1 a * y - f2 a * (y - a) ^ 2 / 2 - l * (y - a) ^ 3 / 6) (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun x _ => (hg1 x).continuousAt.continuousWithinAt)
      (fun x _ => (hg1 x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hg1 x).deriv]
    have hx' : x ∈ Icc a b := ⟨hx.1.le, hx.2.le⟩
    linarith [(base x hx').2]
  intro x hx
  refine ⟨(base x hx).1, (base x hx).2, ?_⟩
  have hmono := hg ⟨le_rfl, hx.1.trans hx.2⟩ hx hx.1
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_div, sub_zero] at hmono
  nlinarith [hmono]

/-- **Third-order lower bound, to the left.**  Note the hypothesis is an *upper* bound `f3 ≤ l`
(not a lower bound as in `taylor3_right`): the cubic remainder `(x - a) ^ 3` is `≤ 0` here, so
lower-bounding it needs an upper bound on the multiplier — this sign flip is inherent to
odd-order Taylor remainders, not an inconsistency with `taylor3_right`. -/
theorem taylor3_left {f f1 f2 f3 : ℝ → ℝ} (h1 : ∀ x, HasDerivAt f (f1 x) x)
    (h2 : ∀ x, HasDerivAt f1 (f2 x) x) (h3 : ∀ x, HasDerivAt f2 (f3 x) x) {a b l : ℝ}
    (hu : ∀ x ∈ Icc b a, f3 x ≤ l) :
    ∀ x ∈ Icc b a,
      f a + f1 a * (x - a) + f2 a * (x - a) ^ 2 / 2 + l * (x - a) ^ 3 / 6 ≤ f x := by
  have g1 : ∀ y, HasDerivAt (fun y => f (-y)) (-f1 (-y)) y := fun y =>
    ((h1 (-y)).comp y (hasDerivAt_neg y)).congr_deriv (by ring)
  have g2 : ∀ y, HasDerivAt (fun y => -f1 (-y)) (f2 (-y)) y := fun y =>
    (((h2 (-y)).comp y (hasDerivAt_neg y)).fun_neg).congr_deriv (by ring)
  have g3 : ∀ y, HasDerivAt (fun y => f2 (-y)) (-f3 (-y)) y := fun y =>
    ((h3 (-y)).comp y (hasDerivAt_neg y)).congr_deriv (by ring)
  intro x hx
  have := (taylor3_right g1 g2 g3 (a := -a) (b := -b) (l := -l)
    (fun y hy => by
      have := hu (-y) ⟨by linarith [hy.2], by linarith [hy.1]⟩
      linarith) (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩).2.2
  simp only [neg_neg] at this
  nlinarith [this]

/-- **The centred cubic form.**  A bound `|f3| ≤ K` on `[c − h, c + h]`, together with
`f c = 0` and `f1 c = 0` (vanishing to second order), bounds `f` below there by its second-order
Taylor term minus the cubic remainder. -/
theorem centred3_lower {f f1 f2 f3 : ℝ → ℝ} (h1 : ∀ x, HasDerivAt f (f1 x) x)
    (h2 : ∀ x, HasDerivAt f1 (f2 x) x) (h3 : ∀ x, HasDerivAt f2 (f3 x) x) {c h K : ℝ} (hh : 0 ≤ h)
    (hzero : f c = 0) (hgrad : f1 c = 0) (hK : ∀ x ∈ Icc (c - h) (c + h), |f3 x| ≤ K) :
    ∀ x ∈ Icc (c - h) (c + h), f2 c * (x - c) ^ 2 / 2 - K * h ^ 3 / 6 ≤ f x := by
  intro x hx
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK c ⟨by linarith, by linarith⟩)
  have hlo : ∀ y ∈ Icc (c - h) (c + h), -K ≤ f3 y := fun y hy => by
    have := hK y hy; rw [abs_le] at this; exact this.1
  have hhi : ∀ y ∈ Icc (c - h) (c + h), f3 y ≤ K := fun y hy => by
    have := hK y hy; rw [abs_le] at this; exact this.2
  rcases le_total c x with hcx | hcx
  · -- right branch: `0 ≤ x - c ≤ h`, so `(x-c)^3 ≤ h^3`, and the lower bound `-K ≤ f3` applies.
    have key := (taylor3_right h1 h2 h3 (b := c + h)
      (fun y hy => hlo y ⟨by linarith [hy.1], hy.2⟩) x ⟨hcx, hx.2⟩).2.2
    rw [hzero, hgrad] at key
    have hcube : (x - c) ^ 3 ≤ h ^ 3 :=
      pow_le_pow_left₀ (by linarith) (by linarith [hx.2]) 3
    nlinarith [key, hcube, hK0]
  · -- left branch: `-h ≤ x - c ≤ 0`, so `-h^3 ≤ (x-c)^3`, and the upper bound `f3 ≤ K` applies
    -- (`taylor3_left`'s hypothesis direction — see its docstring).
    have key := taylor3_left h1 h2 h3 (b := c - h)
      (fun y hy => hhi y ⟨hy.1, by linarith [hy.2]⟩) x ⟨hx.1, hcx⟩
    rw [hzero, hgrad] at key
    have hcube : -(h ^ 3) ≤ (x - c) ^ 3 := by
      have : (c - x) ^ 3 ≤ h ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith [hx.1]) 3
      nlinarith [this]
    nlinarith [key, hcube, hK0]

/-! ## Step 2: the 3-variable assembly lemma (`local_nonneg_of_hessian`)

This packages `taylor3_right`'s cubic bound exactly as `plans/T5a-TriLocal.md` §6 describes:
`φ 1 ≥ φ''(0)/2 − K/6 ≥ (lam/2 − K/6)·‖δ‖² ≥ 0` once `K ≤ 3·lam`.  It is stated with `φ, φ1, φ2, φ3`
as *given* functions of the direction `δ : Fin 3 → ℝ` and the ray parameter `t`, rather than derived
from a fixed trivariate `f` — this is deliberate: it keeps the lemma fully general (no assumption on
how `f`'s partials are represented), matching the task plan's Step 1/Step 3, where `φ, φ', φ'', φ'''`
come from `triD`/`triP_tight`-style `HasDerivAt` chains together with an interval-arithmetic Hessian
and third-derivative certificate.  Instantiating this lemma for `triP pivots` at each `touchType m`
is exactly the remaining work of Task 5a (see the file docstring). -/

/-- **Taylor-to-second-order nonnegativity, from a double zero, in three variables.**

`φ δ` is the scalar restriction of the target function to the ray `t ↦ τ + t • δ` from a point `τ`
where the function and *every* directional derivative vanish (`hzero`, `hgrad`); `hhess` is a
Hessian margin `lam` (a quadratic lower bound on `φ2 δ 0 = δᵀ H δ`, the second directional
derivative at the vanishing point); `hrem` is a bound on the third directional derivative,
uniform in `t ∈ [0,1]`, of the form `K·‖δ‖²` (this is where the cube-radius `ρ` and the raw
third-partial bound `K_m` of the task plan get folded together by the caller:
`K := K_m · ρ`). Given the margin `K ≤ 3·lam`, `φ δ 1` — the target function at `τ + δ` — is
nonnegative for *every* direction `δ`, in particular for every `δ` inside whatever cube the
caller's `hrem` was established on. -/
theorem local_nonneg_of_hessian {φ φ1 φ2 φ3 : (Fin 3 → ℝ) → ℝ → ℝ} {lam K : ℝ}
    (h1 : ∀ δ x, HasDerivAt (φ δ) (φ1 δ x) x)
    (h2 : ∀ δ x, HasDerivAt (φ1 δ) (φ2 δ x) x)
    (h3 : ∀ δ x, HasDerivAt (φ2 δ) (φ3 δ x) x)
    (hzero : ∀ δ, φ δ 0 = 0)
    (hgrad : ∀ δ, φ1 δ 0 = 0)
    (hhess : ∀ δ : Fin 3 → ℝ, lam * (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) ≤ φ2 δ 0)
    (hrem : ∀ δ : Fin 3 → ℝ, ∀ x ∈ Icc (0 : ℝ) 1,
      |φ3 δ x| ≤ K * (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2))
    (hmargin : K ≤ 3 * lam) (δ : Fin 3 → ℝ) :
    0 ≤ φ δ 1 := by
  set S : ℝ := δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2 with hS
  have hSnn : 0 ≤ S := by positivity
  have hl : ∀ x ∈ Icc (0 : ℝ) 1, -(K * S) ≤ φ3 δ x := fun x hx => by
    have := hrem δ x hx
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
