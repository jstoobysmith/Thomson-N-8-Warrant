import Thomson.ThreePoint.Cert.TriLocal

/-! # Task 5a, redesign: a fourth-order one-sided Taylor lower bound

`TriLocalBox.lean`'s cube-wide cubic bound (`local_nonneg_of_hessian_box`) turns out to be too
crude at the fixed radius `rhoLocal = 1/500`: absorbing the *entire* cubic term into a crude
`|φ3| ≤ K‖δ‖²` bound throws away too much (the margin only survives to about a quarter of
`rhoLocal`, independently confirmed by two sessions). The fix keeps the cubic term *exact* (signed,
not absorbed into an absolute bound) and only bounds the *fourth* derivative crudely — one order
deeper than `TriLocal.lean`'s `taylor3_right`/`taylor3_left`, by exactly the same method (one more
monotonicity argument on top of the previous one). This file does not touch `TriLocal.lean`. -/

namespace Thomson.ThreePoint.Cert

open Set

/-- **Fourth-order lower bound, to the right.**  From a lower bound `l ≤ f4` on `[a, b]`, get
matching lower bounds on `f3, f2, f1` (as in `taylor3_right`) and now also a quartic lower bound on
`f` itself, with the cubic term `f3 a · (x-a)³/6` kept *exact* (not absorbed into `l`). -/
theorem taylor4_right {f f1 f2 f3 f4 : ℝ → ℝ} (h1 : ∀ x, HasDerivAt f (f1 x) x)
    (h2 : ∀ x, HasDerivAt f1 (f2 x) x) (h3 : ∀ x, HasDerivAt f2 (f3 x) x)
    (h4 : ∀ x, HasDerivAt f3 (f4 x) x) {a b l : ℝ} (hl : ∀ x ∈ Icc a b, l ≤ f4 x) :
    ∀ x ∈ Icc a b,
      f3 a + l * (x - a) ≤ f3 x ∧
      f2 a + f3 a * (x - a) + l * (x - a) ^ 2 / 2 ≤ f2 x ∧
      f1 a + f2 a * (x - a) + f3 a * (x - a) ^ 2 / 2 + l * (x - a) ^ 3 / 6 ≤ f1 x ∧
      f a + f1 a * (x - a) + f2 a * (x - a) ^ 2 / 2 + f3 a * (x - a) ^ 3 / 6
        + l * (x - a) ^ 4 / 24 ≤ f x := by
  have base := taylor3_right h2 h3 h4 hl
  have hg1 : ∀ x, HasDerivAt
      (fun y => f y - f1 a * y - f2 a * (y - a) ^ 2 / 2 - f3 a * (y - a) ^ 3 / 6
        - l * (y - a) ^ 4 / 24)
      (f1 x - f1 a - f2 a * (x - a) - f3 a * (x - a) ^ 2 / 2 - l * (x - a) ^ 3 / 6) x := fun x => by
    have hq : HasDerivAt (fun y => (y - a) ^ 2) (2 * (x - a)) x :=
      (((hasDerivAt_id' x).sub_const a).fun_pow 2).congr_deriv (by norm_num)
    have hc : HasDerivAt (fun y => (y - a) ^ 3) (3 * (x - a) ^ 2) x :=
      (((hasDerivAt_id' x).sub_const a).fun_pow 3).congr_deriv (by norm_num)
    have hd : HasDerivAt (fun y => (y - a) ^ 4) (4 * (x - a) ^ 3) x :=
      (((hasDerivAt_id' x).sub_const a).fun_pow 4).congr_deriv (by norm_num)
    exact (((((h1 x).fun_sub ((hasDerivAt_id' x).const_mul (f1 a))).fun_sub
      ((hq.const_mul (f2 a)).div_const 2)).fun_sub ((hc.const_mul (f3 a)).div_const 6)).fun_sub
      ((hd.const_mul l).div_const 24)).congr_deriv (by ring)
  have hg : MonotoneOn
      (fun y => f y - f1 a * y - f2 a * (y - a) ^ 2 / 2 - f3 a * (y - a) ^ 3 / 6
        - l * (y - a) ^ 4 / 24) (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun x _ => (hg1 x).continuousAt.continuousWithinAt)
      (fun x _ => (hg1 x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hg1 x).deriv]
    have hx' : x ∈ Icc a b := ⟨hx.1.le, hx.2.le⟩
    linarith [(base x hx').2.2]
  intro x hx
  refine ⟨(base x hx).1, (base x hx).2.1, (base x hx).2.2, ?_⟩
  have hmono := hg ⟨le_rfl, hx.1.trans hx.2⟩ hx hx.1
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_div, sub_zero] at hmono
  nlinarith [hmono]

/-- **Fourth-order lower bound, to the left.**  Unlike `taylor3_left`, the hypothesis is again a
*lower* bound `l ≤ f4` (even-order remainder: `(x-a)^4 ≥ 0` on both sides, so no sign flip — as in
`taylor2_left` vs. `taylor2_right`). -/
theorem taylor4_left {f f1 f2 f3 f4 : ℝ → ℝ} (h1 : ∀ x, HasDerivAt f (f1 x) x)
    (h2 : ∀ x, HasDerivAt f1 (f2 x) x) (h3 : ∀ x, HasDerivAt f2 (f3 x) x)
    (h4 : ∀ x, HasDerivAt f3 (f4 x) x) {a b l : ℝ} (hl : ∀ x ∈ Icc b a, l ≤ f4 x) :
    ∀ x ∈ Icc b a,
      f a + f1 a * (x - a) + f2 a * (x - a) ^ 2 / 2 + f3 a * (x - a) ^ 3 / 6
        + l * (x - a) ^ 4 / 24 ≤ f x := by
  have g1 : ∀ y, HasDerivAt (fun y => f (-y)) (-f1 (-y)) y := fun y =>
    ((h1 (-y)).comp y (hasDerivAt_neg y)).congr_deriv (by ring)
  have g2 : ∀ y, HasDerivAt (fun y => -f1 (-y)) (f2 (-y)) y := fun y =>
    (((h2 (-y)).comp y (hasDerivAt_neg y)).fun_neg).congr_deriv (by ring)
  have g3 : ∀ y, HasDerivAt (fun y => f2 (-y)) (-f3 (-y)) y := fun y =>
    ((h3 (-y)).comp y (hasDerivAt_neg y)).congr_deriv (by ring)
  have g4 : ∀ y, HasDerivAt (fun y => -f3 (-y)) (f4 (-y)) y := fun y =>
    (((h4 (-y)).comp y (hasDerivAt_neg y)).fun_neg).congr_deriv (by ring)
  intro x hx
  have := (taylor4_right g1 g2 g3 g4 (a := -a) (b := -b) (l := l)
    (fun y hy => by
      have := hl (-y) ⟨by linarith [hy.2], by linarith [hy.1]⟩
      linarith) (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩).2.2.2
  simp only [neg_neg] at this
  nlinarith [this]

end Thomson.ThreePoint.Cert
