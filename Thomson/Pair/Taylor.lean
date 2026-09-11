import Mathlib

/-! # Task 4, step 2: second-order lower bounds

The only calculus Task 4 needs: a lower bound `l ≤ f''` on an interval gives the second-order
lower bound `f(a) + f'(a)(x − a) + l(x − a)²/2 ≤ f(x)` there (`taylor2_right`, `taylor2_left`),
from `monotoneOn_of_deriv_nonneg` twice — and its centred form `centred_lower`, which turns a
bound `|f''| ≤ K` on `[c − h, c + h]` into `f(c) − |f'(c)|·h − K·h²/2 ≤ f` there. -/

namespace Thomson.Pair

open Set

/-- **Second-order lower bound, to the right.**  Also the first-order bound on `f'`. -/
theorem taylor2_right {f f1 f2 : ℝ → ℝ} (h1 : ∀ x, HasDerivAt f (f1 x) x)
    (h2 : ∀ x, HasDerivAt f1 (f2 x) x) {a b l : ℝ} (hl : ∀ x ∈ Icc a b, l ≤ f2 x) :
    ∀ x ∈ Icc a b, f1 a + l * (x - a) ≤ f1 x ∧
      f a + f1 a * (x - a) + l * (x - a) ^ 2 / 2 ≤ f x := by
  -- `f1 − l·x` is monotone on `[a, b]`
  have hk1 : ∀ x, HasDerivAt (fun y => f1 y - l * y) (f2 x - l) x := fun x =>
    ((h2 x).fun_sub ((hasDerivAt_id' x).const_mul l)).congr_deriv (by ring)
  have hk : MonotoneOn (fun y => f1 y - l * y) (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun x _ => (hk1 x).continuousAt.continuousWithinAt)
      (fun x _ => (hk1 x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hk1 x).deriv]
    linarith [hl x ⟨hx.1.le, hx.2.le⟩]
  have hder : ∀ x ∈ Icc a b, f1 a + l * (x - a) ≤ f1 x := fun x hx => by
    have := hk ⟨le_rfl, hx.1.trans hx.2⟩ hx hx.1
    simp only at this
    linarith
  -- `f − f1(a)·x − l(x − a)²/2` is monotone on `[a, b]`
  have hg1 : ∀ x, HasDerivAt (fun y => f y - f1 a * y - l * (y - a) ^ 2 / 2)
      (f1 x - f1 a - l * (x - a)) x := fun x => by
    have hq : HasDerivAt (fun y => (y - a) ^ 2) (2 * (x - a)) x :=
      (((hasDerivAt_id' x).sub_const a).fun_pow 2).congr_deriv (by norm_num)
    exact (((h1 x).fun_sub ((hasDerivAt_id' x).const_mul (f1 a))).fun_sub
      ((hq.const_mul l).div_const 2)).congr_deriv (by ring)
  have hg : MonotoneOn (fun y => f y - f1 a * y - l * (y - a) ^ 2 / 2) (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun x _ => (hg1 x).continuousAt.continuousWithinAt)
      (fun x _ => (hg1 x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hg1 x).deriv]
    linarith [hder x ⟨hx.1.le, hx.2.le⟩]
  intro x hx
  refine ⟨hder x hx, ?_⟩
  have := hg ⟨le_rfl, hx.1.trans hx.2⟩ hx hx.1
  simp only [sub_self] at this
  nlinarith [this]

/-- **Second-order lower bound, to the left.** -/
theorem taylor2_left {f f1 f2 : ℝ → ℝ} (h1 : ∀ x, HasDerivAt f (f1 x) x)
    (h2 : ∀ x, HasDerivAt f1 (f2 x) x) {a b l : ℝ} (hl : ∀ x ∈ Icc b a, l ≤ f2 x) :
    ∀ x ∈ Icc b a, f a + f1 a * (x - a) + l * (x - a) ^ 2 / 2 ≤ f x := by
  have g1 : ∀ y, HasDerivAt (fun y => f (-y)) (-f1 (-y)) y := fun y =>
    ((h1 (-y)).comp y (hasDerivAt_neg y)).congr_deriv (by ring)
  have g2 : ∀ y, HasDerivAt (fun y => -f1 (-y)) (f2 (-y)) y := fun y =>
    (((h2 (-y)).comp y (hasDerivAt_neg y)).fun_neg).congr_deriv (by ring)
  intro x hx
  have := (taylor2_right g1 g2 (a := -a) (b := -b) (l := l)
    (fun y hy => hl (-y) ⟨by linarith [hy.2], by linarith [hy.1]⟩) (-x)
    ⟨by linarith [hx.2], by linarith [hx.1]⟩).2
  simp only [neg_neg] at this
  nlinarith [this]

/-- **The centred form.**  A bound `|f''| ≤ K` on `[c − h, c + h]` bounds `f` below there by its
value and slope at the centre. -/
theorem centred_lower {f f1 f2 : ℝ → ℝ} (h1 : ∀ x, HasDerivAt f (f1 x) x)
    (h2 : ∀ x, HasDerivAt f1 (f2 x) x) {c h K : ℝ} (hh : 0 ≤ h)
    (hK : ∀ x ∈ Icc (c - h) (c + h), |f2 x| ≤ K) :
    ∀ x ∈ Icc (c - h) (c + h), f c - |f1 c| * h - K * h ^ 2 / 2 ≤ f x := by
  intro x hx
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK c ⟨by linarith, by linarith⟩)
  have hlo : ∀ y ∈ Icc (c - h) (c + h), -K ≤ f2 y := fun y hy => by
    have := hK y hy; rw [abs_le] at this; exact this.1
  have hxc : |x - c| ≤ h := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsq : (x - c) ^ 2 ≤ h ^ 2 := by
    have := sq_abs (x - c); nlinarith [abs_nonneg (x - c)]
  have hlin : -(|f1 c| * h) ≤ f1 c * (x - c) := by
    have := abs_mul (f1 c) (x - c)
    have h3 : |f1 c * (x - c)| ≤ |f1 c| * h := by
      rw [this]; exact mul_le_mul_of_nonneg_left hxc (abs_nonneg _)
    linarith [neg_abs_le (f1 c * (x - c))]
  have key : f c + f1 c * (x - c) + -K * (x - c) ^ 2 / 2 ≤ f x := by
    rcases le_total c x with hcx | hcx
    · exact (taylor2_right h1 h2 (b := c + h) (fun y hy => hlo y ⟨by linarith [hy.1], hy.2⟩)
        x ⟨hcx, hx.2⟩).2
    · exact taylor2_left h1 h2 (b := c - h) (fun y hy => hlo y ⟨hy.1, by linarith [hy.2]⟩)
        x ⟨hx.1, hcx⟩
  nlinarith [key, hsq, hlin, hK0]

end Thomson.Pair
