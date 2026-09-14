import Thomson.Numerics.TaylorModel

/-! # Task 5b, step 7: coefficient tensors and the Taylor shift

`F(u,v,t) = Fh (Hp pivotsNum) u v t` has degree `≤ 8` in each variable, so it is described by a
`9×9×9` tensor of coefficients.  Two facts make the tensor the right object:

* *tightness*.  Replaying the expression `F` in Taylor-model arithmetic on a box inflates the
  third-order remainder by a factor `10³`–`10⁴`, because the bound on a product is a sum of
  absolute values while the true remainder enjoys massive cancellation.  Shifting the coefficient
  tensor to the centre of the box produces the *exact* Taylor coefficients there, so the remainder
  is the true one.  Empirically this is the difference between `10⁴` and `10⁷` boxes.
* *cost*.  A shift is three passes of a binomial transform, `3·9⁴ ≈ 2·10⁴` operations per box,
  independent of how `F` was built.

This file is the algebra: real coefficient tensors, their evaluation, the shift of one variable,
and the axis permutations that turn it into the other two. -/

namespace Thomson.Tri5b

open Finset

/-- A real coefficient tensor. -/
abbrev RT := Fin 9 → Fin 9 → Fin 9 → ℝ

/-- `ev c u v t = Σ cᵢⱼₖ uⁱ vʲ tᵏ`. -/
noncomputable def ev (c : RT) (u v t : ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, c i j k * (u ^ (i : ℕ) * v ^ (j : ℕ) * t ^ (k : ℕ))

/-! ### The one-dimensional shift -/

theorem sum_fin_le_eq_range {n : ℕ} (g : ℕ → ℝ) {i : ℕ} (hi : i < n) :
    ∑ j : Fin n, (if (j : ℕ) ≤ i then g j else 0) = ∑ j ∈ Finset.range (i + 1), g j := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if j ≤ i then g j else 0) n, ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- The Taylor shift of a one-variable polynomial. -/
theorem shift_sum {n : ℕ} (c : Fin n → ℝ) (a x : ℝ) :
    ∑ i : Fin n, c i * (a + x) ^ (i : ℕ)
      = ∑ j : Fin n, (∑ i : Fin n,
          (if (j : ℕ) ≤ (i : ℕ) then c i * ((i : ℕ).choose (j : ℕ)) * a ^ ((i : ℕ) - (j : ℕ))
            else 0)) * x ^ (j : ℕ) := by
  have step : ∀ i : Fin n, c i * (a + x) ^ (i : ℕ)
      = ∑ j : Fin n, (if (j : ℕ) ≤ (i : ℕ)
          then c i * ((i : ℕ).choose (j : ℕ)) * a ^ ((i : ℕ) - (j : ℕ)) * x ^ (j : ℕ) else 0) := by
    intro i
    rw [sum_fin_le_eq_range
      (fun j => c i * ((i : ℕ).choose j) * a ^ ((i : ℕ) - j) * x ^ j) i.isLt]
    rw [add_comm a x, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    simp only [Finset.mem_range] at hm
    ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => step i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h <;> ring

/-! ### Shifting the first variable of a tensor -/

/-- The first variable shifted by `a`. -/
noncomputable def sh1 (c : RT) (a : ℝ) : RT := fun j y z =>
  ∑ i : Fin 9, (if (j : ℕ) ≤ (i : ℕ)
    then c i y z * ((i : ℕ).choose (j : ℕ)) * a ^ ((i : ℕ) - (j : ℕ)) else 0)

/-- `ev` regrouped as a polynomial in the first variable. -/
theorem ev_eq_outer (c : RT) (u v t : ℝ) :
    ev c u v t = ∑ i : Fin 9, (∑ j, ∑ k, c i j k * (v ^ (j : ℕ) * t ^ (k : ℕ))) * u ^ (i : ℕ) := by
  unfold ev
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem ev_sh1 (c : RT) (a u v t : ℝ) : ev (sh1 c a) u v t = ev c (a + u) v t := by
  rw [ev_eq_outer, ev_eq_outer,
    shift_sum (fun i => ∑ j, ∑ k, c i j k * (v ^ (j : ℕ) * t ^ (k : ℕ))) a u]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  calc ∑ l, ∑ k, (sh1 c a) j l k * (v ^ (l : ℕ) * t ^ (k : ℕ))
      = ∑ l, ∑ k, ∑ i : Fin 9, (if (j : ℕ) ≤ (i : ℕ)
          then c i l k * ((i : ℕ).choose (j : ℕ)) * a ^ ((i : ℕ) - (j : ℕ)) else 0)
            * (v ^ (l : ℕ) * t ^ (k : ℕ)) := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
        rw [sh1, Finset.sum_mul]
    _ = ∑ l, ∑ i : Fin 9, ∑ k, (if (j : ℕ) ≤ (i : ℕ)
          then c i l k * ((i : ℕ).choose (j : ℕ)) * a ^ ((i : ℕ) - (j : ℕ)) else 0)
            * (v ^ (l : ℕ) * t ^ (k : ℕ)) :=
        Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ i : Fin 9, ∑ l, ∑ k, (if (j : ℕ) ≤ (i : ℕ)
          then c i l k * ((i : ℕ).choose (j : ℕ)) * a ^ ((i : ℕ) - (j : ℕ)) else 0)
            * (v ^ (l : ℕ) * t ^ (k : ℕ)) := Finset.sum_comm
    _ = ∑ i : Fin 9, (if (j : ℕ) ≤ (i : ℕ)
          then (∑ l, ∑ k, c i l k * (v ^ (l : ℕ) * t ^ (k : ℕ)))
            * ((i : ℕ).choose (j : ℕ)) * a ^ ((i : ℕ) - (j : ℕ)) else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs with h
        · rw [Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
        · simp

/-! ### The other two axes, by permutation -/

/-- Swap the first two axes. -/
def perm12 (c : RT) : RT := fun i j k => c j i k
/-- Swap the first and third axes. -/
def perm13 (c : RT) : RT := fun i j k => c k j i

theorem ev_perm12 (c : RT) (u v t : ℝ) : ev (perm12 c) u v t = ev c v u t := by
  unfold ev perm12
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => by ring

theorem ev_perm13 (c : RT) (u v t : ℝ) : ev (perm13 c) u v t = ev c t v u := by
  unfold ev perm13
  calc ∑ i, ∑ j, ∑ k, c k j i * (u ^ (i : ℕ) * v ^ (j : ℕ) * t ^ (k : ℕ))
      = ∑ i, ∑ k, ∑ j, c k j i * (u ^ (i : ℕ) * v ^ (j : ℕ) * t ^ (k : ℕ)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, c k j i * (u ^ (i : ℕ) * v ^ (j : ℕ) * t ^ (k : ℕ)) := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, c i j k * (t ^ (i : ℕ) * v ^ (j : ℕ) * u ^ (k : ℕ)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- The second variable shifted by `a`. -/
noncomputable def sh2 (c : RT) (a : ℝ) : RT := perm12 (sh1 (perm12 c) a)
/-- The third variable shifted by `a`. -/
noncomputable def sh3 (c : RT) (a : ℝ) : RT := perm13 (sh1 (perm13 c) a)

theorem ev_sh2 (c : RT) (a u v t : ℝ) : ev (sh2 c a) u v t = ev c u (a + v) t := by
  unfold sh2
  rw [ev_perm12, ev_sh1, ev_perm12]

theorem ev_sh3 (c : RT) (a u v t : ℝ) : ev (sh3 c a) u v t = ev c u v (a + t) := by
  unfold sh3
  rw [ev_perm13, ev_sh1, ev_perm13]

/-- The full Taylor shift. -/
noncomputable def shift (c : RT) (a b d : ℝ) : RT := sh3 (sh2 (sh1 c a) b) d

theorem ev_shift (c : RT) (a b d u v t : ℝ) :
    ev (shift c a b d) u v t = ev c (a + u) (b + v) (d + t) := by
  unfold shift
  rw [ev_sh3, ev_sh2, ev_sh1]

end Thomson.Tri5b
