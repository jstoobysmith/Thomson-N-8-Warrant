import Mathlib

/-! # Task 2, step 1: diagonal dominance

A real symmetric matrix with `Σ_b |N_ab| ≤ 2 N_aa` for every row `a` (equivalently `N_aa ≥ 0` and
`N_aa ≥ Σ_{b ≠ a} |N_ab|`) is positive semidefinite: `x_a N_ab x_b ≥ −|N_ab| (x_a² + x_b²)/2`, and the
two halves of the right-hand side are equal by symmetry. -/

namespace Thomson.PSD

open Matrix

theorem mul_mul_ge {N xa xb : ℝ} : -(|N| * (xa ^ 2 + xb ^ 2) / 2) ≤ xa * (N * xb) := by
  rcases le_total 0 N with h | h
  · rw [abs_of_nonneg h]; nlinarith [mul_nonneg h (sq_nonneg (xa + xb))]
  · rw [abs_of_nonpos h]; nlinarith [mul_nonneg (neg_nonneg.mpr h) (sq_nonneg (xa - xb))]

/-- **Diagonally dominant symmetric matrices are positive semidefinite.** -/
theorem posSemidef_of_dom {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) (hsym : Nᵀ = N)
    (hdom : ∀ a, ∑ b, |N a b| ≤ 2 * N a a) : N.PosSemidef := by
  have hNs : ∀ a b, N b a = N a b := fun a b => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hsym a) b
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hsym]
  simp only [star_trivial, dotProduct, mulVec]
  -- the pointwise bound
  have hpt : ∀ a b, (if a = b then 2 * N a a * x a ^ 2 else 0) - |N a b| * (x a ^ 2 + x b ^ 2) / 2
      ≤ x a * (N a b * x b) := by
    intro a b
    split_ifs with hab
    · subst hab
      have := le_abs_self (N a a)
      nlinarith [sq_nonneg (x a)]
    · linarith [mul_mul_ge (N := N a b) (xa := x a) (xb := x b)]
  have hsum : ∑ a, ∑ b, ((if a = b then 2 * N a a * x a ^ 2 else 0) - |N a b| * (x a ^ 2 + x b ^ 2) / 2)
      ≤ ∑ a, x a * ∑ b, N a b * x b := by
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => hpt a b
  -- the two halves of the negative part are equal
  have hswap : ∑ a, ∑ b, |N a b| * x b ^ 2 = ∑ a, ∑ b, |N a b| * x a ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hNs]
  have hexp : ∑ a, ∑ b, ((if a = b then 2 * N a a * x a ^ 2 else 0) - |N a b| * (x a ^ 2 + x b ^ 2) / 2)
      = ∑ a, x a ^ 2 * (2 * N a a - ∑ b, |N a b|) := by
    have e1 : ∀ a, ∑ b, ((if a = b then 2 * N a a * x a ^ 2 else 0) - |N a b| * (x a ^ 2 + x b ^ 2) / 2)
        = 2 * N a a * x a ^ 2 - (∑ b, |N a b| * x a ^ 2) / 2 - (∑ b, |N a b| * x b ^ 2) / 2 := by
      intro a
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true]
      rw [← Finset.sum_div]
      simp only [mul_add, Finset.sum_add_distrib]
      ring
    have hR : ∑ a, x a ^ 2 * (2 * N a a - ∑ b, |N a b|)
        = ∑ a, 2 * N a a * x a ^ 2 - ∑ a, ∑ b, |N a b| * x a ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_sub, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun b _ => by ring
    simp only [e1, Finset.sum_sub_distrib, ← Finset.sum_div, hswap]
    rw [hR]
    ring
  have hnn : 0 ≤ ∑ a, x a ^ 2 * (2 * N a a - ∑ b, |N a b|) :=
    Finset.sum_nonneg fun a _ => mul_nonneg (sq_nonneg _) (by linarith [hdom a])
  linarith

end Thomson.PSD
