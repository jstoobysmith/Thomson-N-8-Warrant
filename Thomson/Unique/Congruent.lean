import Mathlib

/-! # Equal Gram matrices ⟹ congruent (U6, generic part)

Two finite families of vectors in a finite-dimensional real inner product space with the same
Gram matrix differ by a linear isometry of the whole space.  (`UniquenessPlan.md`, step U6.)

*Proof.*  With `T c = Σ cᵢ zᵢ` and `S c = Σ cᵢ yᵢ`, `‖T c‖ = ‖S c‖` (expand both squares), so
`ker T ≤ ker S` and `S` descends to `range T` as a norm-preserving linear map.  Extend it to the
whole space (`LinearIsometry.extend`) and upgrade to an equivalence (same finite dimension). -/

namespace Thomson.Unique

open Module
open scoped RealInnerProductSpace InnerProductSpace

section Generic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Norm of a linear combination in terms of the Gram matrix. -/
theorem norm_sq_linearCombination {n : ℕ} (z : Fin n → V) (c : Fin n → ℝ) :
    ‖Fintype.linearCombination ℝ z c‖ ^ 2 = ∑ i, ∑ j, c i * c j * ⟪z i, z j⟫ := by
  rw [← real_inner_self_eq_norm_sq, Fintype.linearCombination_apply, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right]; ring

theorem norm_linearCombination_eq {n : ℕ} (y z : Fin n → V)
    (h : ∀ i j, ⟪y i, y j⟫ = ⟪z i, z j⟫) (c : Fin n → ℝ) :
    ‖Fintype.linearCombination ℝ y c‖ = ‖Fintype.linearCombination ℝ z c‖ := by
  have h2 : ‖Fintype.linearCombination ℝ y c‖ ^ 2 = ‖Fintype.linearCombination ℝ z c‖ ^ 2 := by
    simp only [norm_sq_linearCombination, h]
  have := congrArg Real.sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

/-- **Equal Gram matrices ⟹ congruent**, in any finite-dimensional real inner product space. -/
theorem congruent_of_gram_eq' [FiniteDimensional ℝ V] {n : ℕ} (y z : Fin n → V)
    (h : ∀ i j, ⟪y i, y j⟫ = ⟪z i, z j⟫) :
    ∃ f : V ≃ₗᵢ[ℝ] V, ∀ i, y i = f (z i) := by
  classical
  set T := Fintype.linearCombination ℝ z with hT
  set S := Fintype.linearCombination ℝ y with hS
  have hnorm : ∀ c, ‖S c‖ = ‖T c‖ := norm_linearCombination_eq y z h
  have hker : LinearMap.ker T ≤ LinearMap.ker S := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    rw [← norm_eq_zero, hnorm, hc, norm_zero]
  let L0 : LinearMap.range T →ₗ[ℝ] V :=
    ((LinearMap.ker T).liftQ S hker).comp T.quotKerEquivRange.symm.toLinearMap
  have hL0 : ∀ c, L0 ⟨T c, LinearMap.mem_range_self T c⟩ = S c := by
    intro c
    simp [L0]
  let L : LinearMap.range T →ₗᵢ[ℝ] V :=
    { toLinearMap := L0
      norm_map' := by
        rintro ⟨v, c, rfl⟩
        change ‖L0 ⟨T c, _⟩‖ = ‖T c‖
        rw [hL0, hnorm] }
  refine ⟨L.extend.toLinearIsometryEquiv rfl, fun i => ?_⟩
  have hz : z i = T (Pi.single i 1) := by simp [hT]
  have hy : y i = S (Pi.single i 1) := by simp [hS]
  rw [LinearIsometry.coe_toLinearIsometryEquiv]
  have := L.extend_apply ⟨T (Pi.single i 1), LinearMap.mem_range_self T _⟩
  simp only at this
  rw [hz, this, hy]
  exact (hL0 _).symm

end Generic

/-- **Equal Gram matrices ⟹ congruent** (in `ℝ³`). -/
theorem congruent_of_gram_eq {n : ℕ} (y z : Fin n → EuclideanSpace ℝ (Fin 3))
    (h : ∀ i j, ⟪y i, y j⟫_ℝ = ⟪z i, z j⟫_ℝ) :
    ∃ f : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3), ∀ i, y i = f (z i) :=
  congruent_of_gram_eq' y z h

end Thomson.Unique
