import Thomson.Complete

/-!
# The `N = 8` Thomson problem — the solution

The statements of `Challenge.lean`, proved (`Thomson/Complete.lean`).  Checked by the comparator:
same statements, kernel-accepted, axioms `propext`, `Quot.sound`, `Classical.choice` only.
-/

open Thomson

theorem thomson_eight : thomsonInf 8 = antiprismEnergy uStar := Thomson.thomson_eight

theorem thomson_eight_lower : antiprismEnergy uStar ≤ thomsonInf 8 := Thomson.thomson_eight_lower

theorem thomson_eight_unique (x : Fin 8 → EuclideanSpace ℝ (Fin 3)) (hx : Admissible x)
    (hE : energy x = thomsonInf 8) :
    ∃ (f : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (σ : Equiv.Perm (Fin 8)),
      ∀ i, x i = f (antiprism (Real.sqrt uStar) (σ i)) :=
  Thomson.thomson_eight_unique x hx hE

theorem thomson_eight_minimiser_iff (x : Fin 8 → EuclideanSpace ℝ (Fin 3)) :
    (Admissible x ∧ energy x = thomsonInf 8) ↔
    ∃ (f : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (σ : Equiv.Perm (Fin 8)),
      ∀ i, x i = f (antiprism (Real.sqrt uStar) (σ i)) :=
  Thomson.thomson_eight_minimiser_iff x
