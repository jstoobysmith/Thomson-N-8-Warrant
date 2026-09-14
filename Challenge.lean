import Thomson.Antiprism.Family

/-!
# The `N = 8` Thomson problem — the challenge statements

The statements checked by the [comparator](https://github.com/leanprover/comparator)
(`scripts/comparator/`): they import only the *definitions* — `energy`, `Admissible`,
`thomsonInf` (`Thomson/Basic/Energy.lean`), the antiprism family, its energy and the optimal
parameter `uStar` (`Thomson/Antiprism/Family.lean`) — and nothing of the proof.  `Solution.lean`
proves exactly these statements.
-/

open Thomson

/-- The minimal Coulomb energy of eight unit charges on the sphere is the energy of the square
antiprism at the optimal twist `u*`. -/
theorem thomson_eight : thomsonInf 8 = antiprismEnergy uStar := sorry

/-- The lower bound alone. -/
theorem thomson_eight_lower : antiprismEnergy uStar ≤ thomsonInf 8 := sorry

/-- Every admissible configuration of minimal energy is a rotated, relabelled copy of the optimal
square antiprism. -/
theorem thomson_eight_unique (x : Fin 8 → EuclideanSpace ℝ (Fin 3)) (hx : Admissible x)
    (hE : energy x = thomsonInf 8) :
    ∃ (f : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (σ : Equiv.Perm (Fin 8)),
      ∀ i, x i = f (antiprism (Real.sqrt uStar) (σ i)) := sorry

/-- The minimisers, characterised. -/
theorem thomson_eight_minimiser_iff (x : Fin 8 → EuclideanSpace ℝ (Fin 3)) :
    (Admissible x ∧ energy x = thomsonInf 8) ↔
    ∃ (f : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (σ : Equiv.Perm (Fin 8)),
      ∀ i, x i = f (antiprism (Real.sqrt uStar) (σ i)) := sorry
