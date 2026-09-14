import Thomson.Uniqueness.Main
import Thomson.Uniqueness.PairZero

/-! # Uniqueness of the minimiser, from the tasks

`docs/uniqueness.md`, U7: `Thomson.Unique.thomson_eight_unique_of_tasks` with the pair-zero
hypothesis (U3) discharged by `pairP_eq_zero_iff`.  The Tasks proved in the separate
kernel-checked libraries (1a, 1b, 5b and the strict form of 5b) remain hypotheses here, as in `thomson_eight_lower_of_tasks`; they are
discharged in `Thomson/Complete.lean`. -/

namespace Thomson

theorem pairZeroOnlyAtChords (h1a : Task1a) (h1b : Task1b) : Unique.PairZeroOnlyAtChords :=
  fun _ h1 h2 h0 => (pairP_eq_zero_iff h1a h1b h1 h2).mp h0

/-- **Uniqueness of the minimiser**, modulo the separately checked tasks: every admissible
configuration of energy `E(u*)` is an orthogonal image of a relabelling of the optimal square
antiprism. -/
theorem thomson_eight_unique_of_tasks (h1a : Task1a) (h1b : Task1b) (h5b : Task5b)
    (h5s : Unique.Task5bStrict) (x : Fin 8 → EuclideanSpace ℝ (Fin 3)) (hx : Admissible x)
    (hE : energy x = antiprismEnergy uStar) :
    ∃ (f : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (σ : Equiv.Perm (Fin 8)),
      ∀ i, x i = f (antiprism (Real.sqrt uStar) (σ i)) :=
  Unique.thomson_eight_unique_of_tasks h1a h1b h5b h5s (pairZeroOnlyAtChords h1a h1b) x hx hE

/-- The minimisers are exactly the rotated, relabelled optimal antiprisms (modulo the tasks). -/
theorem minimiser_iff_of_tasks (h1a : Task1a) (h1b : Task1b) (h5b : Task5b)
    (h5s : Unique.Task5bStrict) (x : Fin 8 → EuclideanSpace ℝ (Fin 3)) :
    (Admissible x ∧ energy x = antiprismEnergy uStar) ↔
    ∃ (f : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (σ : Equiv.Perm (Fin 8)),
      ∀ i, x i = f (antiprism (Real.sqrt uStar) (σ i)) :=
  Unique.minimiser_iff_of_tasks h1a h1b h5b h5s (pairZeroOnlyAtChords h1a h1b) x

end Thomson
