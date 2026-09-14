import Thomson.Main
import Thomson.Pivots.Discharge
import Thomson.TriangleGlobal.Discharge
import Thomson.Uniqueness.Final

/-! # The main theorem, with every proved Task discharged

The default build (`Thomson.Main`) proves `thomson_eight_lower_of_tasks`, which takes the three
Tasks whose certificates are expensive — 1a, 1b (library `Task1b`) and 5b (library `Tri5b`) — as
hypotheses, so that it does not pay for them.
This file, the library `Complete` (`lake build Complete`; it builds `Tri5b`, about 30 hours of CPU
in `decide +kernel`, a few hours of wall clock on this machine), discharges them.  Nothing is left
open and nothing uses `native_decide`: Task 5a is proved in `Thomson/TriangleLocal/` and Tasks 1a,
1b, 5b in `Thomson/Pivots/`, `Thomson/TriangleGlobal/` with `decide +kernel`, so
`#print axioms Thomson.thomson_eight_lower` lists only `propext, Classical.choice, Quot.sound`.

Uniqueness (`docs/uniqueness.md`, `Thomson/Uniqueness/`) is stated here too: `thomson_eight_unique` and
`thomson_eight_minimiser_iff`. -/

namespace Thomson

/-- **The matching lower bound**: no admissible configuration beats the best antiprism. -/
theorem thomson_eight_lower : antiprismEnergy uStar ≤ thomsonInf 8 :=
  thomson_eight_lower_of_tasks Task1b.task1a Task1b.task1b
    (Tri5b.task5b_of_task5a (triP_local Task1b.task1a Task1b.task1b))

/-- **The square antiprism solves the 8-point Thomson problem.** -/
theorem thomson_eight : thomsonInf 8 = antiprismEnergy uStar :=
  le_antisymm thomsonInf_le_uStar thomson_eight_lower

/-- **Uniqueness**: every admissible configuration of minimal energy is a rotated, relabelled copy
of the optimal square antiprism. -/
theorem thomson_eight_unique (x : Fin 8 → EuclideanSpace ℝ (Fin 3)) (hx : Admissible x)
    (hE : energy x = thomsonInf 8) :
    ∃ (f : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (σ : Equiv.Perm (Fin 8)),
      ∀ i, x i = f (antiprism (Real.sqrt uStar) (σ i)) :=
  thomson_eight_unique_of_tasks Task1b.task1a Task1b.task1b
    (Tri5b.task5b_of_task5a (triP_local Task1b.task1a Task1b.task1b)) Tri5b.task5bStrict
    x hx (hE.trans thomson_eight)

/-- **The minimisers, characterised**: a configuration is admissible with energy `thomsonInf 8`
iff it is a rotated, relabelled optimal square antiprism. -/
theorem thomson_eight_minimiser_iff (x : Fin 8 → EuclideanSpace ℝ (Fin 3)) :
    (Admissible x ∧ energy x = thomsonInf 8) ↔
    ∃ (f : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (σ : Equiv.Perm (Fin 8)),
      ∀ i, x i = f (antiprism (Real.sqrt uStar) (σ i)) := by
  rw [thomson_eight]
  exact minimiser_iff_of_tasks Task1b.task1a Task1b.task1b
    (Tri5b.task5b_of_task5a (triP_local Task1b.task1a Task1b.task1b)) Tri5b.task5bStrict x

end Thomson
