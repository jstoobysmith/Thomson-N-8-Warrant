import Thomson.Main
import Thomson.Task1b.Tasks
import Thomson.Tri5b.Task5b
import Thomson.Unique.Final

/-! # The main theorem, with every proved Task discharged

The default build (`Thomson.Main`) proves `thomson_eight_lower_of_tasks`, which takes the three
Tasks proved with `native_decide` — 1a, 1b (library `Task1b`) and 5b (library `Tri5b`) — as
hypotheses, so that it neither pays for their certificates nor depends on the axioms `native_decide`
adds.
This file, the library `Complete` (`lake build Complete`; it builds `Tri5b`, about an hour of CPU),
discharges them.  Nothing is left open: Task 5a is proved in `Thomson/TriLocalCert/` with
`decide +kernel`, so `#print axioms Thomson.thomson_eight_lower` lists no `sorryAx`, only
`propext, Classical.choice, Quot.sound` and one `…._native.native_decide.ax_…` axiom for each of
the 110 `native_decide` certificates (Task 1b's `check_ok`; Task 5b's `CFtab_eq`, `MItab_eq` and
the 107 covering parts).

Uniqueness (`UniquenessPlan.md`, `Thomson/Unique/`) is stated here too: `thomson_eight_unique` and
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
