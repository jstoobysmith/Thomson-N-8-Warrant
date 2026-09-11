import Thomson.Main
import Thomson.Task1b.Tasks
import Thomson.Tri5b.Task5b

/-! # The main theorem, with every proved Task discharged

The default build (`Thomson.Main`) proves `thomson_eight_lower_of_tasks`, which takes the three
Tasks proved with `native_decide` — 1a, 1b (library `Task1b`) and 5b (library `Tri5b`) — as
hypotheses, so that it neither pays for their certificates nor depends on the axioms `native_decide`
adds.
This file, the library `Complete` (`lake build Complete`; it builds `Tri5b`, about an hour of CPU),
discharges them.  What is left is the `sorry` of `Thomson/ThreePoint/Tasks.lean`: Task 5a
(`triP_local`).  `#print axioms Thomson.thomson_eight_lower` lists `sorryAx` as long as it is open,
and one `…._native.native_decide.ax_…` axiom for each of the 110 `native_decide` certificates
(Task 1b's `check_ok`; Task 5b's `CFtab_eq`, `MItab_eq` and the 107 covering parts). -/

namespace Thomson

/-- **The matching lower bound**: no admissible configuration beats the best antiprism. -/
theorem thomson_eight_lower : antiprismEnergy uStar ≤ thomsonInf 8 :=
  thomson_eight_lower_of_tasks Task1b.task1a Task1b.task1b
    (Tri5b.task5b_of_task5a (triP_local Task1b.task1a Task1b.task1b))

/-- **The square antiprism solves the 8-point Thomson problem.** -/
theorem thomson_eight : thomsonInf 8 = antiprismEnergy uStar :=
  le_antisymm thomsonInf_le_uStar thomson_eight_lower

end Thomson
