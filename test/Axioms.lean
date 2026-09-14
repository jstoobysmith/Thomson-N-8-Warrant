import Thomson.Complete

/-! Axiom audit: every final theorem must depend only on `propext`, `Classical.choice`,
`Quot.sound` — no `sorryAx`, no `Lean.ofReduceBool` (i.e. no `native_decide`). -/

#print axioms Thomson.thomson_eight_lower
#print axioms Thomson.thomson_eight
#print axioms Thomson.thomson_eight_unique
#print axioms Thomson.thomson_eight_minimiser_iff
#print axioms Thomson.Task1b.task1a
#print axioms Thomson.Task1b.task1b
#print axioms Thomson.Tri5b.task5b_of_task5a
