import Thomson.ThreePoint.Tasks

/-! # Task 1b, as a proposition

Task 1b is **proved**, in the `Task1b` library (`Thomson/Task1b/`, a separate `lean_lib`: it reuses
Task 5b's interval machinery and ends in a `native_decide` of about a minute and a half).
`lake build Task1b` checks it.  Here it is only stated, and assumed.

The proof gives much more than `Tasks.lean` asks: `‖pivots − pivotsNum‖∞ ≤ 2·10⁻²¹`, where
`pivots_close` asks for `pivotEps = 10⁻⁶` and Task 5b needs `10⁻¹²`.  On the way it proves Task 1a
(`pivotMatrix_det_isUnit`) as well, since `‖I − N·pivotMatrix‖∞ ≤ 10⁻¹¹ < 1`.

One correction to the data it rests on: `threepoint/task1_leanform.py` builds the bound row as half
of `28a₀ − 4a₁ − 4F − E`, but `evalRow .bound = (64a₀ − 8(a₀+a₁) − 8F)/2 − E` *is*
`28a₀ − 4a₁ − 4F − E`.  So `approx_inverse` is the inverse of `pivotMatrix` with its bound row
halved, and `N·pivotMatrix = diag(2, 1, …, 1)`: the first column of `approx_inverse` has to be
halved before it inverts `pivotMatrix` (`Thomson.Task1b.NArr` does this).  The solution is
unaffected — only the approximate inverse. -/

namespace Thomson

/-- **Task 1a** — the pivot system is nonsingular.  Proved in the `Task1b` library as
`Thomson.Task1b.pivotMatrix_det_isUnit`. -/
def Task1a : Prop := IsUnit pivotMatrix.det

/-- **Task 1b** — the pivots are within `10⁻¹²` of `pivotsNum` (the precision Task 5b needs; the
proof gives `2·10⁻²¹`).  Proved in the `Task1b` library as `Thomson.Task1b.pivots_close_12`. -/
def Task1b : Prop := ∀ j, |pivots j - pivotsNum j| ≤ 1 / 10 ^ 12

/-- Task 1a, assumed here and proved in the `Task1b` library. -/
theorem task1a : Task1a := sorry

/-- Task 1b, assumed here and proved in the `Task1b` library. -/
theorem task1b : Task1b := sorry

/-- Task 1b at `10⁻¹²` gives `pivots_close` at `pivotEps = 10⁻⁶`. -/
theorem pivots_close_of_task1b (h : Task1b) : ∀ j, |pivots j - pivotsNum j| ≤ pivotEps :=
  fun j => le_trans (h j) (by unfold pivotEps; norm_num)

end Thomson
