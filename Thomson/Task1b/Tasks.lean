import Thomson.Task1b.Final
import Thomson.ThreePoint.Tasks

/-! # Tasks 1a and 1b, in the form `Thomson.ThreePoint.Tasks` states them -/

namespace Thomson.Task1b

/-- **Task 1a.** -/
theorem task1a : Thomson.Task1a := pivotMatrix_det_isUnit

/-- **Task 1b** at `pivotEps = 10⁻¹²` (the proof gives `2·10⁻²¹`, `pivots_close_sharp`). -/
theorem task1b : Thomson.Task1b := pivots_close_12

end Thomson.Task1b
