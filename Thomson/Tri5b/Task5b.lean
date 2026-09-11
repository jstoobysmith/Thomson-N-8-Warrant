import Thomson.Tri5b.Final
import Thomson.ThreePoint.Task5b
import Thomson.Task1b.Final

/-! # Task 5b, in the form the main development assumes

`Thomson.Task5b` is the proposition `Thomson/ThreePoint/Task5b.lean` states and assumes; here it is
discharged, from Task 5a and Task 1b at `10⁻¹²`. -/

namespace Thomson.Tri5b

open Thomson

/-- **Task 5b.**  The two hypotheses are the other tasks: Task 5a (`triP_local`, as `TriLocal` at
the radius `rhoLocal = 1/500`) and Task 1b at `10⁻¹²` (`pivots_close` with `pivotEps = 10⁻¹²`). -/
theorem task5b (hloc : TriLocal (fun _ => 1 / 500))
    (hclose : ∀ j, |pivots j - pivotsNum j| ≤ 1 / 10 ^ 12) : Thomson.Task5b :=
  fun a b c h1 h2 h3 h4 h5 h6 hg hout =>
    triP_global hloc hclose a b c h1 h2 h3 h4 h5 h6 hg hout

/-- Task 5a in the shape of `Thomson.triP_local`. -/
theorem triLocal_of_triP_local
    (h : ∀ m : Fin 5, ∀ a b c : ℝ, |a - (touchType m).1| ≤ rhoLocal →
      |b - (touchType m).2.1| ≤ rhoLocal → |c - (touchType m).2.2| ≤ rhoLocal →
      0 ≤ triP pivots a b c) :
    TriLocal (fun _ => 1 / 500) := fun m a b c ha hb hc => h m a b c ha hb hc

/-- **Task 5b from Task 5a alone**: Task 1b at `10⁻¹²` is proved (`Thomson.Task1b.pivots_close_12`,
in fact to `2·10⁻²¹`). -/
theorem task5b_of_task5a (hloc : TriLocal (fun _ => 1 / 500)) : Thomson.Task5b :=
  task5b hloc Thomson.Task1b.pivots_close_12

end Thomson.Tri5b
