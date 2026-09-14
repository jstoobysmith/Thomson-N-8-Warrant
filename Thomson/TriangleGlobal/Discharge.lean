import Thomson.TriangleGlobal.Final
import Thomson.Pivots.Discharge
import Thomson.Uniqueness.Chords

/-! # Task 5b, in the form `Thomson.Certificate.Assemble` states it

`Thomson.Task5b` is the proposition `Thomson/ThreePoint/Tasks.lean` states and the main development
takes as a hypothesis; here it is discharged, from Task 5a and Task 1b (at `10⁻¹²`, proved in the
`Task1b` library). -/

namespace Thomson.Tri5b

open Thomson

/-- **Task 5b**, from Task 5a (as `TriLocal` at the radius `rhoLocal = 1/500`) and Task 1b. -/
theorem task5b (hloc : TriLocal (fun _ => 1 / 500)) (hclose : Thomson.Task1b) : Thomson.Task5b :=
  fun a b c h1 h2 h3 h4 h5 h6 hg hout =>
    triP_global hloc hclose a b c h1 h2 h3 h4 h5 h6 hg hout

/-- Task 5a in the shape of `Thomson.Task5a`. -/
theorem triLocal_of_task5a (h : Thomson.Task5a) : TriLocal (fun _ => 1 / 500) :=
  fun m a b c ha hb hc => h m a b c ha hb hc

/-- **Task 5b from Task 5a alone**: Task 1b is proved (`Thomson.Task1b.task1b`). -/
theorem task5b_of_task5a (h5a : Thomson.Task5a) : Thomson.Task5b :=
  task5b (triLocal_of_task5a h5a) Thomson.Task1b.task1b

/-- **Task 5b with its margin** (uniqueness, `docs/uniqueness.md` U4): the covering's slack is
`≥ 10⁻¹⁰` outside the five cubes.  From Task 1b alone. -/
theorem task5bStrict : Thomson.Unique.Task5bStrict := numCertU_final Thomson.Task1b.task1b

end Thomson.Tri5b
