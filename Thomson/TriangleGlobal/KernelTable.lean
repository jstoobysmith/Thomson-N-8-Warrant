import Thomson.Numerics.PolyList
import Thomson.TriangleLocal.CFData

/-! # Task 5b, kernel layer, step 4: the tensor of `F` as a nested list

Task 5a already carries the tensor of `F` for the true certificate as a nested list
(`Thomson.TriLocalCert.CFtab3`), checked entry by entry against its definition `CFedata` with
`decide +kernel` (`CFt_eq`).  The leaf checker consumes that very list; its enclosure property in
the form the kernel layer uses (`Mem3`) follows from `ITMem_CFt`. -/

namespace Thomson.Tri5b

open Thomson.TriLocalCert

/-- The tensor of `F` for the true certificate, as the nested list `[i][j][k]` (`u` outermost). -/
def CFtabL : IL3 := CFtab3

set_option maxRecDepth 100000 in
theorem CFtabL_shape : Shape9 CFtabL := by decide

/-- **The tensor of `F` for the true certificate, as a nested list.** -/
theorem Mem3_CFtabL {p : Fin 24 → ℝ} (hclose : ∀ j, |p j - pivotsNum j| ≤ 1 / 10 ^ 12) :
    Mem3 CFtabL (ofRT (cF (Mmat (Hp p)))) :=
  Mem3_of_getL CFtabL_shape fun i j k => ITMem_CFt hclose i j k

end Thomson.Tri5b
