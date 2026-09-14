import Thomson.TriangleGlobal.CubeData

/-! # Task 5b: the parameters of the covering — GENERATED -/

namespace Thomson.Tri5b

/-- The root box `[-1, uHi]³` on the fixed-point grid. -/
def rootBx : Bx := ⟨-10000000000000000000000000000000000000000, 5373741950000000000000000000000000000000, -10000000000000000000000000000000000000000, 5373741950000000000000000000000000000000, -10000000000000000000000000000000000000000, 5373741950000000000000000000000000000000⟩

/-- The margin certified on every box: `10⁻¹⁰`. -/
def MG : ℤ := 1000000000000000000000000000000

/-- Enough fuel: the tree is at most `70` deep. -/
def FUEL : ℕ := 256

end Thomson.Tri5b
