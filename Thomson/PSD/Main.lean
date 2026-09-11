import Thomson.PSD.Block0
import Thomson.PSD.Block1
import Thomson.PSD.Block2
import Thomson.PSD.Block3
import Thomson.PSD.Block4
import Thomson.PSD.Block5

/-! # Task 2: the blocks of the certificate are positive semidefinite

For each block `k`, `Hp p k = L D Lᵀ + N` with `L`, `D` the (rounded) `LDLᵀ` factors of
`Hp pivotsNum k − μ_k P` (`Thomson/PSD/Block*.lean`, `threepoint/psd_gen.py`): `D ≥ 0`, and
`N ≈ μ_k P` is diagonally dominant for every `p` within `10⁻¹²` of `pivotsNum`, with slack
`≈ 2μ_k = λ_min ∈ [5.9·10⁻⁴, 1.5·10⁻³]` against a perturbation of `10⁻¹²` (`Thomson.PSD.Check`).
All six checks are `decide +kernel`: no `native_decide`. -/

namespace Thomson.PSD

open Thomson

/-- **Task 2.**  With the pivots within `10⁻¹²` of `pivotsNum` (Task 1b), every block `Hp p k` of
the certificate is positive semidefinite. -/
theorem hp_posSemidef {p : Fin 24 → ℝ} (hclose : ∀ j, |p j - pivotsNum j| ≤ 1 / 10 ^ 12)
    (k : Fin 6) : (Hp p k).PosSemidef := by
  fin_cases k
  · exact posSemidef_of_blockOK hclose ok0
  · exact posSemidef_of_blockOK hclose ok1
  · exact posSemidef_of_blockOK hclose ok2
  · exact posSemidef_of_blockOK hclose ok3
  · exact posSemidef_of_blockOK hclose ok4
  · exact posSemidef_of_blockOK hclose ok5

end Thomson.PSD
