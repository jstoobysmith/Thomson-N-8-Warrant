import Thomson.ThreePoint.Kernel.Psi0
import Thomson.ThreePoint.Kernel.Psi1
import Thomson.ThreePoint.Kernel.Psi2
import Thomson.ThreePoint.Kernel.Psi3
import Thomson.ThreePoint.Kernel.Psi4
import Thomson.ThreePoint.Kernel.Psi5

/-! # Task 1c, part 2: the kernel lemma

`psiN k a b` has a double zero at `u*` for every block `k` and every entry `(a, b)`: the generated
files `Thomson/ThreePoint/Kernel/{Entries,Psi}<k>.lean` (`threepoint/kernel_lean.py`), assembled in
`Thomson.ThreePoint.Redundant` (`psi_dz`, `bvTerm_dz`).  See `Thomson.ThreePoint.Kernel.Defs`. -/
