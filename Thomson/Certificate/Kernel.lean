import Thomson.Certificate.Kernel.Psi0
import Thomson.Certificate.Kernel.Psi1
import Thomson.Certificate.Kernel.Psi2
import Thomson.Certificate.Kernel.Psi3
import Thomson.Certificate.Kernel.Psi4
import Thomson.Certificate.Kernel.Psi5

/-! # Task 1c, part 2: the kernel lemma

`psiN k a b` has a double zero at `u*` for every block `k` and every entry `(a, b)`: the generated
files `Thomson/Certificate/Kernel/{Entries,Psi}<k>.lean` (`scripts/threepoint/kernel_lean.py`), assembled in
`Thomson.Certificate.Redundant` (`psi_dz`, `bvTerm_dz`).  See `Thomson.Certificate.Kernel.Defs`. -/
