import Thomson.Basic.Energy
import Thomson.Basic.ForceBalance
import Thomson.Antiprism.Cube
import Thomson.Antiprism.Family
import Thomson.Antiprism.Derivative
import Thomson.Antiprism.Enclosure
import Thomson.Antiprism.SharpChords
import Thomson.Antiprism.UStarSharp
import Thomson.Antiprism.MinPoly
import Thomson.LP.Yudin
import Thomson.LP.Reduction
import Thomson.LP.Separation
import Thomson.ThreePoint.BachocVallentin
import Thomson.ThreePoint.Certificate
import Thomson.ThreePoint.Toolkit
import Thomson.ThreePoint.Identity
import Thomson.Certificate.Data
import Thomson.Certificate.Linear
import Thomson.Certificate.Perturb
import Thomson.Certificate.Slack
import Thomson.Certificate.Kernel
import Thomson.Certificate.Redundant
import Thomson.Certificate.Assemble
import Thomson.Numerics.Interval
import Thomson.Numerics.TaylorModel
import Thomson.Numerics.Tensor
import Thomson.Numerics.TensorEngine
import Thomson.Numerics.PolyList
import Thomson.Numerics.ListTaylorModel
import Thomson.Numerics.Poly
import Thomson.Uniqueness.Final
import Thomson.Main

/-!
# The `N = 8` Thomson problem

The square antiprism at the optimal twist minimises the Coulomb energy of eight points on the
sphere, and it is the unique minimiser up to isometry (`Thomson.thomson_eight`,
`Thomson.thomson_eight_unique`, in `Thomson.Complete`).  The modules below are in reading order;
`organisation.md` explains the layout and each directory's `README.md` its literature source.

* `Basic`        — energy, admissible configurations, `thomsonInf`, existence, force balance
* `Antiprism`    — the antiprism family, its energy, `u*`, the cube, enclosures, the minimal polynomial
* `LP`           — Delsarte–Yudin linear-programming bounds, slack form, separation
* `ThreePoint`   — the Bachoc–Vallentin three-point bound and its equality case
* `Certificate`  — the concrete certificate: data, linear structure, perturbation, kernel lemma, assembly
* `Numerics`     — verified fixed-point intervals, Taylor models, list polynomials, tensors
* `Uniqueness`   — the equality case classified
* `Main`         — `thomson_eight_lower_of_tasks` (the expensive certificates as hypotheses)

The kernel-checked certificates live in the libraries `Pivots`, `PSD`, `Pair`, `TriangleLocal`,
`TriangleGlobal`; `Thomson.Complete` (library `Complete`) discharges them.
-/
