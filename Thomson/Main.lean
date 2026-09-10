import Mathlib
import Thomson.ThreePoint.Tasks
import Thomson.Separation
import Thomson.Reduction

namespace Thomson
open Finset
open scoped RealInnerProductSpace
open Matrix

/-! # The main theorem -/

/-- Any certificate proves the open inequality: a configuration at least as good as the antiprism
has energy `≤ 19.6753`, hence (§15) all inner products `≤ 0.5373`, hence (§16) energy at least
the certificate's bound, which is at least `E(u*)`. -/
theorem thomson_eight_lower_of_cert (C : ThreePointCert) :
    antiprismEnergy uStar ≤ thomsonInf 8 := by
  apply lower_bound_of_near_optimal (by norm_num)
  intro x hx hE
  have hE' : energy x ≤ 19.6753 := hE.trans antiprismEnergy_uStar_lt.le
  have hsep : ∀ i j, i ≠ j → ⟪x i, x j⟫ ≤ 5373 / 10000 := by
    intro i j hij
    have hs := separation_of_energy_le hx hE' hij
    rw [inner_eq_of_norm _ _ (hx.1 i) (hx.1 j)]
    nlinarith [hs, sq_nonneg (‖x i - x j‖ - 481 / 500)]
  exact C.bound_ge.trans (three_point_bound C x hx hsep)


/-! ## 17. The main theorem -/

/-- The matching lower bound: no admissible configuration beats the best antiprism.  Proved
from `exists_threePointCert`, itself assembled from the eight Tasks of `Thomson.ThreePoint.Tasks`,
which are the only `sorry`s in the development. -/
theorem thomson_eight_lower : antiprismEnergy uStar ≤ thomsonInf 8 :=
  thomson_eight_lower_of_cert (Classical.choice exists_threePointCert)

/-- The square antiprism solves the 8-point Thomson problem (conditional on `thomson_eight_lower`). -/
theorem thomson_eight : thomsonInf 8 = antiprismEnergy uStar :=
  le_antisymm thomsonInf_le_uStar thomson_eight_lower

/-- What is actually proved about the value, sorry-free:
`19.6475 < thomsonInf 8 ≤ E(u*) < 19.6753`. -/
theorem thomsonInf_mem_Ioc : thomsonInf 8 ∈ Set.Ioc (19.6475 : ℝ) (antiprismEnergy uStar) :=
  ⟨thomsonInf_gt'', thomsonInf_le_uStar⟩

/-- The open inequality can fail by at most `0.0278`.  For comparison, the linear-programming
method cannot in principle do better than `19.6478`, a gap of `0.0275`: what is left is not a
matter of finding a better polynomial. -/
theorem thomson_eight_gap : antiprismEnergy uStar - thomsonInf 8 < 278 / 10000 := by
  have h1 := thomsonInf_gt''
  have h2 := antiprismEnergy_uStar_lt
  norm_num at h1 h2 ⊢
  linarith

end Thomson
