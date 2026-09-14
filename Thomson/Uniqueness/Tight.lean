import Mathlib
import Thomson.Certificate.Assemble
import Thomson.LP.Separation
import Thomson.ThreePoint.Identity

/-! # U2 — the concrete certificate is tight only where its polynomials vanish

`docs/uniqueness.md`, step U2.  `theCert` is the certificate of `exists_threePointCert_of_tasks`,
made a definition (the factor `A_k` of `certH k = A_kᵀ A_k` chosen by `Classical.choose`).  Its
three-point polynomial is `Fh certH` (`theCert_Fsum`) and its bound is exactly `E(u*)`
(`theCert_bound`).  So at a configuration with `energy x = E(u*)` the equality case of the
three-point bound (`three_point_tight`) applies, and every pair slack and every triangle slack
vanishes; by `pairP_div`, `triP_div` that is `pairP pivots s = 0` at each of the 28 distances
(`tight_pairs`) and `triP pivots a b c = 0` at each of the 56 triangles (`tight_triangles`). -/

namespace Thomson
open Finset Matrix
open scoped RealInnerProductSpace

namespace Unique

/-- The factor `A_k` of `certH k = A_kᵀ A_k` (Task 2). -/
noncomputable def theA (h1b : Task1b) (k : Fin 6) :
    Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ :=
  Classical.choose (certH_factor h1b k)

theorem theA_spec (h1b : Task1b) (k : Fin 6) : certH k = (theA h1b k)ᵀ * theA h1b k :=
  Classical.choose_spec (certH_factor h1b k)

/-- `Fsum` of the factored data is `Fh certH`. -/
theorem theA_Fsum (h1b : Task1b) (u v t : ℝ) :
    Fsum (fun k => theA h1b k * (B k)ᵀ) (fun _ _ => 1) u v t = Fh certH u v t :=
  Fsum_certH (theA h1b) (theA_spec h1b) u v t

/-- **The concrete certificate**: the record of `exists_threePointCert_of_tasks`, as a definition. -/
noncomputable def theCert (h1a : Task1a) (h1b : Task1b) (h5b : Task5b) : ThreePointCert where
  a0 := a0Fix
  a1 := a1Fix
  lam := lamFix
  L := fun k => theA h1b k * (B k)ᵀ
  D := fun _ _ => 1
  D_nonneg := fun _ _ => zero_le_one
  a1_nonneg := side_conditions.1
  lam_nonneg := side_conditions.2.1
  lam_le := side_conditions.2.2
  pair := pair_of_poly _ _ _ _ _ fun s h1 h2 => by
    rw [theA_Fsum]; exact pairP_nonneg h1a h1b s h1 h2
  tri := tri_of_poly _ _ _ fun a b c ha1 hb1 hc1 ha2 hb2 hc2 hG => by
    rw [theA_Fsum]
    exact triP_nonneg (triP_local h1a h1b) h5b a b c ha1 hb1 hc1 ha2 hb2 hc2 hG
  bound_ge := by rw [theA_Fsum, certData_bound_eq h1a]

theorem theCert_Fsum (h1a : Task1a) (h1b : Task1b) (h5b : Task5b) :
    Fsum (theCert h1a h1b h5b).L (theCert h1a h1b h5b).D = Fh certH := by
  funext u v t; exact theA_Fsum h1b u v t

/-- The bound of the concrete certificate is exactly `E(u*)`. -/
theorem theCert_bound (h1a : Task1a) (h1b : Task1b) (h5b : Task5b) :
    (theCert h1a h1b h5b).bound = antiprismEnergy uStar := by
  unfold ThreePointCert.bound
  rw [theCert_Fsum]
  exact certData_bound_eq h1a

/-! ## Consequences of admissibility and `energy x ≤ E(u*)` -/

section config
variable {x : Fin 8 → EuclideanSpace ℝ (Fin 3)}

/-- Points of an admissible configuration are unit vectors. -/
theorem norm_eq_one_of_admissible (hx : Admissible x) (i : Fin 8) : ‖x i‖ = 1 := hx.1 i

/-- Sharp separation below `E(u*)`: every distance exceeds `0.962`. -/
theorem dist_gt_of_le (hx : Admissible x) (hE : energy x ≤ antiprismEnergy uStar) {i j : Fin 8}
    (hij : i ≠ j) : 481 / 500 < ‖x i - x j‖ :=
  separation_of_energy_le hx (hE.trans antiprismEnergy_uStar_lt.le) hij

/-- The chord range `[0.9619, 2]`. -/
theorem chord_range_of_le (hx : Admissible x) (hE : energy x ≤ antiprismEnergy uStar) :
    ∀ i j, i ≠ j → 9619 / 10000 ≤ ‖x i - x j‖ ∧ ‖x i - x j‖ ≤ 2 := by
  intro i j hij
  refine ⟨le_trans (by norm_num) (dist_gt_of_le hx hE hij).le, ?_⟩
  calc ‖x i - x j‖ ≤ ‖x i‖ + ‖x j‖ := norm_sub_le _ _
    _ = 2 := by rw [hx.1 i, hx.1 j]; norm_num

/-- The inner-product range `t ≤ 0.5373` of the certificate. -/
theorem inner_le_of_le (hx : Admissible x) (hE : energy x ≤ antiprismEnergy uStar) :
    ∀ i j, i ≠ j → ⟪x i, x j⟫ ≤ 5373 / 10000 := by
  intro i j hij
  have hs := dist_gt_of_le hx hE hij
  rw [inner_eq_of_norm _ _ (hx.1 i) (hx.1 j)]
  nlinarith [hs, sq_nonneg (‖x i - x j‖ - 481 / 500)]

/-- The chord range at a minimiser. -/
theorem chord_range (hx : Admissible x) (hE : energy x = antiprismEnergy uStar) :
    ∀ i j, i ≠ j → 9619 / 10000 ≤ ‖x i - x j‖ ∧ ‖x i - x j‖ ≤ 2 :=
  chord_range_of_le hx hE.le

/-- Distinct points are at positive distance. -/
theorem pt_dist_pos (hx : Admissible x) {i j : Fin 8} (hij : i ≠ j) : 0 < ‖x i - x j‖ :=
  norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hij (hx.2 h))

end config

/-! ## Tightness -/

section tight
variable (h1a : Task1a) (h1b : Task1b) (h5b : Task5b)
  {x : Fin 8 → EuclideanSpace ℝ (Fin 3)}

/-- At a minimiser every slack of the concrete certificate vanishes. -/
theorem theCert_tight (hx : Admissible x) (hE : energy x = antiprismEnergy uStar) :
    (∀ i j, i ≠ j → pairSlack (theCert h1a h1b h5b) x i j = 0) ∧
    (∀ i j l, i ≠ j → i ≠ l → j ≠ l → triSlack (theCert h1a h1b h5b) x i j l = 0) :=
  three_point_tight _ x hx.1 (inner_le_of_le hx hE.le) (hE.trans (theCert_bound h1a h1b h5b).symm)

include h1a h1b h5b in
/-- **Every distance of a minimiser is a zero of the pair polynomial.** -/
theorem tight_pairs (hx : Admissible x) (hE : energy x = antiprismEnergy uStar) :
    ∀ i j, i ≠ j → pairP pivots ‖x i - x j‖ = 0 := by
  intro i j hij
  have h0 := (theCert_tight h1a h1b h5b hx hE).1 i j hij
  have hs := (pt_dist_pos hx hij).ne'
  have hdiv := pairP_div pivots hs
  rw [← inner_eq_of_norm _ _ (hx.1 i) (hx.1 j)] at hdiv
  have e : pairP pivots ‖x i - x j‖ / ‖x i - x j‖ = 0 := by
    rw [hdiv, ← h0, pairSlack, theCert_Fsum]
    simp only [theCert]
    ring
  rcases div_eq_zero_iff.mp e with h | h
  · exact h
  · exact absurd h hs

include h1a h1b h5b in
/-- **Every triangle of a minimiser is a zero of the triangle polynomial.** -/
theorem tight_triangles (hx : Admissible x) (hE : energy x = antiprismEnergy uStar) :
    ∀ i j l, i ≠ j → i ≠ l → j ≠ l →
      triP pivots ‖x i - x j‖ ‖x i - x l‖ ‖x j - x l‖ = 0 := by
  intro i j l hij hil hjl
  have h0 := (theCert_tight h1a h1b h5b hx hE).2 i j l hij hil hjl
  have ha := (pt_dist_pos hx hij).ne'
  have hb := (pt_dist_pos hx hil).ne'
  have hc := (pt_dist_pos hx hjl).ne'
  have hdiv := triP_div pivots ha hb hc
  rw [← inner_eq_of_norm _ _ (hx.1 i) (hx.1 j), ← inner_eq_of_norm _ _ (hx.1 i) (hx.1 l),
    ← inner_eq_of_norm _ _ (hx.1 j) (hx.1 l)] at hdiv
  have e : triP pivots ‖x i - x j‖ ‖x i - x l‖ ‖x j - x l‖
      / (‖x i - x j‖ * ‖x i - x l‖ * ‖x j - x l‖) = 0 := by
    rw [hdiv, ← h0, triSlack, theCert_Fsum]
    simp only [theCert, one_div]
  rcases div_eq_zero_iff.mp e with h | h
  · exact h
  · exact absurd h (mul_ne_zero (mul_ne_zero ha hb) hc)

end tight

end Unique

end Thomson
