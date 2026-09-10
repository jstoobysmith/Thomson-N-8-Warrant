import Mathlib
import Thomson.Basic

namespace Thomson
open Finset
open scoped RealInnerProductSpace

/-! ## 9. First-order conditions (force balance) -/

theorem energy_eq_half {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) :
    energy x = (1 / 2) * ∑ i, ∑ j ∈ univ.erase i, ‖x i - x j‖⁻¹ := by
  have split : ∀ i : Fin n, ∑ j ∈ univ.erase i, ‖x i - x j‖⁻¹
      = ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹ + ∑ j ∈ Finset.Iio i, ‖x i - x j‖⁻¹ := by
    intro i
    rw [← Finset.sum_union]
    · congr 1; ext j
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union,
        Finset.mem_Ioi, Finset.mem_Iio]
      exact ⟨fun h => lt_or_gt_of_ne (Ne.symm h), fun h => h.elim (fun h => h.ne') (fun h => h.ne)⟩
    · rw [Finset.disjoint_left]; intro j hj hj'
      exact lt_asymm (Finset.mem_Ioi.mp hj) (Finset.mem_Iio.mp hj')
  have swap : ∑ i, ∑ j ∈ Finset.Iio i, ‖x i - x j‖⁻¹ = ∑ i, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹ := by
    rw [Finset.sum_comm' (t' := univ) (s' := fun j => Finset.Ioi j)]
    · apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro i _
      rw [norm_sub_rev]
    · intro i j; simp [Finset.mem_Iio, Finset.mem_Ioi]
  simp only [split, Finset.sum_add_distrib, swap, energy]
  ring

/-- Energy of the other points, excluding `i`. -/
noncomputable def rest {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) (i : Fin n) : ℝ :=
  (1 / 2) * ∑ k ∈ univ.erase i, ∑ j ∈ (univ.erase i).erase k, ‖x k - x j‖⁻¹

theorem energy_update {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) (i : Fin n)
    (p : EuclideanSpace ℝ (Fin 3)) :
    energy (Function.update x i p) = (∑ j ∈ univ.erase i, ‖p - x j‖⁻¹) + rest x i := by
  rw [energy_eq_half, rest]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hi : ∑ j ∈ univ.erase i, ‖Function.update x i p i - Function.update x i p j‖⁻¹
      = ∑ j ∈ univ.erase i, ‖p - x j‖⁻¹ := by
    apply Finset.sum_congr rfl; intro j hj
    rw [Function.update_self, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hk : ∀ k ∈ univ.erase i, ∑ j ∈ univ.erase k, ‖Function.update x i p k - Function.update x i p j‖⁻¹
      = ‖p - x k‖⁻¹ + ∑ j ∈ (univ.erase i).erase k, ‖x k - x j‖⁻¹ := by
    intro k hk
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hki.symm, Finset.mem_univ i⟩)]
    rw [Function.update_of_ne hki, Function.update_self, norm_sub_rev, Finset.erase_right_comm]
    congr 1
    apply Finset.sum_congr rfl; intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
    rw [Function.update_of_ne hji]
  rw [hi, Finset.sum_congr rfl hk, Finset.sum_add_distrib]
  have hsym : ∑ k ∈ univ.erase i, ‖p - x k‖⁻¹ = ∑ j ∈ univ.erase i, ‖p - x j‖⁻¹ := rfl
  rw [hsym]; ring

theorem hasDerivAt_greatCircle (xi v : EuclideanSpace ℝ (Fin 3)) :
    HasDerivAt (fun t : ℝ => Real.cos t • xi + Real.sin t • v) v 0 := by
  have h1 := (Real.hasDerivAt_cos 0).smul_const xi
  have h2 := (Real.hasDerivAt_sin 0).smul_const v
  have := h1.add h2
  refine this.congr_deriv ?_
  simp

theorem hasDerivAt_inv_norm_curve (xi v xj : EuclideanSpace ℝ (Fin 3)) (hne : xi - xj ≠ 0) :
    HasDerivAt (fun t : ℝ => ‖(Real.cos t • xi + Real.sin t • v) - xj‖⁻¹)
      (-(⟪xi - xj, v⟫ / ‖xi - xj‖ ^ 3)) 0 := by
  set y : ℝ → EuclideanSpace ℝ (Fin 3) := fun t => (Real.cos t • xi + Real.sin t • v) - xj with hy
  have hy0 : y 0 = xi - xj := by simp [hy]
  have hyd : HasDerivAt y v 0 := (hasDerivAt_greatCircle xi v).sub_const xj
  have hn : 0 < ‖xi - xj‖ := norm_pos_iff.mpr hne
  have hq := hyd.norm_sq
  rw [hy0] at hq
  have hs := hq.sqrt (by rw [hy0]; positivity)
  have hi := hs.inv (by rw [hy0]; positivity)
  rw [hy0, Real.sqrt_sq (norm_nonneg _)] at hi
  show HasDerivAt (fun t => ‖y t‖⁻¹) _ 0
  have hfun : (fun t => ‖y t‖⁻¹) = (fun t => Real.sqrt (‖y t‖ ^ 2))⁻¹ := by
    funext t; simp only [Pi.inv_apply]; rw [Real.sqrt_sq (norm_nonneg _)]
  rw [hfun]
  refine hi.congr_deriv ?_
  field_simp

/-- The Coulomb force on point `i`. -/
noncomputable def force {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) (i : Fin n) :
    EuclideanSpace ℝ (Fin 3) :=
  ∑ j ∈ univ.erase i, (‖x i - x j‖ ^ 3)⁻¹ • (x i - x j)

/-- The great circle through `x i` in direction `v` stays on the sphere. -/
theorem norm_greatCircle {xi v : EuclideanSpace ℝ (Fin 3)} (hx : ‖xi‖ = 1) (hv : ‖v‖ = 1)
    (hxv : ⟪xi, v⟫ = 0) (t : ℝ) : ‖Real.cos t • xi + Real.sin t • v‖ = 1 := by
  have hsq : ‖Real.cos t • xi + Real.sin t • v‖ ^ 2 = 1 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right, hxv,
      hx, hv, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, mul_one, sq_abs, sq_abs]
    simp [Real.cos_sq_add_sin_sq]
  rw [← Real.sqrt_sq (norm_nonneg _), hsq, Real.sqrt_one]

/-- First variation: the force is orthogonal to every unit tangent vector at a minimiser. -/
theorem force_inner_eq_zero {n : ℕ} {x : Fin n → EuclideanSpace ℝ (Fin 3)} (hx : Admissible x)
    (hmin : ∀ y : Fin n → EuclideanSpace ℝ (Fin 3), Admissible y → energy x ≤ energy y)
    (i : Fin n) (v : EuclideanSpace ℝ (Fin 3)) (hv1 : ‖v‖ = 1) (hvx : ⟪x i, v⟫ = 0) :
    ⟪force x i, v⟫ = 0 := by
  set γ : ℝ → EuclideanSpace ℝ (Fin 3) := fun t => Real.cos t • x i + Real.sin t • v with hγ
  have hγ0 : γ 0 = x i := by simp [hγ]
  have hγc : Continuous γ := by fun_prop
  have hγn : ∀ t, ‖γ t‖ = 1 := fun t => norm_greatCircle (hx.1 i) hv1 hvx t
  -- nearby configurations are admissible
  have hev : ∀ᶠ t in nhds (0:ℝ), Admissible (Function.update x i (γ t)) := by
    have hall : ∀ᶠ t in nhds (0:ℝ), ∀ j, j ≠ i → γ t ≠ x j := by
      rw [Filter.eventually_all]; intro j
      by_cases hj : j = i
      · exact Filter.Eventually.of_forall fun t h => absurd hj h
      · have : ∀ᶠ t in nhds (0:ℝ), γ t ≠ x j := by
          apply hγc.continuousAt.eventually_ne
          rw [hγ0]; exact fun h => hj (hx.2 h).symm
        filter_upwards [this] with t ht; exact fun _ => ht
    filter_upwards [hall] with t ht
    refine ⟨?_, ?_⟩
    · intro j; by_cases hj : j = i
      · rw [hj, Function.update_self]; exact hγn t
      · rw [Function.update_of_ne hj]; exact hx.1 j
    · intro j k hjk
      by_cases hj : j = i <;> by_cases hk : k = i
      · rw [hj, hk]
      · rw [hj, Function.update_self, Function.update_of_ne hk] at hjk; exact absurd hjk (ht k hk)
      · rw [hk, Function.update_of_ne hj, Function.update_self] at hjk
        exact absurd hjk.symm (ht j hj)
      · rw [Function.update_of_ne hj, Function.update_of_ne hk] at hjk; exact hx.2 hjk
  -- local minimum along the curve
  have hloc : IsLocalMin (fun t => energy (Function.update x i (γ t))) 0 := by
    unfold IsLocalMin IsMinFilter
    filter_upwards [hev] with t ht
    show energy (Function.update x i (γ 0)) ≤ energy (Function.update x i (γ t))
    rw [hγ0, Function.update_eq_self]
    exact hmin _ ht
  -- derivative along the curve
  have hderiv : HasDerivAt (fun t => energy (Function.update x i (γ t)))
      (∑ j ∈ univ.erase i, -(⟪x i - x j, v⟫ / ‖x i - x j‖ ^ 3)) 0 := by
    have hfun : (fun t => energy (Function.update x i (γ t)))
        = fun t => (∑ j ∈ univ.erase i, ‖γ t - x j‖⁻¹) + rest x i := by
      funext t; exact energy_update x i (γ t)
    rw [hfun]
    apply HasDerivAt.add_const
    have hsum := HasDerivAt.sum (x := (0:ℝ)) (u := univ.erase i)
      (A := fun j t => ‖γ t - x j‖⁻¹) (A' := fun j => -(⟪x i - x j, v⟫ / ‖x i - x j‖ ^ 3))
      (fun j hj => by
        have hne : x i - x j ≠ 0 := by
          rw [sub_ne_zero]; exact fun h => (Finset.ne_of_mem_erase hj) (hx.2 h).symm
        exact hasDerivAt_inv_norm_curve (x i) v (x j) hne)
    have hfs : (∑ j ∈ univ.erase i, fun t : ℝ => ‖γ t - x j‖⁻¹)
        = fun t => ∑ j ∈ univ.erase i, ‖γ t - x j‖⁻¹ := by
      funext t; simp [Finset.sum_apply]
    rw [hfs] at hsum
    exact hsum
  have hzero := hloc.hasDerivAt_eq_zero hderiv
  rw [Finset.sum_neg_distrib, neg_eq_zero] at hzero
  rw [force, sum_inner, ← hzero]
  apply Finset.sum_congr rfl; intro j _
  rw [real_inner_smul_left, inv_mul_eq_div]

theorem force_balance {n : ℕ} {x : Fin n → EuclideanSpace ℝ (Fin 3)} (hx : Admissible x)
    (hmin : ∀ y : Fin n → EuclideanSpace ℝ (Fin 3), Admissible y → energy x ≤ energy y)
    (i : Fin n) :
    force x i = ((2:ℝ)⁻¹ * ∑ j ∈ univ.erase i, ‖x i - x j‖⁻¹) • x i := by
  have hxi : ‖x i‖ = 1 := hx.1 i
  -- Step 1: the force is parallel to `x i`
  have hpar : force x i = ⟪force x i, x i⟫ • x i := by
    set w := force x i - ⟪force x i, x i⟫ • x i with hw_def
    have hw : ⟪x i, w⟫ = 0 := by
      rw [hw_def, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hxi,
        real_inner_comm (x i) (force x i)]; ring
    have hw0 : w = 0 := by
      by_contra hw0
      have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have hu1 : ‖‖w‖⁻¹ • w‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwn.ne']
      have hux : ⟪x i, ‖w‖⁻¹ • w⟫ = 0 := by rw [real_inner_smul_right, hw, mul_zero]
      have h0 := force_inner_eq_zero hx hmin i _ hu1 hux
      have hFw : ⟪force x i, w⟫ = ‖w‖ ^ 2 := by
        have hF : force x i = w + ⟪force x i, x i⟫ • x i := by rw [hw_def]; abel
        conv_lhs => rw [hF]
        rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hw]; ring
      rw [real_inner_smul_right, hFw] at h0
      have : ‖w‖⁻¹ * ‖w‖ ^ 2 = ‖w‖ := by field_simp
      rw [this] at h0
      exact hwn.ne' h0
    exact (sub_eq_zero.mp hw0)
  -- Step 2: the multiplier
  have hc : ⟪force x i, x i⟫ = (2:ℝ)⁻¹ * ∑ j ∈ univ.erase i, ‖x i - x j‖⁻¹ := by
    rw [force, sum_inner, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j hj
    have hne : x i - x j ≠ 0 := by
      rw [sub_ne_zero]; exact fun h => (Finset.ne_of_mem_erase hj) (hx.2 h).symm
    have hn : 0 < ‖x i - x j‖ := norm_pos_iff.mpr hne
    have hxj : ‖x j‖ = 1 := hx.1 j
    have key : ⟪x i - x j, x i⟫ = ‖x i - x j‖ ^ 2 / 2 := by
      rw [norm_sub_sq_real, inner_sub_left, real_inner_self_eq_norm_sq, hxi, hxj,
        real_inner_comm (x i) (x j)]; ring
    rw [real_inner_smul_left, key]
    field_simp
  rw [← hc]; exact hpar

end Thomson
