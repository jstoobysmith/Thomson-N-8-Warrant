import Mathlib
import Thomson.ThreePoint.Certificate

/-! # U1 — the three-point bound as an identity, and its equality case

`docs/uniqueness.md`, step U1.  The proof of `three_point_bound` sums four nonnegative quantities:
the Bachoc–Vallentin sum, the pair slacks, the triangle slacks, and the degree-one Schoenberg sum.
Here that is recorded as an exact identity (`three_point_identity`), and so at a configuration
whose energy equals the bound every pair slack and every triangle slack vanishes
(`three_point_tight`). -/

namespace Thomson
open Finset
open scoped RealInnerProductSpace

/-- The value of the three-point bound of a certificate. -/
noncomputable def ThreePointCert.bound (C : ThreePointCert) : ℝ :=
  (64 * C.a0 - 8 * (C.a0 + C.a1) - 8 * Fsum C.L C.D 1 1 1) / 2

/-- The pair slack of a certificate at the pair `(i, j)`. -/
noncomputable def pairSlack (C : ThreePointCert) (x : Fin 8 → EuclideanSpace ℝ (Fin 3))
    (i j : Fin 8) : ℝ :=
  (1 - 18 * C.lam) * ‖x i - x j‖⁻¹ - C.a0 - C.a1 * ⟪x i, x j⟫
    - 3 * Fsum C.L C.D 1 ⟪x i, x j⟫ ⟪x i, x j⟫

/-- The triangle slack of a certificate at the ordered triple `(i, j, l)`. -/
noncomputable def triSlack (C : ThreePointCert) (x : Fin 8 → EuclideanSpace ℝ (Fin 3))
    (i j l : Fin 8) : ℝ :=
  C.lam * (‖x i - x j‖⁻¹ + ‖x i - x l‖⁻¹ + ‖x j - x l‖⁻¹)
    - Fsum C.L C.D ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫

/-- **The three-point identity** (blueprint §12.2): `2E − 2B = BV + pair slack + triangle slack
+ design`. -/
theorem three_point_identity (C : ThreePointCert) (x : Fin 8 → EuclideanSpace ℝ (Fin 3))
    (hx : OnSphere x) :
    2 * energy x - 2 * C.bound
      = (∑ i, ∑ j, ∑ l, Fsum C.L C.D ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫)
        + ∑ i, ∑ j ∈ univ.erase i, pairSlack C x i j
        + ∑ i, ∑ j ∈ univ.erase i, ∑ l ∈ (univ.erase i).erase j, triSlack C x i j l
        + C.a1 * ∑ i, ∑ j, ⟪x i, x j⟫ := by
  set F : ℝ → ℝ → ℝ → ℝ := Fsum C.L C.D with hF
  set t : Fin 8 → Fin 8 → ℝ := fun i j => ⟪x i, x j⟫ with ht
  set h : Fin 8 → Fin 8 → ℝ := fun i j => ‖x i - x j‖⁻¹ with hh
  have htt : ∀ i, t i i = 1 := fun i => by
    simp only [ht, real_inner_self_eq_norm_sq, hx i, one_pow]
  have hsym : ∀ i j, t j i = t i j := fun i j => real_inner_comm _ _
  -- the Bachoc–Vallentin sum, split by coincidences
  have hBV : ∑ i, ∑ j, ∑ l, F (t i j) (t i l) (t j l)
      = 8 * F 1 1 1 + ∑ i, ∑ j ∈ univ.erase i, 3 * F 1 (t i j) (t i j)
        + ∑ i, ∑ j ∈ univ.erase i, ∑ l ∈ (univ.erase i).erase j, F (t i j) (t i l) (t j l) := by
    rw [sum_triple_split]
    have hdiag : ∑ i : Fin 8, F (t i i) (t i i) (t i i) = 8 * F 1 1 1 := by
      simp only [htt, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    have hmid : ∀ i j, F (t i i) (t i j) (t i j) + F (t i j) (t i i) (t j i)
        + F (t i j) (t i j) (t j j) = 3 * F 1 (t i j) (t i j) := by
      intro i j
      have e1 : F (t i j) (t i i) (t j i) = F (t i i) (t i j) (t i j) := by
        rw [hsym, htt, hF, Fsum_swap12]
      have e2 : F (t i j) (t i j) (t j j) = F (t i i) (t i j) (t i j) := by
        rw [htt, htt, hF, Fsum_swap23, Fsum_swap12]
      rw [e1, e2, htt]; ring
    rw [hdiag]
    simp only [hmid]
  -- the distinct edge sums
  set A : ℝ := ∑ i, ∑ j ∈ univ.erase i, h i j with hA
  have hE : energy x = (1 / 2) * A := energy_eq_half x
  have htri : ∑ i, ∑ j ∈ univ.erase i, ∑ l ∈ (univ.erase i).erase j, triSlack C x i j l
      = C.lam * (18 * A)
        - ∑ i, ∑ j ∈ univ.erase i, ∑ l ∈ (univ.erase i).erase j, F (t i j) (t i l) (t j l) := by
    have : ∑ i, ∑ j ∈ univ.erase i, ∑ l ∈ (univ.erase i).erase j,
        C.lam * (h i j + h i l + h j l) = C.lam * (18 * A) := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [sum_distinct_swap23 h, sum_distinct_swap12 h, sum_distinct_swap23 h,
        sum_distinct_const h]
      simp only [Fintype.card_fin]; push_cast; ring
    rw [← this]
    simp only [triSlack, Finset.sum_sub_distrib]
    rfl
  set T : ℝ := ∑ i, ∑ j ∈ univ.erase i, t i j with hT
  have hpair : ∑ i, ∑ j ∈ univ.erase i, pairSlack C x i j
      = (1 - 18 * C.lam) * A - 56 * C.a0 - C.a1 * T
        - ∑ i, ∑ j ∈ univ.erase i, 3 * F 1 (t i j) (t i j) := by
    simp only [pairSlack, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast; ring
  have hdes : ∑ i, ∑ j, ⟪x i, x j⟫ = 8 + T := by
    have hsplit : ∑ i, ∑ j, ⟪x i, x j⟫ = ∑ i, (t i i + ∑ j ∈ univ.erase i, t i j) :=
      Finset.sum_congr rfl fun i _ => (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    rw [hsplit]
    simp only [htt, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast; ring
  change 2 * energy x - 2 * C.bound
      = (∑ i, ∑ j, ∑ l, F (t i j) (t i l) (t j l))
        + ∑ i, ∑ j ∈ univ.erase i, pairSlack C x i j
        + ∑ i, ∑ j ∈ univ.erase i, ∑ l ∈ (univ.erase i).erase j, triSlack C x i j l
        + C.a1 * ∑ i, ∑ j, ⟪x i, x j⟫
  rw [hBV, htri, hpair, hdes, hE, ThreePointCert.bound]
  ring

/-- `(√(2 − 2⟪xᵢ, xⱼ⟫))⁻¹ = ‖xᵢ − xⱼ‖⁻¹` on the sphere. -/
theorem inv_sqrt_two_sub_inner (x : Fin 8 → EuclideanSpace ℝ (Fin 3)) (hx : OnSphere x)
    (i j : Fin 8) : (Real.sqrt (2 - 2 * ⟪x i, x j⟫))⁻¹ = ‖x i - x j‖⁻¹ := by
  rw [inner_eq_of_norm (x i) (x j) (hx i) (hx j),
    show 2 - 2 * (1 - ‖x i - x j‖ ^ 2 / 2) = ‖x i - x j‖ ^ 2 by ring,
    Real.sqrt_sq (norm_nonneg _)]

/-- The pair slack is nonnegative on the certified range. -/
theorem pairSlack_nonneg (C : ThreePointCert) (x : Fin 8 → EuclideanSpace ℝ (Fin 3))
    (hx : OnSphere x) (i j : Fin 8) (hsep : ⟪x i, x j⟫ ≤ 5373 / 10000) :
    0 ≤ pairSlack C x i j := by
  have hge : -1 ≤ ⟪x i, x j⟫ := by
    have := abs_real_inner_le_norm (x i) (x j)
    rw [hx i, hx j, one_mul] at this
    exact (abs_le.mp this).1
  have h1 := C.pair _ hge hsep
  rw [inv_sqrt_two_sub_inner x hx i j] at h1
  unfold pairSlack
  linarith

/-- The triangle slack is nonnegative on the certified range. -/
theorem triSlack_nonneg (C : ThreePointCert) (x : Fin 8 → EuclideanSpace ℝ (Fin 3))
    (hx : OnSphere x) (i j l : Fin 8) (hij : ⟪x i, x j⟫ ≤ 5373 / 10000)
    (hil : ⟪x i, x l⟫ ≤ 5373 / 10000) (hjl : ⟪x j, x l⟫ ≤ 5373 / 10000) :
    0 ≤ triSlack C x i j l := by
  have hge : ∀ a b, -1 ≤ ⟪x a, x b⟫ := fun a b => by
    have := abs_real_inner_le_norm (x a) (x b)
    rw [hx a, hx b, one_mul] at this
    exact (abs_le.mp this).1
  have h1 := C.tri _ _ _ (hge i j) (hge i l) (hge j l) hij hil hjl
    (gram_det_nonneg (x i) (x j) (x l) (hx i) (hx j) (hx l))
  rw [inv_sqrt_two_sub_inner x hx, inv_sqrt_two_sub_inner x hx,
    inv_sqrt_two_sub_inner x hx] at h1
  unfold triSlack
  linarith

/-- The Bachoc–Vallentin sum of a certificate is nonnegative. -/
theorem bvSum_nonneg (C : ThreePointCert) (x : Fin 8 → EuclideanSpace ℝ (Fin 3))
    (hx : OnSphere x) :
    0 ≤ ∑ i, ∑ j, ∑ l, Fsum C.L C.D ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫ := by
  simp only [Fsum]
  rw [sum_swap_out]
  refine Finset.sum_nonneg fun k _ => ?_
  rw [sum_swap_out]
  refine Finset.sum_nonneg fun r _ => ?_
  simp only [← Finset.mul_sum]
  exact mul_nonneg (C.D_nonneg k r) (bv_positivity k x hx (C.L k r))

/-- **Equality forces every slack to vanish.** -/
theorem three_point_tight (C : ThreePointCert) (x : Fin 8 → EuclideanSpace ℝ (Fin 3))
    (hx : OnSphere x) (hsep : ∀ i j, i ≠ j → ⟪x i, x j⟫ ≤ 5373 / 10000)
    (hE : energy x = C.bound) :
    (∀ i j, i ≠ j → pairSlack C x i j = 0) ∧
    (∀ i j l, i ≠ j → i ≠ l → j ≠ l → triSlack C x i j l = 0) := by
  have hid := three_point_identity C x hx
  rw [hE, sub_self] at hid
  have h1 := bvSum_nonneg C x hx
  have h2 : 0 ≤ ∑ i, ∑ j ∈ univ.erase i, pairSlack C x i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j hj =>
      pairSlack_nonneg C x hx i j (hsep i j (Finset.ne_of_mem_erase hj).symm)
  have htri : ∀ i, ∀ j ∈ univ.erase i, ∀ l ∈ (univ.erase i).erase j, 0 ≤ triSlack C x i j l := by
    intro i j hj l hl
    have hji := Finset.ne_of_mem_erase hj
    have hli := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl)
    have hlj := Finset.ne_of_mem_erase hl
    exact triSlack_nonneg C x hx i j l (hsep i j hji.symm) (hsep i l hli.symm) (hsep j l hlj.symm)
  have h3 : 0 ≤ ∑ i, ∑ j ∈ univ.erase i, ∑ l ∈ (univ.erase i).erase j, triSlack C x i j l :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun l hl =>
      htri i j hj l hl
  have h4 : 0 ≤ C.a1 * ∑ i, ∑ j, ⟪x i, x j⟫ := mul_nonneg C.a1_nonneg (sum_P1_nonneg x)
  have hp0 : ∑ i, ∑ j ∈ univ.erase i, pairSlack C x i j = 0 := by linarith
  have ht0 : ∑ i, ∑ j ∈ univ.erase i, ∑ l ∈ (univ.erase i).erase j, triSlack C x i j l = 0 := by
    linarith
  constructor
  · intro i j hij
    have hj : j ∈ univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩
    have e1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j hj =>
      pairSlack_nonneg C x hx i j (hsep i j (Finset.ne_of_mem_erase hj).symm))).mp hp0 i
      (Finset.mem_univ _)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j hj =>
      pairSlack_nonneg C x hx i j (hsep i j (Finset.ne_of_mem_erase hj).symm))).mp e1 j hj
  · intro i j l hij hil hjl
    have hj : j ∈ univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩
    have hl : l ∈ (univ.erase i).erase j :=
      Finset.mem_erase.mpr ⟨hjl.symm, Finset.mem_erase.mpr ⟨hil.symm, Finset.mem_univ _⟩⟩
    have e1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j hj =>
      Finset.sum_nonneg fun l hl => htri i j hj l hl)).mp ht0 i (Finset.mem_univ _)
    have e2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j hj =>
      Finset.sum_nonneg fun l hl => htri i j hj l hl)).mp e1 j hj
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun l hl => htri i j hj l hl)).mp e2 l hl

end Thomson
