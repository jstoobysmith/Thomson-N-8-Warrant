import Mathlib
import Thomson.Antiprism
import Thomson.ThreePoint.Sharp
import Thomson.Unique.Congruent

/-! # U6: geometry — the chord inner products, no aligned quadruple, the antiprism Gram table

`UniquenessPlan.md`, step U6.  Colours `A = 0, D = 1, N = 2, F = 3` as in `Thomson.chord`. -/

namespace Thomson.Unique

open Thomson Matrix
open scoped RealInnerProductSpace InnerProductSpace

/-! ## The four inner products -/

/-- The inner product of two unit vectors at chord distance `chord X`. -/
noncomputable def tval (X : Fin 4) : ℝ := 1 - chord X ^ 2 / 2

theorem tval_zero : tval 0 = uStar := chord_inner_zero
theorem tval_one : tval 1 = 2 * uStar - 1 := chord_inner_one
theorem tval_two : tval 2 = -uStar + Real.sqrt 2 * (1 - uStar) / 2 := chord_inner_two
theorem tval_three : tval 3 = -uStar - Real.sqrt 2 * (1 - uStar) / 2 := chord_inner_three

/-- Unit vectors at distance `chord X` have inner product `tval X`. -/
theorem inner_eq_tval_of_norm {x y : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {X : Fin 4} (hxy : ‖x - y‖ = chord X) : ⟪x, y⟫ = tval X := by
  rw [inner_eq_of_norm x y hx hy, hxy, tval]

/-! ## No aligned quadruple -/

/-- The Gram determinant of the aligned pattern. -/
theorem det_aligned (tA tN : ℝ) :
    (!![1, tA, tN, tN; tA, 1, tN, tN; tN, tN, 1, tA; tN, tN, tA, 1] : Matrix (Fin 4) (Fin 4) ℝ).det
      = (1 - tA) ^ 2 * ((1 + tA) ^ 2 - 4 * tN ^ 2) := by
  have e1 : Fin.succAbove (1 : Fin 4) (2 : Fin 3) = 3 := by decide
  have e2 : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 := by decide
  have e3 : Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 := by decide
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, e1, e2, e3]
  ring

/-- Four unit vectors in `ℝ³` with `⟪a,b⟫ = ⟪c,d⟫ = tA` and all four cross inner products `tN`
exist only if the Gram determinant `(1 − tA)²((1 + tA)² − 4 tN²)` vanishes. -/
theorem aligned_det_eq_zero {a b c d : EuclideanSpace ℝ (Fin 3)} {tA tN : ℝ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
    (hab : ⟪a, b⟫ = tA) (hcd : ⟪c, d⟫ = tA)
    (hac : ⟪a, c⟫ = tN) (had : ⟪a, d⟫ = tN) (hbc : ⟪b, c⟫ = tN) (hbd : ⟪b, d⟫ = tN) :
    (1 - tA) ^ 2 * ((1 + tA) ^ 2 - 4 * tN ^ 2) = 0 := by
  by_contra hne
  have hG : Matrix.gram ℝ ![a, b, c, d]
      = !![1, tA, tN, tN; tA, 1, tN, tN; tN, tN, 1, tA; tN, tN, tA, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ha, hb, hc, hd, hab, hcd, hac, had, hbc, hbd,
        real_inner_comm a, real_inner_comm b, real_inner_comm c]
  have hli : LinearIndependent ℝ ![a, b, c, d] := by
    rw [← Matrix.det_gram_ne_zero_iff_linearIndependent, hG, det_aligned]
    exact hne
  have := hli.fintype_card_le_finrank
  simp at this

/-- **No aligned quadruple.**  Four unit vectors with `⟪a,b⟫ = ⟪c,d⟫ = tA` and the four cross
inner products `= tN` do not exist in `ℝ³`. -/
theorem no_aligned_quadruple (a b c d : EuclideanSpace ℝ (Fin 3))
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
    (hab : ⟪a, b⟫ = tval 0) (hcd : ⟪c, d⟫ = tval 0)
    (hac : ⟪a, c⟫ = tval 2) (had : ⟪a, d⟫ = tval 2) (hbc : ⟪b, c⟫ = tval 2)
    (hbd : ⟪b, d⟫ = tval 2) : False := by
  have h := aligned_det_eq_zero ha hb hc hd hab hcd hac had hbc hbd
  rw [tval_zero, tval_two] at h
  obtain ⟨u1, u2⟩ := uStar_mem_Icc
  obtain ⟨w1, w2⟩ := sqrt2_bounds
  have h1 : 0 < (1 - uStar) ^ 2 := by nlinarith
  have hN1 : -uStar + Real.sqrt 2 * (1 - uStar) / 2 < 18 / 100 := by nlinarith
  have hN2 : 16 / 100 < -uStar + Real.sqrt 2 * (1 - uStar) / 2 := by nlinarith
  have h2 : 0 < (1 + uStar) ^ 2 - 4 * (-uStar + Real.sqrt 2 * (1 - uStar) / 2) ^ 2 := by
    nlinarith
  exact (mul_pos h1 h2).ne' h

/-- `no_aligned_quadruple` in terms of distances. -/
theorem no_aligned_chords (a b c d : EuclideanSpace ℝ (Fin 3))
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
    (hab : ‖a - b‖ = chord 0) (hcd : ‖c - d‖ = chord 0)
    (hac : ‖a - c‖ = chord 2) (had : ‖a - d‖ = chord 2) (hbc : ‖b - c‖ = chord 2)
    (hbd : ‖b - d‖ = chord 2) : False :=
  no_aligned_quadruple a b c d ha hb hc hd (inner_eq_tval_of_norm ha hb hab)
    (inner_eq_tval_of_norm hc hd hcd) (inner_eq_tval_of_norm ha hc hac)
    (inner_eq_tval_of_norm ha hd had) (inner_eq_tval_of_norm hb hc hbc)
    (inner_eq_tval_of_norm hb hd hbd)

/-! ## The antiprism Gram table -/

/-- The colour table of `antiprism` in its *actual* labelling: `0..3` the top square
(`vᵢ` at angle `90°·i`), `4..7` the bottom square (`w_k = 4 + k` at angle `45° + 90°·k`).
Inside a square: `A = 0` for neighbours, `D = 1` for opposite vertices.  Across: `vᵢ` is `N = 2`
to `w_{i−1}` and `wᵢ` and `F = 3` to the other two.  (The diagonal is a dummy `0`.)

This is **not** the labelling of `plans/unique_enum.py` (there `vᵢ` is near `wᵢ, w_{i+1}`); see
`apPerm` and `apColPlan_eq`. -/
def apColG : Fin 8 → Fin 8 → Fin 4 :=
  ![![0, 0, 1, 0, 2, 3, 3, 2],
    ![0, 0, 0, 1, 2, 2, 3, 3],
    ![1, 0, 0, 0, 3, 2, 2, 3],
    ![0, 1, 0, 0, 3, 3, 2, 2],
    ![2, 2, 3, 3, 0, 0, 1, 0],
    ![3, 2, 2, 3, 0, 0, 0, 1],
    ![3, 3, 2, 2, 1, 0, 0, 0],
    ![2, 3, 3, 2, 0, 1, 0, 0]]

/-- The antiprism pattern in the labelling of `UniquenessPlan.md` / `plans/unique_enum.py`
(`ap`): squares `0..3` and `4..7`, `vᵢ` near `wᵢ` and `w_{i+1}` (`w_k = 4 + k`). -/
def apColPlan (i j : Fin 8) : Fin 4 :=
  if i = j then 0
  else if (i.val < 4) = (j.val < 4) then (if (i.val + 8 - j.val) % 4 = 2 then 1 else 0)
  else if (max i.val j.val - min i.val j.val) % 4 ≤ 1 then 2 else 3

/-- The relabelling from the plan's labelling to the geometric one: fixes `0..3`,
`4 ↦ 7, 5 ↦ 4, 6 ↦ 5, 7 ↦ 6` (i.e. `w_k ↦ w_{k−1}`). -/
def apPerm : Equiv.Perm (Fin 8) where
  toFun := ![0, 1, 2, 3, 7, 4, 5, 6]
  invFun := ![0, 1, 2, 3, 5, 6, 7, 4]
  left_inv := by decide
  right_inv := by decide

theorem apColPlan_eq (i j : Fin 8) : apColPlan i j = apColG (apPerm i) (apPerm j) := by
  revert i j; decide

theorem apColG_symm (i j : Fin 8) : apColG i j = apColG j i := by
  revert i j; decide

theorem inner_e3 (a b c d e f : ℝ) :
    ⟪(!₂[a, b, c] : EuclideanSpace ℝ (Fin 3)), !₂[d, e, f]⟫ = a * d + b * e + c * f := by
  rw [inner_coords]; simp

theorem sqrt_uStar_pos : 0 < Real.sqrt uStar :=
  Real.sqrt_pos.mpr (by linarith [uStar_mem_Icc.1])

theorem sqrt_uStar_lt_one : Real.sqrt uStar < 1 := by
  rw [Real.sqrt_lt' one_pos]; linarith [uStar_mem_Icc.2]

/-- The optimal antiprism lies on the unit sphere. -/
theorem norm_antiprism (i : Fin 8) : ‖antiprism (Real.sqrt uStar) i‖ = 1 :=
  antiprism_onSphere sqrt_uStar_pos sqrt_uStar_lt_one i

set_option linter.unusedSimpArgs false in
/-- **The antiprism Gram table** (actual labelling). -/
theorem inner_antiprism (i j : Fin 8) (hij : i ≠ j) :
    ⟪antiprism (Real.sqrt uStar) i, antiprism (Real.sqrt uStar) j⟫ = tval (apColG i j) := by
  have hu : 0 ≤ uStar := by linarith [uStar_mem_Icc.1]
  have hh : Real.sqrt uStar ^ 2 = uStar := Real.sq_sqrt hu
  have hr2 : Real.sqrt (1 - Real.sqrt uStar ^ 2) ^ 2 = 1 - uStar := by
    rw [hh]; exact Real.sq_sqrt (by linarith [uStar_mem_Icc.2])
  have hr2' : Real.sqrt (1 - uStar) ^ 2 = 1 - uStar :=
    Real.sq_sqrt (by linarith [uStar_mem_Icc.2])
  have h22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcase : ∀ k : Fin 8, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by
    decide
  rcases hcase i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hcase j with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
    | exact absurd rfl hij
    | (simp only [ap0, ap1, ap2, ap3, ap4, ap5, ap6, ap7, inner_e3]
       simp [apColG, tval_zero, tval_one, tval_two, tval_three, hh, hr2, hr2', h22, Real.mul_self_sqrt hu]
       try (ring_nf; simp only [hh, hr2, hr2', h22]; ring_nf))

/-- The antiprism Gram table in the plan's labelling: with `z := antiprism (√u*) ∘ apPerm`,
`⟪z i, z j⟫ = tval (apColPlan i j)`. -/
theorem inner_antiprism_plan (i j : Fin 8) (hij : i ≠ j) :
    ⟪antiprism (Real.sqrt uStar) (apPerm i), antiprism (Real.sqrt uStar) (apPerm j)⟫
      = tval (apColPlan i j) := by
  rw [apColPlan_eq]
  exact inner_antiprism _ _ (apPerm.injective.ne hij)

/-- **Assembly helper.**  Eight unit vectors whose distances follow the antiprism pattern (in the
plan's labelling `apColPlan`) are congruent to the optimal antiprism relabelled by `apPerm`. -/
theorem congruent_antiprism (y : Fin 8 → EuclideanSpace ℝ (Fin 3)) (hy : ∀ i, ‖y i‖ = 1)
    (hch : ∀ i j, i ≠ j → ‖y i - y j‖ = chord (apColPlan i j)) :
    ∃ f : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
      ∀ i, y i = f (antiprism (Real.sqrt uStar) (apPerm i)) := by
  refine congruent_of_gram_eq y (fun i => antiprism (Real.sqrt uStar) (apPerm i)) ?_
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hy, norm_antiprism]
  · rw [inner_eq_tval_of_norm (hy i) (hy j) (hch i j hij), inner_antiprism_plan i j hij]

end Thomson.Unique
