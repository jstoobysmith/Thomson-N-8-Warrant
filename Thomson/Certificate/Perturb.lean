import Thomson.Certificate.Linear

namespace Thomson
open Finset Matrix

/-! # Perturbation of the pivots

The step shared by Tasks 2, 4 and 5: every quantity built from the certificate is *affine* in the
24 pivots (`Thomson.Certificate.Linear`), so replacing the true pivots by the rational reference
values `pivotsNum` changes it by at most `‖p − pivotsNum‖∞` times the ℓ¹-norm of its linear part —
a finite, explicitly computable rational quantity.  With Task 1b (`pivots_close`) this converts
each Task into a statement about `pivotsNum` alone, with a margin. -/

/-- The exact affine difference formula. -/
theorem IsAff.sub_eq {f : (Fin 24 → ℝ) → ℝ} (hf : IsAff f) (p q : Fin 24 → ℝ) :
    f p - f q = ∑ j, (p j - q j) * (f (Pi.single j 1) - f 0) := by
  rw [hf p, hf q, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The ℓ∞/ℓ¹ perturbation bound for an affine function of the pivots. -/
theorem IsAff.abs_sub_le {f : (Fin 24 → ℝ) → ℝ} (hf : IsAff f) {p q : Fin 24 → ℝ} {ε : ℝ}
    (h : ∀ j, |p j - q j| ≤ ε) :
    |f p - f q| ≤ ε * ∑ j, |f (Pi.single j 1) - f 0| := by
  rw [hf.sub_eq p q]
  calc |∑ j, (p j - q j) * (f (Pi.single j 1) - f 0)|
      ≤ ∑ j, |(p j - q j) * (f (Pi.single j 1) - f 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ε * |f (Pi.single j 1) - f 0| := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (h j) (abs_nonneg _)
    _ = ε * ∑ j, |f (Pi.single j 1) - f 0| := (Finset.mul_sum _ _ _).symm

/-- A lower bound for an affine function transfers from `q` to `p` with the perturbation loss. -/
theorem IsAff.nonneg_of_nonneg_sub {f : (Fin 24 → ℝ) → ℝ} (hf : IsAff f) {p q : Fin 24 → ℝ}
    {ε : ℝ} (h : ∀ j, |p j - q j| ≤ ε) (hq : ε * ∑ j, |f (Pi.single j 1) - f 0| ≤ f q) :
    0 ≤ f p := by
  have := (abs_le.mp (hf.abs_sub_le h)).1
  linarith

/-! ### The three instances used by the Tasks -/

/-- Task 4: the pair polynomial at a fixed chord length. -/
theorem pairP_perturb {p q : Fin 24 → ℝ} {ε : ℝ} (h : ∀ j, |p j - q j| ≤ ε) (s : ℝ) :
    |pairP p s - pairP q s| ≤ ε * ∑ j, |pairP (Pi.single j 1) s - pairP 0 s| :=
  (pairP_isAff s).abs_sub_le h

/-- Task 5: the triangle polynomial at a fixed chord triple. -/
theorem triP_perturb {p q : Fin 24 → ℝ} {ε : ℝ} (h : ∀ j, |p j - q j| ≤ ε) (a b c : ℝ) :
    |triP p a b c - triP q a b c| ≤ ε * ∑ j, |triP (Pi.single j 1) a b c - triP 0 a b c| :=
  (triP_isAff a b c).abs_sub_le h

/-- Task 2: the entries of the blocks.  `Hp` is affine in the pivots with linear part `eH`, so the
perturbation is supported on the 24 slots and bounded entrywise by `ε`. -/
theorem Hp_sub_apply (p q : Fin 24 → ℝ) (k : Fin 6) (a b : Fin (9 - (k : ℕ))) :
    Hp p k a b - Hp q k a b = ∑ j, eH j (k : ℕ) (a : ℕ) (b : ℕ) * (p j - q j) := by
  simp only [Hp, Matrix.of_apply, add_sub_add_left_eq_sub]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem abs_Hp_sub_apply_le {p q : Fin 24 → ℝ} {ε : ℝ} (h : ∀ j, |p j - q j| ≤ ε)
    (k : Fin 6) (a b : Fin (9 - (k : ℕ))) :
    |Hp p k a b - Hp q k a b| ≤ ε * ∑ j, eH j (k : ℕ) (a : ℕ) (b : ℕ) := by
  rw [Hp_sub_apply]
  calc |∑ j, eH j (k : ℕ) (a : ℕ) (b : ℕ) * (p j - q j)|
      ≤ ∑ j, |eH j (k : ℕ) (a : ℕ) (b : ℕ) * (p j - q j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, eH j (k : ℕ) (a : ℕ) (b : ℕ) * ε := Finset.sum_le_sum fun j _ => by
        rw [abs_mul, abs_of_nonneg (by unfold eH; split <;> norm_num)]
        exact mul_le_mul_of_nonneg_left (h j) (by unfold eH; split <;> norm_num)
    _ = ε * ∑ j, eH j (k : ℕ) (a : ℕ) (b : ℕ) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-! ### The linear part, explicitly

The ℓ¹-norms above, and the entries of `pivotMatrix` itself, are governed by the single quantity
`Gh j u v t`: the value of `Fh` on the indicator of pivot slot `j`.  It is the `(a,b)` entry of
`B_kᵀ S3_k(u,v,t) B_k` at the slot's position (doubled off the diagonal), with no reference to
`Hfix` — which is what makes the entries of `pivotMatrix` explicit polynomials in
`uStar, √2, rStar, s2Star, s4Star`. -/

/-- The linear part of `Fh ∘ Hp` in pivot `j`. -/
noncomputable def Gh (j : Fin 24) (u v t : ℝ) : ℝ :=
  ∑ k : Fin 6, ∑ a : Fin (9 - (k : ℕ)), ∑ b : Fin (9 - (k : ℕ)),
    eH j (k : ℕ) (a : ℕ) (b : ℕ) * ((B k)ᵀ * S3 (k : ℕ) u v t * B k) a b

theorem Fh_Hp_single_sub (j : Fin 24) (u v t : ℝ) :
    Fh (Hp (Pi.single j 1)) u v t - Fh (Hp 0) u v t = Gh j u v t := by
  simp only [Fh, Hp, Gh, Matrix.of_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : ∑ j' : Fin 24, eH j' (k : ℕ) (a : ℕ) (b : ℕ) * (Pi.single j (1:ℝ) : Fin 24 → ℝ) j'
      = eH j (k : ℕ) (a : ℕ) (b : ℕ) := by
    simp [Pi.single_apply, Finset.sum_ite_eq']
  have h0 : ∑ j' : Fin 24, eH j' (k : ℕ) (a : ℕ) (b : ℕ) * (0 : Fin 24 → ℝ) j' = 0 := by simp
  rw [h1, h0]; ring

/-- The linear part of the pair polynomial. -/
theorem pairP_single_sub (j : Fin 24) (s : ℝ) :
    pairP (Pi.single j 1) s - pairP 0 s = -(3 * s) * Gh j 1 (1 - s ^ 2 / 2) (1 - s ^ 2 / 2) := by
  simp only [pairP]
  rw [← Fh_Hp_single_sub j 1 (1 - s ^ 2 / 2) (1 - s ^ 2 / 2)]
  ring

/-- The linear part of the triangle polynomial. -/
theorem triP_single_sub (j : Fin 24) (a b c : ℝ) :
    triP (Pi.single j 1) a b c - triP 0 a b c
      = -(a * b * c) * Gh j (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c ^ 2 / 2) := by
  simp only [triP]
  rw [← Fh_Hp_single_sub j (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c ^ 2 / 2)]
  ring

/-- The entries of the pivot system in the bound row. -/
theorem pivotMatrix_bound_row (j : Fin 24) : pivotMatrix 0 j = -4 * Gh j 1 1 1 := by
  simp only [pivotMatrix, Matrix.of_apply, rowFun, rowSpec, Matrix.cons_val_zero, evalRow]
  rw [← Fh_Hp_single_sub j 1 1 1]
  ring

/-- The entries of the pivot system in a pair-value row. -/
theorem pivotMatrix_pairVal_row {i : Fin 24} {X : Fin 4} (h : rowSpec i = .pairVal X)
    (j : Fin 24) :
    pivotMatrix i j
      = -(3 * chord X) * Gh j 1 (1 - chord X ^ 2 / 2) (1 - chord X ^ 2 / 2) := by
  simp only [pivotMatrix, Matrix.of_apply, rowFun, h, evalRow]
  exact pairP_single_sub j (chord X)

/-- The entries of the pivot system in a triangle-value row. -/
theorem pivotMatrix_triVal_row {i : Fin 24} {m : Fin 5} (h : rowSpec i = .triVal m)
    (j : Fin 24) :
    pivotMatrix i j
      = -((touchType m).1 * (touchType m).2.1 * (touchType m).2.2)
        * Gh j (1 - (touchType m).1 ^ 2 / 2) (1 - (touchType m).2.1 ^ 2 / 2)
            (1 - (touchType m).2.2 ^ 2 / 2) := by
  simp only [pivotMatrix, Matrix.of_apply, rowFun, h, evalRow]
  exact triP_single_sub j _ _ _

/-- The entries of the pivot system in a pair-derivative row. -/
theorem pivotMatrix_pairDer_row {i : Fin 24} {X : Fin 4} (h : rowSpec i = .pairDer X)
    (j : Fin 24) :
    pivotMatrix i j
      = deriv (fun s => -(3 * s) * Gh j 1 (1 - s ^ 2 / 2) (1 - s ^ 2 / 2)) (chord X) := by
  simp only [pivotMatrix, Matrix.of_apply, rowFun, h, evalRow]
  rw [← deriv_fun_sub (pairP_differentiable _).differentiableAt
    (pairP_differentiable _).differentiableAt]
  exact congrArg (fun f => deriv f (chord X)) (funext fun s => pairP_single_sub j s)

/-- The entries of the pivot system in a triangle-derivative row. -/
theorem pivotMatrix_triD_row {i : Fin 24} {m : Fin 5} {c : Fin 3} (h : rowSpec i = .triD m c)
    (j : Fin 24) :
    pivotMatrix i j
      = deriv (fun d =>
          -(((touchType m).1 + (if c = 0 then 1 else 0) * d)
            * ((touchType m).2.1 + (if c = 1 then 1 else 0) * d)
            * ((touchType m).2.2 + (if c = 2 then 1 else 0) * d))
          * Gh j (1 - ((touchType m).1 + (if c = 0 then 1 else 0) * d) ^ 2 / 2)
              (1 - ((touchType m).2.1 + (if c = 1 then 1 else 0) * d) ^ 2 / 2)
              (1 - ((touchType m).2.2 + (if c = 2 then 1 else 0) * d) ^ 2 / 2)) 0 := by
  simp only [pivotMatrix, Matrix.of_apply, rowFun, h, evalRow]
  rw [← deriv_fun_sub (triD_differentiable _ m c).differentiableAt
    (triD_differentiable _ m c).differentiableAt]
  exact congrArg (fun f => deriv f (0:ℝ)) (funext fun d => triP_single_sub j _ _ _)

end Thomson
