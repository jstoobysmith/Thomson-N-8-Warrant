import Thomson.ThreePoint.CertData
import Thomson.ThreePoint.Bound

/-! # The implicit certificate: its linear structure

Blueprint §12.7, Task 1 (implicit form).  The exact certificate cannot be written down (its
coordinates in the field `ℚ(√2, u*, r, s₂, s₄)` have 15 000-digit coefficients), so it is *defined*
as the unique solution of a small linear system:

* the unknowns are 24 entries of the symmetric blocks `H'_k` (`slot`); every other datum is a
  fixed rational (`a0Fix`, `a1Fix`, `lamFix`, `Hfix`);
* `F(u,v,t) = Σ_k ⟨H'_k, B_kᵀ S3_k(u,v,t) B_k⟩` (`Fh`), where `B_k` is an exact basis of the
  kernel complement `v_k^⊥` (`B`), so that `Σ_{i,j,l} F(antiprism) = 0` is automatic;
* the 24 *definitional rows* (`rowSpec`) — the bound, the value and derivative of the pair
  polynomial at the chord lengths, the value and gradient of the triangle polynomial at the five
  antiprism triangle types — are affine functions of the 24 pivots (`rowFun_isAff`), and
  `pivots := pivotMatrix⁻¹ *ᵥ pivotRhs` makes all of them vanish (`rows_vanish`) as soon as
  `pivotMatrix.det ≠ 0`.

Everything in this file is proved; the remaining obligations are listed in
`Thomson.ThreePoint.Tasks`. -/

namespace Thomson
open Finset Matrix

/-! ## The `H`-form of `F` and the affine parametrisation by the pivots -/

/-- `F` in the `H`-form: `Σ_k Σ_{a,b} H_k[a,b] · (B_kᵀ S3_k(u,v,t) B_k)[a,b]`. -/
noncomputable def Fh (H : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ)
    (u v t : ℝ) : ℝ :=
  ∑ k : Fin 6, ∑ a, ∑ b, H k a b * ((B k)ᵀ * S3 (k : ℕ) u v t * B k) a b

/-- The blocks `H'_k` as affine functions of the pivot vector `p`: fixed rational entries, with the
24 slots replaced by `p j`. -/
noncomputable def Hp (p : Fin 24 → ℝ) (k : Fin 6) :
    Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ :=
  Matrix.of fun a b => Hfix k a b + ∑ j, eH j k a b * p j

/-- The pair polynomial `P(s) = (1 − 18λ) − s·[a₀ + a₁ t + 3F(1,t,t)]`, `t = 1 − s²/2`, as a
function of the pivots. -/
noncomputable def pairP (p : Fin 24 → ℝ) (s : ℝ) : ℝ :=
  (1 - 18 * lamFix) - s * (a0Fix + a1Fix * (1 - s ^ 2 / 2)
    + 3 * Fh (Hp p) 1 (1 - s ^ 2 / 2) (1 - s ^ 2 / 2))

/-- The triangle polynomial `T(a,b,c) = λ(bc + ac + ab) − abc·F(1−a²/2, 1−b²/2, 1−c²/2)`. -/
noncomputable def triP (p : Fin 24 → ℝ) (a b c : ℝ) : ℝ :=
  lamFix * (b * c + a * c + a * b)
    - a * b * c * Fh (Hp p) (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c ^ 2 / 2)

/-- The four antiprism chord lengths: `A = √2·r` (square edge), `D = 2r` (square diagonal),
`N = s₂` (near cross), `F = s₄` (far cross). -/
noncomputable def chord : Fin 4 → ℝ := ![Real.sqrt 2 * rStar, 2 * rStar, s2Star, s4Star]

/-- The five antiprism triangle types, as chord-length triples: `FFA, FDN, FNA, DAA, NNA`. -/
noncomputable def touchType : Fin 5 → ℝ × ℝ × ℝ :=
  ![(s4Star, s4Star, Real.sqrt 2 * rStar), (s4Star, 2 * rStar, s2Star),
    (s4Star, s2Star, Real.sqrt 2 * rStar), (2 * rStar, Real.sqrt 2 * rStar, Real.sqrt 2 * rStar),
    (s2Star, s2Star, Real.sqrt 2 * rStar)]

/-- `T` along the coordinate line `c` through the touching type `m`: `d ↦ T(τ_m + d·e_c)`. -/
noncomputable def triD (p : Fin 24 → ℝ) (m : Fin 5) (c : Fin 3) (d : ℝ) : ℝ :=
  triP p ((touchType m).1 + (if c = 0 then 1 else 0) * d)
    ((touchType m).2.1 + (if c = 1 then 1 else 0) * d)
    ((touchType m).2.2 + (if c = 2 then 1 else 0) * d)

/-- The kinds of tightness row. -/
inductive RowSpec
  | bound
  | pairVal (X : Fin 4)
  | pairDer (X : Fin 4)
  | triVal (m : Fin 5)
  | triD (m : Fin 5) (c : Fin 3)

/-- The value of a row at the pivot vector `p` (all rows are `= 0` at the certificate). -/
noncomputable def evalRow (p : Fin 24 → ℝ) : RowSpec → ℝ
  | .bound => (64 * a0Fix - 8 * (a0Fix + a1Fix) - 8 * Fh (Hp p) 1 1 1) / 2 - antiprismEnergy uStar
  | .pairVal X => pairP p (chord X)
  | .pairDer X => deriv (pairP p) (chord X)
  | .triVal m => triP p (touchType m).1 (touchType m).2.1 (touchType m).2.2
  | .triD m c => deriv (triD p m c) 0

/-- The 24 definitional rows (`threepoint/task1_design.json`).  The two rows *not* here — the
pair value at the chord `A` (`pairVal 0`) and the `v`-derivative at the type `FDN` (`triD 1 1`) —
are consequences of these (Task 1c); the three symmetric duplicates (`triD 0 1 = triD 0 0`,
`triD 3 2 = triD 3 1`, `triD 4 1 = triD 4 0`) are equal as functions. -/
def rowSpec : Fin 24 → RowSpec :=
  ![.bound, .pairDer 0, .pairVal 1, .pairDer 1, .pairVal 2, .pairDer 2, .pairVal 3, .pairDer 3,
    .triVal 0, .triD 0 0, .triD 0 2,
    .triVal 1, .triD 1 0, .triD 1 2,
    .triVal 2, .triD 2 0, .triD 2 1, .triD 2 2,
    .triVal 3, .triD 3 0, .triD 3 1,
    .triVal 4, .triD 4 0, .triD 4 2]

noncomputable def rowFun (i : Fin 24) (p : Fin 24 → ℝ) : ℝ := evalRow p (rowSpec i)

/-! ## Affine functions of the pivots -/

/-- `f` is affine in the pivot vector: `f p = f 0 + Σ_j p_j (f e_j − f 0)`. -/
def IsAff (f : (Fin 24 → ℝ) → ℝ) : Prop :=
  ∀ p, f p = f 0 + ∑ j, p j * (f (Pi.single j 1) - f 0)

theorem IsAff.const (c : ℝ) : IsAff fun _ => c := by intro p; simp

theorem IsAff.coord (j : Fin 24) : IsAff fun p => p j := by
  intro p; simp [Pi.single_apply]

theorem IsAff.add {f g : (Fin 24 → ℝ) → ℝ} (hf : IsAff f) (hg : IsAff g) :
    IsAff fun p => f p + g p := by
  intro p
  show f p + g p = (f 0 + g 0) + ∑ j, p j * ((f (Pi.single j 1) + g (Pi.single j 1)) - (f 0 + g 0))
  rw [hf p, hg p]
  have : ∀ j, p j * ((f (Pi.single j 1) + g (Pi.single j 1)) - (f 0 + g 0))
      = p j * (f (Pi.single j 1) - f 0) + p j * (g (Pi.single j 1) - g 0) := fun j => by ring
  simp only [this, Finset.sum_add_distrib]; ring

theorem IsAff.const_mul {f : (Fin 24 → ℝ) → ℝ} (c : ℝ) (hf : IsAff f) :
    IsAff fun p => c * f p := by
  intro p
  show c * f p = c * f 0 + ∑ j, p j * (c * f (Pi.single j 1) - c * f 0)
  rw [hf p, mul_add, Finset.mul_sum]
  congr 1; exact Finset.sum_congr rfl fun j _ => by ring

theorem IsAff.mul_const {f : (Fin 24 → ℝ) → ℝ} (hf : IsAff f) (c : ℝ) :
    IsAff fun p => f p * c := by
  have := hf.const_mul c; simpa only [mul_comm c] using this

theorem IsAff.neg {f : (Fin 24 → ℝ) → ℝ} (hf : IsAff f) : IsAff fun p => -f p := by
  have := hf.const_mul (-1); simpa only [neg_one_mul] using this

theorem IsAff.sub {f g : (Fin 24 → ℝ) → ℝ} (hf : IsAff f) (hg : IsAff g) :
    IsAff fun p => f p - g p := by
  have := hf.add hg.neg; simpa only [sub_eq_add_neg] using this

theorem IsAff.div_const {f : (Fin 24 → ℝ) → ℝ} (hf : IsAff f) (c : ℝ) :
    IsAff fun p => f p / c := by
  have := hf.mul_const c⁻¹; simpa only [div_eq_mul_inv] using this

theorem IsAff.sum {ι : Type*} (s : Finset ι) (f : ι → (Fin 24 → ℝ) → ℝ)
    (hf : ∀ i ∈ s, IsAff (f i)) : IsAff fun p => ∑ i ∈ s, f i p := by
  have h := Finset.sum_induction f IsAff (fun a b ha hb => ha.add hb) (IsAff.const 0) hf
  convert h using 1
  funext p; simp [Finset.sum_apply]

/-- Differentiation in a parameter preserves affinity in the pivots. -/
theorem IsAff.deriv {F : (Fin 24 → ℝ) → ℝ → ℝ} (hF : ∀ s, IsAff fun p => F p s)
    (hd : ∀ p, Differentiable ℝ (F p)) (s : ℝ) : IsAff fun p => _root_.deriv (F p) s := by
  intro p
  have hfun : F p = fun s => F 0 s + ∑ j, p j * (F (Pi.single j 1) s - F 0 s) :=
    funext fun s => hF s p
  have hder : HasDerivAt (F p)
      (_root_.deriv (F 0) s
        + ∑ j, p j * (_root_.deriv (F (Pi.single j 1)) s - _root_.deriv (F 0) s)) s := by
    rw [hfun]
    exact ((hd 0).differentiableAt.hasDerivAt).add (HasDerivAt.fun_sum fun j _ =>
      (((hd (Pi.single j 1)).differentiableAt.hasDerivAt.sub
        (hd 0).differentiableAt.hasDerivAt).const_mul (p j)))
  exact hder.deriv

/-! ## Differentiability of the polynomial pieces -/

theorem Q3_differentiable (k : ℕ) :
    Differentiable ℝ (fun x : ℝ × ℝ × ℝ => Q3 k x.1 x.2.1 x.2.2) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 => simp only [Q3]; fun_prop
  | k + 6 => simp only [Q3]; fun_prop

@[fun_prop]
theorem Q3_differentiable_comp (k : ℕ) {f g h : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (hh : Differentiable ℝ h) :
    Differentiable ℝ fun s => Q3 k (f s) (g s) (h s) :=
  (Q3_differentiable k).comp (hf.prodMk (hg.prodMk hh))

@[fun_prop]
theorem Fh_differentiable_comp (H : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ)
    {f g h : ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hh : Differentiable ℝ h) : Differentiable ℝ fun s => Fh H (f s) (g s) (h s) := by
  unfold Fh
  simp only [Matrix.mul_apply, S3, Y3, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply,
    Matrix.transpose_apply, smul_eq_mul]
  fun_prop

theorem pairP_differentiable (p : Fin 24 → ℝ) : Differentiable ℝ (pairP p) := by
  unfold pairP; fun_prop

theorem triD_differentiable (p : Fin 24 → ℝ) (m : Fin 5) (c : Fin 3) :
    Differentiable ℝ (triD p m c) := by
  unfold triD triP; fun_prop

/-! ## The rows are affine in the pivots -/

theorem Fh_Hp_isAff (u v t : ℝ) : IsAff fun p => Fh (Hp p) u v t := by
  unfold Fh Hp
  simp only [Matrix.of_apply]
  refine IsAff.sum _ _ fun k _ => IsAff.sum _ _ fun a _ => IsAff.sum _ _ fun b _ => ?_
  exact ((IsAff.const _).add (IsAff.sum _ _ fun j _ => (IsAff.coord j).const_mul _)).mul_const _

theorem pairP_isAff (s : ℝ) : IsAff fun p => pairP p s := by
  unfold pairP
  exact (IsAff.const _).sub (((IsAff.const _).add ((Fh_Hp_isAff _ _ _).const_mul 3)).const_mul s)

theorem triP_isAff (a b c : ℝ) : IsAff fun p => triP p a b c := by
  unfold triP
  exact (IsAff.const _).sub ((Fh_Hp_isAff _ _ _).const_mul _)

theorem rowFun_isAff (i : Fin 24) : IsAff (rowFun i) := by
  unfold rowFun
  cases rowSpec i with
  | bound =>
    simp only [evalRow]
    exact (((IsAff.const _).sub ((Fh_Hp_isAff _ _ _).const_mul 8)).div_const 2).sub (IsAff.const _)
  | pairVal X => exact pairP_isAff _
  | pairDer X => exact IsAff.deriv (F := pairP) pairP_isAff pairP_differentiable _
  | triVal m => exact triP_isAff _ _ _
  | triD m c =>
    exact IsAff.deriv (F := fun p => triD p m c) (fun d => triP_isAff _ _ _)
      (fun p => triD_differentiable p m c) _

/-! ## The pivot system and the certificate -/

/-- The matrix of the 24 rows in the 24 pivots. -/
noncomputable def pivotMatrix : Matrix (Fin 24) (Fin 24) ℝ :=
  Matrix.of fun i j => rowFun i (Pi.single j 1) - rowFun i 0

/-- The right-hand side: minus the value of each row at `p = 0`. -/
noncomputable def pivotRhs : Fin 24 → ℝ := fun i => -rowFun i 0

/-- **The pivots of the certificate**: the solution of `pivotMatrix *ᵥ p = pivotRhs`. -/
noncomputable def pivots : Fin 24 → ℝ := pivotMatrix⁻¹ *ᵥ pivotRhs

theorem rowFun_eq_mulVec (i : Fin 24) (p : Fin 24 → ℝ) :
    rowFun i p = (pivotMatrix *ᵥ p) i - pivotRhs i := by
  rw [rowFun_isAff i p]
  simp only [pivotMatrix, pivotRhs, mulVec, dotProduct, Matrix.of_apply, sub_neg_eq_add]
  rw [add_comm]; congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- **Every definitional row vanishes at the certificate**, as soon as the pivot system is
nonsingular (Task 1a). -/
theorem rows_vanish (h : IsUnit pivotMatrix.det) (i : Fin 24) : rowFun i pivots = 0 := by
  rw [rowFun_eq_mulVec, pivots, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h,
    Matrix.one_mulVec, sub_self]

/-- The certificate's blocks. -/
noncomputable abbrev certH : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ :=
  Hp pivots

/-! ### The rows, individually -/

theorem row_bound (h : IsUnit pivotMatrix.det) :
    (64 * a0Fix - 8 * (a0Fix + a1Fix) - 8 * Fh certH 1 1 1) / 2 = antiprismEnergy uStar := by
  have := rows_vanish h 0
  simp only [rowFun, rowSpec, Matrix.cons_val_zero, evalRow] at this
  exact sub_eq_zero.mp this

theorem row_pairVal (h : IsUnit pivotMatrix.det) (X : Fin 4) (hX : X ≠ 0) :
    pairP pivots (chord X) = 0 := by
  fin_cases X
  · exact absurd rfl hX
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 2
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 4
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 6

theorem row_pairDer (h : IsUnit pivotMatrix.det) (X : Fin 4) :
    deriv (pairP pivots) (chord X) = 0 := by
  fin_cases X
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 1
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 3
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 5
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 7

theorem row_triVal (h : IsUnit pivotMatrix.det) (m : Fin 5) :
    triP pivots (touchType m).1 (touchType m).2.1 (touchType m).2.2 = 0 := by
  fin_cases m
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 8
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 11
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 14
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 18
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 21

/-! ### The symmetric duplicates -/

theorem Fh_swap12 (H : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ) (u v t : ℝ) :
    Fh H u v t = Fh H v u t := by
  unfold Fh; simp_rw [S3_swap12 _ u v t]

theorem Fh_swap23 (H : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ) (u v t : ℝ) :
    Fh H u v t = Fh H u t v := by
  unfold Fh; simp_rw [S3_swap23 _ u v t]

theorem triP_swap12 (p : Fin 24 → ℝ) (a b c : ℝ) : triP p a b c = triP p b a c := by
  unfold triP; rw [Fh_swap12]; ring

theorem triP_swap23 (p : Fin 24 → ℝ) (a b c : ℝ) : triP p a b c = triP p a c b := by
  unfold triP; rw [Fh_swap23]; ring

/-- Swapping the two equal coordinates of a touching type does not change the directional
derivative: the three duplicate gradient rows (`FFA`: `v = u`; `DAA`: `t = v`; `NNA`: `v = u`). -/
theorem triD_dup_FFA (p : Fin 24 → ℝ) : triD p 0 1 = triD p 0 0 := by
  funext d; simp only [triD, touchType]; simp only [Matrix.cons_val_zero]
  rw [triP_swap12]; simp

theorem triD_dup_DAA (p : Fin 24 → ℝ) : triD p 3 2 = triD p 3 1 := by
  funext d; simp only [triD, touchType]; simp
  rw [triP_swap23]

theorem triD_dup_NNA (p : Fin 24 → ℝ) : triD p 4 1 = triD p 4 0 := by
  funext d; simp only [triD, touchType]; simp
  rw [triP_swap12]

/-- With the duplicates, the value and the full gradient of `T` vanish at every touching type
for every coordinate, except the one dropped row `triD 1 1` (Task 1c). -/
theorem row_triD (h : IsUnit pivotMatrix.det) (m : Fin 5) (c : Fin 3) (hmc : (m, c) ≠ (1, 1)) :
    deriv (triD pivots m c) 0 = 0 := by
  fin_cases m <;> fin_cases c
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 9
  · rw [show (⟨0, by omega⟩ : Fin 5) = 0 from rfl, show (⟨1, by omega⟩ : Fin 3) = 1 from rfl, triD_dup_FFA]
    simpa [rowFun, rowSpec, evalRow] using rows_vanish h 9
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 10
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 12
  · exact absurd rfl hmc
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 13
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 15
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 16
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 17
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 19
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 20
  · rw [show (⟨3, by omega⟩ : Fin 5) = 3 from rfl, show (⟨2, by omega⟩ : Fin 3) = 2 from rfl, triD_dup_DAA]
    simpa [rowFun, rowSpec, evalRow] using rows_vanish h 20
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 22
  · rw [show (⟨4, by omega⟩ : Fin 5) = 4 from rfl, show (⟨1, by omega⟩ : Fin 3) = 1 from rfl, triD_dup_NNA]
    simpa [rowFun, rowSpec, evalRow] using rows_vanish h 22
  · simpa [rowFun, rowSpec, evalRow] using rows_vanish h 23


/-! ## From the `H`-form back to the `LDLᵀ`-form of `ThreePointCert` -/

theorem dot_mulVec_sum_eq_trace {n : ℕ} (L S : Matrix (Fin n) (Fin n) ℝ) :
    ∑ r, (L r ⬝ᵥ S.mulVec (L r)) = Matrix.trace (L * S * Lᵀ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, dotProduct,
    mulVec, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem Fh_eq_trace (H : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ)
    (u v t : ℝ) :
    Fh H u v t = ∑ k : Fin 6, Matrix.trace (H k * ((B k)ᵀ * S3 (k : ℕ) u v t * B k)ᵀ) := by
  unfold Fh
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]

/-- `Fsum` of `L k := A k * (B k)ᵀ`, `D := 1` is `Fh` of `H k := (A k)ᵀ * A k`. -/
theorem Fsum_eq_Fh (A : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ)
    (u v t : ℝ) :
    Fsum (fun k => A k * (B k)ᵀ) (fun _ _ => 1) u v t = Fh (fun k => (A k)ᵀ * A k) u v t := by
  unfold Fsum
  rw [Fh_eq_trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [one_mul]
  rw [dot_mulVec_sum_eq_trace]
  set S := S3 (k : ℕ) u v t
  have hX : ((A k)ᵀ * A k)ᵀ = (A k)ᵀ * A k := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc Matrix.trace (A k * (B k)ᵀ * S * (A k * (B k)ᵀ)ᵀ)
      = Matrix.trace ((A k)ᵀ * (A k * (B k)ᵀ * S * B k)) := by
        rw [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
          Matrix.trace_mul_comm]
    _ = Matrix.trace ((A k)ᵀ * A k * ((B k)ᵀ * S * B k)) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((A k)ᵀ * A k * ((B k)ᵀ * S * B k)ᵀ) := by
        rw [← Matrix.trace_transpose ((A k)ᵀ * A k * ((B k)ᵀ * S * B k)ᵀ), Matrix.transpose_mul,
          Matrix.transpose_transpose, hX, Matrix.trace_mul_comm]

end Thomson
