import Mathlib
import Thomson.Basic

namespace Thomson
open Finset
open scoped RealInnerProductSpace
open Matrix

/-! # Bachoc–Vallentin three-point positivity for `S²`, degree `d = 8`, `k ≤ 5`

Blueprint §12.2.  Everything here is proved. -/



/-- The inner polynomial of the Bachoc–Vallentin matrices for `S²`: the Chebyshev polynomial
`T_k` of the equator `S¹`, homogenised so that
`Q3 k u v t = ((1-u²)(1-v²))^{k/2} · T_k((t-uv)/√((1-u²)(1-v²)))` is a polynomial.  `k ≤ 5`. -/
noncomputable def Q3 (k : ℕ) (u v t : ℝ) : ℝ :=
  match k with
  | 0 => 1
  | 1 => t - u * v
  | 2 => 2 * (t - u * v) ^ 2 - (1 - u ^ 2) * (1 - v ^ 2)
  | 3 => 4 * (t - u * v) ^ 3 - 3 * (t - u * v) * ((1 - u ^ 2) * (1 - v ^ 2))
  | 4 => 8 * (t - u * v) ^ 4 - 8 * (t - u * v) ^ 2 * ((1 - u ^ 2) * (1 - v ^ 2))
          + ((1 - u ^ 2) * (1 - v ^ 2)) ^ 2
  | 5 => 16 * (t - u * v) ^ 5 - 20 * (t - u * v) ^ 3 * ((1 - u ^ 2) * (1 - v ^ 2))
          + 5 * (t - u * v) * ((1 - u ^ 2) * (1 - v ^ 2)) ^ 2
  | _ => 0

/-- `Y_k(u,v,t)_{ij} = uⁱ vʲ Q_k(u,v,t)`, `0 ≤ i,j ≤ 8-k` (the block sizes of degree `d = 8`). -/
noncomputable def Y3 (k : ℕ) (u v t : ℝ) : Matrix (Fin (9 - k)) (Fin (9 - k)) ℝ :=
  Matrix.of fun i j => u ^ (i : ℕ) * v ^ (j : ℕ) * Q3 k u v t

/-- The Bachoc–Vallentin matrix `S_k = (1/6) Σ_{σ ∈ S₃} Y_k ∘ σ`, symmetric in `(u,v,t)`. -/
noncomputable def S3 (k : ℕ) (u v t : ℝ) : Matrix (Fin (9 - k)) (Fin (9 - k)) ℝ :=
  (1 / 6 : ℝ) • (Y3 k u v t + Y3 k u t v + Y3 k v u t + Y3 k v t u + Y3 k t u v + Y3 k t v u)

theorem S3_swap12 (k : ℕ) (u v t : ℝ) : S3 k u v t = S3 k v u t := by
  ext i j
  simp only [S3, Y3, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, smul_eq_mul]
  ring
theorem S3_swap23 (k : ℕ) (u v t : ℝ) : S3 k u v t = S3 k u t v := by
  ext i j
  simp only [S3, Y3, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, smul_eq_mul]
  ring

/-- The three-point polynomial `F(u,v,t) = Σ_k ⟨F_k, S_k(u,v,t)⟩` with `F_k = L_kᵀ D_k L_k` given in
factored form, so that positive semidefiniteness is `D_k ≥ 0` and needs no linear algebra. -/
noncomputable def Fsum (L : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ)
    (D : (k : Fin 6) → Fin (9 - (k : ℕ)) → ℝ) (u v t : ℝ) : ℝ :=
  ∑ k : Fin 6, ∑ r, D k r * (L k r ⬝ᵥ (S3 (k : ℕ) u v t).mulVec (L k r))

theorem Fsum_swap12 (L) (D) (u v t : ℝ) : Fsum L D u v t = Fsum L D v u t := by
  unfold Fsum
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun r _ => ?_
  rw [S3_swap12]
theorem Fsum_swap23 (L) (D) (u v t : ℝ) : Fsum L D u v t = Fsum L D u t v := by
  unfold Fsum
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun r _ => ?_
  rw [S3_swap23]

/-! ### The addition theorem on the equator `S¹`

Real and imaginary parts of `(a + ib)^k`, `k ≤ 5`: the degree-`k` harmonics of `S¹`, evaluated on
the tangent-plane coordinates `(a, b)` of a unit vector. -/
noncomputable def C1 (k : ℕ) (a b : ℝ) : ℝ :=
  match k with
  | 0 => 1 | 1 => a | 2 => a ^ 2 - b ^ 2 | 3 => a ^ 3 - 3 * a * b ^ 2
  | 4 => a ^ 4 - 6 * a ^ 2 * b ^ 2 + b ^ 4 | 5 => a ^ 5 - 10 * a ^ 3 * b ^ 2 + 5 * a * b ^ 4
  | _ => 0
noncomputable def S1 (k : ℕ) (a b : ℝ) : ℝ :=
  match k with
  | 0 => 0 | 1 => b | 2 => 2 * a * b | 3 => 3 * a ^ 2 * b - b ^ 3
  | 4 => 4 * a ^ 3 * b - 4 * a * b ^ 3 | 5 => 5 * a ^ 4 * b - 10 * a ^ 2 * b ^ 3 + b ^ 5
  | _ => 0

/-- **Addition theorem.**  If `y, z` have tangent-plane coordinates `(a,b)`, `(a',b')` at `x`
(so `t − uv = aa' + bb'`, `1 − u² = a² + b²`, `1 − v² = a'² + b'²`), then
`Q_k(u,v,t) = C_k(a,b) C_k(a',b') + S_k(a,b) S_k(a',b')` — de Moivre. -/
theorem Q3_addition (k : ℕ) (hk : k ≤ 5) (u v t a b a' b' : ℝ)
    (hu : 1 - u ^ 2 = a ^ 2 + b ^ 2) (hv : 1 - v ^ 2 = a' ^ 2 + b' ^ 2)
    (ht : t - u * v = a * a' + b * b') :
    Q3 k u v t = C1 k a b * C1 k a' b' + S1 k a b * S1 k a' b' := by
  interval_cases k <;> simp only [Q3, C1, S1, ht, hu, hv] <;> ring

/-- The quadratic form of `Σ_{j,l} Y_k` at a fixed centre is a sum of two squares. -/
theorem quad_Y3_nonneg (k : ℕ) (hk : k ≤ 5) {n : ℕ} (u : Fin n → ℝ) (t : Fin n → Fin n → ℝ)
    (a b : Fin n → ℝ) (hu : ∀ j, 1 - u j ^ 2 = a j ^ 2 + b j ^ 2)
    (ht : ∀ j l, t j l - u j * u l = a j * a l + b j * b l)
    (w : Fin (9 - k) → ℝ) :
    0 ≤ ∑ j, ∑ l, w ⬝ᵥ (Y3 k (u j) (u l) (t j l)).mulVec w := by
  have key : ∀ j l, w ⬝ᵥ (Y3 k (u j) (u l) (t j l)).mulVec w
      = (∑ p, w p * u j ^ (p : ℕ)) * (∑ p, w p * u l ^ (p : ℕ))
        * (C1 k (a j) (b j) * C1 k (a l) (b l) + S1 k (a j) (b j) * S1 k (a l) (b l)) := by
    intro j l
    rw [← Q3_addition k hk (u j) (u l) (t j l) (a j) (b j) (a l) (b l) (hu j) (hu l) (ht j l)]
    simp only [dotProduct, mulVec, Y3, Matrix.of_apply]
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  simp only [key]
  have hsq : ∀ (g c s : Fin n → ℝ), ∑ j, ∑ l, g j * g l * (c j * c l + s j * s l)
      = (∑ j, g j * c j) ^ 2 + (∑ j, g j * s j) ^ 2 := by
    intro g c s
    simp only [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hsq (fun j => ∑ p, w p * u j ^ (p : ℕ)) (fun j => C1 k (a j) (b j)) (fun j => S1 k (a j) (b j))]
  positivity

/-- Relabelling lemmas for triple sums. -/
theorem tsum_swap12 {ι : Type*} [Fintype ι] (g : ι → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ l, g i j l = ∑ i, ∑ j, ∑ l, g j i l := by
  rw [Finset.sum_comm]
theorem tsum_swap23 {ι : Type*} [Fintype ι] (g : ι → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ l, g i j l = ∑ i, ∑ j, ∑ l, g i l j := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

/-- The symmetrised triple sum equals the unsymmetrised one: each permutation of `(u,v,t)` is a
relabelling of `(i,j,l)`. -/
theorem sum_S3_eq_sum_Y3 (k : ℕ) {n : ℕ} (t : Fin n → Fin n → ℝ) (hsym : ∀ i j, t j i = t i j)
    (w : Fin (9 - k) → ℝ) :
    ∑ i, ∑ j, ∑ l, w ⬝ᵥ (S3 k (t i j) (t i l) (t j l)).mulVec w
      = ∑ i, ∑ j, ∑ l, w ⬝ᵥ (Y3 k (t i j) (t i l) (t j l)).mulVec w := by
  set Φ : Fin n → Fin n → Fin n → ℝ :=
    fun i j l => w ⬝ᵥ (Y3 k (t i j) (t i l) (t j l)).mulVec w with hΦ
  have expand : ∀ i j l, w ⬝ᵥ (S3 k (t i j) (t i l) (t j l)).mulVec w
      = (1 / 6 : ℝ) * (Φ i j l + Φ j i l + Φ i l j + Φ l i j + Φ j l i + Φ l j i) := by
    intro i j l
    simp only [S3, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add,
      smul_eq_mul, hΦ, hsym]
  have e1 : ∑ i, ∑ j, ∑ l, Φ j i l = ∑ i, ∑ j, ∑ l, Φ i j l := (tsum_swap12 Φ).symm
  have e2 : ∑ i, ∑ j, ∑ l, Φ i l j = ∑ i, ∑ j, ∑ l, Φ i j l := (tsum_swap23 Φ).symm
  have e3 : ∑ i, ∑ j, ∑ l, Φ l i j = ∑ i, ∑ j, ∑ l, Φ i j l := by
    rw [tsum_swap23 (fun i j l => Φ l i j)]; exact (tsum_swap12 Φ).symm
  have e4 : ∑ i, ∑ j, ∑ l, Φ j l i = ∑ i, ∑ j, ∑ l, Φ i j l := by
    rw [tsum_swap12 (fun i j l => Φ j l i)]; exact (tsum_swap23 Φ).symm
  have e5 : ∑ i, ∑ j, ∑ l, Φ l j i = ∑ i, ∑ j, ∑ l, Φ i j l := by
    rw [tsum_swap12 (fun i j l => Φ l j i), tsum_swap23 (fun i j l => Φ l i j)]
    exact (tsum_swap12 Φ).symm
  simp only [expand, ← Finset.mul_sum, Finset.sum_add_distrib, e1, e2, e3, e4, e5]
  ring

/-- Every unit vector of `ℝ³` has an orthonormal frame of its orthogonal complement, giving
tangent-plane coordinates with Parseval's identity: extend `{x}` to an orthonormal basis. -/
theorem exists_tangent_frame (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1) :
    ∃ e₁ e₂ : EuclideanSpace ℝ (Fin 3), ∀ y z : EuclideanSpace ℝ (Fin 3), ‖y‖ = 1 → ‖z‖ = 1 →
      (1 - ⟪x, y⟫ ^ 2 = ⟪e₁, y⟫ ^ 2 + ⟪e₂, y⟫ ^ 2) ∧
      (⟪y, z⟫ - ⟪x, y⟫ * ⟪x, z⟫ = ⟪e₁, y⟫ * ⟪e₁, z⟫ + ⟪e₂, y⟫ * ⟪e₂, z⟫) := by
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = Fintype.card (Fin 3) := by simp
  let v : Fin 3 → EuclideanSpace ℝ (Fin 3) := fun _ => x
  have hv : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subtype.ext (by
      have hi := i.2; have hj := j.2
      simp only [Set.mem_singleton_iff] at hi hj
      rw [hi, hj])
    subst hij
    simp [Set.domRestrict, v, real_inner_self_eq_norm_sq, hx]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hv
  have hb0 : b 0 = x := hb 0 (Set.mem_singleton 0)
  refine ⟨b 1, b 2, fun y z hy hz => ?_⟩
  have P := b.sum_inner_mul_inner y z
  have Py := b.sum_inner_mul_inner y y
  rw [Fin.sum_univ_three, hb0] at P Py
  rw [real_inner_self_eq_norm_sq, hy] at Py
  have c1 : ⟪y, x⟫ = ⟪x, y⟫ := real_inner_comm _ _
  have c2 : ⟪y, b 1⟫ = ⟪b 1, y⟫ := real_inner_comm _ _
  have c3 : ⟪y, b 2⟫ = ⟪b 2, y⟫ := real_inner_comm _ _
  rw [c1, c2, c3] at P Py
  constructor
  · linear_combination -Py
  · linear_combination -P

/-- **Bachoc–Vallentin positivity for `S²`, `k ≤ 5`** — from the addition theorem, the
sum-of-squares structure, the relabelling, and the tangent frame. -/
theorem bv_positivity (k : Fin 6) {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3))
    (hx : OnSphere x) (w : Fin (9 - (k : ℕ)) → ℝ) :
    0 ≤ ∑ i, ∑ j, ∑ l, w ⬝ᵥ (S3 (k : ℕ) ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫).mulVec w := by
  have hsym : ∀ i j, ⟪x j, x i⟫ = ⟪x i, x j⟫ := fun i j => real_inner_comm _ _
  have e := sum_S3_eq_sum_Y3 (k : ℕ) (fun i j => ⟪x i, x j⟫) hsym w
  beta_reduce at e
  rw [e]
  refine Finset.sum_nonneg fun i _ => ?_
  obtain ⟨e₁, e₂, hfr⟩ := exists_tangent_frame (x i) (hx i)
  exact quad_Y3_nonneg (k : ℕ) (Nat.lt_succ_iff.mp k.isLt) (fun j => ⟪x i, x j⟫)
    (fun j l => ⟪x j, x l⟫) (fun j => ⟪e₁, x j⟫) (fun j => ⟪e₂, x j⟫)
    (fun j => (hfr (x j) (x j) (hx j) (hx j)).1)
    (fun j l => (hfr (x j) (x l) (hx j) (hx l)).2) w


end Thomson
