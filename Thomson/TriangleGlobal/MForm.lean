import Thomson.Certificate.Perturb

/-! # Task 5b, step 2: a compact evaluable form of `F`

`Fh H u v t = Σ_k Σ_{a,b} H_k[a,b] (B_kᵀ S_k(u,v,t) B_k)[a,b]` is a quadruple sum: evaluating it
at one point costs `Σ_k (9−k)⁴ ≈ 1.5·10⁴` multiplications, which no interval computation inside a
box covering can afford.  Two rewritings bring it down to `≈ 8·10²`, and — more importantly —
separate the parts that depend on `u*` from the parts that depend on the point:

* move the bases to the other side: with `M_k := B_k H_k B_kᵀ` (`Mmat`),
  `Fh H u v t = Σ_k Σ_{i,j} M_k[i,j] S_k(u,v,t)[i,j]` (`Fh_eq_Msum`).  The matrices `M_k` are
  *constants* — they carry every occurrence of `u*` — and are computed once and for all;
* expand the Bachoc–Vallentin symmetrisation: with `wpoly M x y := Σ_{i,j} M[i,j] xⁱ yʲ`,
  `Fh H u v t = (1/3) Σ_{three pairs} wpoly M_k · Q_k` (`Fh_eq_wsum`).  A `wpoly` is a bilinear
  form in the two monomial vectors, so one evaluation costs `2(9−k)²` operations and the whole of
  `F` costs `3 Σ_k 2(9−k)² ≈ 1.6·10³` — and the three pairs share their monomial powers.

Everything here is an identity: no data, no estimates. -/

namespace Thomson.Tri5b

open Thomson Finset Matrix

/-! ## The trace step -/

theorem sum_mul_eq_trace {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℝ) :
    ∑ i, ∑ j, X i j * Y i j = Matrix.trace (X * Yᵀ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]

/-- The constant matrices of the certificate: `M_k = B_k H_k B_kᵀ`. -/
noncomputable def Mmat (H : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ)
    (k : Fin 6) : Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ := B k * H k * (B k)ᵀ

/-- **The bases move to the other side.** -/
theorem Fh_eq_Msum (H : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ)
    (u v t : ℝ) :
    Fh H u v t = ∑ k : Fin 6, ∑ i, ∑ j, Mmat H k i j * S3 (k : ℕ) u v t i j := by
  rw [Fh_eq_trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum_mul_eq_trace]
  set S := S3 (k : ℕ) u v t
  have h1 : ((B k)ᵀ * S * B k)ᵀ = (B k)ᵀ * Sᵀ * B k := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [h1, Mmat]
  calc Matrix.trace (H k * ((B k)ᵀ * Sᵀ * B k))
      = Matrix.trace (H k * (B k)ᵀ * Sᵀ * B k) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (B k * (H k * (B k)ᵀ * Sᵀ)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (B k * H k * (B k)ᵀ * Sᵀ) := by simp only [Matrix.mul_assoc]

/-! ## The symmetrisation step -/

/-- `Q_k` is symmetric in its first two arguments. -/
theorem Q3_swap12 (k : ℕ) (u v t : ℝ) : Q3 k u v t = Q3 k v u t := by
  match k with
  | 0 => rfl
  | 1 | 2 | 3 | 4 | 5 => simp only [Q3]; ring
  | _ + 6 => rfl

/-- The bilinear form attached to a constant matrix: `w_M(x, y) = Σ_{i,j} M[i,j] xⁱ yʲ`. -/
noncomputable def wpoly {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x y : ℝ) : ℝ :=
  ∑ i, ∑ j, M i j * (x ^ (i : ℕ) * y ^ (j : ℕ))

theorem wpoly_add {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x y : ℝ) :
    wpoly M x y + wpoly M y x = ∑ i, ∑ j, M i j * (x ^ (i : ℕ) * y ^ (j : ℕ)
      + y ^ (i : ℕ) * x ^ (j : ℕ)) := by
  unfold wpoly
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- One block of `F`, in the three-pair form. -/
theorem Msum_eq_wsum {k : ℕ} (M : Matrix (Fin (9 - k)) (Fin (9 - k)) ℝ) (u v t : ℝ) :
    ∑ i, ∑ j, M i j * S3 k u v t i j
      = (1 / 6 : ℝ) * ((wpoly M u v + wpoly M v u) * Q3 k u v t
          + (wpoly M u t + wpoly M t u) * Q3 k u t v
          + (wpoly M v t + wpoly M t v) * Q3 k v t u) := by
  rw [wpoly_add, wpoly_add, wpoly_add]
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [S3, Y3, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, smul_eq_mul]
  rw [Q3_swap12 k v u t, Q3_swap12 k t u v, Q3_swap12 k t v u]
  ring

/-- **The evaluable form of `F`.**  `M_k` are the constants, the rest is the point. -/
theorem Fh_eq_wsum (H : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ)
    (u v t : ℝ) :
    Fh H u v t = (1 / 6 : ℝ) * ∑ k : Fin 6,
      ((wpoly (Mmat H k) u v + wpoly (Mmat H k) v u) * Q3 (k : ℕ) u v t
        + (wpoly (Mmat H k) u t + wpoly (Mmat H k) t u) * Q3 (k : ℕ) u t v
        + (wpoly (Mmat H k) v t + wpoly (Mmat H k) t v) * Q3 (k : ℕ) v t u) := by
  rw [Fh_eq_Msum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Msum_eq_wsum _ u v t

/-! ## Symmetry of the constant matrices

`Hfix` and `eH` are symmetric, hence so is every `Hp p`, hence `M_k` is symmetric and the two
`wpoly`s of each pair coincide: half the arithmetic, and half the data. -/

theorem Hfix_symm (k a b : ℕ) : Hfix k a b = Hfix k b a := by
  unfold Hfix
  split_ifs with h1 h2 h2
  · rw [le_antisymm h1 h2]
  · rfl
  · rfl
  · exfalso; omega

theorem eH_symm (j : Fin 24) (k a b : ℕ) : eH j k a b = eH j k b a := by
  unfold eH; exact if_congr or_comm rfl rfl

theorem Hp_symm (p : Fin 24 → ℝ) (k : Fin 6) : (Hp p k)ᵀ = Hp p k := by
  ext a b
  simp only [Matrix.transpose_apply, Hp, Matrix.of_apply]
  rw [Hfix_symm]
  exact congrArg _ (Finset.sum_congr rfl fun j _ => by rw [eH_symm])

theorem Mmat_symm (p : Fin 24 → ℝ) (k : Fin 6) : (Mmat (Hp p) k)ᵀ = Mmat (Hp p) k := by
  simp only [Mmat, Matrix.transpose_mul, Matrix.transpose_transpose, Hp_symm, Matrix.mul_assoc]

theorem wpoly_comm {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : Mᵀ = M) (x y : ℝ) :
    wpoly M x y = wpoly M y x := by
  unfold wpoly
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : M j i = M i j := by
    have := congrFun (congrFun hM i) j
    simpa [Matrix.transpose_apply] using this
  rw [h]; ring

/-- The form actually used by the box covering: one `wpoly` per pair. -/
theorem Fh_Hp_eq_wsum (p : Fin 24 → ℝ) (u v t : ℝ) :
    Fh (Hp p) u v t = (1 / 3 : ℝ) * ∑ k : Fin 6,
      (wpoly (Mmat (Hp p) k) u v * Q3 (k : ℕ) u v t
        + wpoly (Mmat (Hp p) k) u t * Q3 (k : ℕ) u t v
        + wpoly (Mmat (Hp p) k) v t * Q3 (k : ℕ) v t u) := by
  rw [Fh_eq_wsum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← wpoly_comm (Mmat_symm p k) u v, ← wpoly_comm (Mmat_symm p k) u t,
    ← wpoly_comm (Mmat_symm p k) v t]
  ring

end Thomson.Tri5b
