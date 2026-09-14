import Mathlib
import Thomson.ThreePoint.Certificate
import Thomson.Antiprism.Derivative

namespace Thomson
open Finset Matrix
open scoped RealInnerProductSpace

/-! # Toolkit for the Tasks: data-independent lemmas, all proved

Everything here is independent of the certificate data.  The Tasks in
`Thomson.Certificate.Assemble` are reduced to applying these to explicit objects. -/

/-! ### The algebraic constants: `u*`, `√2`, `r = √(1−u*)`, and the two cross chord lengths -/

/-- `r = √(1 − u*)`: half the diagonal of the antiprism squares is `r`, the square edge is `√2·r`. -/
noncomputable def rStar : ℝ := Real.sqrt (1 - uStar)
/-- The near cross chord `s₂ = √(2 + 2u* − √2(1−u*))`. -/
noncomputable def s2Star : ℝ := Real.sqrt (2 + 2 * uStar - Real.sqrt 2 * (1 - uStar))
/-- The far cross chord `s₄ = √(2 + 2u* + √2(1−u*))`. -/
noncomputable def s4Star : ℝ := Real.sqrt (2 + 2 * uStar + Real.sqrt 2 * (1 - uStar))

theorem rStar_sq : rStar ^ 2 = 1 - uStar := by
  obtain ⟨h1, h2⟩ := uStar_mem_Icc
  exact Real.sq_sqrt (by linarith)
theorem s2Star_sq : s2Star ^ 2 = 2 + 2 * uStar - Real.sqrt 2 * (1 - uStar) := by
  obtain ⟨h1, h2⟩ := uStar_mem_Icc; obtain ⟨w1, w2⟩ := sqrt2_bounds
  exact Real.sq_sqrt (by nlinarith)
theorem s4Star_sq : s4Star ^ 2 = 2 + 2 * uStar + Real.sqrt 2 * (1 - uStar) := by
  obtain ⟨h1, h2⟩ := uStar_mem_Icc; obtain ⟨w1, w2⟩ := sqrt2_bounds
  exact Real.sq_sqrt (by nlinarith)

/-- Rational enclosures of the constants, in the pattern of `sqrt2_bounds`. -/
theorem rStar_bounds : (8281 / 10000 : ℝ) < rStar ∧ rStar < 8283 / 10000 := by
  obtain ⟨h1, h2⟩ := uStar_mem_Icc
  constructor
  · rw [rStar, Real.lt_sqrt (by norm_num)]; nlinarith
  · rw [rStar, Real.sqrt_lt' (by norm_num)]; nlinarith
theorem s2Star_bounds : (12875 / 10000 : ℝ) < s2Star ∧ s2Star < 12879 / 10000 := by
  obtain ⟨h1, h2⟩ := uStar_mem_Icc; obtain ⟨w1, w2⟩ := sqrt2_bounds
  have hp1 : (0:ℝ) ≤ Real.sqrt 2 - 141421356 / 100000000 := by linarith
  have hp2 : (0:ℝ) ≤ 141421357 / 100000000 - Real.sqrt 2 := by linarith
  have hu1 : (0:ℝ) ≤ 1 - uStar - 6858 / 10000 := by linarith
  have hu2 : (0:ℝ) ≤ 686 / 1000 - (1 - uStar) := by linarith
  constructor
  · rw [s2Star, Real.lt_sqrt (by norm_num)]; nlinarith [mul_nonneg hp2 hu2, mul_nonneg hp1 hu1]
  · rw [s2Star, Real.sqrt_lt' (by norm_num)]; nlinarith [mul_nonneg hp1 hu2, mul_nonneg hp2 hu1]
theorem s4Star_bounds : (18967 / 10000 : ℝ) < s4Star ∧ s4Star < 18971 / 10000 := by
  obtain ⟨h1, h2⟩ := uStar_mem_Icc; obtain ⟨w1, w2⟩ := sqrt2_bounds
  have hp1 : (0:ℝ) ≤ Real.sqrt 2 - 141421356 / 100000000 := by linarith
  have hp2 : (0:ℝ) ≤ 141421357 / 100000000 - Real.sqrt 2 := by linarith
  have hu1 : (0:ℝ) ≤ 1 - uStar - 6858 / 10000 := by linarith
  have hu2 : (0:ℝ) ≤ 686 / 1000 - (1 - uStar) := by linarith
  constructor
  · rw [s4Star, Real.lt_sqrt (by norm_num)]; nlinarith [mul_nonneg hp1 hu1, mul_nonneg hp2 hu2]
  · rw [s4Star, Real.sqrt_lt' (by norm_num)]; nlinarith [mul_nonneg hp2 hu2, mul_nonneg hp1 hu1]
theorem rStar_pos : 0 < rStar := by linarith [rStar_bounds.1]
theorem s2Star_pos : 0 < s2Star := by linarith [s2Star_bounds.1]
theorem s4Star_pos : 0 < s4Star := by linarith [s4Star_bounds.1]

/-- `E(u*)` in terms of the constants: the target value of Task 3. -/
theorem antiprismEnergy_uStar_eq :
    antiprismEnergy uStar = (4 * Real.sqrt 2 + 2) / rStar + 8 / s2Star + 8 / s4Star := by
  unfold antiprismEnergy rStar s2Star s4Star
  have e1 : (2 - Real.sqrt 2) + (2 + Real.sqrt 2) * uStar = 2 + 2 * uStar - Real.sqrt 2 * (1 - uStar) := by ring
  have e2 : (2 + Real.sqrt 2) + (2 - Real.sqrt 2) * uStar = 2 + 2 * uStar + Real.sqrt 2 * (1 - uStar) := by ring
  rw [e1, e2]; simp only [div_eq_mul_inv]

/-- The four antiprism chord lengths and the antiprism inner products in terms of the constants. -/
theorem antiprism_chords :
    Real.sqrt (2 - 2 * uStar) = Real.sqrt 2 * rStar ∧ Real.sqrt (2 - 2 * (2 * uStar - 1)) = 2 * rStar := by
  obtain ⟨h1, h2⟩ := uStar_mem_Icc
  constructor
  · rw [show (2 - 2 * uStar : ℝ) = 2 * (1 - uStar) by ring, Real.sqrt_mul (by norm_num)]; rfl
  · rw [show (2 - 2 * (2 * uStar - 1) : ℝ) = 2 ^ 2 * (1 - uStar) by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]; rfl

/-! ### Structure of the three-point matrices on the diagonal patterns -/

theorem Q3_one_left (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 5) (t : ℝ) : Q3 k 1 t t = 0 := by
  interval_cases k <;> simp [Q3]
theorem Q3_one_mid (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 5) (t : ℝ) : Q3 k t 1 t = 0 := by
  interval_cases k <;> simp [Q3]
theorem Q3_one_right (k : ℕ) (hk : k ≤ 5) (t : ℝ) : Q3 k t t 1 = (1 - t ^ 2) ^ k := by
  interval_cases k <;> simp only [Q3] <;> ring

/-- `S3 k (1,t,t)` entrywise: `(1/3)(tⁱ⁺ʲ (1−t²)ᵏ + [k = 0](tⁱ + tʲ))`. -/
theorem S3_one_apply (k : ℕ) (hk : k ≤ 5) (t : ℝ) (i j : Fin (9 - k)) :
    S3 k 1 t t i j = (1 / 3 : ℝ) * (t ^ ((i : ℕ) + j) * (1 - t ^ 2) ^ k
      + if k = 0 then t ^ (i : ℕ) + t ^ (j : ℕ) else 0) := by
  simp only [S3, Y3, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, smul_eq_mul]
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0; simp only [Q3, if_true]; ring
  · rw [Q3_one_left k hpos hk, Q3_one_mid k hpos hk, Q3_one_right k hk, if_neg (by omega)]
    ring

/-- `S3 k (1,1,1) = 0` for `k ≥ 1`, and `= 1` (all entries) for `k = 0`. -/
theorem S3_all_one_apply (k : ℕ) (hk : k ≤ 5) (i j : Fin (9 - k)) :
    S3 k 1 1 1 i j = if k = 0 then 1 else 0 := by
  rw [S3_one_apply k hk]; rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0; simp; norm_num
  · simp [Nat.pos_iff_ne_zero.mp hpos, zero_pow (Nat.pos_iff_ne_zero.mp hpos)]

/-- `F(1,1,1)` involves only the `k = 0` block: `Σ_r D₀ᵣ (Σᵢ L₀ᵣᵢ)²`.  This is Task 3's left-hand
side. -/
theorem Fsum_all_one (L : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ)
    (D : (k : Fin 6) → Fin (9 - (k : ℕ)) → ℝ) :
    Fsum L D 1 1 1 = ∑ r, D 0 r * (∑ i, L 0 r i) ^ 2 := by
  unfold Fsum
  rw [Fin.sum_univ_succ]
  have hzero : ∀ k : Fin 5, ∑ r, D k.succ r * (L k.succ r ⬝ᵥ (S3 (k.succ : ℕ) 1 1 1).mulVec (L k.succ r)) = 0 := by
    intro k
    refine Finset.sum_eq_zero fun r _ => ?_
    have : (S3 ((k.succ : Fin 6) : ℕ) 1 1 1) = 0 := by
      ext i j; rw [S3_all_one_apply _ (by omega)]; simp [Fin.val_succ]
    rw [this]; simp
  rw [Finset.sum_eq_zero fun k _ => hzero k, add_zero]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  simp only [dotProduct, mulVec]
  have : ∀ i j : Fin 9, S3 ((0 : Fin 6) : ℕ) 1 1 1 i j = 1 := fun i j => by
    rw [S3_all_one_apply _ (by norm_num)]; simp
  simp only [this, mul_one, sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-! ### Positivity toolkit -/

/-- A polynomial with nonnegative Bernstein coefficients is nonnegative on `[a, b]`. -/
theorem bernstein_nonneg {n : ℕ} (c : Fin (n + 1) → ℝ) (hc : ∀ j, 0 ≤ c j) {a b s : ℝ}
    (ha : a ≤ s) (hb : s ≤ b) :
    0 ≤ ∑ j, c j * (s - a) ^ (j : ℕ) * (b - s) ^ (n - (j : ℕ)) :=
  Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (hc j) (pow_nonneg (by linarith) _)) (pow_nonneg (by linarith) _)

/-- Three-variable tensor Bernstein form: nonnegative coefficients give nonnegativity on a box. -/
theorem bernstein_nonneg_3d {n m l : ℕ} (c : Fin (n + 1) → Fin (m + 1) → Fin (l + 1) → ℝ)
    (hc : ∀ i j k, 0 ≤ c i j k) {a b a' b' a'' b'' p q r : ℝ}
    (hp : a ≤ p ∧ p ≤ b) (hq : a' ≤ q ∧ q ≤ b') (hr : a'' ≤ r ∧ r ≤ b'') :
    0 ≤ ∑ i, ∑ j, ∑ k, c i j k * ((p - a) ^ (i : ℕ) * (b - p) ^ (n - (i : ℕ)))
      * ((q - a') ^ (j : ℕ) * (b' - q) ^ (m - (j : ℕ)))
      * ((r - a'') ^ (k : ℕ) * (b'' - r) ^ (l - (k : ℕ))) := by
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_
  have h1 : 0 ≤ (p - a) ^ (i : ℕ) * (b - p) ^ (n - (i : ℕ)) :=
    mul_nonneg (pow_nonneg (by linarith [hp.1]) _) (pow_nonneg (by linarith [hp.2]) _)
  have h2 : 0 ≤ (q - a') ^ (j : ℕ) * (b' - q) ^ (m - (j : ℕ)) :=
    mul_nonneg (pow_nonneg (by linarith [hq.1]) _) (pow_nonneg (by linarith [hq.2]) _)
  have h3 : 0 ≤ (r - a'') ^ (k : ℕ) * (b'' - r) ^ (l - (k : ℕ)) :=
    mul_nonneg (pow_nonneg (by linarith [hr.1]) _) (pow_nonneg (by linarith [hr.2]) _)
  exact mul_nonneg (mul_nonneg (mul_nonneg (hc i j k) h1) h2) h3

/-- A function with four double zeros and a nonnegative cofactor is nonnegative. -/
theorem nonneg_of_four_double_zeros (P Q : ℝ → ℝ) (s₁ s₂ s₃ s₄ a b : ℝ)
    (hfac : ∀ s, P s = (s - s₁) ^ 2 * (s - s₂) ^ 2 * (s - s₃) ^ 2 * (s - s₄) ^ 2 * Q s)
    (hQ : ∀ s, a ≤ s → s ≤ b → 0 ≤ Q s) :
    ∀ s, a ≤ s → s ≤ b → 0 ≤ P s := by
  intro s ha hb; rw [hfac]; have := hQ s ha hb; positivity

/-- The S-procedure: `T = A + σ·G` with `A, σ, G ≥ 0` gives `T ≥ 0`. -/
theorem nonneg_of_s_procedure {T A σ G : ℝ} (h : T = A + σ * G) (hA : 0 ≤ A) (hσ : 0 ≤ σ)
    (hG : 0 ≤ G) : 0 ≤ T := by
  rw [h]; positivity

/-- **The local lemma.**  If near a point the function dominates `λ|δ|² − M(|δ₁|+|δ₂|+|δ₃|)³`
on the cube of radius `ρ`, and `9Mρ ≤ λ`, then it is nonnegative on that cube. -/
theorem local_nonneg_of_hessian {lam M ρ : ℝ} (hM : 0 ≤ M) (hρ : 0 ≤ ρ) (hlam : 9 * M * ρ ≤ lam)
    {v d₁ d₂ d₃ : ℝ} (h₁ : |d₁| ≤ ρ) (h₂ : |d₂| ≤ ρ) (h₃ : |d₃| ≤ ρ)
    (hv : lam * (d₁ ^ 2 + d₂ ^ 2 + d₃ ^ 2) - M * (|d₁| + |d₂| + |d₃|) ^ 3 ≤ v) : 0 ≤ v := by
  have a1 := abs_nonneg d₁; have a2 := abs_nonneg d₂; have a3 := abs_nonneg d₃
  have sq1 : |d₁| ^ 2 = d₁ ^ 2 := sq_abs d₁
  have sq2 : |d₂| ^ 2 = d₂ ^ 2 := sq_abs d₂
  have sq3 : |d₃| ^ 2 = d₃ ^ 2 := sq_abs d₃
  set S := |d₁| + |d₂| + |d₃| with hS
  have hS3 : S ≤ 3 * ρ := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hcs : S ^ 2 ≤ 3 * (d₁ ^ 2 + d₂ ^ 2 + d₃ ^ 2) := by
    rw [← sq1, ← sq2, ← sq3]; nlinarith [sq_nonneg (|d₁| - |d₂|), sq_nonneg (|d₂| - |d₃|), sq_nonneg (|d₁| - |d₃|)]
  have hcube : S ^ 3 ≤ 9 * ρ * (d₁ ^ 2 + d₂ ^ 2 + d₃ ^ 2) := by
    have : S ^ 3 = S * S ^ 2 := by ring
    rw [this]
    calc S * S ^ 2 ≤ (3 * ρ) * (3 * (d₁ ^ 2 + d₂ ^ 2 + d₃ ^ 2)) :=
          mul_le_mul hS3 hcs (by positivity) (by positivity)
      _ = 9 * ρ * (d₁ ^ 2 + d₂ ^ 2 + d₃ ^ 2) := by ring
  have hq : 0 ≤ d₁ ^ 2 + d₂ ^ 2 + d₃ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hcube hM, mul_le_mul_of_nonneg_right hlam hq]

end Thomson
