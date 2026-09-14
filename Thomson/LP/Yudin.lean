import Mathlib
import Thomson.Basic.ForceBalance

namespace Thomson
open Finset
open scoped RealInnerProductSpace

/-! ## 12. A rigorous lower bound: Yudin's linear-programming method -/

theorem gram_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ] (φ : κ → ι → ℝ) :
    0 ≤ ∑ i, ∑ j, ∑ m, φ m i * φ m j := by
  have : ∑ i, ∑ j, ∑ m, φ m i * φ m j = ∑ m, (∑ i, φ m i) ^ 2 :=
    calc ∑ i, ∑ j, ∑ m, φ m i * φ m j = ∑ i, ∑ m, ∑ j, φ m i * φ m j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ m, ∑ i, ∑ j, φ m i * φ m j := Finset.sum_comm
      _ = ∑ m, (∑ i, φ m i) ^ 2 := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [sq, Finset.sum_mul_sum]
  rw [this]; positivity

theorem inner_coords (x y : EuclideanSpace ℝ (Fin 3)) :
    ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

theorem normsq_coords (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1) :
    x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1 := by
  have := real_inner_self_eq_norm_sq x
  rw [hx, inner_coords] at this
  nlinarith [this]

theorem inner_eq_of_norm (x y : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫ = 1 - ‖x - y‖ ^ 2 / 2 := by
  have := norm_sub_sq_real x y
  rw [hx, hy] at this
  linarith

/-- Traceless symmetric 2-tensor: the real spherical harmonics of degree 2, unnormalised. -/
noncomputable def T2 (a b : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  x a * x b - (if a = b then 1 / 3 else 0)
/-- Traceless symmetric 3-tensor: the real spherical harmonics of degree 3, unnormalised. -/
noncomputable def T3 (a b c : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  x a * x b * x c - (1 / 5) * ((if a = b then x c else 0) + (if a = c then x b else 0)
    + (if b = c then x a else 0))

/-- Addition theorem for `P₂` on the unit sphere. -/
theorem P2_addition (x y : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (3 * ⟪x, y⟫ ^ 2 - 1) / 2 = (3 / 2) * ∑ p : Fin 3 × Fin 3, T2 p.1 p.2 x * T2 p.1 p.2 y := by
  have hx' := normsq_coords x hx; have hy' := normsq_coords y hy
  rw [inner_coords, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_three, T2]
  simp
  linear_combination (1/2) * hx' + (1/2) * hy'

/-- Addition theorem for `P₃` on the unit sphere. -/
theorem P3_addition (x y : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (5 * ⟪x, y⟫ ^ 3 - 3 * ⟪x, y⟫) / 2 =
      (5 / 2) * ∑ p : Fin 3 × Fin 3 × Fin 3, T3 p.1 p.2.1 p.2.2 x * T3 p.1 p.2.1 p.2.2 y := by
  have hx' := normsq_coords x hx; have hy' := normsq_coords y hy
  rw [inner_coords, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_three, Fintype.sum_prod_type, T3]
  simp
  linear_combination (3/2) * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2) * hx'
    + (3/2) * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2) * hy'

/-- Schoenberg positivity for `P₁, P₂, P₃` on `S²`: the Gram sums are nonnegative. -/
theorem sum_P1_nonneg {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) :
    0 ≤ ∑ i, ∑ j, ⟪x i, x j⟫ := by
  have h := gram_nonneg (fun (a : Fin 3) (i : Fin n) => x i a)
  simpa [inner_coords, Fin.sum_univ_three] using h

theorem sum_P2_nonneg {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) (hx : OnSphere x) :
    0 ≤ ∑ i, ∑ j, (3 * ⟪x i, x j⟫ ^ 2 - 1) / 2 := by
  have h := gram_nonneg (fun (p : Fin 3 × Fin 3) (i : Fin n) => T2 p.1 p.2 (x i))
  simp only [P2_addition _ _ (hx _) (hx _), ← Finset.mul_sum]
  positivity

theorem sum_P3_nonneg {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) (hx : OnSphere x) :
    0 ≤ ∑ i, ∑ j, (5 * ⟪x i, x j⟫ ^ 3 - 3 * ⟪x i, x j⟫) / 2 := by
  have h := gram_nonneg (fun (p : Fin 3 × Fin 3 × Fin 3) (i : Fin n) => T3 p.1 p.2.1 p.2.2 (x i))
  simp only [P3_addition _ _ (hx _) (hx _), ← Finset.mul_sum]
  positivity

/-- The degree-3 Yudin polynomial, with rational coefficients chosen so that
`1 - s·f(1 - s²/2)` has double zeros at `s = 93/50` and `s = 31/25`. -/
noncomputable def yudinF (t : ℝ) : ℝ :=
  168670775401 / 239625993870 + 8858474125 / 23962599387 * t
    + 6938750000 / 23962599387 * t ^ 2 + 3125000000 / 23962599387 * t ^ 3

/-- Legendre expansion of `yudinF`, with all coefficients positive. -/
theorem yudinF_legendre (t : ℝ) : yudinF t =
    575399826203 / 718877981610 + 10733474125 / 23962599387 * t
      + 13877500000 / 71887798161 * ((3 * t ^ 2 - 1) / 2)
      + 1250000000 / 23962599387 * ((5 * t ^ 3 - 3 * t) / 2) := by
  unfold yudinF; ring

/-- The key one-variable inequality `f(1 - s²/2) ≤ 1/s` for `s > 0`. -/
theorem yudinF_le_inv {s : ℝ} (hs : 0 < s) : yudinF (1 - s ^ 2 / 2) ≤ s⁻¹ := by
  have key : 1 - s * yudinF (1 - s ^ 2 / 2) = (s - 93 / 50) ^ 2 * (s - 31 / 25) ^ 2
      * (1562500 / 8311689 + 173593750 / 772987077 * s + 78125000 / 772987077 * s ^ 2
        + 390625000 / 23962599387 * s ^ 3) := by
    unfold yudinF; ring
  have hq : 0 ≤ (s - 93 / 50) ^ 2 * (s - 31 / 25) ^ 2
      * (1562500 / 8311689 + 173593750 / 772987077 * s + 78125000 / 772987077 * s ^ 2
        + 390625000 / 23962599387 * s ^ 3) := by positivity
  rw [← one_div, le_div_iff₀ hs]
  linarith

/-- **Yudin's bound, degree 3.**  Every admissible 8-point configuration has energy at least
`7059039119342 / 359438990805 = 19.63904…`. -/
theorem energy_ge_yudin (x : Fin 8 → EuclideanSpace ℝ (Fin 3)) (hx : Admissible x) :
    (7059039119342 / 359438990805 : ℝ) ≤ energy x := by
  obtain ⟨hsph, hinj⟩ := hx
  -- off-diagonal terms are dominated by the Coulomb terms
  have hterm : ∀ i j : Fin 8, i ≠ j → yudinF ⟪x i, x j⟫ ≤ ‖x i - x j‖⁻¹ := by
    intro i j hij
    have hne : x i - x j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hinj h))
    have hpos : 0 < ‖x i - x j‖ := norm_pos_iff.mpr hne
    rw [inner_eq_of_norm _ _ (hsph i) (hsph j)]
    exact yudinF_le_inv hpos
  have hdiag : ∀ i : Fin 8, yudinF ⟪x i, x i⟫ = yudinF 1 := by
    intro i; rw [real_inner_self_eq_norm_sq, hsph i]; norm_num
  -- the double sum splits into diagonal and off-diagonal parts
  have hsplit : ∑ i, ∑ j, yudinF ⟪x i, x j⟫
      = ∑ i, yudinF ⟪x i, x i⟫ + ∑ i, ∑ j ∈ univ.erase i, yudinF ⟪x i, x j⟫ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hoff : ∑ i, ∑ j ∈ univ.erase i, yudinF ⟪x i, x j⟫
      ≤ ∑ i, ∑ j ∈ univ.erase i, ‖x i - x j‖⁻¹ := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_
    exact hterm i j (Finset.ne_of_mem_erase hj).symm
  have hupper : ∑ i, ∑ j, yudinF ⟪x i, x j⟫ ≤ 8 * yudinF 1 + 2 * energy x := by
    rw [hsplit, energy_eq_half]
    simp only [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    linarith
  -- the Legendre expansion gives the lower bound `64 c₀`
  have hlower : (64 : ℝ) * (575399826203 / 718877981610) ≤ ∑ i, ∑ j, yudinF ⟪x i, x j⟫ := by
    simp only [yudinF_legendre, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h1 := sum_P1_nonneg x
    have h2 := sum_P2_nonneg x hsph
    have h3 := sum_P3_nonneg x hsph
    push_cast
    nlinarith [h1, h2, h3]
  have hf1 : yudinF 1 = 463 / 310 := by unfold yudinF; norm_num
  rw [hf1] at hupper
  linarith

/-- The infimum is at least `19.639`: a rigorous lower bound for the 8-point Thomson problem. -/
theorem thomsonInf_ge_yudin : (7059039119342 / 359438990805 : ℝ) ≤ thomsonInf 8 := by
  obtain ⟨x₀, hx₀⟩ := exists_admissible 8
  refine le_csInf ⟨_, x₀, hx₀, rfl⟩ ?_
  rintro e ⟨x, hx, rfl⟩
  exact energy_ge_yudin x hx

theorem thomsonInf_gt : (19.639 : ℝ) < thomsonInf 8 :=
  lt_of_lt_of_le (by norm_num) thomsonInf_ge_yudin

/-! ## 13. Higher-degree Schoenberg positivity, and an improved lower bound

The degree-3 bound of §12 is not the best the linear-programming method can do: the optimal
Yudin polynomial for `N = 8` also uses `P₄` and `P₇`.  Positivity of those two zonal kernels
is proved here the same way, but with the *harmonic* feature map (`2k+1` real solid harmonics)
instead of the full tensor: the identity to check is then homogeneous, needs no sphere
hypothesis, and is closed by `ring`. -/

/-- Summing a rank-one Gram kernel over all pairs gives a square. -/
theorem sum_gram_eq {n : ℕ} (c : ℝ) (f : Fin n → ℝ) :
    ∑ i, ∑ j, c * (f i * f j) = c * (∑ i, f i) ^ 2 := by
  have inner : ∀ i : Fin n, ∑ j, c * (f i * f j) = c * f i * ∑ j, f j := by
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => inner i, ← Finset.sum_mul,
    ← Finset.mul_sum, sq]
  ring

/-! ### Real solid harmonics of degree 4 -/

noncomputable def h4_0 (a b c : ℝ) : ℝ := 3*a^4 + 6*a^2*b^2 - 24*a^2*c^2 + 3*b^4 - 24*b^2*c^2 + 8*c^4
noncomputable def h4_1 (a b c : ℝ) : ℝ := 3*a^3*c + 3*a*b^2*c - 4*a*c^3
noncomputable def h4_2 (a b c : ℝ) : ℝ := 3*a^2*b*c + 3*b^3*c - 4*b*c^3
noncomputable def h4_3 (a b c : ℝ) : ℝ := a^4 - 6*a^2*c^2 - b^4 + 6*b^2*c^2
noncomputable def h4_4 (a b c : ℝ) : ℝ := a^3*b + a*b^3 - 6*a*b*c^2
noncomputable def h4_5 (a b c : ℝ) : ℝ := a^3*c - 3*a*b^2*c
noncomputable def h4_6 (a b c : ℝ) : ℝ := 3*a^2*b*c - b^3*c
noncomputable def h4_7 (a b c : ℝ) : ℝ := a^4 - 6*a^2*b^2 + b^4
noncomputable def h4_8 (a b c : ℝ) : ℝ := a^3*b - a*b^3

/-- The homogeneous zonal identity in degree 4: a polynomial identity on `ℝ³ × ℝ³` with no
sphere hypothesis, so `ring` closes it. -/
theorem zonal4_hom (a b c u v w : ℝ) :
    (3/8) * ((a ^ 2 + b ^ 2 + c ^ 2) * (u ^ 2 + v ^ 2 + w ^ 2)) ^ 2 + (-15/4) * (a * u + b * v + c * w) ^ 2 * ((a ^ 2 + b ^ 2 + c ^ 2) * (u ^ 2 + v ^ 2 + w ^ 2)) + (35/8) * (a * u + b * v + c * w) ^ 4
      = (1/64) * (h4_0 a b c * h4_0 u v w)
      + (5/8) * (h4_1 a b c * h4_1 u v w)
      + (5/8) * (h4_2 a b c * h4_2 u v w)
      + (5/16) * (h4_3 a b c * h4_3 u v w)
      + (5/4) * (h4_4 a b c * h4_4 u v w)
      + (35/8) * (h4_5 a b c * h4_5 u v w)
      + (35/8) * (h4_6 a b c * h4_6 u v w)
      + (35/64) * (h4_7 a b c * h4_7 u v w)
      + (35/4) * (h4_8 a b c * h4_8 u v w) := by
  unfold h4_0 h4_1 h4_2 h4_3 h4_4 h4_5 h4_6 h4_7 h4_8
  ring

/-- Addition theorem for `P4` on the unit sphere. -/
theorem P4_addition (x y : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (35 * ⟪x, y⟫ ^ 4 - 30 * ⟪x, y⟫ ^ 2 + 3) / 8
      = (1/64) * (h4_0 (x 0) (x 1) (x 2) * h4_0 (y 0) (y 1) (y 2))
      + (5/8) * (h4_1 (x 0) (x 1) (x 2) * h4_1 (y 0) (y 1) (y 2))
      + (5/8) * (h4_2 (x 0) (x 1) (x 2) * h4_2 (y 0) (y 1) (y 2))
      + (5/16) * (h4_3 (x 0) (x 1) (x 2) * h4_3 (y 0) (y 1) (y 2))
      + (5/4) * (h4_4 (x 0) (x 1) (x 2) * h4_4 (y 0) (y 1) (y 2))
      + (35/8) * (h4_5 (x 0) (x 1) (x 2) * h4_5 (y 0) (y 1) (y 2))
      + (35/8) * (h4_6 (x 0) (x 1) (x 2) * h4_6 (y 0) (y 1) (y 2))
      + (35/64) * (h4_7 (x 0) (x 1) (x 2) * h4_7 (y 0) (y 1) (y 2))
      + (35/4) * (h4_8 (x 0) (x 1) (x 2) * h4_8 (y 0) (y 1) (y 2)) := by
  have hx' := normsq_coords x hx
  have hy' := normsq_coords y hy
  have h := zonal4_hom (x 0) (x 1) (x 2) (y 0) (y 1) (y 2)
  rw [hx', hy'] at h
  rw [inner_coords]
  linear_combination h

/-- Schoenberg positivity in degree 4. -/
theorem sum_P4_nonneg {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) (hx : OnSphere x) :
    0 ≤ ∑ i, ∑ j, (35 * ⟪x i, x j⟫ ^ 4 - 30 * ⟪x i, x j⟫ ^ 2 + 3) / 8 := by
  have step : ∑ i, ∑ j, (35 * ⟪x i, x j⟫ ^ 4 - 30 * ⟪x i, x j⟫ ^ 2 + 3) / 8
      = ∑ i, ∑ j, ((1/64) * (h4_0 (x i 0) (x i 1) (x i 2) * h4_0 (x j 0) (x j 1) (x j 2))
        + (5/8) * (h4_1 (x i 0) (x i 1) (x i 2) * h4_1 (x j 0) (x j 1) (x j 2))
        + (5/8) * (h4_2 (x i 0) (x i 1) (x i 2) * h4_2 (x j 0) (x j 1) (x j 2))
        + (5/16) * (h4_3 (x i 0) (x i 1) (x i 2) * h4_3 (x j 0) (x j 1) (x j 2))
        + (5/4) * (h4_4 (x i 0) (x i 1) (x i 2) * h4_4 (x j 0) (x j 1) (x j 2))
        + (35/8) * (h4_5 (x i 0) (x i 1) (x i 2) * h4_5 (x j 0) (x j 1) (x j 2))
        + (35/8) * (h4_6 (x i 0) (x i 1) (x i 2) * h4_6 (x j 0) (x j 1) (x j 2))
        + (35/64) * (h4_7 (x i 0) (x i 1) (x i 2) * h4_7 (x j 0) (x j 1) (x j 2))
        + (35/4) * (h4_8 (x i 0) (x i 1) (x i 2) * h4_8 (x j 0) (x j 1) (x j 2))) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      P4_addition (x i) (x j) (hx i) (hx j)
  rw [step]
  simp only [Finset.sum_add_distrib, sum_gram_eq]
  positivity

/-! ### Real solid harmonics of degree 7 -/

noncomputable def h7_0 (a b c : ℝ) : ℝ := 35*a^6*c + 105*a^4*b^2*c - 210*a^4*c^3 + 105*a^2*b^4*c - 420*a^2*b^2*c^3 + 168*a^2*c^5 + 35*b^6*c - 210*b^4*c^3 + 168*b^2*c^5 - 16*c^7
noncomputable def h7_1 (a b c : ℝ) : ℝ := 5*a^7 + 15*a^5*b^2 - 120*a^5*c^2 + 15*a^3*b^4 - 240*a^3*b^2*c^2 + 240*a^3*c^4 + 5*a*b^6 - 120*a*b^4*c^2 + 240*a*b^2*c^4 - 64*a*c^6
noncomputable def h7_2 (a b c : ℝ) : ℝ := 5*a^6*b + 15*a^4*b^3 - 120*a^4*b*c^2 + 15*a^2*b^5 - 240*a^2*b^3*c^2 + 240*a^2*b*c^4 + 5*b^7 - 120*b^5*c^2 + 240*b^3*c^4 - 64*b*c^6
noncomputable def h7_3 (a b c : ℝ) : ℝ := 15*a^6*c + 15*a^4*b^2*c - 80*a^4*c^3 - 15*a^2*b^4*c + 48*a^2*c^5 - 15*b^6*c + 80*b^4*c^3 - 48*b^2*c^5
noncomputable def h7_4 (a b c : ℝ) : ℝ := 15*a^5*b*c + 30*a^3*b^3*c - 80*a^3*b*c^3 + 15*a*b^5*c - 80*a*b^3*c^3 + 48*a*b*c^5
noncomputable def h7_5 (a b c : ℝ) : ℝ := 3*a^7 - 3*a^5*b^2 - 60*a^5*c^2 - 15*a^3*b^4 + 120*a^3*b^2*c^2 + 80*a^3*c^4 - 9*a*b^6 + 180*a*b^4*c^2 - 240*a*b^2*c^4
noncomputable def h7_6 (a b c : ℝ) : ℝ := 9*a^6*b + 15*a^4*b^3 - 180*a^4*b*c^2 + 3*a^2*b^5 - 120*a^2*b^3*c^2 + 240*a^2*b*c^4 - 3*b^7 + 60*b^5*c^2 - 80*b^3*c^4
noncomputable def h7_7 (a b c : ℝ) : ℝ := 3*a^6*c - 15*a^4*b^2*c - 10*a^4*c^3 - 15*a^2*b^4*c + 60*a^2*b^2*c^3 + 3*b^6*c - 10*b^4*c^3
noncomputable def h7_8 (a b c : ℝ) : ℝ := 3*a^5*b*c - 10*a^3*b*c^3 - 3*a*b^5*c + 10*a*b^3*c^3
noncomputable def h7_9 (a b c : ℝ) : ℝ := a^7 - 9*a^5*b^2 - 12*a^5*c^2 - 5*a^3*b^4 + 120*a^3*b^2*c^2 + 5*a*b^6 - 60*a*b^4*c^2
noncomputable def h7_10 (a b c : ℝ) : ℝ := 5*a^6*b - 5*a^4*b^3 - 60*a^4*b*c^2 - 9*a^2*b^5 + 120*a^2*b^3*c^2 + b^7 - 12*b^5*c^2
noncomputable def h7_11 (a b c : ℝ) : ℝ := a^6*c - 15*a^4*b^2*c + 15*a^2*b^4*c - b^6*c
noncomputable def h7_12 (a b c : ℝ) : ℝ := 3*a^5*b*c - 10*a^3*b^3*c + 3*a*b^5*c
noncomputable def h7_13 (a b c : ℝ) : ℝ := a^7 - 21*a^5*b^2 + 35*a^3*b^4 - 7*a*b^6
noncomputable def h7_14 (a b c : ℝ) : ℝ := 7*a^6*b - 35*a^4*b^3 + 21*a^2*b^5 - b^7

/-- The homogeneous zonal identity in degree 7: a polynomial identity on `ℝ³ × ℝ³` with no
sphere hypothesis, so `ring` closes it. -/
theorem zonal7_hom (a b c u v w : ℝ) :
    (-35/16) * (a * u + b * v + c * w) ^ 1 * ((a ^ 2 + b ^ 2 + c ^ 2) * (u ^ 2 + v ^ 2 + w ^ 2)) ^ 3 + (315/16) * (a * u + b * v + c * w) ^ 3 * ((a ^ 2 + b ^ 2 + c ^ 2) * (u ^ 2 + v ^ 2 + w ^ 2)) ^ 2 + (-693/16) * (a * u + b * v + c * w) ^ 5 * ((a ^ 2 + b ^ 2 + c ^ 2) * (u ^ 2 + v ^ 2 + w ^ 2)) + (429/16) * (a * u + b * v + c * w) ^ 7
      = (1/256) * (h7_0 a b c * h7_0 u v w)
      + (7/1024) * (h7_1 a b c * h7_1 u v w)
      + (7/1024) * (h7_2 a b c * h7_2 u v w)
      + (21/512) * (h7_3 a b c * h7_3 u v w)
      + (21/128) * (h7_4 a b c * h7_4 u v w)
      + (21/1024) * (h7_5 a b c * h7_5 u v w)
      + (21/1024) * (h7_6 a b c * h7_6 u v w)
      + (231/256) * (h7_7 a b c * h7_7 u v w)
      + (231/16) * (h7_8 a b c * h7_8 u v w)
      + (231/1024) * (h7_9 a b c * h7_9 u v w)
      + (231/1024) * (h7_10 a b c * h7_10 u v w)
      + (3003/512) * (h7_11 a b c * h7_11 u v w)
      + (3003/128) * (h7_12 a b c * h7_12 u v w)
      + (429/1024) * (h7_13 a b c * h7_13 u v w)
      + (429/1024) * (h7_14 a b c * h7_14 u v w) := by
  unfold h7_0 h7_1 h7_2 h7_3 h7_4 h7_5 h7_6 h7_7 h7_8 h7_9 h7_10 h7_11 h7_12 h7_13 h7_14
  ring

/-- Addition theorem for `P7` on the unit sphere. -/
theorem P7_addition (x y : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (429 * ⟪x, y⟫ ^ 7 - 693 * ⟪x, y⟫ ^ 5 + 315 * ⟪x, y⟫ ^ 3 - 35 * ⟪x, y⟫) / 16
      = (1/256) * (h7_0 (x 0) (x 1) (x 2) * h7_0 (y 0) (y 1) (y 2))
      + (7/1024) * (h7_1 (x 0) (x 1) (x 2) * h7_1 (y 0) (y 1) (y 2))
      + (7/1024) * (h7_2 (x 0) (x 1) (x 2) * h7_2 (y 0) (y 1) (y 2))
      + (21/512) * (h7_3 (x 0) (x 1) (x 2) * h7_3 (y 0) (y 1) (y 2))
      + (21/128) * (h7_4 (x 0) (x 1) (x 2) * h7_4 (y 0) (y 1) (y 2))
      + (21/1024) * (h7_5 (x 0) (x 1) (x 2) * h7_5 (y 0) (y 1) (y 2))
      + (21/1024) * (h7_6 (x 0) (x 1) (x 2) * h7_6 (y 0) (y 1) (y 2))
      + (231/256) * (h7_7 (x 0) (x 1) (x 2) * h7_7 (y 0) (y 1) (y 2))
      + (231/16) * (h7_8 (x 0) (x 1) (x 2) * h7_8 (y 0) (y 1) (y 2))
      + (231/1024) * (h7_9 (x 0) (x 1) (x 2) * h7_9 (y 0) (y 1) (y 2))
      + (231/1024) * (h7_10 (x 0) (x 1) (x 2) * h7_10 (y 0) (y 1) (y 2))
      + (3003/512) * (h7_11 (x 0) (x 1) (x 2) * h7_11 (y 0) (y 1) (y 2))
      + (3003/128) * (h7_12 (x 0) (x 1) (x 2) * h7_12 (y 0) (y 1) (y 2))
      + (429/1024) * (h7_13 (x 0) (x 1) (x 2) * h7_13 (y 0) (y 1) (y 2))
      + (429/1024) * (h7_14 (x 0) (x 1) (x 2) * h7_14 (y 0) (y 1) (y 2)) := by
  have hx' := normsq_coords x hx
  have hy' := normsq_coords y hy
  have h := zonal7_hom (x 0) (x 1) (x 2) (y 0) (y 1) (y 2)
  rw [hx', hy'] at h
  rw [inner_coords]
  linear_combination h

/-- Schoenberg positivity in degree 7. -/
theorem sum_P7_nonneg {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) (hx : OnSphere x) :
    0 ≤ ∑ i, ∑ j, (429 * ⟪x i, x j⟫ ^ 7 - 693 * ⟪x i, x j⟫ ^ 5 + 315 * ⟪x i, x j⟫ ^ 3 - 35 * ⟪x i, x j⟫) / 16 := by
  have step : ∑ i, ∑ j, (429 * ⟪x i, x j⟫ ^ 7 - 693 * ⟪x i, x j⟫ ^ 5 + 315 * ⟪x i, x j⟫ ^ 3 - 35 * ⟪x i, x j⟫) / 16
      = ∑ i, ∑ j, ((1/256) * (h7_0 (x i 0) (x i 1) (x i 2) * h7_0 (x j 0) (x j 1) (x j 2))
        + (7/1024) * (h7_1 (x i 0) (x i 1) (x i 2) * h7_1 (x j 0) (x j 1) (x j 2))
        + (7/1024) * (h7_2 (x i 0) (x i 1) (x i 2) * h7_2 (x j 0) (x j 1) (x j 2))
        + (21/512) * (h7_3 (x i 0) (x i 1) (x i 2) * h7_3 (x j 0) (x j 1) (x j 2))
        + (21/128) * (h7_4 (x i 0) (x i 1) (x i 2) * h7_4 (x j 0) (x j 1) (x j 2))
        + (21/1024) * (h7_5 (x i 0) (x i 1) (x i 2) * h7_5 (x j 0) (x j 1) (x j 2))
        + (21/1024) * (h7_6 (x i 0) (x i 1) (x i 2) * h7_6 (x j 0) (x j 1) (x j 2))
        + (231/256) * (h7_7 (x i 0) (x i 1) (x i 2) * h7_7 (x j 0) (x j 1) (x j 2))
        + (231/16) * (h7_8 (x i 0) (x i 1) (x i 2) * h7_8 (x j 0) (x j 1) (x j 2))
        + (231/1024) * (h7_9 (x i 0) (x i 1) (x i 2) * h7_9 (x j 0) (x j 1) (x j 2))
        + (231/1024) * (h7_10 (x i 0) (x i 1) (x i 2) * h7_10 (x j 0) (x j 1) (x j 2))
        + (3003/512) * (h7_11 (x i 0) (x i 1) (x i 2) * h7_11 (x j 0) (x j 1) (x j 2))
        + (3003/128) * (h7_12 (x i 0) (x i 1) (x i 2) * h7_12 (x j 0) (x j 1) (x j 2))
        + (429/1024) * (h7_13 (x i 0) (x i 1) (x i 2) * h7_13 (x j 0) (x j 1) (x j 2))
        + (429/1024) * (h7_14 (x i 0) (x i 1) (x i 2) * h7_14 (x j 0) (x j 1) (x j 2))) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      P7_addition (x i) (x j) (hx i) (hx j)
  rw [step]
  simp only [Finset.sum_add_distrib, sum_gram_eq]
  positivity

/-! ### The degree-7 Yudin polynomial

Touching distances `49/40`, `8/5`, `47/25` (rational stand-ins for the true contact points
`1.2335…`, `1.6128…`, `1.8710…`), imposed as exact double zeros of the slack. -/

noncomputable def yudinF7 (t : ℝ) : ℝ :=
  (676113793281934502048940645604961225/957432771398587384241118321039853056) + (332875947100292256975895387654204230625/944986145370405748245983782866334966272) * t ^ 1 + (3790767407945690693738291645363757940625/12954185076119312132205361023459341829312) * t ^ 2 + (48985300088925628109141585916316319140625/181358591065670369850875054328430785610368) * t ^ 3 + (18520941844947477382393985389648437500/29754143846711545053659188600758175764201) * t ^ 4 + (-381631562416090375000000000000000000000/1416863992700549764459961361940865512581) * t ^ 5 + (4961210311409174875000000000000000000000/29754143846711545053659188600758175764201) * t ^ 7

/-- Legendre expansion of `yudinF7`: the coefficients of `P₀,…,P₄` and `P₇` are all `≥ 0`. -/
theorem yudinF7_legendre (t : ℝ) : yudinF7 t =
    (1360645848206469402418048553218078275793675/1692680183279590118608167173732020665696768) * (1) + (2967131680522636226603919489095329522825625/6528909278364133314631501955823508281973248) * (t) + (144733766831280576117464496054404885959375/740547580184820676891073138507759041242336) * ((3 * t ^ 2 - 1) / 2) + (19639606735458937946703829671965300703125/332490750287062344726604266268789773619008) * ((5 * t ^ 3 - 3 * t) / 2) + (29633506951915963811830376623437500000/208279006926980815375614320205307230349407) * ((35 * t ^ 4 - 30 * t ^ 2 + 3) / 8) + (6106104998657446000000000000000000000000/981886746941480986770753223825019800218633) * ((429 * t ^ 7 - 693 * t ^ 5 + 315 * t ^ 3 - 35 * t) / 16) := by
  unfold yudinF7; ring

/-- `f(1 - s²/2) ≤ 1/s`: the slack factors as three exact double zeros times a cubic-and-higher
polynomial with positive coefficients. -/
theorem yudinF7_le_inv {s : ℝ} (hs : 0 < s) : yudinF7 (1 - s ^ 2 / 2) ≤ s⁻¹ := by
  have key : 1 - s * yudinF7 (1 - s ^ 2 / 2)
      = (s - 49/40) ^ 2 * (s - 8/5) ^ 2 * (s - 47/25) ^ 2
        * ((390625/5303809) + (85106932845794606364928161316740892578125/476066301547384720858547017612130812227216) * s ^ 1 + (54906117394575251599969302569430810546875/238033150773692360429273508806065406113608) * s ^ 2 + (11989245465455422521531742958587158203125/52896255727487191206505224179125645803024) * s ^ 3 + (876557414679120971144378210882568359375/4250591978101649293379884085822596537743) * s ^ 4 + (734964063639931015916309768676757812500/4250591978101649293379884085822596537743) * s ^ 5 + (3371610640205401347383417480468750000000/29754143846711545053659188600758175764201) * s ^ 6 + (3469940258819581099096679687500000000/70340765595062754263969713004156443887) * s ^ 7 + (364726476799690121669921875000000000000/29754143846711545053659188600758175764201) * s ^ 8 + (38759455557884178710937500000000000000/29754143846711545053659188600758175764201) * s ^ 9) := by
    unfold yudinF7; ring
  have hq : 0 ≤ (s - 49/40) ^ 2 * (s - 8/5) ^ 2 * (s - 47/25) ^ 2
        * ((390625/5303809) + (85106932845794606364928161316740892578125/476066301547384720858547017612130812227216) * s ^ 1 + (54906117394575251599969302569430810546875/238033150773692360429273508806065406113608) * s ^ 2 + (11989245465455422521531742958587158203125/52896255727487191206505224179125645803024) * s ^ 3 + (876557414679120971144378210882568359375/4250591978101649293379884085822596537743) * s ^ 4 + (734964063639931015916309768676757812500/4250591978101649293379884085822596537743) * s ^ 5 + (3371610640205401347383417480468750000000/29754143846711545053659188600758175764201) * s ^ 6 + (3469940258819581099096679687500000000/70340765595062754263969713004156443887) * s ^ 7 + (364726476799690121669921875000000000000/29754143846711545053659188600758175764201) * s ^ 8 + (38759455557884178710937500000000000000/29754143846711545053659188600758175764201) * s ^ 9) := by positivity
  rw [← one_div, le_div_iff₀ hs]
  linarith

/-- **Yudin's bound, degree 7.**  Every admissible 8-point configuration has energy at least
`19.6462249`. -/
theorem energy_ge_yudin7 (x : Fin 8 → EuclideanSpace ℝ (Fin 3)) (hx : Admissible x) :
    (9352905642547650287729263358126768492479175/476066301547384720858547017612130812227216 : ℝ) ≤ energy x := by
  obtain ⟨hsph, hinj⟩ := hx
  have hterm : ∀ i j : Fin 8, i ≠ j → yudinF7 ⟪x i, x j⟫ ≤ ‖x i - x j‖⁻¹ := by
    intro i j hij
    have hne : x i - x j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hinj h))
    have hpos : 0 < ‖x i - x j‖ := norm_pos_iff.mpr hne
    rw [inner_eq_of_norm _ _ (hsph i) (hsph j)]
    exact yudinF7_le_inv hpos
  have hdiag : ∀ i : Fin 8, yudinF7 ⟪x i, x i⟫ = yudinF7 1 := by
    intro i; rw [real_inner_self_eq_norm_sq, hsph i]; norm_num
  have hsplit : ∑ i, ∑ j, yudinF7 ⟪x i, x j⟫
      = ∑ i, yudinF7 ⟪x i, x i⟫ + ∑ i, ∑ j ∈ univ.erase i, yudinF7 ⟪x i, x j⟫ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hoff : ∑ i, ∑ j ∈ univ.erase i, yudinF7 ⟪x i, x j⟫
      ≤ ∑ i, ∑ j ∈ univ.erase i, ‖x i - x j‖⁻¹ :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj =>
      hterm i j (Finset.ne_of_mem_erase hj).symm
  have hupper : ∑ i, ∑ j, yudinF7 ⟪x i, x j⟫ ≤ 8 * yudinF7 1 + 2 * energy x := by
    rw [hsplit, energy_eq_half]
    simp only [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    linarith
  have hlower : (64 : ℝ) * (1360645848206469402418048553218078275793675/1692680183279590118608167173732020665696768) ≤ ∑ i, ∑ j, yudinF7 ⟪x i, x j⟫ := by
    simp only [yudinF7_legendre, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h1 := sum_P1_nonneg x
    have h2 := sum_P2_nonneg x hsph
    have h3 := sum_P3_nonneg x hsph
    have h4 := sum_P4_nonneg x hsph
    have h7 := sum_P7_nonneg x hsph
    push_cast
    linarith
  have hf1 : yudinF7 1 = 136359877934451180935869561895796775/89759322318617567272604842597486224 := by unfold yudinF7; norm_num
  rw [hf1] at hupper
  linarith

/-- The improved rigorous lower bound: `19.6462 < thomsonInf 8`. -/
theorem thomsonInf_ge_yudin7 : (9352905642547650287729263358126768492479175/476066301547384720858547017612130812227216 : ℝ) ≤ thomsonInf 8 := by
  obtain ⟨x₀, hx₀⟩ := exists_admissible 8
  refine le_csInf ⟨_, x₀, hx₀, rfl⟩ ?_
  rintro e ⟨x, hx, rfl⟩
  exact energy_ge_yudin7 x hx

theorem thomsonInf_gt' : (19.6462 : ℝ) < thomsonInf 8 :=
  lt_of_lt_of_le (by norm_num) thomsonInf_ge_yudin7

/-! ### Degree 12: the linear-programming method at its ceiling

The optimal Yudin polynomial for `N = 8` is supported on `P₀,P₁,P₂,P₃,P₇,P₁₂` and gives
`19.6478`; this section proves `19.6475`, within `0.0003` of the method's exact optimum.  Two
things change from §13.  Positivity now needs `P₁₂`, whose `25` harmonics make the `ring`
identity large but still routine.  And the slack polynomial, after its three double zeros are
removed, no longer has positive coefficients: it is positive on the range of possible
distances but not beyond it.  It is therefore certified in the **Bernstein basis** of `[0,2]`,
which is exactly the interval of chord lengths on the unit sphere. -/

noncomputable def h12_0 (a b c : ℝ) : ℝ := 231*a^12 + 1386*a^10*b^2 - 16632*a^10*c^2 + 3465*a^8*b^4 - 83160*a^8*b^2*c^2 + 138600*a^8*c^4 + 4620*a^6*b^6 - 166320*a^6*b^4*c^2 + 554400*a^6*b^2*c^4 - 295680*a^6*c^6 + 3465*a^4*b^8 - 166320*a^4*b^6*c^2 + 831600*a^4*b^4*c^4 - 887040*a^4*b^2*c^6 + 190080*a^4*c^8 + 1386*a^2*b^10 - 83160*a^2*b^8*c^2 + 554400*a^2*b^6*c^4 - 887040*a^2*b^4*c^6 + 380160*a^2*b^2*c^8 - 33792*a^2*c^10 + 231*b^12 - 16632*b^10*c^2 + 138600*b^8*c^4 - 295680*b^6*c^6 + 190080*b^4*c^8 - 33792*b^2*c^10 + 1024*c^12
noncomputable def h12_1 (a b c : ℝ) : ℝ := 231*a^11*c + 1155*a^9*b^2*c - 4620*a^9*c^3 + 2310*a^7*b^4*c - 18480*a^7*b^2*c^3 + 18480*a^7*c^5 + 2310*a^5*b^6*c - 27720*a^5*b^4*c^3 + 55440*a^5*b^2*c^5 - 21120*a^5*c^7 + 1155*a^3*b^8*c - 18480*a^3*b^6*c^3 + 55440*a^3*b^4*c^5 - 42240*a^3*b^2*c^7 + 7040*a^3*c^9 + 231*a*b^10*c - 4620*a*b^8*c^3 + 18480*a*b^6*c^5 - 21120*a*b^4*c^7 + 7040*a*b^2*c^9 - 512*a*c^11
noncomputable def h12_2 (a b c : ℝ) : ℝ := 231*a^10*b*c + 1155*a^8*b^3*c - 4620*a^8*b*c^3 + 2310*a^6*b^5*c - 18480*a^6*b^3*c^3 + 18480*a^6*b*c^5 + 2310*a^4*b^7*c - 27720*a^4*b^5*c^3 + 55440*a^4*b^3*c^5 - 21120*a^4*b*c^7 + 1155*a^2*b^9*c - 18480*a^2*b^7*c^3 + 55440*a^2*b^5*c^5 - 42240*a^2*b^3*c^7 + 7040*a^2*b*c^9 + 231*b^11*c - 4620*b^9*c^3 + 18480*b^7*c^5 - 21120*b^5*c^7 + 7040*b^3*c^9 - 512*b*c^11
noncomputable def h12_3 (a b c : ℝ) : ℝ := 3*a^12 + 12*a^10*b^2 - 210*a^10*c^2 + 15*a^8*b^4 - 630*a^8*b^2*c^2 + 1680*a^8*c^4 - 420*a^6*b^4*c^2 + 3360*a^6*b^2*c^4 - 3360*a^6*c^6 - 15*a^4*b^8 + 420*a^4*b^6*c^2 - 3360*a^4*b^2*c^6 + 1920*a^4*c^8 - 12*a^2*b^10 + 630*a^2*b^8*c^2 - 3360*a^2*b^6*c^4 + 3360*a^2*b^4*c^6 - 256*a^2*c^10 - 3*b^12 + 210*b^10*c^2 - 1680*b^8*c^4 + 3360*b^6*c^6 - 1920*b^4*c^8 + 256*b^2*c^10
noncomputable def h12_4 (a b c : ℝ) : ℝ := 3*a^11*b + 15*a^9*b^3 - 210*a^9*b*c^2 + 30*a^7*b^5 - 840*a^7*b^3*c^2 + 1680*a^7*b*c^4 + 30*a^5*b^7 - 1260*a^5*b^5*c^2 + 5040*a^5*b^3*c^4 - 3360*a^5*b*c^6 + 15*a^3*b^9 - 840*a^3*b^7*c^2 + 5040*a^3*b^5*c^4 - 6720*a^3*b^3*c^6 + 1920*a^3*b*c^8 + 3*a*b^11 - 210*a*b^9*c^2 + 1680*a*b^7*c^4 - 3360*a*b^5*c^6 + 1920*a*b^3*c^8 - 256*a*b*c^10
noncomputable def h12_5 (a b c : ℝ) : ℝ := 45*a^11*c + 45*a^9*b^2*c - 840*a^9*c^3 - 270*a^7*b^4*c + 3024*a^7*c^5 - 630*a^5*b^6*c + 5040*a^5*b^4*c^3 - 3024*a^5*b^2*c^5 - 2880*a^5*c^7 - 495*a^3*b^8*c + 6720*a^3*b^6*c^3 - 15120*a^3*b^4*c^5 + 5760*a^3*b^2*c^7 + 640*a^3*c^9 - 135*a*b^10*c + 2520*a*b^8*c^3 - 9072*a*b^6*c^5 + 8640*a*b^4*c^7 - 1920*a*b^2*c^9
noncomputable def h12_6 (a b c : ℝ) : ℝ := 135*a^10*b*c + 495*a^8*b^3*c - 2520*a^8*b*c^3 + 630*a^6*b^5*c - 6720*a^6*b^3*c^3 + 9072*a^6*b*c^5 + 270*a^4*b^7*c - 5040*a^4*b^5*c^3 + 15120*a^4*b^3*c^5 - 8640*a^4*b*c^7 - 45*a^2*b^9*c + 3024*a^2*b^5*c^5 - 5760*a^2*b^3*c^7 + 1920*a^2*b*c^9 - 45*b^11*c + 840*b^9*c^3 - 3024*b^7*c^5 + 2880*b^5*c^7 - 640*b^3*c^9
noncomputable def h12_7 (a b c : ℝ) : ℝ := 5*a^12 - 10*a^10*b^2 - 320*a^10*c^2 - 85*a^8*b^4 + 960*a^8*b^2*c^2 + 2240*a^8*c^4 - 140*a^6*b^6 + 4480*a^6*b^4*c^2 - 8960*a^6*b^2*c^4 - 3584*a^6*c^6 - 85*a^4*b^8 + 4480*a^4*b^6*c^2 - 22400*a^4*b^4*c^4 + 17920*a^4*b^2*c^6 + 1280*a^4*c^8 - 10*a^2*b^10 + 960*a^2*b^8*c^2 - 8960*a^2*b^6*c^4 + 17920*a^2*b^4*c^6 - 7680*a^2*b^2*c^8 + 5*b^12 - 320*b^10*c^2 + 2240*b^8*c^4 - 3584*b^6*c^6 + 1280*b^4*c^8
noncomputable def h12_8 (a b c : ℝ) : ℝ := 5*a^11*b + 15*a^9*b^3 - 320*a^9*b*c^2 + 10*a^7*b^5 - 640*a^7*b^3*c^2 + 2240*a^7*b*c^4 - 10*a^5*b^7 + 2240*a^5*b^3*c^4 - 3584*a^5*b*c^6 - 15*a^3*b^9 + 640*a^3*b^7*c^2 - 2240*a^3*b^5*c^4 + 1280*a^3*b*c^8 - 5*a*b^11 + 320*a*b^9*c^2 - 2240*a*b^7*c^4 + 3584*a*b^5*c^6 - 1280*a*b^3*c^8
noncomputable def h12_9 (a b c : ℝ) : ℝ := 5*a^11*c - 35*a^9*b^2*c - 80*a^9*c^3 - 110*a^7*b^4*c + 640*a^7*b^2*c^3 + 224*a^7*c^5 - 70*a^5*b^6*c + 1120*a^5*b^4*c^3 - 2016*a^5*b^2*c^5 - 128*a^5*c^7 + 25*a^3*b^8*c - 1120*a^3*b^4*c^5 + 1280*a^3*b^2*c^7 + 25*a*b^10*c - 400*a*b^8*c^3 + 1120*a*b^6*c^5 - 640*a*b^4*c^7
noncomputable def h12_10 (a b c : ℝ) : ℝ := 25*a^10*b*c + 25*a^8*b^3*c - 400*a^8*b*c^3 - 70*a^6*b^5*c + 1120*a^6*b*c^5 - 110*a^4*b^7*c + 1120*a^4*b^5*c^3 - 1120*a^4*b^3*c^5 - 640*a^4*b*c^7 - 35*a^2*b^9*c + 640*a^2*b^7*c^3 - 2016*a^2*b^5*c^5 + 1280*a^2*b^3*c^7 + 5*b^11*c - 80*b^9*c^3 + 224*b^7*c^5 - 128*b^5*c^7
noncomputable def h12_11 (a b c : ℝ) : ℝ := 5*a^12 - 60*a^10*b^2 - 270*a^10*c^2 - 135*a^8*b^4 + 3510*a^8*b^2*c^2 + 1440*a^8*c^4 + 3780*a^6*b^4*c^2 - 20160*a^6*b^2*c^4 - 1344*a^6*c^6 + 135*a^4*b^8 - 3780*a^4*b^6*c^2 + 20160*a^4*b^2*c^6 + 60*a^2*b^10 - 3510*a^2*b^8*c^2 + 20160*a^2*b^6*c^4 - 20160*a^2*b^4*c^6 - 5*b^12 + 270*b^10*c^2 - 1440*b^8*c^4 + 1344*b^6*c^6
noncomputable def h12_12 (a b c : ℝ) : ℝ := 15*a^11*b - 5*a^9*b^3 - 810*a^9*b*c^2 - 90*a^7*b^5 + 1080*a^7*b^3*c^2 + 4320*a^7*b*c^4 - 90*a^5*b^7 + 3780*a^5*b^5*c^2 - 10080*a^5*b^3*c^4 - 4032*a^5*b*c^6 - 5*a^3*b^9 + 1080*a^3*b^7*c^2 - 10080*a^3*b^5*c^4 + 13440*a^3*b^3*c^6 + 15*a*b^11 - 810*a*b^9*c^2 + 4320*a*b^7*c^4 - 4032*a*b^5*c^6
noncomputable def h12_13 (a b c : ℝ) : ℝ := 5*a^11*c - 95*a^9*b^2*c - 60*a^9*c^3 - 30*a^7*b^4*c + 1200*a^7*b^2*c^3 + 96*a^7*c^5 + 210*a^5*b^6*c - 840*a^5*b^4*c^3 - 2016*a^5*b^2*c^5 + 105*a^3*b^8*c - 1680*a^3*b^6*c^3 + 3360*a^3*b^4*c^5 - 35*a*b^10*c + 420*a*b^8*c^3 - 672*a*b^6*c^5
noncomputable def h12_14 (a b c : ℝ) : ℝ := 35*a^10*b*c - 105*a^8*b^3*c - 420*a^8*b*c^3 - 210*a^6*b^5*c + 1680*a^6*b^3*c^3 + 672*a^6*b*c^5 + 30*a^4*b^7*c + 840*a^4*b^5*c^3 - 3360*a^4*b^3*c^5 + 95*a^2*b^9*c - 1200*a^2*b^7*c^3 + 2016*a^2*b^5*c^5 - 5*b^11*c + 60*b^9*c^3 - 96*b^7*c^5
noncomputable def h12_15 (a b c : ℝ) : ℝ := a^12 - 26*a^10*b^2 - 40*a^10*c^2 + 15*a^8*b^4 + 1080*a^8*b^2*c^2 + 120*a^8*c^4 + 84*a^6*b^6 - 1680*a^6*b^4*c^2 - 3360*a^6*b^2*c^4 + 15*a^4*b^8 - 1680*a^4*b^6*c^2 + 8400*a^4*b^4*c^4 - 26*a^2*b^10 + 1080*a^2*b^8*c^2 - 3360*a^2*b^6*c^4 + b^12 - 40*b^10*c^2 + 120*b^8*c^4
noncomputable def h12_16 (a b c : ℝ) : ℝ := a^11*b - 5*a^9*b^3 - 40*a^9*b*c^2 - 6*a^7*b^5 + 240*a^7*b^3*c^2 + 120*a^7*b*c^4 + 6*a^5*b^7 - 840*a^5*b^3*c^4 + 5*a^3*b^9 - 240*a^3*b^7*c^2 + 840*a^3*b^5*c^4 - a*b^11 + 40*a*b^9*c^2 - 120*a*b^7*c^4
noncomputable def h12_17 (a b c : ℝ) : ℝ := 3*a^11*c - 105*a^9*b^2*c - 20*a^9*c^3 + 270*a^7*b^4*c + 720*a^7*b^2*c^3 + 126*a^5*b^6*c - 2520*a^5*b^4*c^3 - 225*a^3*b^8*c + 1680*a^3*b^6*c^3 + 27*a*b^10*c - 180*a*b^8*c^3
noncomputable def h12_18 (a b c : ℝ) : ℝ := 27*a^10*b*c - 225*a^8*b^3*c - 180*a^8*b*c^3 + 126*a^6*b^5*c + 1680*a^6*b^3*c^3 + 270*a^4*b^7*c - 2520*a^4*b^5*c^3 - 105*a^2*b^9*c + 720*a^2*b^7*c^3 + 3*b^11*c - 20*b^9*c^3
noncomputable def h12_19 (a b c : ℝ) : ℝ := a^12 - 44*a^10*b^2 - 22*a^10*c^2 + 165*a^8*b^4 + 990*a^8*b^2*c^2 - 4620*a^6*b^4*c^2 - 165*a^4*b^8 + 4620*a^4*b^6*c^2 + 44*a^2*b^10 - 990*a^2*b^8*c^2 - b^12 + 22*b^10*c^2
noncomputable def h12_20 (a b c : ℝ) : ℝ := 5*a^11*b - 55*a^9*b^3 - 110*a^9*b*c^2 + 66*a^7*b^5 + 1320*a^7*b^3*c^2 + 66*a^5*b^7 - 2772*a^5*b^5*c^2 - 55*a^3*b^9 + 1320*a^3*b^7*c^2 + 5*a*b^11 - 110*a*b^9*c^2
noncomputable def h12_21 (a b c : ℝ) : ℝ := a^11*c - 55*a^9*b^2*c + 330*a^7*b^4*c - 462*a^5*b^6*c + 165*a^3*b^8*c - 11*a*b^10*c
noncomputable def h12_22 (a b c : ℝ) : ℝ := 11*a^10*b*c - 165*a^8*b^3*c + 462*a^6*b^5*c - 330*a^4*b^7*c + 55*a^2*b^9*c - b^11*c
noncomputable def h12_23 (a b c : ℝ) : ℝ := a^12 - 66*a^10*b^2 + 495*a^8*b^4 - 924*a^6*b^6 + 495*a^4*b^8 - 66*a^2*b^10 + b^12
noncomputable def h12_24 (a b c : ℝ) : ℝ := 3*a^11*b - 55*a^9*b^3 + 198*a^7*b^5 - 198*a^5*b^7 + 55*a^3*b^9 - 3*a*b^11

set_option maxHeartbeats 4000000 in
/-- The homogeneous zonal identity in degree 12. -/
theorem zonal12_hom (a b c u v w : ℝ) :
    (231/1024) * ((a ^ 2 + b ^ 2 + c ^ 2) * (u ^ 2 + v ^ 2 + w ^ 2)) ^ 6 + (-9009/512) * (a * u + b * v + c * w) ^ 2 * ((a ^ 2 + b ^ 2 + c ^ 2) * (u ^ 2 + v ^ 2 + w ^ 2)) ^ 5 + (225225/1024) * (a * u + b * v + c * w) ^ 4 * ((a ^ 2 + b ^ 2 + c ^ 2) * (u ^ 2 + v ^ 2 + w ^ 2)) ^ 4 + (-255255/256) * (a * u + b * v + c * w) ^ 6 * ((a ^ 2 + b ^ 2 + c ^ 2) * (u ^ 2 + v ^ 2 + w ^ 2)) ^ 3 + (2078505/1024) * (a * u + b * v + c * w) ^ 8 * ((a ^ 2 + b ^ 2 + c ^ 2) * (u ^ 2 + v ^ 2 + w ^ 2)) ^ 2 + (-969969/512) * (a * u + b * v + c * w) ^ 10 * ((a ^ 2 + b ^ 2 + c ^ 2) * (u ^ 2 + v ^ 2 + w ^ 2)) + (676039/1024) * (a * u + b * v + c * w) ^ 12
      = (1/1048576) * (h12_0 a b c * h12_0 u v w)
      + (39/131072) * (h12_1 a b c * h12_1 u v w)
      + (39/131072) * (h12_2 a b c * h12_2 u v w)
      + (3003/262144) * (h12_3 a b c * h12_3 u v w)
      + (3003/65536) * (h12_4 a b c * h12_4 u v w)
      + (1001/131072) * (h12_5 a b c * h12_5 u v w)
      + (1001/131072) * (h12_6 a b c * h12_6 u v w)
      + (9009/2097152) * (h12_7 a b c * h12_7 u v w)
      + (9009/131072) * (h12_8 a b c * h12_8 u v w)
      + (153153/262144) * (h12_9 a b c * h12_9 u v w)
      + (153153/262144) * (h12_10 a b c * h12_10 u v w)
      + (2431/524288) * (h12_11 a b c * h12_11 u v w)
      + (2431/131072) * (h12_12 a b c * h12_12 u v w)
      + (138567/262144) * (h12_13 a b c * h12_13 u v w)
      + (138567/262144) * (h12_14 a b c * h12_14 u v w)
      + (138567/1048576) * (h12_15 a b c * h12_15 u v w)
      + (138567/16384) * (h12_16 a b c * h12_16 u v w)
      + (323323/262144) * (h12_17 a b c * h12_17 u v w)
      + (323323/262144) * (h12_18 a b c * h12_18 u v w)
      + (88179/524288) * (h12_19 a b c * h12_19 u v w)
      + (88179/131072) * (h12_20 a b c * h12_20 u v w)
      + (2028117/262144) * (h12_21 a b c * h12_21 u v w)
      + (2028117/262144) * (h12_22 a b c * h12_22 u v w)
      + (676039/2097152) * (h12_23 a b c * h12_23 u v w)
      + (676039/131072) * (h12_24 a b c * h12_24 u v w) := by
  unfold h12_0 h12_1 h12_2 h12_3 h12_4 h12_5 h12_6 h12_7 h12_8 h12_9 h12_10 h12_11 h12_12 h12_13 h12_14 h12_15 h12_16 h12_17 h12_18 h12_19 h12_20 h12_21 h12_22 h12_23 h12_24
  ring

set_option maxHeartbeats 1000000 in
/-- Addition theorem for `P₁₂` on the unit sphere. -/
theorem P12_addition (x y : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (676039 * ⟪x, y⟫ ^ 12 - 1939938 * ⟪x, y⟫ ^ 10 + 2078505 * ⟪x, y⟫ ^ 8 - 1021020 * ⟪x, y⟫ ^ 6 + 225225 * ⟪x, y⟫ ^ 4 - 18018 * ⟪x, y⟫ ^ 2 + 231) / 1024
      = (1/1048576) * (h12_0 (x 0) (x 1) (x 2) * h12_0 (y 0) (y 1) (y 2))
      + (39/131072) * (h12_1 (x 0) (x 1) (x 2) * h12_1 (y 0) (y 1) (y 2))
      + (39/131072) * (h12_2 (x 0) (x 1) (x 2) * h12_2 (y 0) (y 1) (y 2))
      + (3003/262144) * (h12_3 (x 0) (x 1) (x 2) * h12_3 (y 0) (y 1) (y 2))
      + (3003/65536) * (h12_4 (x 0) (x 1) (x 2) * h12_4 (y 0) (y 1) (y 2))
      + (1001/131072) * (h12_5 (x 0) (x 1) (x 2) * h12_5 (y 0) (y 1) (y 2))
      + (1001/131072) * (h12_6 (x 0) (x 1) (x 2) * h12_6 (y 0) (y 1) (y 2))
      + (9009/2097152) * (h12_7 (x 0) (x 1) (x 2) * h12_7 (y 0) (y 1) (y 2))
      + (9009/131072) * (h12_8 (x 0) (x 1) (x 2) * h12_8 (y 0) (y 1) (y 2))
      + (153153/262144) * (h12_9 (x 0) (x 1) (x 2) * h12_9 (y 0) (y 1) (y 2))
      + (153153/262144) * (h12_10 (x 0) (x 1) (x 2) * h12_10 (y 0) (y 1) (y 2))
      + (2431/524288) * (h12_11 (x 0) (x 1) (x 2) * h12_11 (y 0) (y 1) (y 2))
      + (2431/131072) * (h12_12 (x 0) (x 1) (x 2) * h12_12 (y 0) (y 1) (y 2))
      + (138567/262144) * (h12_13 (x 0) (x 1) (x 2) * h12_13 (y 0) (y 1) (y 2))
      + (138567/262144) * (h12_14 (x 0) (x 1) (x 2) * h12_14 (y 0) (y 1) (y 2))
      + (138567/1048576) * (h12_15 (x 0) (x 1) (x 2) * h12_15 (y 0) (y 1) (y 2))
      + (138567/16384) * (h12_16 (x 0) (x 1) (x 2) * h12_16 (y 0) (y 1) (y 2))
      + (323323/262144) * (h12_17 (x 0) (x 1) (x 2) * h12_17 (y 0) (y 1) (y 2))
      + (323323/262144) * (h12_18 (x 0) (x 1) (x 2) * h12_18 (y 0) (y 1) (y 2))
      + (88179/524288) * (h12_19 (x 0) (x 1) (x 2) * h12_19 (y 0) (y 1) (y 2))
      + (88179/131072) * (h12_20 (x 0) (x 1) (x 2) * h12_20 (y 0) (y 1) (y 2))
      + (2028117/262144) * (h12_21 (x 0) (x 1) (x 2) * h12_21 (y 0) (y 1) (y 2))
      + (2028117/262144) * (h12_22 (x 0) (x 1) (x 2) * h12_22 (y 0) (y 1) (y 2))
      + (676039/2097152) * (h12_23 (x 0) (x 1) (x 2) * h12_23 (y 0) (y 1) (y 2))
      + (676039/131072) * (h12_24 (x 0) (x 1) (x 2) * h12_24 (y 0) (y 1) (y 2)) := by
  have hx' := normsq_coords x hx
  have hy' := normsq_coords y hy
  have h := zonal12_hom (x 0) (x 1) (x 2) (y 0) (y 1) (y 2)
  rw [hx', hy'] at h
  rw [inner_coords]
  linear_combination h

set_option maxHeartbeats 1000000 in
/-- Schoenberg positivity in degree 12. -/
theorem sum_P12_nonneg {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) (hx : OnSphere x) :
    0 ≤ ∑ i, ∑ j, (676039 * ⟪x i, x j⟫ ^ 12 - 1939938 * ⟪x i, x j⟫ ^ 10 + 2078505 * ⟪x i, x j⟫ ^ 8 - 1021020 * ⟪x i, x j⟫ ^ 6 + 225225 * ⟪x i, x j⟫ ^ 4 - 18018 * ⟪x i, x j⟫ ^ 2 + 231) / 1024 := by
  have step : ∑ i, ∑ j, (676039 * ⟪x i, x j⟫ ^ 12 - 1939938 * ⟪x i, x j⟫ ^ 10 + 2078505 * ⟪x i, x j⟫ ^ 8 - 1021020 * ⟪x i, x j⟫ ^ 6 + 225225 * ⟪x i, x j⟫ ^ 4 - 18018 * ⟪x i, x j⟫ ^ 2 + 231) / 1024
      = ∑ i, ∑ j, ((1/1048576) * (h12_0 (x i 0) (x i 1) (x i 2) * h12_0 (x j 0) (x j 1) (x j 2))
        + (39/131072) * (h12_1 (x i 0) (x i 1) (x i 2) * h12_1 (x j 0) (x j 1) (x j 2))
        + (39/131072) * (h12_2 (x i 0) (x i 1) (x i 2) * h12_2 (x j 0) (x j 1) (x j 2))
        + (3003/262144) * (h12_3 (x i 0) (x i 1) (x i 2) * h12_3 (x j 0) (x j 1) (x j 2))
        + (3003/65536) * (h12_4 (x i 0) (x i 1) (x i 2) * h12_4 (x j 0) (x j 1) (x j 2))
        + (1001/131072) * (h12_5 (x i 0) (x i 1) (x i 2) * h12_5 (x j 0) (x j 1) (x j 2))
        + (1001/131072) * (h12_6 (x i 0) (x i 1) (x i 2) * h12_6 (x j 0) (x j 1) (x j 2))
        + (9009/2097152) * (h12_7 (x i 0) (x i 1) (x i 2) * h12_7 (x j 0) (x j 1) (x j 2))
        + (9009/131072) * (h12_8 (x i 0) (x i 1) (x i 2) * h12_8 (x j 0) (x j 1) (x j 2))
        + (153153/262144) * (h12_9 (x i 0) (x i 1) (x i 2) * h12_9 (x j 0) (x j 1) (x j 2))
        + (153153/262144) * (h12_10 (x i 0) (x i 1) (x i 2) * h12_10 (x j 0) (x j 1) (x j 2))
        + (2431/524288) * (h12_11 (x i 0) (x i 1) (x i 2) * h12_11 (x j 0) (x j 1) (x j 2))
        + (2431/131072) * (h12_12 (x i 0) (x i 1) (x i 2) * h12_12 (x j 0) (x j 1) (x j 2))
        + (138567/262144) * (h12_13 (x i 0) (x i 1) (x i 2) * h12_13 (x j 0) (x j 1) (x j 2))
        + (138567/262144) * (h12_14 (x i 0) (x i 1) (x i 2) * h12_14 (x j 0) (x j 1) (x j 2))
        + (138567/1048576) * (h12_15 (x i 0) (x i 1) (x i 2) * h12_15 (x j 0) (x j 1) (x j 2))
        + (138567/16384) * (h12_16 (x i 0) (x i 1) (x i 2) * h12_16 (x j 0) (x j 1) (x j 2))
        + (323323/262144) * (h12_17 (x i 0) (x i 1) (x i 2) * h12_17 (x j 0) (x j 1) (x j 2))
        + (323323/262144) * (h12_18 (x i 0) (x i 1) (x i 2) * h12_18 (x j 0) (x j 1) (x j 2))
        + (88179/524288) * (h12_19 (x i 0) (x i 1) (x i 2) * h12_19 (x j 0) (x j 1) (x j 2))
        + (88179/131072) * (h12_20 (x i 0) (x i 1) (x i 2) * h12_20 (x j 0) (x j 1) (x j 2))
        + (2028117/262144) * (h12_21 (x i 0) (x i 1) (x i 2) * h12_21 (x j 0) (x j 1) (x j 2))
        + (2028117/262144) * (h12_22 (x i 0) (x i 1) (x i 2) * h12_22 (x j 0) (x j 1) (x j 2))
        + (676039/2097152) * (h12_23 (x i 0) (x i 1) (x i 2) * h12_23 (x j 0) (x j 1) (x j 2))
        + (676039/131072) * (h12_24 (x i 0) (x i 1) (x i 2) * h12_24 (x j 0) (x j 1) (x j 2))) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      P12_addition (x i) (x j) (hx i) (hx j)
  rw [step]
  simp only [Finset.sum_add_distrib, sum_gram_eq]
  positivity

/-- The degree-12 Yudin polynomial: touching distances `123/100`, `42/25`, `47/25`. -/
noncomputable def yudinF12 (t : ℝ) : ℝ :=
  (34645068691531042154161429510684749298607544489195322272041466068539910227765625/49042594187248903829211620825899122958892848689022009980306315505972859726406024) + (121397969730264244919756155254208481103532361460061701403801531927980619052734375/343298159310742326804481345781293860712249940823154069862144208541810018084842168) * t ^ 1 + (312374772044418065617314442366031033226600418895684974648770945614003515625000/1125040784258050696456633623815101603457747933409212775765453866944133954397891) * t ^ 2 + (50871775330122658859775838643323637494805158289110421515844282404445648193359375/200257259597933023969280785039088085415479132146839874086250788316055843882824598) * t ^ 3 + (31159373556544588444925716718750000000000000000000000000000000000000000000000/164414827256102646937012138784144569306633113421050799742406230144545027818411) * t ^ 4 + (-3332082262041546022264629574727978787525399392864665527343750000000000000000000/14304089971280930283520056074220577529677080867631419577589342022575417420201757) * t ^ 5 + (-423767480369006402850989747375000000000000000000000000000000000000000000000000/493244481768307940811036416352433707919899340263152399227218690433635083455233) * t ^ 6 + (43317069406540098289440184471463724237830192107240651855468750000000000000000000/300385889396899535953921177558632128123218698220259811129376182474083765824236897) * t ^ 7 + (2012895531752780413542201300031250000000000000000000000000000000000000000000000/1150903790792718528559084971489011985146431793947355598196843611011815194728877) * t ^ 8 + (-805158212701112165416880520012500000000000000000000000000000000000000000000000/493244481768307940811036416352433707919899340263152399227218690433635083455233) * t ^ 10 + (841756313278435445663102361831250000000000000000000000000000000000000000000000/1479733445304923822433109249057301123759698020789457197681656071300905250365699) * t ^ 12

/-- Legendre expansion of `yudinF12`; all six coefficients are `≥ 0`. -/
theorem yudinF12_legendre (t : ℝ) : yudinF12 t =
    (25112058114515892702458371168699918546758419316915880412639437758263139355711703125/31240132497277551739207802466097741324814744614907020357455122977304711645720637288) * (1) + (3274994498117545420192398862664635048859126277705238295159568670423619001083984375/7209261345525588862894108261407171074957248757286235467105028379378010379781685528) * (t) + (58638878783256120377955532578228523914334874563431925487481228319292625781250000/300385889396899535953921177558632128123218698220259811129376182474083765824236897) * ((3 * t ^ 2 - 1) / 2) + (21756251352562735059934010323040099821071918911979203317348307096593475341796875/367138309262877210610348105904994823261711742269206435824793111912769047118511763) * ((5 * t ^ 3 - 3 * t) / 2) + (53313316192664736356234073195647660600406390285834648437500000000000000000000000/9912734350097684686479398859434860228066217041268573767269414021644764272199817601) * ((429 * t ^ 7 - 693 * t ^ 5 + 315 * t ^ 3 - 35 * t) / 16) + (116026176443278758427650668800000000000000000000000000000000000000000000000000/134655743522748067841412941664214402262132519891840604989030702488382377783278609) * ((676039 * t ^ 12 - 1939938 * t ^ 10 + 2078505 * t ^ 8 - 1021020 * t ^ 6 + 225225 * t ^ 4 - 18018 * t ^ 2 + 231) / 1024) := by
  unfold yudinF12; ring

set_option maxHeartbeats 1000000 in
/-- `f(1 - s²/2) ≤ 1/s` on the range `0 < s ≤ 2` of chord lengths of the unit sphere.  The
slack is three exact double zeros times a polynomial with nonnegative Bernstein coefficients
on `[0,2]`. -/
theorem yudinF12_le_inv {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) : yudinF12 (1 - s ^ 2 / 2) ≤ s⁻¹ := by
  have h0 : (0:ℝ) ≤ s := hs.le
  have h2 : (0:ℝ) ≤ 2 - s := by linarith
  have key : 1 - s * yudinF12 (1 - s ^ 2 / 2)
      = (s - 123/100) ^ 2 * (s - 42/25) ^ 2 * (s - 47/25) ^ 2
        * ((244140625/1978128094753456128) * s ^ 0 * (2 - s) ^ 29 + (37289677906352839707766236795615457861784921717939561665097117082635361083984375/8959358132913587991108802920667598005445181716053536759887552281996653762358471922024448) * s ^ 1 * (2 - s) ^ 28 + (456108105793725667230809235173665804366695675015843874423870850596656493408203125/6719518599685190993331602190500698504083886287040152569915664211497490321768853941518336) * s ^ 2 * (2 - s) ^ 27 + (28752308744941260157847453470479430278835686748127969607248157483321618716552734375/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 3 * (2 - s) ^ 26 + (218735335703137768359238718927384640227428701685244486395797250162216077599365234375/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 4 * (2 - s) ^ 25 + (2568024547432404009687984198937190553472879761557240663269200443093423159141845703125/80634223196222291919979226286008382049006635444481830838987970537969883861226247298220032) * s ^ 5 * (2 - s) ^ 24 + (1512922848820067616434089033596019173313771293589649760716530859658432780452880859375/10079277899527786489997403285751047756125829430560228854873496317246235482653280912277504) * s ^ 6 * (2 - s) ^ 23 + (11761600226135708579572572333582364721246668168854918884326577194974485389393310546875/20158555799055572979994806571502095512251658861120457709746992634492470965306561824555008) * s ^ 7 * (2 - s) ^ 22 + (76853056210658041143616674013971695874210512224258446998173263547756731954117431640625/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 8 * (2 - s) ^ 21 + (142644011507664938229593385763397206687557385547107612803747736843042745304288330078125/26878074398740763973326408762002794016335545148160610279662656845989961287075415766073344) * s ^ 9 * (2 - s) ^ 20 + (256425101168404940909209146870294333332847532963119746535231168316296887568111572265625/20158555799055572979994806571502095512251658861120457709746992634492470965306561824555008) * s ^ 10 * (2 - s) ^ 19 + (118521449385228368867125947336180844546279671398156395780329286082780476009996337890625/4479679066456793995554401460333799002722590858026768379943776140998326881179235961012224) * s ^ 11 * (2 - s) ^ 18 + (1937838023685690868481588427528966544718630474009838478100244095585982137947191162109375/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 12 * (2 - s) ^ 17 + (883378792142592638104622203614817382228554341938866861955560251779782178983778076171875/11519174742317470274282746612286911721286662206354547262712567219709983408746606756888576) * s ^ 13 * (2 - s) ^ 16 + (543788789520584292230543434820897961847913202552280779304484997315843006921988525390625/5039638949763893244998701642875523878062914715280114427436748158623117741326640456138752) * s ^ 14 * (2 - s) ^ 15 + (193036746355081261395651848339356683912245593841103861211549353942143855931912841796875/1439896842789683784285343326535863965160832775794318407839070902463747926093325844611072) * s ^ 15 * (2 - s) ^ 14 + (281308265359987796262099751938493509949719976941174555034658543915825959978675537109375/1919862457052911712380457768714485286881110367725757877118761203284997234791101126148096) * s ^ 16 * (2 - s) ^ 13 + (11232575861451087995051549290282182210119284093011223612179179526217002295292423095703125/80634223196222291919979226286008382049006635444481830838987970537969883861226247298220032) * s ^ 17 * (2 - s) ^ 12 + (2275220104963855391883326390658632957422122083780309069012291961405251286338394775390625/20158555799055572979994806571502095512251658861120457709746992634492470965306561824555008) * s ^ 18 * (2 - s) ^ 11 + (3044662147322738148614778138120859906275027683920506143991770623323435031176842041015625/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 19 * (2 - s) ^ 10 + (534890469678430299520309609025201886128304186002604371875564126144612092822386474609375/13439037199370381986663204381001397008167772574080305139831328422994980643537707883036672) * s ^ 20 * (2 - s) ^ 9 + (410681394390227195437583939465701807632773017027741070297585030446900568033468017578125/26878074398740763973326408762002794016335545148160610279662656845989961287075415766073344) * s ^ 21 * (2 - s) ^ 8 + (4067381476863596001452134674379364019579165103040722465328669496293971389388427734375/1119919766614198498888600365083449750680647714506692094985944035249581720294808990253056) * s ^ 22 * (2 - s) ^ 7 + (6642696536630242295946155163926156659030684141968179915212126609475168901268310546875/20158555799055572979994806571502095512251658861120457709746992634492470965306561824555008) * s ^ 23 * (2 - s) ^ 6 + (332687517059150870823100158345704747236343106959177947078339161635839040506591796875/4479679066456793995554401460333799002722590858026768379943776140998326881179235961012224) * s ^ 24 * (2 - s) ^ 5 + (13014223708205767069589564222792650622896522921267955163856304723693893350212158203125/80634223196222291919979226286008382049006635444481830838987970537969883861226247298220032) * s ^ 25 * (2 - s) ^ 4 + (1974435313533393320681030312700939426847034025529546452363873345014212061161865234375/20158555799055572979994806571502095512251658861120457709746992634492470965306561824555008) * s ^ 26 * (2 - s) ^ 3 + (1093438969609697795116914764070821825060846872986511166521222585180168304591552734375/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 27 * (2 - s) ^ 2 + (11104928732293450705839171994612871054386917221917374591520167064464263427734375/3379189640274171985582902786271409858729638565270380975567344335678898829152051265536) * s ^ 28 * (2 - s) ^ 1 + (11013061617529695942994575376818078331234607076756341514198120083461181640625/136030216250604861471673062579408742472179853879318232693432614396499609224579383296) * s ^ 29 * (2 - s) ^ 0) := by
    unfold yudinF12; ring
  have hbern : (0:ℝ) ≤ (244140625/1978128094753456128) * s ^ 0 * (2 - s) ^ 29 + (37289677906352839707766236795615457861784921717939561665097117082635361083984375/8959358132913587991108802920667598005445181716053536759887552281996653762358471922024448) * s ^ 1 * (2 - s) ^ 28 + (456108105793725667230809235173665804366695675015843874423870850596656493408203125/6719518599685190993331602190500698504083886287040152569915664211497490321768853941518336) * s ^ 2 * (2 - s) ^ 27 + (28752308744941260157847453470479430278835686748127969607248157483321618716552734375/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 3 * (2 - s) ^ 26 + (218735335703137768359238718927384640227428701685244486395797250162216077599365234375/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 4 * (2 - s) ^ 25 + (2568024547432404009687984198937190553472879761557240663269200443093423159141845703125/80634223196222291919979226286008382049006635444481830838987970537969883861226247298220032) * s ^ 5 * (2 - s) ^ 24 + (1512922848820067616434089033596019173313771293589649760716530859658432780452880859375/10079277899527786489997403285751047756125829430560228854873496317246235482653280912277504) * s ^ 6 * (2 - s) ^ 23 + (11761600226135708579572572333582364721246668168854918884326577194974485389393310546875/20158555799055572979994806571502095512251658861120457709746992634492470965306561824555008) * s ^ 7 * (2 - s) ^ 22 + (76853056210658041143616674013971695874210512224258446998173263547756731954117431640625/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 8 * (2 - s) ^ 21 + (142644011507664938229593385763397206687557385547107612803747736843042745304288330078125/26878074398740763973326408762002794016335545148160610279662656845989961287075415766073344) * s ^ 9 * (2 - s) ^ 20 + (256425101168404940909209146870294333332847532963119746535231168316296887568111572265625/20158555799055572979994806571502095512251658861120457709746992634492470965306561824555008) * s ^ 10 * (2 - s) ^ 19 + (118521449385228368867125947336180844546279671398156395780329286082780476009996337890625/4479679066456793995554401460333799002722590858026768379943776140998326881179235961012224) * s ^ 11 * (2 - s) ^ 18 + (1937838023685690868481588427528966544718630474009838478100244095585982137947191162109375/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 12 * (2 - s) ^ 17 + (883378792142592638104622203614817382228554341938866861955560251779782178983778076171875/11519174742317470274282746612286911721286662206354547262712567219709983408746606756888576) * s ^ 13 * (2 - s) ^ 16 + (543788789520584292230543434820897961847913202552280779304484997315843006921988525390625/5039638949763893244998701642875523878062914715280114427436748158623117741326640456138752) * s ^ 14 * (2 - s) ^ 15 + (193036746355081261395651848339356683912245593841103861211549353942143855931912841796875/1439896842789683784285343326535863965160832775794318407839070902463747926093325844611072) * s ^ 15 * (2 - s) ^ 14 + (281308265359987796262099751938493509949719976941174555034658543915825959978675537109375/1919862457052911712380457768714485286881110367725757877118761203284997234791101126148096) * s ^ 16 * (2 - s) ^ 13 + (11232575861451087995051549290282182210119284093011223612179179526217002295292423095703125/80634223196222291919979226286008382049006635444481830838987970537969883861226247298220032) * s ^ 17 * (2 - s) ^ 12 + (2275220104963855391883326390658632957422122083780309069012291961405251286338394775390625/20158555799055572979994806571502095512251658861120457709746992634492470965306561824555008) * s ^ 18 * (2 - s) ^ 11 + (3044662147322738148614778138120859906275027683920506143991770623323435031176842041015625/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 19 * (2 - s) ^ 10 + (534890469678430299520309609025201886128304186002604371875564126144612092822386474609375/13439037199370381986663204381001397008167772574080305139831328422994980643537707883036672) * s ^ 20 * (2 - s) ^ 9 + (410681394390227195437583939465701807632773017027741070297585030446900568033468017578125/26878074398740763973326408762002794016335545148160610279662656845989961287075415766073344) * s ^ 21 * (2 - s) ^ 8 + (4067381476863596001452134674379364019579165103040722465328669496293971389388427734375/1119919766614198498888600365083449750680647714506692094985944035249581720294808990253056) * s ^ 22 * (2 - s) ^ 7 + (6642696536630242295946155163926156659030684141968179915212126609475168901268310546875/20158555799055572979994806571502095512251658861120457709746992634492470965306561824555008) * s ^ 23 * (2 - s) ^ 6 + (332687517059150870823100158345704747236343106959177947078339161635839040506591796875/4479679066456793995554401460333799002722590858026768379943776140998326881179235961012224) * s ^ 24 * (2 - s) ^ 5 + (13014223708205767069589564222792650622896522921267955163856304723693893350212158203125/80634223196222291919979226286008382049006635444481830838987970537969883861226247298220032) * s ^ 25 * (2 - s) ^ 4 + (1974435313533393320681030312700939426847034025529546452363873345014212061161865234375/20158555799055572979994806571502095512251658861120457709746992634492470965306561824555008) * s ^ 26 * (2 - s) ^ 3 + (1093438969609697795116914764070821825060846872986511166521222585180168304591552734375/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 27 * (2 - s) ^ 2 + (11104928732293450705839171994612871054386917221917374591520167064464263427734375/3379189640274171985582902786271409858729638565270380975567344335678898829152051265536) * s ^ 28 * (2 - s) ^ 1 + (11013061617529695942994575376818078331234607076756341514198120083461181640625/136030216250604861471673062579408742472179853879318232693432614396499609224579383296) * s ^ 29 * (2 - s) ^ 0 := by
    have e0 : (0:ℝ) ≤ (244140625/1978128094753456128) * s ^ 0 * (2 - s) ^ 29 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e1 : (0:ℝ) ≤ (37289677906352839707766236795615457861784921717939561665097117082635361083984375/8959358132913587991108802920667598005445181716053536759887552281996653762358471922024448) * s ^ 1 * (2 - s) ^ 28 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e2 : (0:ℝ) ≤ (456108105793725667230809235173665804366695675015843874423870850596656493408203125/6719518599685190993331602190500698504083886287040152569915664211497490321768853941518336) * s ^ 2 * (2 - s) ^ 27 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e3 : (0:ℝ) ≤ (28752308744941260157847453470479430278835686748127969607248157483321618716552734375/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 3 * (2 - s) ^ 26 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e4 : (0:ℝ) ≤ (218735335703137768359238718927384640227428701685244486395797250162216077599365234375/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 4 * (2 - s) ^ 25 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e5 : (0:ℝ) ≤ (2568024547432404009687984198937190553472879761557240663269200443093423159141845703125/80634223196222291919979226286008382049006635444481830838987970537969883861226247298220032) * s ^ 5 * (2 - s) ^ 24 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e6 : (0:ℝ) ≤ (1512922848820067616434089033596019173313771293589649760716530859658432780452880859375/10079277899527786489997403285751047756125829430560228854873496317246235482653280912277504) * s ^ 6 * (2 - s) ^ 23 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e7 : (0:ℝ) ≤ (11761600226135708579572572333582364721246668168854918884326577194974485389393310546875/20158555799055572979994806571502095512251658861120457709746992634492470965306561824555008) * s ^ 7 * (2 - s) ^ 22 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e8 : (0:ℝ) ≤ (76853056210658041143616674013971695874210512224258446998173263547756731954117431640625/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 8 * (2 - s) ^ 21 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e9 : (0:ℝ) ≤ (142644011507664938229593385763397206687557385547107612803747736843042745304288330078125/26878074398740763973326408762002794016335545148160610279662656845989961287075415766073344) * s ^ 9 * (2 - s) ^ 20 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e10 : (0:ℝ) ≤ (256425101168404940909209146870294333332847532963119746535231168316296887568111572265625/20158555799055572979994806571502095512251658861120457709746992634492470965306561824555008) * s ^ 10 * (2 - s) ^ 19 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e11 : (0:ℝ) ≤ (118521449385228368867125947336180844546279671398156395780329286082780476009996337890625/4479679066456793995554401460333799002722590858026768379943776140998326881179235961012224) * s ^ 11 * (2 - s) ^ 18 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e12 : (0:ℝ) ≤ (1937838023685690868481588427528966544718630474009838478100244095585982137947191162109375/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 12 * (2 - s) ^ 17 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e13 : (0:ℝ) ≤ (883378792142592638104622203614817382228554341938866861955560251779782178983778076171875/11519174742317470274282746612286911721286662206354547262712567219709983408746606756888576) * s ^ 13 * (2 - s) ^ 16 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e14 : (0:ℝ) ≤ (543788789520584292230543434820897961847913202552280779304484997315843006921988525390625/5039638949763893244998701642875523878062914715280114427436748158623117741326640456138752) * s ^ 14 * (2 - s) ^ 15 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e15 : (0:ℝ) ≤ (193036746355081261395651848339356683912245593841103861211549353942143855931912841796875/1439896842789683784285343326535863965160832775794318407839070902463747926093325844611072) * s ^ 15 * (2 - s) ^ 14 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e16 : (0:ℝ) ≤ (281308265359987796262099751938493509949719976941174555034658543915825959978675537109375/1919862457052911712380457768714485286881110367725757877118761203284997234791101126148096) * s ^ 16 * (2 - s) ^ 13 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e17 : (0:ℝ) ≤ (11232575861451087995051549290282182210119284093011223612179179526217002295292423095703125/80634223196222291919979226286008382049006635444481830838987970537969883861226247298220032) * s ^ 17 * (2 - s) ^ 12 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e18 : (0:ℝ) ≤ (2275220104963855391883326390658632957422122083780309069012291961405251286338394775390625/20158555799055572979994806571502095512251658861120457709746992634492470965306561824555008) * s ^ 18 * (2 - s) ^ 11 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e19 : (0:ℝ) ≤ (3044662147322738148614778138120859906275027683920506143991770623323435031176842041015625/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 19 * (2 - s) ^ 10 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e20 : (0:ℝ) ≤ (534890469678430299520309609025201886128304186002604371875564126144612092822386474609375/13439037199370381986663204381001397008167772574080305139831328422994980643537707883036672) * s ^ 20 * (2 - s) ^ 9 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e21 : (0:ℝ) ≤ (410681394390227195437583939465701807632773017027741070297585030446900568033468017578125/26878074398740763973326408762002794016335545148160610279662656845989961287075415766073344) * s ^ 21 * (2 - s) ^ 8 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e22 : (0:ℝ) ≤ (4067381476863596001452134674379364019579165103040722465328669496293971389388427734375/1119919766614198498888600365083449750680647714506692094985944035249581720294808990253056) * s ^ 22 * (2 - s) ^ 7 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e23 : (0:ℝ) ≤ (6642696536630242295946155163926156659030684141968179915212126609475168901268310546875/20158555799055572979994806571502095512251658861120457709746992634492470965306561824555008) * s ^ 23 * (2 - s) ^ 6 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e24 : (0:ℝ) ≤ (332687517059150870823100158345704747236343106959177947078339161635839040506591796875/4479679066456793995554401460333799002722590858026768379943776140998326881179235961012224) * s ^ 24 * (2 - s) ^ 5 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e25 : (0:ℝ) ≤ (13014223708205767069589564222792650622896522921267955163856304723693893350212158203125/80634223196222291919979226286008382049006635444481830838987970537969883861226247298220032) * s ^ 25 * (2 - s) ^ 4 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e26 : (0:ℝ) ≤ (1974435313533393320681030312700939426847034025529546452363873345014212061161865234375/20158555799055572979994806571502095512251658861120457709746992634492470965306561824555008) * s ^ 26 * (2 - s) ^ 3 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e27 : (0:ℝ) ≤ (1093438969609697795116914764070821825060846872986511166521222585180168304591552734375/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 27 * (2 - s) ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e28 : (0:ℝ) ≤ (11104928732293450705839171994612871054386917221917374591520167064464263427734375/3379189640274171985582902786271409858729638565270380975567344335678898829152051265536) * s ^ 28 * (2 - s) ^ 1 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    have e29 : (0:ℝ) ≤ (11013061617529695942994575376818078331234607076756341514198120083461181640625/136030216250604861471673062579408742472179853879318232693432614396499609224579383296) * s ^ 29 * (2 - s) ^ 0 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0 _)) (pow_nonneg h2 _)
    linarith [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29]
  have hq : (0:ℝ) ≤ (s - 123/100) ^ 2 * (s - 42/25) ^ 2 * (s - 47/25) ^ 2
        * ((244140625/1978128094753456128) * s ^ 0 * (2 - s) ^ 29 + (37289677906352839707766236795615457861784921717939561665097117082635361083984375/8959358132913587991108802920667598005445181716053536759887552281996653762358471922024448) * s ^ 1 * (2 - s) ^ 28 + (456108105793725667230809235173665804366695675015843874423870850596656493408203125/6719518599685190993331602190500698504083886287040152569915664211497490321768853941518336) * s ^ 2 * (2 - s) ^ 27 + (28752308744941260157847453470479430278835686748127969607248157483321618716552734375/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 3 * (2 - s) ^ 26 + (218735335703137768359238718927384640227428701685244486395797250162216077599365234375/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 4 * (2 - s) ^ 25 + (2568024547432404009687984198937190553472879761557240663269200443093423159141845703125/80634223196222291919979226286008382049006635444481830838987970537969883861226247298220032) * s ^ 5 * (2 - s) ^ 24 + (1512922848820067616434089033596019173313771293589649760716530859658432780452880859375/10079277899527786489997403285751047756125829430560228854873496317246235482653280912277504) * s ^ 6 * (2 - s) ^ 23 + (11761600226135708579572572333582364721246668168854918884326577194974485389393310546875/20158555799055572979994806571502095512251658861120457709746992634492470965306561824555008) * s ^ 7 * (2 - s) ^ 22 + (76853056210658041143616674013971695874210512224258446998173263547756731954117431640625/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 8 * (2 - s) ^ 21 + (142644011507664938229593385763397206687557385547107612803747736843042745304288330078125/26878074398740763973326408762002794016335545148160610279662656845989961287075415766073344) * s ^ 9 * (2 - s) ^ 20 + (256425101168404940909209146870294333332847532963119746535231168316296887568111572265625/20158555799055572979994806571502095512251658861120457709746992634492470965306561824555008) * s ^ 10 * (2 - s) ^ 19 + (118521449385228368867125947336180844546279671398156395780329286082780476009996337890625/4479679066456793995554401460333799002722590858026768379943776140998326881179235961012224) * s ^ 11 * (2 - s) ^ 18 + (1937838023685690868481588427528966544718630474009838478100244095585982137947191162109375/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 12 * (2 - s) ^ 17 + (883378792142592638104622203614817382228554341938866861955560251779782178983778076171875/11519174742317470274282746612286911721286662206354547262712567219709983408746606756888576) * s ^ 13 * (2 - s) ^ 16 + (543788789520584292230543434820897961847913202552280779304484997315843006921988525390625/5039638949763893244998701642875523878062914715280114427436748158623117741326640456138752) * s ^ 14 * (2 - s) ^ 15 + (193036746355081261395651848339356683912245593841103861211549353942143855931912841796875/1439896842789683784285343326535863965160832775794318407839070902463747926093325844611072) * s ^ 15 * (2 - s) ^ 14 + (281308265359987796262099751938493509949719976941174555034658543915825959978675537109375/1919862457052911712380457768714485286881110367725757877118761203284997234791101126148096) * s ^ 16 * (2 - s) ^ 13 + (11232575861451087995051549290282182210119284093011223612179179526217002295292423095703125/80634223196222291919979226286008382049006635444481830838987970537969883861226247298220032) * s ^ 17 * (2 - s) ^ 12 + (2275220104963855391883326390658632957422122083780309069012291961405251286338394775390625/20158555799055572979994806571502095512251658861120457709746992634492470965306561824555008) * s ^ 18 * (2 - s) ^ 11 + (3044662147322738148614778138120859906275027683920506143991770623323435031176842041015625/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 19 * (2 - s) ^ 10 + (534890469678430299520309609025201886128304186002604371875564126144612092822386474609375/13439037199370381986663204381001397008167772574080305139831328422994980643537707883036672) * s ^ 20 * (2 - s) ^ 9 + (410681394390227195437583939465701807632773017027741070297585030446900568033468017578125/26878074398740763973326408762002794016335545148160610279662656845989961287075415766073344) * s ^ 21 * (2 - s) ^ 8 + (4067381476863596001452134674379364019579165103040722465328669496293971389388427734375/1119919766614198498888600365083449750680647714506692094985944035249581720294808990253056) * s ^ 22 * (2 - s) ^ 7 + (6642696536630242295946155163926156659030684141968179915212126609475168901268310546875/20158555799055572979994806571502095512251658861120457709746992634492470965306561824555008) * s ^ 23 * (2 - s) ^ 6 + (332687517059150870823100158345704747236343106959177947078339161635839040506591796875/4479679066456793995554401460333799002722590858026768379943776140998326881179235961012224) * s ^ 24 * (2 - s) ^ 5 + (13014223708205767069589564222792650622896522921267955163856304723693893350212158203125/80634223196222291919979226286008382049006635444481830838987970537969883861226247298220032) * s ^ 25 * (2 - s) ^ 4 + (1974435313533393320681030312700939426847034025529546452363873345014212061161865234375/20158555799055572979994806571502095512251658861120457709746992634492470965306561824555008) * s ^ 26 * (2 - s) ^ 3 + (1093438969609697795116914764070821825060846872986511166521222585180168304591552734375/40317111598111145959989613143004191024503317722240915419493985268984941930613123649110016) * s ^ 27 * (2 - s) ^ 2 + (11104928732293450705839171994612871054386917221917374591520167064464263427734375/3379189640274171985582902786271409858729638565270380975567344335678898829152051265536) * s ^ 28 * (2 - s) ^ 1 + (11013061617529695942994575376818078331234607076756341514198120083461181640625/136030216250604861471673062579408742472179853879318232693432614396499609224579383296) * s ^ 29 * (2 - s) ^ 0) := mul_nonneg (by positivity) hbern
  rw [← one_div, le_div_iff₀ hs]
  linarith

set_option maxHeartbeats 1000000 in
/-- **Yudin's bound at degree 12.**  Every admissible 8-point configuration has energy at
least `19.6475640`, against a method optimum of `19.6478`. -/
theorem energy_ge_yudin12 (x : Fin 8 → EuclideanSpace ℝ (Fin 3)) (hx : Admissible x) :
    (76724062790141578473323669343642141230914095486355401886155184551047892478384515625/3905016562159693967400975308262217665601843076863377544681890372163088955715079661 : ℝ) ≤ energy x := by
  obtain ⟨hsph, hinj⟩ := hx
  have hterm : ∀ i j : Fin 8, i ≠ j → yudinF12 ⟪x i, x j⟫ ≤ ‖x i - x j‖⁻¹ := by
    intro i j hij
    have hne : x i - x j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hinj h))
    have hpos : 0 < ‖x i - x j‖ := norm_pos_iff.mpr hne
    have hle2 : ‖x i - x j‖ ≤ 2 := by
      have h := norm_sub_le (x i) (x j)
      rw [hsph i, hsph j] at h
      linarith
    rw [inner_eq_of_norm _ _ (hsph i) (hsph j)]
    exact yudinF12_le_inv hpos hle2
  have hdiag : ∀ i : Fin 8, yudinF12 ⟪x i, x i⟫ = yudinF12 1 := by
    intro i; rw [real_inner_self_eq_norm_sq, hsph i]; norm_num
  have hsplit : ∑ i, ∑ j, yudinF12 ⟪x i, x j⟫
      = ∑ i, yudinF12 ⟪x i, x i⟫ + ∑ i, ∑ j ∈ univ.erase i, yudinF12 ⟪x i, x j⟫ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hoff : ∑ i, ∑ j ∈ univ.erase i, yudinF12 ⟪x i, x j⟫
      ≤ ∑ i, ∑ j ∈ univ.erase i, ‖x i - x j‖⁻¹ :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj =>
      hterm i j (Finset.ne_of_mem_erase hj).symm
  have hupper : ∑ i, ∑ j, yudinF12 ⟪x i, x j⟫ ≤ 8 * yudinF12 1 + 2 * energy x := by
    rw [hsplit, energy_eq_half]
    simp only [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    linarith
  have hlower : (64 : ℝ) * (25112058114515892702458371168699918546758419316915880412639437758263139355711703125/31240132497277551739207802466097741324814744614907020357455122977304711645720637288) ≤ ∑ i, ∑ j, yudinF12 ⟪x i, x j⟫ := by
    simp only [yudinF12_legendre, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h1 := sum_P1_nonneg x
    have h2 := sum_P2_nonneg x hsph
    have h3 := sum_P3_nonneg x hsph
    have h7 := sum_P7_nonneg x hsph
    have h12 := sum_P12_nonneg x hsph
    push_cast
    linarith
  have hf1 : yudinF12 1 = 13758168730630577439177979321639367763328957522925277625489850892359375/9058420591342176993351704978531960850644159086157308834471768161780132 := by unfold yudinF12; norm_num
  rw [hf1] at hupper
  linarith

/-- The best lower bound proved here: `19.6475 < thomsonInf 8`. -/
theorem thomsonInf_ge_yudin12 : (76724062790141578473323669343642141230914095486355401886155184551047892478384515625/3905016562159693967400975308262217665601843076863377544681890372163088955715079661 : ℝ) ≤ thomsonInf 8 := by
  obtain ⟨x₀, hx₀⟩ := exists_admissible 8
  refine le_csInf ⟨_, x₀, hx₀, rfl⟩ ?_
  rintro e ⟨x, hx, rfl⟩
  exact energy_ge_yudin12 x hx

theorem thomsonInf_gt'' : (19.6475 : ℝ) < thomsonInf 8 :=
  lt_of_lt_of_le (by norm_num) thomsonInf_ge_yudin12

end Thomson
