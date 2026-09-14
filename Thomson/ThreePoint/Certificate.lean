import Mathlib
import Thomson.ThreePoint.BachocVallentin
import Thomson.LP.Yudin
import Thomson.Antiprism.Family

namespace Thomson
open Finset
open scoped RealInnerProductSpace
open Matrix

/-! # The three-point certificate and the three-point bound

Blueprint §12.2.  `ThreePointCert` is the certificate; `three_point_bound` is the bound, proved;
`pair_of_poly`, `tri_of_poly` restate the certificate's two inequalities as the polynomial
obligations of the Tasks (`Thomson.Certificate.Assemble`). -/

/-- **A three-point certificate.**  The data of the Cohn–Woo-type bound of blueprint §12, with
the four properties the bound needs.  `pair` and `tri` are required only on the range
`t ≤ 0.5373` that `separation_of_energy_le` guarantees for a near-optimal configuration
(`t < 1 - 0.962²/2 = 0.537278`). -/
structure ThreePointCert where
  a0 : ℝ
  a1 : ℝ
  lam : ℝ
  L : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ
  D : (k : Fin 6) → Fin (9 - (k : ℕ)) → ℝ
  D_nonneg : ∀ k r, 0 ≤ D k r
  a1_nonneg : 0 ≤ a1
  lam_nonneg : 0 ≤ lam
  lam_le : lam ≤ 1 / 18
  pair : ∀ t : ℝ, -1 ≤ t → t ≤ 5373 / 10000 →
    a0 + a1 * t + 3 * Fsum L D 1 t t ≤ (1 - 18 * lam) * (Real.sqrt (2 - 2 * t))⁻¹
  tri : ∀ u v t : ℝ, -1 ≤ u → -1 ≤ v → -1 ≤ t →
    u ≤ 5373 / 10000 → v ≤ 5373 / 10000 → t ≤ 5373 / 10000 →
    0 ≤ 1 + 2 * u * v * t - u ^ 2 - v ^ 2 - t ^ 2 →
    Fsum L D u v t ≤ lam * ((Real.sqrt (2 - 2 * u))⁻¹ + (Real.sqrt (2 - 2 * v))⁻¹
      + (Real.sqrt (2 - 2 * t))⁻¹)
  bound_ge : antiprismEnergy uStar ≤ (64 * a0 - 8 * (a0 + a1) - 8 * Fsum L D 1 1 1) / 2

/-! ### The one remaining leaf, as explicit polynomial obligations

`exists_threePointCert` asks for data `(a₀, a₁, λ, L, D)` with `D ≥ 0`, the bound, and the two
inequalities `pair` and `tri`.  The next two lemmas restate `pair` and `tri` as polynomial
inequalities in chord lengths — the precise shape that a Bernstein certificate (`pair`, one
variable, as in `yudinF12_le_inv`) and a 3-dimensional interval verification (`tri`) must
establish; blueprint §12.7, steps 2–4. -/

/-- The `pair` obligation as a polynomial inequality in the chord length `s = √(2−2t)`:
it suffices that `(1 − 18λ) − s·[a₀ + a₁ t + 3F(1,t,t)] ≥ 0` for `s ∈ [0.9619, 2]`, `t = 1 − s²/2`.
The lower end is `√(2 − 2·0.5373) = 0.96197…` (the separation theorem's `t ≤ 0.5373`) rounded down;
it was `24/25` once, which is too generous for the triangle inequality (`tri_of_poly`). -/
theorem pair_of_poly (L : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ)
    (D : (k : Fin 6) → Fin (9 - (k : ℕ)) → ℝ) (a0 a1 lam : ℝ)
    (h : ∀ s : ℝ, 9619 / 10000 ≤ s → s ≤ 2 →
      0 ≤ (1 - 18 * lam) - s * (a0 + a1 * (1 - s ^ 2 / 2) + 3 * Fsum L D 1 (1 - s ^ 2 / 2) (1 - s ^ 2 / 2))) :
    ∀ t : ℝ, -1 ≤ t → t ≤ 5373 / 10000 →
      a0 + a1 * t + 3 * Fsum L D 1 t t ≤ (1 - 18 * lam) * (Real.sqrt (2 - 2 * t))⁻¹ := by
  intro t ht1 ht2
  set s := Real.sqrt (2 - 2 * t) with hs
  have h2t : 0 ≤ 2 - 2 * t := by linarith
  have hs2 : s ^ 2 = 2 - 2 * t := Real.sq_sqrt h2t
  have hspos : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hslo : 9619 / 10000 ≤ s := by
    rw [hs, Real.le_sqrt (by norm_num) h2t]; linarith
  have hshi : s ≤ 2 := by
    rw [hs, Real.sqrt_le_left (by norm_num)]; linarith
  have ht : t = 1 - s ^ 2 / 2 := by linarith
  have key := h s hslo hshi
  rw [← ht] at key
  rw [le_mul_inv_iff₀ hspos]
  linarith

/-- The `tri` obligation as a polynomial inequality in the three chord lengths `p, q, r`:
`λ(qr + pr + pq) − pqr·F ≥ 0` where `u = 1 − p²/2` etc., for chords in `[0.9619, 2]`.
The certificate is *not* nonnegative on the larger range `[24/25, 2]³` (`Thomson.TriangleGlobal.Domain`):
the chord bound has to be the true one, `(9619/10000)² ≤ 2 − 2·(5373/10000)`. -/
theorem tri_of_poly (L : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ)
    (D : (k : Fin 6) → Fin (9 - (k : ℕ)) → ℝ) (lam : ℝ)
    (h : ∀ p q r : ℝ, 9619 / 10000 ≤ p → 9619 / 10000 ≤ q → 9619 / 10000 ≤ r → p ≤ 2 → q ≤ 2 → r ≤ 2 →
      0 ≤ 1 + 2 * (1 - p ^ 2 / 2) * (1 - q ^ 2 / 2) * (1 - r ^ 2 / 2)
          - (1 - p ^ 2 / 2) ^ 2 - (1 - q ^ 2 / 2) ^ 2 - (1 - r ^ 2 / 2) ^ 2 →
      0 ≤ lam * (q * r + p * r + p * q)
          - p * q * r * Fsum L D (1 - p ^ 2 / 2) (1 - q ^ 2 / 2) (1 - r ^ 2 / 2)) :
    ∀ u v t : ℝ, -1 ≤ u → -1 ≤ v → -1 ≤ t →
      u ≤ 5373 / 10000 → v ≤ 5373 / 10000 → t ≤ 5373 / 10000 →
      0 ≤ 1 + 2 * u * v * t - u ^ 2 - v ^ 2 - t ^ 2 →
      Fsum L D u v t ≤ lam * ((Real.sqrt (2 - 2 * u))⁻¹ + (Real.sqrt (2 - 2 * v))⁻¹
        + (Real.sqrt (2 - 2 * t))⁻¹) := by
  intro u v t hu1 hv1 ht1 hu2 hv2 ht2 hdet
  set p := Real.sqrt (2 - 2 * u) with hp
  set q := Real.sqrt (2 - 2 * v) with hq
  set r := Real.sqrt (2 - 2 * t) with hr
  have hp2 : p ^ 2 = 2 - 2 * u := Real.sq_sqrt (by linarith)
  have hq2 : q ^ 2 = 2 - 2 * v := Real.sq_sqrt (by linarith)
  have hr2 : r ^ 2 = 2 - 2 * t := Real.sq_sqrt (by linarith)
  have hpp : 0 < p := Real.sqrt_pos.mpr (by linarith)
  have hqp : 0 < q := Real.sqrt_pos.mpr (by linarith)
  have hrp : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hu : u = 1 - p ^ 2 / 2 := by linarith
  have hv : v = 1 - q ^ 2 / 2 := by linarith
  have ht : t = 1 - r ^ 2 / 2 := by linarith
  have lo : ∀ w : ℝ, w ≤ 5373 / 10000 → 9619 / 10000 ≤ Real.sqrt (2 - 2 * w) := fun w hw => by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hi : ∀ w : ℝ, -1 ≤ w → Real.sqrt (2 - 2 * w) ≤ 2 := fun w hw => by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  have key := h p q r (lo u hu2) (lo v hv2) (lo t ht2) (hi u hu1) (hi v hv1) (hi t ht1)
    (by rw [← hu, ← hv, ← ht]; exact hdet)
  rw [← hu, ← hv, ← ht] at key
  have hpqr : 0 < p * q * r := by positivity
  rw [inv_eq_one_div, inv_eq_one_div, inv_eq_one_div]
  rw [show lam * (1 / p + 1 / q + 1 / r) = lam * (q * r + p * r + p * q) / (p * q * r) by
    field_simp]
  rw [le_div_iff₀ hpqr]
  linarith

/-- The Gram determinant of three unit vectors in `ℝ³` is a square, hence nonnegative. -/
theorem gram_det_nonneg (x y z : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hz : ‖z‖ = 1) :
    0 ≤ 1 + 2 * ⟪x, y⟫ * ⟪x, z⟫ * ⟪y, z⟫ - ⟪x, y⟫ ^ 2 - ⟪x, z⟫ ^ 2 - ⟪y, z⟫ ^ 2 := by
  have hx' := normsq_coords x hx; have hy' := normsq_coords y hy; have hz' := normsq_coords z hz
  rw [inner_coords, inner_coords, inner_coords]
  have key : 1 + 2 * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2) * (x 0 * z 0 + x 1 * z 1 + x 2 * z 2)
        * (y 0 * z 0 + y 1 * z 1 + y 2 * z 2) - (x 0 * y 0 + x 1 * y 1 + x 2 * y 2) ^ 2
        - (x 0 * z 0 + x 1 * z 1 + x 2 * z 2) ^ 2 - (y 0 * z 0 + y 1 * z 1 + y 2 * z 2) ^ 2
      = (x 0 * (y 1 * z 2 - y 2 * z 1) - x 1 * (y 0 * z 2 - y 2 * z 0)
          + x 2 * (y 0 * z 1 - y 1 * z 0)) ^ 2 := by
    linear_combination
      (2*y 0^2*z 0^2 - y 0^2 + 2*y 0*y 1*z 0*z 1 + 2*y 0*y 2*z 0*z 2 - y 1^2*z 2^2
        + 2*y 1*y 2*z 1*z 2 - y 2^2*z 1^2 - z 0^2) * hx'
      + (2*x 0*x 1*z 0*z 1 + 2*x 0*x 2*z 0*z 2 - 2*x 1^2*z 0^2 - x 1^2*z 2^2 + x 1^2
        + 2*x 1*x 2*z 1*z 2 - 2*x 2^2*z 0^2 - x 2^2*z 1^2 + x 2^2 + z 0^2 - 1) * hy'
      + (2*x 0*x 1*y 0*y 1 + 2*x 0*x 2*y 0*y 2 + 2*x 1^2*y 1^2 + x 1^2*y 2^2 - x 1^2
        + 2*x 1*x 2*y 1*y 2 + x 2^2*y 1^2 + 2*x 2^2*y 2^2 - x 2^2 - y 1^2 - y 2^2) * hz'
  rw [key]; positivity

/-- Splitting a triple sum by coincidences of the indices. -/
theorem sum_triple_split {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ l, f i j l
      = ∑ i, f i i i + ∑ i, ∑ j ∈ univ.erase i, (f i i j + f i j i + f i j j)
        + ∑ i, ∑ j ∈ univ.erase i, ∑ l ∈ (univ.erase i).erase j, f i j l := by
  have inner : ∀ i j, j ≠ i →
      ∑ l, f i j l = f i j i + f i j j + ∑ l ∈ (univ.erase i).erase j, f i j l := by
    intro i j hji
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)]
    ring
  have mid : ∀ i, ∑ j, ∑ l, f i j l
      = (f i i i + ∑ l ∈ univ.erase i, f i i l)
        + ∑ j ∈ univ.erase i, (f i j i + f i j j + ∑ l ∈ (univ.erase i).erase j, f i j l) := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    exact Finset.sum_congr rfl fun j hj => inner i j (Finset.ne_of_mem_erase hj)
  simp only [mid, Finset.sum_add_distrib]
  ring

/-- Pulling an outer index through a triple sum. -/
theorem sum_swap_out {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → ι → ι → κ → ℝ) :
    ∑ i, ∑ j, ∑ l, ∑ k, f i j l k = ∑ k, ∑ i, ∑ j, ∑ l, f i j l k := by
  have e1 : ∀ i j, ∑ l, ∑ k, f i j l k = ∑ k, ∑ l, f i j l k := fun i j => Finset.sum_comm
  have e2 : ∀ i, ∑ j, ∑ k, ∑ l, f i j l k = ∑ k, ∑ j, ∑ l, f i j l k := fun i => Finset.sum_comm
  have e3 : ∑ i, ∑ k, ∑ j, ∑ l, f i j l k = ∑ k, ∑ i, ∑ j, ∑ l, f i j l k := Finset.sum_comm
  rw [← e3]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e2]
  exact Finset.sum_congr rfl fun j _ => e1 i j

/-- Over the distinct ordered triples, the three edge sums coincide. -/
theorem sum_distinct_swap23 {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ι → ℝ) :
    ∑ i, ∑ j ∈ univ.erase i, ∑ l ∈ (univ.erase i).erase j, g i l
      = ∑ i, ∑ j ∈ univ.erase i, ∑ l ∈ (univ.erase i).erase j, g i j := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm' (t' := univ.erase i) (s' := fun l => (univ.erase i).erase l)]
  intro j l
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  tauto

theorem sum_distinct_swap12 {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ι → ℝ) :
    ∑ i, ∑ j ∈ univ.erase i, ∑ l ∈ (univ.erase i).erase j, g j l
      = ∑ i, ∑ j ∈ univ.erase i, ∑ l ∈ (univ.erase i).erase j, g i l := by
  rw [Finset.sum_comm' (t' := univ) (s' := fun j => univ.erase j)]
  · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.erase_right_comm]
  · intro i j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, true_and]
    exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem sum_distinct_const {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ι → ℝ) :
    ∑ i, ∑ j ∈ univ.erase i, ∑ l ∈ (univ.erase i).erase j, g i j
      = ((Fintype.card ι : ℝ) - 2) * ∑ i, ∑ j ∈ univ.erase i, g i j := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.sum_const, Finset.card_erase_of_mem hj, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, nsmul_eq_mul]
  have : 2 ≤ Fintype.card ι := by
    have := Finset.card_pos.mpr ⟨j, hj⟩
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ] at this
    omega
  push_cast [Nat.cast_sub (by omega : 1 ≤ Fintype.card ι), Nat.cast_sub (by omega : 1 ≤ Fintype.card ι - 1)]
  ring

/-- **The three-point bound** (blueprint §12.2).  Any certificate bounds the energy of every
configuration whose pairwise inner products stay in the certified range. -/
theorem three_point_bound (C : ThreePointCert) (x : Fin 8 → EuclideanSpace ℝ (Fin 3))
    (hx : Admissible x) (hsep : ∀ i j, i ≠ j → ⟪x i, x j⟫ ≤ 5373 / 10000) :
    (64 * C.a0 - 8 * (C.a0 + C.a1) - 8 * Fsum C.L C.D 1 1 1) / 2 ≤ energy x := by
  obtain ⟨hsph, -⟩ := hx
  -- notation
  set F : ℝ → ℝ → ℝ → ℝ := Fsum C.L C.D with hF
  set t : Fin 8 → Fin 8 → ℝ := fun i j => ⟪x i, x j⟫ with ht
  set h : Fin 8 → Fin 8 → ℝ := fun i j => ‖x i - x j‖⁻¹ with hh
  have htt : ∀ i, t i i = 1 := fun i => by
    simp only [ht, real_inner_self_eq_norm_sq, hsph i, one_pow]
  have hsym : ∀ i j, t j i = t i j := fun i j => real_inner_comm _ _
  have hge : ∀ i j, -1 ≤ t i j := fun i j => by
    have := abs_real_inner_le_norm (x i) (x j)
    rw [hsph i, hsph j, one_mul] at this
    exact (abs_le.mp this).1
  have hsqrt : ∀ i j, (Real.sqrt (2 - 2 * t i j))⁻¹ = h i j := fun i j => by
    have := inner_eq_of_norm (x i) (x j) (hsph i) (hsph j)
    simp only [ht, hh]
    rw [this, show 2 - 2 * (1 - ‖x i - x j‖ ^ 2 / 2) = ‖x i - x j‖ ^ 2 by ring,
      Real.sqrt_sq (norm_nonneg _)]
  -- (1) Bachoc–Vallentin positivity, weighted by the certificate
  have hBV : 0 ≤ ∑ i, ∑ j, ∑ l, F (t i j) (t i l) (t j l) := by
    simp only [hF, Fsum]
    rw [sum_swap_out]
    refine Finset.sum_nonneg fun k _ => ?_
    rw [sum_swap_out]
    refine Finset.sum_nonneg fun r _ => ?_
    simp only [← Finset.mul_sum]
    exact mul_nonneg (C.D_nonneg k r) (bv_positivity k x hsph (C.L k r))
  -- (2) split by coincidences
  rw [sum_triple_split] at hBV
  -- (3a) the two-equal terms, from the pair inequality
  have hpair : ∀ i j, j ≠ i → F (t i i) (t i j) (t i j) + F (t i j) (t i i) (t j i)
      + F (t i j) (t i j) (t j j) ≤ (1 - 18 * C.lam) * h i j - C.a0 - C.a1 * t i j := by
    intro i j hji
    have h1 := C.pair (t i j) (hge i j) (hsep i j (Ne.symm hji))
    rw [hsqrt] at h1
    have e1 : F (t i j) (t i i) (t j i) = F (t i i) (t i j) (t i j) := by
      rw [hsym, htt, hF, Fsum_swap12]
    have e2 : F (t i j) (t i j) (t j j) = F (t i i) (t i j) (t i j) := by
      rw [htt, htt, hF, Fsum_swap23, Fsum_swap12]
    rw [e1, e2, htt]
    linarith
  -- (3b) the distinct terms, from the triangle inequality
  have htri : ∀ i j l, j ≠ i → l ≠ i → l ≠ j →
      F (t i j) (t i l) (t j l) ≤ C.lam * (h i j + h i l + h j l) := by
    intro i j l hji hli hlj
    have := C.tri (t i j) (t i l) (t j l) (hge i j) (hge i l) (hge j l)
      (hsep i j (Ne.symm hji)) (hsep i l (Ne.symm hli)) (hsep j l (Ne.symm hlj))
      (gram_det_nonneg (x i) (x j) (x l) (hsph i) (hsph j) (hsph l))
    rwa [hsqrt, hsqrt, hsqrt] at this
  -- (4) sum the bounds
  have hdiag : ∑ i : Fin 8, F (t i i) (t i i) (t i i) = 8 * F 1 1 1 := by
    simp only [htt, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hmid : ∑ i, ∑ j ∈ univ.erase i, (F (t i i) (t i j) (t i j) + F (t i j) (t i i) (t j i)
        + F (t i j) (t i j) (t j j))
      ≤ ∑ i, ∑ j ∈ univ.erase i, ((1 - 18 * C.lam) * h i j - C.a0 - C.a1 * t i j) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj)
  have hdist : ∑ i, ∑ j ∈ univ.erase i, ∑ l ∈ (univ.erase i).erase j, F (t i j) (t i l) (t j l)
      ≤ ∑ i, ∑ j ∈ univ.erase i, ∑ l ∈ (univ.erase i).erase j,
          C.lam * (h i j + h i l + h j l) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun l hl =>
      htri i j l (Finset.ne_of_mem_erase hj) (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl))
        (Finset.ne_of_mem_erase hl)
  -- the distinct edge sums
  set A : ℝ := ∑ i, ∑ j ∈ univ.erase i, h i j with hA
  have hE : energy x = (1 / 2) * A := energy_eq_half x
  have hdist' : ∑ i, ∑ j ∈ univ.erase i, ∑ l ∈ (univ.erase i).erase j,
      C.lam * (h i j + h i l + h j l) = C.lam * (18 * A) := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [sum_distinct_swap23 h, sum_distinct_swap12 h, sum_distinct_swap23 h, sum_distinct_const h]
    simp only [Fintype.card_fin]; push_cast; ring
  -- Schoenberg at degree 1
  set T : ℝ := ∑ i, ∑ j ∈ univ.erase i, t i j with hT
  have hT8 : -8 ≤ T := by
    have h0 := sum_P1_nonneg x
    have hsplit : ∑ i, ∑ j, ⟪x i, x j⟫ = ∑ i, (t i i + ∑ j ∈ univ.erase i, t i j) :=
      Finset.sum_congr rfl fun i _ => (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    rw [hsplit] at h0
    simp only [htt, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h0
    push_cast at h0
    linarith
  have hmid' : ∑ i, ∑ j ∈ univ.erase i, ((1 - 18 * C.lam) * h i j - C.a0 - C.a1 * t i j)
      = (1 - 18 * C.lam) * A - 56 * C.a0 - C.a1 * T := by
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have ha1T : -8 * C.a1 ≤ C.a1 * T := by nlinarith [C.a1_nonneg, hT8]
  rw [hdiag] at hBV
  rw [hE]
  linarith [hBV, hmid, hdist, hdist', hmid', ha1T]

end Thomson
