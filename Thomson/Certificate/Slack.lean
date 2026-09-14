import Thomson.Certificate.Linear
import Thomson.Antiprism.SharpChords
import Thomson.Antiprism.Derivative

/-! # Task 1c, part 1: the slack identity along the antiprism family

For a pivot vector `p` and the square antiprism at parameter `u` (`u = h²`, `antiprism h`), the
three-point bound is an *identity* once its inequalities are written as sums of slacks
(blueprint §12.2):

`2·E(u) − (64a₀ − 8(a₀ + a₁) − 8F(1,1,1)) = pairSum p u + triSum p u + bvTerm p u`,

where, with the multiplicities `A 8, D 4, N 8, F 8` of the four chord lengths and
`FFA 8, FDN 16, FNA 16, DAA 8, NNA 8` of the five triangle types,

* `pairSum p u = 2·Σ_X mult_X · pairP p s_X / s_X`,
* `triSum p u = 6·Σ_m mult_m · triP p τ_m / (abc)(τ_m)`,
* `bvTerm p u = Σ_k ⟨Hp p k, B_kᵀ Acomb_k(u) B_k⟩`, where `Acomb_k(u)` is the sum of
  `S3_k(⟪xᵢ,xⱼ⟫, ⟪xᵢ,xₗ⟫, ⟪xⱼ,xₗ⟫)` over all ordered triples of points, grouped by type.

Nothing here is specific to the certificate: the identity holds for every `p` and every
`u ∈ [0, 1)`.  It is bookkeeping — every unordered pair lies in six triangles, and the inner
products of the antiprism sum to `−4` (`Σᵢ xᵢ = 0`).  The certificate enters in
`Thomson.Certificate.Redundant`, together with the kernel lemma (`Thomson.Certificate.Kernel`):
`bvTerm p` has a double zero at `u*` for every `p`. -/

namespace Thomson
open Finset Matrix

/-! ## The family -/

/-- Half the splitting of the two cross chords: their inner products are `−u ± cU u`. -/
noncomputable def cU (u : ℝ) : ℝ := Real.sqrt 2 * (1 - u) / 2

theorem cU_sq (u : ℝ) : cU u ^ 2 = (1 - u) ^ 2 / 2 := by
  unfold cU; rw [div_pow, mul_pow, sqrt2_sq]; ring

/-- The four inner products of the antiprism at parameter `u`: square edge `A`, square diagonal
`D`, near cross chord `N`, far cross chord `F`. -/
noncomputable def tA (u : ℝ) : ℝ := u
noncomputable def tD (u : ℝ) : ℝ := 2 * u - 1
noncomputable def tN (u : ℝ) : ℝ := -u + cU u
noncomputable def tF (u : ℝ) : ℝ := -u - cU u

/-- The four chord lengths at parameter `u` (`chord` at `u = u*`). -/
noncomputable def chA (u : ℝ) : ℝ := Real.sqrt 2 * Real.sqrt (1 - u)
noncomputable def chD (u : ℝ) : ℝ := 2 * Real.sqrt (1 - u)
noncomputable def chN (u : ℝ) : ℝ := Real.sqrt (2 + 2 * u - Real.sqrt 2 * (1 - u))
noncomputable def chF (u : ℝ) : ℝ := Real.sqrt (2 + 2 * u + Real.sqrt 2 * (1 - u))

theorem chA_uStar : chA uStar = chord 0 := by simp [chA, chord, rStar]
theorem chD_uStar : chD uStar = chord 1 := by simp [chD, chord, rStar]
theorem chN_uStar : chN uStar = chord 2 := by simp [chN, chord, s2Star]
theorem chF_uStar : chF uStar = chord 3 := by simp [chF, chord, s4Star]

section family
variable {u : ℝ}

theorem cross_pos (hu0 : 0 ≤ u) (_hu1 : u ≤ 1) : 0 < 2 + 2 * u - Real.sqrt 2 * (1 - u) := by
  have h1 := sqrt2_lt_two; have h2 := sqrt2_pos
  nlinarith

theorem chA_pos (hu1 : u < 1) : 0 < chA u := mul_pos sqrt2_pos (Real.sqrt_pos.mpr (by linarith))
theorem chD_pos (hu1 : u < 1) : 0 < chD u := mul_pos two_pos (Real.sqrt_pos.mpr (by linarith))
theorem chN_pos (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : 0 < chN u := Real.sqrt_pos.mpr (cross_pos hu0 hu1)
theorem chF_pos (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : 0 < chF u := by
  have := cross_pos hu0 hu1; have h2 := sqrt2_pos
  exact Real.sqrt_pos.mpr (by nlinarith)

theorem chA_inner (hu1 : u ≤ 1) : 1 - chA u ^ 2 / 2 = tA u := by
  rw [chA, mul_pow, sqrt2_sq, Real.sq_sqrt (by linarith), tA]; ring
theorem chD_inner (hu1 : u ≤ 1) : 1 - chD u ^ 2 / 2 = tD u := by
  rw [chD, mul_pow, Real.sq_sqrt (by linarith), tD]; ring
theorem chN_inner (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : 1 - chN u ^ 2 / 2 = tN u := by
  rw [chN, Real.sq_sqrt (cross_pos hu0 hu1).le, tN, cU]; ring
theorem chF_inner (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : 1 - chF u ^ 2 / 2 = tF u := by
  have := cross_pos hu0 hu1; have h2 := sqrt2_pos
  rw [chF, Real.sq_sqrt (by nlinarith), tF, cU]; ring

/-- The antiprism's inner products sum to `−4` (its centroid is the origin). -/
theorem inner_sum (u : ℝ) : 8 * tA u + 4 * tD u + 8 * tN u + 8 * tF u = -4 := by
  unfold tA tD tN tF; ring

/-- The energy of the antiprism as a sum over the four chord lengths. -/
theorem antiprismEnergy_eq_chords (_hu0 : 0 ≤ u) (hu1 : u < 1) :
    antiprismEnergy u = 8 / chA u + 4 / chD u + 8 / chN u + 8 / chF u := by
  have hr : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.mpr (by linarith)
  have hs := sqrt2_pos
  have e2 : (2 - Real.sqrt 2) + (2 + Real.sqrt 2) * u = 2 + 2 * u - Real.sqrt 2 * (1 - u) := by ring
  have e3 : (2 + Real.sqrt 2) + (2 - Real.sqrt 2) * u = 2 + 2 * u + Real.sqrt 2 * (1 - u) := by ring
  unfold antiprismEnergy chA chD chN chF
  rw [e2, e3]
  have key : (4 * Real.sqrt 2 + 2) * (Real.sqrt (1 - u))⁻¹
      = 8 / (Real.sqrt 2 * Real.sqrt (1 - u)) + 4 / (2 * Real.sqrt (1 - u)) := by
    field_simp
    nlinarith [sqrt2_sq]
  rw [key]; ring

end family

/-! ## The three sums -/

/-- The pair slacks: `2·Σ_X mult_X · pairP p s_X / s_X`. -/
noncomputable def pairSum (p : Fin 24 → ℝ) (u : ℝ) : ℝ :=
  2 * (8 * (pairP p (chA u) / chA u) + 4 * (pairP p (chD u) / chD u)
    + 8 * (pairP p (chN u) / chN u) + 8 * (pairP p (chF u) / chF u))

/-- The triangle slacks: `6·Σ_m mult_m · triP p τ_m / (abc)`, over `FFA, FDN, FNA, DAA, NNA`
(the order of `touchType`). -/
noncomputable def triSum (p : Fin 24 → ℝ) (u : ℝ) : ℝ :=
  6 * (8 * (triP p (chF u) (chF u) (chA u) / (chF u * chF u * chA u))
    + 16 * (triP p (chF u) (chD u) (chN u) / (chF u * chD u * chN u))
    + 16 * (triP p (chF u) (chN u) (chA u) / (chF u * chN u * chA u))
    + 8 * (triP p (chD u) (chA u) (chA u) / (chD u * chA u * chA u))
    + 8 * (triP p (chN u) (chN u) (chA u) / (chN u * chN u * chA u)))

/-- `Σ_{i,j,l} S3_k(⟪xᵢ,xⱼ⟫, ⟪xᵢ,xₗ⟫, ⟪xⱼ,xₗ⟫)` over the antiprism at parameter `u`, grouped by
the type of the triple: `i = j = l` (8), two equal (`6·mult_X` for each chord), all distinct
(`6·mult_m` for each triangle type). -/
noncomputable def Acomb (k : ℕ) (u : ℝ) : Matrix (Fin (9 - k)) (Fin (9 - k)) ℝ :=
  (8 : ℝ) • S3 k 1 1 1
    + (48 : ℝ) • S3 k 1 (tA u) (tA u) + (24 : ℝ) • S3 k 1 (tD u) (tD u)
    + (48 : ℝ) • S3 k 1 (tN u) (tN u) + (48 : ℝ) • S3 k 1 (tF u) (tF u)
    + (48 : ℝ) • S3 k (tF u) (tF u) (tA u) + (96 : ℝ) • S3 k (tF u) (tD u) (tN u)
    + (96 : ℝ) • S3 k (tF u) (tN u) (tA u) + (48 : ℝ) • S3 k (tD u) (tA u) (tA u)
    + (48 : ℝ) • S3 k (tN u) (tN u) (tA u)

/-- The `(a, b)` entry of `B_kᵀ Acomb_k(u) B_k`. -/
noncomputable def psi (k : Fin 6) (a b : Fin (9 - (k : ℕ))) (u : ℝ) : ℝ :=
  ((B k)ᵀ * Acomb (k : ℕ) u * B k) a b

/-- The Bachoc–Vallentin term: `Σ_k ⟨Hp p k, B_kᵀ Acomb_k(u) B_k⟩`. -/
noncomputable def bvTerm (p : Fin 24 → ℝ) (u : ℝ) : ℝ :=
  ∑ k : Fin 6, ∑ a, ∑ b, Hp p k a b * psi k a b u

/-- `bvTerm` is the sum of `F` over all ordered triples of points: `F` is linear in `S3`. -/
theorem bvTerm_eq (p : Fin 24 → ℝ) (u : ℝ) :
    bvTerm p u = 8 * Fh (Hp p) 1 1 1
      + 48 * Fh (Hp p) 1 (tA u) (tA u) + 24 * Fh (Hp p) 1 (tD u) (tD u)
      + 48 * Fh (Hp p) 1 (tN u) (tN u) + 48 * Fh (Hp p) 1 (tF u) (tF u)
      + 48 * Fh (Hp p) (tF u) (tF u) (tA u) + 96 * Fh (Hp p) (tF u) (tD u) (tN u)
      + 96 * Fh (Hp p) (tF u) (tN u) (tA u) + 48 * Fh (Hp p) (tD u) (tA u) (tA u)
      + 48 * Fh (Hp p) (tN u) (tN u) (tA u) := by
  unfold bvTerm psi Acomb Fh
  simp only [Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [mul_left_comm]

/-! ## The identity -/

theorem pairP_div (p : Fin 24 → ℝ) {s : ℝ} (hs : s ≠ 0) :
    pairP p s / s = (1 - 18 * lamFix) / s
      - (a0Fix + a1Fix * (1 - s ^ 2 / 2) + 3 * Fh (Hp p) 1 (1 - s ^ 2 / 2) (1 - s ^ 2 / 2)) := by
  unfold pairP; field_simp

theorem triP_div (p : Fin 24 → ℝ) {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    triP p a b c / (a * b * c) = lamFix * (1 / a + 1 / b + 1 / c)
      - Fh (Hp p) (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c ^ 2 / 2) := by
  unfold triP; field_simp

/-- **The slack identity** along the antiprism family, for every pivot vector `p`. -/
theorem slack_identity (p : Fin 24 → ℝ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    2 * antiprismEnergy u - (64 * a0Fix - 8 * (a0Fix + a1Fix) - 8 * Fh (Hp p) 1 1 1)
      = pairSum p u + triSum p u + bvTerm p u := by
  have hA := (chA_pos hu1).ne'; have hD := (chD_pos hu1).ne'
  have hN := (chN_pos hu0 hu1.le).ne'; have hF := (chF_pos hu0 hu1.le).ne'
  rw [antiprismEnergy_eq_chords hu0 hu1, bvTerm_eq]
  unfold pairSum triSum
  rw [pairP_div p hA, pairP_div p hD, pairP_div p hN, pairP_div p hF,
    triP_div p hF hF hA, triP_div p hF hD hN, triP_div p hF hN hA, triP_div p hD hA hA,
    triP_div p hN hN hA]
  rw [chA_inner hu1.le, chD_inner hu1.le, chN_inner hu0 hu1.le, chF_inner hu0 hu1.le]
  linear_combination (2 * a1Fix) * inner_sum u

/-! ## Double zeros -/

/-- `f` has a double zero at `x₀`: `f u = (u − x₀)²·g u` with `g` differentiable.  The kernel
lemma says that `bvTerm p` has one at `u*`, for every `p`. -/
def DoubleZero (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∃ g : ℝ → ℝ, Differentiable ℝ g ∧ ∀ u, f u = (u - x₀) ^ 2 * g u

namespace DoubleZero
variable {f g : ℝ → ℝ} {x₀ : ℝ}

theorem eq_zero (h : DoubleZero f x₀) : f x₀ = 0 := by
  obtain ⟨g, -, hg⟩ := h; rw [hg]; ring

theorem hasDerivAt (h : DoubleZero f x₀) : HasDerivAt f 0 x₀ := by
  obtain ⟨g, hd, hg⟩ := h
  have h1 : HasDerivAt (fun u => (u - x₀) ^ 2) (↑2 * (x₀ - x₀) ^ (2 - 1) * 1) x₀ :=
    ((hasDerivAt_id x₀).sub_const x₀).fun_pow 2
  have h2 := h1.fun_mul (hd x₀).hasDerivAt
  rw [show f = fun u => (u - x₀) ^ 2 * g u from funext hg]
  exact h2.congr_deriv (by ring)

theorem zero : DoubleZero (fun _ => 0) x₀ := ⟨fun _ => 0, differentiable_const _, fun _ => by ring⟩

theorem add (hf : DoubleZero f x₀) (hg : DoubleZero g x₀) : DoubleZero (fun u => f u + g u) x₀ := by
  obtain ⟨F, hF, hf⟩ := hf; obtain ⟨G, hG, hg⟩ := hg
  exact ⟨fun u => F u + G u, hF.add hG, fun u => by simp only [hf, hg]; ring⟩

theorem const_mul (c : ℝ) (hf : DoubleZero f x₀) : DoubleZero (fun u => c * f u) x₀ := by
  obtain ⟨F, hF, hf⟩ := hf
  exact ⟨fun u => c * F u, hF.const_mul c, fun u => by simp only [hf]; ring⟩

theorem sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} (h : ∀ i ∈ s, DoubleZero (f i) x₀) :
    DoubleZero (fun u => ∑ i ∈ s, f i u) x₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (x₀ := x₀))
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end DoubleZero

end Thomson
