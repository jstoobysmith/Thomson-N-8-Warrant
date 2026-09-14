import Thomson.Numerics.Poly

/-! # Task 5a, numeric side, step 2: coefficients, derivatives at `0`, majorants

Along a ray, `triP` is a polynomial in the ray parameter, handled as a coefficient list
(`Thomson.Numerics.Poly`).  This file adds what the certificate needs about such lists:

* `getD_radd`, `getD_rmul` — the coefficients of a sum and of a product (`Σ_{i ≤ n} pᵢ q_{n−i}`);
* `reval_rder_iter_zero` — the `k`-th derivative at `0` is `k! · p_k`;
* `WMaj s P p` — *weighted majorant*: `|p_n| ≤ P_n sⁿ`; preserved by sums and products, it bounds
  the fourth derivative on `[0, 1]` uniformly in the direction (`abs_rder4_le`). -/

namespace Thomson.TriLocalCert

open Thomson.Pair Finset

/-- The coefficient of `xⁿ`. -/
noncomputable def co (p : List ℝ) (n : ℕ) : ℝ := p.getD n 0

@[simp] theorem co_nil (n : ℕ) : co [] n = 0 := by simp [co]
@[simp] theorem co_cons_zero (a : ℝ) (p : List ℝ) : co (a :: p) 0 = a := by simp [co]
@[simp] theorem co_cons_succ (a : ℝ) (p : List ℝ) (n : ℕ) : co (a :: p) (n + 1) = co p n := by
  simp [co]

theorem co_radd : ∀ (p q : List ℝ) (n : ℕ), co (radd p q) n = co p n + co q n
  | [], q, n => by simp [radd]
  | a :: p, [], n => by simp [radd]
  | a :: p, b :: q, 0 => by simp [radd]
  | a :: p, b :: q, n + 1 => by simp only [radd, co_cons_succ]; exact co_radd p q n

theorem co_rsmul (c : ℝ) : ∀ (p : List ℝ) (n : ℕ), co (rsmul c p) n = c * co p n
  | [], n => by simp [rsmul]
  | a :: p, 0 => by simp [rsmul]
  | a :: p, n + 1 => by
      have := co_rsmul c p n
      simpa [rsmul] using this

/-- **The coefficients of a product.** -/
theorem co_rmul : ∀ (p q : List ℝ) (n : ℕ),
    co (rmul p q) n = ∑ i ∈ range (n + 1), co p i * co q (n - i)
  | [], q, n => by simp [rmul]
  | a :: p, q, 0 => by simp [rmul, co_radd, co_rsmul]
  | a :: p, q, n + 1 => by
      rw [rmul, co_radd, co_rsmul, co_cons_succ, co_rmul p q n, Finset.sum_range_succ' _ (n + 1)]
      simp only [co_cons_succ, co_cons_zero, Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      ring

/-- The coefficients of the derivative. -/
theorem co_rder : ∀ (p : List ℝ) (n : ℕ), co (rder p) n = (n + 1) * co p (n + 1)
  | [], n => by simp [rder]
  | [a], n => by simp [rder]
  | a :: b :: p, 0 => by simp [rder, co_radd]
  | a :: b :: p, n + 1 => by
      simp only [rder, co_radd, co_cons_succ]
      rw [co_rder (b :: p) n, co_cons_succ]
      push_cast
      ring

theorem reval_zero (p : List ℝ) : reval p 0 = co p 0 := by
  cases p <;> simp

/-- The `k`-th derivative list. -/
noncomputable def rderN : ℕ → List ℝ → List ℝ
  | 0, p => p
  | k + 1, p => rder (rderN k p)

theorem co_rderN (p : List ℝ) : ∀ (k n : ℕ),
    co (rderN k p) n = (∏ i ∈ range k, ((n + 1 + i : ℕ) : ℝ)) * co p (n + k)
  | 0, n => by simp [rderN]
  | k + 1, n => by
      rw [rderN, co_rder, co_rderN p k (n + 1), Finset.prod_range_succ']
      simp only [add_zero]
      have e : n + 1 + k = n + (k + 1) := by omega
      rw [e]
      have e2 : ∀ i, (n + 1 + i : ℕ) = n + (i + 1) + 1 - 1 + 0 := fun i => by omega
      have e3 : ∏ i ∈ range k, ((n + 1 + 1 + i : ℕ) : ℝ) = ∏ i ∈ range k, ((n + 1 + (i + 1) : ℕ) : ℝ) :=
        Finset.prod_congr rfl fun i _ => by congr 1; omega
      rw [e3]
      push_cast
      ring

/-- **The `k`-th derivative at `0` is `k!` times the `k`-th coefficient.** -/
theorem reval_rderN_zero (p : List ℝ) (k : ℕ) : reval (rderN k p) 0 = (k.factorial : ℝ) * co p k := by
  rw [reval_zero, co_rderN p k 0, show 0 + k = k from Nat.zero_add k]
  congr 1
  rw [← Finset.prod_range_add_one_eq_factorial]
  push_cast
  exact Finset.prod_congr rfl fun i _ => by ring

/-! ## Weighted majorants -/

/-- `|p_n| ≤ P_n · sⁿ` for every `n` (`P` has nonnegative coefficients). -/
def WMaj (s : ℝ) (P p : List ℝ) : Prop := (∀ n, 0 ≤ co P n) ∧ ∀ n, |co p n| ≤ co P n * s ^ n

theorem WMaj.radd {s : ℝ} {P Q p q : List ℝ} (hp : WMaj s P p) (hq : WMaj s Q q) :
    WMaj s (radd P Q) (radd p q) := by
  refine ⟨fun n => by rw [co_radd]; exact add_nonneg (hp.1 n) (hq.1 n), fun n => ?_⟩
  rw [co_radd, co_radd, add_mul]
  exact (abs_add_le _ _).trans (add_le_add (hp.2 n) (hq.2 n))

theorem WMaj.rsmul {s : ℝ} {P p : List ℝ} {c C : ℝ} (hc : |c| ≤ C) (hp : WMaj s P p) :
    WMaj s (Pair.rsmul C P) (Pair.rsmul c p) := by
  have hC : 0 ≤ C := (abs_nonneg c).trans hc
  refine ⟨fun n => by rw [co_rsmul]; exact mul_nonneg hC (hp.1 n), fun n => ?_⟩
  rw [co_rsmul, co_rsmul, abs_mul, mul_assoc]
  exact mul_le_mul hc (hp.2 n) (abs_nonneg _) hC

theorem WMaj.rmul {s : ℝ} (hs : 0 ≤ s) {P Q p q : List ℝ} (hp : WMaj s P p) (hq : WMaj s Q q) :
    WMaj s (Pair.rmul P Q) (Pair.rmul p q) := by
  refine ⟨fun n => by
    rw [co_rmul]; exact Finset.sum_nonneg fun i _ => mul_nonneg (hp.1 i) (hq.1 _), fun n => ?_⟩
  rw [co_rmul, co_rmul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [abs_mul]
  calc |co p i| * |co q (n - i)| ≤ (co P i * s ^ i) * (co Q (n - i) * s ^ (n - i)) :=
        mul_le_mul (hp.2 i) (hq.2 _) (abs_nonneg _) (mul_nonneg (hp.1 i) (pow_nonneg hs _))
    _ = co P i * co Q (n - i) * s ^ n := by
        rw [show s ^ n = s ^ i * s ^ (n - i) by rw [← pow_add]; congr 1; omega]; ring

theorem co_eq_zero {p : List ℝ} {n : ℕ} (h : p.length ≤ n) : co p n = 0 := by
  simp [co, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-- Evaluation as a finite sum, over any range covering the list. -/
theorem reval_eq_sum : ∀ (p : List ℝ) (x : ℝ) (N : ℕ), p.length ≤ N →
    reval p x = ∑ n ∈ range N, co p n * x ^ n
  | [], x, N, _ => by simp
  | a :: p, x, 0, h => by simp at h
  | a :: p, x, N + 1, h => by
      rw [Finset.sum_range_succ', reval_cons, reval_eq_sum p x N (by simpa using h),
        Finset.mul_sum]
      simp only [co_cons_succ, co_cons_zero, pow_zero, mul_one, pow_succ]
      rw [add_comm]
      congr 1
      exact Finset.sum_congr rfl fun n _ => by ring

/-- **The fourth derivative on `[0, 1]`, uniformly in the direction.**  If `P` majorises `g` with
weight `s ≤ ρ`, then `|g⁗(x)| ≤ s⁴ · P⁗(ρ)` for `0 ≤ x ≤ 1`. -/
theorem abs_rder4_le {s ρ x : ℝ} (hs : 0 ≤ s) (hsρ : s ≤ ρ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {P g : List ℝ} (h : WMaj s P g) :
    |reval (rderN 4 g) x| ≤ s ^ 4 * reval (rderN 4 P) ρ := by
  set N := (rderN 4 g).length + (rderN 4 P).length
  rw [reval_eq_sum _ x N (by omega), reval_eq_sum _ ρ N (by omega), Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [co_rderN, co_rderN, abs_mul, abs_mul]
  set c : ℝ := ∏ i ∈ range 4, ((n + 1 + i : ℕ) : ℝ)
  have hc : 0 ≤ c := Finset.prod_nonneg fun i _ => by positivity
  have hxn : |x ^ n| ≤ 1 := by rw [abs_pow, abs_of_nonneg hx0]; exact pow_le_one₀ hx0 hx1
  have hsn : s ^ n ≤ ρ ^ n := pow_le_pow_left₀ hs hsρ n
  have hP := h.1 (n + 4)
  calc |c| * |co g (n + 4)| * |x ^ n| ≤ c * (co P (n + 4) * s ^ (n + 4)) * 1 := by
        rw [abs_of_nonneg hc]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (h.2 _) hc) hxn (abs_nonneg _)
          (mul_nonneg hc (mul_nonneg hP (pow_nonneg hs _)))
    _ = s ^ 4 * (c * co P (n + 4) * s ^ n) := by rw [pow_add]; ring
    _ ≤ s ^ 4 * (c * co P (n + 4) * ρ ^ n) := by
        gcongr
    _ = s ^ 4 * (c * co P (n + 4) * ρ ^ n) := rfl

end Thomson.TriLocalCert
