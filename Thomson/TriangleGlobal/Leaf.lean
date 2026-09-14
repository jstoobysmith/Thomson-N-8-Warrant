import Thomson.Numerics.TensorEngine
import Thomson.TriangleGlobal.Main

/-! # Task 5b, step 9: one box of the covering

Given the coefficient tensor of `F`, this file certifies one box: it assembles the polynomial

`P(u,v,t) = λ·(L(u) + L(v) + L(t)) − F(u,v,t) − σ·gram(u,v,t)`,

where `L` is the tangent-line minorant of `1/√(2−2·)` at a fixed-point chord `a₀ = n/SCALE`
(`inv_sqrt_tangent`) and `σ ≥ 0` is an S-procedure multiplier, shifts its tensor to the centre of
the box, and applies `TM.nonneg`.  Since `L ≤ 1/√(2−2·)` and `σ·gram ≥ 0` on the domain, `P ≥ 0`
gives the slack bound the covering needs. -/

namespace Thomson.Tri5b

open Thomson

/-! ### The Gram tensor -/

/-- `gram` as a real coefficient tensor. -/
noncomputable def gramRT : RT := fun i j k =>
  if (i : ℕ) = 0 ∧ (j : ℕ) = 0 ∧ (k : ℕ) = 0 then 1
  else if (i : ℕ) = 1 ∧ (j : ℕ) = 1 ∧ (k : ℕ) = 1 then 2
  else if (i : ℕ) = 2 ∧ (j : ℕ) = 0 ∧ (k : ℕ) = 0 then -1
  else if (i : ℕ) = 0 ∧ (j : ℕ) = 2 ∧ (k : ℕ) = 0 then -1
  else if (i : ℕ) = 0 ∧ (j : ℕ) = 0 ∧ (k : ℕ) = 2 then -1
  else 0

/-- the same, as fixed-point intervals -/
def gramIT : IT := fun i j k =>
  if (i : ℕ) = 0 ∧ (j : ℕ) = 0 ∧ (k : ℕ) = 0 then Itv.cst SCALE
  else if (i : ℕ) = 1 ∧ (j : ℕ) = 1 ∧ (k : ℕ) = 1 then Itv.cst (2 * SCALE)
  else if (i : ℕ) = 2 ∧ (j : ℕ) = 0 ∧ (k : ℕ) = 0 then Itv.cst (-SCALE)
  else if (i : ℕ) = 0 ∧ (j : ℕ) = 2 ∧ (k : ℕ) = 0 then Itv.cst (-SCALE)
  else if (i : ℕ) = 0 ∧ (j : ℕ) = 0 ∧ (k : ℕ) = 2 then Itv.cst (-SCALE)
  else Itv.zero

theorem ITMem_gram : ITMem gramIT gramRT := by
  intro i j k
  unfold gramIT gramRT
  have h1 : ((SCALE : ℤ) : ℝ) / SCALE = 1 := div_self (ne_of_gt SCALE_pos')
  have h2 : ((2 * SCALE : ℤ) : ℝ) / SCALE = 2 := by
    push_cast; rw [mul_div_assoc, div_self (ne_of_gt SCALE_pos'), mul_one]
  have h3 : ((-SCALE : ℤ) : ℝ) / SCALE = -1 := by
    push_cast; rw [neg_div, div_self (ne_of_gt SCALE_pos')]
  split_ifs
  · rw [← h1]; exact Itv.mem_cst _
  · rw [← h2]; exact Itv.mem_cst _
  · rw [← h3]; exact Itv.mem_cst _
  · rw [← h3]; exact Itv.mem_cst _
  · rw [← h3]; exact Itv.mem_cst _
  · exact Itv.mem_zero

set_option maxHeartbeats 2000000 in
theorem ev_gramRT (u v t : ℝ) : ev gramRT u v t = gramU u v t := by
  unfold ev gramRT gramU
  simp [Fin.sum_univ_succ]
  ring


/-! ### The tangent-line minorant, on the fixed-point grid -/

/-- `lamFix` on the grid. -/
def LAM : ℤ := 97932235147000000000000000000000000000

theorem mem_LAM : (Itv.cst LAM).Mem lamFix := by
  have h := Itv.mem_cst LAM
  have e : lamFix = ((LAM : ℤ) : ℝ) / SCALE := by
    unfold lamFix LAM SCALE; norm_num
  rw [e]; exact h

/-- The constant term of the tangent minorant at the chord `n/SCALE`. -/
noncomputable def tanA (n : ℤ) : ℝ :=
  ((SCALE * (3 * (n * n) - 2 * SCALE2) : ℤ) : ℝ) / ((2 * (n * n * n) : ℤ) : ℝ)
/-- Its slope. -/
noncomputable def tanB (n : ℤ) : ℝ := ((SCALE3 : ℤ) : ℝ) / ((n * n * n : ℤ) : ℝ)

theorem tan_le {n : ℤ} (hn : 0 < n) {u : ℝ} (hu : u < 1) :
    tanA n + tanB n * u ≤ (Real.sqrt (2 - 2 * u))⁻¹ := by
  have hS := SCALE_pos'
  have hn' : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h0 : (0:ℝ) < (n : ℝ) / SCALE := div_pos hn' hS
  have hx : (0:ℝ) < 2 - 2 * u := by linarith
  have key := inv_sqrt_tangent h0 hx
  have hid : tanA n + tanB n * u
      = 1 / ((n : ℝ) / SCALE) - ((2 - 2 * u) - ((n : ℝ) / SCALE) ^ 2)
          / (2 * ((n : ℝ) / SCALE) ^ 3) := by
    unfold tanA tanB
    rw [SCALE2_eq, SCALE3_eq]
    push_cast
    field_simp
    ring
  rw [hid]; exact key

/-- The affine minorant `λ(L(u)+L(v)+L(t))` as a real tensor. -/
noncomputable def tanRT (n1 n2 n3 : ℤ) : RT := fun i j k =>
  if (i : ℕ) = 0 ∧ (j : ℕ) = 0 ∧ (k : ℕ) = 0 then lamFix * (tanA n1 + tanA n2 + tanA n3)
  else if (i : ℕ) = 1 ∧ (j : ℕ) = 0 ∧ (k : ℕ) = 0 then lamFix * tanB n1
  else if (i : ℕ) = 0 ∧ (j : ℕ) = 1 ∧ (k : ℕ) = 0 then lamFix * tanB n2
  else if (i : ℕ) = 0 ∧ (j : ℕ) = 0 ∧ (k : ℕ) = 1 then lamFix * tanB n3
  else 0

/-- the same on the grid -/
def tanIT (n1 n2 n3 : ℤ) : IT := fun i j k =>
  if (i : ℕ) = 0 ∧ (j : ℕ) = 0 ∧ (k : ℕ) = 0 then
    Itv.mul (Itv.cst LAM)
      (Itv.add (Itv.add (Itv.ofDiv (SCALE * (3 * (n1 * n1) - 2 * SCALE2)) (2 * (n1 * n1 * n1)))
        (Itv.ofDiv (SCALE * (3 * (n2 * n2) - 2 * SCALE2)) (2 * (n2 * n2 * n2))))
        (Itv.ofDiv (SCALE * (3 * (n3 * n3) - 2 * SCALE2)) (2 * (n3 * n3 * n3))))
  else if (i : ℕ) = 1 ∧ (j : ℕ) = 0 ∧ (k : ℕ) = 0 then
    Itv.mul (Itv.cst LAM) (Itv.ofDiv SCALE3 (n1 * n1 * n1))
  else if (i : ℕ) = 0 ∧ (j : ℕ) = 1 ∧ (k : ℕ) = 0 then
    Itv.mul (Itv.cst LAM) (Itv.ofDiv SCALE3 (n2 * n2 * n2))
  else if (i : ℕ) = 0 ∧ (j : ℕ) = 0 ∧ (k : ℕ) = 1 then
    Itv.mul (Itv.cst LAM) (Itv.ofDiv SCALE3 (n3 * n3 * n3))
  else Itv.zero

theorem ITMem_tan {n1 n2 n3 : ℤ} (h1 : 0 < n1) (h2 : 0 < n2) (h3 : 0 < n3) :
    ITMem (tanIT n1 n2 n3) (tanRT n1 n2 n3) := by
  have p1 : (0:ℤ) < 2 * (n1 * n1 * n1) := by positivity
  have p2 : (0:ℤ) < 2 * (n2 * n2 * n2) := by positivity
  have p3 : (0:ℤ) < 2 * (n3 * n3 * n3) := by positivity
  have q1 : (0:ℤ) < n1 * n1 * n1 := by positivity
  have q2 : (0:ℤ) < n2 * n2 * n2 := by positivity
  have q3 : (0:ℤ) < n3 * n3 * n3 := by positivity
  intro i j k
  unfold tanIT tanRT
  split_ifs
  · exact Itv.mem_mul mem_LAM
      (Itv.mem_add (Itv.mem_add (Itv.mem_ofDiv p1) (Itv.mem_ofDiv p2)) (Itv.mem_ofDiv p3))
  · exact Itv.mem_mul mem_LAM (Itv.mem_ofDiv q1)
  · exact Itv.mem_mul mem_LAM (Itv.mem_ofDiv q2)
  · exact Itv.mem_mul mem_LAM (Itv.mem_ofDiv q3)
  · exact Itv.mem_zero

set_option maxHeartbeats 2000000 in
theorem ev_tanRT (n1 n2 n3 : ℤ) (u v t : ℝ) :
    ev (tanRT n1 n2 n3) u v t
      = lamFix * (tanA n1 + tanB n1 * u) + lamFix * (tanA n2 + tanB n2 * v)
        + lamFix * (tanA n3 + tanB n3 * t) := by
  unfold ev tanRT
  simp [Fin.sum_univ_succ]
  ring


set_option maxRecDepth 8000 in
/-- **One box of the covering.**  If the Taylor model of
`λ(L(u)+L(v)+L(t)) − F − σ·gram` extracted from the shifted tensor is nonnegative on the box, then
`F` is below the certificate's target there. -/
theorem leaf_sound {C : IT} {c : RT} (hC : ITMem C c)
    {n1 n2 n3 : ℤ} (hn1 : 0 < n1) (hn2 : 0 < n2) (hn3 : 0 < n3)
    {s : ℤ} (hs : 0 ≤ s) (mg : ℤ)
    (a b d h1 h2 h3 : ℤ) (hh1 : 0 < h1) (hh2 : 0 < h2) (hh3 : 0 < h3)
    (hcheck : TM.geBound mg (toTM (IshiftA (toITA (ITsub (ITsub (tanIT n1 n2 n3) C)
        (ITsmul (Itv.cst s) gramIT))).get a b d).get h1 h2 h3) = true)
    {u v t : ℝ}
    (hu : |u - (a : ℝ) / SCALE| ≤ (h1 : ℝ) / SCALE)
    (hv : |v - (b : ℝ) / SCALE| ≤ (h2 : ℝ) / SCALE)
    (ht : |t - (d : ℝ) / SCALE| ≤ (h3 : ℝ) / SCALE)
    (hu1 : u < 1) (hv1 : v < 1) (ht1 : t < 1) (hgram : 0 ≤ gramU u v t) :
    ev c u v t + (mg : ℝ) / SCALE ≤ lamFix * ((Real.sqrt (2 - 2 * u))⁻¹
      + (Real.sqrt (2 - 2 * v))⁻¹ + (Real.sqrt (2 - 2 * t))⁻¹) := by
  have hmem := ITMem_toITA (ITMem_sub (ITMem_sub (ITMem_tan hn1 hn2 hn3) hC)
      (ITMem_smul (Itv.mem_cst s) ITMem_gram))
  have hpos := box_sound hmem mg a b d h1 h2 h3 hh1 hh2 hh3 hcheck hu hv ht
  rw [ev_sub, ev_sub, ev_smul, ev_gramRT, ev_tanRT] at hpos
  have hσ : (0:ℝ) ≤ (s : ℝ) / SCALE := by
    apply div_nonneg _ (le_of_lt SCALE_pos'); exact_mod_cast hs
  have hlam : (0:ℝ) < lamFix := by unfold lamFix; norm_num
  have l1 := tan_le hn1 hu1
  have l2 := tan_le hn2 hv1
  have l3 := tan_le hn3 ht1
  have hprod : 0 ≤ (s : ℝ) / SCALE * gramU u v t := mul_nonneg hσ hgram
  have m1 := mul_le_mul_of_nonneg_left l1 hlam.le
  have m2 := mul_le_mul_of_nonneg_left l2 hlam.le
  have m3 := mul_le_mul_of_nonneg_left l3 hlam.le
  clear hcheck hmem l1 l2 l3
  linarith

end Thomson.Tri5b
