import Thomson.TriangleLocal.Patch

/-! # Task 5a, numeric side, step 5: polarization

A quadratic form `Q(δ) = Σ H_ab δ_a δ_b` is determined by its values on six directions, and a
cubic form `K(δ) = Σ C_abc δ_a δ_b δ_c` by its values on ten.  `Hpol Q` and `Cpol K` are the
*symmetric* coefficient tables recovered from those values; for a genuine quadratic (cubic) form
they represent the same form (`Qf (Hpol Q) = Q`, proved on Task 5a's side, where `Q` and `K` are the
second and third ray derivatives).  The values are taken on the ten directions `dirR`; the interval
versions (`HpolI`, `CpolI`) mirror the formulas operation by operation. -/

namespace Thomson.TriLocalCert

open Thomson.Tri5b

/-- The ten directions: `e₀, e₁, e₂, e₀+e₁, e₀+e₂, e₁+e₂, e₀−e₁, e₀−e₂, e₁−e₂, e₀+e₁+e₂`. -/
def dirZ : Fin 10 → Fin 3 → ℤ
  | 0 => ![1, 0, 0] | 1 => ![0, 1, 0] | 2 => ![0, 0, 1]
  | 3 => ![1, 1, 0] | 4 => ![1, 0, 1] | 5 => ![0, 1, 1]
  | 6 => ![1, -1, 0] | 7 => ![1, 0, -1] | 8 => ![0, 1, -1]
  | 9 => ![1, 1, 1]

/-- The directions in `ℝ`. -/
noncomputable def dirR (k : Fin 10) : Fin 3 → ℝ := fun a => (dirZ k a : ℝ)

/-- The symmetric table of a quadratic form, from its values `q k = Q (dirR k)`. -/
noncomputable def HpolV (q : Fin 10 → ℝ) : Fin 3 → Fin 3 → ℝ
  | 0, 0 => q 0 | 1, 1 => q 1 | 2, 2 => q 2
  | 0, 1 => (q 3 - q 0 - q 1) / 2 | 1, 0 => (q 3 - q 0 - q 1) / 2
  | 0, 2 => (q 4 - q 0 - q 2) / 2 | 2, 0 => (q 4 - q 0 - q 2) / 2
  | 1, 2 => (q 5 - q 1 - q 2) / 2 | 2, 1 => (q 5 - q 1 - q 2) / 2

/-- **The polarization of a quadratic form.** -/
noncomputable def Hpol (Q : (Fin 3 → ℝ) → ℝ) : Fin 3 → Fin 3 → ℝ := HpolV fun k => Q (dirR k)

/-- The ten values of the symmetric cubic tensor: `S₀₀₀, S₁₁₁, S₂₂₂, S₀₀₁, S₀₁₁, S₀₀₂, S₀₂₂,
S₁₁₂, S₁₂₂, S₀₁₂`, from `κ k = K (dirR k)`. -/
noncomputable def Svals (κ : Fin 10 → ℝ) : Fin 10 → ℝ
  | 0 => κ 0 | 1 => κ 1 | 2 => κ 2
  | 3 => (κ 3 - κ 6 - 2 * κ 1) / 6
  | 4 => (κ 3 + κ 6 - 2 * κ 0) / 6
  | 5 => (κ 4 - κ 7 - 2 * κ 2) / 6
  | 6 => (κ 4 + κ 7 - 2 * κ 0) / 6
  | 7 => (κ 5 - κ 8 - 2 * κ 2) / 6
  | 8 => (κ 5 + κ 8 - 2 * κ 1) / 6
  | 9 => (κ 9 - (κ 0 + κ 1 + κ 2)
      - 3 * ((κ 3 - κ 6 - 2 * κ 1) / 6 + (κ 3 + κ 6 - 2 * κ 0) / 6
        + (κ 4 - κ 7 - 2 * κ 2) / 6 + (κ 4 + κ 7 - 2 * κ 0) / 6
        + (κ 5 - κ 8 - 2 * κ 2) / 6 + (κ 5 + κ 8 - 2 * κ 1) / 6)) / 6

/-- Which of the ten symmetric values sits at `(a, b, c)` (it depends on the multiset only). -/
def msIdx (a b c : Fin 3) : Fin 10 :=
  match [a, b, c].count 0, [a, b, c].count 1 with
  | 3, _ => 0 | _, 3 => 1 | 0, 0 => 2
  | 2, 1 => 3 | 1, 2 => 4 | 2, 0 => 5 | 1, 0 => 6 | 0, 2 => 7 | 0, 1 => 8
  | _, _ => 9

/-- **The polarization of a cubic form**: the symmetric tensor. -/
noncomputable def Cpol (K : (Fin 3 → ℝ) → ℝ) : Fin 3 → Fin 3 → Fin 3 → ℝ :=
  fun a b c => Svals (fun k => K (dirR k)) (msIdx a b c)

/-! ## Interval mirrors -/

def HpolI (q : Fin 10 → Itv) : Fin 3 → Fin 3 → Itv
  | 0, 0 => q 0 | 1, 1 => q 1 | 2, 2 => q 2
  | 0, 1 => Itv.mul (Itv.sub (Itv.sub (q 3) (q 0)) (q 1)) (Itv.ofDiv 1 2)
  | 1, 0 => Itv.mul (Itv.sub (Itv.sub (q 3) (q 0)) (q 1)) (Itv.ofDiv 1 2)
  | 0, 2 => Itv.mul (Itv.sub (Itv.sub (q 4) (q 0)) (q 2)) (Itv.ofDiv 1 2)
  | 2, 0 => Itv.mul (Itv.sub (Itv.sub (q 4) (q 0)) (q 2)) (Itv.ofDiv 1 2)
  | 1, 2 => Itv.mul (Itv.sub (Itv.sub (q 5) (q 1)) (q 2)) (Itv.ofDiv 1 2)
  | 2, 1 => Itv.mul (Itv.sub (Itv.sub (q 5) (q 1)) (q 2)) (Itv.ofDiv 1 2)

/-- `(x ∓ y − 2z)/6` in intervals. -/
def pol6 (sgn : Bool) (x y z : Itv) : Itv :=
  Itv.mul (Itv.sub (if sgn then Itv.sub x y else Itv.add x y) (Itv.mul (Itv.cst (2 * SCALE)) z))
    (Itv.ofDiv 1 6)

def SvalsI (κ : Fin 10 → Itv) : Fin 10 → Itv
  | 0 => κ 0 | 1 => κ 1 | 2 => κ 2
  | 3 => pol6 true (κ 3) (κ 6) (κ 1)
  | 4 => pol6 false (κ 3) (κ 6) (κ 0)
  | 5 => pol6 true (κ 4) (κ 7) (κ 2)
  | 6 => pol6 false (κ 4) (κ 7) (κ 0)
  | 7 => pol6 true (κ 5) (κ 8) (κ 2)
  | 8 => pol6 false (κ 5) (κ 8) (κ 1)
  | 9 => Itv.mul (Itv.sub (Itv.sub (κ 9) (Itv.add (Itv.add (κ 0) (κ 1)) (κ 2)))
      (Itv.mul (Itv.cst (3 * SCALE))
        (Itv.add (Itv.add (Itv.add (Itv.add (Itv.add (pol6 true (κ 3) (κ 6) (κ 1))
          (pol6 false (κ 3) (κ 6) (κ 0))) (pol6 true (κ 4) (κ 7) (κ 2)))
          (pol6 false (κ 4) (κ 7) (κ 0))) (pol6 true (κ 5) (κ 8) (κ 2)))
          (pol6 false (κ 5) (κ 8) (κ 1)))))
      (Itv.ofDiv 1 6)

def CpolI (κ : Fin 10 → Itv) : Fin 3 → Fin 3 → Fin 3 → Itv :=
  fun a b c => SvalsI κ (msIdx a b c)

theorem mem_ofDiv_half : (Itv.ofDiv 1 2).Mem (1 / 2) := by
  have := Itv.mem_ofDiv (n := 1) (d := 2) (by norm_num); norm_num at this ⊢; exact this

theorem mem_ofDiv_sixth : (Itv.ofDiv 1 6).Mem (1 / 6) := by
  have := Itv.mem_ofDiv (n := 1) (d := 6) (by norm_num); norm_num at this ⊢; exact this

theorem mem_cstS (n : ℤ) : (Itv.cst (n * SCALE)).Mem (n : ℝ) := by
  have h := Itv.mem_cst (n * SCALE)
  rwa [show ((n * SCALE : ℤ) : ℝ) / SCALE = n by push_cast; field_simp [SCALE_pos'.ne']] at h

theorem HpolI_mem {qi : Fin 10 → Itv} {q : Fin 10 → ℝ} (h : ∀ k, (qi k).Mem (q k)) :
    ∀ i j, (HpolI qi i j).Mem (HpolV q i j) := by
  intro i j
  have half := mem_ofDiv_half
  fin_cases i <;> fin_cases j <;> simp only [HpolI, HpolV] <;>
    first
    | exact h _
    | (rw [div_eq_mul_one_div]; exact Itv.mem_mul (Itv.mem_sub (Itv.mem_sub (h _) (h _)) (h _)) half)

theorem pol6_mem {x y z : Itv} {a b c : ℝ} (hx : x.Mem a) (hy : y.Mem b) (hz : z.Mem c) :
    (pol6 true x y z).Mem ((a - b - 2 * c) / 6) ∧ (pol6 false x y z).Mem ((a + b - 2 * c) / 6) := by
  have h2 : (Itv.cst (2 * SCALE)).Mem 2 := by simpa using mem_cstS 2
  constructor
  · rw [div_eq_mul_one_div]
    exact Itv.mem_mul (Itv.mem_sub (Itv.mem_sub hx hy) (Itv.mem_mul h2 hz)) mem_ofDiv_sixth
  · rw [div_eq_mul_one_div]
    exact Itv.mem_mul (Itv.mem_sub (Itv.mem_add hx hy) (Itv.mem_mul h2 hz)) mem_ofDiv_sixth

theorem SvalsI_mem {κi : Fin 10 → Itv} {κ : Fin 10 → ℝ} (h : ∀ k, (κi k).Mem (κ k)) :
    ∀ k, (SvalsI κi k).Mem (Svals κ k) := by
  have p36 := pol6_mem (h 3) (h 6) (h 1); have p36' := pol6_mem (h 3) (h 6) (h 0)
  have p47 := pol6_mem (h 4) (h 7) (h 2); have p47' := pol6_mem (h 4) (h 7) (h 0)
  have p58 := pol6_mem (h 5) (h 8) (h 2); have p58' := pol6_mem (h 5) (h 8) (h 1)
  have h3 : (Itv.cst (3 * SCALE)).Mem 3 := by simpa using mem_cstS 3
  intro k
  fin_cases k
  · exact h 0
  · exact h 1
  · exact h 2
  · exact p36.1
  · exact p36'.2
  · exact p47.1
  · exact p47'.2
  · exact p58.1
  · exact p58'.2
  · simp only [SvalsI, Svals]
    rw [div_eq_mul_one_div]
    exact Itv.mem_mul (Itv.mem_sub (Itv.mem_sub (h 9) (Itv.mem_add (Itv.mem_add (h 0) (h 1)) (h 2)))
      (Itv.mem_mul h3 (Itv.mem_add (Itv.mem_add (Itv.mem_add (Itv.mem_add (Itv.mem_add p36.1
        p36'.2) p47.1) p47'.2) p58.1) p58'.2))) mem_ofDiv_sixth

theorem CpolI_mem {κi : Fin 10 → Itv} {K : (Fin 3 → ℝ) → ℝ}
    (h : ∀ k, (κi k).Mem (K (dirR k))) : ∀ a b c, (CpolI κi a b c).Mem (Cpol K a b c) :=
  fun a b c => SvalsI_mem h (msIdx a b c)

end Thomson.TriLocalCert
