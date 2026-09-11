import Thomson.TriLocalCert.Enclose
import Thomson.TriLocalCert.Polar

/-! # Task 5a, numeric side, step 6: the data of one touching type

From an enclosure `CF` of `F`'s tensor and enclosures `T₀, T₁, T₂` of the touching type `τ`,
`computeD` produces the interval data of `Thomson.TriLocalCert.Patch`:

* `H`, `C` — the polarizations (`Hpol`, `Cpol`) of the second and third derivatives along the ten
  directions, each from the jet of the ray polynomial (`qI`, `kI`);
* `M` — the value at `ρ = 1/500` of the fourth derivative of the majorant (`MI`).

`computeD_mem` says the data enclose, for every `p` with `ITMem CF (cF (Mmat (Hp p)))`, the true
`Hpol`, `Cpol` of `triP p` at `τ` and the real `M`; `ray4_le_M` is the matching bound
`|(d/dx)⁴ triP p (τ + xδ)| ≤ M · ‖δ‖⁴` on the cube. -/

namespace Thomson.TriLocalCert

open Thomson Thomson.Pair Thomson.Tri5b Finset

/-- `λ` on the grid. -/
def lamQ : ℤ := 97932235147000000000000000000000000000

theorem lamQ_eq : (lamQ : ℝ) / SCALE = lamFix := by norm_num [lamQ, lamFix, SCALE]

theorem mem_lamI : (Itv.cst lamQ).Mem lamFix := by
  have := Itv.mem_cst lamQ; rwa [lamQ_eq] at this

/-- The direction `k` on the grid. -/
def dI (k : Fin 10) (a : Fin 3) : Itv := Itv.cst (dirZ k a * SCALE)

theorem mem_dI (k : Fin 10) (a : Fin 3) : (dI k a).Mem (dirR k a) := mem_cstS _

/-- The jet of the ray polynomial along direction `k`. -/
@[irreducible] def jetK (CF : IT) (T0 T1 T2 : Itv) (k : Fin 10) : List Itv :=
  JgL CF (Itv.cst lamQ) T0 T1 T2 (dI k 0) (dI k 1) (dI k 2)

/-- The second derivative at `0` along direction `k`: `2 g₂`. -/
@[irreducible] def qI (CF : IT) (T0 T1 T2 : Itv) (k : Fin 10) : Itv :=
  Itv.mul (Itv.cst (2 * SCALE)) ((jetK CF T0 T1 T2 k).getD 2 Itv.zero)

/-- The third derivative at `0` along direction `k`: `6 g₃`. -/
@[irreducible] def kI (CF : IT) (T0 T1 T2 : Itv) (k : Fin 10) : Itv :=
  Itv.mul (Itv.cst (6 * SCALE)) ((jetK CF T0 T1 T2 k).getD 3 Itv.zero)

/-- `ρ = 1/500`. -/
theorem mem_RHO : (Itv.cst RHO).Mem (1 / 500) := by
  have := Itv.mem_cst RHO
  rwa [show (RHO : ℝ) / SCALE = 1 / 500 by norm_num [RHO, SCALE]] at this

/-- `1 − T²/2 − a`, enclosed: the constant term of the shifted `u`. -/
def EuI (T : Itv) (a : ℤ) : Itv :=
  Itv.sub (Itv.sub Itv.one (Itv.mul (Itv.mul T T) (Itv.ofDiv 1 2))) (Itv.cst a)

/-- The fourth derivative of the (shifted) majorant, at `ρ`.  `CS` encloses the tensor of `F`
shifted to the grid point `(a, b, c)`. -/
@[irreducible] def MI (CS : IT) (T0 T1 T2 : Itv) (a b c : ℤ) : Itv :=
  lev (lder (lder (lder (lder (IPgLs (fun i j k => Itv.cst (aHi (CS i j k))) (Itv.cst lamQ)
    (Itv.cst (aHi T0)) (Itv.cst (aHi T1)) (Itv.cst (aHi T2))
    (Itv.cst (aHi (EuI T0 a))) (Itv.cst (aHi (EuI T1 b))) (Itv.cst (aHi (EuI T2 c))))))))
    (Itv.cst RHO)

/-- **The data of one touching type.** -/
def computeD (CF CS : IT) (T0 T1 T2 : Itv) (a b c : ℤ) : Data where
  H := (List.finRange 3).map fun a => (List.finRange 3).map fun b => HpolI (qI CF T0 T1 T2) a b
  C := (List.finRange 3).map fun a => (List.finRange 3).map fun b => (List.finRange 3).map
    fun c => CpolI (kI CF T0 T1 T2) a b c
  M := MI CS T0 T1 T2 a b c

theorem getD_finRange3 {α : Type*} (f : Fin 3 → α) (d : α) (a : Fin 3) :
    ((List.finRange 3).map f).getD a d = f a := by
  fin_cases a <;> rfl

/-- The real second and third derivatives at `0` along a direction. -/
noncomputable def Q2 (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (v : Fin 3 → ℝ) : ℝ :=
  deriv (deriv (rayR p τ v)) 0
noncomputable def K3 (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (v : Fin 3 → ℝ) : ℝ :=
  deriv (deriv (deriv (rayR p τ v))) 0

/-- The real `M`. -/
noncomputable def Mreal (CS : IT) (T0 T1 T2 : Itv) (a b c : ℤ) : ℝ :=
  reval (rderN 4 (PgLs (fun i j k => (aHi (CS i j k) : ℝ) / SCALE) ((lamQ : ℝ) / SCALE)
    ((aHi T0 : ℝ) / SCALE) ((aHi T1 : ℝ) / SCALE) ((aHi T2 : ℝ) / SCALE)
    ((aHi (EuI T0 a) : ℝ) / SCALE) ((aHi (EuI T1 b) : ℝ) / SCALE) ((aHi (EuI T2 c) : ℝ) / SCALE)))
    (1 / 500)

variable {p : Fin 24 → ℝ} {CF CS : IT} {τ : ℝ × ℝ × ℝ} {T0 T1 T2 : Itv} {a b c : ℤ}

theorem mem_qI (hc : ITMem CF (cF (Mmat (Hp p)))) (h0 : T0.Mem τ.1) (h1 : T1.Mem τ.2.1)
    (h2 : T2.Mem τ.2.2) (k : Fin 10) : (qI CF T0 T1 T2 k).Mem (Q2 p τ (dirR k)) := by
  have hj := JMem_JgL hc mem_lamI h0 h1 h2 (mem_dI k 0) (mem_dI k 1) (mem_dI k 2) 2 (by norm_num)
  have h2S : (Itv.cst (2 * SCALE)).Mem 2 := by simpa using mem_cstS 2
  rw [Q2, ray2_zero]
  unfold qI jetK
  exact Itv.mem_mul h2S hj

theorem mem_kI (hc : ITMem CF (cF (Mmat (Hp p)))) (h0 : T0.Mem τ.1) (h1 : T1.Mem τ.2.1)
    (h2 : T2.Mem τ.2.2) (k : Fin 10) : (kI CF T0 T1 T2 k).Mem (K3 p τ (dirR k)) := by
  have hj := JMem_JgL hc mem_lamI h0 h1 h2 (mem_dI k 0) (mem_dI k 1) (mem_dI k 2) 3 (by norm_num)
  have h6S : (Itv.cst (6 * SCALE)).Mem 6 := by simpa using mem_cstS 6
  rw [K3, ray3_zero]
  unfold kI jetK
  exact Itv.mem_mul h6S hj

theorem mem_aHi_cst (I : Itv) : (Itv.cst (aHi I)).Mem ((aHi I : ℝ) / SCALE) := Itv.mem_cst _

theorem mem_EuI {T : Itv} {t : ℝ} (hT : T.Mem t) (a : ℤ) :
    (EuI T a).Mem (1 - t ^ 2 / 2 - (a : ℝ) / SCALE) := by
  have hh : (Itv.ofDiv 1 2).Mem (1 / 2) := by
    have := Itv.mem_ofDiv (n := 1) (d := 2) (by norm_num); norm_num at this ⊢; exact this
  have := Itv.mem_sub (Itv.mem_sub Itv.mem_one (Itv.mem_mul (Itv.mem_mul hT hT) hh)) (Itv.mem_cst a)
  rw [show 1 - t ^ 2 / 2 - (a : ℝ) / SCALE = 1 - t * t * (1 / 2) - (a : ℝ) / SCALE by ring]
  exact this

theorem mem_MI (CS : IT) (T0 T1 T2 : Itv) (a b c : ℤ) :
    (MI CS T0 T1 T2 a b c).Mem (Mreal CS T0 T1 T2 a b c) := by
  have hP := LMem_IPgLs (cb := fun (i j k : Fin 9) => (aHi (CS i j k) : ℝ) / SCALE)
    (fun (i j k : Fin 9) => mem_aHi_cst (CS i j k)) (Itv.mem_cst lamQ) (mem_aHi_cst T0)
    (mem_aHi_cst T1) (mem_aHi_cst T2) (mem_aHi_cst (EuI T0 a)) (mem_aHi_cst (EuI T1 b))
    (mem_aHi_cst (EuI T2 c))
  unfold MI
  exact mem_lev mem_RHO (LMem_lder (LMem_lder (LMem_lder (LMem_lder hP))))

theorem computeD_h (CF CS : IT) (T0 T1 T2 : Itv) (a0 b0 c0 : ℤ) (a b : Fin 3) :
    (computeD CF CS T0 T1 T2 a0 b0 c0).h a b = HpolI (qI CF T0 T1 T2) a b := by
  unfold Data.h
  rw [show (computeD CF CS T0 T1 T2 a0 b0 c0).H = (List.finRange 3).map fun a =>
      (List.finRange 3).map fun b => HpolI (qI CF T0 T1 T2) a b from rfl,
    getD_finRange3, getD_finRange3]

theorem computeD_c (CF CS : IT) (T0 T1 T2 : Itv) (a0 b0 c0 : ℤ) (a b c : Fin 3) :
    (computeD CF CS T0 T1 T2 a0 b0 c0).c a b c = CpolI (kI CF T0 T1 T2) a b c := by
  unfold Data.c
  rw [show (computeD CF CS T0 T1 T2 a0 b0 c0).C = (List.finRange 3).map fun a => (List.finRange 3).map
      fun b => (List.finRange 3).map fun c => CpolI (kI CF T0 T1 T2) a b c from rfl,
    getD_finRange3, getD_finRange3, getD_finRange3]

theorem computeD_M (CF CS : IT) (T0 T1 T2 : Itv) (a b c : ℤ) :
    (computeD CF CS T0 T1 T2 a b c).M = MI CS T0 T1 T2 a b c := rfl

/-- **The data enclose the true `Hpol`, `Cpol`, `M`.** -/
theorem computeD_mem (hc : ITMem CF (cF (Mmat (Hp p)))) (h0 : T0.Mem τ.1) (h1 : T1.Mem τ.2.1)
    (h2 : T2.Mem τ.2.2) :
    (computeD CF CS T0 T1 T2 a b c).Mem (Hpol (Q2 p τ)) (Cpol (K3 p τ))
      (Mreal CS T0 T1 T2 a b c) := by
  refine ⟨fun a b => ?_, fun a b c => ?_, ?_⟩
  · rw [computeD_h]; exact HpolI_mem (mem_qI hc h0 h1 h2) a b
  · rw [computeD_c]; exact CpolI_mem (mem_kI hc h0 h1 h2) a b c
  · rw [computeD_M]; exact mem_MI CS T0 T1 T2 a b c

/-- **The fourth derivative on the cube**, against the same `M`. -/
theorem ray4_le_M (hcs : ITMem CS (shift (cF (Mmat (Hp p))) ((a : ℝ) / SCALE) ((b : ℝ) / SCALE)
      ((c : ℝ) / SCALE)))
    (h0 : T0.Mem τ.1) (h1 : T1.Mem τ.2.1) (h2 : T2.Mem τ.2.2) {δ : Fin 3 → ℝ}
    (hδ : ∀ i, |δ i| ≤ 1 / 500) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |deriv (deriv (deriv (deriv (rayR p τ δ)))) x| ≤ Mreal CS T0 T1 T2 a b c * N2 δ ^ 2 := by
  have hS : (0 : ℝ) < SCALE := SCALE_pos'
  set s := max |δ 0| (max |δ 1| |δ 2|) with hs
  have hs0 : 0 ≤ s := le_max_of_le_left (abs_nonneg _)
  have hδs : ∀ i, |δ i| ≤ s := fun i => by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_of_le_right (le_max_left _ _)
    · exact le_max_of_le_right (le_max_right _ _)
  have hsρ : s ≤ 1 / 500 := max_le (hδ 0) (max_le (hδ 1) (hδ 2))
  have hcb : ∀ i j k, |shift (cF (Mmat (Hp p))) ((a : ℝ) / SCALE) ((b : ℝ) / SCALE)
      ((c : ℝ) / SCALE) i j k| ≤ (aHi (CS i j k) : ℝ) / SCALE := fun i j k => by
    rw [le_div_iff₀ hS]; exact abs_le_aHi (hcs i j k)
  have hτ : ∀ {T : Itv} {t : ℝ}, T.Mem t → |t| ≤ (aHi T : ℝ) / SCALE := fun hT => by
    rw [le_div_iff₀ hS]; exact abs_le_aHi hT
  have hΛ : |lamFix| ≤ (lamQ : ℝ) / SCALE := by
    rw [lamQ_eq, abs_of_nonneg (by norm_num [lamFix])]
  have key := abs_ray4_le_s hs0 hsρ hδs hx0 hx1 hcb hΛ (hτ h0) (hτ h1) (hτ h2)
    (hτ (mem_EuI h0 a)) (hτ (mem_EuI h1 b)) (hτ (mem_EuI h2 c))
  have hs2 : s ^ 2 ≤ N2 δ := by
    simp only [N2]
    rcases le_total |δ 0| (max |δ 1| |δ 2|) with h | h
    · rw [hs, max_eq_right h]
      rcases le_total |δ 1| |δ 2| with h' | h'
      · rw [max_eq_right h', sq_abs]; nlinarith [sq_nonneg (δ 0), sq_nonneg (δ 1)]
      · rw [max_eq_left h', sq_abs]; nlinarith [sq_nonneg (δ 0), sq_nonneg (δ 2)]
    · rw [hs, max_eq_left h, sq_abs]; nlinarith [sq_nonneg (δ 1), sq_nonneg (δ 2)]
  have hs4 : s ^ 4 ≤ N2 δ ^ 2 := by
    have := pow_le_pow_left₀ (sq_nonneg s) hs2 2
    calc s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ ≤ N2 δ ^ 2 := this
  have hM0 : 0 ≤ Mreal CS T0 T1 T2 a b c := by
    have hW := WMaj_gLs (p := p) (τ := τ) (δ := δ) hs0 hδs hcb hΛ (hτ h0) (hτ h1) (hτ h2)
      (hτ (mem_EuI h0 a)) (hτ (mem_EuI h1 b)) (hτ (mem_EuI h2 c))
    unfold Mreal
    set P := PgLs (fun i j k => (aHi (CS i j k) : ℝ) / SCALE) ((lamQ : ℝ) / SCALE)
      ((aHi T0 : ℝ) / SCALE) ((aHi T1 : ℝ) / SCALE) ((aHi T2 : ℝ) / SCALE)
      ((aHi (EuI T0 a) : ℝ) / SCALE) ((aHi (EuI T1 b) : ℝ) / SCALE) ((aHi (EuI T2 c) : ℝ) / SCALE)
    rw [reval_eq_sum _ _ (rderN 4 P).length le_rfl]
    refine Finset.sum_nonneg fun n _ => mul_nonneg ?_ (by positivity)
    rw [co_rderN]
    exact mul_nonneg (Finset.prod_nonneg fun i _ => by positivity) (hW.1 _)
  calc |deriv (deriv (deriv (deriv (rayR p τ δ)))) x| ≤ s ^ 4 * Mreal CS T0 T1 T2 a b c := by
        simpa [Mreal, mul_comm] using key
    _ ≤ N2 δ ^ 2 * Mreal CS T0 T1 T2 a b c := mul_le_mul_of_nonneg_right hs4 hM0
    _ = Mreal CS T0 T1 T2 a b c * N2 δ ^ 2 := by ring

end Thomson.TriLocalCert
