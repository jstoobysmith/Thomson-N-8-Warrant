import Thomson.ThreePoint.Kernel

/-! # Task 1c: the two dropped rows

The pivot system has 24 rows (`rowSpec`), but the certificate is tight at 26 conditions: the pair
value at the chord `A` (`pairVal 0`) and the `v`-derivative at the type `FDN` (`triD 1 1`) were
dropped, because they follow from the others.  Both come out of the slack identity
(`slack_identity`), evaluated and differentiated along the antiprism family at `u*`:

* at `u = u*`, the left side is `0` (the bound row `row_bound` and `antiprismEnergy_eq_chords`),
  `bvTerm` is `0` (the kernel lemma, `bvTerm_dz`), and every pair and triangle slack vanishes by a
  definitional row except `pairP pivots (chord 0)`: **1c(i)**;
* the derivative at `u*` of the left side is `2·E′(u*) = 0`; every slack now has a double zero at
  `u*` except the `FDN` triangle, whose derivative is `96 · ∂_v triP(τ_FDN) · (2r)′(u*) / Π`, and
  `(2√(1−u))′ ≠ 0`: **1c(ii)**. -/

namespace Thomson
open Finset Matrix Filter Topology

theorem uStar_pos : 0 < uStar := by linarith [uStar_mem_Icc.1]
theorem uStar_lt_one : uStar < 1 := by linarith [uStar_mem_Icc.2]

/-! ## The kernel term vanishes to second order -/

theorem psi_dz (k : Fin 6) (a b : Fin (9 - (k : ℕ))) : DoubleZero (psi k a b) uStar := by
  refine DoubleZero.congr ?_ fun u => (psi_eq_psiN k a b u).symm
  obtain ⟨k, hk⟩ := k
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only at ha hb ⊢
  interval_cases k
  · exact psiN_dz_0 a b ha hb
  · exact psiN_dz_1 a b ha hb
  · exact psiN_dz_2 a b ha hb
  · exact psiN_dz_3 a b ha hb
  · exact psiN_dz_4 a b ha hb
  · exact psiN_dz_5 a b ha hb

/-- **The kernel lemma**: for every pivot vector, `bvTerm p` has a double zero at `u*`. -/
theorem bvTerm_dz (p : Fin 24 → ℝ) : DoubleZero (bvTerm p) uStar := by
  show DoubleZero (fun u => ∑ k : Fin 6, ∑ a, ∑ b, Hp p k a b * psi k a b u) uStar
  refine DoubleZero.sum _ fun k _ => DoubleZero.sum _ fun a _ => DoubleZero.sum _ fun b _ => ?_
  exact (psi_dz k a b).const_mul _

/-! ## 1c(i): the pair value at the chord `A` -/

section
variable (h : IsUnit pivotMatrix.det)
include h

theorem pairSum_uStar :
    pairSum pivots uStar = 16 * (pairP pivots (chord 0) / chord 0) := by
  unfold pairSum
  rw [chA_uStar, chD_uStar, chN_uStar, chF_uStar, row_pairVal h 1 (by decide),
    row_pairVal h 2 (by decide), row_pairVal h 3 (by decide)]
  ring

theorem triSum_uStar : triSum pivots uStar = 0 := by
  have t0 := row_triVal h 0; have t1 := row_triVal h 1; have t2 := row_triVal h 2
  have t3 := row_triVal h 3; have t4 := row_triVal h 4
  rw [touchType_zero] at t0; rw [touchType_one] at t1; rw [touchType_two] at t2
  rw [touchType_three] at t3; rw [touchType_four] at t4
  unfold triSum
  rw [chA_uStar, chD_uStar, chN_uStar, chF_uStar]
  simp only at t0 t1 t2 t3 t4
  rw [t0, t1, t2, t3, t4]
  ring

/-- **Task 1c(i).** -/
theorem row_pairVal_A_of : pairP pivots (chord 0) = 0 := by
  have hid := slack_identity pivots uStar_pos.le uStar_lt_one
  rw [pairSum_uStar h, triSum_uStar h, (bvTerm_dz pivots).eq_zero] at hid
  have hb := row_bound h
  have hc : 0 < chord 0 := by rw [← chA_uStar]; exact chA_pos uStar_lt_one
  have : pairP pivots (chord 0) / chord 0 = 0 := by linarith
  rwa [div_eq_zero_iff, or_iff_left hc.ne'] at this

/-- The pair polynomial has a double zero at each of the four chord lengths. -/
theorem pairP_tight_of (X : Fin 4) :
    pairP pivots (chord X) = 0 ∧ deriv (pairP pivots) (chord X) = 0 := by
  refine ⟨?_, row_pairDer h X⟩
  by_cases hX : X = 0
  · subst hX; exact row_pairVal_A_of h
  · exact row_pairVal h X hX

end

/-! ## Calculus along the family -/

theorem Q3_differentiable_comp3 (k : ℕ) {f g h : ℝ × ℝ × ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (hh : Differentiable ℝ h) :
    Differentiable ℝ fun x => Q3 k (f x) (g x) (h x) :=
  (Q3_differentiable k).comp (hf.prodMk (hg.prodMk hh))

attribute [local fun_prop] Q3_differentiable_comp3

theorem triP_differentiable3 (p : Fin 24 → ℝ) :
    Differentiable ℝ (fun x : ℝ × ℝ × ℝ => triP p x.1 x.2.1 x.2.2) := by
  unfold triP Fh
  simp only [Matrix.mul_apply, S3, Y3, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply,
    Matrix.transpose_apply, smul_eq_mul]
  fun_prop

/-- The chain rule for the triangle polynomial along a curve `u ↦ (a u, b u, c u)`, with the
three partial derivatives written as one-variable derivatives. -/
theorem hasDerivAt_triP_curve (p : Fin 24 → ℝ) {a b c : ℝ → ℝ} {da db dc u₀ : ℝ}
    (ha : HasDerivAt a da u₀) (hb : HasDerivAt b db u₀) (hc : HasDerivAt c dc u₀) :
    HasDerivAt (fun u => triP p (a u) (b u) (c u))
      (da * deriv (fun d => triP p (a u₀ + d) (b u₀) (c u₀)) 0
        + db * deriv (fun d => triP p (a u₀) (b u₀ + d) (c u₀)) 0
        + dc * deriv (fun d => triP p (a u₀) (b u₀) (c u₀ + d)) 0) u₀ := by
  set f : ℝ × ℝ × ℝ → ℝ := fun x => triP p x.1 x.2.1 x.2.2 with hf_def
  set x₀ : ℝ × ℝ × ℝ := (a u₀, b u₀, c u₀) with hx₀
  have hL : HasFDerivAt f (fderiv ℝ f x₀) x₀ := (triP_differentiable3 p x₀).hasFDerivAt
  have hγ : HasDerivAt (fun u => (a u, b u, c u)) (da, db, dc) u₀ := ha.prodMk (hb.prodMk hc)
  have h1 : HasDerivAt (fun u => f (a u, b u, c u)) (fderiv ℝ f x₀ (da, db, dc)) u₀ :=
    hL.comp_hasDerivAt_of_eq u₀ hγ rfl
  have hpart : ∀ e : ℝ × ℝ × ℝ,
      deriv (fun d : ℝ => f (x₀ + d • e)) 0 = fderiv ℝ f x₀ e := fun e => by
    have hline : HasDerivAt (fun d : ℝ => x₀ + d • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x₀
    exact (hL.comp_hasDerivAt_of_eq 0 hline (by simp)).deriv
  have e1 : (fun d : ℝ => triP p (a u₀ + d) (b u₀) (c u₀))
      = fun d : ℝ => f (x₀ + d • ((1 : ℝ), (0 : ℝ), (0 : ℝ))) := by
    funext d; simp [hf_def, hx₀]
  have e2 : (fun d : ℝ => triP p (a u₀) (b u₀ + d) (c u₀))
      = fun d : ℝ => f (x₀ + d • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) := by
    funext d; simp [hf_def, hx₀]
  have e3 : (fun d : ℝ => triP p (a u₀) (b u₀) (c u₀ + d))
      = fun d : ℝ => f (x₀ + d • ((0 : ℝ), (0 : ℝ), (1 : ℝ))) := by
    funext d; simp [hf_def, hx₀]
  rw [e1, e2, e3, hpart, hpart, hpart]
  have hsplit : ((da, db, dc) : ℝ × ℝ × ℝ)
      = da • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) + db • ((0 : ℝ), (1 : ℝ), (0 : ℝ))
        + dc • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_add, map_smul, map_smul, map_smul] at h1
  simpa [smul_eq_mul] using h1

/-- A pair slack with a double zero of `pairP` has derivative `0`. -/
theorem hasDerivAt_pairTerm {g : ℝ → ℝ} {dg u₀ : ℝ} (hg : HasDerivAt g dg u₀) (hg0 : g u₀ ≠ 0)
    (hv : pairP pivots (g u₀) = 0) (hd : deriv (pairP pivots) (g u₀) = 0) :
    HasDerivAt (fun u => pairP pivots (g u) / g u) 0 u₀ := by
  have h1 : HasDerivAt (fun u => pairP pivots (g u)) (deriv (pairP pivots) (g u₀) * dg) u₀ :=
    ((pairP_differentiable pivots) (g u₀)).hasDerivAt.comp u₀ hg
  refine (h1.div hg hg0).congr_deriv ?_
  rw [hv, hd]; ring

/-- A triangle slack at a zero of `triP`: the quotient rule loses the denominator's derivative. -/
theorem hasDerivAt_triTerm {a b c : ℝ → ℝ} {da db dc u₀ D : ℝ}
    (ha : HasDerivAt a da u₀) (hb : HasDerivAt b db u₀) (hc : HasDerivAt c dc u₀)
    (hv : triP pivots (a u₀) (b u₀) (c u₀) = 0) (hprod : a u₀ * b u₀ * c u₀ ≠ 0)
    (hD : HasDerivAt (fun u => triP pivots (a u) (b u) (c u)) D u₀) :
    HasDerivAt (fun u => triP pivots (a u) (b u) (c u) / (a u * b u * c u))
      (D / (a u₀ * b u₀ * c u₀)) u₀ := by
  refine (hD.div ((ha.fun_mul hb).fun_mul hc) hprod).congr_deriv ?_
  rw [hv, zero_mul, sub_zero]; field_simp

/-- The partial derivatives of `triP` at a touching type are the rows `triD`. -/
theorem partial_zero (p : Fin 24 → ℝ) (m : Fin 5) :
    deriv (fun d => triP p ((touchType m).1 + d) (touchType m).2.1 (touchType m).2.2) 0
      = deriv (triD p m 0) 0 := by
  congr 1; funext d; simp [triD]
theorem partial_one (p : Fin 24 → ℝ) (m : Fin 5) :
    deriv (fun d => triP p (touchType m).1 ((touchType m).2.1 + d) (touchType m).2.2) 0
      = deriv (triD p m 1) 0 := by
  congr 1; funext d; simp [triD]
theorem partial_two (p : Fin 24 → ℝ) (m : Fin 5) :
    deriv (fun d => triP p (touchType m).1 (touchType m).2.1 ((touchType m).2.2 + d)) 0
      = deriv (triD p m 2) 0 := by
  congr 1; funext d; simp [triD]

/-! ### The chords along the family -/

theorem hasDerivAt_sqrt_one_sub {u : ℝ} (hu : u < 1) :
    HasDerivAt (fun v => Real.sqrt (1 - v)) (-1 / (2 * Real.sqrt (1 - u))) u := by
  have := ((hasDerivAt_id u).const_sub 1).sqrt (by simp; linarith)
  simpa using this

theorem hasDerivAt_chA {u : ℝ} (hu : u < 1) :
    HasDerivAt chA (Real.sqrt 2 * (-1 / (2 * Real.sqrt (1 - u)))) u :=
  (hasDerivAt_sqrt_one_sub hu).const_mul _

theorem hasDerivAt_chD {u : ℝ} (hu : u < 1) :
    HasDerivAt chD (2 * (-1 / (2 * Real.sqrt (1 - u)))) u :=
  (hasDerivAt_sqrt_one_sub hu).const_mul _

theorem hasDerivAt_chN {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    HasDerivAt chN ((2 + Real.sqrt 2) / (2 * chN u)) u := by
  have h1 : HasDerivAt (fun v => 2 + 2 * v - Real.sqrt 2 * (1 - v)) (2 + Real.sqrt 2) u := by
    have e : (fun v => 2 + 2 * v - Real.sqrt 2 * (1 - v))
        = fun v => (2 - Real.sqrt 2) + (2 + Real.sqrt 2) * v := by funext v; ring
    rw [e]
    simpa using ((hasDerivAt_id u).const_mul (2 + Real.sqrt 2)).const_add (2 - Real.sqrt 2)
  exact h1.sqrt (cross_pos hu0 hu1).ne'

theorem hasDerivAt_chF {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    HasDerivAt chF ((2 - Real.sqrt 2) / (2 * chF u)) u := by
  have h1 : HasDerivAt (fun v => 2 + 2 * v + Real.sqrt 2 * (1 - v)) (2 - Real.sqrt 2) u := by
    have e : (fun v => 2 + 2 * v + Real.sqrt 2 * (1 - v))
        = fun v => (2 + Real.sqrt 2) + (2 - Real.sqrt 2) * v := by funext v; ring
    rw [e]
    simpa using ((hasDerivAt_id u).const_mul (2 - Real.sqrt 2)).const_add (2 + Real.sqrt 2)
  have hp := cross_pos hu0 hu1; have h2 := sqrt2_pos
  exact h1.sqrt (by nlinarith)

/-! ## 1c(ii): the `v`-derivative at the type `FDN` -/

section
variable (h : IsUnit pivotMatrix.det)
include h

/-- **Task 1c(ii).** -/
theorem row_triD_FDN_v_of : deriv (triD pivots 1 1) 0 = 0 := by
  have hu0 := uStar_pos.le; have hu1 := uStar_lt_one
  set X := deriv (triD pivots 1 1) 0 with hX
  -- the chords and their derivatives at `u*`
  have dA := hasDerivAt_chA hu1; have dD := hasDerivAt_chD hu1
  have dN := hasDerivAt_chN hu0 hu1.le; have dF := hasDerivAt_chF hu0 hu1.le
  have pA := chA_pos hu1; have pD := chD_pos hu1
  have pN := chN_pos hu0 hu1.le; have pF := chF_pos hu0 hu1.le
  rw [chA_uStar] at pA; rw [chD_uStar] at pD; rw [chN_uStar] at pN; rw [chF_uStar] at pF
  -- the pair slacks
  have tight := fun X => pairP_tight_of h X
  have hPA := hasDerivAt_pairTerm dA (by rw [chA_uStar]; exact pA.ne')
    (by rw [chA_uStar]; exact (tight 0).1) (by rw [chA_uStar]; exact (tight 0).2)
  have hPD := hasDerivAt_pairTerm dD (by rw [chD_uStar]; exact pD.ne')
    (by rw [chD_uStar]; exact (tight 1).1) (by rw [chD_uStar]; exact (tight 1).2)
  have hPN := hasDerivAt_pairTerm dN (by rw [chN_uStar]; exact pN.ne')
    (by rw [chN_uStar]; exact (tight 2).1) (by rw [chN_uStar]; exact (tight 2).2)
  have hPF := hasDerivAt_pairTerm dF (by rw [chF_uStar]; exact pF.ne')
    (by rw [chF_uStar]; exact (tight 3).1) (by rw [chF_uStar]; exact (tight 3).2)
  have hpair : HasDerivAt (pairSum pivots) 0 uStar := by
    have := ((((hPA.const_mul 8).add (hPD.const_mul 4)).add (hPN.const_mul 8)).add
      (hPF.const_mul 8)).const_mul 2
    unfold pairSum
    exact this.congr_deriv (by ring)
  -- the partial derivatives at the five types
  have v0 := row_triVal h 0; have v1 := row_triVal h 1; have v2 := row_triVal h 2
  have v3 := row_triVal h 3; have v4 := row_triVal h 4
  have g : ∀ m c, (m, c) ≠ (1, 1) → deriv (triD pivots m c) 0 = 0 :=
    fun m c hmc => row_triD h m c hmc
  have q00 := partial_zero pivots 0; have q01 := partial_one pivots 0
  have q02 := partial_two pivots 0
  have q10 := partial_zero pivots 1; have q11 := partial_one pivots 1
  have q12 := partial_two pivots 1
  have q20 := partial_zero pivots 2; have q21 := partial_one pivots 2
  have q22 := partial_two pivots 2
  have q30 := partial_zero pivots 3; have q31 := partial_one pivots 3
  have q32 := partial_two pivots 3
  have q40 := partial_zero pivots 4; have q41 := partial_one pivots 4
  have q42 := partial_two pivots 4
  rw [touchType_zero] at v0 q00 q01 q02
  rw [touchType_one] at v1 q10 q11 q12
  rw [touchType_two] at v2 q20 q21 q22
  rw [touchType_three] at v3 q30 q31 q32
  rw [touchType_four] at v4 q40 q41 q42
  simp only at v0 v1 v2 v3 v4 q00 q01 q02 q10 q11 q12 q20 q21 q22 q30 q31 q32 q40 q41 q42
  rw [g 0 0 (by decide)] at q00; rw [g 0 1 (by decide)] at q01; rw [g 0 2 (by decide)] at q02
  rw [g 1 0 (by decide)] at q10; rw [← hX] at q11; rw [g 1 2 (by decide)] at q12
  rw [g 2 0 (by decide)] at q20; rw [g 2 1 (by decide)] at q21; rw [g 2 2 (by decide)] at q22
  rw [g 3 0 (by decide)] at q30; rw [g 3 1 (by decide)] at q31; rw [g 3 2 (by decide)] at q32
  rw [g 4 0 (by decide)] at q40; rw [g 4 1 (by decide)] at q41; rw [g 4 2 (by decide)] at q42
  -- the triangle slacks
  have T0 := hasDerivAt_triP_curve pivots dF dF dA
  have T1 := hasDerivAt_triP_curve pivots dF dD dN
  have T2 := hasDerivAt_triP_curve pivots dF dN dA
  have T3 := hasDerivAt_triP_curve pivots dD dA dA
  have T4 := hasDerivAt_triP_curve pivots dN dN dA
  simp only [chA_uStar, chD_uStar, chN_uStar, chF_uStar] at T0 T1 T2 T3 T4
  rw [q00, q01, q02] at T0; rw [q10, q11, q12] at T1; rw [q20, q21, q22] at T2
  rw [q30, q31, q32] at T3; rw [q40, q41, q42] at T4
  have R0 := hasDerivAt_triTerm dF dF dA (by simp only [chA_uStar, chF_uStar]; exact v0)
    (by simp only [chA_uStar, chF_uStar]; positivity) T0
  have R1 := hasDerivAt_triTerm dF dD dN (by simp only [chD_uStar, chN_uStar, chF_uStar]; exact v1)
    (by simp only [chD_uStar, chN_uStar, chF_uStar]; positivity) T1
  have R2 := hasDerivAt_triTerm dF dN dA (by simp only [chA_uStar, chN_uStar, chF_uStar]; exact v2)
    (by simp only [chA_uStar, chN_uStar, chF_uStar]; positivity) T2
  have R3 := hasDerivAt_triTerm dD dA dA (by simp only [chA_uStar, chD_uStar]; exact v3)
    (by simp only [chA_uStar, chD_uStar]; positivity) T3
  have R4 := hasDerivAt_triTerm dN dN dA (by simp only [chA_uStar, chN_uStar]; exact v4)
    (by simp only [chA_uStar, chN_uStar]; positivity) T4
  simp only [chA_uStar, chD_uStar, chN_uStar, chF_uStar] at R0 R1 R2 R3 R4
  set dDv := 2 * (-1 / (2 * Real.sqrt (1 - uStar))) with hdDv
  have htri : HasDerivAt (triSum pivots)
      (6 * (16 * (dDv * X / (chord 3 * chord 1 * chord 2)))) uStar := by
    have := ((((((R0.const_mul 8).add (R1.const_mul 16)).add (R2.const_mul 16)).add
      (R3.const_mul 8)).add (R4.const_mul 8))).const_mul 6
    refine this.congr_deriv ?_
    ring
  -- the right side of the slack identity, and the left side
  have hR := (hpair.add htri).add (bvTerm_dz pivots).hasDerivAt
  have hL : HasDerivAt (fun u => 2 * antiprismEnergy u
      - (64 * a0Fix - 8 * (a0Fix + a1Fix) - 8 * Fh (Hp pivots) 1 1 1)) 0 uStar := by
    have := ((hasDerivAt_antiprismEnergy hu0 hu1).const_mul 2).sub_const
      (64 * a0Fix - 8 * (a0Fix + a1Fix) - 8 * Fh (Hp pivots) 1 1 1)
    rw [antiprismEnergy'_uStar, mul_zero] at this
    exact this
  have heq : (fun u => 2 * antiprismEnergy u
      - (64 * a0Fix - 8 * (a0Fix + a1Fix) - 8 * Fh (Hp pivots) 1 1 1))
      =ᶠ[𝓝 uStar] fun u => pairSum pivots u + triSum pivots u + bvTerm pivots u := by
    filter_upwards [Ioo_mem_nhds uStar_pos uStar_lt_one] with u hu
    exact slack_identity pivots hu.1.le hu.2
  have huniq := (hL.congr_of_eventuallyEq heq.symm).unique hR
  -- `0 = 96 · (2r)′ · X / Π`, and `(2r)′ ≠ 0`
  have hr : 0 < Real.sqrt (1 - uStar) := Real.sqrt_pos.mpr (by linarith)
  have hdD : dDv ≠ 0 := by
    rw [hdDv]; exact mul_ne_zero two_ne_zero (div_ne_zero (by norm_num) (by positivity))
  have hprod : chord 3 * chord 1 * chord 2 ≠ 0 := by positivity
  have : dDv * X / (chord 3 * chord 1 * chord 2) = 0 := by linarith
  rw [div_eq_zero_iff, or_iff_left hprod, mul_eq_zero, or_iff_right hdD] at this
  exact this

end

end Thomson
