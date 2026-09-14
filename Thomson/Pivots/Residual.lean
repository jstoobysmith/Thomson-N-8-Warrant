import Thomson.Pivots.Entries
import Thomson.Antiprism.UStarSharp

/-! # Task 1b, step 7: the rows at the reference pivots

The residual `pivotRhs − pivotMatrix·pivotsNum` is `−rowFun · pivotsNum`: the rows evaluated at the
rational reference vector.  Unlike the entries of `pivotMatrix` these involve the whole certificate —
the constants `a₀, a₁, λ`, the antiprism energy, and `F` itself at `pivotsNum`, whose tensor is
Task 5b's `cF (Mmat (Hp pivotsNum))`.  Their true values are `≈ 10⁻²¹`; the enclosures here are
good to `≈ 10⁻²⁸`. -/

namespace Thomson.Task1b

open Thomson Thomson.Tri5b

theorem deriv_pairP (p : Fin 24 → ℝ) (c : RT) (hc : ∀ u v t, Fh (Hp p) u v t = ev c u v t)
    (s : ℝ) :
    deriv (pairP p) s
      = -(a0Fix + a1Fix * (1 - s ^ 2 / 2) + 3 * ev c 1 (1 - s ^ 2 / 2) (1 - s ^ 2 / 2))
        + s ^ 2 * (a1Fix + 3 * evDiagD c (1 - s ^ 2 / 2)) := by
  have hfun : pairP p = fun x => (1 - 18 * lamFix) - x * (a0Fix + a1Fix * (1 - x ^ 2 / 2)
      + 3 * ev c 1 (1 - x ^ 2 / 2) (1 - x ^ 2 / 2)) := by
    funext x; simp only [pairP, hc]
  rw [hfun]
  have hw := hasDerivAt_sub_sq s
  have hcomp0 := (hasDerivAt_evDiag c (1 - s ^ 2 / 2)).comp s hw
  have hcomp : HasDerivAt (fun x => ev c 1 (1 - x ^ 2 / 2) (1 - x ^ 2 / 2))
      (evDiagD c (1 - s ^ 2 / 2) * (-s)) s := hcomp0
  have hg : HasDerivAt (fun x => a0Fix + a1Fix * (1 - x ^ 2 / 2)
      + 3 * ev c 1 (1 - x ^ 2 / 2) (1 - x ^ 2 / 2))
      (a1Fix * (-s) + 3 * (evDiagD c (1 - s ^ 2 / 2) * (-s))) s :=
    ((hw.const_mul a1Fix).const_add a0Fix).fun_add (hcomp.const_mul 3)
  have hsg : HasDerivAt (fun x => x * (a0Fix + a1Fix * (1 - x ^ 2 / 2)
      + 3 * ev c 1 (1 - x ^ 2 / 2) (1 - x ^ 2 / 2)))
      (1 * (a0Fix + a1Fix * (1 - s ^ 2 / 2) + 3 * ev c 1 (1 - s ^ 2 / 2) (1 - s ^ 2 / 2))
        + s * (a1Fix * (-s) + 3 * (evDiagD c (1 - s ^ 2 / 2) * (-s)))) s :=
    (hasDerivAt_id' s).fun_mul hg
  rw [(hsg.const_sub (1 - 18 * lamFix)).deriv]
  ring

theorem deriv_triP_1 (p : Fin 24 → ℝ) (c : RT) (hc : ∀ u v t, Fh (Hp p) u v t = ev c u v t)
    (a b c3 : ℝ) :
    deriv (fun d => triP p (a + d) b c3) 0
      = lamFix * (b + c3) - b * c3 * ev c (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2)
        + a * a * b * c3 * evD1 c (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2) := by
  have hfun : (fun d => triP p (a + d) b c3) = fun d =>
      lamFix * (b * c3 + (a + d) * c3 + (a + d) * b)
        - (a + d) * b * c3 * ev c (1 - (a + d) ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2) := by
    funext d; simp only [triP, hc]
  rw [hfun]
  have h0 : HasDerivAt (fun d : ℝ => a + d) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add a
  have hcomp0 := (hasDerivAt_evD1 c (1 - (a + 0) ^ 2 / 2) (1 - b ^ 2 / 2)
    (1 - c3 ^ 2 / 2)).comp 0 (hasDerivAt_sub_sq_shift a)
  have hcomp : HasDerivAt (fun d => ev c (1 - (a + d) ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2))
      (evD1 c (1 - (a + 0) ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2) * (-a)) 0 := hcomp0
  have hL : HasDerivAt (fun d => lamFix * (b * c3 + (a + d) * c3 + (a + d) * b))
      (lamFix * (b + c3)) 0 :=
    ((((h0.mul_const c3).const_add (b * c3)).fun_add (h0.mul_const b)).const_mul lamFix).congr_deriv
      (by ring)
  have hP : HasDerivAt (fun d => (a + d) * b * c3) (b * c3) 0 :=
    ((h0.mul_const b).mul_const c3).congr_deriv (by ring)
  rw [(hL.fun_sub (hP.fun_mul hcomp)).deriv]
  simp only [add_zero]
  ring

theorem deriv_triP_2 (p : Fin 24 → ℝ) (c : RT) (hc : ∀ u v t, Fh (Hp p) u v t = ev c u v t)
    (a b c3 : ℝ) :
    deriv (fun d => triP p a (b + d) c3) 0
      = lamFix * (a + c3) - a * c3 * ev c (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2)
        + a * b * b * c3 * evD2 c (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2) := by
  have hfun : (fun d => triP p a (b + d) c3) = fun d =>
      lamFix * ((b + d) * c3 + a * c3 + a * (b + d))
        - a * (b + d) * c3 * ev c (1 - a ^ 2 / 2) (1 - (b + d) ^ 2 / 2) (1 - c3 ^ 2 / 2) := by
    funext d; simp only [triP, hc]
  rw [hfun]
  have h0 : HasDerivAt (fun d : ℝ => b + d) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add b
  have hcomp0 := (hasDerivAt_evD2 c (1 - a ^ 2 / 2) (1 - (b + 0) ^ 2 / 2)
    (1 - c3 ^ 2 / 2)).comp 0 (hasDerivAt_sub_sq_shift b)
  have hcomp : HasDerivAt (fun d => ev c (1 - a ^ 2 / 2) (1 - (b + d) ^ 2 / 2) (1 - c3 ^ 2 / 2))
      (evD2 c (1 - a ^ 2 / 2) (1 - (b + 0) ^ 2 / 2) (1 - c3 ^ 2 / 2) * (-b)) 0 := hcomp0
  have hL : HasDerivAt (fun d => lamFix * ((b + d) * c3 + a * c3 + a * (b + d)))
      (lamFix * (a + c3)) 0 :=
    ((((h0.mul_const c3).add_const (a * c3)).fun_add (h0.const_mul a)).const_mul lamFix).congr_deriv
      (by ring)
  have hP : HasDerivAt (fun d => a * (b + d) * c3) (a * c3) 0 :=
    ((h0.const_mul a).mul_const c3).congr_deriv (by ring)
  rw [(hL.fun_sub (hP.fun_mul hcomp)).deriv]
  simp only [add_zero]
  ring

theorem deriv_triP_3 (p : Fin 24 → ℝ) (c : RT) (hc : ∀ u v t, Fh (Hp p) u v t = ev c u v t)
    (a b c3 : ℝ) :
    deriv (fun d => triP p a b (c3 + d)) 0
      = lamFix * (a + b) - a * b * ev c (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2)
        + a * b * c3 * c3 * evD3 c (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2) := by
  have hfun : (fun d => triP p a b (c3 + d)) = fun d =>
      lamFix * (b * (c3 + d) + a * (c3 + d) + a * b)
        - a * b * (c3 + d) * ev c (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - (c3 + d) ^ 2 / 2) := by
    funext d; simp only [triP, hc]
  rw [hfun]
  have h0 : HasDerivAt (fun d : ℝ => c3 + d) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add c3
  have hcomp0 := (hasDerivAt_evD3 c (1 - a ^ 2 / 2) (1 - b ^ 2 / 2)
    (1 - (c3 + 0) ^ 2 / 2)).comp 0 (hasDerivAt_sub_sq_shift c3)
  have hcomp : HasDerivAt (fun d => ev c (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - (c3 + d) ^ 2 / 2))
      (evD3 c (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - (c3 + 0) ^ 2 / 2) * (-c3)) 0 := hcomp0
  have hL : HasDerivAt (fun d => lamFix * (b * (c3 + d) + a * (c3 + d) + a * b))
      (lamFix * (a + b)) 0 :=
    ((((h0.const_mul b).fun_add (h0.const_mul a)).add_const (a * b)).const_mul lamFix).congr_deriv
      (by ring)
  have hP : HasDerivAt (fun d => a * b * (c3 + d)) (a * b) 0 :=
    (h0.const_mul (a * b)).congr_deriv (by ring)
  rw [(hL.fun_sub (hP.fun_mul hcomp)).deriv]
  simp only [add_zero]
  ring

/-- `triD` along each coordinate is `triP` along a shifted argument. -/
theorem triD_zero (p : Fin 24 → ℝ) (m : Fin 5) :
    triD p m 0 = fun d => triP p ((touchType m).1 + d) (touchType m).2.1 (touchType m).2.2 := by
  funext d; simp [triD]
theorem triD_one (p : Fin 24 → ℝ) (m : Fin 5) :
    triD p m 1 = fun d => triP p (touchType m).1 ((touchType m).2.1 + d) (touchType m).2.2 := by
  funext d; simp [triD]
theorem triD_two (p : Fin 24 → ℝ) (m : Fin 5) :
    triD p m 2 = fun d => triP p (touchType m).1 (touchType m).2.1 ((touchType m).2.2 + d) := by
  funext d; simp [triD]

/-- `1/x` on a positive interval: `[⌊SCALE²/hi⌋, ⌈SCALE²/lo⌉]`. -/
def invI (I : Itv) : Itv := ⟨SCALE2 / I.hi, -((-SCALE2) / I.lo)⟩

theorem mem_invI {I : Itv} {x : ℝ} (hx : I.Mem x) (hpos : 0 < I.lo) : (invI I).Mem x⁻¹ := by
  obtain ⟨h1, h2⟩ := hx
  have hS := SCALE_pos'
  have hlo : (0:ℝ) < I.lo := by exact_mod_cast hpos
  have hxS : 0 < x * SCALE := lt_of_lt_of_le hlo h1
  have hx0 : 0 < x := by
    rcases lt_or_ge 0 x with h | h
    · exact h
    · nlinarith
  have hhi : (0:ℝ) < I.hi := lt_of_lt_of_le hxS h2
  have hhiZ : (0:ℤ) < I.hi := by exact_mod_cast hhi
  have key : ∀ (a d : ℤ), 0 < d → ((a / d : ℤ) : ℝ) * d ≤ a := by
    intro a d hd
    have := Int.ediv_mul_le a (ne_of_gt hd)
    exact_mod_cast this
  have eS2 : ((SCALE2 : ℤ) : ℝ) = (SCALE : ℝ) ^ 2 := by rw [SCALE2_eq]; push_cast; ring
  have hinv : x⁻¹ * SCALE = (SCALE : ℝ) ^ 2 / (x * SCALE) := by field_simp
  constructor
  · show ((SCALE2 / I.hi : ℤ) : ℝ) ≤ x⁻¹ * SCALE
    rw [hinv]
    have k1 := key SCALE2 I.hi hhiZ
    have h3 : ((SCALE2 / I.hi : ℤ) : ℝ) ≤ ((SCALE2 : ℤ) : ℝ) / I.hi := by
      rw [le_div_iff₀ hhi]; exact k1
    calc ((SCALE2 / I.hi : ℤ) : ℝ) ≤ ((SCALE2 : ℤ) : ℝ) / I.hi := h3
      _ ≤ (SCALE : ℝ) ^ 2 / (x * SCALE) := by
        rw [eS2]; exact div_le_div_of_nonneg_left (by positivity) hxS h2
  · show x⁻¹ * SCALE ≤ ((-((-SCALE2) / I.lo) : ℤ) : ℝ)
    rw [hinv]
    have k2 := key (-SCALE2) I.lo hpos
    have h3 : ((SCALE2 : ℤ) : ℝ) / I.lo ≤ ((-((-SCALE2) / I.lo) : ℤ) : ℝ) := by
      rw [div_le_iff₀ hlo]; push_cast at k2 ⊢; linarith
    calc (SCALE : ℝ) ^ 2 / (x * SCALE) ≤ (SCALE : ℝ) ^ 2 / I.lo :=
          div_le_div_of_nonneg_left (by positivity) hlo h1
      _ = ((SCALE2 : ℤ) : ℝ) / I.lo := by rw [eS2]
      _ ≤ _ := h3

/-- `√2`, from `sqrt2_bounds_45`. -/
def sqrt2I : Itv := ⟨14142135623730950488016887242096980785696, 14142135623730950488016887242096980785697⟩

theorem mem_sqrt2I : sqrt2I.Mem (Real.sqrt 2) := by
  obtain ⟨h1, h2⟩ := sqrt2_bounds_45
  constructor <;> simp only [sqrt2I, SCALE] <;> push_cast <;> linarith

/-- The antiprism energy at `u*`, in terms of the chords. -/
theorem antiprismEnergy_uStar :
    antiprismEnergy uStar = (4 * Real.sqrt 2 + 2) * rStar⁻¹ + 8 * s2Star⁻¹ + 8 * s4Star⁻¹ := by
  have e2 : (2 - Real.sqrt 2) + (2 + Real.sqrt 2) * uStar
      = 2 + 2 * uStar - Real.sqrt 2 * (1 - uStar) := by ring
  have e4 : (2 + Real.sqrt 2) + (2 - Real.sqrt 2) * uStar
      = 2 + 2 * uStar + Real.sqrt 2 * (1 - uStar) := by ring
  simp only [antiprismEnergy, rStar, s2Star, s4Star, e2, e4]

def rStarI : Itv := Itv.mul chordDI halfI

theorem mem_rStarI : rStarI.Mem rStar := by
  have h := Itv.mem_mul mem_chordDI mem_halfI
  have e : 2 * rStar * (1 / 2) = rStar := by ring
  rwa [e] at h

def energyI : Itv :=
  Itv.add (Itv.add (Itv.mul (Itv.add (Itv.mul (intI 4) sqrt2I) (intI 2)) (invI rStarI))
    (Itv.mul (intI 8) (invI chordNI))) (Itv.mul (intI 8) (invI chordFI))

theorem mem_energyI : energyI.Mem (antiprismEnergy uStar) := by
  rw [antiprismEnergy_uStar]
  have hr := mem_invI mem_rStarI (by decide)
  have hn := mem_invI mem_chordNI (by decide)
  have hf := mem_invI mem_chordFI (by decide)
  have h := Itv.mem_add (Itv.mem_add (Itv.mem_mul (Itv.mem_add (Itv.mem_mul (mem_intI 4) mem_sqrt2I)
    (mem_intI 2)) hr) (Itv.mem_mul (mem_intI 8) hn)) (Itv.mem_mul (mem_intI 8) hf)
  simpa [energyI] using h

/-! ### The certificate's constants -/

def a0I : Itv := Itv.cst 9443687221010000000000000000000000000000
def a1I : Itv := Itv.cst 2445383048987000000000000000000000000000
def lamI : Itv := Itv.cst LAM

theorem mem_a0I : a0I.Mem a0Fix := by
  have h := Itv.mem_cst 9443687221010000000000000000000000000000
  have e : ((9443687221010000000000000000000000000000 : ℤ) : ℝ) / SCALE = a0Fix := by
    unfold a0Fix SCALE; norm_num
  rwa [e] at h

theorem mem_a1I : a1I.Mem a1Fix := by
  have h := Itv.mem_cst 2445383048987000000000000000000000000000
  have e : ((2445383048987000000000000000000000000000 : ℤ) : ℝ) / SCALE = a1Fix := by
    unfold a1Fix SCALE; norm_num
  rwa [e] at h

theorem mem_lamI : lamI.Mem lamFix := mem_LAM

/-! ### The tensor of `F` at the reference pivots -/

/-- The coefficient tensor of `Fh (Hp pivotsNum)`. -/
noncomputable def cFnum : RT := cF (Mmat (Hp pivotsNum))

theorem Fh_num (u v t : ℝ) : Fh (Hp pivotsNum) u v t = ev cFnum u v t :=
  (ev_cF_eq_Fh pivotsNum u v t).symm

/-! ### The rows at `pivotsNum`, by type -/

def resBound (C : IT) : Itv :=
  Itv.sub (Itv.mul (Itv.sub (Itv.sub (Itv.mul (intI 64) a0I) (Itv.mul (intI 8) (Itv.add a0I a1I)))
    (Itv.mul (intI 8) (evI C Itv.one Itv.one Itv.one))) halfI) energyI

theorem mem_resBound {C : IT} (hC : ITMem C cFnum) : (resBound C).Mem (rowFun 0 pivotsNum) := by
  have h := Itv.mem_sub (Itv.mem_mul (Itv.mem_sub (Itv.mem_sub (Itv.mem_mul (mem_intI 64) mem_a0I)
    (Itv.mem_mul (mem_intI 8) (Itv.mem_add mem_a0I mem_a1I)))
    (Itv.mem_mul (mem_intI 8) (mem_evI hC Itv.mem_one Itv.mem_one Itv.mem_one))) mem_halfI) mem_energyI
  have e : rowFun 0 pivotsNum = ((((64 : ℤ) : ℝ) * a0Fix - ((8 : ℤ) : ℝ) * (a0Fix + a1Fix))
      - ((8 : ℤ) : ℝ) * ev cFnum 1 1 1) * (1 / 2) - antiprismEnergy uStar := by
    simp only [rowFun, rowSpec, Matrix.cons_val_zero, evalRow, Fh_num]
    push_cast; ring
  rw [e]; exact h

def resPairVal (C : IT) (X : Itv) : Itv :=
  Itv.sub (Itv.sub Itv.one (Itv.mul (intI 18) lamI))
    (Itv.mul X (Itv.add (Itv.add a0I (Itv.mul a1I (subSqI X)))
      (Itv.mul (intI 3) (evI C Itv.one (subSqI X) (subSqI X)))))

theorem mem_resPairVal {C : IT} (hC : ITMem C cFnum) {i : Fin 24} {X : Fin 4}
    (h : rowSpec i = .pairVal X) : (resPairVal C (chordI X)).Mem (rowFun i pivotsNum) := by
  have hx := mem_chordI X
  have hw := mem_subSqI hx
  have hm := Itv.mem_sub (Itv.mem_sub Itv.mem_one (Itv.mem_mul (mem_intI 18) mem_lamI))
    (Itv.mem_mul hx (Itv.mem_add (Itv.mem_add mem_a0I (Itv.mem_mul mem_a1I hw))
      (Itv.mem_mul (mem_intI 3) (mem_evI hC Itv.mem_one hw hw))))
  have e : rowFun i pivotsNum = 1 - ((18 : ℤ) : ℝ) * lamFix - chord X * (a0Fix
      + a1Fix * (1 - chord X ^ 2 / 2)
      + ((3 : ℤ) : ℝ) * ev cFnum 1 (1 - chord X ^ 2 / 2) (1 - chord X ^ 2 / 2)) := by
    simp only [rowFun, h, evalRow, pairP, Fh_num]
    push_cast; ring
  rw [e]; exact hm

def resPairDer (C : IT) (X : Itv) : Itv :=
  Itv.add (Itv.neg (Itv.add (Itv.add a0I (Itv.mul a1I (subSqI X)))
      (Itv.mul (intI 3) (evI C Itv.one (subSqI X) (subSqI X)))))
    (Itv.mul (Itv.mul X X) (Itv.add a1I (Itv.mul (intI 3) (evIDiagD C (subSqI X)))))

theorem mem_resPairDer {C : IT} (hC : ITMem C cFnum) {i : Fin 24} {X : Fin 4}
    (h : rowSpec i = .pairDer X) : (resPairDer C (chordI X)).Mem (rowFun i pivotsNum) := by
  have hx := mem_chordI X
  have hw := mem_subSqI hx
  have hm := Itv.mem_add (Itv.mem_neg (Itv.mem_add (Itv.mem_add mem_a0I (Itv.mem_mul mem_a1I hw))
      (Itv.mem_mul (mem_intI 3) (mem_evI hC Itv.mem_one hw hw))))
    (Itv.mem_mul (Itv.mem_mul hx hx) (Itv.mem_add mem_a1I
      (Itv.mem_mul (mem_intI 3) (mem_evIDiagD hC hw))))
  have e : rowFun i pivotsNum = -(a0Fix + a1Fix * (1 - chord X ^ 2 / 2)
      + ((3 : ℤ) : ℝ) * ev cFnum 1 (1 - chord X ^ 2 / 2) (1 - chord X ^ 2 / 2))
      + chord X * chord X * (a1Fix + ((3 : ℤ) : ℝ) * evDiagD cFnum (1 - chord X ^ 2 / 2)) := by
    simp only [rowFun, h, evalRow]
    rw [deriv_pairP pivotsNum cFnum Fh_num]
    push_cast; ring
  rw [e]; exact hm

def resTriVal (G : IT) (A B C : Itv) : Itv :=
  Itv.sub (Itv.mul lamI (Itv.add (Itv.add (Itv.mul B C) (Itv.mul A C)) (Itv.mul A B)))
    (Itv.mul (Itv.mul (Itv.mul A B) C) (evI G (subSqI A) (subSqI B) (subSqI C)))

theorem mem_resTriVal {G : IT} (hG : ITMem G cFnum) {i : Fin 24} {m : Fin 5}
    (h : rowSpec i = .triVal m) :
    (resTriVal G (typeI m).1 (typeI m).2.1 (typeI m).2.2).Mem (rowFun i pivotsNum) := by
  obtain ⟨ha, hb, hc⟩ := mem_typeI m
  have hm := Itv.mem_sub (Itv.mem_mul mem_lamI (Itv.mem_add (Itv.mem_add (Itv.mem_mul hb hc)
      (Itv.mem_mul ha hc)) (Itv.mem_mul ha hb)))
    (Itv.mem_mul (Itv.mem_mul (Itv.mem_mul ha hb) hc)
      (mem_evI hG (mem_subSqI ha) (mem_subSqI hb) (mem_subSqI hc)))
  have e : rowFun i pivotsNum = triP pivotsNum (touchType m).1 (touchType m).2.1
      (touchType m).2.2 := by simp only [rowFun, h, evalRow]
  rw [e, triP, Fh_num]; exact hm

def resTriD (G : IT) (A B C : Itv) (c : Fin 3) : Itv :=
  let UA := subSqI A
  let UB := subSqI B
  let UC := subSqI C
  match (c : ℕ) with
  | 0 => Itv.add (Itv.sub (Itv.mul lamI (Itv.add B C)) (Itv.mul (Itv.mul B C) (evI G UA UB UC)))
      (Itv.mul (Itv.mul (Itv.mul (Itv.mul A A) B) C) (evID1 G UA UB UC))
  | 1 => Itv.add (Itv.sub (Itv.mul lamI (Itv.add A C)) (Itv.mul (Itv.mul A C) (evI G UA UB UC)))
      (Itv.mul (Itv.mul (Itv.mul (Itv.mul A B) B) C) (evID2 G UA UB UC))
  | _ => Itv.add (Itv.sub (Itv.mul lamI (Itv.add A B)) (Itv.mul (Itv.mul A B) (evI G UA UB UC)))
      (Itv.mul (Itv.mul (Itv.mul (Itv.mul A B) C) C) (evID3 G UA UB UC))

theorem mem_resTriD {G : IT} (hG : ITMem G cFnum) {i : Fin 24} {m : Fin 5} {c : Fin 3}
    (h : rowSpec i = .triD m c) :
    (resTriD G (typeI m).1 (typeI m).2.1 (typeI m).2.2 c).Mem (rowFun i pivotsNum) := by
  obtain ⟨ha, hb, hc⟩ := mem_typeI m
  have hua := mem_subSqI ha
  have hub := mem_subSqI hb
  have huc := mem_subSqI hc
  have e : rowFun i pivotsNum = deriv (triD pivotsNum m c) 0 := by simp only [rowFun, h, evalRow]
  rw [e]
  fin_cases c
  · have hd := (congrArg (fun f => deriv f 0) (triD_zero pivotsNum m)).trans
      (deriv_triP_1 pivotsNum cFnum Fh_num _ _ _)
    have hm := Itv.mem_add (Itv.mem_sub (Itv.mem_mul mem_lamI (Itv.mem_add hb hc))
      (Itv.mem_mul (Itv.mem_mul hb hc) (mem_evI hG hua hub huc)))
      (Itv.mem_mul (Itv.mem_mul (Itv.mem_mul (Itv.mem_mul ha ha) hb) hc) (mem_evID1 hG hua hub huc))
    rw [← hd] at hm
    exact hm
  · have hd := (congrArg (fun f => deriv f 0) (triD_one pivotsNum m)).trans
      (deriv_triP_2 pivotsNum cFnum Fh_num _ _ _)
    have hm := Itv.mem_add (Itv.mem_sub (Itv.mem_mul mem_lamI (Itv.mem_add ha hc))
      (Itv.mem_mul (Itv.mem_mul ha hc) (mem_evI hG hua hub huc)))
      (Itv.mem_mul (Itv.mem_mul (Itv.mem_mul (Itv.mem_mul ha hb) hb) hc) (mem_evID2 hG hua hub huc))
    rw [← hd] at hm
    exact hm
  · have hd := (congrArg (fun f => deriv f 0) (triD_two pivotsNum m)).trans
      (deriv_triP_3 pivotsNum cFnum Fh_num _ _ _)
    have hm := Itv.mem_add (Itv.mem_sub (Itv.mem_mul mem_lamI (Itv.mem_add ha hb))
      (Itv.mem_mul (Itv.mem_mul ha hb) (mem_evI hG hua hub huc)))
      (Itv.mem_mul (Itv.mem_mul (Itv.mem_mul (Itv.mem_mul ha hb) hc) hc) (mem_evID3 hG hua hub huc))
    rw [← hd] at hm
    exact hm

end Thomson.Task1b
