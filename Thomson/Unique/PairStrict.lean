import Thomson.Pair.Sweep

/-! # Uniqueness, step U3: the strict sweep

`UniquenessPlan.md`, U3.  The sweep of `Thomson.Pair.Sweep` carries a lower bound `p` for `Φ` from
grid point to grid point and checks `p ≥ 0`.  For uniqueness we need `Φ > 0` away from the double
zero; the computation is the same, with strict tests:

* in `runS` (vs `run`): `0 < p` and `0 < stepP …` instead of `0 ≤ p`, `0 ≤ stepP …`;
* in `sweepOKS` (vs `sweepOK`): `0 < cellLo …` on the first cell (so `Φ'' > 0` there, and
  `Φ(x) ≥ ½ Φ''_min (x − x₀)² > 0` for `x > x₀`) and `xh < g₁`.

The eight existing certificates `cellsFl … cellsAr` pass the strict checker unchanged
(`Thomson.Unique.PairStrictCerts`).  Soundness: `sweep_sound_pos`, `Φ > 0` on `(x₀, gEnd]`. -/

namespace Thomson.Pair

open Thomson.Tri5b Set

/-! ## The strict checker -/

/-- The sweep with strict tests: as `run`, but the lower bound for `f` must stay `> 0`. -/
def runS (F2 F3 F4 : List Itv) : ℤ → ℤ → ℤ → List (ℤ × ℤ × ℤ × ℤ) → Option ℤ
  | g, _, _, [] => some g
  | g, p, d, (g2, c, h, hh) :: rest =>
    if c - h ≤ g ∧ g2 ≤ c + h ∧ g < g2 ∧ 0 ≤ h ∧ h * h ≤ 2 * SCALE * hh ∧ 0 < p ∧
        (0 ≤ d ∨ cellLo F2 F3 F4 c h hh ≤ 0) ∧ 0 < stepP p d (cellLo F2 F3 F4 c h hh) (g2 - g)
    then runS F2 F3 F4 g2 (stepP p d (cellLo F2 F3 F4 c h hh) (g2 - g))
      (stepD d (cellLo F2 F3 F4 c h hh) (g2 - g)) rest
    else none

/-- **The strict sweep checker.**  As `sweepOK`, with `f'' > 0` on the first cell and `xh < g₁`,
and the strict `runS` for the rest. -/
def sweepOKS (F2 F3 F4 : List Itv) (xl xh gEnd : ℤ) : List (ℤ × ℤ × ℤ × ℤ) → Bool
  | [] => false
  | (g1, c, h, hh) :: rest =>
    decide (c - h ≤ xl ∧ g1 ≤ c + h ∧ xh < g1 ∧ 0 ≤ h ∧ h * h ≤ 2 * SCALE * hh ∧
        0 < cellLo F2 F3 F4 c h hh) &&
      decide (runS F2 F3 F4 g1 (stepP 0 0 (cellLo F2 F3 F4 c h hh) (g1 - xh))
        (stepD 0 (cellLo F2 F3 F4 c h hh) (g1 - xh)) rest = some gEnd)

/-! ## Soundness -/

/-- The minorant `P + D u + L u²/2` of one step is `> 0` on `(0, τ]`. -/
theorem quad_pos {P D L τ u : ℝ} (hP : 0 ≤ P) (hτ : 0 < τ) (hu0 : 0 < u) (huτ : u ≤ τ)
    (hend : 0 < P + D * τ + L * τ ^ 2 / 2) (hDL : 0 ≤ D ∨ L ≤ 0) :
    0 < P + D * u + L * u ^ 2 / 2 := by
  rcases le_or_gt L 0 with hL | hL
  · -- concave: above the chord through `u = 0` and `u = τ`
    have key : τ * (P + D * u + L * u ^ 2 / 2)
        = (τ - u) * P + u * (P + D * τ + L * τ ^ 2 / 2) + (-L) * u * τ * (τ - u) / 2 := by ring
    have h1 : 0 ≤ (-L) * u * τ * (τ - u) :=
      mul_nonneg (mul_nonneg (mul_nonneg (neg_nonneg.mpr hL) hu0.le) hτ.le) (sub_nonneg.mpr huτ)
    have : 0 < τ * (P + D * u + L * u ^ 2 / 2) := by
      rw [key]
      nlinarith [mul_nonneg (sub_nonneg.mpr huτ) hP, mul_pos hu0 hend]
    exact (mul_pos_iff_of_pos_left hτ).mp this
  · rcases hDL with hD | hL'
    · nlinarith [mul_pos hL (mul_pos hu0 hu0), mul_nonneg hD hu0.le]
    · linarith

variable {p : List ℝ} {F2 F3 F4 : List Itv}

theorem run_pos (h2 : LMem F2 (rder (rder p))) (h3 : LMem F3 (rder (rder (rder p))))
    (h4 : LMem F4 (rder (rder (rder (rder p))))) :
    ∀ (cells : List (ℤ × ℤ × ℤ × ℤ)) (g pp d gEnd : ℤ),
      runS F2 F3 F4 g pp d cells = some gEnd →
      (pp : ℝ) ≤ reval p ((g : ℝ) / SCALE) * SCALE →
      (d : ℝ) ≤ reval (rder p) ((g : ℝ) / SCALE) * SCALE →
      ∀ x : ℝ, (g : ℝ) / SCALE < x → x ≤ (gEnd : ℝ) / SCALE → 0 < reval p x := by
  have hS : (0 : ℝ) < SCALE := SCALE_pos'
  intro cells
  induction cells with
  | nil =>
    intro g pp d gEnd hrun _ _ x hx1 hx2
    simp only [runS, Option.some.injEq] at hrun
    subst hrun
    linarith
  | cons cell rest ih =>
    obtain ⟨g2, c, h, hh⟩ := cell
    intro g pp d gEnd hrun hp hd x hx1 hx2
    simp only [runS] at hrun
    split_ifs at hrun with hc
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := hc
    set l := cellLo F2 F3 F4 c h hh with hl
    set G : ℝ := (g : ℝ) / SCALE with hG
    set G2 : ℝ := (g2 : ℝ) / SCALE with hG2
    have hGG2 : G < G2 := by
      rw [hG, hG2]; exact div_lt_div_of_pos_right (by exact_mod_cast c3) hS
    -- `l` bounds `f''` on `[G, G2]`
    have hlow : ∀ ξ ∈ Icc G G2, (l : ℝ) / SCALE ≤ reval (rder (rder p)) ξ := by
      intro ξ hξ
      rw [div_le_iff₀ hS]
      refine cellLo_sound h2 h3 h4 c4 c5 ?_ ?_
      · have : (g : ℝ) ≤ ξ * SCALE := by rw [← div_le_iff₀ hS]; exact hξ.1
        have c1' : ((c - h : ℤ) : ℝ) ≤ g := by exact_mod_cast c1
        linarith
      · have : ξ * SCALE ≤ g2 := by rw [← le_div_iff₀ hS]; exact hξ.2
        have c2' : (g2 : ℝ) ≤ ((c + h : ℤ) : ℝ) := by exact_mod_cast c2
        linarith
    have T := taylor2_right (hasDerivAt_reval p) (hasDerivAt_reval (rder p)) hlow
    -- the step, in real units
    set P : ℝ := (pp : ℝ) / SCALE
    set D : ℝ := (d : ℝ) / SCALE
    set L : ℝ := (l : ℝ) / SCALE
    set τ : ℝ := G2 - G with hτ
    have hτ0 : 0 < τ := by rw [hτ]; linarith
    have hP : P ≤ reval p G := by rw [div_le_iff₀ hS]; exact hp
    have hD : D ≤ reval (rder p) G := by rw [div_le_iff₀ hS]; exact hd
    have hP0 : 0 ≤ P := div_nonneg (by exact_mod_cast c6.le) hS.le
    have ht : ((g2 - g : ℤ) : ℝ) = τ * SCALE := by
      rw [hτ, hG, hG2]; push_cast; field_simp
    have hstepP : (stepP pp d l (g2 - g) : ℝ) / SCALE ≤ P + D * τ + L * τ ^ 2 / 2 := by
      have := stepP_le pp d l (g2 - g) (by omega)
      rw [ht] at this
      rw [div_le_iff₀ hS]
      have e : ((pp : ℝ) + d * (τ * SCALE) / SCALE + l * (τ * SCALE) ^ 2 / (2 * SCALE ^ 2))
          = (P + D * τ + L * τ ^ 2 / 2) * SCALE := by
        simp only [P, D, L]; field_simp
      linarith
    have hstepD : (stepD d l (g2 - g) : ℝ) / SCALE ≤ D + L * τ := by
      have := stepD_le d l (g2 - g)
      rw [ht] at this
      rw [div_le_iff₀ hS]
      have e : ((d : ℝ) + l * (τ * SCALE) / SCALE) = (D + L * τ) * SCALE := by
        simp only [D, L]; field_simp
      linarith
    have hend : 0 < P + D * τ + L * τ ^ 2 / 2 := by
      have : (0 : ℝ) < (stepP pp d l (g2 - g) : ℝ) / SCALE :=
        div_pos (by exact_mod_cast c8) hS
      linarith
    have hDL : 0 ≤ D ∨ L ≤ 0 := by
      rcases c7 with h' | h'
      · exact Or.inl (div_nonneg (by exact_mod_cast h') hS.le)
      · exact Or.inr (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h') hS.le)
    rcases le_or_gt x G2 with hxG2 | hxG2
    · -- inside the step
      have hT := (T x ⟨hx1.le, hxG2⟩).2
      have hq := quad_pos hP0 hτ0 (sub_pos.mpr hx1) (by linarith) hend hDL
      have hlin : D * (x - G) ≤ reval (rder p) G * (x - G) :=
        mul_le_mul_of_nonneg_right hD (sub_nonneg.mpr hx1.le)
      linarith
    · -- beyond: the next steps
      refine ih g2 _ _ gEnd hrun ?_ ?_ x hxG2 hx2
      · have hT := (T G2 ⟨hGG2.le, le_rfl⟩).2
        have hlin : D * τ ≤ reval (rder p) G * τ := mul_le_mul_of_nonneg_right hD hτ0.le
        rw [← div_le_iff₀ hS]
        have : P + D * τ + L * τ ^ 2 / 2 ≤ reval p G2 := by
          simp only [τ] at hlin ⊢; linarith
        linarith
      · have hT := (T G2 ⟨hGG2.le, le_rfl⟩).1
        rw [← div_le_iff₀ hS]
        have : D + L * τ ≤ reval (rder p) G2 := by simp only [τ] at ⊢; linarith
        linarith

/-- **Soundness of the strict sweep.**  A double zero `x₀` of `f` enclosed by `[xl, xh]` and a
sweep accepted by the strict checker give `f > 0` on `(x₀, gEnd]`. -/
theorem sweep_sound_pos (h2 : LMem F2 (rder (rder p))) (h3 : LMem F3 (rder (rder (rder p))))
    (h4 : LMem F4 (rder (rder (rder (rder p))))) {xl xh gEnd : ℤ}
    {cells : List (ℤ × ℤ × ℤ × ℤ)} (hok : sweepOKS F2 F3 F4 xl xh gEnd cells = true)
    {x0 : ℝ} (hx0l : (xl : ℝ) ≤ x0 * SCALE) (hx0h : x0 * SCALE ≤ xh)
    (hf0 : reval p x0 = 0) (hf1 : reval (rder p) x0 = 0) :
    ∀ x : ℝ, x0 < x → x ≤ (gEnd : ℝ) / SCALE → 0 < reval p x := by
  have hS : (0 : ℝ) < SCALE := SCALE_pos'
  match cells, hok with
  | [], hok => simp [sweepOKS] at hok
  | (g1, c, h, hh) :: rest, hok =>
    simp only [sweepOKS, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨c1, c2, c3, c4, c5, c6⟩, hrun⟩ := hok
    set l := cellLo F2 F3 F4 c h hh with hl
    set G1 : ℝ := (g1 : ℝ) / SCALE with hG1
    have hlow : ∀ ξ ∈ Icc x0 G1, (l : ℝ) / SCALE ≤ reval (rder (rder p)) ξ := by
      intro ξ hξ
      rw [div_le_iff₀ hS]
      refine cellLo_sound h2 h3 h4 c4 c5 ?_ ?_
      · have c1' : ((c - h : ℤ) : ℝ) ≤ xl := by exact_mod_cast c1
        nlinarith [hξ.1]
      · have : ξ * SCALE ≤ g1 := by rw [← le_div_iff₀ hS]; exact hξ.2
        have c2' : (g1 : ℝ) ≤ ((c + h : ℤ) : ℝ) := by exact_mod_cast c2
        linarith
    have T := taylor2_right (hasDerivAt_reval p) (hasDerivAt_reval (rder p)) hlow
    rw [hf0, hf1] at T
    set L : ℝ := (l : ℝ) / SCALE
    have hL0 : 0 < L := div_pos (by exact_mod_cast c6) hS
    intro x hx1 hx2
    rcases le_or_gt x G1 with hxG1 | hxG1
    · have := (T x ⟨hx1.le, hxG1⟩).2
      have hsq : 0 < (x - x0) ^ 2 := by have := sub_pos.mpr hx1; positivity
      nlinarith [mul_pos hL0 hsq]
    · -- the rest of the sweep, from `g₁`
      have ht0 : 0 ≤ g1 - xh := by omega
      set τ : ℝ := ((g1 - xh : ℤ) : ℝ) / SCALE with hτ
      have hτ0 : 0 ≤ τ := div_nonneg (by exact_mod_cast ht0) hS.le
      have hτG : τ ≤ G1 - x0 := by
        have : x0 ≤ (xh : ℝ) / SCALE := by rw [le_div_iff₀ hS]; exact hx0h
        rw [hτ, hG1]; push_cast
        rw [sub_div]; linarith
      have hx0G1 : x0 ≤ G1 := by linarith
      have ht : ((g1 - xh : ℤ) : ℝ) = τ * SCALE := by rw [hτ]; field_simp
      refine run_pos h2 h3 h4 rest g1 _ _ gEnd hrun ?_ ?_ x hxG1 hx2
      · have hT := (T G1 ⟨hx0G1, le_rfl⟩).2
        have := stepP_le 0 0 l (g1 - xh) ht0
        rw [ht] at this
        have e : ((0 : ℤ) : ℝ) + ((0 : ℤ) : ℝ) * (τ * SCALE) / SCALE
            + l * (τ * SCALE) ^ 2 / (2 * SCALE ^ 2) = L * τ ^ 2 / 2 * SCALE := by
          simp only [L]; push_cast; field_simp; ring
        rw [e] at this
        have hsq : τ ^ 2 ≤ (G1 - x0) ^ 2 := pow_le_pow_left₀ hτ0 hτG 2
        have : L * τ ^ 2 / 2 ≤ reval p G1 := by
          nlinarith [mul_le_mul_of_nonneg_left hsq hL0.le]
        nlinarith
      · have hT := (T G1 ⟨hx0G1, le_rfl⟩).1
        have := stepD_le 0 l (g1 - xh)
        rw [ht] at this
        have e : ((0 : ℤ) : ℝ) + l * (τ * SCALE) / SCALE = L * τ * SCALE := by
          simp only [L]; push_cast; field_simp; ring
        rw [e] at this
        have : L * τ ≤ reval (rder p) G1 := by nlinarith [mul_le_mul_of_nonneg_left hτG hL0.le]
        nlinarith

end Thomson.Pair
