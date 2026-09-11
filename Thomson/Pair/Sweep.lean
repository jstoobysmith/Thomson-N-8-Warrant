import Thomson.Pair.Poly
import Thomson.Pair.Taylor

/-! # Task 4, step 3: the sweep from a double zero

The pair polynomial vanishes to second order at the four chords, and its value just beside them
is `≈ 10⁻⁶` — far below what a direct enclosure of the certificate can resolve (see
`Thomson.Pair.Main`).  So positivity is not checked *pointwise* there but *integrated* from the
zero: starting from `f(x₀) = f'(x₀) = 0`, a lower bound `l ≤ f''` on each cell of a grid
`x₀ < g₁ < g₂ < …` gives lower bounds for `f` and `f'` at the next grid point, by the second-order
bound of `Thomson.Pair.Taylor`, and shows that the quadratic minorant stays `≥ 0` on the cell.  The
uncertainty of the data then enters only through `f''`, which is of size `10⁻²` at the chords.

* `cellLo` — a lower bound for `f''` on a cell `[c − h, c + h]`: `f''(c) − |f'''(c)|·h − K·h²/2`,
  with `K` an interval bound for `|f''''|` on the cell (`centred_lower`);
* `run`, `sweepOK` — the sweep, a `Bool`-valued checker on fixed-point integers;
* `sweep_sound` — `sweepOK … = true` and a double zero at `x₀` give `f ≥ 0` on `[x₀, gEnd]`.

Every number is an integer `n` standing for `n / SCALE` (`SCALE = 10⁴⁰`, Task 5b's grid); the
statements carry the factor `SCALE` on the real side, as `Itv.Mem` does. -/

namespace Thomson.Pair

open Thomson.Tri5b Set

/-! ## Arithmetic helpers -/

/-- Floor division by a positive integer lies below the real quotient. -/
theorem ediv_le_div (a b : ℤ) (hb : 0 < b) : ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  have h := Int.ediv_mul_le a hb.ne'
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [le_div_iff₀ hb']
  exact_mod_cast h

/-- An upper bound (× `SCALE`) for `|x|` on an interval. -/
def absHi (I : Itv) : ℤ := max I.hi (-I.lo)

theorem abs_le_absHi {I : Itv} {x : ℝ} (h : I.Mem x) : |x| * SCALE ≤ (absHi I : ℝ) := by
  obtain ⟨h1, h2⟩ := h
  have hS := SCALE_pos'
  have e : |x| * SCALE = |x * SCALE| := by rw [abs_mul, abs_of_pos hS]
  rw [e, absHi]
  push_cast
  rcases le_total 0 (x * SCALE) with h | h
  · rw [abs_of_nonneg h]; exact le_max_of_le_left h2
  · rw [abs_of_nonpos h]; exact le_max_of_le_right (by linarith)

/-! ## A lower bound for `f''` on a cell -/

/-- Lower bound (× `SCALE`) for `f''` on `[c − h, c + h]`, from the coefficient lists of `f''`,
`f'''`, `f''''`; `hh` is an upper bound for `h²/(2·SCALE)`. -/
def cellLo (F2 F3 F4 : List Itv) (c h hh : ℤ) : ℤ :=
  (lev F2 (Itv.cst c)).lo - (Itv.mul (Itv.cst (absHi (lev F3 (Itv.cst c)))) (Itv.cst h)).hi
    - (Itv.mul (Itv.cst (absHi (lev F4 ⟨c - h, c + h⟩))) (Itv.cst hh)).hi

theorem cellLo_sound {p : List ℝ} {F2 F3 F4 : List Itv}
    (h2 : LMem F2 (rder (rder p))) (h3 : LMem F3 (rder (rder (rder p))))
    (h4 : LMem F4 (rder (rder (rder (rder p))))) {c h hh : ℤ} (h0 : 0 ≤ h)
    (hhh : h * h ≤ 2 * SCALE * hh) {x : ℝ} (hx1 : ((c - h : ℤ) : ℝ) ≤ x * SCALE)
    (hx2 : x * SCALE ≤ ((c + h : ℤ) : ℝ)) :
    (cellLo F2 F3 F4 c h hh : ℝ) ≤ reval (rder (rder p)) x * SCALE := by
  have hS : (0 : ℝ) < SCALE := SCALE_pos'
  have hh0 : (0 : ℝ) ≤ h := by exact_mod_cast h0
  have hhh' : (h : ℝ) * h ≤ 2 * (SCALE : ℝ) * hh := by exact_mod_cast hhh
  set S : ℝ := (SCALE : ℝ) with hSdef
  set cr : ℝ := (c : ℝ) / S with hcr
  set hr : ℝ := (h : ℝ) / S with hhr
  have hcm : (Itv.cst c).Mem cr := Itv.mem_cst c
  set A3 := absHi (lev F3 (Itv.cst c)) with hA3def
  set K4 := absHi (lev F4 ⟨c - h, c + h⟩) with hK4def
  -- membership in the cell
  have hcell : ∀ ξ ∈ Icc (cr - hr) (cr + hr),
      (⟨c - h, c + h⟩ : Itv).Mem ξ := by
    intro ξ hξ
    have e1 : cr - hr = ((c : ℝ) - h) / S := by rw [hcr, hhr]; ring
    have e2 : cr + hr = ((c : ℝ) + h) / S := by rw [hcr, hhr]; ring
    obtain ⟨q1, q2⟩ := hξ
    rw [e1, div_le_iff₀ hS] at q1
    rw [e2, le_div_iff₀ hS] at q2
    constructor <;> push_cast <;> linarith
  have hK : ∀ ξ ∈ Icc (cr - hr) (cr + hr),
      |reval (rder (rder (rder (rder p)))) ξ| ≤ (K4 : ℝ) / S := by
    intro ξ hξ
    rw [le_div_iff₀ hS]
    exact abs_le_absHi (mem_lev (hcell ξ hξ) h4)
  have hxin : x ∈ Icc (cr - hr) (cr + hr) := by
    have e1 : cr - hr = ((c : ℝ) - h) / S := by rw [hcr, hhr]; ring
    have e2 : cr + hr = ((c : ℝ) + h) / S := by rw [hcr, hhr]; ring
    push_cast at hx1 hx2
    rw [e1, e2]
    exact ⟨by rw [div_le_iff₀ hS]; linarith, by rw [le_div_iff₀ hS]; linarith⟩
  have key := centred_lower (hasDerivAt_reval _) (hasDerivAt_reval _)
    (div_nonneg hh0 hS.le) hK x hxin
  have hK0 : (0 : ℝ) ≤ K4 := by
    have := abs_le_absHi (mem_lev (hcell cr ⟨by linarith [div_nonneg hh0 hS.le],
      by linarith [div_nonneg hh0 hS.le]⟩) h4)
    nlinarith [abs_nonneg (reval (rder (rder (rder (rder p)))) cr)]
  have hv2 := (mem_lev hcm h2).1
  have hA3 : |reval (rder (rder (rder p))) cr| * S ≤ A3 := abs_le_absHi (mem_lev hcm h3)
  have hM1 := (Itv.mem_mul (Itv.mem_cst A3) (Itv.mem_cst h)).2
  have hM2 := (Itv.mem_mul (Itv.mem_cst K4) (Itv.mem_cst hh)).2
  -- the three terms
  set V : ℝ := ((lev F2 (Itv.cst c)).lo : ℝ)
  set M1 : ℝ := ((Itv.mul (Itv.cst A3) (Itv.cst h)).hi : ℝ)
  set M2 : ℝ := ((Itv.mul (Itv.cst K4) (Itv.cst hh)).hi : ℝ)
  set P3 : ℝ := |reval (rder (rder (rder p))) cr|
  have e1 : (A3 : ℝ) / S * ((h : ℝ) / S) * S = A3 * h / S := by field_simp
  have e2 : (K4 : ℝ) / S * ((hh : ℝ) / S) * S = K4 * hh / S := by field_simp
  rw [e1] at hM1
  rw [e2] at hM2
  have t1 : P3 * h ≤ M1 := by
    refine le_trans ?_ hM1
    rw [le_div_iff₀ hS]
    nlinarith [abs_nonneg (reval (rder (rder (rder p))) cr)]
  have t2 : (K4 : ℝ) * h ^ 2 / (2 * S ^ 2) ≤ M2 := by
    refine le_trans ?_ hM2
    rw [div_le_div_iff₀ (by positivity) hS]
    nlinarith [mul_le_mul_of_nonneg_left hhh' (mul_nonneg hK0 hS.le)]
  have t3 : reval (rder (rder p)) cr * S - P3 * h - (K4 : ℝ) * h ^ 2 / (2 * S ^ 2)
      ≤ reval (rder (rder p)) x * S := by
    have e3 : (reval (rder (rder p)) cr - P3 * hr - (K4 : ℝ) / S * hr ^ 2 / 2) * S
        = reval (rder (rder p)) cr * S - P3 * h - (K4 : ℝ) * h ^ 2 / (2 * S ^ 2) := by
      rw [hhr]; field_simp
    rw [← e3]
    exact mul_le_mul_of_nonneg_right key hS.le
  have hcl : (cellLo F2 F3 F4 c h hh : ℝ) = V - M1 - M2 := by
    simp only [cellLo, V, M1, M2, A3, K4]; push_cast; ring
  rw [hcl]
  linarith

/-! ## The sweep -/

/-- The new lower bound for `f'` after a step of length `t` (all × `SCALE`). -/
def stepD (d l t : ℤ) : ℤ := d + l * t / SCALE

/-- The new lower bound for `f` after a step of length `t`: `p + d t + l t²/2`, rounded down. -/
def stepP (p d l t : ℤ) : ℤ := p + d * t / SCALE + l * t / SCALE * t / SCALE / 2

theorem stepD_le (d l t : ℤ) :
    (stepD d l t : ℝ) ≤ d + l * t / SCALE := by
  unfold stepD
  have := ediv_le_div (l * t) SCALE SCALE_pos
  push_cast at this ⊢
  linarith

theorem stepP_le (p d l t : ℤ) (ht : 0 ≤ t) :
    (stepP p d l t : ℝ) ≤ p + d * t / SCALE + l * t ^ 2 / (2 * SCALE ^ 2) := by
  have hS : (0 : ℝ) < SCALE := SCALE_pos'
  have ht' : (0 : ℝ) ≤ t := by exact_mod_cast ht
  unfold stepP
  have a1 := ediv_le_div (d * t) SCALE SCALE_pos
  have a2 := ediv_le_div (l * t) SCALE SCALE_pos
  have a3 := ediv_le_div (l * t / SCALE * t) SCALE SCALE_pos
  have a4 := ediv_le_div (l * t / SCALE * t / SCALE) 2 (by norm_num)
  push_cast at a1 a2 a3 a4 ⊢
  have b3 : ((l * t / SCALE : ℤ) : ℝ) * t / SCALE ≤ l * t / SCALE * t / SCALE := by
    apply div_le_div_of_nonneg_right _ hS.le
    exact mul_le_mul_of_nonneg_right a2 ht'
  have e : (l : ℝ) * t / SCALE * t / SCALE / 2 = l * t ^ 2 / (2 * SCALE ^ 2) := by
    field_simp
  linarith

/-- The sweep proper: from grid point `g`, with lower bounds `p ≤ f(g)`, `d ≤ f'(g)`, through the
cells `(g₂, c, h, hh)`, each step going from the current point to `g₂` inside `[c − h, c + h]`.
Returns the last grid point if every step is accepted. -/
def run (F2 F3 F4 : List Itv) : ℤ → ℤ → ℤ → List (ℤ × ℤ × ℤ × ℤ) → Option ℤ
  | g, _, _, [] => some g
  | g, p, d, (g2, c, h, hh) :: rest =>
    if c - h ≤ g ∧ g2 ≤ c + h ∧ g < g2 ∧ 0 ≤ h ∧ h * h ≤ 2 * SCALE * hh ∧ 0 ≤ p ∧
        (0 ≤ d ∨ cellLo F2 F3 F4 c h hh ≤ 0) ∧ 0 ≤ stepP p d (cellLo F2 F3 F4 c h hh) (g2 - g)
    then run F2 F3 F4 g2 (stepP p d (cellLo F2 F3 F4 c h hh) (g2 - g))
      (stepD d (cellLo F2 F3 F4 c h hh) (g2 - g)) rest
    else none

/-- **The sweep checker.**  `x₀ ∈ [xl, xh]` is the double zero; the first cell covers
`[xl, g₁]` and must have `f'' ≥ 0`. -/
def sweepOK (F2 F3 F4 : List Itv) (xl xh gEnd : ℤ) : List (ℤ × ℤ × ℤ × ℤ) → Bool
  | [] => false
  | (g1, c, h, hh) :: rest =>
    decide (c - h ≤ xl ∧ g1 ≤ c + h ∧ xh ≤ g1 ∧ 0 ≤ h ∧ h * h ≤ 2 * SCALE * hh ∧
        0 ≤ cellLo F2 F3 F4 c h hh) &&
      decide (run F2 F3 F4 g1 (stepP 0 0 (cellLo F2 F3 F4 c h hh) (g1 - xh))
        (stepD 0 (cellLo F2 F3 F4 c h hh) (g1 - xh)) rest = some gEnd)

/-- The minorant `P + D u + L u²/2` of one step is `≥ 0` on `[0, τ]`. -/
theorem quad_nonneg {P D L τ u : ℝ} (hP : 0 ≤ P) (hτ : 0 < τ) (hu0 : 0 ≤ u) (huτ : u ≤ τ)
    (hend : 0 ≤ P + D * τ + L * τ ^ 2 / 2) (hDL : 0 ≤ D ∨ L ≤ 0) :
    0 ≤ P + D * u + L * u ^ 2 / 2 := by
  rcases le_or_gt L 0 with hL | hL
  · -- concave: above the chord through `u = 0` and `u = τ`
    have key : τ * (P + D * u + L * u ^ 2 / 2)
        = (τ - u) * P + u * (P + D * τ + L * τ ^ 2 / 2) + (-L) * u * τ * (τ - u) / 2 := by ring
    have h1 : 0 ≤ (-L) * u * τ * (τ - u) :=
      mul_nonneg (mul_nonneg (mul_nonneg (neg_nonneg.mpr hL) hu0) hτ.le) (sub_nonneg.mpr huτ)
    have : 0 ≤ τ * (P + D * u + L * u ^ 2 / 2) := by
      rw [key]
      nlinarith [mul_nonneg (sub_nonneg.mpr huτ) hP, mul_nonneg hu0 hend]
    exact (mul_nonneg_iff_of_pos_left hτ).mp this
  · rcases hDL with hD | hL'
    · positivity
    · linarith

variable {p : List ℝ} {F2 F3 F4 : List Itv}

theorem run_sound (h2 : LMem F2 (rder (rder p))) (h3 : LMem F3 (rder (rder (rder p))))
    (h4 : LMem F4 (rder (rder (rder (rder p))))) :
    ∀ (cells : List (ℤ × ℤ × ℤ × ℤ)) (g pp d gEnd : ℤ),
      run F2 F3 F4 g pp d cells = some gEnd → 0 ≤ pp →
      (pp : ℝ) ≤ reval p ((g : ℝ) / SCALE) * SCALE →
      (d : ℝ) ≤ reval (rder p) ((g : ℝ) / SCALE) * SCALE →
      ∀ x : ℝ, (g : ℝ) / SCALE ≤ x → x ≤ (gEnd : ℝ) / SCALE → 0 ≤ reval p x := by
  have hS : (0 : ℝ) < SCALE := SCALE_pos'
  intro cells
  induction cells with
  | nil =>
    intro g pp d gEnd hrun hpp hp _ x hx1 hx2
    simp only [run, Option.some.injEq] at hrun
    subst hrun
    have hx : x = (g : ℝ) / SCALE := le_antisymm hx2 hx1
    subst hx
    have : (0 : ℝ) ≤ pp := by exact_mod_cast hpp
    nlinarith
  | cons cell rest ih =>
    obtain ⟨g2, c, h, hh⟩ := cell
    intro g pp d gEnd hrun hpp hp hd x hx1 hx2
    simp only [run] at hrun
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
    have hP0 : 0 ≤ P := div_nonneg (by exact_mod_cast hpp) hS.le
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
    have hend : 0 ≤ P + D * τ + L * τ ^ 2 / 2 := by
      have : (0 : ℝ) ≤ (stepP pp d l (g2 - g) : ℝ) / SCALE :=
        div_nonneg (by exact_mod_cast c8) hS.le
      linarith
    have hDL : 0 ≤ D ∨ L ≤ 0 := by
      rcases c7 with h' | h'
      · exact Or.inl (div_nonneg (by exact_mod_cast h') hS.le)
      · exact Or.inr (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h') hS.le)
    rcases le_total x G2 with hxG2 | hxG2
    · -- inside the step
      have hT := (T x ⟨hx1, hxG2⟩).2
      have hq := quad_nonneg hP0 hτ0 (sub_nonneg.mpr hx1) (by linarith) hend hDL
      have hlin : D * (x - G) ≤ reval (rder p) G * (x - G) :=
        mul_le_mul_of_nonneg_right hD (sub_nonneg.mpr hx1)
      linarith
    · -- beyond: the next steps
      refine ih g2 _ _ gEnd hrun c8 ?_ ?_ x hxG2 hx2
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

/-- **Soundness of the sweep.**  A double zero `x₀` of `f` enclosed by `[xl, xh]` and an accepted
sweep give `f ≥ 0` on `[x₀, gEnd]`. -/
theorem sweep_sound (h2 : LMem F2 (rder (rder p))) (h3 : LMem F3 (rder (rder (rder p))))
    (h4 : LMem F4 (rder (rder (rder (rder p))))) {xl xh gEnd : ℤ}
    {cells : List (ℤ × ℤ × ℤ × ℤ)} (hok : sweepOK F2 F3 F4 xl xh gEnd cells = true)
    {x0 : ℝ} (hx0l : (xl : ℝ) ≤ x0 * SCALE) (hx0h : x0 * SCALE ≤ xh)
    (hf0 : reval p x0 = 0) (hf1 : reval (rder p) x0 = 0) :
    ∀ x : ℝ, x0 ≤ x → x ≤ (gEnd : ℝ) / SCALE → 0 ≤ reval p x := by
  have hS : (0 : ℝ) < SCALE := SCALE_pos'
  match cells, hok with
  | [], hok => simp [sweepOK] at hok
  | (g1, c, h, hh) :: rest, hok =>
    simp only [sweepOK, Bool.and_eq_true, decide_eq_true_eq] at hok
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
    have hL0 : 0 ≤ L := div_nonneg (by exact_mod_cast c6) hS.le
    intro x hx1 hx2
    rcases le_total x G1 with hxG1 | hxG1
    · have := (T x ⟨hx1, hxG1⟩).2
      nlinarith [sq_nonneg (x - x0)]
    · -- the rest of the sweep, from `g₁`
      have ht0 : 0 ≤ g1 - xh := by omega
      set τ : ℝ := ((g1 - xh : ℤ) : ℝ) / SCALE with hτ
      have hτ0 : 0 ≤ τ := div_nonneg (by exact_mod_cast ht0) hS.le
      have hτG : τ ≤ G1 - x0 := by
        have : x0 ≤ (xh : ℝ) / SCALE := by rw [le_div_iff₀ hS]; exact hx0h
        rw [hτ, hG1]; push_cast
        rw [sub_div]; linarith
      have hx0G1 : x0 ≤ G1 := by linarith
      have hstart : 0 ≤ stepP 0 0 l (g1 - xh) := by
        unfold stepP
        have : 0 ≤ l * (g1 - xh) / SCALE := Int.ediv_nonneg (mul_nonneg c6 ht0) SCALE_pos.le
        have : 0 ≤ l * (g1 - xh) / SCALE * (g1 - xh) / SCALE :=
          Int.ediv_nonneg (mul_nonneg this ht0) SCALE_pos.le
        have : 0 ≤ l * (g1 - xh) / SCALE * (g1 - xh) / SCALE / 2 :=
          Int.ediv_nonneg this (by norm_num)
        simpa using this
      have ht : ((g1 - xh : ℤ) : ℝ) = τ * SCALE := by rw [hτ]; field_simp
      refine run_sound h2 h3 h4 rest g1 _ _ gEnd hrun hstart ?_ ?_ x hxG1 hx2
      · have hT := (T G1 ⟨hx0G1, le_rfl⟩).2
        have := stepP_le 0 0 l (g1 - xh) ht0
        rw [ht] at this
        have e : ((0 : ℤ) : ℝ) + ((0 : ℤ) : ℝ) * (τ * SCALE) / SCALE
            + l * (τ * SCALE) ^ 2 / (2 * SCALE ^ 2) = L * τ ^ 2 / 2 * SCALE := by
          simp only [L]; push_cast; field_simp; ring
        rw [e] at this
        have hsq : τ ^ 2 ≤ (G1 - x0) ^ 2 := pow_le_pow_left₀ hτ0 hτG 2
        have : L * τ ^ 2 / 2 ≤ reval p G1 := by nlinarith [mul_le_mul_of_nonneg_left hsq hL0]
        nlinarith
      · have hT := (T G1 ⟨hx0G1, le_rfl⟩).1
        have := stepD_le 0 l (g1 - xh)
        rw [ht] at this
        have e : ((0 : ℤ) : ℝ) + l * (τ * SCALE) / SCALE = L * τ * SCALE := by
          simp only [L]; push_cast; field_simp; ring
        rw [e] at this
        have : L * τ ≤ reval (rder p) G1 := by nlinarith [mul_le_mul_of_nonneg_left hτG hL0]
        nlinarith

end Thomson.Pair
