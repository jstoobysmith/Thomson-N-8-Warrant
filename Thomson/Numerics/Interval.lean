import Mathlib

/-! # Task 5b, step 5: verified fixed-point interval arithmetic

The box covering needs `≈10³` evaluations of a degree-24 polynomial in three variables whose
coefficients carry the algebraic constant `u*`; each evaluation is `≈10³` operations.  That is far
beyond what `norm_num` can do term by term, so the arithmetic is *reflected*: it is performed by
computable functions on `ℤ`, and each operation is accompanied by a soundness lemma saying that the
real number it models lies in the interval it returns.

Every endpoint is an integer multiple of `10⁻⁴⁰` (`SCALE`).  The scale is decimal on purpose: all
the certificate's data (`Bpoly`, `HfixTable`, `pivotsNum`, `lamFix`) and both endpoints of the
enclosure of `u*` (`Thomson.Antiprism.UStarSharp`) have denominators dividing `10⁴⁰`, so *no rounding at all*
happens when the data are read in; rounding occurs only in `Itv.mul`, where it is directed outwards
by `Int.ediv` (floor, since the divisor is positive) on the lower endpoint and its mirror image on
the upper one. -/

namespace Thomson.Tri5b

/-- Denominator of the fixed-point grid. -/
def SCALE : ℤ := 10000000000000000000000000000000000000000   -- `10 ^ 40`, written out: a numeral is a constant
                          -- to the compiler, `10 ^ 40` is a call to `Monoid.npow`

/-- `SCALE ^ 2`, as a numeral: see the comment on `SCALE`. -/
def SCALE2 : ℤ := 100000000000000000000000000000000000000000000000000000000000000000000000000000000
/-- `SCALE ^ 3`, as a numeral. -/
def SCALE3 : ℤ := 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

theorem SCALE2_eq : SCALE2 = SCALE ^ 2 := by unfold SCALE2 SCALE; norm_num
theorem SCALE3_eq : SCALE3 = SCALE ^ 3 := by unfold SCALE3 SCALE; norm_num

theorem SCALE_pos : (0:ℤ) < SCALE := by unfold SCALE; norm_num

theorem SCALE_pos' : (0:ℝ) < (SCALE : ℝ) := by exact_mod_cast SCALE_pos

/-- An interval with fixed-point endpoints: `⟨lo, hi⟩` denotes `[lo/SCALE, hi/SCALE]`. -/
structure Itv where
  lo : ℤ
  hi : ℤ
deriving DecidableEq, Repr, Inhabited

namespace Itv

/-- `x` is enclosed by `I`.  Stated multiplied by `SCALE`, which keeps `linarith` happy. -/
def Mem (I : Itv) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x * SCALE ∧ x * SCALE ≤ (I.hi : ℝ)

/-- Floor division by `SCALE`: `(a / SCALE) * SCALE ≤ a`. -/
theorem ediv_mul_le (a : ℤ) : ((a / SCALE : ℤ) : ℝ) * (SCALE : ℝ) ≤ (a : ℝ) := by
  have h1 := Int.mul_ediv_add_emod a SCALE
  have h2 := Int.emod_nonneg a SCALE_pos.ne'
  have h1' : (SCALE : ℝ) * ((a / SCALE : ℤ) : ℝ) + ((a % SCALE : ℤ) : ℝ) = (a : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h1
  have h2' : (0:ℝ) ≤ ((a % SCALE : ℤ) : ℝ) := by exact_mod_cast h2
  nlinarith

/-- Ceiling division by `SCALE`. -/
theorem le_neg_ediv_mul (a : ℤ) : (a : ℝ) ≤ ((-((-a) / SCALE) : ℤ) : ℝ) * (SCALE : ℝ) := by
  have := ediv_mul_le (-a)
  push_cast at this ⊢
  linarith

/-! ### The operations -/

def add (I J : Itv) : Itv := ⟨I.lo + J.lo, I.hi + J.hi⟩
def neg (I : Itv) : Itv := ⟨-I.hi, -I.lo⟩
def sub (I J : Itv) : Itv := add I (neg J)

/-- Multiplication: the four corner products, rounded outwards. -/
def mul (I J : Itv) : Itv :=
  let a := I.lo * J.lo
  let b := I.lo * J.hi
  let c := I.hi * J.lo
  let d := I.hi * J.hi
  ⟨(min (min a b) (min c d)) / SCALE, -((-(max (max a b) (max c d))) / SCALE)⟩

/-- The exact interval of an integer multiple of `10⁻⁴⁰`. -/
def cst (n : ℤ) : Itv := ⟨n, n⟩

def one : Itv := cst SCALE
def zero : Itv := cst 0

/-- A zero factor annihilates: `⌊0/SCALE⌋ = 0`.  The shift skips such products — most of the
tensor is zero, and all but `27` entries of the Gram tensor are. -/
theorem mul_zero_left {I J : Itv} (h1 : I.lo = 0) (h2 : I.hi = 0) : mul I J = zero := by
  unfold mul zero cst
  rw [h1, h2]
  simp

def npow (I : Itv) : ℕ → Itv
  | 0 => one
  | (n + 1) => mul I (npow I n)

/-- Horner evaluation of `Σ cₙ xⁿ` (coefficients from the constant term upwards). -/
def horner : List ℤ → Itv → Itv
  | [], _ => zero
  | (c :: cs), x => add (cst c) (mul x (horner cs x))

/-- Sum of a list of intervals. -/
def sumL (L : List Itv) : Itv := L.foldr add zero

/-- Is the interval entirely `≥ 0`? -/
def nonneg (I : Itv) : Bool := 0 ≤ I.lo

/-! ### Soundness -/

theorem mem_add {I J : Itv} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (add I J).Mem (x + y) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  constructor <;> simp only [add, Int.cast_add] <;> nlinarith

theorem mem_neg {I : Itv} {x : ℝ} (hx : I.Mem x) : (neg I).Mem (-x) := by
  obtain ⟨h1, h2⟩ := hx
  constructor <;> simp only [neg, Int.cast_neg] <;> nlinarith

theorem mem_sub {I J : Itv} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (sub I J).Mem (x - y) := by
  rw [sub_eq_add_neg]; exact mem_add hx (mem_neg hy)

theorem mem_cst (n : ℤ) : (cst n).Mem ((n : ℝ) / SCALE) := by
  have h := SCALE_pos'
  constructor <;> simp only [cst] <;> rw [div_mul_cancel₀ _ (ne_of_gt h)]

theorem mem_one : one.Mem 1 := by
  constructor <;> simp [Mem, one, cst]

theorem mem_zero : zero.Mem 0 := by
  constructor <;> simp [Mem, zero, cst]

/-- The bilinear minimum principle on a rectangle. -/
theorem min4_le_mul {a b c d x y : ℝ} (hx : a ≤ x) (hx' : x ≤ b) (hy : c ≤ y) (hy' : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y := by
  rcases le_total 0 y with hyp | hyp
  · have h1 : a * y ≤ x * y := mul_le_mul_of_nonneg_right hx hyp
    have h2 : min (a * c) (a * d) ≤ a * y := by
      rcases le_total 0 a with ha | ha
      · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hy ha)
      · exact le_trans (min_le_right _ _) (by nlinarith)
    exact le_trans (le_trans (min_le_left _ _) h2) h1
  · have h1 : b * y ≤ x * y := by nlinarith
    have h2 : min (b * c) (b * d) ≤ b * y := by
      rcases le_total 0 b with hb | hb
      · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hy hb)
      · exact le_trans (min_le_right _ _) (by nlinarith)
    exact le_trans (le_trans (min_le_right _ _) h2) h1

theorem mul_le_max4 {a b c d x y : ℝ} (hx : a ≤ x) (hx' : x ≤ b) (hy : c ≤ y) (hy' : y ≤ d) :
    x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  rcases le_total 0 y with hyp | hyp
  · have h1 : x * y ≤ b * y := mul_le_mul_of_nonneg_right hx' hyp
    have h2 : b * y ≤ max (b * c) (b * d) := by
      rcases le_total 0 b with hb | hb
      · exact le_trans (mul_le_mul_of_nonneg_left hy' hb) (le_max_right _ _)
      · exact le_trans (by nlinarith) (le_max_left _ _)
    exact le_trans (le_trans h1 h2) (le_max_right _ _)
  · have h1 : x * y ≤ a * y := by nlinarith
    have h2 : a * y ≤ max (a * c) (a * d) := by
      rcases le_total 0 a with ha | ha
      · exact le_trans (mul_le_mul_of_nonneg_left hy' ha) (le_max_right _ _)
      · exact le_trans (by nlinarith) (le_max_left _ _)
    exact le_trans (le_trans h1 h2) (le_max_left _ _)

theorem mem_mul {I J : Itv} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (mul I J).Mem (x * y) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  have hS := SCALE_pos'
  set X := x * (SCALE : ℝ) with hX
  set Y := y * (SCALE : ℝ) with hY
  have hxy : x * y * (SCALE : ℝ) = X * Y / (SCALE : ℝ) := by
    field_simp [hX, hY]; ring
  constructor
  · simp only [mul]
    rw [hxy, le_div_iff₀ hS]
    refine le_trans (ediv_mul_le _) ?_
    push_cast
    exact min4_le_mul h1 h2 h3 h4
  · simp only [mul]
    rw [hxy, div_le_iff₀ hS]
    refine le_trans ?_ (le_neg_ediv_mul _)
    push_cast
    exact mul_le_max4 h1 h2 h3 h4

theorem mem_npow {I : Itv} {x : ℝ} (hx : I.Mem x) : ∀ n, (npow I n).Mem (x ^ n)
  | 0 => by simpa [npow] using mem_one
  | (n + 1) => by
      have := mem_mul hx (mem_npow hx n)
      simpa [npow, pow_succ, mul_comm] using this

theorem mem_horner {x : ℝ} {X : Itv} (hx : X.Mem x) :
    ∀ (cs : List ℤ), (horner cs X).Mem (cs.foldr (fun c acc => (c : ℝ) / SCALE + x * acc) 0)
  | [] => by simpa [horner] using mem_zero
  | (c :: cs) => by
      simpa [horner] using mem_add (mem_cst c) (mem_mul hx (mem_horner hx cs))

theorem mem_sumL {α : Type*} (g : α → Itv) (h : α → ℝ) (hg : ∀ a, (g a).Mem (h a)) :
    ∀ (l : List α), (sumL (l.map g)).Mem ((l.map h).sum)
  | [] => by simpa [sumL] using mem_zero
  | (a :: as) => by
      simpa [sumL, List.foldr] using mem_add (hg a) (mem_sumL g h hg as)

/-- The version used on `Finset.univ`. -/
theorem mem_sum_fin {n : ℕ} (g : Fin n → Itv) (h : Fin n → ℝ) (hg : ∀ a, (g a).Mem (h a)) :
    (sumL ((List.finRange n).map g)).Mem (∑ i, h i) := by
  rw [Fin.sum_univ_def]
  exact mem_sumL g h hg _


/-- The enclosure of a quotient `n/d` of integers (`d > 0`), rounded outwards. -/
def ofDiv (n d : ℤ) : Itv := ⟨(n * SCALE) / d, -((-(n * SCALE)) / d)⟩

theorem mem_ofDiv {n d : ℤ} (hd : 0 < d) : (ofDiv n d).Mem ((n : ℝ) / d) := by
  have hd' : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hS := SCALE_pos'
  have key : ∀ a : ℤ, ((a / d : ℤ) : ℝ) * d ≤ (a : ℝ) := by
    intro a
    have h1 := Int.mul_ediv_add_emod a d
    have h2 := Int.emod_nonneg a (by omega : d ≠ 0)
    have h1' : (d : ℝ) * ((a / d : ℤ) : ℝ) + ((a % d : ℤ) : ℝ) = (a : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h1
    have h2' : (0:ℝ) ≤ ((a % d : ℤ) : ℝ) := by exact_mod_cast h2
    nlinarith
  simp only [Mem, ofDiv]
  constructor
  · have h := key (n * SCALE)
    push_cast at h ⊢
    rw [div_mul_eq_mul_div, le_div_iff₀ hd']
    nlinarith
  · have h := key (-(n * SCALE))
    push_cast at h ⊢
    rw [div_mul_eq_mul_div, div_le_iff₀ hd']
    nlinarith

theorem nonneg_sound {I : Itv} {x : ℝ} (hx : I.Mem x) (h : I.nonneg = true) : 0 ≤ x := by
  have h0 : (0:ℤ) ≤ I.lo := by simpa [nonneg] using h
  have h0' : (0:ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast h0
  have := hx.1
  nlinarith [SCALE_pos']

end Itv
end Thomson.Tri5b
