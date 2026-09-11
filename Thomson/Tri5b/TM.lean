import Thomson.Tri5b.Interval

/-! # Task 5b, step 6: quadratic Taylor models

Plain interval arithmetic is useless here: the quantity to be certified is a difference of two
numbers of size `5·10⁻²` whose difference is as small as `10⁻⁹`, so the dependency problem swamps
any box of usable size.  What is needed is a *centred* form — the value, gradient and Hessian at
the centre of the box, with a rigorous bound on the rest.

A `TM` is exactly that: for a box with centre `c` and half-widths `h`, write the point as
`c + h·e` with `e ∈ [-1,1]³` (the *normalised* coordinates — with them, every monomial `e^α` is
bounded by `1`, so a tail bound is just a sum of absolute values).  A `TM` carries integer
coefficients `c, gᵢ, qᵢⱼ` (all in units of `SCALE⁻¹`) and an integer radius `r`, and models the
real number `x` by

`|x · SCALE − (c + Σᵢ gᵢ eᵢ + Σᵢ≤ⱼ qᵢⱼ eᵢ eⱼ)| ≤ r`.

Addition is exact; multiplication truncates the degree-3 and degree-4 parts of the product into the
radius, together with the rounding needed to bring the product back to the fixed-point grid. -/

namespace Thomson.Tri5b

/-- A quadratic Taylor model in the three normalised box coordinates. -/
structure TM where
  c : ℤ
  g1 : ℤ
  g2 : ℤ
  g3 : ℤ
  q11 : ℤ
  q12 : ℤ
  q13 : ℤ
  q22 : ℤ
  q23 : ℤ
  q33 : ℤ
  r : ℤ
deriving Repr, Inhabited

namespace TM

/-- The polynomial part, as a real number. -/
def val (A : TM) (e1 e2 e3 : ℝ) : ℝ :=
  (A.c : ℝ) + A.g1 * e1 + A.g2 * e2 + A.g3 * e3
    + A.q11 * (e1 * e1) + A.q12 * (e1 * e2) + A.q13 * (e1 * e3)
    + A.q22 * (e2 * e2) + A.q23 * (e2 * e3) + A.q33 * (e3 * e3)

/-- `x` is modelled by `A` at the normalised point `(e1,e2,e3)`. -/
def Mem (A : TM) (x : ℝ) (e1 e2 e3 : ℝ) : Prop :=
  |x * SCALE - A.val e1 e2 e3| ≤ (A.r : ℝ)

/-- The normalised box: `|eᵢ| ≤ 1`. -/
def Box (e1 e2 e3 : ℝ) : Prop := |e1| ≤ 1 ∧ |e2| ≤ 1 ∧ |e3| ≤ 1

/-! ### Operations -/

def add (A B : TM) : TM :=
  ⟨A.c + B.c, A.g1 + B.g1, A.g2 + B.g2, A.g3 + B.g3,
   A.q11 + B.q11, A.q12 + B.q12, A.q13 + B.q13, A.q22 + B.q22, A.q23 + B.q23, A.q33 + B.q33,
   A.r + B.r⟩

def neg (A : TM) : TM :=
  ⟨-A.c, -A.g1, -A.g2, -A.g3, -A.q11, -A.q12, -A.q13, -A.q22, -A.q23, -A.q33, A.r⟩

def sub (A B : TM) : TM := add A (neg B)

/-- `Σ|gᵢ|`, `Σ|qᵢⱼ|`, and the total: the bounds of the linear, quadratic and whole parts on
the normalised box. -/
def linN (A : TM) : ℤ := |A.g1| + |A.g2| + |A.g3|
def quaN (A : TM) : ℤ := |A.q11| + |A.q12| + |A.q13| + |A.q22| + |A.q23| + |A.q33|
def absN (A : TM) : ℤ := |A.c| + A.linN + A.quaN

/-- Multiplication: the degree `≤ 2` part is kept, everything else goes into the radius. -/
def mul (A B : TM) : TM :=
  let c := A.c * B.c
  let g1 := A.c * B.g1 + B.c * A.g1
  let g2 := A.c * B.g2 + B.c * A.g2
  let g3 := A.c * B.g3 + B.c * A.g3
  let q11 := A.c * B.q11 + B.c * A.q11 + A.g1 * B.g1
  let q12 := A.c * B.q12 + B.c * A.q12 + A.g1 * B.g2 + A.g2 * B.g1
  let q13 := A.c * B.q13 + B.c * A.q13 + A.g1 * B.g3 + A.g3 * B.g1
  let q22 := A.c * B.q22 + B.c * A.q22 + A.g2 * B.g2
  let q23 := A.c * B.q23 + B.c * A.q23 + A.g2 * B.g3 + A.g3 * B.g2
  let q33 := A.c * B.q33 + B.c * A.q33 + A.g3 * B.g3
  let tail := A.linN * B.quaN + B.linN * A.quaN + A.quaN * B.quaN
      + A.absN * B.r + B.absN * A.r + A.r * B.r
  ⟨c / SCALE, g1 / SCALE, g2 / SCALE, g3 / SCALE,
   q11 / SCALE, q12 / SCALE, q13 / SCALE, q22 / SCALE, q23 / SCALE, q33 / SCALE,
   tail / SCALE + 11⟩

/-- The constant `n/SCALE`. -/
def cst (n : ℤ) : TM := ⟨n, 0,0,0, 0,0,0,0,0,0, 0⟩

def one : TM := cst SCALE
def zero : TM := cst 0

/-- An interval constant. -/
def ofItv (I : Itv) : TM := ⟨I.lo, 0,0,0, 0,0,0,0,0,0, I.hi - I.lo⟩

/-- The affine model of `centre/SCALE + (half/SCALE)·eᵢ`. -/
def var1 (centre half : ℤ) : TM := ⟨centre, half, 0,0, 0,0,0,0,0,0, 0⟩
def var2 (centre half : ℤ) : TM := ⟨centre, 0, half, 0, 0,0,0,0,0,0, 0⟩
def var3 (centre half : ℤ) : TM := ⟨centre, 0,0, half, 0,0,0,0,0,0, 0⟩

def npow (A : TM) : ℕ → TM
  | 0 => one
  | (n+1) => mul A (npow A n)

def sumL (L : List TM) : TM := L.foldr add zero

/-! ### Soundness -/

theorem mem_add {A B : TM} {x y e1 e2 e3 : ℝ} (hx : A.Mem x e1 e2 e3) (hy : B.Mem y e1 e2 e3) :
    (add A B).Mem (x + y) e1 e2 e3 := by
  unfold Mem at *
  have hv : (add A B).val e1 e2 e3 = A.val e1 e2 e3 + B.val e1 e2 e3 := by
    simp only [add, val]; push_cast; ring
  rw [hv]
  have : (x + y) * SCALE - (A.val e1 e2 e3 + B.val e1 e2 e3)
      = (x * SCALE - A.val e1 e2 e3) + (y * SCALE - B.val e1 e2 e3) := by ring
  rw [this]
  refine le_trans (abs_add_le _ _) ?_
  simp only [add, Int.cast_add]
  linarith

theorem mem_neg {A : TM} {x e1 e2 e3 : ℝ} (hx : A.Mem x e1 e2 e3) :
    (neg A).Mem (-x) e1 e2 e3 := by
  unfold Mem at *
  have hv : (neg A).val e1 e2 e3 = -(A.val e1 e2 e3) := by
    simp only [neg, val]; push_cast; ring
  rw [hv, show -x * SCALE - -(A.val e1 e2 e3) = -(x * SCALE - A.val e1 e2 e3) by ring, abs_neg]
  exact hx

theorem mem_sub {A B : TM} {x y e1 e2 e3 : ℝ} (hx : A.Mem x e1 e2 e3) (hy : B.Mem y e1 e2 e3) :
    (sub A B).Mem (x - y) e1 e2 e3 := by
  rw [sub_eq_add_neg]; exact mem_add hx (mem_neg hy)

theorem mem_cst (n : ℤ) : (cst n).Mem ((n : ℝ) / SCALE) 0 0 0 := by
  unfold Mem cst val
  rw [div_mul_cancel₀ _ (ne_of_gt SCALE_pos')]
  simp

/-- `cst` models its value at every point of the box. -/
theorem mem_cst' (n : ℤ) (e1 e2 e3 : ℝ) : (cst n).Mem ((n : ℝ) / SCALE) e1 e2 e3 := by
  unfold Mem cst val
  rw [div_mul_cancel₀ _ (ne_of_gt SCALE_pos')]
  simp

theorem mem_one (e1 e2 e3 : ℝ) : one.Mem 1 e1 e2 e3 := by
  have := mem_cst' SCALE e1 e2 e3
  rwa [div_self (ne_of_gt SCALE_pos')] at this

theorem mem_zero (e1 e2 e3 : ℝ) : zero.Mem 0 e1 e2 e3 := by
  unfold Mem zero cst val
  simp

theorem mem_ofItv {I : Itv} {x : ℝ} (hx : I.Mem x) (e1 e2 e3 : ℝ) :
    (ofItv I).Mem x e1 e2 e3 := by
  obtain ⟨h1, h2⟩ := hx
  unfold Mem ofItv val
  simp only
  rw [abs_le]
  push_cast
  constructor <;> linarith

theorem mem_var1 (centre half : ℤ) (e1 e2 e3 : ℝ) :
    (var1 centre half).Mem (((centre : ℝ) + half * e1) / SCALE) e1 e2 e3 := by
  unfold Mem var1 val
  rw [div_mul_cancel₀ _ (ne_of_gt SCALE_pos')]
  simp

theorem mem_var2 (centre half : ℤ) (e1 e2 e3 : ℝ) :
    (var2 centre half).Mem (((centre : ℝ) + half * e2) / SCALE) e1 e2 e3 := by
  unfold Mem var2 val
  rw [div_mul_cancel₀ _ (ne_of_gt SCALE_pos')]
  simp

theorem mem_var3 (centre half : ℤ) (e1 e2 e3 : ℝ) :
    (var3 centre half).Mem (((centre : ℝ) + half * e3) / SCALE) e1 e2 e3 := by
  unfold Mem var3 val
  rw [div_mul_cancel₀ _ (ne_of_gt SCALE_pos')]
  simp


/-! ### Multiplication -/

theorem ediv_err (a : ℤ) :
    0 ≤ (a : ℝ) / SCALE - ((a / SCALE : ℤ) : ℝ) ∧ (a : ℝ) / SCALE - ((a / SCALE : ℤ) : ℝ) < 1 := by
  have hS := SCALE_pos'
  have h1 := Int.mul_ediv_add_emod a SCALE
  have h2 := Int.emod_nonneg a SCALE_pos.ne'
  have h3 := Int.emod_lt_of_pos a SCALE_pos
  have h1' : (SCALE : ℝ) * ((a / SCALE : ℤ) : ℝ) + ((a % SCALE : ℤ) : ℝ) = (a : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h1
  have h2' : (0 : ℝ) ≤ ((a % SCALE : ℤ) : ℝ) := by exact_mod_cast h2
  have h3' : ((a % SCALE : ℤ) : ℝ) < (SCALE : ℝ) := by exact_mod_cast h3
  constructor
  · rw [sub_nonneg, le_div_iff₀ hS]; nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hS]; nlinarith

/-- One rounded coefficient contributes at most one unit of error. -/
theorem round_term (a : ℤ) (m : ℝ) (hm : |m| ≤ 1) :
    |((a : ℝ) / SCALE - ((a / SCALE : ℤ) : ℝ)) * m| ≤ 1 := by
  obtain ⟨h1, h2⟩ := ediv_err a
  rw [abs_mul, abs_of_nonneg h1]
  nlinarith [abs_nonneg m]

theorem abs_mul_le_one {p q : ℝ} (hp : |p| ≤ 1) (hq : |q| ≤ 1) : |p * q| ≤ 1 := by
  rw [abs_mul]; nlinarith [abs_nonneg p, abs_nonneg q]

/-- The linear part is bounded by the sum of the absolute values of its coefficients. -/
theorem abs_lin (A : TM) {e1 e2 e3 : ℝ} (he : Box e1 e2 e3) :
    |(A.g1 : ℝ) * e1 + A.g2 * e2 + A.g3 * e3| ≤ (A.linN : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := he
  have b1 : |(A.g1 : ℝ) * e1| ≤ |(A.g1 : ℝ)| := by
    rw [abs_mul]; nlinarith [abs_nonneg ((A.g1 : ℝ)), abs_nonneg e1]
  have b2 : |(A.g2 : ℝ) * e2| ≤ |(A.g2 : ℝ)| := by
    rw [abs_mul]; nlinarith [abs_nonneg ((A.g2 : ℝ)), abs_nonneg e2]
  have b3 : |(A.g3 : ℝ) * e3| ≤ |(A.g3 : ℝ)| := by
    rw [abs_mul]; nlinarith [abs_nonneg ((A.g3 : ℝ)), abs_nonneg e3]
  have := abs_add_le ((A.g1 : ℝ) * e1 + A.g2 * e2) ((A.g3 : ℝ) * e3)
  have := abs_add_le ((A.g1 : ℝ) * e1) ((A.g2 : ℝ) * e2)
  simp only [linN, Int.cast_add, Int.cast_abs]
  linarith

theorem abs_qua (A : TM) {e1 e2 e3 : ℝ} (he : Box e1 e2 e3) :
    |(A.q11 : ℝ) * (e1 * e1) + A.q12 * (e1 * e2) + A.q13 * (e1 * e3)
      + A.q22 * (e2 * e2) + A.q23 * (e2 * e3) + A.q33 * (e3 * e3)| ≤ (A.quaN : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := he
  have m11 := abs_mul_le_one h1 h1
  have m12 := abs_mul_le_one h1 h2
  have m13 := abs_mul_le_one h1 h3
  have m22 := abs_mul_le_one h2 h2
  have m23 := abs_mul_le_one h2 h3
  have m33 := abs_mul_le_one h3 h3
  have b : ∀ (z : ℤ) (m : ℝ), |m| ≤ 1 → |(z : ℝ) * m| ≤ |(z : ℝ)| := by
    intro z m hm; rw [abs_mul]; nlinarith [abs_nonneg ((z : ℝ)), abs_nonneg m]
  have b11 := b A.q11 _ m11
  have b12 := b A.q12 _ m12
  have b13 := b A.q13 _ m13
  have b22 := b A.q22 _ m22
  have b23 := b A.q23 _ m23
  have b33 := b A.q33 _ m33
  simp only [quaN, Int.cast_add, Int.cast_abs]
  have t1 := abs_add_le ((A.q11 : ℝ) * (e1*e1) + A.q12 * (e1*e2) + A.q13 * (e1*e3)
      + A.q22 * (e2*e2) + A.q23 * (e2*e3)) ((A.q33 : ℝ) * (e3*e3))
  have t2 := abs_add_le ((A.q11 : ℝ) * (e1*e1) + A.q12 * (e1*e2) + A.q13 * (e1*e3)
      + A.q22 * (e2*e2)) ((A.q23 : ℝ) * (e2*e3))
  have t3 := abs_add_le ((A.q11 : ℝ) * (e1*e1) + A.q12 * (e1*e2) + A.q13 * (e1*e3))
      ((A.q22 : ℝ) * (e2*e2))
  have t4 := abs_add_le ((A.q11 : ℝ) * (e1*e1) + A.q12 * (e1*e2)) ((A.q13 : ℝ) * (e1*e3))
  have t5 := abs_add_le ((A.q11 : ℝ) * (e1*e1)) ((A.q12 : ℝ) * (e1*e2))
  linarith

theorem abs_val (A : TM) {e1 e2 e3 : ℝ} (he : Box e1 e2 e3) :
    |A.val e1 e2 e3| ≤ (A.absN : ℝ) := by
  have hl := abs_lin A he
  have hq := abs_qua A he
  have h1 := abs_add_le ((A.c : ℝ) + ((A.g1 : ℝ) * e1 + A.g2 * e2 + A.g3 * e3))
      ((A.q11 : ℝ) * (e1 * e1) + A.q12 * (e1 * e2) + A.q13 * (e1 * e3)
        + A.q22 * (e2 * e2) + A.q23 * (e2 * e3) + A.q33 * (e3 * e3))
  have h2 := abs_add_le ((A.c : ℝ)) ((A.g1 : ℝ) * e1 + A.g2 * e2 + A.g3 * e3)
  have hv : A.val e1 e2 e3 = ((A.c : ℝ) + ((A.g1 : ℝ) * e1 + A.g2 * e2 + A.g3 * e3))
      + ((A.q11 : ℝ) * (e1 * e1) + A.q12 * (e1 * e2) + A.q13 * (e1 * e3)
        + A.q22 * (e2 * e2) + A.q23 * (e2 * e3) + A.q33 * (e3 * e3)) := by
    unfold val; ring
  simp only [absN, Int.cast_add, Int.cast_abs]
  rw [hv]
  linarith


theorem abs_sum10 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : ℝ}
    (h1 : |a1| ≤ 1) (h2 : |a2| ≤ 1) (h3 : |a3| ≤ 1) (h4 : |a4| ≤ 1) (h5 : |a5| ≤ 1)
    (h6 : |a6| ≤ 1) (h7 : |a7| ≤ 1) (h8 : |a8| ≤ 1) (h9 : |a9| ≤ 1) (h10 : |a10| ≤ 1) :
    |a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10| ≤ 10 := by
  rw [abs_le] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ⊢
  constructor <;> [linarith; linarith]

theorem abs_sum4 {a1 a2 a3 a4 b1 b2 b3 b4 : ℝ}
    (h1 : |a1| ≤ b1) (h2 : |a2| ≤ b2) (h3 : |a3| ≤ b3) (h4 : |a4| ≤ b4) :
    |a1 + a2 + a3 + a4| ≤ b1 + b2 + b3 + b4 := by
  rw [abs_le] at h1 h2 h3 h4 ⊢
  constructor <;> [linarith; linarith]

theorem mem_mul {A B : TM} {x y e1 e2 e3 : ℝ} (he : Box e1 e2 e3)
    (hx : A.Mem x e1 e2 e3) (hy : B.Mem y e1 e2 e3) : (mul A B).Mem (x * y) e1 e2 e3 := by
  obtain ⟨he1, he2, he3⟩ := he
  have hbox : Box e1 e2 e3 := ⟨he1, he2, he3⟩
  have hS := SCALE_pos'
  set P := A.val e1 e2 e3 with hP
  set Q := B.val e1 e2 e3 with hQ
  set ra := x * SCALE - P with hra
  set rb := y * SCALE - Q with hrb
  -- the three parts of each model
  set LA := (A.g1 : ℝ) * e1 + A.g2 * e2 + A.g3 * e3 with hLA
  set LB := (B.g1 : ℝ) * e1 + B.g2 * e2 + B.g3 * e3 with hLB
  set QA := (A.q11 : ℝ) * (e1 * e1) + A.q12 * (e1 * e2) + A.q13 * (e1 * e3)
      + A.q22 * (e2 * e2) + A.q23 * (e2 * e3) + A.q33 * (e3 * e3) with hQA
  set QB := (B.q11 : ℝ) * (e1 * e1) + B.q12 * (e1 * e2) + B.q13 * (e1 * e3)
      + B.q22 * (e2 * e2) + B.q23 * (e2 * e3) + B.q33 * (e3 * e3) with hQB
  -- the exact (unrounded) degree ≤ 2 part of the product
  set T : ℝ := ((A.c * B.c : ℤ) : ℝ)
      + ((A.c * B.g1 + B.c * A.g1 : ℤ) : ℝ) * e1
      + ((A.c * B.g2 + B.c * A.g2 : ℤ) : ℝ) * e2
      + ((A.c * B.g3 + B.c * A.g3 : ℤ) : ℝ) * e3
      + ((A.c * B.q11 + B.c * A.q11 + A.g1 * B.g1 : ℤ) : ℝ) * (e1 * e1)
      + ((A.c * B.q12 + B.c * A.q12 + A.g1 * B.g2 + A.g2 * B.g1 : ℤ) : ℝ) * (e1 * e2)
      + ((A.c * B.q13 + B.c * A.q13 + A.g1 * B.g3 + A.g3 * B.g1 : ℤ) : ℝ) * (e1 * e3)
      + ((A.c * B.q22 + B.c * A.q22 + A.g2 * B.g2 : ℤ) : ℝ) * (e2 * e2)
      + ((A.c * B.q23 + B.c * A.q23 + A.g2 * B.g3 + A.g3 * B.g2 : ℤ) : ℝ) * (e2 * e3)
      + ((A.c * B.q33 + B.c * A.q33 + A.g3 * B.g3 : ℤ) : ℝ) * (e3 * e3) with hT
  set R : ℝ := LA * QB + LB * QA + QA * QB with hR
  have hsplit : P * Q = T + R := by
    simp only [hP, hQ, hT, hR, hLA, hLB, hQA, hQB, val]
    push_cast
    ring
  -- bounds
  have bLA := abs_lin A hbox
  have bLB := abs_lin B hbox
  have bQA := abs_qua A hbox
  have bQB := abs_qua B hbox
  have bP := abs_val A hbox
  have bQ := abs_val B hbox
  have bra : |ra| ≤ (A.r : ℝ) := hx
  have brb : |rb| ≤ (B.r : ℝ) := hy
  have hRb : |R| ≤ (A.linN : ℝ) * B.quaN + (B.linN : ℝ) * A.quaN + (A.quaN : ℝ) * B.quaN := by
    have h1 : |LA * QB| ≤ (A.linN : ℝ) * B.quaN := by
      rw [abs_mul]
      exact mul_le_mul bLA bQB (abs_nonneg _) (le_trans (abs_nonneg _) bLA)
    have h2 : |LB * QA| ≤ (B.linN : ℝ) * A.quaN := by
      rw [abs_mul]
      exact mul_le_mul bLB bQA (abs_nonneg _) (le_trans (abs_nonneg _) bLB)
    have h3 : |QA * QB| ≤ (A.quaN : ℝ) * B.quaN := by
      rw [abs_mul]
      exact mul_le_mul bQA bQB (abs_nonneg _) (le_trans (abs_nonneg _) bQA)
    have t1 := abs_add_le (LA * QB + LB * QA) (QA * QB)
    have t2 := abs_add_le (LA * QB) (LB * QA)
    rw [hR]; linarith
  have hPb : |P * rb| ≤ (A.absN : ℝ) * B.r := by
    rw [abs_mul]; exact mul_le_mul bP brb (abs_nonneg _) (le_trans (abs_nonneg _) bP)
  have hQb : |Q * ra| ≤ (B.absN : ℝ) * A.r := by
    rw [abs_mul]; exact mul_le_mul bQ bra (abs_nonneg _) (le_trans (abs_nonneg _) bQ)
  have hrr : |ra * rb| ≤ (A.r : ℝ) * B.r := by
    rw [abs_mul]; exact mul_le_mul bra brb (abs_nonneg _) (le_trans (abs_nonneg _) bra)
  -- the identity for the product
  have hxy : x * y * SCALE * SCALE = T + R + P * rb + Q * ra + ra * rb := by
    have hx' : x * SCALE = P + ra := by rw [hra]; ring
    have hy' : y * SCALE = Q + rb := by rw [hrb]; ring
    have : (x * SCALE) * (y * SCALE) = (P + ra) * (Q + rb) := by rw [hx', hy']
    calc x * y * SCALE * SCALE = (x * SCALE) * (y * SCALE) := by ring
      _ = (P + ra) * (Q + rb) := this
      _ = P * Q + P * rb + Q * ra + ra * rb := by ring
      _ = T + R + P * rb + Q * ra + ra * rb := by rw [hsplit]
  -- the rounding
  have hround : |T / SCALE - (mul A B).val e1 e2 e3| ≤ 10 := by
    have expand : T / SCALE - (mul A B).val e1 e2 e3 =
        (((A.c * B.c : ℤ) : ℝ) / SCALE - (((A.c * B.c : ℤ) / SCALE : ℤ) : ℝ)) * 1
        + (((A.c * B.g1 + B.c * A.g1 : ℤ) : ℝ) / SCALE
            - (((A.c * B.g1 + B.c * A.g1 : ℤ) / SCALE : ℤ) : ℝ)) * e1
        + (((A.c * B.g2 + B.c * A.g2 : ℤ) : ℝ) / SCALE
            - (((A.c * B.g2 + B.c * A.g2 : ℤ) / SCALE : ℤ) : ℝ)) * e2
        + (((A.c * B.g3 + B.c * A.g3 : ℤ) : ℝ) / SCALE
            - (((A.c * B.g3 + B.c * A.g3 : ℤ) / SCALE : ℤ) : ℝ)) * e3
        + (((A.c * B.q11 + B.c * A.q11 + A.g1 * B.g1 : ℤ) : ℝ) / SCALE
            - (((A.c * B.q11 + B.c * A.q11 + A.g1 * B.g1 : ℤ) / SCALE : ℤ) : ℝ)) * (e1 * e1)
        + (((A.c * B.q12 + B.c * A.q12 + A.g1 * B.g2 + A.g2 * B.g1 : ℤ) : ℝ) / SCALE
            - (((A.c * B.q12 + B.c * A.q12 + A.g1 * B.g2 + A.g2 * B.g1 : ℤ) / SCALE : ℤ) : ℝ))
            * (e1 * e2)
        + (((A.c * B.q13 + B.c * A.q13 + A.g1 * B.g3 + A.g3 * B.g1 : ℤ) : ℝ) / SCALE
            - (((A.c * B.q13 + B.c * A.q13 + A.g1 * B.g3 + A.g3 * B.g1 : ℤ) / SCALE : ℤ) : ℝ))
            * (e1 * e3)
        + (((A.c * B.q22 + B.c * A.q22 + A.g2 * B.g2 : ℤ) : ℝ) / SCALE
            - (((A.c * B.q22 + B.c * A.q22 + A.g2 * B.g2 : ℤ) / SCALE : ℤ) : ℝ)) * (e2 * e2)
        + (((A.c * B.q23 + B.c * A.q23 + A.g2 * B.g3 + A.g3 * B.g2 : ℤ) : ℝ) / SCALE
            - (((A.c * B.q23 + B.c * A.q23 + A.g2 * B.g3 + A.g3 * B.g2 : ℤ) / SCALE : ℤ) : ℝ))
            * (e2 * e3)
        + (((A.c * B.q33 + B.c * A.q33 + A.g3 * B.g3 : ℤ) : ℝ) / SCALE
            - (((A.c * B.q33 + B.c * A.q33 + A.g3 * B.g3 : ℤ) / SCALE : ℤ) : ℝ)) * (e3 * e3) := by
      simp only [hT, mul, val]
      field_simp
      ring
    rw [expand]
    have o1 : |(1:ℝ)| ≤ 1 := by norm_num
    have r1 := round_term (A.c * B.c) 1 o1
    have r2 := round_term (A.c * B.g1 + B.c * A.g1) e1 he1
    have r3 := round_term (A.c * B.g2 + B.c * A.g2) e2 he2
    have r4 := round_term (A.c * B.g3 + B.c * A.g3) e3 he3
    have r5 := round_term (A.c * B.q11 + B.c * A.q11 + A.g1 * B.g1) _ (abs_mul_le_one he1 he1)
    have r6 := round_term (A.c * B.q12 + B.c * A.q12 + A.g1 * B.g2 + A.g2 * B.g1) _
        (abs_mul_le_one he1 he2)
    have r7 := round_term (A.c * B.q13 + B.c * A.q13 + A.g1 * B.g3 + A.g3 * B.g1) _
        (abs_mul_le_one he1 he3)
    have r8 := round_term (A.c * B.q22 + B.c * A.q22 + A.g2 * B.g2) _ (abs_mul_le_one he2 he2)
    have r9 := round_term (A.c * B.q23 + B.c * A.q23 + A.g2 * B.g3 + A.g3 * B.g2) _
        (abs_mul_le_one he2 he3)
    have r10 := round_term (A.c * B.q33 + B.c * A.q33 + A.g3 * B.g3) _ (abs_mul_le_one he3 he3)
    exact abs_sum10 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  -- put the pieces together
  have htb : |R + P * rb + Q * ra + ra * rb|
      ≤ ((A.linN * B.quaN + B.linN * A.quaN + A.quaN * B.quaN
          + A.absN * B.r + B.absN * A.r + A.r * B.r : ℤ) : ℝ) := by
    have := abs_sum4 hRb hPb hQb hrr
    push_cast at this ⊢
    linarith
  set tl : ℤ := A.linN * B.quaN + B.linN * A.quaN + A.quaN * B.quaN
      + A.absN * B.r + B.absN * A.r + A.r * B.r with htl
  have hr : (mul A B).r = tl / SCALE + 11 := by simp only [mul, htl]
  have hlow : ((tl / SCALE : ℤ) : ℝ) > (tl : ℝ) / SCALE - 1 := by
    have := (ediv_err tl).2; linarith
  have hdecomp : x * y * SCALE - (mul A B).val e1 e2 e3
      = (T / SCALE - (mul A B).val e1 e2 e3) + (R + P * rb + Q * ra + ra * rb) / SCALE := by
    have h := hxy
    field_simp at h ⊢
    linarith
  rw [Mem, hdecomp, hr]
  have hq : |(R + P * rb + Q * ra + ra * rb) / SCALE| ≤ (tl : ℝ) / SCALE := by
    rw [abs_div, abs_of_pos hS]
    gcongr
  have := abs_add_le (T / SCALE - (mul A B).val e1 e2 e3)
      ((R + P * rb + Q * ra + ra * rb) / SCALE)
  push_cast
  linarith


/-! ### Powers and sums -/

theorem mem_npow {A : TM} {x e1 e2 e3 : ℝ} (he : Box e1 e2 e3) (hx : A.Mem x e1 e2 e3) :
    ∀ n, (npow A n).Mem (x ^ n) e1 e2 e3
  | 0 => by simpa [npow] using mem_one e1 e2 e3
  | (n + 1) => by
      have := mem_mul he hx (mem_npow he hx n)
      simpa [npow, pow_succ, mul_comm] using this

theorem mem_sumL {α : Type*} (g : α → TM) (f : α → ℝ) {e1 e2 e3 : ℝ}
    (hg : ∀ a, (g a).Mem (f a) e1 e2 e3) :
    ∀ (l : List α), (sumL (l.map g)).Mem ((l.map f).sum) e1 e2 e3
  | [] => by simpa [sumL] using mem_zero e1 e2 e3
  | (a :: as) => by
      simpa [sumL, List.foldr] using mem_add (hg a) (mem_sumL g f hg as)

theorem mem_sum_fin {n : ℕ} (g : Fin n → TM) (f : Fin n → ℝ) {e1 e2 e3 : ℝ}
    (hg : ∀ a, (g a).Mem (f a) e1 e2 e3) :
    (sumL ((List.finRange n).map g)).Mem (∑ i, f i) e1 e2 e3 := by
  rw [Fin.sum_univ_def]
  exact mem_sumL g f hg _

/-! ### The lower bound on a box -/

/-- A lower bound for `g·e + q·e²` on `|e| ≤ 1`, in fixed-point integers. -/
def loAxis (g q : ℤ) : ℤ := if 2 * q ≤ |g| then q - |g| else -((g * g + 4 * q - 1) / (4 * q))

theorem loAxis_le (g q : ℤ) {e : ℝ} (he : |e| ≤ 1) :
    (loAxis g q : ℝ) ≤ (g : ℝ) * e + (q : ℝ) * (e * e) := by
  have hE0 : (0:ℝ) ≤ |e| := abs_nonneg e
  have hee : e * e = |e| * |e| := by rw [← abs_mul, abs_mul_self]
  have hge2 : -(|(g : ℝ)| * |e|) ≤ (g : ℝ) * e := by
    have h := neg_abs_le ((g : ℝ) * e); rwa [abs_mul] at h
  have hA0 : (0:ℝ) ≤ |(g : ℝ)| := abs_nonneg _
  unfold loAxis
  split_ifs with hc
  · have hc' : 2 * (q : ℝ) ≤ |(g : ℝ)| := by
      have h := (Int.cast_le (R := ℝ)).mpr hc
      push_cast at h; exact h
    have hfac : (0:ℝ) ≤ (1 - |e|) * (|(g : ℝ)| - (q : ℝ) * (1 + |e|)) := by
      refine mul_nonneg (by linarith) ?_
      rcases le_total 0 ((q : ℝ)) with hq0 | hq0
      · nlinarith
      · nlinarith
    push_cast
    nlinarith
  · push_neg at hc
    have hq0 : (0:ℤ) < q := by have := abs_nonneg g; omega
    have hq0' : (0:ℝ) < (q : ℝ) := by exact_mod_cast hq0
    have hD : (0:ℤ) < 4 * q := by omega
    set k : ℤ := (g * g + 4 * q - 1) / (4 * q) with hk
    have hdiv := Int.mul_ediv_add_emod (g * g + 4 * q - 1) (4 * q)
    rw [← hk] at hdiv
    have hm0 := Int.emod_nonneg (g * g + 4 * q - 1) (by omega : (4 * q : ℤ) ≠ 0)
    have hm1 := Int.emod_lt_of_pos (g * g + 4 * q - 1) hD
    have hkey : g * g ≤ 4 * q * k := by omega
    have hkey' : (g : ℝ) * g ≤ 4 * (q : ℝ) * (k : ℝ) := by exact_mod_cast hkey
    have hsq : (0:ℝ) ≤ ((q : ℝ) * e + (g : ℝ) / 2) ^ 2 := sq_nonneg _
    rw [Int.cast_neg]
    nlinarith [hsq, hkey', hq0']

/-- The certified lower bound for the modelled quantity on the whole box. -/
def loBound (A : TM) : ℤ :=
  A.c + loAxis A.g1 A.q11 + loAxis A.g2 A.q22 + loAxis A.g3 A.q33
    - |A.q12| - |A.q13| - |A.q23| - A.r

/-- Decide nonnegativity on the box. -/
def nonneg (A : TM) : Bool := 0 ≤ A.loBound

/-- The certified lower bound really is one. -/
theorem loBound_le {A : TM} {x e1 e2 e3 : ℝ} (he : Box e1 e2 e3) (hx : A.Mem x e1 e2 e3) :
    (A.loBound : ℝ) ≤ x * SCALE := by
  obtain ⟨he1, he2, he3⟩ := he
  have a1 := loAxis_le A.g1 A.q11 he1
  have a2 := loAxis_le A.g2 A.q22 he2
  have a3 := loAxis_le A.g3 A.q33 he3
  have b : ∀ (z : ℤ) (p q : ℝ), |p| ≤ 1 → |q| ≤ 1 → -|(z : ℝ)| ≤ (z : ℝ) * (p * q) := by
    intro z p q hp hq
    have h1 : |(z : ℝ) * (p * q)| ≤ |(z : ℝ)| := by
      rw [abs_mul]
      nlinarith [abs_nonneg ((z : ℝ)), abs_nonneg (p * q), abs_mul_le_one hp hq]
    linarith [(abs_le.mp h1).1]
  have b12 := b A.q12 e1 e2 he1 he2
  have b13 := b A.q13 e1 e3 he1 he3
  have b23 := b A.q23 e2 e3 he2 he3
  have hval : (A.loBound : ℝ) + A.r ≤ A.val e1 e2 e3 := by
    simp only [loBound, val, Int.cast_add, Int.cast_sub, Int.cast_abs]
    push_cast
    linarith
  have := (abs_le.mp hx).1
  linarith

theorem nonneg_sound {A : TM} {x e1 e2 e3 : ℝ} (he : Box e1 e2 e3) (hx : A.Mem x e1 e2 e3)
    (h : A.nonneg = true) : 0 ≤ x := by
  have hlb : (0:ℤ) ≤ A.loBound := by simpa [nonneg] using h
  have hlb' : (0:ℝ) ≤ (A.loBound : ℝ) := by exact_mod_cast hlb
  have := loBound_le he hx
  nlinarith [SCALE_pos']

/-- Certify a positive margin: `m/SCALE ≤ x`. -/
def geBound (m : ℤ) (A : TM) : Bool := m ≤ A.loBound

theorem geBound_sound {A : TM} {m : ℤ} {x e1 e2 e3 : ℝ} (he : Box e1 e2 e3)
    (hx : A.Mem x e1 e2 e3) (h : geBound m A = true) : (m : ℝ) / SCALE ≤ x := by
  have hlb : m ≤ A.loBound := by simpa [geBound] using h
  have hlb' : (m : ℝ) ≤ (A.loBound : ℝ) := by exact_mod_cast hlb
  have h2 := loBound_le he hx
  rw [div_le_iff₀ SCALE_pos']
  linarith

end TM
end Thomson.Tri5b
