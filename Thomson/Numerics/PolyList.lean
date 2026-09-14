import Thomson.Numerics.TensorEngine

/-! # Task 5b, kernel layer, step 1: list polynomials

The covering is re-checked by `decide +kernel`, and the kernel is a very different machine from
the interpreter: it reduces terms lazily, has no arrays, and pays for every `match` and every
instance projection.  What it does well is structural recursion on lists and arithmetic on
`Nat` literals (GMP).  So the tensor of `F` is stored here as a nested list `List (List (List Itv))`
(index `u` outermost) and the Taylor shift is *Horner's* form of the shift — repeated
multiplication by `(x + a)` — which needs no binomial coefficients, no powers and no random
access: `p(x + a) = c₀ + (x + a)·q(x + a)` for `p = c₀ + x·q`.  Every multiplication in it is by
the exact point `a/SCALE` (`Itv.mulC`, two products instead of four).

This file: the operations on nested lists, their real semantics (`ev1`, `ev2`, `ev3`), the
enclosure relation (`Mem1`, `Mem2`, `Mem3`) and the lemmas that carry both through addition,
subtraction, scaling, the shift and the box normalisation.  The interface to the rest of the
development is `ofRT`: `ev3 (ofRT c) = ev c`, and a nested list of intervals enclosing `c`
entrywise encloses `ofRT c` (`Mem3_of_getL`). -/

namespace Thomson.Tri5b

open Finset

/-! ### Two cheaper multiplications -/

/-- Multiplication by the exact point `a/SCALE`: two products and no `min`/`max`. -/
def Itv.mulC (a : ℤ) (I : Itv) : Itv :=
  if 0 ≤ a then ⟨(a * I.lo) / SCALE, -((-(a * I.hi)) / SCALE)⟩
  else ⟨(a * I.hi) / SCALE, -((-(a * I.lo)) / SCALE)⟩

theorem Itv.lo_le_hi_of_mem {I : Itv} {x : ℝ} (hx : I.Mem x) : I.lo ≤ I.hi := by
  obtain ⟨h1, h2⟩ := hx
  exact_mod_cast le_trans h1 h2

theorem Itv.mulC_eq {I : Itv} (h : I.lo ≤ I.hi) (a : ℤ) : Itv.mulC a I = Itv.mul (Itv.cst a) I := by
  unfold Itv.mulC Itv.mul Itv.cst
  simp only
  split_ifs with ha
  · have h1 : a * I.lo ≤ a * I.hi := mul_le_mul_of_nonneg_left h ha
    rw [min_self, min_eq_left h1, max_self, max_eq_right h1]
  · push Not at ha
    have h1 : a * I.hi ≤ a * I.lo := mul_le_mul_of_nonpos_left h ha.le
    rw [min_self, min_eq_right h1, max_self, max_eq_left h1]

theorem Itv.mem_mulC {I : Itv} {x : ℝ} (hx : I.Mem x) (a : ℤ) :
    (Itv.mulC a I).Mem ((a : ℝ) / SCALE * x) := by
  rw [Itv.mulC_eq (Itv.lo_le_hi_of_mem hx)]
  exact Itv.mem_mul (Itv.mem_cst a) hx

theorem ediv_mul_le_gen (a : ℤ) {d : ℤ} (hd : 0 < d) : ((a / d : ℤ) : ℝ) * d ≤ (a : ℝ) := by
  have h1 := Int.mul_ediv_add_emod a d
  have h2 := Int.emod_nonneg a (by omega : d ≠ 0)
  have h1' : (d : ℝ) * ((a / d : ℤ) : ℝ) + ((a % d : ℤ) : ℝ) = (a : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h1
  have h2' : (0:ℝ) ≤ ((a % d : ℤ) : ℝ) := by exact_mod_cast h2
  nlinarith

theorem le_neg_ediv_mul_gen (a : ℤ) {d : ℤ} (hd : 0 < d) :
    (a : ℝ) ≤ ((-((-a) / d) : ℤ) : ℝ) * (d : ℝ) := by
  have := ediv_mul_le_gen (-a) hd
  push_cast at this ⊢
  linarith

/-- Multiplication by the exact nonnegative rational `n/d` (used with `n = h^i`, `d = SCALE^i`). -/
def Itv.mulQ (n d : ℤ) (I : Itv) : Itv := ⟨(n * I.lo) / d, -((-(n * I.hi)) / d)⟩

theorem Itv.mem_mulQ {I : Itv} {x : ℝ} (hx : I.Mem x) {n d : ℤ} (hn : 0 ≤ n) (hd : 0 < d) :
    (Itv.mulQ n d I).Mem ((n : ℝ) / d * x) := by
  obtain ⟨h1, h2⟩ := hx
  have hd' : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hn' : (0:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hS := SCALE_pos'
  have e : (n : ℝ) / d * x * SCALE = (n : ℝ) * (x * SCALE) / d := by field_simp
  constructor
  · show (((n * I.lo) / d : ℤ) : ℝ) ≤ (n : ℝ) / d * x * SCALE
    rw [e, le_div_iff₀ hd']
    refine le_trans (ediv_mul_le_gen _ hd) ?_
    push_cast
    exact mul_le_mul_of_nonneg_left h1 hn'
  · show (n : ℝ) / d * x * SCALE ≤ ((-((-(n * I.hi)) / d) : ℤ) : ℝ)
    rw [e, div_le_iff₀ hd']
    refine le_trans ?_ (le_neg_ediv_mul_gen _ hd)
    push_cast
    exact mul_le_mul_of_nonneg_left h2 hn'

/-! ### Generic list operations -/

/-- Add `c` to the constant term. -/
def addC {α : Type*} (add : α → α → α) (c : α) : List α → List α
  | [] => [c]
  | d :: l => add c d :: l

/-- The coefficients of `(x + a)·p(x)`, from those of `p`: `smul` is multiplication by `a`. -/
def mulXA {α : Type*} (add : α → α → α) (smul : α → α) : List α → List α
  | [] => []
  | c :: q => smul c :: addC add c (mulXA add smul q)

/-- The coefficients of `p(x + a)`: Horner's form of the Taylor shift. -/
def shiftL {α : Type*} (add : α → α → α) (smul : α → α) : List α → List α
  | [] => []
  | c :: q => addC add c (mulXA add smul (shiftL add smul q))

/-- `p ↦ (hp·p₀, hp·h·p₁, hp·h²·p₂, …)`, with the powers carried as exact fractions `hp/Sp`. -/
def scaleGen {α : Type*} (mq : ℤ → ℤ → α → α) (h : ℤ) : ℤ → ℤ → List α → List α
  | _, _, [] => []
  | hp, Sp, c :: q => mq hp Sp c :: scaleGen mq h (hp * h) (Sp * SCALE) q

/-- The real version of `scaleGen`. -/
def scaleGenR {α : Type*} (ms : ℝ → α → α) (h : ℝ) : ℝ → List α → List α
  | _, [] => []
  | hp, c :: q => ms hp c :: scaleGenR ms h (hp * h) q

/-! ### Real semantics of a coefficient list -/

/-- Horner evaluation, constant term first. -/
def ev1 : List ℝ → ℝ → ℝ
  | [], _ => 0
  | c :: q, x => c + x * ev1 q x

@[simp] theorem ev1_nil (x : ℝ) : ev1 [] x = 0 := rfl
@[simp] theorem ev1_cons (c : ℝ) (q : List ℝ) (x : ℝ) : ev1 (c :: q) x = c + x * ev1 q x := rfl

theorem ev1_map_smul (a : ℝ) (p : List ℝ) (x : ℝ) : ev1 (p.map (a * ·)) x = a * ev1 p x := by
  induction p with
  | nil => simp
  | cons c q ih => simp [ih]; ring

theorem ev1_map_addC {α : Type*} (add : α → α → α) (φ : α → ℝ)
    (hadd : ∀ x y, φ (add x y) = φ x + φ y) (c : α) (l : List α) (x : ℝ) :
    ev1 ((addC add c l).map φ) x = φ c + ev1 (l.map φ) x := by
  cases l with
  | nil => simp [addC]
  | cons d l => simp [addC, hadd]; ring

theorem ev1_map_mulXA {α : Type*} (add : α → α → α) (smul : α → α) (φ : α → ℝ) (a : ℝ)
    (hadd : ∀ x y, φ (add x y) = φ x + φ y) (hsmul : ∀ x, φ (smul x) = a * φ x)
    (p : List α) (x : ℝ) :
    ev1 ((mulXA add smul p).map φ) x = (x + a) * ev1 (p.map φ) x := by
  induction p with
  | nil => simp [mulXA]
  | cons c q ih =>
      simp only [mulXA, List.map_cons, ev1_cons, ev1_map_addC add φ hadd, ih, hsmul]
      ring

theorem ev1_map_shiftL {α : Type*} (add : α → α → α) (smul : α → α) (φ : α → ℝ) (a : ℝ)
    (hadd : ∀ x y, φ (add x y) = φ x + φ y) (hsmul : ∀ x, φ (smul x) = a * φ x)
    (p : List α) (x : ℝ) :
    ev1 ((shiftL add smul p).map φ) x = ev1 (p.map φ) (a + x) := by
  induction p with
  | nil => simp [shiftL]
  | cons c q ih =>
      simp only [shiftL, List.map_cons, ev1_cons, ev1_map_addC add φ hadd,
        ev1_map_mulXA add smul φ a hadd hsmul, ih]
      ring

theorem ev1_map_scaleGenR {α : Type*} (ms : ℝ → α → α) (φ : α → ℝ)
    (hms : ∀ s c, φ (ms s c) = s * φ c) (h : ℝ) (p : List α) (hp x : ℝ) :
    ev1 ((scaleGenR ms h hp p).map φ) x = hp * ev1 (p.map φ) (h * x) := by
  induction p generalizing hp with
  | nil => simp [scaleGenR]
  | cons c q ih =>
      simp only [scaleGenR, List.map_cons, ev1_cons, ih, hms]
      ring

/-! ### Enclosure, generically -/

theorem forall₂_addC {α β : Type*} {R : α → β → Prop} {addA : α → α → α} {addB : β → β → β}
    (hadd : ∀ x y x' y', R x x' → R y y' → R (addA x y) (addB x' y'))
    {c : α} {c' : β} (hc : R c c') {l : List α} {l' : List β} (h : List.Forall₂ R l l') :
    List.Forall₂ R (addC addA c l) (addC addB c' l') := by
  cases h with
  | nil => exact List.Forall₂.cons hc List.Forall₂.nil
  | cons hd tl => exact List.Forall₂.cons (hadd _ _ _ _ hc hd) tl

theorem forall₂_mulXA {α β : Type*} {R : α → β → Prop} {addA : α → α → α} {addB : β → β → β}
    {smulA : α → α} {smulB : β → β}
    (hadd : ∀ x y x' y', R x x' → R y y' → R (addA x y) (addB x' y'))
    (hsmul : ∀ x x', R x x' → R (smulA x) (smulB x'))
    {p : List α} {p' : List β} (h : List.Forall₂ R p p') :
    List.Forall₂ R (mulXA addA smulA p) (mulXA addB smulB p') := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hc ht ih => exact List.Forall₂.cons (hsmul _ _ hc) (forall₂_addC hadd hc ih)

theorem forall₂_shiftL {α β : Type*} {R : α → β → Prop} {addA : α → α → α} {addB : β → β → β}
    {smulA : α → α} {smulB : β → β}
    (hadd : ∀ x y x' y', R x x' → R y y' → R (addA x y) (addB x' y'))
    (hsmul : ∀ x x', R x x' → R (smulA x) (smulB x'))
    {p : List α} {p' : List β} (h : List.Forall₂ R p p') :
    List.Forall₂ R (shiftL addA smulA p) (shiftL addB smulB p') := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hc ht ih => exact forall₂_addC hadd hc (forall₂_mulXA hadd hsmul ih)

theorem forall₂_scaleGen {α β : Type*} {R : α → β → Prop} {mq : ℤ → ℤ → α → α}
    {ms : ℝ → β → β}
    (hmq : ∀ (n d : ℤ) x x', 0 ≤ n → 0 < d → R x x' → R (mq n d x) (ms ((n : ℝ) / d) x'))
    {h : ℤ} (hh : 0 ≤ h) :
    ∀ {hp Sp : ℤ}, 0 ≤ hp → 0 < Sp → ∀ {p : List α} {p' : List β}, List.Forall₂ R p p' →
      List.Forall₂ R (scaleGen mq h hp Sp p) (scaleGenR ms ((h : ℝ) / SCALE) ((hp : ℝ) / Sp) p') := by
  intro hp Sp hhp hSp p p' h
  induction h generalizing hp Sp with
  | nil => exact List.Forall₂.nil
  | cons hc ht ih =>
      refine List.Forall₂.cons (hmq _ _ _ _ hhp hSp hc) ?_
      have e : (hp : ℝ) / Sp * ((h : ℝ) / SCALE) = ((hp * h : ℤ) : ℝ) / ((Sp * SCALE : ℤ) : ℝ) := by
        push_cast; rw [div_mul_div_comm]
      rw [e]
      exact ih (mul_nonneg hhp hh) (mul_pos hSp SCALE_pos)

/-! ### The three levels -/

abbrev IL1 := List Itv
abbrev IL2 := List IL1
abbrev IL3 := List IL2
abbrev RL1 := List ℝ
abbrev RL2 := List RL1
abbrev RL3 := List RL2

/-- `ev2 P y z = Σⱼ (Σₖ Pⱼₖ zᵏ) yʲ`. -/
def ev2 (P : RL2) (y z : ℝ) : ℝ := ev1 (P.map fun r => ev1 r z) y
/-- `ev3 T x y z = Σᵢ (Σⱼ (Σₖ Tᵢⱼₖ zᵏ) yʲ) xⁱ`. -/
def ev3 (T : RL3) (x y z : ℝ) : ℝ := ev1 (T.map fun P => ev2 P y z) x

@[simp] theorem ev2_nil (y z : ℝ) : ev2 [] y z = 0 := rfl
@[simp] theorem ev2_cons (r : RL1) (P : RL2) (y z : ℝ) : ev2 (r :: P) y z = ev1 r z + y * ev2 P y z := rfl
@[simp] theorem ev3_nil (x y z : ℝ) : ev3 [] x y z = 0 := rfl
@[simp] theorem ev3_cons (P : RL2) (T : RL3) (x y z : ℝ) :
    ev3 (P :: T) x y z = ev2 P y z + x * ev3 T x y z := rfl

def Mem1 (P : IL1) (p : RL1) : Prop := List.Forall₂ Itv.Mem P p
def Mem2 (P : IL2) (p : RL2) : Prop := List.Forall₂ Mem1 P p
def Mem3 (T : IL3) (t : RL3) : Prop := List.Forall₂ Mem2 T t

/-! ### Addition, negation, subtraction (padded) -/

def addR1 : RL1 → RL1 → RL1
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: addR1 p q
def addR2 : RL2 → RL2 → RL2
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => addR1 a b :: addR2 p q
def addI1 : IL1 → IL1 → IL1
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => Itv.add a b :: addI1 p q
def addI2 : IL2 → IL2 → IL2
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => addI1 a b :: addI2 p q

def negR1 (p : RL1) : RL1 := p.map (fun c => -c)
def negR2 (p : RL2) : RL2 := p.map negR1
def negR3 (p : RL3) : RL3 := p.map negR2
def negI1 (p : IL1) : IL1 := p.map Itv.neg
def negI2 (p : IL2) : IL2 := p.map negI1
def negI3 (p : IL3) : IL3 := p.map negI2

def subR1 : RL1 → RL1 → RL1
  | [], q => negR1 q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a - b) :: subR1 p q
def subR2 : RL2 → RL2 → RL2
  | [], q => negR2 q
  | a :: p, [] => a :: p
  | a :: p, b :: q => subR1 a b :: subR2 p q
def subR3 : RL3 → RL3 → RL3
  | [], q => negR3 q
  | a :: p, [] => a :: p
  | a :: p, b :: q => subR2 a b :: subR3 p q
def subI1 : IL1 → IL1 → IL1
  | [], q => negI1 q
  | a :: p, [] => a :: p
  | a :: p, b :: q => Itv.sub a b :: subI1 p q
def subI2 : IL2 → IL2 → IL2
  | [], q => negI2 q
  | a :: p, [] => a :: p
  | a :: p, b :: q => subI1 a b :: subI2 p q
def subI3 : IL3 → IL3 → IL3
  | [], q => negI3 q
  | a :: p, [] => a :: p
  | a :: p, b :: q => subI2 a b :: subI3 p q

theorem ev1_addR1 (p q : RL1) (x : ℝ) : ev1 (addR1 p q) x = ev1 p x + ev1 q x := by
  induction p generalizing q with
  | nil => simp [addR1]
  | cons a p ih =>
      cases q with
      | nil => simp [addR1]
      | cons b q => simp [addR1, ih]; ring

theorem ev2_addR2 (p q : RL2) (y z : ℝ) : ev2 (addR2 p q) y z = ev2 p y z + ev2 q y z := by
  induction p generalizing q with
  | nil => simp [addR2]
  | cons a p ih =>
      cases q with
      | nil => simp [addR2]
      | cons b q => simp [addR2, ih, ev1_addR1]; ring

theorem ev1_negR1 (p : RL1) (x : ℝ) : ev1 (negR1 p) x = -ev1 p x := by
  induction p with
  | nil => simp [negR1]
  | cons a p ih => simp [negR1] at ih ⊢; rw [ih]; ring

theorem ev2_negR2 (p : RL2) (y z : ℝ) : ev2 (negR2 p) y z = -ev2 p y z := by
  induction p with
  | nil => simp [negR2]
  | cons a p ih => simp [negR2] at ih ⊢; rw [ih, ev1_negR1]; ring

theorem ev3_negR3 (p : RL3) (x y z : ℝ) : ev3 (negR3 p) x y z = -ev3 p x y z := by
  induction p with
  | nil => simp [negR3]
  | cons a p ih => simp [negR3] at ih ⊢; rw [ih, ev2_negR2]; ring

theorem ev1_subR1 (p q : RL1) (x : ℝ) : ev1 (subR1 p q) x = ev1 p x - ev1 q x := by
  induction p generalizing q with
  | nil => simp [subR1, ev1_negR1]
  | cons a p ih =>
      cases q with
      | nil => simp [subR1]
      | cons b q => simp [subR1, ih]; ring

theorem ev2_subR2 (p q : RL2) (y z : ℝ) : ev2 (subR2 p q) y z = ev2 p y z - ev2 q y z := by
  induction p generalizing q with
  | nil => simp [subR2, ev2_negR2]
  | cons a p ih =>
      cases q with
      | nil => simp [subR2]
      | cons b q => simp [subR2, ih, ev1_subR1]; ring

theorem ev3_subR3 (p q : RL3) (x y z : ℝ) : ev3 (subR3 p q) x y z = ev3 p x y z - ev3 q x y z := by
  induction p generalizing q with
  | nil => simp [subR3, ev3_negR3]
  | cons a p ih =>
      cases q with
      | nil => simp [subR3]
      | cons b q => simp [subR3, ih, ev2_subR2]; ring

theorem Mem1_addI1 {P Q : IL1} {p q : RL1} (hP : Mem1 P p) (hQ : Mem1 Q q) :
    Mem1 (addI1 P Q) (addR1 p q) := by
  unfold Mem1 at *
  induction hP generalizing Q q with
  | nil => simpa [addI1, addR1] using hQ
  | cons ha hp ih =>
      cases hQ with
      | nil => exact List.Forall₂.cons ha hp
      | cons hb hq => exact List.Forall₂.cons (Itv.mem_add ha hb) (ih hq)

theorem Mem2_addI2 {P Q : IL2} {p q : RL2} (hP : Mem2 P p) (hQ : Mem2 Q q) :
    Mem2 (addI2 P Q) (addR2 p q) := by
  unfold Mem2 at *
  induction hP generalizing Q q with
  | nil => simpa [addI2, addR2] using hQ
  | cons ha hp ih =>
      cases hQ with
      | nil => exact List.Forall₂.cons ha hp
      | cons hb hq => exact List.Forall₂.cons (Mem1_addI1 ha hb) (ih hq)

theorem Mem1_negI1 {P : IL1} {p : RL1} (hP : Mem1 P p) : Mem1 (negI1 P) (negR1 p) := by
  unfold Mem1 negI1 negR1 at *
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact hP.imp fun {_ _} h => Itv.mem_neg h

theorem Mem2_negI2 {P : IL2} {p : RL2} (hP : Mem2 P p) : Mem2 (negI2 P) (negR2 p) := by
  unfold Mem2 negI2 negR2 at *
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact hP.imp fun {_ _} h => Mem1_negI1 h

theorem Mem3_negI3 {P : IL3} {p : RL3} (hP : Mem3 P p) : Mem3 (negI3 P) (negR3 p) := by
  unfold Mem3 negI3 negR3 at *
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact hP.imp fun {_ _} h => Mem2_negI2 h

theorem Mem1_subI1 {P Q : IL1} {p q : RL1} (hP : Mem1 P p) (hQ : Mem1 Q q) :
    Mem1 (subI1 P Q) (subR1 p q) := by
  unfold Mem1 at *
  induction hP generalizing Q q with
  | nil => simp only [subI1, subR1]; exact Mem1_negI1 hQ
  | cons ha hp ih =>
      cases hQ with
      | nil => exact List.Forall₂.cons ha hp
      | cons hb hq => exact List.Forall₂.cons (Itv.mem_sub ha hb) (ih hq)

theorem Mem2_subI2 {P Q : IL2} {p q : RL2} (hP : Mem2 P p) (hQ : Mem2 Q q) :
    Mem2 (subI2 P Q) (subR2 p q) := by
  unfold Mem2 at *
  induction hP generalizing Q q with
  | nil => simp only [subI2, subR2]; exact Mem2_negI2 hQ
  | cons ha hp ih =>
      cases hQ with
      | nil => exact List.Forall₂.cons ha hp
      | cons hb hq => exact List.Forall₂.cons (Mem1_subI1 ha hb) (ih hq)

theorem Mem3_subI3 {P Q : IL3} {p q : RL3} (hP : Mem3 P p) (hQ : Mem3 Q q) :
    Mem3 (subI3 P Q) (subR3 p q) := by
  unfold Mem3 at *
  induction hP generalizing Q q with
  | nil => simp only [subI3, subR3]; exact Mem3_negI3 hQ
  | cons ha hp ih =>
      cases hQ with
      | nil => exact List.Forall₂.cons ha hp
      | cons hb hq => exact List.Forall₂.cons (Mem2_subI2 ha hb) (ih hq)

/-! ### Scalar multiples -/

def smulR1 (a : ℝ) (p : RL1) : RL1 := p.map (a * ·)
def smulR2 (a : ℝ) (p : RL2) : RL2 := p.map (smulR1 a)
def smulR3 (a : ℝ) (p : RL3) : RL3 := p.map (smulR2 a)
def smulI1 (a : ℤ) (p : IL1) : IL1 := p.map (Itv.mulC a)
def smulI2 (a : ℤ) (p : IL2) : IL2 := p.map (smulI1 a)
def smulI3 (a : ℤ) (p : IL3) : IL3 := p.map (smulI2 a)

theorem ev1_smulR1 (a : ℝ) (p : RL1) (x : ℝ) : ev1 (smulR1 a p) x = a * ev1 p x :=
  ev1_map_smul a p x

theorem ev2_smulR2 (a : ℝ) (p : RL2) (y z : ℝ) : ev2 (smulR2 a p) y z = a * ev2 p y z := by
  induction p with
  | nil => simp [smulR2]
  | cons r p ih => simp [smulR2] at ih ⊢; rw [ih, ev1_smulR1]; ring

theorem ev3_smulR3 (a : ℝ) (p : RL3) (x y z : ℝ) : ev3 (smulR3 a p) x y z = a * ev3 p x y z := by
  induction p with
  | nil => simp [smulR3]
  | cons P p ih => simp [smulR3] at ih ⊢; rw [ih, ev2_smulR2]; ring

theorem Mem1_smulI1 {P : IL1} {p : RL1} (hP : Mem1 P p) (a : ℤ) :
    Mem1 (smulI1 a P) (smulR1 ((a : ℝ) / SCALE) p) := by
  unfold Mem1 smulI1 smulR1 at *
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact hP.imp fun {_ _} h => Itv.mem_mulC h a

theorem Mem2_smulI2 {P : IL2} {p : RL2} (hP : Mem2 P p) (a : ℤ) :
    Mem2 (smulI2 a P) (smulR2 ((a : ℝ) / SCALE) p) := by
  unfold Mem2 smulI2 smulR2 at *
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact hP.imp fun {_ _} h => Mem1_smulI1 h a

theorem Mem3_smulI3 {P : IL3} {p : RL3} (hP : Mem3 P p) (a : ℤ) :
    Mem3 (smulI3 a P) (smulR3 ((a : ℝ) / SCALE) p) := by
  unfold Mem3 smulI3 smulR3 at *
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact hP.imp fun {_ _} h => Mem2_smulI2 h a

/-! ### The shift, axis by axis -/

/-- Shift the third variable (`z`) by `a`. -/
def shR3 (a : ℝ) (T : RL3) : RL3 := T.map (List.map (shiftL (· + ·) (a * ·)))
/-- Shift the second variable (`y`) by `a`. -/
def shR2 (a : ℝ) (T : RL3) : RL3 := T.map (shiftL addR1 (smulR1 a))
/-- Shift the first variable (`x`) by `a`. -/
def shR1 (a : ℝ) (T : RL3) : RL3 := shiftL addR2 (smulR2 a) T
def shI3 (a : ℤ) (T : IL3) : IL3 := T.map (List.map (shiftL Itv.add (Itv.mulC a)))
def shI2 (a : ℤ) (T : IL3) : IL3 := T.map (shiftL addI1 (smulI1 a))
def shI1 (a : ℤ) (T : IL3) : IL3 := shiftL addI2 (smulI2 a) T

theorem ev1_shiftL (a : ℝ) (p : RL1) (x : ℝ) : ev1 (shiftL (· + ·) (a * ·) p) x = ev1 p (a + x) := by
  have := ev1_map_shiftL (α := ℝ) (· + ·) (a * ·) id a (fun _ _ => rfl) (fun _ => rfl) p x
  simpa using this

theorem ev2_shiftL (a : ℝ) (P : RL2) (y z : ℝ) :
    ev2 (shiftL addR1 (smulR1 a) P) y z = ev2 P (a + y) z := by
  unfold ev2
  exact ev1_map_shiftL addR1 (smulR1 a) (fun r => ev1 r z) a
    (fun r s => ev1_addR1 r s z) (fun r => ev1_smulR1 a r z) P y

theorem ev3_shR3 (a : ℝ) (T : RL3) (x y z : ℝ) : ev3 (shR3 a T) x y z = ev3 T x y (a + z) := by
  unfold ev3 shR3
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun P _ => ?_
  simp only [Function.comp, ev2, List.map_map]
  congr 1
  exact List.map_congr_left fun r _ => by simp [ev1_shiftL]

theorem ev3_shR2 (a : ℝ) (T : RL3) (x y z : ℝ) : ev3 (shR2 a T) x y z = ev3 T x (a + y) z := by
  unfold ev3 shR2
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun P _ => by simp [ev2_shiftL]

theorem ev3_shR1 (a : ℝ) (T : RL3) (x y z : ℝ) : ev3 (shR1 a T) x y z = ev3 T (a + x) y z := by
  unfold ev3 shR1
  exact ev1_map_shiftL addR2 (smulR2 a) (fun P => ev2 P y z) a
    (fun P Q => ev2_addR2 P Q y z) (fun P => ev2_smulR2 a P y z) T x

theorem Mem1_shiftL {P : IL1} {p : RL1} (hP : Mem1 P p) (a : ℤ) :
    Mem1 (shiftL Itv.add (Itv.mulC a) P) (shiftL (· + ·) (((a : ℝ) / SCALE) * ·) p) :=
  forall₂_shiftL (fun _ _ _ _ hx hy => Itv.mem_add hx hy) (fun _ _ hx => Itv.mem_mulC hx a) hP

theorem Mem2_shiftL {P : IL2} {p : RL2} (hP : Mem2 P p) (a : ℤ) :
    Mem2 (shiftL addI1 (smulI1 a) P) (shiftL addR1 (smulR1 ((a : ℝ) / SCALE)) p) :=
  forall₂_shiftL (fun _ _ _ _ hx hy => Mem1_addI1 hx hy) (fun _ _ hx => Mem1_smulI1 hx a) hP

theorem Mem3_shI3 {T : IL3} {t : RL3} (hT : Mem3 T t) (a : ℤ) :
    Mem3 (shI3 a T) (shR3 ((a : ℝ) / SCALE) t) := by
  unfold Mem3 shI3 shR3 at *
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine hT.imp fun {P p} h => ?_
  unfold Mem2 at *
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact h.imp fun {r s} h => Mem1_shiftL h a

theorem Mem3_shI2 {T : IL3} {t : RL3} (hT : Mem3 T t) (a : ℤ) :
    Mem3 (shI2 a T) (shR2 ((a : ℝ) / SCALE) t) := by
  unfold Mem3 shI2 shR2 at *
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact hT.imp fun {P p} h => Mem2_shiftL h a

theorem Mem3_shI1 {T : IL3} {t : RL3} (hT : Mem3 T t) (a : ℤ) :
    Mem3 (shI1 a T) (shR1 ((a : ℝ) / SCALE) t) :=
  forall₂_shiftL (fun _ _ _ _ hx hy => Mem2_addI2 hx hy) (fun _ _ hx => Mem2_smulI2 hx a) hT

/-! ### Box normalisation: `x ↦ h·x` on each axis -/

def scR3 (h : ℝ) (T : RL3) : RL3 := T.map (List.map (scaleGenR (fun s c => s * c) h 1))
def scR2 (h : ℝ) (T : RL3) : RL3 := T.map (scaleGenR (fun s => smulR1 s) h 1)
def scR1 (h : ℝ) (T : RL3) : RL3 := scaleGenR (fun s => smulR2 s) h 1 T
def scI3 (h : ℤ) (T : IL3) : IL3 := T.map (List.map (scaleGen Itv.mulQ h 1 1))
def scI2 (h : ℤ) (T : IL3) : IL3 := T.map (scaleGen (fun n d => List.map (Itv.mulQ n d)) h 1 1)
def scI1 (h : ℤ) (T : IL3) : IL3 :=
  scaleGen (fun n d => List.map (List.map (Itv.mulQ n d))) h 1 1 T

theorem ev1_scaleGenR (h : ℝ) (p : RL1) (hp x : ℝ) :
    ev1 (scaleGenR (fun s c => s * c) h hp p) x = hp * ev1 p (h * x) := by
  have := ev1_map_scaleGenR (α := ℝ) (fun s c => s * c) id (fun _ _ => rfl) h p hp x
  simpa using this

theorem ev3_scR3 (h : ℝ) (T : RL3) (x y z : ℝ) : ev3 (scR3 h T) x y z = ev3 T x y (h * z) := by
  unfold ev3 scR3
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun P _ => ?_
  simp only [Function.comp, ev2, List.map_map]
  congr 1
  exact List.map_congr_left fun r _ => by simp [ev1_scaleGenR]

theorem ev3_scR2 (h : ℝ) (T : RL3) (x y z : ℝ) : ev3 (scR2 h T) x y z = ev3 T x (h * y) z := by
  unfold ev3 scR2
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun P _ => ?_
  simp only [Function.comp, ev2]
  have := ev1_map_scaleGenR (fun s => smulR1 s) (fun r => ev1 r z)
    (fun s r => ev1_smulR1 s r z) h P 1 y
  simpa using this

theorem ev3_scR1 (h : ℝ) (T : RL3) (x y z : ℝ) : ev3 (scR1 h T) x y z = ev3 T (h * x) y z := by
  unfold ev3 scR1
  have := ev1_map_scaleGenR (fun s => smulR2 s) (fun P => ev2 P y z)
    (fun s P => ev2_smulR2 s P y z) h T 1 x
  simpa using this

theorem Mem1_scaleGen {P : IL1} {p : RL1} (hP : Mem1 P p) {h : ℤ} (hh : 0 ≤ h) :
    Mem1 (scaleGen Itv.mulQ h 1 1 P) (scaleGenR (fun s c => s * c) ((h : ℝ) / SCALE) 1 p) := by
  have := forall₂_scaleGen (R := Itv.Mem) (mq := Itv.mulQ) (ms := fun s c => s * c)
    (fun n d x x' hn hd hx => Itv.mem_mulQ hx hn hd) hh (hp := 1) (Sp := 1) zero_le_one one_pos hP
  simp only [Int.cast_one, div_one] at this
  exact this

theorem Mem2_scaleGen {P : IL2} {p : RL2} (hP : Mem2 P p) {h : ℤ} (hh : 0 ≤ h) :
    Mem2 (scaleGen (fun n d => List.map (Itv.mulQ n d)) h 1 1 P)
      (scaleGenR (fun s => smulR1 s) ((h : ℝ) / SCALE) 1 p) := by
  have := forall₂_scaleGen (R := Mem1) (mq := fun n d => List.map (Itv.mulQ n d))
    (ms := fun s => smulR1 s) (fun n d x x' hn hd hx => by
      unfold Mem1 smulR1 at *
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact hx.imp fun {_ _} h => Itv.mem_mulQ h hn hd) hh (hp := 1) (Sp := 1) zero_le_one one_pos hP
  simp only [Int.cast_one, div_one] at this
  exact this

theorem Mem3_scI3 {T : IL3} {t : RL3} (hT : Mem3 T t) {h : ℤ} (hh : 0 ≤ h) :
    Mem3 (scI3 h T) (scR3 ((h : ℝ) / SCALE) t) := by
  unfold Mem3 scI3 scR3 at *
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine hT.imp fun {P p} h => ?_
  unfold Mem2 at *
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact h.imp fun {r s} h => Mem1_scaleGen h hh

theorem Mem3_scI2 {T : IL3} {t : RL3} (hT : Mem3 T t) {h : ℤ} (hh : 0 ≤ h) :
    Mem3 (scI2 h T) (scR2 ((h : ℝ) / SCALE) t) := by
  unfold Mem3 scI2 scR2 at *
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact hT.imp fun {P p} h => Mem2_scaleGen h hh

theorem Mem3_scI1 {T : IL3} {t : RL3} (hT : Mem3 T t) {h : ℤ} (hh : 0 ≤ h) :
    Mem3 (scI1 h T) (scR1 ((h : ℝ) / SCALE) t) := by
  have := forall₂_scaleGen (R := Mem2) (mq := fun n d => List.map (List.map (Itv.mulQ n d)))
    (ms := fun s => smulR2 s) (fun n d x x' hn hd hx => by
      unfold Mem2 smulR2 at *
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine hx.imp fun {r s} h => ?_
      unfold Mem1 smulR1 at *
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact h.imp fun {_ _} h => Itv.mem_mulQ h hn hd) hh (hp := 1) (Sp := 1) zero_le_one one_pos hT
  simp only [Int.cast_one, div_one] at this
  exact this

/-! ### Shift to the centre, then normalise to the box -/

/-- The coefficients of `P(a + h₁e₁, b + h₂e₂, d + h₃e₃)`, everything in units of `SCALE⁻¹`. -/
def shsc (a b d h1 h2 h3 : ℤ) (T : IL3) : IL3 :=
  scI1 h1 (scI2 h2 (scI3 h3 (shI3 d (shI2 b (shI1 a T)))))

def shscR (a b d h1 h2 h3 : ℝ) (T : RL3) : RL3 :=
  scR1 h1 (scR2 h2 (scR3 h3 (shR3 d (shR2 b (shR1 a T)))))

theorem ev3_shscR (a b d h1 h2 h3 : ℝ) (T : RL3) (e1 e2 e3 : ℝ) :
    ev3 (shscR a b d h1 h2 h3 T) e1 e2 e3 = ev3 T (a + h1 * e1) (b + h2 * e2) (d + h3 * e3) := by
  unfold shscR
  rw [ev3_scR1, ev3_scR2, ev3_scR3, ev3_shR3, ev3_shR2, ev3_shR1]

theorem Mem3_shsc {T : IL3} {t : RL3} (hT : Mem3 T t) (a b d : ℤ) {h1 h2 h3 : ℤ}
    (hh1 : 0 ≤ h1) (hh2 : 0 ≤ h2) (hh3 : 0 ≤ h3) :
    Mem3 (shsc a b d h1 h2 h3 T)
      (shscR ((a : ℝ) / SCALE) ((b : ℝ) / SCALE) ((d : ℝ) / SCALE)
        ((h1 : ℝ) / SCALE) ((h2 : ℝ) / SCALE) ((h3 : ℝ) / SCALE) t) :=
  Mem3_scI1 (Mem3_scI2 (Mem3_scI3 (Mem3_shI3 (Mem3_shI2 (Mem3_shI1 hT a) b) d) hh3) hh2) hh1

/-! ### The interface to `RT` -/

/-- The nested list of a `9×9×9` real tensor. -/
def ofRT (c : RT) : RL3 :=
  List.ofFn fun i : Fin 9 => List.ofFn fun j : Fin 9 => List.ofFn fun k : Fin 9 => c i j k

theorem ev1_ofFn {n : ℕ} (f : Fin n → ℝ) (x : ℝ) :
    ev1 (List.ofFn f) x = ∑ i : Fin n, f i * x ^ (i : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, ev1_cons, ih, Fin.sum_univ_succ, Finset.mul_sum]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring

theorem ev3_ofRT (c : RT) (u v t : ℝ) : ev3 (ofRT c) u v t = ev c u v t := by
  unfold ev3 ofRT ev
  rw [List.map_ofFn, ev1_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp, ev2]
  rw [List.map_ofFn, ev1_ofFn, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Function.comp]
  rw [ev1_ofFn, Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Entry `(i, j, k)` of a nested list, `0` beyond its ends. -/
def getL (L : IL3) (i j k : ℕ) : Itv := ((L.getD i []).getD j []).getD k Itv.zero

/-- A nested list is a full `9×9×9` table. -/
def Shape9 (L : IL3) : Prop :=
  L.length = 9 ∧ ∀ i < 9, (L.getD i []).length = 9 ∧ ∀ j < 9, ((L.getD i []).getD j []).length = 9

instance (L : IL3) : Decidable (Shape9 L) := by unfold Shape9; infer_instance

theorem forall₂_ofFn_of_getD {α β : Type*} {R : α → β → Prop} {n : ℕ} {l : List α} (d : α)
    (hl : l.length = n) {f : Fin n → β} (h : ∀ i : Fin n, R (l.getD i d) (f i)) :
    List.Forall₂ R l (List.ofFn f) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [hl], fun i h1 h2 => ?_⟩
  have hi : i < n := by simpa [hl] using h1
  have e1 : l.get ⟨i, h1⟩ = l.getD i d := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
  have e2 : (List.ofFn f).get ⟨i, h2⟩ = f ⟨i, hi⟩ := by
    simp [List.getElem_ofFn]
  rw [e1, e2]
  exact h ⟨i, hi⟩

/-- **The interface.**  A full table enclosing `c` entry by entry encloses `ofRT c`. -/
theorem Mem3_of_getL {L : IL3} (hs : Shape9 L) {c : RT}
    (h : ∀ i j k : Fin 9, (getL L i j k).Mem (c i j k)) : Mem3 L (ofRT c) := by
  obtain ⟨h0, hrest⟩ := hs
  refine forall₂_ofFn_of_getD [] h0 fun i => ?_
  obtain ⟨h1, hrest'⟩ := hrest i i.isLt
  refine forall₂_ofFn_of_getD [] h1 fun j => ?_
  refine forall₂_ofFn_of_getD Itv.zero (hrest' j j.isLt) fun k => ?_
  exact h i j k

end Thomson.Tri5b
