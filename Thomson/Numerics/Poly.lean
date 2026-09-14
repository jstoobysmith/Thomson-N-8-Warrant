import Thomson.Numerics.Interval

/-! # Task 4, step 1: polynomials as coefficient lists

The pair polynomial is a polynomial of degree `33` in one variable once it is written in
`w = 1 − s²/2` (`Thomson.Pair.Coeff`).  Everything Task 4 computes is a coefficient list of such a
polynomial — its coefficients, its derivatives, its mirror image `w ↦ −w` — so this file provides
the list operations twice, once on `ℝ` (to state and prove things) and once on the fixed-point
intervals `Itv` of Task 5b (to compute), together with

* the evaluation lemmas on `ℝ` (`reval_radd`, `reval_rmul`, …) and the derivative
  (`hasDerivAt_reval`);
* the enclosure lemmas: every interval operation encloses the real one (`LMem_ladd`, …,
  `mem_lev`).

Lists hold the constant term first.  The derivative and the mirror image are defined by the Horner
recursion `c + x·q(x)`, so that their correctness is one line each, and their interval versions
need no multiplication (`lder`, `lalt` are exact). -/

namespace Thomson.Pair

open Thomson.Tri5b

/-! ## Real coefficient lists -/

/-- Horner evaluation. -/
noncomputable def reval : List ℝ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => c + x * reval cs x

noncomputable def radd : List ℝ → List ℝ → List ℝ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: radd p q

noncomputable def rsmul (c : ℝ) (p : List ℝ) : List ℝ := p.map (c * ·)

noncomputable def rmul : List ℝ → List ℝ → List ℝ
  | [], _ => []
  | a :: p, q => radd (rsmul a q) (0 :: rmul p q)

/-- The derivative: `(c + x q)' = q + x q'` (and `c' = 0`, as the empty list). -/
noncomputable def rder : List ℝ → List ℝ
  | [] => []
  | [_] => []
  | _ :: c :: cs => radd (c :: cs) (0 :: rder (c :: cs))

/-- The mirror image `x ↦ p(−x)`: `c + x q(x) ↦ c + x (−q(−x))`. -/
noncomputable def ralt : List ℝ → List ℝ
  | [] => []
  | c :: cs => c :: (ralt cs).map (fun a => -a)

/-- Add `c` to the coefficient of `xⁿ`. -/
noncomputable def raddAt : ℕ → ℝ → List ℝ → List ℝ
  | 0, c, [] => [c]
  | 0, c, a :: l => (a + c) :: l
  | n + 1, c, [] => 0 :: raddAt n c []
  | n + 1, c, a :: l => a :: raddAt n c l

@[simp] theorem reval_nil (x : ℝ) : reval [] x = 0 := rfl
@[simp] theorem reval_cons (c : ℝ) (cs : List ℝ) (x : ℝ) :
    reval (c :: cs) x = c + x * reval cs x := rfl

theorem reval_radd : ∀ (p q : List ℝ) (x : ℝ), reval (radd p q) x = reval p x + reval q x
  | [], q, x => by simp [radd]
  | a :: p, [], x => by simp [radd]
  | a :: p, b :: q, x => by simp only [radd, reval_cons, reval_radd p q x]; ring

theorem reval_rsmul (c : ℝ) : ∀ (p : List ℝ) (x : ℝ), reval (rsmul c p) x = c * reval p x
  | [], x => by simp [rsmul]
  | a :: p, x => by
      have := reval_rsmul c p x
      simp only [rsmul, List.map_cons, reval_cons] at this ⊢
      rw [this]; ring

theorem reval_rmul : ∀ (p q : List ℝ) (x : ℝ), reval (rmul p q) x = reval p x * reval q x
  | [], q, x => by simp [rmul]
  | a :: p, q, x => by
      simp only [rmul, reval_radd, reval_rsmul, reval_cons, reval_rmul p q x]; ring

theorem reval_neg_map : ∀ (p : List ℝ) (x : ℝ), reval (p.map (fun a => -a)) x = -reval p x
  | [], x => by simp
  | a :: p, x => by simp only [List.map_cons, reval_cons, reval_neg_map p x]; ring

theorem reval_ralt : ∀ (p : List ℝ) (x : ℝ), reval (ralt p) x = reval p (-x)
  | [], x => by simp [ralt]
  | c :: cs, x => by simp only [ralt, reval_cons, reval_neg_map, reval_ralt cs x]; ring

theorem reval_raddAt : ∀ (n : ℕ) (c : ℝ) (l : List ℝ) (x : ℝ),
    reval (raddAt n c l) x = reval l x + c * x ^ n
  | 0, c, [], x => by simp [raddAt]
  | 0, c, a :: l, x => by simp [raddAt]; ring
  | n + 1, c, [], x => by
      simp only [raddAt, reval_cons, reval_raddAt n c [] x, reval_nil]; ring
  | n + 1, c, a :: l, x => by
      simp only [raddAt, reval_cons, reval_raddAt n c l x]; ring

/-- **The derivative of a coefficient list.** -/
theorem hasDerivAt_reval : ∀ (p : List ℝ) (x : ℝ), HasDerivAt (reval p) (reval (rder p) x) x
  | [], x => by
      show HasDerivAt (fun _ => (0:ℝ)) 0 x
      exact hasDerivAt_const x 0
  | [c], x => by
      show HasDerivAt (fun y => c + y * 0) 0 x
      simpa using hasDerivAt_const x c
  | c :: d :: cs, x => by
      have h : HasDerivAt (fun y => c + y * reval (d :: cs) y)
          (1 * reval (d :: cs) x + x * reval (rder (d :: cs)) x) x :=
        ((hasDerivAt_id x).mul (hasDerivAt_reval (d :: cs) x)).const_add c
      have e : reval (rder (c :: d :: cs)) x
          = 1 * reval (d :: cs) x + x * reval (rder (d :: cs)) x := by
        simp only [rder, reval_radd, reval_cons]; ring
      rw [e]; exact h

theorem differentiable_reval (p : List ℝ) : Differentiable ℝ (reval p) :=
  fun x => (hasDerivAt_reval p x).differentiableAt

theorem continuous_reval (p : List ℝ) : Continuous (reval p) :=
  (differentiable_reval p).continuous

/-! ## Interval coefficient lists -/

def ladd : List Itv → List Itv → List Itv
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => Itv.add a b :: ladd p q

def lsmul (c : Itv) (p : List Itv) : List Itv := p.map (Itv.mul c)

def lmul : List Itv → List Itv → List Itv
  | [], _ => []
  | a :: p, q => ladd (lsmul a q) (Itv.zero :: lmul p q)

def lder : List Itv → List Itv
  | [] => []
  | [_] => []
  | _ :: c :: cs => ladd (c :: cs) (Itv.zero :: lder (c :: cs))

def lalt : List Itv → List Itv
  | [] => []
  | c :: cs => c :: (lalt cs).map Itv.neg

def laddAt : ℕ → Itv → List Itv → List Itv
  | 0, c, [] => [c]
  | 0, c, a :: l => Itv.add a c :: l
  | n + 1, c, [] => Itv.zero :: laddAt n c []
  | n + 1, c, a :: l => a :: laddAt n c l

/-- Horner evaluation with interval coefficients. -/
def lev : List Itv → Itv → Itv
  | [], _ => Itv.zero
  | c :: cs, x => Itv.add c (Itv.mul x (lev cs x))

/-! ## Enclosure -/

/-- `P` encloses `p`, coefficient by coefficient. -/
abbrev LMem (P : List Itv) (p : List ℝ) : Prop :=
  List.Forall₂ (fun (I : Itv) (x : ℝ) => I.Mem x) P p

theorem LMem.nil : LMem [] [] := List.Forall₂.nil

theorem LMem.cons {I : Itv} {x : ℝ} {P : List Itv} {p : List ℝ} (h : I.Mem x) (hP : LMem P p) :
    LMem (I :: P) (x :: p) := List.Forall₂.cons h hP

theorem LMem_ladd {P Q : List Itv} {p q : List ℝ} (hP : LMem P p) (hQ : LMem Q q) :
    LMem (ladd P Q) (radd p q) := by
  induction hP generalizing Q q with
  | nil => simpa [ladd, radd] using hQ
  | cons h hP ih =>
    cases hQ with
    | nil => simpa [ladd, radd] using LMem.cons h hP
    | cons h' hQ => simpa [ladd, radd] using LMem.cons (Itv.mem_add h h') (ih hQ)

theorem LMem_lsmul {C : Itv} {c : ℝ} (hc : C.Mem c) {P : List Itv} {p : List ℝ}
    (hP : LMem P p) : LMem (lsmul C P) (rsmul c p) := by
  induction hP with
  | nil => exact LMem.nil
  | cons h _ ih => simpa [lsmul, rsmul] using LMem.cons (Itv.mem_mul hc h) ih

theorem LMem_lmul {P Q : List Itv} {p q : List ℝ} (hP : LMem P p) (hQ : LMem Q q) :
    LMem (lmul P Q) (rmul p q) := by
  induction hP with
  | nil => exact LMem.nil
  | cons h _ ih => exact LMem_ladd (LMem_lsmul h hQ) (LMem.cons Itv.mem_zero ih)

theorem LMem_lder {P : List Itv} {p : List ℝ} (hP : LMem P p) : LMem (lder P) (rder p) := by
  induction hP with
  | nil => exact LMem.nil
  | cons h hP ih =>
    cases hP with
    | nil => exact LMem.nil
    | cons h' hP' => exact LMem_ladd (LMem.cons h' hP') (LMem.cons Itv.mem_zero ih)

theorem LMem_map_neg {P : List Itv} {p : List ℝ} (hP : LMem P p) :
    LMem (P.map Itv.neg) (p.map (fun a => -a)) := by
  induction hP with
  | nil => exact LMem.nil
  | cons h _ ih => exact LMem.cons (Itv.mem_neg h) ih

theorem LMem_lalt {P : List Itv} {p : List ℝ} (hP : LMem P p) : LMem (lalt P) (ralt p) := by
  induction hP with
  | nil => exact LMem.nil
  | cons h _ ih => exact LMem.cons h (LMem_map_neg ih)

theorem LMem_laddAt {C : Itv} {c : ℝ} (hc : C.Mem c) (n : ℕ) {L : List Itv} {l : List ℝ}
    (hL : LMem L l) : LMem (laddAt n C L) (raddAt n c l) := by
  induction n generalizing L l with
  | zero =>
    cases hL with
    | nil => exact LMem.cons hc LMem.nil
    | cons h hL => exact LMem.cons (Itv.mem_add h hc) hL
  | succ n ih =>
    cases hL with
    | nil => exact LMem.cons Itv.mem_zero (ih LMem.nil)
    | cons h hL => exact LMem.cons h (ih hL)

theorem mem_lev {X : Itv} {x : ℝ} (hx : X.Mem x) {P : List Itv} {p : List ℝ} (hP : LMem P p) :
    (lev P X).Mem (reval p x) := by
  induction hP with
  | nil => simpa [lev] using Itv.mem_zero
  | cons h _ ih => simpa [lev] using Itv.mem_add h (Itv.mem_mul hx ih)

end Thomson.Pair
