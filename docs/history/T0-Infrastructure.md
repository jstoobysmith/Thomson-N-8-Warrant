# T0 — Verified interval arithmetic, the expression language, and the two Taylor lemmas

*Shared by 1a, 1b, 2, 4, 5a, 5b.  Data-independent except for the mirrored tables (§5).
Estimated size: 1200 lines of Lean.  Do it in the order given; each section builds alone.*

## 0. Deliverables

| file | content |
|---|---|
| `Thomson/Interval/Iv.lean` | `Iv`, arithmetic, `mem`, soundness |
| `Thomson/Interval/Expr.lean` | `E`, `eval`, `ieval`, `deriv`, `subst`, `sum`, soundness, chain rule |
| `Thomson/Interval/Taylor.lean` | `taylor2_lower`, `taylor3_lower` |
| `Thomson/Interval/Atoms.lean` | `atomVal`, `atomEnv`, `atomEnv_mem` (needs the 1b enclosures) |
| `Thomson/ThreePoint/Mirror.lean` | `BpolyE, S3E, HpE, FhE, GhE, pairPE, triPE` and the bridge lemmas |
| `scripts/threepoint/task1_emit_lean.py` (extended) | also emits `BpolyE`, `HfixQ`, `pivotsNumQ` |

## 1. `Iv` (`Thomson/Interval/Iv.lean`)

```lean
/-- Closed interval `[lo, hi] / 2^prec`. -/
structure Iv where
  lo : ℤ
  hi : ℤ
deriving DecidableEq, Repr

def Iv.prec : ℕ := 128
def Iv.sc : ℤ := 2 ^ Iv.prec                     -- keep it a `def`, never unfold in proofs

/-- Real semantics. -/
def Iv.mem (I : Iv) (x : ℝ) : Prop := (I.lo : ℝ) / 2 ^ Iv.prec ≤ x ∧ x ≤ (I.hi : ℝ) / 2 ^ Iv.prec

def Iv.add (a b : Iv) : Iv := ⟨a.lo + b.lo, a.hi + b.hi⟩
def Iv.neg (a : Iv) : Iv := ⟨-a.hi, -a.lo⟩
def Iv.sub (a b : Iv) : Iv := a.add b.neg
/-- floor and ceiling of `x / 2^prec`: `Int./` is `Int.ediv`, which is the floor for a positive divisor. -/
def Iv.fl (x : ℤ) : ℤ := x / Iv.sc
def Iv.ce (x : ℤ) : ℤ := -((-x) / Iv.sc)
def Iv.mul (a b : Iv) : Iv :=
  let p1 := a.lo * b.lo; let p2 := a.lo * b.hi; let p3 := a.hi * b.lo; let p4 := a.hi * b.hi
  ⟨Iv.fl (min (min p1 p2) (min p3 p4)), Iv.ce (max (max p1 p2) (max p3 p4))⟩
def Iv.pow (a : Iv) : ℕ → Iv
  | 0 => ⟨Iv.sc, Iv.sc⟩
  | n + 1 => (a.pow n).mul a
/-- Outward-rounded rational constant. -/
def Iv.ofRat (q : ℚ) : Iv := ⟨(q.num * Iv.sc) / q.den, -((-(q.num * Iv.sc)) / q.den)⟩
def Iv.ofInt (n : ℤ) : Iv := ⟨n * Iv.sc, n * Iv.sc⟩
/-- Hull, for box splitting. -/
def Iv.hull (a b : Iv) : Iv := ⟨min a.lo b.lo, max a.hi b.hi⟩
/-- Upper bound of `|x|` for `x ∈ I`, as a scaled integer. -/
def Iv.absHi (a : Iv) : ℤ := max (-a.lo) a.hi
```

Soundness lemmas (all short; the only real work is `mem_mul`):

```lean
theorem Iv.mem_add (ha : a.mem x) (hb : b.mem y) : (a.add b).mem (x + y)
theorem Iv.mem_neg (ha : a.mem x) : a.neg.mem (-x)
theorem Iv.mem_sub ...
theorem Iv.fl_le (x : ℤ) : (Iv.fl x : ℝ) ≤ (x : ℝ) / 2 ^ Iv.prec        -- Int.ediv_mul_le, cast
theorem Iv.le_ce (x : ℤ) : (x : ℝ) / 2 ^ Iv.prec ≤ (Iv.ce x : ℝ)
theorem Iv.mem_mul (ha : a.mem x) (hb : b.mem y) : (a.mul b).mem (x * y)
theorem Iv.mem_pow (ha : a.mem x) (n : ℕ) : (a.pow n).mem (x ^ n)
theorem Iv.mem_ofRat (q : ℚ) : (Iv.ofRat q).mem (q : ℝ)                  -- Rat.floor_intCast_div_natCast
theorem Iv.mem_ofInt (n : ℤ) : (Iv.ofInt n).mem (n : ℝ)
theorem Iv.mem_hull_left (ha : a.mem x) : (a.hull b).mem x   (and _right)
theorem Iv.abs_le_of_mem (ha : a.mem x) : |x| ≤ (a.absHi : ℝ) / 2 ^ Iv.prec
theorem Iv.pos_of_mem (ha : a.mem x) (h : 0 < a.lo) : 0 < x
theorem Iv.nonneg_of_mem (ha : a.mem x) (h : 0 ≤ a.lo) : 0 ≤ x
theorem Iv.le_of_mem (ha : a.mem x) (hb : b.mem y) (h : a.hi ≤ b.lo) : x ≤ y
```

`mem_mul` proof: `x*y` lies between the min and max of the four endpoint products
(`mul_le_mul` case split on the signs is the messy way; the clean way: `x = lo + θ(hi − lo)`
is bilinear, so `x*y` is a convex combination of the four corner products — use
`Set.mem_segment`-free reasoning: prove `min(...) ≤ x*y` by `nlinarith [mul_nonneg (sub_nonneg.2 ha.1) (sub_nonneg.2 hb.1), ...]` with the four products of `(x − lo)`, `(hi − x)`,
`(y − lo')`, `(hi' − y)` supplied; then apply `fl_le`/`le_ce`).  Write the scaled statement with
`(2:ℝ)^prec` cleared by `div_le_iff` first.

Pitfalls: never let `simp` unfold `Iv.sc` or `2 ^ 128` into a numeral inside proofs (cast it,
keep it symbolic as `(2:ℝ)^Iv.prec`); for the checkers, `decide +kernel` must reduce it, which it
does by itself.

## 2. `E` (`Thomson/Interval/Expr.lean`)

```lean
inductive E
  | const : ℚ → E
  | var : ℕ → E
  | add : E → E → E
  | mul : E → E → E
  | neg : E → E
  | pow : E → ℕ → E
deriving DecidableEq, Repr

namespace E
def eval (ρ : ℕ → ℝ) : E → ℝ
  | const q => q | var i => ρ i | add a b => a.eval ρ + b.eval ρ | mul a b => a.eval ρ * b.eval ρ
  | neg a => -a.eval ρ | pow a n => a.eval ρ ^ n

def ieval (env : ℕ → Iv) : E → Iv
  | const q => Iv.ofRat q | var i => env i | add a b => (a.ieval env).add (b.ieval env)
  | mul a b => (a.ieval env).mul (b.ieval env) | neg a => (a.ieval env).neg | pow a n => (a.ieval env).pow n

theorem ieval_mem (e : E) (h : ∀ i, (env i).mem (ρ i)) : (e.ieval env).mem (e.eval ρ)   -- induction

/-- Smart constructors used by the *mirrors* (so that `B`'s zero entries cost nothing). -/
def smul (q : ℚ) (e : E) : E := if q = 0 then const 0 else mul (const q) e
def mul' : E → E → E | const 0, _ => const 0 | _, const 0 => const 0 | a, b => mul a b
def add' : E → E → E | const 0, b => b | a, const 0 => a | a, b => add a b
theorem eval_mul' : (mul' a b).eval ρ = a.eval ρ * b.eval ρ     -- by cases; `simp [mul', eval]`
theorem eval_add' ...

/-- Finite sums, as `List.foldr` (E is not a monoid, so no `Finset.sum`). -/
def sum (n : ℕ) (f : Fin n → E) : E := (List.ofFn f).foldr add' (const 0)
theorem eval_sum : (sum n f).eval ρ = ∑ i, (f i).eval ρ            -- induction on n via List.ofFn_succ

/-- Substitution of expressions for variables. -/
def subst (σ : ℕ → E) : E → E
theorem eval_subst : (e.subst σ).eval ρ = e.eval (fun i => (σ i).eval ρ)

/-- The variables actually used are `< n`. -/
def below (n : ℕ) : E → Bool
theorem eval_congr (h : e.below n = true) (hρ : ∀ i < n, ρ i = ρ' i) : e.eval ρ = e.eval ρ'

/-- Symbolic partial derivative in variable `i`. -/
def deriv (i : ℕ) : E → E
  | const _ => const 0 | var j => if j = i then const 1 else const 0
  | add a b => add' (a.deriv i) (b.deriv i)
  | mul a b => add' (mul' (a.deriv i) b) (mul' a (b.deriv i))
  | neg a => neg (a.deriv i)
  | pow a 0 => const 0
  | pow a (n+1) => mul' (smul (n+1) (pow a n)) (a.deriv i)

theorem hasDerivAt_update (e : E) (ρ : ℕ → ℝ) (i : ℕ) :
    HasDerivAt (fun x => e.eval (Function.update ρ i x)) ((e.deriv i).eval ρ) (ρ i)
  -- induction; `pow` case via `HasDerivAt.pow`; `var` case by `Function.update_apply` split.

/-- Chain rule along a curve moving the first `n` variables. -/
theorem hasDerivAt_curve (e : E) (hn : e.below n = true) (γ : Fin n → ℝ → ℝ) (γ' : Fin n → ℝ)
    (t : ℝ) (hγ : ∀ i, HasDerivAt (γ i) (γ' i) t) (ρ₀ : ℕ → ℝ) :
    HasDerivAt (fun t => e.eval (fun i => if h : i < n then γ ⟨i, h⟩ t else ρ₀ i))
      (∑ i : Fin n, (e.deriv i).eval (fun j => if h : j < n then γ ⟨j, h⟩ t else ρ₀ j) * γ' i) t
  -- induction on e; `var` case: exactly one term of the sum survives (Finset.sum_ite_eq).
end E
```

Practical notes.

* `ieval` on a big term is what `decide +kernel` runs.  Keep `E` first-order (no closures); the
  kernel reduces `E.ieval env e` structurally, and `env` must be a closed term whose `Iv`s are
  literals (§4).  Do not use `Finset.sum`, `Rat` division, or `Real` anywhere inside `ieval`.
* For `E.eval` bridge proofs use `simp only [E.eval, E.eval_sum, E.eval_mul', E.eval_add', E.eval_subst]`
  followed by `ring_nf` only on *small* residues.
* Add `E.dual` (forward-mode: evaluate value and one directional derivative together, as a pair of
  `Iv`) only if 5b's box count makes symbolic `deriv` trees too large; the soundness is the same
  induction.  Not needed for 1a–5a.

## 3. The two Taylor lemmas (`Thomson/Interval/Taylor.lean`)

Both are about a real function `φ` on `[0,1]` given with its first and second (third) derivative
functions as `HasDerivAt` hypotheses on `[0,1]`.  Proof: apply `monotoneOn_of_deriv_nonneg` on
`Set.Icc 0 1` to the auxiliary function shown; continuity/differentiability from the `HasDerivAt`s.

```lean
/-- Second order: `φ(1) ≥ φ(0) + φ'(0) − K/2` if `|φ''| ≤ K` on `[0,1]`. -/
theorem taylor2_lower {φ φ' φ'' : ℝ → ℝ} {K : ℝ}
    (h1 : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt φ (φ' t) t)
    (h2 : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt φ' (φ'' t) t)
    (hK : ∀ t ∈ Set.Icc (0:ℝ) 1, |φ'' t| ≤ K) :
    φ 0 + φ' 0 - K / 2 ≤ φ 1
-- auxiliary g t := φ t − φ' 0 * t + K/2 * t^2;  g' = φ' − φ' 0 + K t ≥ 0 (from φ'(t) ≥ φ'(0) − K t,
-- itself `monotoneOn_of_deriv_nonneg` applied to φ' + K t).

/-- Third order with vanishing value and gradient: `φ(1) ≥ φ''(0)/2 − K/6` if `|φ'''| ≤ K`. -/
theorem taylor3_lower {φ φ' φ'' φ''' : ℝ → ℝ} {K : ℝ}
    (h1 ...) (h2 ...) (h3 : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt φ'' (φ''' t) t)
    (hK : ∀ t ∈ Set.Icc (0:ℝ) 1, |φ''' t| ≤ K) (h0 : φ 0 = 0) (h0' : φ' 0 = 0) :
    φ'' 0 / 2 - K / 6 ≤ φ 1
-- ψ t := φ t − φ'' 0 / 2 * t^2 + K/6 * t^3 has ψ'' ≥ 0, ψ'(0) = 0 ⇒ ψ' ≥ 0 ⇒ ψ(1) ≥ ψ(0) = 0.
```

These are used with `φ t = T(c + t·(x − c))` (the segment from a box centre `c` to a point `x`)
and with `φ t = T(τ + t·δ)`; the `HasDerivAt`s come from `E.hasDerivAt_curve` with
`γ i t = c i + t * (x i − c i)`, `γ' i = x i − c i`.

## 4. Atoms (`Thomson/Interval/Atoms.lean`)

```lean
/-- The real atoms.  Point variables 0,1,2 are placeholders (set per use). -/
noncomputable def atomVal (p : Fin 3 → ℝ) : ℕ → ℝ := fun i =>
  if h : i < 3 then p ⟨i, h⟩ else if i = 3 then uStar else if h : i < 28 then pivots ⟨i - 4, by omega⟩
  else if i = 28 then Real.sqrt 2 else if i = 29 then rStar else if i = 30 then s2Star else s4Star

/-- The interval environment: rational enclosures, as literals.  Generated. -/
def atomEnvC : ℕ → Iv   -- 3 ↦ uStar to 22 digits; 4+j ↦ pivotsNum j ± pivotEps; 28..31 ↦ 40/35-digit enclosures
def atomEnv (box : Fin 3 → Iv) : ℕ → Iv := fun i => if h : i < 3 then box ⟨i, h⟩ else atomEnvC i

theorem atomEnv_mem (box) (p) (hp : ∀ i, (box i).mem (p i)) : ∀ i, (atomEnv box i).mem (atomVal p i)
```

`atomEnv_mem` uses: `uStar_mem_Icc_sharp22` and `sqrt2_bounds_sharp40` (added in Step 0 / T1b),
`rStar/s2Star/s4Star_bounds_sharp` (already in `Sharp.lean`; re-derive at 35 digits from the
40-digit `√2` and 22-digit `u*` by the same two-line proofs), and `pivots_close` (1b).  Until 1b
is done, state `atomEnv_mem` with `pivots_close` as an explicit hypothesis so 1a can already use
the pivot-free atoms.

Write the rational endpoints of `atomEnvC` as `Iv.ofRat (lo)`, `Iv.ofRat (hi)` hulls — i.e.
`⟨(Iv.ofRat lo).lo, (Iv.ofRat hi).hi⟩` — so `mem` follows from `mem_ofRat` and the enclosure
theorems; the kernel then reduces the `ofRat`s once.

## 5. Mirrors (`Thomson/ThreePoint/Mirror.lean`) — the bridge to the real definitions

Everything below is a Lean *definition* built from the same tables as `CertData.lean`, plus one
bridge lemma each.  Extend `task1_emit_lean.py` to emit `BpolyE : ℕ → ℕ → ℕ → E` (the same
match table as `Bpoly`, with `uStar ↦ E.var 3`, rationals as `E.const`) and
`HfixQ : ℕ → ℕ → ℕ → ℚ`, `a0Q a1Q lamQ : ℚ`, `pivotsNumQ : Fin 24 → ℚ`; and **redefine** in
`CertData.lean` `Bpoly k i a := (BpolyE k i a).eval (fun i => if i = 3 then uStar else 0)`,
`HfixTable k a b := (HfixQ k a b : ℝ)`, `a0Fix := (a0Q : ℝ)` etc., `pivotsNum j := (pivotsNumQ j : ℝ)`.
Then the bridges are definitional or `E.eval_congr` (BpolyE uses only var 3: prove
`∀ k i a, (BpolyE k i a).below 4 = true` by `decide` over the finitely many nonzero cases, or make
`BpolyE` take the variable index as an argument).  Re-run `lake build`; `Task1a.lean`,
`Linear.lean`, `Sharp.lean` do not unfold these tables, `Toolkit.lean` does not either.

```lean
def Q3E (k : ℕ) (u v t : E) : E := match k with   -- literally Q3 with E operations
def Y3E (k : ℕ) (u v t : E) (i j : ℕ) : E := mul' (mul' (pow u i) (pow v j)) (Q3E k u v t)
def S3E (k : ℕ) (u v t : E) (i j : ℕ) : E :=
  smul (1/6) (add' (Y3E k u v t i j) (add' (Y3E k u t v i j) (add' (Y3E k v u t i j)
    (add' (Y3E k v t u i j) (add' (Y3E k t u v i j) (Y3E k t v u i j))))))
/-- `(B_kᵀ S3_k B_k)[a,b]` as an expression. -/
def BSBE (k : ℕ) (u v t : E) (a b : ℕ) : E :=
  E.sum (9 - k) fun l => mul' (E.sum (9 - k) fun i => mul' (BpolyE k i a) (S3E k u v t i l)) (BpolyE k l b)
def HpE (k a b : ℕ) : E :=                                   -- Hfix + Σ_j eH j k a b · p_j ; HfixQsym = symmetrised HfixQ
  add' (const (HfixQsym k a b)) (E.sum 24 fun j => if slot j = (k,a,b) ∨ slot j = (k,b,a) then var (4 + j) else const 0)
def FhE (u v t : E) : E :=
  E.sum 6 fun k => E.sum (9 - k) fun a => E.sum (9 - k) fun b => mul' (HpE k a b) (BSBE k u v t a b)
def GhE (j : Fin 24) (u v t : E) : E :=                     -- linear part in pivot j (Perturb.Gh)
  let (k, a, b) := slot j; if a = b then BSBE k u v t a a else add' (BSBE k u v t a b) (BSBE k u v t b a)
def tOfS (s : E) : E := add' (const 1) (neg (smul (1/2) (pow s 2)))
def pairPE : E := add' (const (1 - 18 * lamQ))
  (neg (mul' (var 0) (add' (const a0Q) (add' (smul a1Q (tOfS (var 0))) (smul 3 (FhE (const 1) (tOfS (var 0)) (tOfS (var 0))))))))
def triPE : E := ... lamQ * (bc + ac + ab) − abc · FhE (tOfS a) (tOfS b) (tOfS c) with a,b,c = var 0,1,2
def chordE : Fin 4 → E := ![mul (var 28) (var 29), smul 2 (var 29), var 30, var 31]
def touchTypeE : Fin 5 → E × E × E := ...   -- same table as touchType
```

Bridge lemmas (each a `simp only [..., E.eval_sum, E.eval_mul', E.eval_add', E.eval, Matrix.mul_apply,
Matrix.transpose_apply, Fh, Hp, S3, Y3, Q3, B, Bpoly, Matrix.of_apply, Finset.mul_sum]` plus
`Finset.sum_congr`; no `ring` on anything larger than one `Q3`):

```lean
theorem Q3E_eval : (Q3E k u v t).eval ρ = Q3 k (u.eval ρ) (v.eval ρ) (t.eval ρ)      -- cases k ≤ 5, else both 0
theorem S3E_eval (hij : i < 9 - k) ... : (S3E k u v t i j).eval ρ = S3 k (..) (..) (..) ⟨i,_⟩ ⟨j,_⟩
theorem BpolyE_eval (hρ : ρ 3 = uStar) : (BpolyE k i a).eval ρ = Bpoly k i a
theorem BSBE_eval (hρ : ρ 3 = uStar) : (BSBE k u v t a b).eval ρ = ((B k)ᵀ * S3 k (..) (..) (..) * B k) ⟨a,_⟩ ⟨b,_⟩
theorem HpE_eval (hρ : ∀ j, ρ (4 + j) = p j) : (HpE k a b).eval ρ = Hp p k ⟨a,_⟩ ⟨b,_⟩
theorem FhE_eval (hρ3) (hρp) : (FhE u v t).eval ρ = Fh (Hp p) (u.eval ρ) (v.eval ρ) (t.eval ρ)
theorem GhE_eval : (GhE j u v t).eval ρ = Gh j (u.eval ρ) (v.eval ρ) (t.eval ρ)           -- Perturb.Gh
theorem pairPE_eval (p) (s) : pairPE.eval (atomVal ![s, 0, 0]) = pairP pivots s
theorem triPE_eval (a b c) : triPE.eval (atomVal ![a, b, c]) = triP pivots a b c
theorem chordE_eval : (chordE X).eval (atomVal p) = chord X ;  touchTypeE_eval likewise
```

`Gh` in `Perturb.lean` is `Σ_k Σ_a Σ_b eH j k a b * (BᵀS3B)_ab`; `GhE` picks the one or two
surviving terms directly — prove `GhE_eval` via `Finset.sum_eq_single` twice (the `eH`
indicator is nonzero exactly at `(k,a,b)` and `(k,b,a)`).

**Acceptance for T0.**  A file `Thomson/Interval/Test.lean` with
`example : 0 < (pairPE.ieval (atomEnv ![Iv.ofRat (3/2), Iv.ofInt 0, Iv.ofInt 0])).lo := by decide +kernel`
(the pair polynomial at `s = 1.5`, value `≈ 10⁻⁴`, well away from the roots) compiles in under a
minute, and `#print axioms` of the bridge lemmas is standard.  If `decide +kernel` hits
`maxRecDepth`, raise it (`set_option maxRecDepth 100000`) and check that `E.sum` is built by
`List.foldr` (right-nested, shallow) rather than a left fold.
