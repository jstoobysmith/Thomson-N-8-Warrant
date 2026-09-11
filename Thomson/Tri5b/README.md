# `Thomson/Tri5b` — Task 5b

Independent development for **Task 5b** of `Thomson/ThreePoint/Tasks.lean` (global positivity of
the triangle polynomial away from the five touching types).  It touches no existing file.

## Two findings that change the task

### 1. Task 5 as stated is false; the chord bound must be `9619/10000`, not `24/25`

At `(a, b, c) = (1.682, 24/25, 24/25)`:

| | |
|---|---|
| chords in `[24/25, 2]` | yes |
| `gram` | `+5.6·10⁻³ > 0` |
| distance to the nearest touching type | `≥ 0.21` (so Task 5b's hypothesis holds too) |
| `triP pivots` | **`−3.7·10⁻⁶ < 0`** (`−1.68·10⁻⁵` at `a = 1.684`) |

So `triP_nonneg`, `triP_global` and the `tri` field of `exists_threePointCert` are refuted as they
stand.  The cause is arithmetic, not structural: `separation_of_energy_le` gives `t ≤ 0.5373`, i.e.
chords `≥ √(2 − 2·0.5373) = 0.9619771…`, and `tri_of_poly` rounds that down to `24/25 = 0.96`.
The certificate is tight and has no slack on the sliver `0.96 ≤ b, c < 0.96099…`.  On the true range
the minimum of `triP` is `+1.475·10⁻⁵`, at `(1.6865, 0.96198, 0.96198)`.

`Domain.lean` proves `tri_of_poly'`, which is `tri_of_poly` with `9619/10000` in place of `24/25`
— the same proof, since `(9619/10000)² = 0.92525161 ≤ 0.9254`.  `Tasks.lean` needs the constant
changed in `triP_nonneg`, `triP_global` and the `tri` field; `pairP_nonneg` is unaffected
(`pairP pivots (24/25) = +2.5·10⁻⁴`).

### 2. `pivotEps = 10⁻⁶` is too weak for Task 5b

Just outside a `rhoLocal`-cube the value of `triP` is only `≈ ½·λ_min·(1/500)² ≈ 1.2·10⁻⁹`
(`λ_min ≈ 6.2·10⁻⁴` is the smallest Hessian eigenvalue at a touching type, in chord variables),
while `pivots_close` permits `triP pivots` to differ from `triP pivotsNum` by
`10⁻⁶ · Σⱼ|Gⱼ| ≈ 1.1·10⁻⁵`.  Some vectors satisfying Task 1b's conclusion really do make `triP`
negative there, so **no** proof of Task 5b can use Task 1b as currently stated.

Task 1b's own sketch says the residual at `pivotsNum` is `≈ 2·10⁻²¹` and that only the enclosures
limit the estimate, so this is a matter of digits: `UStar.lean` proves `u*` to `3·10⁻³²`
(the existing `uStar_mem_Icc_sharp` gives `10⁻¹³`), which is what a `10⁻¹⁵`-grade Task 1b needs.
`Reduce.lean` carries `ε` as a parameter throughout, so the development is unaffected by the exact
value once it is small enough.

Task 5a is *not* affected: there the constant and linear terms vanish exactly (`triP_tight`), so
`ε` only perturbs the Hessian, by `ε·Σⱼ‖D²Gⱼ‖ ≈ 10⁻⁶·(95 … 3111)`, which stays below `λ_min` at all
five types (worst ratio `0.83`, at `FFA`).

## The proof architecture

```
Domain.lean       the corrected chord range     tri_of_poly'
Symmetry.lean     sort the triple               Task 5 ⇐ Task 5a + the sorted statement
Main.lean         chords ↔ inner products       Task 5 ⇐ NumCertU + Task 5a
Reduce.lean       the ℓ¹ alternative            (not used: the uncertainty is folded into the data)
MForm.lean        F in evaluable form           Fh = (1/3) Σ_k w_k(u,v) Q_k(u,v,t) + …
UStar.lean        u* to 32 digits
Interval.lean     fixed-point intervals         scale 10⁻⁴⁰, exact for all the certificate's data
TM.lean           quadratic Taylor models       value + gradient + Hessian + radius, and `loBound`
Tensor.lean       coefficient tensors           the Taylor shift `ev (shift c a b d) = ev c (a+·) …`
Engine.lean       interval tensors              shift, `toTM`, `box_sound`, `inv_sqrt_tangent`
Shift1.lean       multiplication by a monomial  index shifts with degree bookkeeping
QTensor.lean      the tensors of `Q_k`          65 coefficients, checked against `Q3`
Bridge.lean       the tensor of `F`             from `M_k = B_k H_k B_kᵀ` and the `Q`-tensors
CertIntervals.lean  the certificate's data      `B`, `Hfix`, `pivotsNum`, and the pivot widening
CFTable.lean      that tensor, tabulated        729 entries, `native_decide`d against the definition
Leaf.lean         one box                       `leaf_sound`
Cover.lean        boxes, splitting, leaves      `leafAuto_sound`
CubeData.lean     the five local cubes          chord enclosures and `cubeSound`
Skip.lean         pruning + the bit checker     `bcheck_sound`, `Covers`, `task5_of_data`
Params.lean       the root box and the margin
Part000–106.lean  the covering, in 107 pieces    one `native_decide` each, ≤ 891 boxes
Certificate.lean  the pieces, recombined         `cert_cover`, by `covers_split`
Final.lean        the theorem                   `tri_nonneg`, `triP_global`
```

The sorting reduction is what makes a box covering possible at all: `triP` is symmetric but the
five touching types are listed as *ordered* triples, so on the full cube the permuted images of the
touching points are zeros of `triP` that Task 5b's hypothesis does not exclude — no covering with a
positive margin can exist there.  All five types are already listed in decreasing order, so on the
sorted cone they are the only zeros.

The pivot uncertainty is not carried as an `ℓ¹` loss but folded into the data: an entry of `Hp p`
differs from the same entry of `Hp pivotsNum` by at most `ε` times the number of pivot slots at
that position (`0` or `1`), so widening those 24 entries by `ε` makes the whole tensor enclose `F`
for the *true* certificate.  At `ε = 10⁻¹²` the widening costs `< 10⁻¹⁰` on every box of the
covering, which is why the margin certified everywhere is `10⁻¹⁰`.

## The statement

```lean
theorem Thomson.Tri5b.tri_nonneg
    (hloc : TriLocal (fun _ => 1 / 500))                        -- Task 5a
    (hclose : ∀ j, |pivots j - pivotsNum j| ≤ 1 / 10 ^ 12) :    -- Task 1b, at 10⁻¹²
    ∀ a b c : ℝ, chordLo ≤ a → chordLo ≤ b → chordLo ≤ c → a ≤ 2 → b ≤ 2 → c ≤ 2 →
      0 ≤ gram a b c → 0 ≤ triP pivots a b c
```

and `triP_global` is the same in the shape of `Thomson.triP_global`.  The covering is checked by
`native_decide`, so `Lean.ofReduceBool` appears in the axioms of the pieces and of everything above
it; the same statement is `decide +kernel`-checkable box by box (see below).

## What remains

**Only Task 5a** (`TriLocal`, the local cubes of radius `1/500`).  Task 1b at `10⁻¹²` is proved in
the `Task1b` library (`Thomson/Task1b/`, to `2·10⁻²¹`), and `Task5b.lean` combines the two:

```lean
theorem Thomson.Tri5b.task5b_of_task5a (hloc : TriLocal (fun _ => 1 / 500)) : Thomson.Task5b
```

The covering, the certificate's data, the enclosures of `u*` and of the four touching chords are
all here and proved.  Both libraries are outside `defaultTargets`: `lake build Tri5b`,
`lake build Task1b`.

## Performance notes

`native_decide` evaluates in Lean's *interpreter*: every call to one of our own functions costs a
few microseconds of interpreter overhead, whatever it computes.  The covering is `2·10⁴` interval
operations per box and `3·10⁴` boxes, so the whole check is `≈10⁹` interpreted operations — an
hour on one core.  Five things brought it there from "does not finish"; each was found by timing
the pieces from `#eval`, and each is easy to reintroduce by accident.

* **Numerals, not `10 ^ n`.**  To the compiler `10 ^ 40` is a call to `Monoid.npow`, re-evaluated
  at every use — and `SCALE` is used twice in every interval multiplication.  `SCALE`, `SCALE2`,
  `SCALE3`, `EPS`, `MG`, `LAM`, `UHI` and `sigmas` are therefore written out, and `n ^ 3` inside
  `tanIT` is `n * n * n`.
* **No `![…]` at run time.**  A `![x₀, …, x₂₃]` vector is a `Matrix.vecCons` chain, and *one* read
  of it costs the interpreter `≈0.1 s` — more than a whole box.  `pivQ`, `slot`, `cubeD` and
  `Bx.lo/hi` are matches on `ℕ`; `pivQn`, `slotN`, `cubeLoN`, `cubeHiN` carry the data, and
  `slotN_eq` ties `slotN` back to `Thomson.slot`.  This one change took a single entry of
  `MIedata` from four minutes to 19 ms.
* **Tabulate into a value, not behind a function.**  `Ishift C a b d` is a function, so each of the
  `9³` reads of it recomputes the whole shift: `9³` base reads per entry.  The obvious fix,
  `fun C => let tbl := …; fun i j k => tbl …`, does *not* work — the compiler eta-expands it back
  to arity 4 and rebuilds `tbl` on every read (`trace.compiler.ir.result` shows it).  The table has
  to be a value of a data type: `ITA` wraps an `Array`, and `ITA.get A` — a partial application —
  evaluates `A` once.  `toITA`, `Ish1A`, `IshiftA`.
* **Hoist and skip.**  `Ish1A` computes the nine powers of the shift once (`powA`) instead of at
  every entry, and skips products with a zero factor (`Itv.mul_zero_left`); `negGramA`, the tensor
  of the Gram pruning test, is a closed term, so the interpreter builds it once for the whole run.
* **Cut the covering into pieces.**  A covering is a union, so a box may be covered piece by piece
  (`covers_split`).  The tree is cut greedily at `≤ 891` boxes per piece into 107 modules with one
  `native_decide` each, which `lake` builds in parallel: about an hour of CPU, but ten minutes of
  wall clock on eleven cores.

## Reproducing and re-checking

`threepoint/tri5b_*.py` regenerate everything: `tri5b_mirror.py` is a bit-for-bit Python copy of
the Lean fixed-point interval arithmetic, `tri5b_build.py` rebuilds the tensor of `F` from
`CertData.lean` (and checks it against a floating-point evaluation of `Fh`), `tri5b_cubes.py` the
cube images, `tri5b_tree2.py` the covering and `tri5b_parts.py` the Lean modules.  `tri5b_eval.py`
is the independent floating-point evaluator used for the counterexample and for the landscape
numbers quoted here.

**Accept a leaf on the exact model, never on the float one.**  `tri5b_tree.py` (superseded)
searched with a float model and a safety factor of two, and re-checked a sample of leaves exactly.
That is not enough: the float model uses the midpoints of the certificate's intervals and so misses
the `10⁻¹²` pivot widening entirely, and the *first* leaf of the tree it produced fails the integer
test that Lean performs.  In `tri5b_tree2.py` the float model only proposes the S-procedure
multiplier; `leaf_exact` — the mirror of `leafCheck` — decides.  It costs 23 ms per leaf, the tree
takes six minutes on eleven cores, and the multiplier `σ = 0` wins on every leaf sampled.

**The centred form is the wrong bound; shift the tensor instead.**  A box of half-width `h` at
distance `d` from a touching type is certified only if the remainder beats `½ λ_min d²`.  Three
ways to bound that remainder were measured on this certificate, on boxes near `FFA`:

| form | remainder on a `4·10⁻³` box | boxes needed |
|---|---|---|
| `F`-expression replayed in Taylor-model arithmetic | `2.9·10⁻⁶` | `~10⁷` |
| Horner on the tensor in Taylor-model arithmetic | `1.0·10⁻⁵` | `~10⁷` |
| **Taylor shift of the coefficient tensor** (`Tensor.lean`) | **`2.0·10⁻⁹`** | **`~10⁴`** |

The first two lose a factor `10³`–`5·10³` because every product is bounded by a sum of absolute
values, while the true third-order tail cancels massively.  Shifting the tensor produces the exact
Taylor coefficients, so the tail is the true one — `Σ_{|α|≥3} |c_α| h^α`, computed inside `toTM`.

With that bound a *plain axis-aligned* covering closes; eigen-aligned boxes are not needed.
Measured counts (adaptive bisection, S-procedure multiplier on the boxes that meet `gram = 0`,
`ρ = 1/500`, the corrected chord range):

* **8 559 boxes** with the second-order minorant of `λ/√(2−2u)` (tangent *parabola*: rational data,
  valid whenever `(a₋+2a₀) ≥ 2γ A₊ a₀³ (A₊+a₀)²`);
* **23 866 boxes** with the tangent *line* only — the form `Leaf.lean` implements today.

At `≈ 2·10⁴` interval operations per box (three passes of a binomial transform on a `9×9×9`
tensor) that is `2·10⁸`–`5·10⁸` operations: comfortably `native_decide`, and — at the `10³`
interval multiplications per second measured for `decide +kernel` in `plans/README.md` §1.1 —
`2`–`6` CPU-days in the kernel, parallelisable over chunk files.  **So Task 5b need not add
`Lean.ofReduceBool`**; that is the main practical consequence of the tensor form, and it changes
the decision table of `plans/T5b-TriGlobal.md` §4 (which assumed `10⁵`–`10⁶` boxes from the
centred form).

Structural evaluation without a tensor was measured and rejected for the same reason.
