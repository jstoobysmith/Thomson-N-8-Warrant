# `Thomson/Task1b` — Tasks 1b and 1a

**Proved.** `lake build Task1b` checks it (not part of the default build; see *Performance*).

```lean
theorem Thomson.Task1b.pivotMatrix_det_isUnit : IsUnit pivotMatrix.det              -- Task 1a
theorem Thomson.Task1b.pivots_close_sharp : ∀ j, |pivots j - pivotsNum j| ≤ 2 / 10 ^ 21  -- Task 1b
```

Axioms: `propext`, `Classical.choice`, `Quot.sound` — nothing else.  Every numerical step is
`decide +kernel`; there is no `native_decide` anywhere in the directory.  `Tasks.lean` asks for
`pivotEps = 10⁻¹²` (what Tasks 4 and 5b need); the proof gives
`2·10⁻²¹`.  The main library states both as propositions `Thomson.Task1a`, `Thomson.Task1b`
(`Thomson/ThreePoint/Tasks.lean`) and takes them as hypotheses; `Thomson.Task1b.task1a`, `task1b`
(`Thomson/Pivots/Tasks.lean`) discharge them, in `Thomson/Complete.lean` and in
`Thomson.Tri5b.task5b_of_task5a`, so that Task 5b rests on Task 5a alone.

## The argument

With `M = pivotMatrix`, `N` the 17-digit approximate inverse and `r = rowFun · pivotsNum`, two
numbers are computed on verified enclosures: `η = ‖I − N M‖∞ ≤ 10⁻¹¹` (it is `5.25·10⁻¹²`) and
`ρ = ‖N r‖∞ ≤ 10⁻²¹` (it is `4.0·10⁻²²`).  Then `M y = 0 ⇒ y = (I − N M) y ⇒ y = 0` (Task 1a), and
`x = pivots − pivotsNum` satisfies `x = (I − N M) x − N r`, so `‖x‖∞ ≤ ρ/(1 − η)` (Task 1b).

## Where the enclosures come from

Every entry of `M` is a value or derivative of `Gh j` (`Thomson.Certificate.Perturb`), and `Gh j` is
`Fh` of the indicator block of pivot `j` — so Task 5b's coefficient-tensor bridge
(`Thomson.TriangleGlobal.Bridge`) applies once it is stated for any symmetric block (`GTensor.lean`).  The
residual needs `F` at `pivotsNum`, which is exactly the tensor Task 5b built.  So the whole of the
certificate's data — `B` from `u*` to 32 digits, the four chords to 32 digits — is reused.

```
Eval.lean      a tensor evaluated at enclosed points, and its partial derivatives
GTensor.lean   Gh j = Fh (eH j); the bridge for any symmetric block; the interval tensor of Gh j
Diag.lean      the derivative along v = t (the pair rows move both)
Rows.lean      the derivative rows: product and chain rule, per row type
Points.lean    the chords and the touching types, and x ↦ 1 − x²/2
Entries.lean   an enclosure of every entry of pivotMatrix, per row type
Residual.lean  the rows at pivotsNum: constants, λ, the antiprism energy, 1/x on intervals
Tab.lean       N, the approximate inverse (with its first column halved), as a list of rows
System.lean    the dispatch by rowSpec: entAt, resAt
KBase.lean     nested-list tables, and the two lemmas turning a checked table into an enclosure
gen/           the generator of the tables below (not part of the library; see gen/tables.lean)
KT00…KT23      GENERATED: for each pivot j, the blocks M_k, the tensor of Gh j and column j
KTF.lean       GENERATED: the blocks, the tensor of F at pivotsNum and the residual
KSystem.lean   the checked tables assembled into Mtab and Rtab
Check.lean     η and ρ, by decide +kernel, and what they mean (estimates)
Final.lean     the contraction argument: Task 1a and Task 1b
Discharge.lean the main library's Task1a/Task1b propositions, discharged
```

## A correction to `approx_inverse`

`scripts/threepoint/task1_leanform.py` builds the bound row as *half* of `28a₀ − 4a₁ − 4F − E`; its comment
says that is `evalRow .bound`, but `(64a₀ − 8(a₀+a₁) − 8F)/2 − E = 28a₀ − 4a₁ − 4F − E`.  So the
stored `approx_inverse` inverts `pivotMatrix` with its bound row halved: `N·pivotMatrix` is
`diag(2, 1, …, 1)`, and `‖I − N·pivotMatrix‖∞ = 2186`.  Halving the first column of `N` restores
`5.25·10⁻¹²`.  The pivots themselves are unaffected (a row scaling does not change a solution); only
anyone using `approx_inverse` against `pivotMatrix` — Task 1a's sketch does — needs the fix.  This
was found by comparing the verified enclosures with the Python matrix: every other row agrees to
all digits shown, the bound row by a factor of exactly `2`.

## Performance

The check used to be one `native_decide` of about 90 s, on `Array`-based tables (`toITA`, `Tab3`).
The kernel cannot reduce `Array.ofFn` — it is well-founded recursion — so for `decide +kernel`
every table is a nested `List` instead, read with `List.getD`, and every table is *checked* against
its definition rather than computed inside the check.

The kernel caches every closed subterm it reduces within one declaration and only drops the cache
between declarations, so the binding constraint is memory, not time.  Measured here (Lean 4.33,
one core): about `1600` interval products per second, and about `230 kB` of cache per product —
a single `entAt (GIT j) i` with the tensor left as a definition reached `14 GB`, and the whole
block table `MI BI (eHI j)` in one theorem (`3·10⁴` products) took `6.9 GB` for `19 s` of CPU.

So each generated module cuts its work into pieces of at most a few thousand products:

| check | per theorem | theorems per module | peak |
|---|---|---|---|
| blocks `M_k` (`MItab⟨j⟩_eq_k_i`) | one row, `≤162` products | 39 | `< 0.1 GB` |
| tensor (`Gtab⟨j⟩_eq_p_q`) | one `(p,q)` row, `2439` products | 81 | `≈0.6 GB` |
| column (`col⟨j⟩_eq⟨i⟩`) | one entry, `≤4400` products | 24 | `≈1 GB` |
| `η` and `ρ` (`check_ok`) | `1.4·10⁴` products | 1 | `≈3 GB` |

The 25 modules are independent, so `lake` runs them in parallel; the total is about `8·10⁶`
interval products, i.e. of the order of `1.5` CPU-hours, ten minutes of wall clock on 14 idle
cores.  (The figures above were taken on a machine that was simultaneously running Task 5b's
covering, so the wall-clock times measured there are not meaningful; the CPU times are.)
