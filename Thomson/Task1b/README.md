# `Thomson/Task1b` — Tasks 1b and 1a

**Proved.** `lake build Task1b` checks it (about five minutes; not part of the default build).

```lean
theorem Thomson.Task1b.pivotMatrix_det_isUnit : IsUnit pivotMatrix.det              -- Task 1a
theorem Thomson.Task1b.pivots_close_sharp : ∀ j, |pivots j - pivotsNum j| ≤ 2 / 10 ^ 21  -- Task 1b
```

Axioms: `propext`, `Classical.choice`, `Quot.sound`, and one `native_decide` (`Check.check_ok`,
about 90 s).  `Tasks.lean` asks for `pivotEps = 10⁻¹²` (what Tasks 4 and 5b need); the proof gives
`2·10⁻²¹`.  The main library states both as propositions `Thomson.Task1a`, `Thomson.Task1b`
(`Thomson/ThreePoint/Tasks.lean`) and takes them as hypotheses; `Thomson.Task1b.task1a`, `task1b`
(`Thomson/Task1b/Tasks.lean`) discharge them, in `Thomson/Complete.lean` and in
`Thomson.Tri5b.task5b_of_task5a`, so that Task 5b rests on Task 5a alone.

## The argument

With `M = pivotMatrix`, `N` the 17-digit approximate inverse and `r = rowFun · pivotsNum`, two
numbers are computed on verified enclosures: `η = ‖I − N M‖∞ ≤ 10⁻¹¹` (it is `5.25·10⁻¹²`) and
`ρ = ‖N r‖∞ ≤ 10⁻²¹` (it is `4.0·10⁻²²`).  Then `M y = 0 ⇒ y = (I − N M) y ⇒ y = 0` (Task 1a), and
`x = pivots − pivotsNum` satisfies `x = (I − N M) x − N r`, so `‖x‖∞ ≤ ρ/(1 − η)` (Task 1b).

## Where the enclosures come from

Every entry of `M` is a value or derivative of `Gh j` (`Thomson.ThreePoint.Perturb`), and `Gh j` is
`Fh` of the indicator block of pivot `j` — so Task 5b's coefficient-tensor bridge
(`Thomson.Tri5b.Bridge`) applies once it is stated for any symmetric block (`GTensor.lean`).  The
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
Tab.lean       B, the blocks M_k and the 25 tensors tabulated; N (with its first column halved)
System.lean    the dispatch by rowSpec; the matrix and the residual, tabulated
Check.lean     η and ρ, by native_decide, and what they mean (estimates)
Final.lean     the contraction argument: Task 1a and Task 1b
Tasks.lean     the main library's Task1a/Task1b propositions, discharged
```

## A correction to `approx_inverse`

`threepoint/task1_leanform.py` builds the bound row as *half* of `28a₀ − 4a₁ − 4F − E`; its comment
says that is `evalRow .bound`, but `(64a₀ − 8(a₀+a₁) − 8F)/2 − E = 28a₀ − 4a₁ − 4F − E`.  So the
stored `approx_inverse` inverts `pivotMatrix` with its bound row halved: `N·pivotMatrix` is
`diag(2, 1, …, 1)`, and `‖I − N·pivotMatrix‖∞ = 2186`.  Halving the first column of `N` restores
`5.25·10⁻¹²`.  The pivots themselves are unaffected (a row scaling does not change a solution); only
anyone using `approx_inverse` against `pivotMatrix` — Task 1a's sketch does — needs the fix.  This
was found by comparing the verified enclosures with the Python matrix: every other row agrees to
all digits shown, the bound row by a factor of exactly `2`.

## Performance

Same lessons as Task 5b (`Thomson/Tri5b/README.md`): tables are values (`Tab3`, `ITA`, `Array`),
never functions; no `![…]` at run time.  The 24 tensors of `Gh j` and the tensor of `F` are each
built once (`GA`, `FA`), the columns of `M` from them (`MA`); the whole check is about 90 s in the
interpreter.
