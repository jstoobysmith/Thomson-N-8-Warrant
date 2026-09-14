# Closing the eight `sorry`s — the plan

*Written 2026-09-10.  Everything below was checked against the code as it stands
(`Thomson/ThreePoint/Tasks.lean`, `Linear.lean`, `Perturb.lean`, `Sharp.lean`, `Enclosure.lean`,
`Tri5b/`) and against the numbers at `pivotsNum` (scripts in `docs/history/` are described where used).
Read this file first, then the task file you are assigned.  Each task file is self-contained:
statement, prerequisites, the exact Lean declarations to write, the proofs, the data to generate,
and the acceptance test.*

> **Status, 2026-09-11.**  Everything below is a *plan*; the live status is the table at the top of
> `Thomson/ThreePoint/Tasks.lean`.  Done: 1a, 1b (library `Task1b`, `native_decide`), 1c(i) and
> 1c(ii) (`Thomson/ThreePoint/{Slack,Kernel/*,Redundant}.lean`), 2 (`Thomson/PSD/`), 4
> (`Thomson/Pair/`), 5b (library `Tri5b`, `native_decide`), and the statement fixes of §2.1–2.2
> (chord bound `9619/10000`, `pivotEps = 10⁻¹²`).  §2.3 (per-type radii) was not needed: Task 5b uses
> the uniform `rhoLocal = 1/500`.  Open: 5a.  The tasks proved by `native_decide` enter the default
> build as hypotheses (`Task1a`, `Task1b`, `Task5b`); `Thomson/Complete.lean` discharges them.

## 0. What is open, and in which order to do it

| leaf in `Tasks.lean` | plan file | needs | kind |
|---|---|---|---|
| — (statement fixes) | §2 below | nothing | edits, 1 hour |
| — (infrastructure) | [T0-Infrastructure.md](T0-Infrastructure.md) | nothing | Lean library, the biggest single piece |
| `pivotMatrix_det_isUnit` (1a) | [T1a-PivotDet.md](T1a-PivotDet.md) | T0 | computation in the kernel |
| `pivots_close` (1b) | [T1b-PivotEnclosure.md](T1b-PivotEnclosure.md) | T0, 1a | computation in the kernel |
| `row_pairVal_A`, `row_triD_FDN_v` (1c) | [T1c-RedundantRows.md](T1c-RedundantRows.md) | nothing (T0's `E.deriv` is convenient for 1c(ii)) | algebra + generated `ring` identities |
| `certH_posSemidef` (2) | [T2-PSD.md](T2-PSD.md) | 1b | rational linear algebra |
| `pairP_nonneg` (4) | [T4-Pair.md](T4-Pair.md) | T0, 1b, 1c(i) | 1-D Taylor + interval covering |
| `triP_local` (5a) | [T5a-TriLocal.md](T5a-TriLocal.md) | T0, 1b, 1c(ii) | 3-D Taylor at the five types |
| `triP_global` (5b) | [T5b-TriGlobal.md](T5b-TriGlobal.md) | T0, 1b, 5a's radii | box covering, `native_decide` |

Critical path: **fixes → T0 → 1a → 1b → {2, 4, 5a, 5b}**, with 1c in parallel from day one.
T0 is where the effort is; every numeric task is a thin layer on it.

## 1. The two architectural decisions

### 1.1 Everything numeric goes through one verified interval kernel

The sketches in `Tasks.lean` say "interval arithmetic" and "one mechanical lemma per box" without
saying how.  There is no interval arithmetic in Mathlib, and `norm_num`/`nlinarith` cannot bound a
degree-50 polynomial in five irrational atoms 576 times (1a), let alone 10⁵ times (5b).  So T0
builds the tool once:

* `Iv` — closed intervals with `ℤ` endpoints at a fixed binary scale `2^128`; `add/neg/mul/pow`
  with outward rounding; soundness lemmas w.r.t. `ℝ`.
* `E` — a tiny expression language (`const ℚ | var ℕ | add | mul | neg | pow`) with `eval : E → (ℕ → ℝ) → ℝ`,
  interval evaluation `ieval` (sound), symbolic partial derivatives `deriv i` (sound: a `HasDerivAt`
  lemma), substitution, and a chain rule along curves.  Every polynomial in the development
  (`Fh (Hp p)`, `pairP`, `triP`, the rows of `pivotMatrix`) is *mirrored* as an `E`-term built by
  a Lean function from the same tables, and one generic lemma says its `eval` is the real thing.
  No `ring` on large terms anywhere.
* Two calculus lemmas (`Taylor.lean`): a second-order and a third-order lower bound along a segment,
  from `monotoneOn_of_deriv_nonneg` — no `taylorWithinEval`.
* Each numeric fact is then `theorem foo : 0 ≤ T x := checker_sound data (by decide +kernel)`
  where `checker : Data → Bool` is a computable function with a soundness theorem.

Measured on this machine (Lean v4.33, Mathlib pinned in `lakefile.toml`): `decide +kernel` does
about **1000 interval multiplications of 128–200-bit integers per second**; `native_decide` does the
same in milliseconds.  Consequences: 1a, 1b, 2, 4, 5a (each `≤ 10⁶` operations) run in the kernel;
5b (box covering, `≥ 10⁸` operations) uses `native_decide` and therefore adds the axiom
`Lean.ofReduceBool` to `thomson_eight_lower`.  The statements are identical, so any single box can
be re-checked with `decide +kernel` (about 10 s per box); doing all of them is a few CPU-days,
parallelisable by file.  Say this honestly in the blueprint when 5b lands.

### 1.2 The five open tasks must never see the certificate's zeros "from the outside"

At the four chords and five triangle types the polynomials vanish to second order, and the true
pivots are only known as `pivotsNum ± pivotEps`.  Every inequality is therefore proved in one of
two regimes, and only these two:

* **Local** (a fixed radius around a zero): exact Taylor expansion at the zero, where the constant
  and linear terms are *theorems* (`pairP_tight`, `triP_tight`), the quadratic term is bounded
  below by an interval-checked matrix inequality, and the remainder by an interval bound on the
  third derivative.  Uses `Taylor.lean`.
* **Global** (a box not containing a zero): value and gradient at the box centre by tight interval
  evaluation, second-derivative bound on the box by crude interval evaluation, assembled by the
  second-order lemma of `Taylor.lean`.  Box lists are produced offline (Python, same arithmetic),
  Lean only re-checks.

## 2. Statement fixes to make before anything else (`Step 0`)

These are edits to existing files; all must build with `lake build` before T0 starts.

1. **The chord lower bound `24/25` is wrong and must become `9619/10000`.**  The certificate was
   designed for inner products `t ≤ 0.5373`, i.e. chords `s ≥ √0.9254 = 0.96198`.  The Lean
   statements ask for `s ≥ 0.96` (`t ≤ 0.5392`), outside the design, and there
   `triP pivotsNum` is **negative**: `triP(1.6835, 0.96, 0.96) = −1.3·10⁻⁵` with Gram value
   `+0.002` (inside the admissible region).  So `triP_global` as stated is false.  With the bound
   `9619/10000` (`0.9619² = 0.92525 ≤ 0.9254`, so `tri_of_poly`'s `lo` argument still works) the
   worst value on the whole region is `+2.07·10⁻⁵`, at `(1.685, 0.9619, 0.9619)`.
   Replace `24 / 25` by `9619 / 10000` in: `Bound.lean` (`pair_of_poly`, `tri_of_poly` — in the
   `lo` proofs `norm_num` still closes `(9619/10000)² ≤ 2 − 2·(5373/10000)`), `Tasks.lean`
   (`pairP_nonneg`, `triP_global`, `triP_nonneg`), `Tri5b/Symmetry.lean` (`TriSorted`,
   `tri_nonneg_of`).  The pair polynomial is fine either way (`pairP(0.96) = 2.5·10⁻⁴`).
2. **`pivotEps := 1 / 10 ^ 12`** (was `10⁻⁶`).  Task 5 needs the pivots to about `10⁻⁹`; with
   `u*` to 22 digits the residual bound gives `≈ 4·10⁻¹⁵`, so `10⁻¹²` is comfortable.  Nothing
   downstream in `Tasks.lean` uses the old value except the comments.
3. **Local radii become per-type**: replace `rhoLocal : ℝ := 1/500` by `rho0 : Fin 5 → ℝ`
   (values fixed by T5a; expect `10⁻⁴`–`10⁻³`), and thread it through `triP_local`, `triP_global`,
   `triP_nonneg`, `Tri5b.rho`, `TriLocal`, `TriSorted`, `tri_nonneg_of`.  Also make `triP_nonneg`
   go through `Tri5b.tri_nonneg_of` (sorted cone), so that 5b is only asked on `c ≤ b ≤ a`.
4. Add to `Tasks.lean` the two sharper enclosures 1b needs (`uStar` to 22 digits, `√2` to 40):
   they are proved exactly as `uStar_mem_Icc_sharp` in `Thomson/Enclosure.lean`; see T1b §2.

## 3. Numbers everyone should know (at `pivotsNum`, double precision; `docs/history/survey.py` and
`docs/history/check_kernel.py` reproduce them — run both from the repository root)

| quantity | value |
|---|---|
| chords `A, D, N, F` | `1.17125, 1.65639, 1.28769, 1.89689` |
| `‖pivotMatrix‖∞`, `‖N‖∞`, `‖I − N·pivotMatrix‖∞` | `132`, `3.9·10³`, `1.3·10⁻¹⁰` (`scripts/threepoint/task1a_pivotmatrix.json`, `N` has 12-digit rational entries) |
| smallest eigenvalue of `H'_k`, `k = 0..5` | `1.42e−3, 1.18e−3, 5.92e−4, 1.43e−3, 1.41e−3, 1.49e−3` |
| `P''(s_X)` at the four chords | `1.59e−2, 7.74e−3, 7.27e−3, 4.37e−2` |
| `min pairP` at distance `≥ 0.01 / 0.02 / 0.05` from the chords | `3.7e−7 / 1.2e−6 / 4.5e−6` |
| Hessian eigenvalues of `triP` (chord variables) at types 0..4 | `(3.9e−3, .135, .157)`, `(2.0e−3, 4.0e−3, .118)`, `(9.3e−4, 7.3e−3, 3.3e−2)`, `(6.4e−4, 3.3e−3, 6.7e−2)`, `(8.4e−4, 6.2e−3, 6.9e−2)` |
| `triP / (½ δᵀHδ)` along the softest eigenvector, `|δ| = 10⁻³ … 10⁻¹` | between `0.73` and `3.6` for all types (type 3 reaches `22` at `0.1`): the quadratic part is never cancelled |
| `min triP` on the sorted Gram region, Chebyshev distance `≥ 0.02 / 0.05 / 0.1` from all types | `1.4e−7 / 3.3e−7 / 6.7e−7` (`c ≥ 0.962`) |
| `min triP` on the face `c = 0.9619` | `+2.07e−5` |
| `triP` outside the Gram region | negative (down to `−6e−4`): boundary boxes need the S-procedure |
| kernel speed | `decide +kernel`: ~1000 `Iv.mul`/s; `native_decide`: ~10⁶/s |

## 4. Conventions

* New Lean lives in `Thomson/Interval/` (T0), `Thomson/ThreePoint/Kernel*.lean` (1c),
  `Thomson/TriangleLocal/Calculus/` (per-task certificate files), `Thomson/TriangleGlobal/` (Task 5).  Add every
  new module to `Thomson.lean`.
* Generated Lean files carry the header `-- GENERATED by scripts/threepoint/<script>.py; do not edit` and
  the generating script is committed in `scripts/threepoint/`.
* Atom numbering for `E` (fixed, used by every task): `0,1,2` = point variables (`s` for the pair
  polynomial; `a,b,c` for the triangle; `u,v,t` inside `FhE`), `3` = `uStar`, `4+j` = pivot `j`
  (`j < 24`), `28` = `√2`, `29` = `rStar`, `30` = `s2Star`, `31` = `s4Star`, `32..34` = `rStar⁻¹, s2Star⁻¹, s4Star⁻¹`
  (for `E(u*)` in the bound row, T1b §3), `100+` = entries of the constant matrices `M_k` (T5b §1).
* A task is done when `lake build` is clean, the leaf's `sorry` is gone, and
  `#print axioms Thomson.thomson_eight_lower` shows only `propext, Classical.choice, Quot.sound`
  plus `sorryAx` for the leaves still open (plus `Lean.ofReduceBool` once 5b is in).
* Do not touch `scripts/threepoint/task1_*.py` outputs or `CertData.lean` except through
  `task1_emit_lean.py` (T0 extends that script to also emit the `E`-tables).
