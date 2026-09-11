# T1a — `pivotMatrix_det_isUnit : IsUnit pivotMatrix.det`

*Needs: T0 (§1–2, §4 without pivots, §5 `GhE`).  Output: `Thomson/ThreePoint/Cert/PivotDet.lean`
(+ generated `Cert/PivotData.lean`).  Kernel `decide`, about 10⁵ interval operations.*

## 1. The mathematics (unchanged from the sketch, now made checkable)

Let `N` be the rational 24×24 matrix in `threepoint/task1a_pivotmatrix.json` (`N_num / den`,
12-digit entries), `M := pivotMatrix`, `Eₘ := 1 − N * M`.  Numerically `‖Eₘ‖∞ = 1.3·10⁻¹⁰`.
If `M *ᵥ x = 0` then `x = Eₘ *ᵥ x`, so `‖x‖∞ ≤ ‖Eₘ‖∞ ‖x‖∞`, hence `x = 0`.  So `M.mulVec` is
injective, `Matrix.mulVec_injective_iff_isUnit` gives `IsUnit M`, and `Matrix.isUnit_iff_isUnit_det`
finishes.

What has to be *computed*: an interval enclosure `Miv : Fin 24 → Fin 24 → Iv` of `M`, the
interval matrix `1 − N·Miv`, and the bound `max_i Σ_j |(1 − N·Miv)_ij| < 1`.

## 2. Step 1 — every entry of `M` as an `E`-term (no `deriv` left)

From `Perturb.lean` each entry is a fixed multiple of `Gh j` at a chord point, or a `deriv` of
such.  Define the mirrored row entries (`Thomson/ThreePoint/Cert/PivotData.lean`, hand-written, 24
cases through `rowSpec`):

```lean
/-- `E`-term whose value is `pivotMatrix i j`.  Variable 0 is the unused point variable. -/
def entryE (i j : Fin 24) : E :=
  match rowSpec i with
  | .bound      => smul (-4) (GhE j (const 1) (const 1) (const 1))
  | .pairVal X  => (pairLinE j).subst (fun k => if k = 0 then chordE X else var k)
  | .pairDer X  => ((pairLinE j).deriv 0).subst (fun k => if k = 0 then chordE X else var k)
  | .triVal m   => (triLinE j).subst (σ m)
  | .triD m c   => ((triLinE j).deriv c).subst (σ m)
-- pairLinE j := −(3·var 0) · GhE j 1 (tOfS (var 0)) (tOfS (var 0))     (mirrors pairP_single_sub)
-- triLinE j  := −(var 0 · var 1 · var 2) · GhE j (tOfS (var 0)) (tOfS (var 1)) (tOfS (var 2))
-- σ m substitutes the three coordinates of touchTypeE m for vars 0,1,2.
```

and prove the single bridge

```lean
theorem entryE_eval (i j : Fin 24) : (entryE i j).eval (atomVal 0) = pivotMatrix i j
```

by `cases hrow : rowSpec i` and, per case, the matching `pivotMatrix_*_row` lemma of
`Perturb.lean` on the right and `E.eval_subst`, `GhE_eval`, `chordE_eval`, `touchTypeE_eval` on the
left.  For the two derivative cases use `E.hasDerivAt_update` (T0) to rewrite
`deriv (fun s => …) (chord X)` as `((pairLinE j).deriv 0).eval (Function.update … 0 (chord X))`
via `HasDerivAt.deriv`; the function inside `deriv` in `pivotMatrix_pairDer_row` is exactly
`fun s => (pairLinE j).eval (Function.update (atomVal 0) 0 s)` after `pairLinE_eval`, so first
rewrite the function with `funext` and then apply `HasDerivAt.deriv`.  The `triD` case is the
same with the line `d ↦ touchType m + d·e_c` (variable `c` of `triLinE`), i.e. the derivative in
variable `c` at the point `touchType m` — note that `triD` moves only one coordinate, so it *is*
the partial derivative: `Function.update (σ-point) c (τ_c + d)`.

## 3. Step 2 — the checker

```lean
/-- Row-wise ℓ¹ upper bound of `1 − N·Miv` as scaled integers; returns `true` iff every row sum is `< 2^prec`. -/
def contractionOK (N : Fin 24 → Fin 24 → ℚ) (Miv : Fin 24 → Fin 24 → Iv) : Bool :=
  (List.finRange 24).all fun i =>
    ((List.finRange 24).map fun j =>
      let e := (if i = j then Iv.ofInt 1 else Iv.ofInt 0).sub
                 (E-free: Σ_k (Iv.ofRat (N i k)).mul (Miv k j), as a foldr)
      e.absHi).foldr (· + ·) 0 < Iv.sc

theorem contractionOK_sound (N) (Miv) (M : Matrix (Fin 24) (Fin 24) ℝ)
    (hM : ∀ i j, (Miv i j).mem (M i j)) (h : contractionOK N Miv = true) :
    ∀ x : Fin 24 → ℝ, M *ᵥ x = 0 → x = 0
```

Proof of soundness: for `x` with `M x = 0`, let `c := Finset.univ.sup' _ (fun j => |x j|)`
(attained at some `j₀`).  `x = x − N·(M x) = (1 − N M) x`, so
`|x j₀| ≤ Σ_j |(1 − N M) j₀ j| |x j| ≤ (Σ_j |(1−NM) j₀ j|) c < c` unless `c = 0`.  The row sum is
bounded by the computed integer sum via `Iv.abs_le_of_mem` on each entry (interval `mem` of
`(1 − N M) i j` follows from `Iv.mem_sub`, `Iv.mem_mul`, `Iv.mem_ofRat`, and a `mem` for the
foldr-sum, proven by induction on the list).  Keep the checker's shape and the soundness proof's
shape identical (same foldr order), otherwise the `mem` lemma will not match.

Then:

```lean
def NQ : Fin 24 → Fin 24 → ℚ := ![![…], …]                                   -- generated from JSON
def Miv : Fin 24 → Fin 24 → Iv := fun i j => (entryE i j).ieval (atomEnv0)     -- atomEnv with pivot slots unused
theorem Miv_mem (i j) : (Miv i j).mem (pivotMatrix i j) := by
  rw [← entryE_eval]; exact E.ieval_mem _ (atomEnv_mem_nopivots …)
theorem pivotMatrix_det_isUnit : IsUnit pivotMatrix.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have := contractionOK_sound NQ Miv pivotMatrix Miv_mem (by decide +kernel) (x - y) (by rw [Matrix.mulVec_sub, hxy, sub_self])
  exact sub_eq_zero.mp this
```

`decide +kernel` here evaluates 576 `E.ieval`s (each `GhE` is one or two `BSBE` entries: ≤ 4
products of `Bpoly` polynomials with 6 permuted `S3` monomials, i.e. a few hundred interval
operations; the derivative rows are 2–3× that) plus the 24³ rational-times-interval products:
roughly `5·10⁵` operations, a few minutes.  If it is slow, first replace `Iv.ofRat (N i k)` by a
precomputed `Niv : Fin 24 → Fin 24 → Iv` table (generated as integers), which removes the
`ofRat` reductions.

## 4. Step 3 — accuracy check before writing Lean

The atoms enter `Miv` only through `atomEnvC` (uStar 22 digits, √2 40 digits, chords 35 digits).
Run `threepoint/pivotmatrix_lean.py`'s arithmetic in *interval* form (Python `fractions` with the
same outward rounding, or `mpmath.iv`) to confirm `max_i Σ_j |(1 − N·Miv)_ij| < 1` with the
enclosure widths actually used — expected `≈ 10⁻⁹`, far below `1`.  Do this first; it takes an
hour and prevents a day of kernel time on a wrong `N`.

## 5. Acceptance

`lake build Thomson.ThreePoint.Cert.PivotDet` clean; `#print axioms Thomson.pivotMatrix_det_isUnit`
= `propext, Classical.choice, Quot.sound`.  Then delete the `sorry` in `Tasks.lean` by
`import`ing the new file (the theorem name must stay `Thomson.pivotMatrix_det_isUnit`).
