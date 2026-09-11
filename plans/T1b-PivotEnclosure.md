# T1b — `pivots_close : ∀ j, |pivots j - pivotsNum j| ≤ pivotEps` with `pivotEps = 10⁻¹²`

*Needs: T0, T1a (its `Miv`, `NQ`, and the contraction bound `η`).  Output:
`Thomson/ThreePoint/Cert/PivotEnclosure.lean`.  Kernel `decide`, ≈ 10⁵ operations.*

## 1. The mathematics

With `M = pivotMatrix`, `N` the rational approximate inverse, `Eₘ = 1 − N M`, `‖Eₘ‖∞ ≤ η < 1`
(1a), and `res := pivotRhs − M *ᵥ pivotsNum` (the 24 rows evaluated at `pivotsNum`, by
`rowFun_eq_mulVec`: `res i = −rowFun i pivotsNum`):

`x := pivots − pivotsNum` satisfies `M x = res` (because `M pivots = pivotRhs`, from
`Matrix.mul_nonsing_inv` with 1a).  Then `x = N (M x) + Eₘ x = N res + Eₘ x`, so
`‖x‖∞ ≤ ‖N‖∞ ‖res‖∞ + η ‖x‖∞`, i.e. `‖x‖∞ ≤ ‖N‖∞ ‖res‖∞ / (1 − η)`.

Numbers: `‖N‖∞ = 3.9·10³`, `η ≈ 10⁻⁹`, true `‖res‖∞ ≈ 2·10⁻²¹`; the computed enclosure of `res`
is limited by the atom enclosures: with `u*` to 22 digits the widths are `≈ 10⁻¹⁸`, so the bound
is `≈ 4·10⁻¹⁵ < 10⁻¹²`.

## 2. Step 1 — the sharper enclosures (also used by T0 §4)

Copy `Thomson/Enclosure.lean` and redo it with longer rationals:

* `sqrt2_bounds_sharp40`: `√2` between two 40-digit rationals (`Real.lt_sqrt`, `Real.sqrt_lt'`,
  `norm_num`).
* `uStar_mem_Icc_sharp22`: `u* ∈ [u_lo, u_hi]` with 22-digit rationals straddling
  `u* = 0.3140893678892018651770997…` (get 30 digits from `hp_project.py`'s `findroot` at
  `mp.dps = 50`).  Same proof as `uStar_mem_Icc_sharp`: `antiprismEnergy'_neg_sharp22` and
  `_pos_sharp22` via `term_lt`/`lt_term` with rational cube-root bounds — produce the six
  rational bounds `y, z` with a 10-line Python helper (they must satisfy the side conditions
  `y³ ≤ X ≤ z³` at the two endpoints; print 30 digits and round in the safe direction).
* `rStar_bounds_sharp35`, `s2Star_bounds_sharp35`, `s4Star_bounds_sharp35`: the two-line
  `nlinarith` proofs of `Sharp.lean`, with the new inputs.

Then `atomEnvC` (T0 §4) uses these.  Check with Python that the *products* of these widths through
`entryE`/the residual give `‖res‖∞`-widths `< 10⁻¹⁶` before proceeding.

## 3. Step 2 — the residual as `E`-terms

`res i = −rowFun i pivotsNum = −evalRow pivotsNum (rowSpec i)`.  Mirror `evalRow` at `pivotsNum`:

```lean
def rowE (i : Fin 24) : E :=          -- value of rowFun i at the *pivot atoms* (vars 4..27)
  match rowSpec i with
  | .bound     => smul (1/2) (… 64 a0Q − 8(a0Q + a1Q) − 8 · FhE 1 1 1 …) − ⟨E(u*)⟩
  | .pairVal X => pairPE.subst (0 ↦ chordE X)
  | .pairDer X => (pairPE.deriv 0).subst (0 ↦ chordE X)
  | .triVal m  => triPE.subst (σ m)
  | .triD m c  => (triPE.deriv c).subst (σ m)
```

The bound row contains `antiprismEnergy uStar`, which is not a polynomial in the atoms.  Use
`antiprismEnergy_uStar_eq : E(u*) = (4√2+2)/rStar + 8/s2Star + 8/s4Star` (`Toolkit.lean`) and
multiply the bound row through by `rStar * s2Star * s4Star > 0` — or simpler: add three more atoms
`32, 33, 34` for `rStar⁻¹, s2Star⁻¹, s4Star⁻¹` with their own enclosures (from the 35-digit chord
bounds by `one_div_lt_one_div_of_lt`), so that `E(u*)` is the `E`-term
`(4·var 28 + 2)·var 32 + 8·var 33 + 8·var 34`.  This is the cleaner route; do it in T0 §4.

Bridge: `theorem rowE_eval (i) : (rowE i).eval (atomVal' pivotsNum) = rowFun i pivotsNum`, where
`atomVal'` is `atomVal` with the pivot atoms set to `pivotsNum` instead of `pivots`
(generalise `atomVal` over the pivot vector: `atomVal (p : Fin 24 → ℝ) (pt : Fin 3 → ℝ)`).  Proof per
`rowSpec` case as in T1a §2, using `pairPE_eval`, `triPE_eval`, `E.hasDerivAt_update`.

Environment: `atomEnvNum` = `atomEnvC` but with pivot atoms set to the *exact* rationals
`Iv.ofRat (pivotsNumQ j)` (width one ulp), since here the pivots really are `pivotsNum`.

## 4. Step 3 — the checker and the theorem

```lean
def resIv (i : Fin 24) : Iv := ((rowE i).ieval atomEnvNum).neg
/-- `bound = ‖N‖∞ · max_i |res|_i / (1 − η)` as a scaled integer; checks `bound ≤ pivotEps`. -/
def enclosureOK (N : Fin 24 → Fin 24 → ℚ) (resIv : Fin 24 → Iv) (ηNum ηDen : ℕ) (eps : ℚ) : Bool

theorem enclosureOK_sound (M : Matrix _ _ ℝ) (hM : IsUnit M.det) (N) (Miv) (hMiv : ∀ i j, (Miv i j).mem (M i j))
    (hη : contractionBound N Miv ≤ η) (hη1 : η < 1)                      -- the scalar version of T1a's checker
    (res : Fin 24 → ℝ) (hres : ∀ i, (resIv i).mem (res i))
    (h : enclosureOK N resIv … = true) :
    ∀ j, |(M⁻¹ *ᵥ res) j| ≤ pivotEps
```

The soundness proof is the inequality chain of §1 with `x := M⁻¹ *ᵥ res` (so `M x = res` by
`Matrix.mul_nonsing_inv` and `Matrix.mulVec_mulVec`), `‖·‖∞` handled as in T1a via the maximising
index.  Rather than dividing by `1 − η` in ℤ, check the equivalent `‖N‖∞ ‖res‖∞ ≤ pivotEps · (1 − η)`
with everything as scaled integers.  Refactor T1a's `contractionOK` into a function returning the
row-sum maximum (`contractionBound : … → ℤ`) so both tasks share it.

Finally

```lean
theorem pivots_close : ∀ j, |pivots j - pivotsNum j| ≤ pivotEps := by
  have hdet := pivotMatrix_det_isUnit
  have hx : pivots - pivotsNum = pivotMatrix⁻¹ *ᵥ (pivotRhs - pivotMatrix *ᵥ pivotsNum) := by
    simp [pivots, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet]
  have hres : ∀ i, (resIv i).mem ((pivotRhs - pivotMatrix *ᵥ pivotsNum) i) := by
    intro i; rw [Pi.sub_apply, ← sub_eq_zero.mpr …]   -- (pivotRhs − M pivotsNum) i = −rowFun i pivotsNum, from rowFun_eq_mulVec
    …  exact Iv.mem_neg (rowE_eval i ▸ E.ieval_mem _ atomEnvNum_mem)
  intro j; rw [← Pi.sub_apply, hx]
  exact enclosureOK_sound _ hdet NQ Miv Miv_mem … (by decide +kernel) j
```

## 5. Pitfalls

* `rowFun_eq_mulVec` gives `rowFun i p = (M *ᵥ p) i − pivotRhs i`; the sign of `res` is
  `pivotRhs − M pivotsNum = −rowFun · pivotsNum`.  Get it right once, in `hres`.
* The `deriv` rows: `pairPE.deriv 0` doubles the tree; that is fine (≈ 2·10³ operations each).
* If `enclosureOK` fails by a small factor, the culprit is the width of `atomEnvC 3` (`u*`); the
  fix is more digits in `uStar_mem_Icc_sharp22`, not a bigger `pivotEps` (Task 5 needs `10⁻⁹`).

## 6. Acceptance

`#print axioms Thomson.pivots_close` standard.  After this, `certH_sub_pivotsNum_le`,
`pairP_sub_pivotsNum_le`, `triP_sub_pivotsNum_le` in `Tasks.lean` are theorems, and T0's
`atomEnv_mem` can drop its `pivots_close` hypothesis.
