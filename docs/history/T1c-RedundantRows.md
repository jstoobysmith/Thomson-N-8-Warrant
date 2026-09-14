# T1c — the two redundant rows: `row_pairVal_A` and `row_triD_FDN_v`

*Needs: nothing from T0 except (for 1c(ii)) the chain rule `E.hasDerivAt_curve` — or Mathlib's
`HasFDerivAt.comp_hasDerivAt`; either works.  Output: `Thomson/ThreePoint/Kernel.lean`
(generated, ≈ 110 `ring` identities), `Thomson/ThreePoint/Slack.lean` (the identity),
`Thomson/TriangleLocal/Calculus/Redundant.lean` (the two theorems).  No numerics at all.*

## 0. What is actually true (verified symbolically, `docs/history/check_kernel.py`)

Define the inner products of the antiprism family as functions of `u` (no square roots):

```
tA u = u,   tD u = 2u − 1,   tN u = −u + √2(1−u)/2,   tF u = −u − √2(1−u)/2
```

and the *combinatorial kernel matrix* (size `9−k`, entries polynomials in `u, √2`)

```
Acomb k u := 8·S3 k 1 1 1 + 6·[8·S3 k 1 (tA u) (tA u) + 4·S3 k 1 (tD u) (tD u) + 8·S3 k 1 (tN u) (tN u) + 8·S3 k 1 (tF u) (tF u)]
             + 6·[8·S3 k (tF u) (tF u) (tA u) + 16·S3 k (tF u) (tD u) (tN u) + 16·S3 k (tF u) (tN u) (tA u)
                  + 8·S3 k (tD u) (tA u) (tA u) + 8·S3 k (tN u) (tN u) (tA u)]
```

(this is `Σ_{i,j,l} S3_k(t_ij, t_il, t_jl)` over the antiprism at parameter `u`, grouped by the
14 triple types with their multiplicities; the grouping is only motivation, it is never proved).
Facts, all checked:

* `Acomb k u` has rank one for every `u`, `k = 0..5`;
* `ψ_kab(u) := (B_kᵀ · Acomb k u · B_k)[a,b]`, with `B_k` the tables of `CertData.lean` (built at
  `uStar`), satisfies **`ψ_kab(u) = (u − uStar)² · χ_kab(u)`** with `χ_kab` an explicit polynomial
  in `u, uStar, √2` of at most 170 terms.  In particular `ψ_kab(uStar) = 0` and
  `ψ'_kab(uStar) = 0`.  This is a polynomial identity — it holds with `uStar` replaced by any
  free variable, because `B` was built from the family's kernel vectors.

Everything in 1c follows from these 110 identities and elementary algebra.

## 1. The generated file `Kernel.lean`

Script `scripts/threepoint/kernel_lean.py` (start from `docs/history/check_kernel.py`, which already parses
`Bpoly` from `CertData.lean` and computes `ψ` and the quotient):

* For each `k ≤ 5` and `a ≤ b < 8 − k` (the last row/column of `B` is zero), emit

  ```lean
  theorem psi_k_a_b (u : ℝ) : psi k a b u = (u - uStar) ^ 2 * (CHI) := by
    unfold psi Acomb; simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, B, Bpoly,
      S3, Y3, Q3, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero,
      tA, tD, tN, tF, mul_zero, zero_mul, add_zero, zero_add]
    linear_combination (COF) * sqrt2_sq
  ```

  where `CHI` and `COF` are printed by sympy: write `ψ − (u−u*)²χ` as a polynomial in
  `w = √2`, reduce modulo `w² − 2`, and `COF` is the quotient (so the identity is exactly
  `ψ − (u−u*)²χ = COF · (w² − 2)`, closed by `linear_combination`, which calls `ring1`).
  Alternative if `linear_combination` is slow: `ring_nf` then `simp only [sqrt2_pow_even, sqrt2_pow_odd]`
  (two helper lemmas `√2 ^ (2n) = 2^n`, `√2 ^ (2n+1) = 2^n √2`) then `ring_nf`.
* Definitions emitted once at the top:

  ```lean
  noncomputable def tA (u : ℝ) : ℝ := u   -- etc.
  noncomputable def Acomb (k : ℕ) (u : ℝ) : Matrix (Fin (9 - k)) (Fin (9 - k)) ℝ := …
  noncomputable def psi (k a b : ℕ) (u : ℝ) : ℝ := if h : a < 9 - k ∧ b < 9 - k then ((B k)ᵀ * Acomb k u * B k) ⟨a, h.1⟩ ⟨b, h.2⟩ else 0
  ```
* Test one identity by hand first (the `k = 5` ones are smallest) to fix the `simp` set; the
  `Fin.sum_univ_succ` expansion of a 9-fold double sum gives 81 products, of which `simp` kills all
  but ≤ 4 because `Bpoly` reduces to `0` on the missing patterns (make sure `Bpoly` unfolds by
  `simp [Bpoly]` — it is a `match`; if not, add `@[simp]` equation lemmas via `Bpoly.eq_def`).
* Then the two consequences, uniform over the index:

  ```lean
  theorem psi_at_uStar (k a b) : psi k a b uStar = 0
  theorem psi_hasDerivAt_uStar (k a b) : HasDerivAt (psi k a b) 0 uStar
  -- both by `fin_cases` dispatch to psi_k_a_b; the second by
  -- HasDerivAt.mul of ((u − uStar)^2, derivative 2(u−uStar) = 0 at uStar) and (χ, differentiable by fun_prop),
  -- then `simp`.
  ```
  (For `b < a` use symmetry `psi k a b = psi k b a`, from `S3` symmetric and `Bᵀ A B` symmetric.)

## 2. The slack identity along the family (`Slack.lean`), hand-written

Chords and types as functions of `u` (with `chordU X uStar = chord X`, `touchTypeU m uStar = touchType m`
by `rfl`/`simp`):

```lean
noncomputable def rU u := Real.sqrt (1 - u);  s2U u := Real.sqrt (2 + 2u − √2(1−u));  s4U u := Real.sqrt (2 + 2u + √2(1−u))
noncomputable def chordU : Fin 4 → ℝ → ℝ := ![fun u => √2 * rU u, fun u => 2 * rU u, s2U, s4U]
noncomputable def touchTypeU : Fin 5 → ℝ → ℝ × ℝ × ℝ := … (same table as touchType with rU, s2U, s4U)
```

Define the two sums and the kernel term:

```lean
/-- `2·Σ_X mult_X · pairP p (s_X)/s_X` with multiplicities `A 8, D 4, N 8, F 8`. -/
noncomputable def pairSum (p) (u) : ℝ := 2 * (8 * pairP p (chordU 0 u) / chordU 0 u + 4 * pairP p (chordU 1 u) / chordU 1 u + 8 * … + 8 * …)
/-- `6·Σ_m mult_m · triP p τ_m / (a b c)` with multiplicities `8, 16, 16, 8, 8`. -/
noncomputable def triSum (p) (u) : ℝ := 6 * (8 * triP p a₀ b₀ c₀ / (a₀ b₀ c₀) + 16 * … + 16 * … + 8 * … + 8 * …)
/-- The Bachoc–Vallentin term `Σ_k ⟨H_k(p), B_kᵀ Acomb_k(u) B_k⟩`. -/
noncomputable def bvTerm (p) (u) : ℝ := ∑ k : Fin 6, ∑ a, ∑ b, Hp p k a b * psi k a b u
```

**Lemma S1** (`bvTerm_eq`): `bvTerm p u = 8·Fh (Hp p) 1 1 1 + 6·(8 Fh(Hp p) 1 (tA u) (tA u) + 4 … ) + 6·(8 Fh (Hp p) (tF u) (tF u) (tA u) + …)`.
Proof: unfold `Fh`, `bvTerm`, `psi`, `Acomb`; `Matrix.mul_add`, `Matrix.add_mul`, `Matrix.mul_smul`,
`Matrix.smul_mul`, `Finset.sum_add_distrib`, `Finset.mul_sum`; `ring`.  Purely structural.

**Lemma S2** (`inner_of_chord`): for `u ∈ [1/4, 1/2]`: `1 − (chordU X u)²/2 = t_X u` for the four `X`
(the four `chord_inner_*` lemmas of `Sharp.lean`, redone for general `u` with `Real.sq_sqrt`), and
the same for the three coordinates of each `touchTypeU m u`.  Also `0 < chordU X u`.

**Lemma S3** (`energy_eq_chordSum`): `antiprismEnergy u = 8/chordU 0 u + 4/chordU 1 u + 8/chordU 2 u + 8/chordU 3 u`
from `antiprism_energy_eq'` (`Antiprism.lean`: `E(u) = (4√2+2)/√(1−u) + 8/√(a+bu) + 8/√(b+au)`), using
`√2·√(1−u) = chordU 0 u`, `8/(√2 r) = 4√2/r` (`field_simp`, `sqrt2_sq`), and `a + bu = 2 + 2u − √2(1−u)`.

**Lemma S4** (`triCount`): `6·(8(2/s_F + 1/s_A) + 16(1/s_F + 1/s_D + 1/s_N) + 16(1/s_F + 1/s_N + 1/s_A) + 8(1/s_D + 2/s_A) + 8(2/s_N + 1/s_A)) = 6·(2·(8/s_A + 4/s_D + 8/s_N + 8/s_F))`
— `ring`.  (Every unordered pair lies in exactly 6 ordered distinct triples.)

**Lemma S5** (`centered`): `8·tA u + 4·tD u + 8·tN u + 8·tF u = -4` — `ring` (the `√2` terms cancel).

**Theorem S** (`slack_identity`): for `p : Fin 24 → ℝ` and `u ∈ [1/4, 1/2]`,

```
2 * (antiprismEnergy u − (64 a0Fix − 8 (a0Fix + a1Fix) − 8 Fh (Hp p) 1 1 1) / 2)
  = pairSum p u + triSum p u + bvTerm p u
```

Proof: unfold `pairSum`, `triSum`, `pairP`, `triP`; rewrite the inner products by S2 and
`bvTerm` by S1; `field_simp` with the chord positivity; then it is `ring` after substituting S3,
S4, S5 (do `linear_combination (coeffs) * S3 + … ` rather than hoping `ring` finds it: the
identity is linear in `Fh` values, and the only non-polynomial facts are S3, S4, S5).  Check the
bookkeeping first in sympy with symbolic `Fh` values — the script for that is ten lines.

## 3. 1c(i): `row_pairVal_A : pairP pivots (chord 0) = 0`

At `u = uStar`, with `p = pivots` and `h := pivotMatrix_det_isUnit` (Task 1a; if 1a is not yet
done, prove the statement under the hypothesis `IsUnit pivotMatrix.det` and discharge later —
`Tasks.lean` already threads it):

* `bvTerm pivots uStar = 0` by `psi_at_uStar` (`Finset.sum_eq_zero`).
* the left side of S is `0` by `row_bound h`.
* in `pairSum`, the three terms `X ≠ 0` vanish by `row_pairVal h X hX`; in `triSum`, all five by
  `row_triVal h m`.
* what remains: `2 · 8 · pairP pivots (chord 0) / chord 0 = 0` with `chord 0 > 0`
  (`Real.sqrt 2 * rStar > 0`), so `pairP pivots (chord 0) = 0`.

## 4. 1c(ii): `row_triD_FDN_v : deriv (triD pivots 1 1) 0 = 0`

Differentiate S in `u` at `uStar` (both sides are differentiable on a neighbourhood
`Set.Ioo (1/4) (1/2)`; `uStar` is interior by `uStar_mem_Icc`).

* Left side: `HasDerivAt (fun u => 2 (E u − const)) (2 E'(u*)) u*` from `hasDerivAt_antiprismEnergy`,
  and `antiprismEnergy'_uStar : E'(u*) = 0`.
* `bvTerm`: `HasDerivAt (bvTerm pivots) 0 uStar` from `psi_hasDerivAt_uStar` and `HasDerivAt.sum`.
* Pair terms: for each `X`, `g_X(u) := pairP pivots (chordU X u) / chordU X u` has derivative
  `(P'(s) s' s − P(s) s')/s²` at `u*` (chain rule `HasDerivAt.comp` with `pairP_differentiable`,
  and `HasDerivAt.div`), which is `0` because `P(s_X) = 0` (row_pairVal / 1c(i)) and
  `P'(s_X) = deriv (pairP pivots) (chord X) = 0` (`row_pairDer h X`).  The chord functions are
  differentiable at `u*` (`Real.hasDerivAt_sqrt` with positive radicand).
* Triangle terms: for `m`, `h_m(u) := triP pivots (a_m u) (b_m u) (c_m u) / (a_m u · b_m u · c_m u)`.
  Numerator: `HasDerivAt (fun u => triP pivots (a u) (b u) (c u)) (∂ₐT·a' + ∂ᵦT·b' + ∂_cT·c') u*`,
  where `∂ₐT = deriv (triD pivots m 0) 0` etc.  Get this from the multivariable chain rule: either
  `E.hasDerivAt_curve` on `triPE` (T0) with `γ = (a_m, b_m, c_m)`, together with the identification
  `deriv (triD pivots m c) 0 = ((triPE.deriv c).eval …)` (T0's `hasDerivAt_update`, as in T1a §2); or
  Mathlib's `HasFDerivAt.comp_hasDerivAt` with `fderiv` of `fun x : ℝ×ℝ×ℝ => triP pivots x.1 x.2.1 x.2.2`
  (differentiable by `fun_prop` after `unfold triP Fh`, cf. `Q3_differentiable`) and
  `fderiv … (e_c) = deriv (triD …) 0` via `HasFDerivAt.comp_hasDerivAt` on the line `d ↦ τ + d e_c`.
  The `E` route avoids `fderiv` bookkeeping; prefer it.
  All partials vanish by `row_triD h m c hmc` except `(m, c) = (1, 1)`, and `triP pivots τ_m = 0`
  (`row_triVal`), so the derivative of `h_m` at `u*` is `0` for `m ≠ 1` and
  `(deriv (triD pivots 1 1) 0) · b₁'(u*) / (a₁ b₁ c₁)` for `m = 1`, where `b₁ u = 2·rU u` and
  `b₁'(u*) = −1/rU u* = −1/rStar ≠ 0`.
* Assemble: the derivative of the right side at `u*` is `6 · 16 · X · (−1/rStar) / Π` with
  `X := deriv (triD pivots 1 1) 0`, the left side's is `0`; uniqueness of derivatives
  (`HasDerivAt.unique`) gives `X · (−96/(rStar · Π)) = 0`, hence `X = 0`.

## 5. Acceptance

`Kernel.lean` builds (budget: 110 identities × ≤ 30 s); `#print axioms` of both theorems is
standard *given* `pivotMatrix_det_isUnit`.  Then `pairP_tight` and `triP_tight` in `Tasks.lean` are
fully proved.
