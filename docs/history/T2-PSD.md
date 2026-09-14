# T2 — `certH_posSemidef (k : Fin 6) : (certH k).PosSemidef`

*Needs: T1b (`pivots_close`).  Output: `Thomson/TriangleLocal/Calculus/PSD.lean` and the generated
`Cert/PSDData.lean`.  Rational arithmetic only (`norm_num`), no interval kernel needed.*

## 1. The mathematics

`certH k = Hp pivots k = Hp pivotsNum k + Δ_k`, with `|Δ_k[a,b]| ≤ pivotEps` and `Δ_k` supported on
the pivot slots of block `k` (`certH_sub_pivotsNum_le`).  The matrix `A_k := Hp pivotsNum k` is
rational and symmetric, its top-left `(8−k)×(8−k)` block has smallest eigenvalue
`λ_k ∈ {1.42e−3, 1.18e−3, 5.92e−4, 1.43e−3, 1.41e−3, 1.49e−3}`, and its last row and column are
zero (column `8−k` of `B` is zero and `Hfix`/`slot` never touch index `8−k` — check this in the
tables; if some `Hfix k a (8−k)` is nonzero, treat the block as full size instead).

Certificate: rational `L_k` (unit lower triangular) and `d_k` (positive diagonal), both rounded to
20 digits, with residual `R_k := A_k − μ_k·P_k − L_k D_k L_kᵀ`, `μ_k := λ_k/2`, `P_k := diagonal (indicator of a < 8−k)`.
Then for every `x`:

```
xᵀ certH x = xᵀ (L D Lᵀ) x + μ xᵀ P x + xᵀ R x + xᵀ Δ x
           ≥ 0 + μ Σ_{a<8−k} x_a² − (Σ|R_ab|) Σ_{a<8-k} x_a² − (Σ|Δ_ab|) Σ_{a<8-k} x_a²  ≥ 0
```

because `Σ|R| ≲ 10⁻¹⁸`, `Σ|Δ| ≤ 14·pivotEps ≤ 1.4·10⁻¹¹`, and `μ ≥ 2.9·10⁻⁴`.  (Both `R` and `Δ`
are supported inside the `(8−k)` block, so `|x_a x_b| ≤ (x_a² + x_b²)/2` only involves those
coordinates.)

## 2. Step 1 — data (`scripts/threepoint/psd_lean.py`)

For each `k`: build `A_k` from `HfixQ` and `pivotsNumQ` exactly (fractions), take the `(8−k)` block,
compute `L, d` by Cholesky-LDL in `mpmath` at 40 digits of `A − μ P`, round to 20-digit rationals,
recompute `R = A − μP − L D Lᵀ` **exactly in fractions**, print `Σ|R_ab|` (expect `≤ 10⁻¹⁷`), and
emit

```lean
def Lq (k : Fin 6) : Matrix (Fin (9-k)) (Fin (9-k)) ℚ := …   -- unit lower triangular, zeros in last row/col
def dq (k : Fin 6) : Fin (9-k) → ℚ := …                       -- > 0 on a < 8−k, 0 at a = 8−k
def muq (k : Fin 6) : ℚ := …
def rbound (k : Fin 6) : ℚ := …                                -- ≥ Σ|R_ab|, e.g. 10⁻¹⁶
```

## 3. Step 2 — Lean

```lean
/-- The exact residual identity, entrywise: 81 rational equalities per block. -/
theorem residual_bound (k : Fin 6) (a b : Fin (9-k)) :
    |Hp pivotsNum k a b - (muq k : ℝ) * (if (a:ℕ) < 8 - k ∧ a = b then 1 else 0)
      - ((Lq k).map (↑) * Matrix.diagonal ((↑) ∘ dq k) * ((Lq k).map (↑))ᵀ) a b| ≤ (rbound k : ℝ) / 81 := by
  fin_cases k <;> fin_cases a <;> fin_cases b <;>
    simp [Hp, Hfix, HfixTable, eH, slot, pivotsNum, Lq, dq, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
```

(`Hp pivotsNum k a b = Hfix k a b + Σ_j eH j k a b · pivotsNum j` — the sum has one or zero
nonzero terms; `simp [eH, slot]` decides the `if`s.)  This is 271 `norm_num` goals on 20-digit
rationals; a minute or two.  If `fin_cases` on `Fin (9 - k)` is awkward with the dependent size,
prove six separate lemmas `residual_bound_0 … residual_bound_5` with `k` a numeral.

```lean
/-- Quadratic-form bound for a small symmetric perturbation supported on the first `n₀` coordinates. -/
theorem abs_quad_le {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) (n₀ : ℕ) (ε : ℝ)
    (hR : ∀ a b, |R a b| ≤ ε) (hsupp : ∀ a b, (n₀ ≤ a ∨ n₀ ≤ b) → R a b = 0) (x : Fin n → ℝ) :
    |x ⬝ᵥ (R *ᵥ x)| ≤ (n₀ ^ 2 * ε) * ∑ a with (a : ℕ) < n₀, x a ^ 2
-- |Σ_ab R_ab x_a x_b| ≤ Σ_ab |R_ab| |x_a||x_b| ≤ ε Σ_{a,b<n₀} (x_a² + x_b²)/2 = ε n₀ Σ_{a<n₀} x_a².
```

(For `Δ`, `hR` comes from `certH_sub_pivotsNum_le` with `ε = 14·pivotEps`; the `Σ_j eH` there is
`≤ 14` since every pivot lies in exactly one slot — or just bound it by `24`.)

```lean
theorem certH_posSemidef (k : Fin 6) : (certH k).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?herm, ?pos⟩
  · -- symmetric: `Matrix.IsHermitian.ext`, `star` trivial on ℝ, `Hp_symm` (Tri5b/MForm.lean)
  · intro x; simp only [star_trivial]
    -- decompose certH k = L D Lᵀ + μ P + R + Δ  (as matrices, by `ext`, from residual_bound's defining identity)
    -- xᵀ L D Lᵀ x = Σ_r d_r (Lᵀx)_r² ≥ 0   (dot_mulVec_sum_eq_trace-style; or Matrix.posSemidef_conjTranspose_mul_self)
    -- xᵀ μP x = μ Σ_{a<8−k} x_a²
    -- |xᵀ R x| ≤ (rbound k) Σ …, |xᵀ Δ x| ≤ 14·pivotEps·… by abs_quad_le
    -- conclude with `norm_num [muq, rbound, pivotEps]` for μ − rbound − 14·pivotEps·(8−k)² ≥ 0 and `nlinarith`
```

For the first bullet note `Matrix.PosSemidef` in this Mathlib is the `Finsupp` form; go through
`posSemidef_iff_dotProduct_mulVec` (exists, `PosDef.lean:297`).

## 4. Acceptance

`#print axioms Thomson.certH_posSemidef` standard.  `certH_factor` and hence
`exists_threePointCert`'s `D_nonneg` path close automatically.
