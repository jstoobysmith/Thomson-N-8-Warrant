# T5a — `triP_local (m : Fin 5)`: nonnegativity on the cube of radius `rho0 m` about `touchType m`

*Needs: T0, T1b, T1c(ii) (through `triP_tight`).  Output: `Thomson/TriangleLocal/Calculus/TriLocal.lean`,
data `Cert/TriLocalData.lean`.  Kernel `decide`; five Hessians and five third-derivative bounds.*

This is the three-variable version of T4 §2, with a 3×3 matrix inequality in place of `P'' ≥ c`.
The radius is small (expect `rho0 m ≈ 10⁻⁴`–`10⁻³`); the *large* neighbourhood is handled by T5b's
shells, not here.  Do not try to push `rho0` up: T5b's cost is insensitive to it.

## 1. Numbers (chord variables, at `pivotsNum`)

| type `m` | `τ_m` | Hessian eigenvalues of `triP` |
|---|---|---|
| 0 `FFA` | `(1.8969, 1.8969, 1.1712)` | `3.92e−3, 0.135, 0.157` |
| 1 `FDN` | `(1.8969, 1.6564, 1.2877)` | `1.98e−3, 4.02e−3, 0.118` |
| 2 `FNA` | `(1.8969, 1.2877, 1.1712)` | `9.29e−4, 7.28e−3, 3.30e−2` |
| 3 `DAA` | `(1.6564, 1.1712, 1.1712)` | `6.37e−4, 3.32e−3, 6.70e−2` |
| 4 `NNA` | `(1.2877, 1.2877, 1.1712)` | `8.41e−4, 6.23e−3, 6.94e−2` |

Third derivatives: measure `K_m := max over the cube of Σ_{i,j,k} |∂³T/∂x_i∂x_j∂x_k|` numerically
first (`scripts/threepoint/tri_local.py`, finite differences at 30 digits, then the interval value);
expect `K_m` of order `1`–`10`.  Then `rho0 m := (3/2)·λ_m / K_m` rounded down to a short rational.

## 2. The statement to prove

```lean
theorem triP_local (m : Fin 5) : ∀ a b c : ℝ,
    |a − (touchType m).1| ≤ rho0 m → |b − (touchType m).2.1| ≤ rho0 m → |c − (touchType m).2.2| ≤ rho0 m →
    0 ≤ triP pivots a b c
```

Write `δ := (a, b, c) − τ_m`, `φ t := triP pivots (τ_m + t·δ)`.

## 3. Step 1 — derivatives of `φ` through `E`

With `triPE` (T0 §5) and `E.hasDerivAt_curve` for `γ i t = τ_i + t δ_i`, `γ' i = δ_i` (`n = 3`):

* `φ' t = Σ_i (∂_i triPE).eval(τ + tδ) · δ_i`,
* `φ'' t = Σ_{i,j} (∂_i∂_j triPE).eval(τ + tδ) · δ_i δ_j`,
* `φ''' t = Σ_{i,j,k} (∂_i∂_j∂_k triPE).eval(τ + tδ) · δ_i δ_j δ_k`,

each obtained by applying `hasDerivAt_curve` to the previous derivative expression (the sums are
finite `Finset.sum`s over `Fin 3`; `HasDerivAt.sum`, `HasDerivAt.mul_const`).

* `φ 0 = triP pivots τ_m = 0` — `(triP_tight m).1`.
* `φ' 0 = Σ_i (deriv (triD pivots m i) 0) δ_i = 0` — `(triP_tight m).2 i` after identifying
  `(∂_i triPE).eval(τ_m) = deriv (triD pivots m i) 0` (`E.hasDerivAt_update` + `HasDerivAt.deriv`,
  since `triD` moves exactly coordinate `i`; same identification as in T1a §2).

## 4. Step 2 — the Hessian bound `φ'' 0 ≥ λ_m |δ|²`

`φ'' 0 = δᵀ H δ` with `H_ij := (∂_i∂_j triPE).eval (atomVal τ_m)`, a real symmetric 3×3 matrix
enclosed entrywise by `Hiv m i j := ((triPE.deriv i).deriv j).ieval (atomEnv (touchIv m))`.
Certificate (generated): a rational `λ_m`, a rational unit lower triangular `L_m` and positive
`d_m`, and `ε_m ≥` the width of the enclosures plus the rounding residual, such that

```lean
theorem quad_lower_of_ldl {H : Matrix (Fin 3) (Fin 3) ℝ} {L : Matrix (Fin 3) (Fin 3) ℚ} {d : Fin 3 → ℚ} {lam ε : ℚ}
    (hsym : ∀ i j, H i j = H j i)
    (hres : ∀ i j, |H i j − (lam : ℝ) * (if i = j then 1 else 0) − (L.map (↑) * diagonal ((↑) ∘ d) * (L.map (↑))ᵀ) i j| ≤ ε)
    (hd : ∀ i, 0 ≤ d i) (hε : 9 * ε ≤ lam') (δ : Fin 3 → ℝ) :
    (lam − lam' : ℝ) * (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) ≤ δ ⬝ᵥ (H *ᵥ δ)
```

(`xᵀ L D Lᵀ x ≥ 0`, and the residual's quadratic form is `≥ −9ε|δ|²` by `|δ_i δ_j| ≤ (δ_i² + δ_j²)/2`.)
`hres` is checked per entry: `H i j ∈ Hiv m i j` (`E.ieval_mem`) and the rational number
`lam·[i=j] + (L D Lᵀ)_ij` lies within `ε` of both endpoints — a `decide +kernel` on the `Iv` data
plus `norm_num` on the rational LDL product.  Take `lam' := lam/2` and `λ_m := lam/2` as the final
constant.  Generate `L, d` from the midpoint Hessian in Python (30 digits, round to 15).

## 5. Step 3 — the remainder bound `|φ''' t| ≤ K_m |δ|_∞³ ≤ K_m ρ |δ|_∞²`

For `t ∈ [0,1]` the point `τ_m + tδ` lies in the cube `C_m := Π [τ_i − ρ, τ_i + ρ]`
(`cubeIv m := ![(touchIv m).1.hull-widened by ρ, …]`).  Bound each of the 27 third partials by
one interval evaluation on `cubeIv m`, sum the `absHi`s: this is `K_m` (as a scaled integer;
`decide +kernel` proves `Σ_{ijk} absHi ≤ K_m·2^prec`).  Then
`|φ''' t| ≤ Σ_{ijk} |∂³| |δ_i||δ_j||δ_k| ≤ K_m ρ³`, and since we need it relative to `|δ|²`, use
`|δ_i δ_j δ_k| ≤ ρ · (δ_i² + δ_j² + δ_k²)/3` — i.e. state the bound as
`|φ''' t| ≤ K_m ρ (δ_0² + δ_1² + δ_2²)` (each of the 27 terms `≤ ρ (δ_i²+δ_j²+δ_k²)/3·M_ijk`, summed).

## 6. Step 4 — assembly

`taylor3_lower` (T0 §3) with `K := K_m ρ (Σ δ_i²)`:
`φ 1 ≥ φ'' 0 / 2 − K/6 ≥ (λ_m/2 − K_m ρ/6)(Σ δ_i²) ≥ 0` once `K_m ρ ≤ 3 λ_m` (`norm_num` on the
rational data).  `φ 1 = triP pivots a b c`.

## 7. Data file (`scripts/threepoint/tri_local.py` → `Cert/TriLocalData.lean`)

Per type: `rho0Q m : ℚ`, `lamQ m : ℚ`, `Lq m`, `dq m`, `epsQ m`, `Kq m`.  The script must compute
`K_m` with the *same* interval evaluation as Lean (implement `Iv` in Python — 40 lines — and
evaluate the same `E`-trees; or overestimate by a safety factor 4 and let Lean confirm).
Print, for the record, the final margins `3λ_m − K_m ρ_m`.

## 8. Acceptance

`#print axioms Thomson.triP_local` standard.  The values `rho0 m` are then fixed for T5b; put
them in `Tasks.lean` (`noncomputable def rho0 (m : Fin 5) : ℝ := (rho0Q m : ℝ)`).
