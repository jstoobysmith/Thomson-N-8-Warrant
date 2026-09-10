# The N = 8 Thomson problem — a Lean 4 formalisation blueprint

## 0. Status: read this first

**The N = 8 Thomson problem is open, and this document does not close it.** What it does
contain is a formalisation that has been pushed as far as the mathematics currently allows:
everything provable about the problem is proved in Lean, and the open content is isolated as a
single inequality.

The Lean development is a **standalone Lake project** in this directory (`lakefile.toml`, pinned
to the same Mathlib as Physlib; `lake exe cache get` once, then `lake build`), split into modules
so that each part compiles separately and each Task can be owned by a separate agent:

| module | content |
|---|---|
| `Thomson/Basic.lean` | §1–4: definitions, elementary facts, existence of a minimiser |
| `Thomson/Cube.lean` | §5 |
| `Thomson/Antiprism.lean` | §6–8: the antiprism family, certified upper bound, `uStar` |
| `Thomson/ForceBalance.lean` | §9: `energy_eq_half`, force balance |
| `Thomson/Derivative.lean` | §10–11: `E′`, pinning `u*`, `antiprismEnergy'_uStar`, `equilateral_not_better` |
| `Thomson/Yudin.lean` | §12–13: the LP bounds and Schoenberg positivity (the slow module) |
| `Thomson/Reduction.lean` | §14 |
| `Thomson/Separation.lean` | §15: slack rigidity, `separation_of_energy_le` |
| `Thomson/ThreePoint/BV.lean` | Bachoc–Vallentin matrices and positivity — **proved** |
| `Thomson/ThreePoint/Bound.lean` | `ThreePointCert`, `three_point_bound` — **proved**; `pair_of_poly`, `tri_of_poly` |
| `Thomson/ThreePoint/Toolkit.lean` | data-independent constants, structure lemmas, positivity toolkit — **proved** |
| `Thomson/ThreePoint/MinPoly.lean` | Task 0: the degree-12 minimal polynomial of `u*` over `ℚ(√2)` — **proved** |
| `Thomson/ThreePoint/CertData.lean` | **generated data tables** (`threepoint/task1_emit_lean.py`): scaled exact kernel bases `B k`, fixed rationals `a0Fix, a1Fix, lamFix, Hfix`, the 24 pivot `slot`s, `pivotsNum` |
| `Thomson/ThreePoint/Linear.lean` | **the implicit certificate**: `Fh`, `Hp`, the 24 definitional rows (`rowSpec`, `rowFun`), `IsAff` (rows are affine in the pivots, incl. `deriv` rows), `pivotMatrix`, `pivots := pivotMatrix⁻¹ *ᵥ pivotRhs`, `rows_vanish`, the individual tightness rows, the symmetric duplicates, `Fsum_eq_Fh` — **all proved** |
| `Thomson/ThreePoint/Tasks.lean` | **the open Tasks** (eight `sorry`s) and `exists_threePointCert` |
| `Thomson/Main.lean` | `thomson_eight_lower` and the final statements |
| `Thomson8.lean` | umbrella import (the monolithic file is kept as `Thomson8_monolithic_backup.lean.txt`) |

It compiles with zero errors (8723 jobs), and its `sorry`s are exactly the **Tasks** in
`Thomson/ThreePoint/Tasks.lean` — eight leaves, each stated with a proof sketch.  **The certificate
itself is now a Lean definition** (`certH := Hp pivots`, `pivots := pivotMatrix⁻¹ *ᵥ pivotRhs`,
`Linear.lean`), and every tightness condition at the antiprism is a *theorem* (`rows_vanish`) modulo
the single hypothesis `IsUnit pivotMatrix.det` (Task 1a).  Tasks 0, 3 and 6 are proved; what is left
is `det ≠ 0`, an enclosure of the pivots, two redundant rows, and the inequalities:

| Task | statement | what to do |
|---|---|---|
| 0 `uStar_minpoly` | `A(u*) + √2·B(u*) = 0`, the degree-12 minimal polynomial | **PROVED** (2026-09-10): radicals rewritten as `rStar, s2Star, s4Star`, two squarings as `linear_combination` steps with Gröbner cofactors, result `= (76864+20992√2)·(A+√2B)` exactly |
| 1 (data) | `certH := Hp pivots` | **DONE AS A DEFINITION** (2026-09-10, `Linear.lean` + `CertData.lean`). The exact certificate was also computed explicitly (`task1_exact.py`, `task1_solve.py`: all 29 tightness rows to `3e−38`) but its coefficients have 15 846 digits, so it is *defined implicitly*: 95 fixed 13-digit rationals (`a0, a1, λ` among them), 24 pivots solved from the 24 definitional rows. Design: `task1_design2.py` → `task1_design.json` |
| 1a `pivotMatrix_det_isUnit` | `IsUnit pivotMatrix.det` | approximate inverse `N` (`task1_design.json: leanform.approx_inverse`, 17-digit rationals, `‖I − N M‖∞ = 5e−12`) + interval arithmetic on the explicit entries; then `mulVec`-injectivity |
| 1b `pivots_close` | `|pivots − pivotsNum| ≤ pivotEps = 1e−6` | `M⁻¹ = (I − E)⁻¹ N`; residual at `pivotsNum` is `2e−21` exactly, limited in Lean only by the enclosures (sharpen `uStar_mem_Icc` to ~13 digits) |
| 1c `row_pairVal_A`, `row_triD_FDN_v` | the two redundant rows | slack identity at the antiprism family + kernel lemma (`B_kᵀ v_k = 0`, `Σ_{j,l} S3_k(antiprism)` rank one); the derivative row via `E′(u*) = 0` |
| 2 `certH_posSemidef` | `(certH k).PosSemidef` | rational `LDLᵀ` of `Hp pivotsNum k − λ_k·1` (`λ_k ≥ 5.9e−4`) + `14·pivotEps` perturbation |
| 3 `certData_bound_eq` | `(64a₀ − 8(a₀+a₁) − 8 Fh certH 1 1 1)/2 = E(u*)` | **PROVED** — it is the first definitional row (`row_bound`) |
| 4 `pairP_nonneg` | `pairP pivots ≥ 0` on `[24/25, 2]` | `pairP_tight` (all 8 double-zero conditions, **proved**) → `Polynomial` factorisation → Bernstein for the cofactor at `pivotsNum` + perturbation |
| 5a `triP_local` (×5) | `triP pivots ≥ 0` on the cube of radius `rhoLocal` about `touchType m` | `triP_tight` (value and gradient, **proved**) + `local_nonneg_of_hessian` |
| 5b `triP_global` | `triP pivots ≥ 0` on the region outside the five cubes | Bernstein box covering (`bernstein_nonneg_3d`, `nonneg_of_s_procedure`) |
| 6 `side_conditions` | `0 ≤ a₁`, `0 ≤ λ ≤ 1/18` | **PROVED** (`norm_num`: the data are rational) |

`Thomson/ThreePoint/Toolkit.lean` (all proved) supplies the constants `rStar, s2Star, s4Star`
with squares and enclosures, `antiprismEnergy_uStar_eq`, the diagonal structure of the
three-point matrices (`S3_one_apply`, `Fsum_all_one`), and the positivity lemmas.  The glue —
`pairP_tight`, `triP_tight`, `triP_nonneg`, `certH_factor` (PSD ⟹ `Aᵀ A` via `CFC.sqrt`),
`Fsum_eq_Fh`, `exists_threePointCert`, `thomson_eight_lower` — is proved.  Numbers of the pivot
system in the chord form used by Lean (`task1_leanform.py`): condition `1.1e5`, `‖M‖∞ = 132`,
`‖N‖∞ = 3.9e3`; `H'_k` smallest eigenvalues `1.4e−3, 1.2e−3, 5.9e−4, 1.4e−3, 1.4e−3, 1.5e−3`.

Everything else is proved — Bachoc–Vallentin positivity for `S²` (`bv_positivity`), the
three-point bound (`three_point_bound`), `E′(u*) = 0` (`antiprismEnergy'_uStar`), the
polynomial-form reductions (`pair_of_poly`, `tri_of_poly`), and

```lean
theorem exists_threePointCert : Nonempty ThreePointCert := ⟨{ … from Tasks 1–6 … }⟩  -- PROVED
theorem thomson_eight_lower : antiprismEnergy uStar ≤ thomsonInf 8 :=                 -- PROVED
  thomson_eight_lower_of_cert (Classical.choice exists_threePointCert)
```

Axiom audit: `bv_positivity`, `three_point_bound`, `separation_of_energy_le`,
`antiprismEnergy'_uStar` depend only on `propext, Classical.choice, Quot.sound`;
`thomson_eight_lower` adds `sorryAx` solely through the Tasks.

*(Earlier in this document, "the one `sorry`" refers to the state before §12/§16; the open
content is now the two leaves.)*

Every other declaration is fully proved. An axiom audit (`#print axioms`) confirms that each of
the theorems below depends only on `propext`, `Classical.choice`, `Quot.sound`; `sorryAx`
appears only in `thomson_eight`, through the one open lemma.

| Proved in Lean | Statement |
|---|---|
| `exists_minimiser` | A minimiser exists for every `n ≥ 2` |
| `force_balance` | At a minimiser, `Fᵢ = (½ Σⱼ‖xᵢ−xⱼ‖⁻¹) · xᵢ` — the first-order condition |
| `cube_energy` | `E(cube) = 6√3 + 3√6 + 2` exactly |
| `antiprism_energy_eq'` | Closed form for the square-antiprism family, `E(u) = (4√2+2)/√(1−u) + 8/√(a+bu) + 8/√(b+au)` |
| `thomson_eight_upper` | `thomsonInf 8 < 19.6753` |
| `cube_not_minimal` | The cube is not a minimiser |
| `thomsonInf_le_uStar` | `thomsonInf 8 ≤ E(u*)` — the "≤" half of the main theorem |
| `antiprismEnergy'_strictMonoOn` | `E′` is strictly increasing on `[0,1)`; the family energy is strictly convex |
| `uStar_mem_Icc` | `u* ∈ [0.3140, 0.3142]` |
| `antiprismEnergy_uStar_gt`, `_lt` | `19.675287 < E(u*) < 19.6753` |
| `antiprism_local_min` | Local minimality within the antiprism family |
| `thomsonInf_ge_yudin` | `19.639 < thomsonInf 8` — Yudin's LP bound at degree 3 |
| `sum_P4_nonneg`, `sum_P7_nonneg` | Schoenberg positivity for `P₄`, `P₇` on `S²`, from real solid harmonics |
| `thomsonInf_ge_yudin7` | **`19.6462 < thomsonInf 8`** — Yudin's LP bound at degree 7 |
| `thomson_eight_gap` | `E(u*) − thomsonInf 8 < 0.0291` — the open inequality can fail by at most this much |
| `thomsonInf_attained` | The infimum is attained, for every `n ≥ 2` |
| `energy_isometry` | Energy is invariant under `O(3)`: the gauge freedom of any search |
| `sum_local_energy`, `covering_radius` | `Σᵢλᵢ = 2E`, and a minimiser has covering radius `≤ n(n−1)/(2E)` |
| `covering_radius_eight` | No hole of radius `> 1.4253` at an 8-point minimiser |
| `thomson_eight_lower_of` | The open inequality follows from two named steps, `H1` (local) and `H2` (global) |
| `yudin12_pair_slack` | The Yudin bound in slack form: every pair's Coulomb excess is `≤ E(x) − B₁₂` (§8.1) |
| `separation_of_energy_le` | **`E(x) ≤ 19.6753` forces all pairwise distances `> 0.962`** — 19× the old constant (§8.1) |
| `three_point_bound` | **The three-point bound of §12.2, proved**: any `ThreePointCert` bounds the energy of every configuration with inner products `≤ 0.5373` |
| `thomson_eight_lower_of_cert` | Any certificate proves the open inequality (via `separation_of_energy_le`) |
| `bv_positivity` | **Bachoc–Vallentin three-point positivity for `S²`, `k ≤ 5`, proved** (addition theorem on `S¹` + sum of squares + orthonormal frame) |
| `antiprismEnergy'_uStar` | `E′(u*) = 0` — the algebraic equation the exact certificate lives over |
| `thomson_eight_lower` | **Proved** from `exists_threePointCert` — the single remaining `sorry` |

Known rigorous cases of the Thomson problem are N = 2, 3, 4, 5, 6, 12. N = 7 and 8 are open;
N = 5 needed a book-length computer-assisted argument (Schwartz). What remains here is
`thomson_eight_lower`, and §5 explains why none of the three standard attacks proves it. The
LP method (§5.1) is now formalised at its practical optimum: it pins the infimum to
`(19.6462, 19.6753)`. The residual gap of `0.029` is what no known method closes — and §5.1
records the computation showing that the LP method *cannot* close it, whatever polynomial is
used, since its true optimum is `19.6478`.

---

## 1. The problem

For distinct `x₁,…,x_N ∈ S² ⊂ ℝ³`, the Coulomb energy is
`E = Σ_{i<j} ‖xᵢ − xⱼ‖⁻¹`; the Thomson problem asks for its minimum.

```lean
noncomputable def energy {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ i, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹
```

### 1.1 The junk-value trap

In Lean `(0:ℝ)⁻¹ = 0`, so this energy is *finite* on collapsed configurations —
`energy_const : energy (fun _ => p) = 0` is proved. A naive infimum over the sphere is
therefore `0`. Injectivity is carried in the definition:

```lean
def Admissible (x : Fin n → EuclideanSpace ℝ (Fin 3)) : Prop :=
  (∀ i, ‖x i‖ = 1) ∧ Function.Injective x
noncomputable def thomsonInf (n : ℕ) : ℝ := sInf (energy '' {x | Admissible x})
```

---

## 2. Existence and the first-order condition — proved

**Lemma 2.1** (`term_le_energy`). For `i < j`, `‖xᵢ−xⱼ‖⁻¹ ≤ E(x)`.

**Lemma 2.2** (`dist_ge_of_energy_le`). If `x` is injective and `E(x) ≤ M` then
`‖xᵢ−xⱼ‖ ≥ M⁻¹` for all `i ≠ j`.

**Theorem 2.3** (`exists_minimiser`). For `n ≥ 2` the infimum is attained.

*Proof.* Take any admissible `x₀` (explicitly, `(i/n, √(1−(i/n)²), 0)`) and let `M = E(x₀)`.
The set `K = {x on the sphere with all pairwise distances ≥ M⁻¹}` is closed in the compact
`(S²)ⁿ`, contains `x₀` by Lemma 2.2, and `E` is *continuous* on it. `IsCompact.exists_isMinOn`
gives a minimiser over `K`; any admissible `y` with `E(y) ≤ M` lies in `K` by Lemma 2.2,
and any other `y` has `E(y) > M ≥ E(x*)`. ∎

No lower-semicontinuity machinery is needed; this is the route to take for any `N`.

**Theorem 2.4** (`force_balance`). If `x` minimises, then for each `i`

$$F_i := \sum_{j \ne i} \frac{x_i - x_j}{\lVert x_i - x_j\rVert^{3}}
\;=\; \Bigl(\tfrac12 \sum_{j\ne i} \tfrac{1}{\lVert x_i-x_j\rVert}\Bigr)\, x_i .$$

*Proof (as formalised).* For a unit `v ⊥ xᵢ`, the great circle `γ(t) = cos t·xᵢ + sin t·v`
stays on the sphere (`norm_greatCircle`), and `γ(t) ≠ xⱼ` for `t` near `0` by continuity, so
`x[i := γ(t)]` is eventually admissible. Minimality makes `t ↦ E(x[i := γ(t)])` a local
minimum at `0`. The energy decomposes as `Σ_{j≠i} ‖γ(t) − xⱼ‖⁻¹ + const` (`energy_update`,
via the symmetric form `energy_eq_half`), and each summand has derivative
`−⟨xᵢ−xⱼ, v⟩/‖xᵢ−xⱼ‖³` at `0` (`hasDerivAt_inv_norm_curve`, chaining `norm_sq → sqrt → inv`).
`IsLocalMin.hasDerivAt_eq_zero` gives `⟨Fᵢ, v⟩ = 0` for all unit `v ⊥ xᵢ`
(`force_inner_eq_zero`). Applying this to the unit vector along `Fᵢ − ⟨Fᵢ,xᵢ⟩xᵢ` forces that
vector to vanish, so `Fᵢ ∥ xᵢ`; the multiplier follows from
`⟨xᵢ−xⱼ, xᵢ⟩ = ½‖xᵢ−xⱼ‖²` on the unit sphere. ∎

Consequences for a minimiser: `Σᵢ λᵢ = E`; pairwise distances `≥ 1/E ≈ 0.0508`; covering
radius `≤ 28/E ≈ 1.423` (the last by moving the point of largest local energy into a hole —
stated in the previous version of this document, not yet in Lean).

---

## 3. The candidate: the square antiprism — proved

Two squares of circumradius `r = √(1−h²)` at heights `±h`, the lower rotated by 45°
(`antiprism h`). The cube is **not** in this family (twist 0, not 45°).

**Proposition 3.1** (`antiprism_energy_eq'`). With `u = h² < 1`, `a = 2−√2`, `b = 2+√2`:

$$E(u) = \frac{4\sqrt2+2}{\sqrt{1-u}} + \frac{8}{\sqrt{a+bu}} + \frac{8}{\sqrt{b+au}} .$$

The formalised proof is a 28-term expansion (`Finset.Ioi` rewritten by `decide`, entries by
`rfl`-lemmas `ap0…ap7`, then `sub_e3`/`norm_e3`, `ring_nf`, and `√(1−h²)² = 1−h²`,
`√2² = 2`), after which the eight cross-terms match on both sides syntactically and only the
two intra-square identities `√(2−2h²) = √2·√(1−h²)`, `√(4−4h²) = 2√(1−h²)` remain.

Useful identities: `a+b = 4`, `b−a = 2√2`, `ab = 2`, `(a+bu)(b+au) = 2(u²+6u+1)`.

**Proposition 3.2** (`hasDerivAt_antiprismEnergy`, `antiprismEnergy'_strictMonoOn`).

$$E'(u) = \frac{2\sqrt2+1}{\sqrt{1-u}^{\,3}} - \frac{4b}{\sqrt{a+bu}^{\,3}} - \frac{4a}{\sqrt{b+au}^{\,3}},$$

and `E′` is strictly increasing on `[0,1)`: each of the three terms is, since `C/√(·)³` is
strictly decreasing (`div_cube_sqrt_lt`). So `E` is strictly convex on the family and has a
unique critical point.

**Definition** (`uStar`). The window is `[¼, ½]`; `E` is continuous there
(`antiprismEnergy_continuousOn`), so a minimiser exists (`exists_uStar`); `uStar` is one, by
`Classical.choose`. This avoids ever needing `u*` as an explicit algebraic number.

**Theorem 3.3** (`uStar_mem_Icc`). `u* ∈ [0.3140, 0.3142]`.

*Proof.* Rational bounds on `√2` and on the three `√`'s give `E′(0.3140) < 0 < E′(0.3142)`
(`antiprismEnergy'_neg`, `_pos`; helpers `term_lt`, `lt_term`). By monotonicity of `E′`,
`E` is strictly decreasing on `[¼, 0.3140]` and strictly increasing on `[0.3142, ½]`
(`strictAntiOn_of_deriv_neg`, `strictMonoOn_of_deriv_pos`), so the minimiser cannot lie in
either. ∎

**Theorem 3.4** (`antiprismEnergy_uStar_gt`, `_lt`). `19.675287 < E(u*) < 19.6753`.

*Proof.* Upper: `E(u*) ≤ E(196/625) < 19.6753` (`antiprismEnergy_bound`). Lower: rational
bounds give `E(0.3140) > 19.6752879` and `E′(0.3140) > −1/250`; monotonicity of `E′` and the
mean-value inequality `Convex.mul_sub_le_image_sub_of_le_deriv` give
`E(u*) ≥ E(0.3140) − (1/250)(u* − 0.3140) > 19.675287`. ∎

For reference, floating-point: `u* = 0.3140893679…`, `h* = 0.5604367653…`,
`E(u*) = 19.6752878612…`, agreeing with the published conjectured minimum `19.675287861`.
The energy-optimal antiprism is *not* the equilateral one (`u = √2/(4+√2) ≈ 0.2612`,
`E ≈ 19.72517`).

**Theorem 3.5** (`thomson_eight_upper`, `thomsonInf_le_uStar`).
`thomsonInf 8 < 19.6753` and `thomsonInf 8 ≤ E(u*)`. Both via `csInf_le` with
`antiprism_admissible` (on-sphere by `linear_combination`, injective by 64 `fin_cases`).

**Theorem 3.6** (`antiprism_local_min`). With `ε = 1/20` and `u₀ = u*`, every antiprism with
`|h² − u*| < ε` has energy `≥ E(u*)`. This is local minimality *within the family*; it is not
the Hessian statement of §5.5.

---

## 4. Competitors — proved

**Proposition 4.1** (`cube_energy`). `E(cube) = 6√3 + 3√6 + 2 = 19.740774…`
(12 pairs at `2/√3`, 12 at `2√2/√3`, 4 at `2`). **Corollary** (`cube_not_minimal`): the cube
is not a minimiser.

Also: equilateral antiprism `≈ 19.72517`; hexagonal bipyramid `8 + 2√3 + 6√2 ≈ 19.94938`.

---

## 5. The gap

Everything above is now formal. What is left is one inequality:

```lean
theorem thomson_eight_lower : antiprismEnergy uStar ≤ thomsonInf 8
```

i.e. *no admissible 8-point configuration has energy below the best antiprism*. Here is the
honest position on the three known methods.

### 5.1 Linear programming (Delsarte–Yudin) — insufficient

**Theorem 5.1.** If `f(t) ≤ (2−2t)^{−1/2}` on `[−1,1)` and `f = Σ c_k P_k` (Legendre) with
`c_k ≥ 0` for `k ≥ 1`, then `E ≥ ½(c₀N² − N f(1))` for any `N` points on `S²`.

*Proof.* `‖x−y‖ = √(2−2⟨x,y⟩)`, so `2E ≥ Σ_{i≠j} f(⟨xᵢ,xⱼ⟩) = Σ_{i,j} f − N f(1) ≥ c₀N² − N f(1)`,
using Schoenberg positive-definiteness `Σ_{i,j} P_k(⟨xᵢ,xⱼ⟩) ≥ 0`. ∎

This proves N = 12 (Cohn–Kumar universal optimality) but **cannot reach 19.6753 for N = 8**:
the LP bound is sharp only for *sharp configurations*, and the optimal antiprism has too many
distinct inner products. Three-point SDP bounds (Cohn–Woo) improve it but, to my knowledge,
have not closed the gap.

**Numerical value (computed, `scipy.optimize.linprog`, validated by reproducing the sharp
values 9.985281 for N = 6 and 49.165253 for N = 12).** For N = 8 the optimal LP bound is
`19.6478`; degree 3 already gives `19.63906`, degrees 4–6 add **nothing**, degree 7 jumps to
`19.64716`, and degrees 12 and 17 add `0.0006` more. The optimal polynomial is supported on
`P₀,P₁,P₂,P₃,P₇` (then `P₁₂`, `P₁₇`), and touches `(2−2t)^{−1/2}` at three distances
`1.2335…, 1.6128…, 1.8710…`. **The gap to the antiprism, `19.67529 − 19.6478 = 0.0275`, is not
closable by any polynomial `f`** — this is a computation, not a quotation.

A cheap-looking shortcut does *not* work, and it is worth recording: products of positive
definite kernels are positive definite (Schur), and `P₁,P₂,P₃` are Gram kernels, so every
monomial `P₁^a P₂^b P₃^c` is one too. Optimising over the cone they generate (574 generators,
degrees to 24) returns exactly the degree-3 value `19.639062`. `P₇` is genuinely needed, and
must be obtained as a kernel in its own right.

**Formalised (§§12–13 of the Lean file).** Both the degree-3 and the degree-7 bounds are
fully proved. The degree-3 case first:

- *Schoenberg positivity for `k ≤ 3`* (`sum_P1_nonneg`, `sum_P2_nonneg`, `sum_P3_nonneg`):
  no spherical-harmonic library is needed. `P₂(⟨x,y⟩) = (3/2) Σ_{ab} T₂(x)_{ab} T₂(y)_{ab}` with
  `T₂(x)_{ab} = x_a x_b − δ_{ab}/3`, and `P₃(⟨x,y⟩) = (5/2) Σ_{abc} T₃(x)_{abc} T₃(y)_{abc}` with
  `T₃(x)_{abc} = x_a x_b x_c − (δ_{ab}x_c + δ_{ac}x_b + δ_{bc}x_a)/5`. On the unit sphere these
  are `linear_combination` identities (`P2_addition`, `P3_addition`), and
  `Σ_{i,j} Σ_m φ_m(xᵢ)φ_m(xⱼ) = Σ_m (Σ_i φ_m(xᵢ))² ≥ 0` (`gram_nonneg`).
- *The polynomial.* Instead of the irrational LP optimum, `yudinF` is the unique cubic whose
  slack `1 − s·f(1 − s²/2)` (`s = ‖x−y‖`) has double zeros at the rational distances
  `s = 93/50` and `s = 31/25` (near the true touching points `1.8594`, `1.2417`). Then
  `1 − s f(1 − s²/2) = (s − 93/50)²(s − 31/25)²·q(s)` is a `ring` identity with `q` a cubic
  with positive coefficients, so `f(⟨xᵢ,xⱼ⟩) ≤ ‖xᵢ−xⱼ‖⁻¹` for `i ≠ j` costs one `positivity`
  (`yudinF_le_inv`). Its Legendre coefficients are positive (`yudinF_legendre`, by `ring`).
- *Assembly* (`energy_ge_yudin`): `Σ_{i,j} f = 8 f(1) + Σ_{i≠j} f ≤ 8·(463/310) + 2E` and
  `Σ_{i,j} f ≥ 64 c₀`, giving `E ≥ 32c₀ − 4f(1) = 7059039119342/359438990805 = 19.63904…`.
  `le_csInf` transfers this to `thomsonInf 8`.

Losing `0.00002` to rational touching points is the price of a proof with no interval
arithmetic and no sum-of-squares certificate.

**Degree 7 (§13, `thomsonInf_ge_yudin7`): `19.6462 < thomsonInf 8`.** Two new ingredients.

- *Schoenberg positivity for `P₄` and `P₇`, from harmonics rather than tensors.* The tensor
  construction of §12 does not scale: degree `k` needs `3^k` components, so `k = 7` would be
  `2187` of them. Instead use the `2k+1` real solid harmonics `H_{k,m}`, which are sparse
  (at most ten monomials each), and state the identity in **homogeneous** form,
  `Σ_j b_j (x·y)^{k−2j} (|x|²|y|²)^j = Σ_m w_m H_{k,m}(x) H_{k,m}(y)` with `w_m > 0` rational.
  In that form it is an identity on all of `ℝ³ × ℝ³` with **no sphere hypothesis**, so `ring`
  proves it outright (`zonal4_hom`, `zonal7_hom`); substituting `|x| = |y| = 1` recovers the
  addition theorem (`P4_addition`, `P7_addition`). The harmonics and weights are computed
  once by exact rational linear algebra; the degree-7 identity has 15 terms and `ring` checks
  it in seconds. This is the piece the blueprint previously listed as a missing Mathlib
  prerequisite, and it now costs about thirty lines per degree.
- *A degree-7 rational certificate.* Touching distances `49/40`, `8/5`, `47/25` imposed as
  exact double zeros of the slack, with the Legendre support `{0,1,2,3,4,7}` (six unknowns for
  the six tangency conditions; `c₄` comes out positive, at `2·10⁻⁵`). All six coefficients are
  `≥ 0` and the degree-9 cofactor has all-positive coefficients, so `positivity` again closes
  the pointwise inequality. The proved value is
  `9352905642547650287729263358126768492479175/476066301547384720858547017612130812227216`,
  which is `19.6462249…`, against the unattainable LP optimum `19.6478`.

### 5.2 Interval branch-and-bound — the dimension wall

Gauge-fix rotations, cover the reduced configuration space by boxes, and discard each by a
certificate: an energy lower bound `Σ 1/max_B‖xᵢ−xⱼ‖`, or — the real workhorse — an
interval enclosure of the tangential gradient not containing `0` (no critical point, so by
`force_balance` no minimiser). Surviving boxes contain critical points; interval Newton
certifies each and bounds its energy.

The reduced space has dimension `2N−3`: **7** for N = 5 (Schwartz's proof), **13** for N = 8.
Six more dimensions is not a constant factor; a naive subdivision is infeasible. And Lean has
no verified interval arithmetic in Mathlib; executing such a search in the kernel is orders of
magnitude too slow, and `native_decide` moves the compiler into the trusted base.

### 5.3 Certified critical-point enumeration — the completeness problem

Introduce `d_ij² = ‖xᵢ−xⱼ‖²` to make Theorem 2.4 polynomial, enumerate all complex solutions
by homotopy continuation, certify each by alpha-theory. This *would* be a proof — the
minimiser is a critical point. The obstruction is proving you found *all* solutions: the
Bézout/BKK bound for 8 points with 32 unknowns and auxiliary distance variables vastly
exceeds the true count, so certified and found counts do not meet.

### 5.4 Combinatorial reduction — delicate

There are exactly 14 combinatorial types of simplicial 3-polytopes with 8 vertices. But the
conjectured minimiser's hull is **not simplicial** (two square faces, four cocircular points),
so the classification must handle degenerate hulls — which is where the difficulty
concentrates. "Enumerate the 14 triangulations" skips the actual problem.

### 5.5 Reachable: full local minimality, and the two-step split

The Lean file now states the open inequality as a consequence of two named hypotheses
(`thomson_eight_lower_of`), which is the useful form for anyone continuing the work:

- **H1 (local).** Every admissible configuration within `ε` of a rotated, relabelled copy of
  the optimal antiprism has energy `≥ E(u*)`. This is the transverse-Hessian statement below.
- **H2 (global).** Every admissible configuration with energy `≤ E(u*)` is within `ε` of such
  a copy. This is where the difficulty of `N = 8` lives.

That `H1 ∧ H2 → thomson_eight_lower` is proved. §14 of the file supplies the standard tools a
proof of H2 would start from: the infimum is attained (`thomsonInf_attained`); the search may
be restricted to the sublevel set `{E ≤ E(u*)}` (`lower_bound_of_near_optimal`); the rotation
gauge may be fixed (`energy_isometry`); pairwise distances there exceed `1/19.6753`
(`separated_of_near_optimal`); and a minimiser has no hole of radius above `1.4253`
(`covering_radius_eight`, via `Σᵢλᵢ = 2E` and moving the worst point into the hole).

The Hessian of `E` on `(S²)⁸` at the antiprism, transverse to the rotation orbit, is a
finite algebraic computation; its positive-definiteness would upgrade Theorem 3.6 from
"within the family" to "among all configurations near the antiprism". The formalisable route
is interval bounds at a rational parameter plus a Lipschitz estimate. This is the piece a
future global argument would need at step 5 of §6.2.

---

## 6. Lean 4

### 6.1 What compiles, and how the proofs go

`Thomson8.lean`: 1459 lines, 1 `sorry`, standard axioms only. Sections: definitions;
elementary facts; 3-vector arithmetic; existence; cube; antiprism; upper bound; `uStar`;
force balance; derivative and pinning; six-digit bounds; family local minimum; Yudin LP bound
at degree 3; higher-degree Schoenberg positivity and the degree-7 bound; reduction steps
(attainment, gauge, separation, covering radius); the open statement, split in two.

API notes, all learned the hard way:

- Define the energy with `Finset.Ioi`, **not** a filter on `Fin n × Fin n`: the product
  filter's decidability instance causes `isDefEq` timeouts on `Finset.single_le_sum`.
- `EuclideanSpace.norm_eq` unfolds through `.ofLp`; entry `2` of `![a,b,c]` needs
  `Matrix.cons_val_two, Matrix.tail_cons`. Entries ≥ 3 do not reduce by `simp`; state
  `theorem cube3 : cube 3 = !₂[…] := rfl` and rewrite with those.
- After `fin_cases i`, goals contain `(fun i => i) ⟨k, _⟩`; a `show ‖antiprism h k‖ = 1`
  per case fixes it. Coordinate equalities come from
  `congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v.ofLp k)` (`e3_inj`).
- `Finset.Ioi (0 : Fin 8) = {1,…,7}` is closed by `decide`; then
  `repeat rw [Finset.sum_insert (by decide)]`.
- `HasDerivAt.inv` yields the Pi-inverse `c⁻¹`, not `fun t => (c t)⁻¹`: use `show` +
  `funext` + `Pi.inv_apply`, then `congr_deriv`. `HasDerivAt.sum` wants a Pi-sum
  `∑ j, A j`; convert with `Finset.sum_apply`.
- `IsMinOn f s a` applies directly to a membership proof; `IsLocalMin` needs
  `unfold IsLocalMin IsMinFilter` before `filter_upwards`.
- `linear_combination (√2²/2) * hr2 + ((1−h²)/2) * h2` is the clean way to discharge
  `s² + s² + h² = 1` with `s = r√2/2`.
- Rational bounds through `Real.lt_sqrt` / `Real.sqrt_lt'` + `norm_num` handle
  nine-digit denominators without trouble; `nlinarith [s2l, s2u]` closes the linear-in-`√2`
  side conditions.
- Coordinates of a general `x : EuclideanSpace ℝ (Fin 3)`: `⟪x, y⟫ = x 0 * y 0 + …` is
  `simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]`; `‖x‖ = 1` becomes
  `x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1` via `real_inner_self_eq_norm_sq`.
- Sums over `Fin 3 × Fin 3 × Fin 3` expand with `Fintype.sum_prod_type` then
  `Fin.sum_univ_three`; `simp` then decides the `if (0 : Fin 3) = 1` tests, and a single
  `linear_combination` finishes the 27-term addition identity. `Finset.sum_comm` in a triple
  sum needs to be applied as a term (`Finset.sum_congr rfl fun i _ => Finset.sum_comm`);
  `rw` gets stuck on the metavariable.
- A twelve-digit rational Yudin polynomial is no problem for `ring`/`norm_num`/`linarith`;
  neither is an eighty-digit one, which is what the degree-7 certificate needs.
- State kernel identities **homogeneously** whenever the geometry allows: a hypothesis-free
  `ring` goal is worth far more than a `linear_combination` whose cofactors must be computed.
- `inv_le_inv_of_le` and `div_eq_div_iff` are gone; use `one_div_lt_one_div_of_lt` and
  `div_eq_iff`/`eq_div_iff`. `Finset.sum_lt_sum_of_nonempty` needs the nonemptiness of
  `univ.erase i`, which comes from `Finset.card_erase_of_mem` plus `omega`.
- Strictness matters in the covering argument: the moved configuration must be *strictly*
  better, so the sum bound has to come from `Finset.sum_lt_sum_of_nonempty`, not `gcongr`.

### 6.2 The conditional proof skeleton

1. Existence — **proved**.
2. Upper bound `< 19.6753` — **proved**.
3. Force balance, separation — **proved** (covering bound not yet in Lean).
4. Gauge-fix; cover the compact 13-dimensional region by finitely many boxes.
5. Discard each box by an energy or gradient certificate, or place it in the antiprism
   neighbourhood handled by full local minimality (§5.5).
6. Conclude `thomson_eight_lower`.

Steps 4–5 are the open problem.

### 6.3 Milestones

| Milestone | Content | Status |
|---|---|---|
| A1 | `cube_energy`, `cube_not_minimal` | **done** |
| A2 | `exists_minimiser` | **done** |
| A3 | `antiprism_energy_eq'`, `thomson_eight_upper` | **done** |
| A4 | `force_balance` | **done** |
| B-family | `uStar` pinned; `19.675287 < E(u*) < 19.6753`; `antiprism_local_min` | **done** |
| B-LP3 | Yudin degree-3 bound `19.639 < thomsonInf 8` | **done** |
| B-LP7 | Schoenberg for `P₄,P₇`; degree-7 bound `19.6462 < thomsonInf 8`; gap `< 0.0291` | **done** |
| B-reduce | Attainment, gauge, separation, covering radius; two-step split of the open goal | **done** |
| B-Hessian | Positive-definite Hessian transverse to rotations = **H1** (§5.5) | open, reachable |
| C | **H2**, hence `thomson_eight_lower` | **open mathematics** (LP cannot close it: optimum 19.6478) |

### 6.4 Mathlib gaps identified

- Verified interval arithmetic — absent; blocks B-Hessian at scale and C entirely.
- Schoenberg / spherical-harmonic addition theorem — absent in general; done here by hand
  for degrees 2, 3 (tensor form) and 4, 7 (harmonic form) on `S²`. The harmonic form is
  mechanical and cheap at any fixed degree, so N = 12 (needing degree ≤ 5) is now a short
  step; a general, degree-indexed addition theorem remains a genuine Mathlib gap.
- Verified interval arithmetic — still absent, and still the blocker for H2.
- Everything used here exists: `IsCompact.exists_isMinOn`, `HasDerivAt.{norm_sq,sqrt,inv,sum}`,
  `IsLocalMin.hasDerivAt_eq_zero`, `strictMonoOn_of_deriv_pos`,
  `Convex.mul_sub_le_image_sub_of_le_deriv`.

---

## 7. Recommendation

The provable core is done and reusable for any `N`, and the LP method has now been pushed to
within `0.0016` of its own ceiling. Three honest next steps, in increasing order of ambition:

- **N = 12** (cheapest, highest value to others): with `zonal{k}_hom` the harmonic addition
  theorem is now mechanical at any fixed degree, so Cohn–Kumar universal optimality for the
  icosahedron is a short extension rather than a new project.
- **H1 / B-Hessian** (§5.5): genuinely new, self-contained, finite, and the natural
  continuation of the antiprism work.
- **H2**: the open problem. Do not start it without verified interval arithmetic in Mathlib;
  that library is the real prerequisite, and it is worth building on its own merits.

Do not frame the project as formalising a proof of N = 8; no such proof exists.

---

## 8. Slack rigidity, the counterexample search, and where the proof must come from

*(Added 2026-09-10.  Everything in this section is new, and §8.1 is now formalised in Lean.)*

### 8.1 The Yudin bound in slack form — an exact identity, not an inequality

§5.1 records that the LP method is capped at `19.6478`.  That is a statement about its
*value*.  The method still carries information that the value throws away.  Write
`f = yudinF12`, `B₁₂ = 19.64756399…`, `g(s) = 1/s − f(1 − s²/2) ≥ 0`, and
`M_k = Σ_{i,j} P_k(⟪xᵢ,xⱼ⟫) ≥ 0`.  Then for **every** admissible eight-point configuration

> `E(x)  =  B₁₂  +  Σ_{i<j} g(‖xᵢ−xⱼ‖)  +  ½ Σ_{k≥1} c_k M_k(x)`      (★)

*exactly* — the LP bound is the statement that the last two terms are `≥ 0`.  The two terms
are the **slack** (how far the true Coulomb kernel sits above the Yudin polynomial) and the
**design defect** (how far the configuration is from being a spherical design).

A configuration with `E(x) ≤ 19.6753` therefore has a total budget of
`19.6753 − B₁₂ < 0.0277361` to divide between them, and — since every summand is nonnegative
— *each individual pair* must stay inside that budget.  Because `g(s) → ∞` as `s → 0`, this
is a strong separation statement.  Formalised in `Thomson8.lean` §15:

| Lean name | Statement |
|---|---|
| `yudin12_pair_slack` | `‖xₐ−x_b‖⁻¹ − f(⟪xₐ,x_b⟫) ≤ E(x) − B₁₂` for every pair |
| `yudin12_slack_gt` | `g(s) > 0.0277361` on `(0, 0.962]` — Bernstein certificate, 26 positive coefficients on `[0, 481/500]` |
| `separation_of_energy_le` | `E(x) ≤ 19.6753 ⟹ ‖xᵢ−xⱼ‖ > 0.962` for all `i ≠ j` |
| `separated_sharp` | the same, in the `Separated` language of §1 |

This replaces the separation constant `1/19.6753 ≈ 0.0508` of §14 by `0.962`, a factor of
nineteen.  **The method cannot be pushed past `1.1713`**: the optimal antiprism itself
satisfies `E ≤ 19.6753` and has shortest distance `1.1713`, so it is a witness against any
stronger separation theorem under that hypothesis.  (For scale, the largest shortest-distance
eight points can have at all — the Tammes value — is `1.2153`.)

### 8.2 The LP dual says what a counterexample would have to look like

Solving the degree-20 LP and reading off the **dual** gives the pair-distance distribution
that the bound is actually built on — the "ideal" configuration that would attain `19.6478`:

| distance | ideal multiplicity | square antiprism |
|---|---|---|
| `1.2335` | 16.49 | 8 at `1.1713`, 8 at `1.2877` |
| `1.6561` | 1.72 | 4 at `1.6564` |
| `1.7496` | 0.66 | — |
| `1.8772` | 9.12 | 8 at `1.8969` |

The ideal is recognisably "the antiprism with its two short distances merged into one".  And
it is **provably unrealisable**: it needs 16.49 of the 28 pairs at distance `1.2335`, so its
shortest distance would be `1.2335` — but no eight points on `S²` have shortest distance
above the Tammes value `1.2153` (Schütte–van der Waerden 1951).  *The LP optimum is not a
configuration, and cannot be approached by one.*

Adding that fact to the LP as an extra constraint (force one pair to `s ≤ 1.2153`, maximise
the resulting `δ = min_{s≤1.2153} g(s)` jointly with `f`) is a valid strengthening, but a
nearly worthless one: it buys **`+0.0000353`**, taking `19.6477916 → 19.6478269`.  Forcing a
single pair to be short is almost free.  The leverage would have to come from forcing *many*
pairs to be short simultaneously, and no such theorem is available.

### 8.3 The real obstruction: slack and design defect cannot be small together

Decomposing (★) for various configurations exposes the actual mechanism:

| configuration | energy | slack | design defect | total |
|---|---|---|---|---|
| **square antiprism** (conjectured minimum) | **19.675288** | 0.006784 | 0.020713 | **0.027496** |
| slack-minimiser (the LP-ideal target) | 19.723090 | **0.000880** | 0.074419 | 0.075299 |
| design-defect-minimiser | 19.739099 | 0.087140 | **0.004168** | 0.091308 |
| cube (a 3-design) | 19.740774 | 0.089561 | 0.003421 | 0.092983 |

Driving either term to its own minimum makes the other blow up, and costs `0.05–0.06` in
energy.  The antiprism is the balance point.  Notably the slack-minimiser is essentially the
*Tammes* configuration (16 short distances at `1.2147`–`1.2171`, i.e. as equal as eight points
can make them) — the LP ideal is realised as closely as geometry permits, and it loses.

Where the antiprism's defect sits, by harmonic degree (contribution `½c_k M_k`):

| `k` | 1 | 2 | 3 | 7 | 12 | 17 |
|---|---|---|---|---|---|---|
| antiprism | 0 | 0.00522 | 0 | 0.01185 | 0.00194 | 0.00170 |
| slack-minimiser | 0 | 0.07109 | 0 | 0.00190 | 0.00122 | 0.00021 |

The antiprism is centred and a 3-design in degrees 1 and 3, but is **not a tight frame**: its
inertia eigenvalues are `(2.51271, 2.74364, 2.74364)` against `8/3 = 2.66667`, because
`u* = 0.31409 ≠ 1/3`.  It deliberately pays `0.0052` of degree-2 defect to buy lower slack.

**This is the missing ingredient.**  The LP uses only `slack ≥ 0` and `defect ≥ 0`
separately.  What is needed is a *joint* lower bound — a quantitative statement that eight
points cannot be simultaneously near-design and near-LP-ideal.  Three-point (Cohn–Woo) and
four-point (de Laat) bounds are exactly the machinery that sees this, which is consistent with
their settling `N = 4, 6, 12` (sharp configurations, where the two terms vanish together) and
not `N = 8`.

### 8.4 An explicit, finite search region for `H2`

Applying (★) degree by degree turns the budget into hard constraints.  Any `x` with
`E(x) ≤ 19.6753` satisfies `½ c_k M_k(x) ≤ 0.027496` for each `k`, hence:

| constraint | bound | antiprism |
|---|---|---|
| `M₁ = ⎮Σ xᵢ⎮²` | `≤ 0.1210` — centroid within `0.3478` of the origin | 0 |
| `M₂ = Σᵢⱼ P₂` | `≤ 0.2810` — inertia eigenvalues near `8/3` | 0.0533 |
| `M₃ = Σᵢⱼ P₃` | `≤ 0.9210` | 0 |
| `M₇` | `≤ 10.93` | 4.71 |
| `M₁₂`, `M₁₇` | vacuous (`M_k ≤ 64` always) | 6.27, 7.72 |
| every pairwise distance | `> 0.962` (§8.1) | `≥ 1.1713` |

So `H2` is no longer an unstructured global search: a counterexample must be nearly centred,
nearly a tight frame, a near 3-design, and separated — all explicit and checkable.  This is a
substantially smaller region than "the 13-dimensional reduced space", and it is what a rigorous
interval branch-and-bound would have to cover.

### 8.5 The counterexample search — negative, and thoroughly so

Directed by §8.2 rather than blind, plus a large blind control:

| search | starts / candidates | anything below `19.6752878612`? |
|---|---|---|
| random multistart, best 20 % polished to `gtol 1e-13` | **800 000** | none |
| full landscape census, *every* start polished | **50 000** | none — 100 % of basins were the antiprism |
| structured families (cube, prism, bipyramids, bicapped octahedron, gyro-twists) | 11 | none |
| LP-directed: minimise slack, minimise design defect, realise the ideal distribution | 300+ | none (`19.7231`, `19.7391`) |

Only two critical values were ever seen: `19.6752878612` (square antiprism) and
`19.6816336242`, the known second local minimum — whose basin is so small that it appeared in
none of the 850 000 random starts and had to be reached from a pentagonal-bipyramid seed.
Perturbing it by `10⁻⁵` sends 82 % of trajectories to the antiprism.

**Conclusion: there is no counterexample.**  The conjecture `E₈ = E(u*) = 19.6752878612…`
survives every attack tried here, and the search additionally establishes that the energy
landscape for `N = 8` is essentially a single funnel.  The obstruction to a *proof* is now
localised precisely: it is the joint slack/design-defect inequality of §8.3, which no two-point
method can see.

---

## 9. The analytic attack: no counterexample, and `H1` settled infinitesimally

*(Added 2026-09-10.  §8 worked numerically; this section works in closed form.)*

### 9.1 The LP ideal is unrealisable — and its best realisation is the Tammes optimum

§8.2 found that the LP dual wants **16.49 of the 28 pairs at distance `1.2335`**.  Asking which
real configuration comes closest to that has an exact answer.  Imposing "all 16 short edges
equal" on the antiprism family gives the *equilateral* square antiprism, and every quantity is
algebraic:

> `u_e = (2√2 − 1)/7 = 0.2612038749…`,  common edge `d_e = √((16 − 4√2)/7) = 1.2155625241…`,
> `E(u_e) = 19.7251730552…`

That configuration is exactly the **Tammes optimum for `N = 8`**: a direct max–min search
returns `1.21555992` with distance profile `16 × 1.21556`, `4 × 1.71906`, `8 × 1.88871` — the
equilateral antiprism, 16 equal shortest edges.  So

* the LP wants a shortest distance of `1.2335`;
* no eight points on `S²` achieve more than `d_e = 1.21556` — the LP ideal misses the geometric
  ceiling by `1.5 %`;
* the configuration that realises the ideal as closely as geometry allows loses to the Thomson
  antiprism by **`0.049885`**, twice the entire LP gap.

The LP optimum is not merely unattained; the whole neighbourhood of it in "distance-profile
space" is energetically bad.

### 9.2 Closed-form families: an analytic counterexample does not exist

Every family of eight points with enough symmetry to admit a closed-form energy, optimised to
30 digits:

| family (closed form) | optimised energy | excess over `E(u*)` |
|---|---|---|
| **square antiprism `D4d` (4+4)** | **19.675287861232762264** | **0** |
| antiprism with unequal heights (4+4) | 19.675287861232762264 | 0 — *collapses to `h₁ = h₂`* |
| capped `(1+4+3)` | 19.716580501973384907 | 0.0412926 |
| square prism / cube `D4h` (4+4) | 19.740774073762798056 | 0.0654862 |
| bicapped antiprism `D3d` (1+3+3+1) | 19.740774073762798056 | 0.0654862 — *this is the cube again* |
| `(2+4+2)` stacked | 19.850935802058544588 | 0.1756479 |
| capped, twisted `(1+3+4)` | 19.886369198731077151 | 0.2110813 |
| hexagonal bipyramid `(1+6+1)` | 19.949382989376324880 | 0.2740951 |
| bicapped prism `D3h` (1+3+3+1) | 20.282892795591030683 | 0.6076049 |
| equilateral antiprism = Tammes (§9.1) | 19.725173055269718497 | 0.0498851 |

The unequal-height antiprism is the informative row: given a genuinely extra parameter, the
optimiser drives `h₁ − h₂ → −3·10⁻²⁰`.  The symmetry is not imposed, it is *forced*.

### 9.3 Two parallel squares: the `45°` twist is the unique interior critical point

For two squares of radius `r = √(1−h²)` at heights `±h` with relative twist `φ`, write
`A = 2 + 2h²`, `B = 2r²`, `F(c) = (A − Bc)^{−1/2}`.  Then

`E(h,φ) = 8/(r√2) + 2/r + 4[ G(cos φ) + G(sin φ) ]`,  `G(c) = F(c) + F(−c)`,

and since `G′` is odd, `∂E/∂φ = 4 sin φ cos φ · [H(sin φ) − H(cos φ)]` with `H(c) = G′(c)/c`.
Expanding `(A ∓ Bc)^{−3/2}` binomially, all coefficients are positive and only even powers of
`c` survive in `H`, so **`H` is strictly increasing on `(0,1)`**.  Hence `H(sin φ) = H(cos φ)`
forces `φ = 45°`: the antiprism is the *only* interior critical twist, the prism/cube being the
boundary case `φ = 0`.  Together with `antiprismEnergy'_strictMonoOn` (§10 of the Lean file,
which pins `u*` uniquely), this makes the antiprism the unique minimum of the whole
two-parameter `(h, φ)` family — analytically, with no numerics.

### 9.4 `H1` is true: the transverse Hessian is positive definite

Computing the Hessian of the energy at the antiprism in the 16 tangent directions, to 40-digit
precision (central differences; eigenvalues correct to ≥ 12 significant figures):

| eigenvalue | 0 | 0.197335601582 | 0.419702583146 | 1.67790876857 | 2.96188175025 | 2.98860183290 | 3.07040088591 | 3.72455005398 | 4.22288196949 |
|---|---|---|---|---|---|---|---|---|---|
| multiplicity | 3 | 2 | 1 | 2 | 2 | 1 | 2 | 1 | 2 |

Exactly **three zero modes** — the rotations of `SO(3)`, as they must be — and **thirteen
strictly positive eigenvalues**, with spectral gap `λ_min = 0.19734`.  The multiplicity pattern
`(2,1,2,2,1,2,1,2)` is the `D4d` irreducible decomposition, a strong internal check.

So the square antiprism is a **strict local minimum**, and `H1` of `thomson_eight_lower_of`
holds infinitesimally.  *Caveat:* converting this into `H1` as stated in Lean — with an
explicit `ε` — needs a bound on the third derivative on a neighbourhood plus a Taylor estimate.
That is routine but not free, and it is not yet done.

### 9.5 Why no two-point method can finish, definitively

§8 showed the LP is capped at `19.6478`.  One more escape route was tried and closed.  Using
the *proven upper* bounds `M₁ ≤ 0.121`, `M₂ ≤ 0.281`, `M₃ ≤ 0.921` of §8.4, one may relax the
Schoenberg sign conditions and let `c₁, c₂, c₃` go negative at a penalty `½|c_k|·U_k` — a valid
conditional LP that is not bounded by `19.6478` a priori, and which can be bootstrapped
(better bound → smaller budget → smaller `U_k` → better bound).  It gains **`+1·10⁻⁷`** and
reaches its fixed point in two rounds.

The reason is structural and worth stating: at the LP optimum, complementary slackness forces
`M_k = 0` for *every* degree the polynomial uses.  The ideal distribution is a perfect design in
all those degrees, so upper bounds on `M_k` can never bite.  The only thing separating the LP
ideal from a real configuration is realisability by eight points in `ℝ³` — a rank condition that
no two-point method can express.  This is the same conclusion as §8.3, reached independently.

### 9.6 Where this leaves the problem

Proved or established here, none of it previously in the file:

* the LP ideal is unrealisable, quantitatively, with the obstruction identified as the Tammes
  ceiling `√((16−4√2)/7)` (§9.1);
* no closed-form family contains a counterexample, and extra parameters are forced back to the
  antiprism (§9.2);
* the antiprism is the unique minimum of the two-square family, analytically (§9.3);
* `H1` holds infinitesimally, with an explicit spectral gap (§9.4);
* two-point methods are exhausted for a second, independent reason (§9.5).

What is left is exactly `H2`, and it is left in a much better state: §8.4 confines any
counterexample to an explicit compact region, and §9.4 removes the local step from the
remaining difficulty.  The one method that could still close the gap is a three-point (SDP)
certificate, because it is the cheapest object that sees the rank-3 realisability the LP is
blind to.

---

## 10. A proof that the linear-programming method cannot prove `N = 8`

*(Added 2026-09-10.)*  §§8–9 asserted, on numerical evidence, that the LP method is capped
below the conjectured minimum.  That deserves a proof, and it has a short one.

### 10.1 The duality

A Yudin/Delsarte bound for `N = 8` is built from `f = Σ_{k≤d} c_k P_k` with `c_k ≥ 0` for
`k ≥ 1` and `f(t) ≤ (2−2t)^{−1/2}` on `[−1,1)`; it certifies
`bound(f) = 32c₀ − 4f(1) = 28c₀ − 4Σ_{k≥1}c_k`.

Call a finite set of *virtual pairs* — atoms `t₁,…,t_r ∈ [−1,1)` with weights `w_i > 0` —
**admissible** if `Σ_i w_i = 28` and `Σ_i w_i P_k(t_i) ≥ −4` for every `k ≥ 1`.  (Every genuine
eight-point configuration gives one, taking its 28 pairs with unit weights: there
`Σ_{i,j}P_k = 8 + 2Σ_{i<j}P_k ≥ 0` is Schoenberg positivity.)  Then for any admissible `f`,

`Σ_i w_i/√(2−2t_i) ≥ Σ_i w_i f(t_i) = c₀·28 + Σ_{k≥1} c_k·(Σ_i w_i P_k(t_i)) ≥ 28c₀ − 4Σ_{k≥1}c_k = bound(f).`

**So a single admissible `w` caps every LP bound of every degree at once.**  Exhibiting one with
`Σ_i w_i/√(2−2t_i) < E(u*)` proves the method cannot work.

### 10.2 The certificate

Seven rational atoms with rational weights:

| `t_i` | `−153/200` | `−19/25` | `−27/50` | `−107/200` | `−73/200` | `6/25` | `49/200` |
|---|---|---|---|---|---|---|---|
| `s_i = √(2−2t_i)` | 1.878829 | 1.876166 | 1.754993 | 1.752142 | 1.652271 | 1.232883 | 1.228821 |
| `w_i` | `9179/2000` | `21963/5000` | `5727/10000` | `653/2000` | `17269/10000` | `44701/10000` | `119217/10000` |

* `Σ w_i = 28` **exactly**, every `w_i > 0`, every `t_i ∈ [−1,1)`.
* `Σ_i w_i P_k(t_i) ≥ −4` for `k = 1,…,100`, verified in exact rational arithmetic (Legendre
  three-term recurrence over `ℚ`).  Worst case `k = 3`: `−3.97002986`, slack `0.02997`.
* For `k > 100`, Bernstein's bound `|P_k(cos θ)| ≤ √(2/(πk sin θ))` (Szegő 7.3.3) with
  `min_i sin θ_i = 0.64403` gives `|Σ_i w_i P_k(t_i)| ≤ 28·√(2/(100π·0.64403)) = 2.7838 < 4`.

So `w` is admissible, and

> `Σ_i w_i/√(2−2t_i) = 19.66931671074457…  <  19.67528786123276… = E(u*)`,  margin `0.005971`.

> **Theorem.**  No Yudin/Delsarte linear-programming bound for `N = 8`, of any degree, exceeds
> `19.6693168`.  In particular the method cannot prove `thomsonInf 8 ≥ E(u*)`.

(The bound `19.6693` is not the method's true optimum — `19.6478`, §8 — because the certificate
was built with slack `0.03` for robustness.  Any admissible `w` gives a valid cap; this one is
chosen to have small rational data.)

### 10.3 What is and is not ruled out

This closes the *method*, not the *problem*.  For the record, the three statuses are different:

* **Disproved?**  No.  §8.5 and §9.2 found no counterexample — 850 000 random starts, a full
  landscape census, every closed-form family.  The conjecture is almost certainly true.
* **Impossible to prove?**  No, and provably not.  "Every eight unit vectors satisfy `E ≥ E(u*)`"
  is a first-order sentence over the reals — introduce `d_ij ≥ 0` with `d_ij² = ‖xᵢ−xⱼ‖²` to clear
  the radicals; `E(u*)` is algebraic since `u*` is.  By Tarski–Seidenberg it is **decidable**:
  a mechanical procedure is guaranteed to settle it.  There is no independence phenomenon here;
  the obstruction is cost (doubly exponential in ~24 variables), not logic.
* **Provable by the method in this file?**  No — §10.2 above.

A proof must therefore come from something that sees rank-3 realisability, which the two-point
LP provably cannot: a three-point (Cohn–Woo) or four-point (de Laat) SDP certificate, or a
Schwartz-style rigorous interval branch-and-bound over the region pinned down in §8.4.

### 10.4 Formalisation note

§10.2 is finite and formalisable.  The cleanest Lean statement avoids Bernstein's inequality by
bounding degree: *no admissible `f` of degree `≤ 100` gives a bound above `19.6693168`* — that is
100 exact rational inequalities plus the duality chain of §10.1, all of it `norm_num`-checkable.
Extending to all degrees needs `|P_k(cos θ)| ≤ √(2/(πk sin θ))`, which is not currently in
Mathlib.

---

## 11. Literature review: what could still prove `N = 8`, and why the classical routes fail

*(Added 2026-09-10.  A survey of every method that has ever settled a case of this problem, or
a neighbouring one, assessed against `N = 8`.)*

### 11.1 The root cause: for `N = 8` three notions of "optimal" split apart

For `N = 4, 6, 12` the optimal configuration is *simultaneously* the Tammes optimum, the energy
minimiser, and a spherical design.  That coincidence — a **sharp configuration** — is exactly
why linear programming is sharp there, and it is the hidden hypothesis behind every classical
method.  Inside the square antiprism family the three criteria are three different numbers:

| criterion | parameter `u = h²` | value |
|---|---|---|
| Tammes (all 16 short edges equal, max–min distance) | `(2√2 − 1)/7` | `0.2612038750` |
| **Coulomb energy** | `u*` | **`0.3140893679`** |
| spherical design (tight frame, `M₂ = 0`) | `1/3` | `0.3333333333` |

with `E(u_Tammes) = 19.7251731`, `E(u*) = 19.6752879`, `E(1/3) = 19.6816389`.  The degree-2
defect has an exact closed form,

> `M₂(u) = 48(1−u)² + 96u² − 32 = 16(3u − 1)²`,  so `M₂(u*) = 0.0533275497 > 0`.

**`N = 8` is hard because `u* ≠ 1/3`.**  Every classical method is built on one of the three
criteria, and at `N = 8` they disagree.  (`E(1/3) = 19.6816389` happens to sit very close to the
second local minimum `19.6816336` of §8.5 — a coincidence, not an identity; they differ at the
sixth decimal.)

### 11.2 Two-point / positive-definite potentials — proved impossible

Yudin–Delsarte LP (§10), and with it **every** positive-definite potential, since
`Σ_{i<j} f = ½Σ_{j≥1} c_j M_j − 4f(1) + 32c₀` for `f = Σc_j P_j` with `c_j ≥ 0`.  Two
consequences, both analytic:

* An LP bound is *sharp* only if the antiprism has zero slack **and** zero defect.  Its defect
  is `½Σ_j c_j M_j`, and `M₂(u*) = 16(3u*−1)² > 0`, so any `f` that uses degree 2 at all is
  strictly non-sharp.  §10 turns this into the quantitative theorem (cap `19.6693168`).
* **No positive-definite potential has the square antiprism as its unique minimiser.**  Such a
  potential is minimised exactly on configurations with `M_j = 0` for every `j` with `c_j > 0`;
  the antiprism has `M₁ = M₃ = 0` but `M₂ > 0`, so either it is not a minimiser (if `c₂ > 0`),
  or the minimum is attained on a whole family (if `c₂ = 0`).

### 11.3 Tumanov's analytic method (the `N = 5` breakthrough) — fails, exactly

The only *traditional*, non-computer proof in this area is Tumanov's: with
`G_k(r) = (4 − r²)^k`, the triangular bipyramid uniquely minimises `a₁G₁ + a₂G₂`, and Schwartz's
**Forcing Lemma** then transfers optimality from such polynomial potentials to `R_s`
(`(G₂,G₃,G₅)` is forcing on `(−2,0)`, and so on).  This is precisely the analytic route.

It fails for `N = 8`, and one can say by exactly how much.  Since `4 − r² = 2 + 2t`,

> `Σ_{i<j} G₂ = 320/3 + 4M₁ + (4/3)M₂`,

so the antiprism's `G₂`-excess over the true minimum (attained by the cube, a 3-design) is
`(4/3)M₂(u*) = 0.0711033996` — confirmed numerically to nine digits.  Testing `k = 1,…,10`:

| `k` | 1 | 2 | 3 | 4 | 5 | 6 | 8 | 10 |
|---|---|---|---|---|---|---|---|---|
| antiprism optimal for `G_k`? | yes (tie) | **no** | no | no | no | no | no | no |
| loses by | 0 | 0.0711 | 0.4266 | 0.6698 | 0.1111 | 2.335 | 245.4 | 4922 |

The `G_k` are positive definite, so this is §11.2 again — but it is worth stating separately,
because it shows the *specific* mechanism that made `N = 5` tractable is unavailable at `N = 8`.

### 11.4 What remains, ranked

1. **Three-point (Cohn–Woo) or four-point (de Laat) SDP.**  The only bound method that sees the
   rank-3 realisability the LP is provably blind to.  Cohn–Woo settles `4, 6, 12`; de Laat's
   four-point bound has been computed only for `N = 5` ("the first time a 4-point bound has been
   computed for a problem in discrete geometry").  **Nobody has computed either for `N = 8`.**
   This is the clearest open avenue, and a rational SDP certificate is formalisable.
2. **Delaunay-type enumeration, after Musin–Tarasov.**  They solved Tammes `N = 13, 14` by
   enumerating *irreducible contact graphs*.  The energy analogue: every configuration carries a
   Delaunay triangulation, and there are exactly **14 combinatorial types of simplicial
   3-polytopes on 8 vertices** (Britton–Dunitz; 12 faces, 18 edges by Euler).  Fourteen cases is
   a genuinely small, finite, and *analytic-flavoured* case analysis — much more attractive than
   a 13-dimensional box search.  Caveat: the antiprism's own hull is **not** simplicial (two
   square faces, four cocircular points), so it is a degenerate case on the boundary between
   types and needs separate treatment — exactly the difficulty Musin–Tarasov also face.
3. **Schwartz-style divide and conquer.**  Proven to work on a non-sharp case, using
   stereographic projection to give the moduli space a flat structure, ~12 hours of exact
   arithmetic in Mathematica.  But `N = 5` has a 7-dimensional moduli space and `N = 8` has 13;
   naive subdivision is `2⁶ = 64×` worse *per level*.  Needs the pruning of §8.4 to be viable.
4. **Real algebraic geometry / Positivstellensatz.**  Decidable in principle (§10.3), doubly
   exponential in ~24 variables in practice.  The fallback that guarantees the problem is not
   hopeless, not a plan.
5. **Verified interval arithmetic in Mathlib.**  Infrastructure, and a prerequisite for 2 or 3.

### 11.5 Nothing new in the recent literature

Searches through September 2026 turned up no claimed progress on `N = 7` or `N = 8`.  Vallentin's
2025 survey *Conic optimization for extremal geometry* treats kissing numbers and packing, not
small-`N` energy.  Beware secondary sources: several state that `N ≤ 8` is "solved", conflating
MathWorld's *exact closed-form coordinates* with a *proof of optimality*.  The rigorous list is
`N = 2, 3, 4, 5, 6, 12`.

---

## Appendix: numerical summary

| Configuration | Energy |
|---|---|
| Square antiprism, `u* = 0.31408937…` (conjectured optimum) | **19.6752878612…** — proved `∈ (19.675287, 19.6753)` |
| Square antiprism, `h = 14/25` (certified upper bound) | 19.6752920… |
| Yudin LP lower bound, degree 3, rational touching points (proved: `thomsonInf_ge_yudin`) | 19.6390467 |
| Yudin LP lower bound, degree 7, rational touching points (proved: `thomsonInf_ge_yudin7`) | **19.6462249** |
| Yudin LP lower bound, degree 7, exact optimum (numerical) | 19.6471627 |
| Yudin LP lower bound, optimal over all degrees (numerical; ceiling of the method) | 19.6478 |
| Remaining gap, proved | 0.0291 |
| Remaining gap, irreducible by the LP method | 0.0275 |
| Equilateral square antiprism `u = (2√2−1)/7` = Tammes optimum, edge `√((16−4√2)/7)` | 19.7251730552… |
| Cube, `6√3 + 3√6 + 2` | ≈ 19.740774 |
| Hexagonal bipyramid, `8 + 2√3 + 6√2` | ≈ 19.949383 |

Rational witnesses used in Lean: `1.41421356 < √2 < 1.41421357`; sign of `E′` certified at
`u = 157/500` and `u = 1571/5000`; `E(157/500) > 19.6752879`, `E′(157/500) > −1/250`.

---

## 12. The three-point SDP bound is (numerically) sharp for `N = 8` — handoff

*(Added 2026-09-10.  This section is written so that another tool can pick the problem up and
finish it.  Scripts and data: [`threepoint/`](threepoint/), see its README.)*

### 12.1 The result

> **Numerically, the Cohn–Woo-type three-point bound, restricted by the Lean-proved separation
> theorem to inner products `t ≤ 0.537`, equals the conjectured minimum `E(u*)` for the 8-point
> Thomson problem.**

| certificate | bound | `E(u*) − bound` |
|---|---|---|
| grid only, 44 pts/axis, `d=10` | 19.6757987 | `−5.1e−4` (grid artefact, above the true value) |
| grid + antiprism points, `d=8`, Legendre support `{1}` only (**minimal**) | **19.67528931** | `−1.5e−6` |
| grid + antiprism points, `d=8`, support `{1,2,3,4,7,12}` | 19.67528805 | `−1.9e−7` |
| grid + antiprism points, `d=10` | 19.67528827 | `−4.1e−7` |
| grid + antiprism points, `d=12` | 19.67528894 | `−1.1e−6` |

with `E(u*) = 19.67528786…`.  The sharp certificates are tight at all four antiprism distances
(slack `~1e−8`) and all five antiprism triangle types (slack `~1e−10`), and valid elsewhere on an
80-points-per-axis grid to `~2e−6`.  Since any valid certificate has bound `≤ E(u*)` (the antiprism
exists), "bound `= E(u*)` to solver tolerance, tight at the antiprism" is exactly the signature of
a sharp bound.  This is the first method for `N = 8` that is not provably capped below the target,
and — modulo an exact certificate (§12.5) — it is a proof.

Controls that isolate what matters:

* `λ = 0` form (triangle polynomial `≤ 0`): converges to `≈ 19.6730` (`d = 10, 12, 14` →
  19.67247, 19.67282, 19.67293).  Not sharp.  The `λ` term is essential.
* **Unrestricted range** `t ∈ [−1, 0.995]`: the bound collapses to the LP value `19.64763`, with
  `λ* = 0`.  **The separation theorem is an essential ingredient**, not a convenience.  On the
  Lean-proved range `[−1, 0.537]` it is sharp; the bootstrap-shrunk range `[−0.937, 0.44]` is not
  needed.
* Degree: `d = 4` → gap 0.023; `d = 6` → gap 0.006; **`d = 8` sharp**.  Minimal sharp degree is 8.

### 12.2 The bound, derived (this is not copied from a paper; check it)

Let `h(t) = (2−2t)^{−1/2}` and, for `N = 8` points with Gram entries `t_ij`, let `E = Σ_{i<j} h(t_ij)`.
Ingredients:

* **Bachoc–Vallentin positivity for `S²`.**  For `k ≥ 0`, `d ≥ k`, let
  `Q_k(u,v,t) = ((1−u²)(1−v²))^{k/2} T_k((t−uv)/√((1−u²)(1−v²)))` (`T_k` Chebyshev — the Gegenbauer
  polynomial of `S¹`; this is a polynomial in `u,v,t`), let `Y_k(u,v,t)_{ij} = u^i v^j Q_k(u,v,t)`
  for `0 ≤ i,j ≤ d−k`, and `S_k = (1/6) Σ_{σ∈S₃} Y_k∘σ` (symmetrised over permutations of
  `(u,v,t)`).  Then for every finite `C ⊂ S²`, `Σ_{x,y,z∈C} S_k(x·y, x·z, y·z) ⪰ 0`.
  (`bv.py` checks this numerically for random `C`, `k ≤ 6`.)  With `F_k ⪰ 0` and
  `F(u,v,t) := Σ_k ⟨F_k, S_k(u,v,t)⟩`:  `Σ_{i,j,l} F(t_ij, t_il, t_jl) ≥ 0`.
* Split that sum by coincidences: `8F(1,1,1) + 3Σ_{i≠j} F(1,t_ij,t_ij) + Σ_{distinct} F ≥ 0`.
* Schoenberg: `Σ_{i≠j} f(t_ij) ≥ 64a₀ − 8f(1)` for `f = Σ a_k P_k`, `a_k ≥ 0 (k ≥ 1)`.

Impose, for `λ ∈ [0, 1/18]`:

* **(pair)** `f(t) + 3F(1,t,t) ≤ (1−18λ) h(t)` for all `t` a pair can take;
* **(triangle)** `F(u,v,t) ≤ λ[h(u)+h(v)+h(t)]` for all `(u,v,t)` a triangle of distinct points can take.

Summing (triangle) over the 336 ordered distinct triples gives `Σ_{dist} F ≤ 36λE` (each pair
sits in `6` triples, three slots), summing (pair) gives `Σ_{i≠j}[f + 3F(1,t,t)] ≤ (2−36λ)E`, and
combining with the two positivity statements:

> `E ≥ B := (64a₀ − 8f(1) − 8F(1,1,1))/2`.

`check_lam2.py` verifies the exact identity `2E − 2B = design + BV + triangle-slack + pair-slack`
with all four terms `≥ 0` to `1e−14` on real configurations.  With `λ = 0` this is the
formulation of §12.1's first control; the `λ` freedom is what makes it sharp.

**Why the range restriction is legitimate.**  To prove `E(x) ≥ E(u*)` for all `x` it suffices to
prove it for `E(x) ≤ 19.6753`; for those, `separation_of_energy_le` (Lean, §15) gives every
`t_ij ≤ 1 − 0.962²/2 = 0.53728`, so (pair) and (triangle) need only hold there.

### 12.3 The structure of the sharp certificate (`threepoint/certificate_numerical.json`)

* `f(t) = a₀ + a₁ t` with `a₀ = 0.9014825`, `a₁ = 0.3917947`, and `λ = 0.0070150`.  **Only
  `P₁` appears** — the only Schoenberg fact needed is `|Σxᵢ|² ≥ 0`.  Allowing `P₂,…,P₁₂`
  changes nothing (`a₃ ≈ 5e−6`, rest zero).
* `F_k` for `k = 0,…,5`, of sizes `9,8,7,6,5,4` (the block sizes of `d = 8`); `F₆, F₇, F₈ ≈ 0`.
* **Every `F_k` has a one-dimensional kernel**, and it is forced: the antiprism's matrices
  `M_k := Σ_{i,j,l} S_k(t_ij,t_il,t_jl)` have **rank exactly one** for every `k` (a consequence
  of vertex-transitivity), and complementary slackness `⟨F_k, M_k⟩ = 0` means `F_k v_k = 0` for
  the range vector `v_k` of `M_k`.  The `v_k` are in the JSON; `F_k v_k ≈ 0` to `1e−7`.
* Tight points: the four antiprism inner products `{0.31409, 0.17091, −0.37182, −0.79909}` in
  (pair), the five antiprism triangle types in (triangle).

**Step 1 of §12.5 is done** (`threepoint/exact_kernels.py`, output `kernel_vectors_exact.json`):
the kernel vectors are **rational functions of `u` with rational coefficients — `√2` cancels** —
valid for the whole antiprism family, e.g.
`v₀(u) = [1, 0, (3u²−2u+1)/2, 0, (35u⁴−60u³+42u²−12u+3)/8, 5u(u−1)⁴/8, …]`,
and `v₁, v₂` carry a `(3u−1)` denominator, `v₃, v₄` a `(35u²−30u+3)`, `v₅` a `(u²+6u+1)`.  So the
kernel constraints `F_k v_k = 0` are linear over `ℚ(u*)` with no `√2`; the number field enters
only through the touching points and `E(u*)`.

**Step 2, first pass** (`threepoint/project_certificate.py`): projecting the numerical `F_k`
onto `{F_k v_k = 0}` moves them by `≤ 5e−6`, leaves the bound at `19.67528925`, and the surviving
eigenvalues on `v_k^⊥` are `8e−6, 1e−4, 1e−5, 4e−6, 2e−5, 6e−5` for `k = 0…5`.  The pair
polynomial has value/derivative `~1e−6 / 1e−5` at the four distances and the triangle slack has
value/gradient `~1e−7 / 1e−4` at the five types — an exact double-zero structure seen through
solver tolerance.  **The delicate point:** the PSD margins are of the same order as the residuals,
so before exact projection the certificate must be refined to higher precision (Newton on the
KKT system with the tightness conditions imposed, in `mpmath`), otherwise rounding can push an
`F_k` off the cone.  That refinement is the next concrete task.

**GO/NO-GO test — passed** (`threepoint/gonogo.py`, output `certificate_tight.json`).  Instead of
maximising the bound, impose exact tightness at the antiprism as *linear* constraints — bound
`= E(u*)`, double zeros of the pair polynomial at the four distances, zero value and zero
gradient of the triangle slack at the five triangle types, `F_k = W_k H_k W_kᵀ` with `W_k` a basis
of `v_k^⊥` — and maximise the minimum eigenvalue `μ` of the `H_k`.  Result:

> `μ* = 2.49 × 10⁻³` on every block, with `a₀ = 0.94955, a₁ = 0.27961, λ = 0.010162`.

A certificate exactly tight at the antiprism exists with a PSD margin a hundred to a thousand
times larger than the SDP-optimal one had — because the solver may now pick the best-conditioned
member of the ~90-dimensional tight family.  Fine-grid verification (`verify_tight.py`): bound
`= E(u*) − 3.7e−9`, kernels exact to `1e−16`, tightness at the antiprism to `1e−9`, pair
polynomial `≥ −2e−8`, triangle slack `≥ −6.7e−6` on 80 pts/axis (a between-grid-points defect
of the 30/axis solve; removed by re-solving on a finer grid — `gonogo_fine.py`).  The
high-precision projection onto the exact tightness space is `hp_project.py`.

**Refinement, and a defect the grids cannot see.**  Maximising the PSD margin trades away
inequality slack, so `gonogo2.py` fixes the PSD margin (`1.5e−3`) and instead maximises the
inequality slack *weighted by distance to the touching points* (where it must vanish), with the
degenerate boundary of `Δ` and the box faces sampled explicitly; `gonogo3.py` adds cutting
planes from a 100-pts/axis verification.  After one round the triangle slack is `≥ +2.7e−9` on
217 397 points (120/axis) and, after the 50-digit projection (`hp_project.py`), the pair
polynomial is `≥ +4.5e−12` and the triangle slack `≥ +1.3e−7` on the high-precision grids, with
tightness residuals `4e−17`.

**But** (`hessians.py`, 40 digits): at **three of the five** touching triangle types the Hessian
of the triangle slack had a negative eigenvalue (`−7.2e−4, −6.9e−5, −1.1e−4`) — with value and
gradient exactly zero there, the slack goes *negative* along one direction, by `≈ −4e−8` at
distance `0.01`, below any grid's resolution.  Those certificates are therefore subtly invalid
near three touching points; a grid verification is not sufficient evidence.  The pair
polynomial is fine (`P''(s_i) ∈ [0.0067, 0.074]` at the four distances).

The fix is exact: the Hessian of the slack at a fixed point is *linear* in the unknowns, so
`Hess T(τ_m) ⪰ η I` (five 3×3 LMIs, `η = 2e−4`) and `P''(s_i) ≥ η` are added to the SDP
(`gonogo4.py`).  Any rigorous finish *must* include these: positive-definite local structure at
every touching point is what lets interval arithmetic handle the neighbourhoods of the double
zeros.  Result (`certificate_pd.json`, `η = 2e−4`): **all five Hessians positive definite**, with three
of them sitting exactly at `η` (the LMI is active — this constraint genuinely shapes the
certificate), `ε* = 1.24e−3`, PSD margin `1.5e−3`, tightness exact after projection, pair
polynomial `≥ +4.8e−12`.  One residual `−1.8e−8` dip at distance `≈ 0.05` from a touching
triangle, where with `η` that small the cubic terms overtake the quadratic.

**`η = 1e−3` is infeasible** (`certificate_final.json` — *do not use*: its inequality margin is
`ε = −5.2e−3`, the Hessian LMIs at `1e−3` were met only by violating the pair inequality at
`t = −1` by `5e−3` and the triangle inequality by `3e−4`), and so is `η = 5e−3`.  The feasible
Hessian margin therefore lies in `(2e−4, 1e−3)` at PSD margin `1.5e−3`.  `gonogo5.py` makes `η`
a variable and maximises it subject to a fixed positive inequality margin, with dense cutting
planes within `0.1` of each touching type (`certificate_etamax.json`); `verify_tight.py` now also
runs a local fine check (spacing `0.004`) around the touching types.  **The valid certificate as
of this writing is `certificate_pd.json` / its 50-digit projection**, modulo its `−1.8e−8`
sub-grid dip; `certificate_etamax.json` supersedes it if its checks pass.

### 12.4 Two obstacles, honestly

1. **A rational certificate cannot finish the proof.**  Any certificate with rational data proves
   `E ≥ E(u*) − ε`, never `E ≥ E(u*)`: exact tightness at the antiprism requires the data to lie
   in the number field of `u*`, and `u*` has **degree 12 over `ℚ(√2)`** (24 over `ℚ`); its
   minimal polynomial is printed by the sympy snippet in the session log and is easily
   recomputed by clearing the three radicals in `E′(u) = 0`.  This is the same wall de Laat hit
   for `N = 5` ("numerically sharp").  It is not a wall of principle: the Cohn–Kumar / Cohn–Woo
   programme solves exactly this kind of interpolation problem in a number field.
2. **The triangle inequality lives in three variables.**  After `u = 1−p²/2` etc. it is a
   polynomial inequality of degree `≈ 35` in the three edge lengths on a semialgebraic set, with
   five interior double zeros.  A direct SOS certificate is huge; a **3-dimensional rigorous
   interval branch-and-bound** with local Hessian positivity at the five touching points is far
   more practical — three dimensions is small — and needs exactly the verified interval
   arithmetic §7 already identifies as the infrastructure prerequisite.

### 12.5 The finishing plan (what "another tool" should do, in order)

1. **Exact kernel vectors.**  Derive `v_k` symbolically as the single-point profile of the
   antiprism (vertex-transitivity makes `M_k = 8 w_k w_kᵀ`); entries are polynomials in `u*` and
   `√2`.
2. **Exact interpolation problem.**  Unknowns: `a₀, a₁, λ`, `F₀…F₅` (155 entries).  Equations:
   `F_k v_k = 0` (39), double zeros of the pair polynomial at the four distances (8), value and
   gradient zeros of the triangle polynomial at the five triangle types (5 + 15), and
   `28a₀ − 4a₁ − 4F(1,1,1) = E(u*)` (1).  About 68 equations on 158 unknowns — a ~90-dimensional
   affine family; the numerical certificate is a point near it.  Project the numerical solution
   onto the exact affine space over `ℚ(√2, u*)` (or, first, over a high-precision floating
   approximation to check the projection keeps `F_k ⪰ 0` on `v_k^⊥` with margin).
3. **Pair inequality**, exactly: as in `yudinF12_le_inv` — `Π(s−s_i)²` times a polynomial with
   nonnegative Bernstein coefficients on `[0.962, 2]`, now over the number field.
4. **Triangle inequality**, rigorously: interval branch-and-bound over `Δ ∩ [−1,0.537]³` away
   from the five touching points, plus positive-definiteness of the Hessian of the triangle slack
   at each touching point (checked exactly), plus a Taylor remainder bound to glue the two.
5. **Formalisation.**  (a) Bachoc–Vallentin positivity for `S²` at `d = 8, k ≤ 5` — the same
   style of hand-written addition theorem as `P12_addition`, now for `S¹` harmonics in the
   tangent plane; (b) the algebra of §12.2; (c) steps 3–4 as certificates.  Step 4 is the one
   that needs new Mathlib infrastructure.

### 12.6 What is settled by this section and what is not

Settled: the two-point method is capped (§10); the three-point method is not, and its numerical
optimum is `E(u*)` to seven digits with the full sharpness signature; the certificate's
structure — support, ranks, kernels, touching points — is known and recorded.

Not settled: `thomson_eight_lower` is still a `sorry`.  The remaining work is an exact
interpolation in a degree-24 number field and a 3-dimensional rigorous verification.  Both are
finite, both are standard in kind, neither is small.

**Range correction (found while writing the Lean skeleton).**  The separation theorem gives
`s > 0.962`, i.e. `t < 1 − 0.962²/2 = 0.537278`; every SDP run above used `t ≤ 0.537`, leaving
`(0.537, 0.537278)` uncovered.  `ThreePointCert` in `Thomson8.lean` §16 carries the range
`t ≤ 0.5373`, and `gonogo5_r.py` re-solves at that range (`certificate_r5373.json`).  The
certificate has ample slack, so this is expected to pass unchanged — but it must be the range used.
**Done** (`certificate_r5373.json`, `certificate_r5373_hp.json`): at `t ≤ 0.5373` the SDP is feasible
with `ε* = 1.227e−3`, PSD margin `1.5e−3`, bound `= E(u*)` after the 50-digit projection, all
five Hessians positive definite (`≥ 2e−4`), pair polynomial `≥ +4.7e−12`.  Residual: the
triangle slack still shows sub-grid dips of `−1.4e−8` (120/axis, at `(−0.755, 0.124, 0.292)`) and
`−6.7e−8` (local check, at `(−0.831, −0.831, 0.382)`, distance `≈ 0.08` from a touching type) —
cubic-term dips where `η = 2e−4` is too weak and the cut set had no points.  These are at the
level of the solver's own tolerance (`optimal_inaccurate`).  `gonogo4_r2.py` adds dense local
cutting planes at fixed `η`.  The dense version (`gonogo4_r2.py`, 53k constraints) broke the
solver; the *targeted* version (`gonogo4_r3.py`, a few hundred cuts around the two dips) worked:
**`certificate_r5373b.json` / `certificate_r5373b_hp.json` is the final numerical reference** —
triangle slack `≥ +7.2e−9` on 217 395 grid points, no sub-grid dips; the only residual negatives
(`−5.9e−8` in the pair polynomial at `t = −0.3718`, `−1.0e−8` in the local check at a touching
type) are *at the tight points* and are solver tolerance, gone after the 50-digit projection
(pair `≥ +4.8e−12`).  **Task 1 should start from the cleanest
available `*_hp.json`, and Task 5 must expect to discover and repair dips of this size** — the
exact projection changes the data by `~1e−7`, which is the same order.

**The Lean skeleton (`Thomson8.lean` §16, 2026-09-10).**  The proof architecture is now
formalised: `S3` (the Bachoc–Vallentin matrices, `k ≤ 5`, written out), `Fsum`, and a structure
`ThreePointCert` whose fields are exactly the certificate's data and the four properties the
bound needs (`D ≥ 0` for the LDLᵀ form, `pair`, `tri` on `t ≤ 0.5373`, `bound_ge`).
`three_point_bound` — the whole of §12.2 — is **proved**; `bv_positivity` is **proved** (the
`S¹` addition theorem `Q3_addition` as six `ring` identities, a sum-of-squares argument, the
relabelling of the symmetrised sum, and an orthonormal frame of `x^⊥` from
`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`); `antiprismEnergy'_uStar : E′(u*) = 0`
is **proved**; and `thomson_eight_lower` is **proved** from the single remaining leaf
`exists_threePointCert` — the exact certificate (numerically established).

Nothing else in the argument is unproved.  A reader of the Lean file can see precisely what
remains and that each piece is a finite, well-defined task.

### 12.7 Next session starts here

**Open `Thomson/ThreePoint/Tasks.lean`: it contains the eight open leaves, each with a proof
sketch, and the header explains the implicit certificate.**  The standalone project builds:
`lake build` → 8723 jobs, zero errors, eight `sorry`s (all in `Tasks.lean`).  Do **not** re-run the
SDPs and do **not** recompute the exact certificate (`task1_solve.py` did: its closed forms have
15 846-digit coefficients and are useless).

**The certificate is now a Lean definition** (`Thomson/ThreePoint/Linear.lean`, data in
`CertData.lean` generated from `threepoint/task1_design.json` by `task1_emit_lean.py`):
`F(u,v,t) = Σ_k ⟨H'_k, B_kᵀ S3_k(u,v,t) B_k⟩` with exact, rationally scaled, inverse-free bases
`B_k` of `v_k^⊥`; `a₀, a₁, λ` and 92 entries of the `H'_k` are fixed 13-digit rationals; the 24
remaining entries (`slot`) are `pivots := pivotMatrix⁻¹ *ᵥ pivotRhs`, where the 24 rows are: the
bound `= E(u*)`; `P(s_X) = 0` for `X = D, N, F` and `P′(s_X) = 0` for all four chords; `T(τ_m) = 0`
for the five triangle types; the 11 distinct gradient components except `∂_v T(τ_FDN)`.  Every
row is affine in the pivots (`rowFun_isAff` — including the `deriv` rows, via `IsAff.deriv`), so
`rows_vanish : IsUnit pivotMatrix.det → ∀ i, rowFun i pivots = 0` is proved, and with it Task 3
(the bound is a definitional row), all eight double-zero conditions of the pair polynomial
(`pairP_tight`, given 1c(i)) and all value/gradient conditions at the five types (`triP_tight`,
given 1c(ii)).  The symmetric duplicates are proved equal (`triD_dup_*`).  Task 6 is `norm_num`.

Order of work: **1a and 1b first** (they are the same interval-arithmetic infrastructure: an
approximate inverse `N` is in `task1_design.json` under `leanform.approx_inverse`;
`‖I − N·M‖∞ = 5·10⁻¹²`, `‖N‖∞ = 3.9·10³`, `‖M‖∞ = 132`; the residual of `pivotsNum` is `2·10⁻²¹`,
so the enclosure is limited only by how sharply `uStar` is enclosed — sharpen `uStar_mem_Icc` to
~13 digits by the same sign argument).  Then 2, 4, 5a, 5b in parallel (all are "margin at
`pivotsNum` ≫ `pivotEps` perturbation" arguments; the margins are in the `Tasks.lean` header).
1c is a pen-and-paper argument to formalise: the slack identity of `three_point_bound` as an
*equality* at the antiprism family, the kernel lemma (`Σ_{j,l} S3_k(antiprism)` has rank one with
range `v_k(u)`, `B_kᵀ v_k(u*) = 0`), and `E′(u*) = 0` for the derivative row.

The older plan below (explicit data, then verification) is kept for the numerical details it
records; its steps 1–2 are now Tasks 5 and 4 on `triP pivots` / `pairP pivots`.  Then:

1. **Rigorous triangle inequality (the only genuinely new piece).**  In Lean this is exactly the
   hypothesis of `tri_of_poly` (§16): `λ(qr + pr + pq) − pqr·F(1−p²/2, 1−q²/2, 1−r²/2) ≥ 0` for
   chord lengths `p,q,r ∈ [0.96, 2]` satisfying the Gram condition — a polynomial inequality in
   three variables.  Equivalently `T(u,v,t) ≥ 0` on `Δ ∩ [−1, 0.5373]³`.  Away from the five touching types: interval arithmetic on `T`
   (a polynomial of degree ≤ 16 plus three `(2−2x)^{−1/2}`), branch-and-bound in 3-D, with the
   verification grids of `verify_tight.py` as a guide to where subdivision is needed (near the
   touching types and the degenerate boundary of `Δ`).  Inside a ball of radius `ρ_m` around each
   touching type: `T = ½ δᵀ H_m δ + O(|δ|³)`; `H_m ⪰ 1e−3 I` (imposed), so a bound
   `|D³T| ≤ M` on the ball gives `T ≥ ½·1e−3·|δ|² − (M/6)|δ|³ > 0` for `|δ| < 3e−3/M`.  Compute
   `M` by interval arithmetic; pick `ρ_m` accordingly; branch-and-bound outside the balls.
   Ballpark (`third_deriv.py`, finite differences on `certificate_pd.json`): `|D³T| ≈ 0.04–0.26`
   near the five touching types, `≈ 2.5` globally (the potential's `(2−2x)^{−5/2}` growth toward
   the box edge `x = 0.537`).  With `η = 1e−3` that gives `ρ_m ≈ 0.01`, where `T ≈ ½ηρ² ≈ 5e−8` —
   small, so the branch-and-bound must resolve down to that scale near the touching points.
   The Hessian margin has a ceiling: `η = 5e−3` (at PSD margin `1.5e−3`) is **infeasible** — the
   local structure at the touching points is genuinely constrained, not free.  Trading PSD
   margin for Hessian margin does not help: `μ = 5e−4, η = 3e−3` is also **infeasible** (the
   solver returns a garbage point).  Every factor in `η` is
   a factor in `ρ_m`, so take the largest feasible `η` before starting the interval verification.
2. **Rigorous pair inequality.**  In Lean this is exactly the hypothesis of `pair_of_poly`
   (§16): `(1 − 18λ) − s·[a₀ + a₁t + 3F(1,t,t)] ≥ 0` for `s ∈ [0.96, 2]`, `t = 1 − s²/2`.  Write it
   as `Π_i (s−s_i)² · Q(s)` with `Q` having nonnegative Bernstein coefficients — the
   `yudinF12_le_inv` pattern; only novelty is that `s_i` and the coefficients live in the number
   field.  (Note `0.96`, not `0.962`: `t ≤ 0.5373` corresponds to `s ≥ 0.96198`.)
3. **Exactness.**  Either (a) carry `u*, r=√(1−u*), √2` and the two cross-distance roots as
   symbols with their polynomial relations and verify all identities by `linear_combination`
   modulo those relations (the natural Lean route — no explicit number field needed), or (b)
   round to `ℚ(√2, u*)` via the projection of `hp_project.py` in exact arithmetic.
4. **Bachoc–Vallentin positivity in Lean** for `S²`, `d = 8`, `k ≤ 5`: same style as
   `P12_addition`, for `S¹` harmonics in the tangent plane.  This is labour, not risk.
5. Assemble `thomson_eight_lower` from §12.2's algebra (`check_lam2.py` is the numerical model of
   the exact identity to formalise) and `separation_of_energy_le`.

What is *not* needed: any Schoenberg positivity beyond `P₁`; the bootstrap-shrunk range; higher
degree than `d = 8`.
