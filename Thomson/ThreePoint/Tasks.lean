import Thomson.ThreePoint.Linear
import Thomson.ThreePoint.MinPoly

namespace Thomson
open Finset Matrix
open scoped MatrixOrder

/-! # THE OPEN TASKS

Blueprint §12.  The Cohn–Woo-type three-point bound is numerically sharp for `N = 8`: restricted by
the separation theorem of §15 to inner products `t ≤ 0.5373`, its value is `E(u*)` to seven digits,
with a certificate exactly tight at the antiprism.  The architecture of the proof is in place:

* `S3`, `Fsum`, `ThreePointCert`, `bv_positivity`, `three_point_bound` — the bound, **proved**
  (`Thomson.ThreePoint.BV`, `Thomson.ThreePoint.Bound`);
* `Fh`, `Hp`, `pivots`, `certH` — **the certificate**, defined implicitly as the solution of a
  24×24 linear system whose 24 rows are tightness conditions at the antiprism
  (`Thomson.ThreePoint.Linear`; data in `Thomson.ThreePoint.CertData`).  Every definitional row
  vanishes at the certificate (`rows_vanish`) as soon as the system is nonsingular;
* `exists_threePointCert` — **proved** below from the Tasks;
* `thomson_eight_lower` — **proved** from it (`Thomson.Main`).

So the open problem is exactly the `sorry`s of this file, and nothing else.  All of them are
finite, explicit, numerically verified statements (`threepoint/task1_design2.py`,
`threepoint/task1_design.json`).  They are independent of each other except where stated.

**Why the certificate is implicit.**  A rational certificate proves `E ≥ E(u*) − ε`, never
`E ≥ E(u*)`: exact tightness at the antiprism forces the data into the degree-192 field
`K = ℚ(√2, u*, r, s₂, s₄)`.  The exact solution was computed (`task1_exact.py`, `task1_solve.py`:
all 29 tightness rows to `3·10⁻³⁸`) but its coordinates have 15 000-digit coefficients, so it is
not a usable Lean object.  Instead the 24 pivot unknowns are *defined* as `pivotMatrix⁻¹ *ᵥ pivotRhs`
with `pivotMatrix` built structurally from `S3`, the exact kernel bases `B`, and the chord lengths:
tightness is then by definition, and what remains are *inequalities* (robust, margin `≫ 10⁻⁶`)
plus `det ≠ 0` and an enclosure of the pivots.

**Numbers** (`task1_design2.py`, inner-product form of the rows; the chord form used here has the
same solution): pivot block condition `2.2·10⁵`, `‖M‖∞ ≈ 1.3·10²`, `‖M⁻¹‖∞ ≈ 9.4·10³`;
`H'_k` smallest eigenvalues `1.4e−3, 1.2e−3, 5.9e−4, 1.4e−3, 1.4e−3, 1.5e−3`; the exact pivots
agree with `pivotsNum` to `4·10⁻²²`; pair polynomial `≥ 0` on `[24/25, 2]` with exact double zeros
at the chords; triangle slack `≥ 0` on `Δ ∩ [−1, 0.5373]³` with exact second-order zeros at the five
types (Hessians `⪰ 2·10⁻⁴` in inner-product variables).

**Redundancies** (rank 24 of 26 rows).  The bound row is a combination of the nine value rows,
and one combination of all rows vanishes identically (the derivative of the slack identity along
the antiprism family); both follow from the kernel structure of `B` — this is Task 1c. -/

/-- The precision of the pivot enclosure (Task 1b); Task 2 needs `pivotEps < λ_min/28 ≈ 2·10⁻⁵`. -/
noncomputable def pivotEps : ℝ := 1 / 10 ^ 6

/-! ## Task 1 — the pivot system -/

/-- **Task 1a — the pivot system is nonsingular.**
*Sketch.*  Let `N` be the rational 24×24 matrix of `threepoint/task1_design.json` (`approx_inverse`,
the double-precision inverse of the chord-form system).  Show `‖I − N * pivotMatrix‖∞ < 1` by
interval arithmetic: each entry of `pivotMatrix` is `rowFun i (Pi.single j 1) − rowFun i 0`, i.e.
(after `simp [rowFun, rowSpec, evalRow, pairP, triP, triD, Fh, Hp, eH, slot, Hfix, B, Bpoly, S3, Y3,
Q3, Fin.sum_univ_succ]`) an explicit polynomial in `uStar, √2, rStar, s2Star, s4Star` — for the
derivative rows first rewrite `deriv` of the explicit polynomial by `HasDerivAt.deriv` — and the
enclosures `uStar_mem_Icc`, `sqrt2_bounds`, `rStar_bounds`, `s2Star_bounds`, `s4Star_bounds`
(4–8 digits suffice here, the entries are `O(1)`–`O(10²)` and `‖N‖∞ ≈ 10⁴`, so `~10⁻⁵` accuracy per
entry is needed: sharpen the enclosures once as in Task 1b).  Then `pivotMatrix *ᵥ x = 0` gives
`x = (I − N * pivotMatrix) *ᵥ x`, so `‖x‖∞ ≤ ‖I − N M‖∞ ‖x‖∞ < ‖x‖∞` unless `x = 0`; conclude with
`Matrix.mulVec_injective_iff_isUnit` (or `Matrix.exists_mulVec_eq_zero_iff`). -/
theorem pivotMatrix_det_isUnit : IsUnit pivotMatrix.det := sorry

/-- **Task 1b — enclosure of the pivots.**
*Sketch.*  With `N`, `E := I − N * pivotMatrix`, `‖E‖∞ ≤ η < 1` from Task 1a:
`pivots − pivotsNum = pivotMatrix⁻¹ *ᵥ (pivotRhs − pivotMatrix *ᵥ pivotsNum)` and
`‖pivotMatrix⁻¹‖∞ ≤ ‖N‖∞/(1 − η)`.  The residual `pivotRhs − pivotMatrix *ᵥ pivotsNum` is an
explicit expression (the rows evaluated at `pivotsNum`, `rowFun_eq_mulVec`); its true value is
`≈ 10⁻²¹`, so the bound is limited only by the enclosures: `uStar` to `13` digits gives
`‖residual‖∞ ≲ 10⁻¹⁰` and `‖pivots − pivotsNum‖∞ ≲ 10⁻⁶`.  Sharpen `uStar_mem_Icc` by the same
argument as in `Thomson.Derivative` (sign of `antiprismEnergy'` at two 13-digit rationals; the
value `u* = 0.3140893678892018651770997…`), then `rStar`, `s2Star`, `s4Star`, `√2` likewise. -/
theorem pivots_close : ∀ j, |pivots j - pivotsNum j| ≤ pivotEps := sorry

/-- **Task 1c(i) — the dropped value row** (pair value at the chord `A = √2·r`).
*Sketch.*  The slack identity at the antiprism `x(u) := antiprism √u` (blueprint §12.2; it is the
algebra of `three_point_bound` as an equality): for every `p`,
`2·(E(u) − bound(p)) = 2·Σ_X mult_X · pairP p (s_X)/s_X + 6·Σ_m mult_m · triP p τ_m/(Π τ_m)
  + a1Fix·‖Σᵢ xᵢ‖² + Σ_{i,j,l} Fh (Hp p) ⟪xᵢ,xⱼ⟫ ⟪xᵢ,xₗ⟫ ⟪xⱼ,xₗ⟫`,
with multiplicities `A 8, D 4, N 8, F 8` and `FFA 8, FDN 16, FNA 16, DAA 8, NNA 8`.  At `u = u*`:
`Σᵢ xᵢ = 0`; and the last sum is `Σ_k Σ_i g_k(i)ᵀ H'_k g_k(i)` with `g_k(i) = B_kᵀ m_k(i)`, where
`m_k(i)(u) m_k(i)(u)ᵀ ∝ Σ_{j,l} S3 k ⟪xᵢ,xⱼ⟫ ⟪xᵢ,xₗ⟫ ⟪xⱼ,xₗ⟫` has rank one with range `v_k(u)`
(**kernel lemma**: polynomial identities in `u, √2`, `threepoint/exact_kernels.py`,
`kernel_vectors_exact.json`), and `B_kᵀ v_k(u*) = 0` by construction of `B` (`Bpoly`: column
`a` is `c_a(d_i e_i − n_i e_{p₀})`, orthogonal to `v_k = (n_i/d_i)`) — so the last two terms vanish
identically in `p`.  With `row_bound`, `row_pairVal` (`X ≠ 0`) and `row_triVal`, only
`16 · pairP pivots (chord 0)/chord 0` is left.
*Alternative (mechanical):* the identity restricted to the 24 pivot columns and the constant column
is 25 polynomial identities in `K` modulo `rStar_sq, s2Star_sq, s4Star_sq, √2² = 2` only (no
minimal polynomial: it holds for every `u`), each by `linear_combination`. -/
theorem row_pairVal_A : pairP pivots (chord 0) = 0 := sorry

/-- **Task 1c(ii) — the dropped gradient row** (`v`-derivative at the type `FDN = (s₄, 2r, s₂)`).
*Sketch.*  Differentiate the slack identity of 1c(i) along the family at `u*`.  Left side:
`2·E′(u*) = 0` (`antiprismEnergy'_uStar`).  Right side: each pair term
`d/du [pairP(s_X(u))/s_X(u)]` vanishes by `row_pairVal`/`row_pairVal_A` and `row_pairDer`; each
triangle term `d/du [triP(τ_m(u))/Π(u)] = (∇triP(τ_m)·τ_m′)/Π − triP(τ_m)Π′/Π²` vanishes by
`row_triVal` and `row_triD` except the single component `∂_v triP(τ_FDN) · (2r)′(u*)`, with
`(2√(1−u))′ = −1/√(1−u) ≠ 0`; the positivity terms are `≥ 0`, vanish at `u*`, hence have zero
derivative — or directly: `Σ_k Σ_i g_k(i)(u)ᵀ H'_k g_k(i)(u)` is quadratic in `g_k(i)(u)` with
`g_k(i)(u*) = 0`.  Hence `16 · ∂_v triP(τ_FDN) · (−1/r) = 0`. -/
theorem row_triD_FDN_v : deriv (triD pivots 1 1) 0 = 0 := sorry

/-! ### Consequences: full tightness (proved from 1a and 1c) -/

/-- The pair polynomial has a double zero at each of the four chord lengths. -/
theorem pairP_tight (X : Fin 4) :
    pairP pivots (chord X) = 0 ∧ deriv (pairP pivots) (chord X) = 0 := by
  refine ⟨?_, row_pairDer pivotMatrix_det_isUnit X⟩
  by_cases hX : X = 0
  · subst hX; exact row_pairVal_A
  · exact row_pairVal pivotMatrix_det_isUnit X hX

/-- The triangle polynomial vanishes to second order at each of the five types. -/
theorem triP_tight (m : Fin 5) :
    triP pivots (touchType m).1 (touchType m).2.1 (touchType m).2.2 = 0 ∧
      ∀ c : Fin 3, deriv (triD pivots m c) 0 = 0 := by
  refine ⟨row_triVal pivotMatrix_det_isUnit m, fun c => ?_⟩
  by_cases h : (m, c) = (1, 1)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact row_triD_FDN_v
  · exact row_triD pivotMatrix_det_isUnit m c h

/-! ## Task 2 — positive semidefiniteness -/

/-- **Task 2 — the blocks are positive semidefinite.**
*Sketch.*  `certH k = Hp pivots k = Hp pivotsNum k + Δ_k`, where `Δ_k` is supported on the slots of
block `k` with entries `pivots j − pivotsNum j`, `|·| ≤ pivotEps` (Task 1b).  `Hp pivotsNum k` is an
explicit rational symmetric matrix; compute its exact rational `LDLᵀ` after subtracting
`λ_k · 1` with `λ_k` just below its smallest eigenvalue (`λ_k ≥ 5.9·10⁻⁴`, see the header), so that
`x ⬝ᵥ (Hp pivotsNum k *ᵥ x) ≥ λ_k ‖x‖²` is a sum of squares (`nlinarith`/`linear_combination`).
Then `|x ⬝ᵥ (Δ_k *ᵥ x)| ≤ 2·(#slots of `k`)·pivotEps·‖x‖² ≤ 14·pivotEps·‖x‖²`, and
`Matrix.PosSemidef.of_dotProduct_mulVec_nonneg` (Hermitian: `Hp` is symmetric by `Hfix`/`eH`)
finishes since `λ_k > 14·pivotEps`.  The unused last row/column (`a = 8 − k`) is zero. -/
theorem certH_posSemidef (k : Fin 6) : (certH k).PosSemidef := sorry

/-- The factorisation `certH k = Aᵀ A` used by the glue (from Task 2 via the matrix square root). -/
theorem certH_factor (k : Fin 6) :
    ∃ A : Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ, certH k = Aᵀ * A := by
  have h0 : 0 ≤ certH k := (certH_posSemidef k).nonneg
  refine ⟨CFC.sqrt (certH k), ?_⟩
  have hs := CFC.sqrt_mul_sqrt_self (certH k) h0
  have hsa : IsSelfAdjoint (CFC.sqrt (certH k)) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have hT : (CFC.sqrt (certH k))ᵀ = CFC.sqrt (certH k) := by
    have := hsa.star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  rw [hT, hs]

/-! ## Task 3 — the bound (PROVED: it is a definitional row) -/

theorem certData_bound_eq :
    (64 * a0Fix - 8 * (a0Fix + a1Fix) - 8 * Fh certH 1 1 1) / 2 = antiprismEnergy uStar :=
  row_bound pivotMatrix_det_isUnit

/-! ## Task 4 — the pair inequality -/

/-- **Task 4 — the pair inequality on `[24/25, 2]`.**
*Sketch.*  `pairP pivots` is a polynomial in `s` of degree `≤ 43` (by `S3_one_apply`, `F(1,t,t)`
is explicit: `(S3 k 1 t t)ᵢⱼ = (1/3) tⁱ⁺ʲ(1−t²)ᵏ` for `k ≥ 1`, `(1/3)(tⁱ + tʲ + tⁱ⁺ʲ)` for `k = 0`),
with coefficients affine in `pivots`.  Package it as `P : Polynomial ℝ` with `P.eval s = pairP
pivots s`; `pairP_tight` and `Polynomial.deriv` give `P.IsRoot s_X` and `(derivative P).IsRoot s_X`
at the four distinct chords (`√2 r < s₂ < 2r < s₄`, from the `_bounds` lemmas), hence
`(X − C s_X)² ∣ P` (`Polynomial.mul_divByMonic_eq_iff_isRoot` twice, or
`Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative`), hence `P = q² · Q` with
`q = Π (X − C s_X)` and `Q := P /ₘ q²`.  `Q` has coefficients affine in `pivots`; at `pivotsNum`
its Bernstein coefficients on `[24/25, 2]` are positive with a margin (to compute:
`threepoint/`, following `hp_project.py`), and `|Q(pivots) − Q(pivotsNum)| ≤ C·pivotEps`
termwise.  Conclude with `bernstein_nonneg` and `nonneg_of_four_double_zeros`. -/
theorem pairP_nonneg : ∀ s : ℝ, 24 / 25 ≤ s → s ≤ 2 → 0 ≤ pairP pivots s := sorry

/-! ## Task 5 — the triangle inequality -/

/-- Radius of the locally controlled cube around each touching type (a parameter: choose it so that
Task 5a holds with the Hessian margin available; larger `ρ` means fewer boxes in Task 5b). -/
noncomputable def rhoLocal : ℝ := 1 / 500

/-- **Task 5a — local positivity at a touching type** (five instances).
*Sketch.*  By `triP_tight m`, the expansion of `triP pivots` about `τ_m` has no constant or linear
term: `triP (τ_m + δ) = ½ δᵀ H_m δ + Σ_{|α| ≥ 3} c_α δ^α` (an exact polynomial identity in `δ`,
obtained by `ring_nf` after substituting; the coefficients are affine in `pivots`).  Provide
`lamLocal m` with `H_m ⪰ lamLocal m · I` at `pivotsNum` minus the `pivotEps` perturbation
(numerically the Hessians of the slack in inner-product variables are `⪰ 2·10⁻⁴`; in chord variables
`triP = abc · slack`, so `H_m = abc · H_m^{slack}` up to the chain rule — recompute with
`threepoint/hessians.py`), and `MLocal m` bounding `Σ_{|α| ≥ 3} |c_α| ρ^{|α|−3}`; then
`local_nonneg_of_hessian` with `9 · MLocal m · rhoLocal ≤ lamLocal m`. -/
theorem triP_local (m : Fin 5) : ∀ a b c : ℝ,
    |a - (touchType m).1| ≤ rhoLocal → |b - (touchType m).2.1| ≤ rhoLocal →
    |c - (touchType m).2.2| ≤ rhoLocal → 0 ≤ triP pivots a b c := sorry

/-- **Task 5b — global positivity away from the touching types**, by a Bernstein box covering of
`{(a,b,c) ∈ [24/25, 2]³ : G ≥ 0} \ ⋃_m cube(τ_m, rhoLocal)` (`bernstein_nonneg_3d`, with
`nonneg_of_s_procedure` on boxes meeting the Gram boundary `G = 0`).  The box list is generated
externally for `triP pivotsNum` with margin `≫ pivotEps · (sum of |coefficients|)`; one mechanical
lemma per box. -/
theorem triP_global : ∀ a b c : ℝ, 24 / 25 ≤ a → 24 / 25 ≤ b → 24 / 25 ≤ c →
    a ≤ 2 → b ≤ 2 → c ≤ 2 →
    0 ≤ 1 + 2 * (1 - a ^ 2 / 2) * (1 - b ^ 2 / 2) * (1 - c ^ 2 / 2)
        - (1 - a ^ 2 / 2) ^ 2 - (1 - b ^ 2 / 2) ^ 2 - (1 - c ^ 2 / 2) ^ 2 →
    (∀ m : Fin 5, rhoLocal < |a - (touchType m).1| ∨ rhoLocal < |b - (touchType m).2.1|
      ∨ rhoLocal < |c - (touchType m).2.2|) →
    0 ≤ triP pivots a b c := sorry

/-- **Task 5 — the triangle inequality**, assembled from 5a and 5b.  **Proved** modulo them. -/
theorem triP_nonneg : ∀ a b c : ℝ, 24 / 25 ≤ a → 24 / 25 ≤ b → 24 / 25 ≤ c →
    a ≤ 2 → b ≤ 2 → c ≤ 2 →
    0 ≤ 1 + 2 * (1 - a ^ 2 / 2) * (1 - b ^ 2 / 2) * (1 - c ^ 2 / 2)
        - (1 - a ^ 2 / 2) ^ 2 - (1 - b ^ 2 / 2) ^ 2 - (1 - c ^ 2 / 2) ^ 2 →
    0 ≤ triP pivots a b c := by
  intro a b c ha1 hb1 hc1 ha2 hb2 hc2 hG
  by_cases hloc : ∃ m : Fin 5, |a - (touchType m).1| ≤ rhoLocal ∧ |b - (touchType m).2.1| ≤ rhoLocal
      ∧ |c - (touchType m).2.2| ≤ rhoLocal
  · obtain ⟨m, h1, h2, h3⟩ := hloc
    exact triP_local m a b c h1 h2 h3
  · push Not at hloc
    refine triP_global a b c ha1 hb1 hc1 ha2 hb2 hc2 hG fun m => ?_
    by_contra hcon
    push Not at hcon
    exact absurd (hloc m hcon.1 hcon.2.1) (not_lt.mpr hcon.2.2)

/-! ## Task 6 — the side conditions (PROVED: the data are rational) -/

theorem side_conditions : 0 ≤ a1Fix ∧ 0 ≤ lamFix ∧ lamFix ≤ 1 / 18 := by
  norm_num [a1Fix, lamFix]

-- END OF TASKS -----------------------------------------------------------------------------

/-! ## Assembly -/

/-- `Fsum` of the `LDLᵀ` data built from `certH = Aᵀ A` equals `Fh certH`. -/
theorem Fsum_certH (A : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ)
    (hA : ∀ k, certH k = (A k)ᵀ * A k) (u v t : ℝ) :
    Fsum (fun k => A k * (B k)ᵀ) (fun _ _ => 1) u v t = Fh certH u v t := by
  rw [Fsum_eq_Fh]; congr 1; funext k; exact (hA k).symm

/-- **The certificate exists**, assembled from the Tasks.  **Proved** modulo them. -/
theorem exists_threePointCert : Nonempty ThreePointCert := by
  choose A hA using certH_factor
  have hF := Fsum_certH A hA
  refine ⟨{
    a0 := a0Fix, a1 := a1Fix, lam := lamFix, L := (fun k => A k * (B k)ᵀ), D := (fun _ _ => 1),
    D_nonneg := fun _ _ => zero_le_one,
    a1_nonneg := side_conditions.1,
    lam_nonneg := side_conditions.2.1,
    lam_le := side_conditions.2.2,
    pair := pair_of_poly _ _ _ _ _ fun s h1 h2 => by rw [hF]; exact pairP_nonneg s h1 h2,
    tri := tri_of_poly _ _ _ fun a b c ha1 hb1 hc1 ha2 hb2 hc2 hG => by
      rw [hF]; exact triP_nonneg a b c ha1 hb1 hc1 ha2 hb2 hc2 hG,
    bound_ge := by rw [hF, certData_bound_eq] }⟩

end Thomson
