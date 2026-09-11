import Thomson.ThreePoint.Linear
import Thomson.ThreePoint.MinPoly
import Thomson.ThreePoint.Perturb
import Thomson.ThreePoint.Sharp
import Thomson.Pair.Main
import Thomson.PSD.Main
import Thomson.ThreePoint.Redundant

namespace Thomson
open Finset Matrix
open scoped MatrixOrder

/-! # THE TASKS

Blueprint §12.  The Cohn–Woo-type three-point bound is numerically sharp for `N = 8`: restricted by
the separation theorem of §15 to inner products `t ≤ 0.5373` (chords `s ≥ 0.9619`), its value is
`E(u*)`, with a certificate exactly tight at the antiprism.  This file states what remains to be
proved about that certificate, the *Tasks*, and assembles them into `exists_threePointCert_of`.

## Status

| Task | statement here | status | proof |
|---|---|---|---|
| 1a | `Task1a` (`det ≠ 0`) | **proved** (`native_decide`) | `Task1b` library: `Thomson.Task1b.task1a` |
| 1b | `Task1b` (pivots to `pivotEps = 10⁻¹²`) | **proved**, to `2·10⁻²¹` (`native_decide`) | `Task1b` library: `Thomson.Task1b.task1b` |
| 1c(i) | `row_pairVal_A` | **proved** from 1a (algebra: `ring`) | `Thomson.ThreePoint.Redundant`, `Slack`, `Kernel` |
| 1c(ii) | `row_triD_FDN_v` | **proved** from 1a (algebra + calculus) | `Thomson.ThreePoint.Redundant` |
| 2 | `certH_posSemidef` | **proved** from 1b (`decide +kernel`) | `Thomson/PSD/`, `Thomson.PSD.hp_posSemidef` |
| 3 | `certData_bound_eq` | **proved** (a definitional row) | below |
| 4 | `pairP_nonneg` | **proved** from 1a, 1b, 1c(i) (`decide +kernel`) | `Thomson/Pair/`, `Thomson.Pair.pairP_nonneg_of` |
| 5a | `triP_local : Task5a` | **open** — `sorry` | below |
| 5b | `Task5b` | **proved** from 1b, 5a (`native_decide`) | `Tri5b` library: `Thomson.Tri5b.task5b_of_task5a` |
| 6 | `side_conditions` | **proved** | below |

**The only `sorry` of this file — and of the default build — is Task 5a (`triP_local`).**

The three tasks proved with `native_decide` (1a, 1b, 5b) are kept out of the default build: their
libraries (`lake build Task1b`, about 2 minutes; `lake build Tri5b`, about an hour of CPU) import this
file, and the axioms `native_decide` adds (one per certificate, `…._native.native_decide.ax_…`)
should not leak into everything else.  So here
they are *propositions* (`Task1a`, `Task1b`, `Task5b`), taken as hypotheses by every theorem that
needs them, down to `thomson_eight_lower_of_tasks` (`Thomson.Main`).  The library `Complete`
(`Thomson/Complete.lean`, `lake build Complete`) imports all three proofs and states the main
theorem outright; its only `sorry` is Task 5a.

## The constants (all final)

* chord range `[9619/10000, 2]`: `√(2 − 2·0.5373) = 0.96197…` rounded down (`pair_of_poly`,
  `tri_of_poly`).  An earlier `24/25` made Task 5 false (`Thomson.Tri5b.Domain`);
* `pivotEps = 10⁻¹²` — what Tasks 4 and 5b need; Task 1b gives `2·10⁻²¹`;
* `rhoLocal = 1/500` — the radius of the cubes of Task 5a, as used by the covering of Task 5b.

## The certificate

`Fh`, `Hp`, `pivots`, `certH` (`Thomson.ThreePoint.Linear`, data in `CertData.lean`): the
certificate is the solution of a 24×24 linear system whose rows are tightness conditions at the
antiprism, so every definitional row vanishes by definition once the system is nonsingular
(`rows_vanish`, given Task 1a).

**Why the certificate is implicit.**  A rational certificate proves `E ≥ E(u*) − ε`, never
`E ≥ E(u*)`: exact tightness at the antiprism forces the data into the degree-192 field
`K = ℚ(√2, u*, r, s₂, s₄)`.  The exact solution was computed (`task1_exact.py`, `task1_solve.py`:
all 29 tightness rows to `3·10⁻³⁸`) but its coordinates have 15 000-digit coefficients, so it is
not a usable Lean object.  Instead the 24 pivot unknowns are *defined* as `pivotMatrix⁻¹ *ᵥ pivotRhs`
with `pivotMatrix` built structurally from `S3`, the exact kernel bases `B`, and the chord lengths:
tightness is then by definition, and what remains are *inequalities* (robust, margin `≫ pivotEps`)
plus `det ≠ 0` and an enclosure of the pivots.

**Numbers** (`threepoint/task1_design2.py`; `plans/README.md` §3): `‖pivotMatrix‖∞ ≈ 1.3·10²`,
`‖pivotMatrix⁻¹‖∞ ≈ 3.9·10³`; smallest eigenvalues of `H'_k`: `1.4e−3, 1.2e−3, 5.9e−4, 1.4e−3,
1.4e−3, 1.5e−3`; the exact pivots agree with `pivotsNum` to `4·10⁻²²`; pair polynomial `≥ 0` on
`[9619/10000, 2]` with exact double zeros at the chords; triangle polynomial `≥ 0` on
`Δ ∩ [9619/10000, 2]³` (minimum `+1.5·10⁻⁵` away from the types) with exact second-order zeros at
the five types, Hessians in chord variables `⪰ 6.4·10⁻⁴`.

**Redundancies** (rank 24 of 26 rows).  The bound row is a combination of the nine value rows,
and one combination of all rows vanishes identically (the derivative of the slack identity along
the antiprism family); both follow from the kernel structure of `B` — this is Task 1c. -/

/-- The precision of the pivot enclosure (Task 1b).  Task 2 needs `pivotEps < λ_min/28 ≈ 2·10⁻⁵`;
Tasks 4 and 5b need `10⁻¹²`: just outside a `rhoLocal`-cube `triP` is only `≈ 10⁻⁹`, and near the
chord `F` the interval enclosure of the pair polynomial's second derivative at `10⁻⁶` is as wide
as the second derivative itself. -/
noncomputable def pivotEps : ℝ := 1 / 10 ^ 12

/-! ## Task 1 — the pivot system -/

/-- **Task 1a — the pivot system is nonsingular.**  **Proved** in the `Task1b` library
(`Thomson.Task1b.pivotMatrix_det_isUnit`): with `N` the rational approximate inverse of
`threepoint/task1_design.json` (first column halved, see `Thomson/Task1b/README.md`),
`‖I − N·pivotMatrix‖∞ ≤ 10⁻¹¹ < 1` by interval arithmetic at `10⁻⁴⁰`, so `pivotMatrix` is
injective (`Matrix.mulVec_injective_iff_isUnit`). -/
def Task1a : Prop := IsUnit pivotMatrix.det

/-- **Task 1b — enclosure of the pivots**, to `pivotEps = 10⁻¹²`.  **Proved** in the `Task1b`
library (`Thomson.Task1b.pivots_close_sharp`: `|pivots j − pivotsNum j| ≤ 2·10⁻²¹`), by the same
contraction: `pivots − pivotsNum = pivotMatrix⁻¹ (pivotRhs − pivotMatrix pivotsNum)`, the residual
enclosed with the sharp enclosures of `u*, √2, r, s₂, s₄` (`Thomson.Enclosure`,
`Thomson.ThreePoint.Sharp`). -/
def Task1b : Prop := ∀ j, |pivots j - pivotsNum j| ≤ pivotEps

/-! ### Consequences of Task 1b: the pivots may be replaced by `pivotsNum`

Everything built from the certificate is affine in the pivots (`Thomson.ThreePoint.Linear`), so
Task 1b bounds the error made by evaluating at the rational reference vector `pivotsNum` instead —
by `pivotEps` times an explicit rational ℓ¹-norm (`Thomson.ThreePoint.Perturb`).  Note that they
may be applied only *after* the tangencies have been divided out, since at a touching point the
polynomial itself vanishes and no uniform margin is available. -/

/-- Task 2's perturbation `Δ_k`: entrywise, supported on the slots of block `k`. -/
theorem certH_sub_pivotsNum_le (h1b : Task1b) (k : Fin 6) (a b : Fin (9 - (k : ℕ))) :
    |certH k a b - Hp pivotsNum k a b| ≤ pivotEps * ∑ j, eH j (k : ℕ) (a : ℕ) (b : ℕ) :=
  abs_Hp_sub_apply_le h1b k a b

/-- The pair polynomial's perturbation, at a fixed chord length. -/
theorem pairP_sub_pivotsNum_le (h1b : Task1b) (s : ℝ) :
    |pairP pivots s - pairP pivotsNum s|
      ≤ pivotEps * ∑ j, |pairP (Pi.single j 1) s - pairP 0 s| :=
  pairP_perturb h1b s

/-- The triangle polynomial's perturbation, at a fixed chord triple. -/
theorem triP_sub_pivotsNum_le (h1b : Task1b) (a b c : ℝ) :
    |triP pivots a b c - triP pivotsNum a b c|
      ≤ pivotEps * ∑ j, |triP (Pi.single j 1) a b c - triP 0 a b c| :=
  triP_perturb h1b a b c

/-- **Task 1c(i) — the dropped value row** (pair value at the chord `A = √2·r`).  **Proved**
(`Thomson.ThreePoint.Redundant`).  The slack identity along the antiprism family
(`Thomson.ThreePoint.Slack`, the algebra of `three_point_bound` as an equality): for every `p` and
`u ∈ [0, 1)`,
`2·E(u) − (64a₀ − 8(a₀+a₁) − 8F(1,1,1)) = pairSum p u + triSum p u + bvTerm p u`,
with `bvTerm p u = Σ_k ⟨Hp p k, B_kᵀ Acomb_k(u) B_k⟩`.  **Kernel lemma**
(`Thomson.ThreePoint.Kernel`, generated by `threepoint/kernel_lean.py`):
`(B_kᵀ Acomb_k(u) B_k)[a,b] = (u − u*)²·χ_kab(u)`, 155 polynomial identities in `u, u*` after the
`√2` of `Acomb` has been eliminated (155 more), so `bvTerm p` has a double zero at `u*` for every
`p`.  At `u = u*` the left side vanishes (`row_bound`), and so does every slack but
`16 · pairP pivots (chord 0)/chord 0` (`row_pairVal`, `row_triVal`). -/
theorem row_pairVal_A (h1a : Task1a) : pairP pivots (chord 0) = 0 := row_pairVal_A_of h1a

/-- **Task 1c(ii) — the dropped gradient row** (`v`-derivative at the type `FDN = (s₄, 2r, s₂)`).
**Proved** (`Thomson.ThreePoint.Redundant`): differentiate the slack identity along the family at
`u*`.  The left side has derivative `2·E′(u*) = 0`; the pair slacks and `bvTerm` have double zeros;
each triangle slack has derivative `∇triP(τ_m)·τ_m′/Π`, which vanishes by `row_triD` except for the
single component `∂_v triP(τ_FDN) · (2r)′(u*)`, and `(2√(1−u))′ ≠ 0`. -/
theorem row_triD_FDN_v (h1a : Task1a) : deriv (triD pivots 1 1) 0 = 0 := row_triD_FDN_v_of h1a

/-! ### Consequences: full tightness (from 1a and 1c) -/

/-- The pair polynomial has a double zero at each of the four chord lengths. -/
theorem pairP_tight (h1a : Task1a) (X : Fin 4) :
    pairP pivots (chord X) = 0 ∧ deriv (pairP pivots) (chord X) = 0 := by
  refine ⟨?_, row_pairDer h1a X⟩
  by_cases hX : X = 0
  · subst hX; exact row_pairVal_A h1a
  · exact row_pairVal h1a X hX

/-- The triangle polynomial vanishes to second order at each of the five types. -/
theorem triP_tight (h1a : Task1a) (m : Fin 5) :
    triP pivots (touchType m).1 (touchType m).2.1 (touchType m).2.2 = 0 ∧
      ∀ c : Fin 3, deriv (triD pivots m c) 0 = 0 := by
  refine ⟨row_triVal h1a m, fun c => ?_⟩
  by_cases h : (m, c) = (1, 1)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact row_triD_FDN_v h1a
  · exact row_triD h1a m c h

/-! ## Task 2 — positive semidefiniteness -/

/-- **Task 2 — the blocks are positive semidefinite.**  **Proved** in `Thomson/PSD/`
(`Thomson.PSD.hp_posSemidef`; `decide +kernel` only).  For each block, `Hp p k = L D Lᵀ + N` with
`L`, `D` the rounded `LDLᵀ` factors of `Hp pivotsNum k − μ_k·P` on the `10⁻⁴⁰` grid
(`threepoint/psd_gen.py`): `D ≥ 0`, and `N ≈ μ_k·P` is diagonally dominant for every `p` within
`10⁻¹²` of `pivotsNum` (Task 1b), with slack `≈ λ_min ∈ [5.9·10⁻⁴, 1.5·10⁻³]`. -/
theorem certH_posSemidef (h1b : Task1b) (k : Fin 6) : (certH k).PosSemidef :=
  PSD.hp_posSemidef (fun j => (h1b j).trans (by unfold pivotEps; norm_num)) k

/-- The factorisation `certH k = Aᵀ A` used by the glue (from Task 2 via the matrix square root). -/
theorem certH_factor (h1b : Task1b) (k : Fin 6) :
    ∃ A : Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ, certH k = Aᵀ * A := by
  have h0 : 0 ≤ certH k := (certH_posSemidef h1b k).nonneg
  refine ⟨CFC.sqrt (certH k), ?_⟩
  have hs := CFC.sqrt_mul_sqrt_self (certH k) h0
  have hsa : IsSelfAdjoint (CFC.sqrt (certH k)) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have hT : (CFC.sqrt (certH k))ᵀ = CFC.sqrt (certH k) := by
    have := hsa.star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  rw [hT, hs]

/-! ## Task 3 — the bound (**proved**: it is a definitional row) -/

theorem certData_bound_eq (h1a : Task1a) :
    (64 * a0Fix - 8 * (a0Fix + a1Fix) - 8 * Fh certH 1 1 1) / 2 = antiprismEnergy uStar :=
  row_bound h1a

/-! ## Task 4 — the pair inequality (**proved**, from 1a, 1b, 1c(i)) -/

/-- **Task 4 — the pair inequality on `[9619/10000, 2]`.**  **Proved** in `Thomson/Pair/`
(`Thomson.Pair.pairP_nonneg_of`, on the larger range `[24/25, 2]`; `decide +kernel` only, no
`native_decide`), from the double zeros at the chords (`pairP_tight`, i.e. Tasks 1a and 1c(i)) and
Task 1b.  In `w = 1 − s²/2` it suffices that `Φ(w) = α² − (2 − 2w) R(w)² ≥ 0`, where
`pairP pivots s = α − s R(w)`; `Φ` is a polynomial of degree `33` with double zeros at the four
chords, and eight sweeps integrate an interval lower bound for `Φ''` outwards from them
(`Thomson.Pair.Sweep`). -/
theorem pairP_nonneg (h1a : Task1a) (h1b : Task1b) :
    ∀ s : ℝ, 9619 / 10000 ≤ s → s ≤ 2 → 0 ≤ pairP pivots s := fun s hs1 hs2 =>
  Pair.pairP_nonneg_of (pairP_tight h1a) h1b s (le_trans (by norm_num) hs1) hs2

/-! ## Task 5 — the triangle inequality -/

/-- Radius of the locally controlled cube around each touching type: Task 5a is asked on these
cubes, and the covering of Task 5b is built outside them. -/
noncomputable def rhoLocal : ℝ := 1 / 500

/-- The statement of Task 5a: local positivity on the cube of radius `rhoLocal` about each of the
five touching types. -/
def Task5a : Prop := ∀ m : Fin 5, ∀ a b c : ℝ,
    |a - (touchType m).1| ≤ rhoLocal → |b - (touchType m).2.1| ≤ rhoLocal →
    |c - (touchType m).2.2| ≤ rhoLocal → 0 ≤ triP pivots a b c

/-- **Task 5a — local positivity at a touching type** (five instances).  **Open.**
*Plan*: `plans/T5a-TriLocal.md`.
*Sketch.*  By `triP_tight m`, the expansion of `triP pivots` about `τ_m` has no constant or linear
term: `triP (τ_m + δ) = q_m(δ) + c_m(δ) + (higher)`, `q_m` quadratic, `c_m` cubic (the coefficients
are affine in `pivots`; the Taylor-shift machinery of `Thomson/Tri5b/` computes them as interval
tensors).  Smallest Hessian eigenvalues in chord variables: `3.9e−3, 2.0e−3, 9.3e−4, 6.4e−4, 8.4e−4`
for types `0..4`.
**Caution (numerics, `thompsoneight-fd`, 2026-09-11):** at `rhoLocal = 1/500` the *crude* bound
`λ_min |δ|² ≥ Σ_{|α| ≥ 3} |c_α| |δ|^|α|` fails — it holds only to radius `≈ 5.0e−4, 5.6e−4, 2.7e−4,
5.5e−4, 8.0e−4` — because the tail is `3–8×` the quadratic there.  A *directional* bound works:
with `δ = r·e`, `‖e‖∞ = 1`, `0 < r ≤ ρ`,
`triP (τ_m + r e) ≥ r² [q_m(e) − ρ |c_m(e)| − ρ² T_m(e)]` (`T_m` the absolute quartic-and-higher
tail), and the bracket is `≥ 0.83·q_m(e)` on the whole cube surface for all five types; so cover
the six faces of the cube by 2-D patches with interval enclosures of `q_m` and `c_m`.  (The
radius must stay `1/500`: the covering of Task 5b excludes exactly these cubes.) -/
theorem triP_local (h1a : Task1a) (h1b : Task1b) : Task5a := sorry

/-- **Task 5b — global positivity away from the touching types**, on `[9619/10000, 2]³ ∩ {G ≥ 0}`
outside the five `rhoLocal`-cubes.  **Proved** in the `Tri5b` library
(`Thomson.Tri5b.task5b_of_task5a`, from Task 5a; Task 1b enters through its proof): a covering by
107 × ≈ 900 boxes, each checked by Taylor expansion of the coefficient tensor in fixed-point
interval arithmetic, with the S-procedure on boxes meeting the Gram boundary `G = 0`;
`native_decide`.  See `Thomson/Tri5b/README.md`. -/
def Task5b : Prop :=
  ∀ a b c : ℝ, 9619 / 10000 ≤ a → 9619 / 10000 ≤ b → 9619 / 10000 ≤ c →
    a ≤ 2 → b ≤ 2 → c ≤ 2 →
    0 ≤ 1 + 2 * (1 - a ^ 2 / 2) * (1 - b ^ 2 / 2) * (1 - c ^ 2 / 2)
        - (1 - a ^ 2 / 2) ^ 2 - (1 - b ^ 2 / 2) ^ 2 - (1 - c ^ 2 / 2) ^ 2 →
    (∀ m : Fin 5, rhoLocal < |a - (touchType m).1| ∨ rhoLocal < |b - (touchType m).2.1|
      ∨ rhoLocal < |c - (touchType m).2.2|) →
    0 ≤ triP pivots a b c

/-- **Task 5 — the triangle inequality**, assembled from 5a and 5b.  **Proved** modulo them. -/
theorem triP_nonneg (h5a : Task5a) (h5b : Task5b) :
    ∀ a b c : ℝ, 9619 / 10000 ≤ a → 9619 / 10000 ≤ b → 9619 / 10000 ≤ c →
    a ≤ 2 → b ≤ 2 → c ≤ 2 →
    0 ≤ 1 + 2 * (1 - a ^ 2 / 2) * (1 - b ^ 2 / 2) * (1 - c ^ 2 / 2)
        - (1 - a ^ 2 / 2) ^ 2 - (1 - b ^ 2 / 2) ^ 2 - (1 - c ^ 2 / 2) ^ 2 →
    0 ≤ triP pivots a b c := by
  intro a b c ha1 hb1 hc1 ha2 hb2 hc2 hG
  by_cases hloc : ∃ m : Fin 5, |a - (touchType m).1| ≤ rhoLocal ∧ |b - (touchType m).2.1| ≤ rhoLocal
      ∧ |c - (touchType m).2.2| ≤ rhoLocal
  · obtain ⟨m, h1, h2, h3⟩ := hloc
    exact h5a m a b c h1 h2 h3
  · push Not at hloc
    refine h5b a b c ha1 hb1 hc1 ha2 hb2 hc2 hG fun m => ?_
    by_contra hcon
    push Not at hcon
    exact absurd (hloc m hcon.1 hcon.2.1) (not_lt.mpr hcon.2.2)

/-! ## Task 6 — the side conditions (**proved**: the data are rational) -/

theorem side_conditions : 0 ≤ a1Fix ∧ 0 ≤ lamFix ∧ lamFix ≤ 1 / 18 := by
  norm_num [a1Fix, lamFix]

-- END OF TASKS -----------------------------------------------------------------------------

/-! ## Assembly -/

/-- `Fsum` of the `LDLᵀ` data built from `certH = Aᵀ A` equals `Fh certH`. -/
theorem Fsum_certH (A : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ)
    (hA : ∀ k, certH k = (A k)ᵀ * A k) (u v t : ℝ) :
    Fsum (fun k => A k * (B k)ᵀ) (fun _ _ => 1) u v t = Fh certH u v t := by
  rw [Fsum_eq_Fh]; congr 1; funext k; exact (hA k).symm

/-- **The certificate exists**, assembled from the Tasks.  The hypotheses are the three tasks
proved outside the default build (`Complete.lean` discharges them); the one open task, 5a, enters
through its `sorry`. -/
theorem exists_threePointCert_of_tasks (h1a : Task1a) (h1b : Task1b) (h5b : Task5b) :
    Nonempty ThreePointCert := by
  choose A hA using certH_factor h1b
  have hF := Fsum_certH A hA
  refine ⟨{
    a0 := a0Fix, a1 := a1Fix, lam := lamFix, L := (fun k => A k * (B k)ᵀ), D := (fun _ _ => 1),
    D_nonneg := fun _ _ => zero_le_one,
    a1_nonneg := side_conditions.1,
    lam_nonneg := side_conditions.2.1,
    lam_le := side_conditions.2.2,
    pair := pair_of_poly _ _ _ _ _ fun s h1 h2 => by rw [hF]; exact pairP_nonneg h1a h1b s h1 h2,
    tri := tri_of_poly _ _ _ fun a b c ha1 hb1 hc1 ha2 hb2 hc2 hG => by
      rw [hF]; exact triP_nonneg (triP_local h1a h1b) h5b a b c ha1 hb1 hc1 ha2 hb2 hc2 hG,
    bound_ge := by rw [hF, certData_bound_eq h1a] }⟩

end Thomson
