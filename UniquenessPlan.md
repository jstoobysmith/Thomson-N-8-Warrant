# Uniqueness of the minimiser — the plan

*Written 2026-09-11, against the code as it stands (`Thomson/ThreePoint/Tasks.lean`,
`Thomson/Pair/`, `Thomson/Tri5b/`, `Thomson/Main.lean`, `Thomson/Complete.lean`) and blueprint §12.
Numbers were checked with `plans/survey.py`'s evaluator and `plans/unique_enum.py`.*

## 0. What is being proved, and the one idea

What the repository will have shortly (Task 5a is the last `sorry`):

```lean
theorem thomson_eight : thomsonInf 8 = antiprismEnergy uStar
```

What it will not have: that the square antiprism is the *only* configuration with that energy.
The target of this plan is

```lean
/-- Every admissible configuration with the minimal energy is a rotated, relabelled copy of the
optimal square antiprism. -/
theorem thomson_eight_unique (x : Fin 8 → EuclideanSpace ℝ (Fin 3)) (hx : Admissible x)
    (hE : energy x = thomsonInf 8) :
    ∃ (f : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (σ : Equiv.Perm (Fin 8)),
      ∀ i, x i = f (antiprism (Real.sqrt uStar) (σ i))
```

(the same shape as `NearAntiprism` in `Thomson/Reduction.lean`, with `ε = 0`), and its
`_of_tasks` version in the default build, taking `Task1a`, `Task1b`, `Task5b` as hypotheses exactly
as `thomson_eight_lower_of_tasks` does.

**The idea.**  `three_point_bound` is proved by summing inequalities, and the certificate is tight
*only* at the antiprism: the pair polynomial `pairP pivots` vanishes on `[0.9619, 2]` exactly at the
four chords `A, D, N, F`, and the triangle polynomial `triP pivots` vanishes on the admissible
region exactly at the five triangle types `FFA, FDN, FNA, DAA, NNA`.  So at a configuration with
`energy x = E(u*)` every slack term of the bound is zero, hence

* every one of the 28 distances is one of the four chords, and
* every one of the 56 triangles is one of the five types.

That is a finite combinatorial constraint on an edge colouring of `K₈` by four colours.  It has
exactly two solutions up to relabelling (`plans/unique_enum.py`): the antiprism, and an "aligned"
pattern that no eight points of `ℝ³` realise (one `4×4` Gram determinant is nonzero).  Two
configurations with the same Gram matrix differ by an orthogonal map, which is the theorem.

Nothing new is needed on the analytic side: **no new certificate, no new SDP run, no new interval
infrastructure, no strict version of Task 5a**, and neither the Bachoc–Vallentin term nor the design
term of the identity is used.  The two places where the existing proofs give `≥ 0` and uniqueness
needs `> 0` are cheap: the Task 5b covering already certifies a margin of `10⁻¹⁰` and only needs
that margin *exported*; the Task 4 sweep checker needs three `≤` turned into `<` and the same eight
certificates re-checked.

## 1. What is already there (and is reused unchanged)

| fact | where | used for |
|---|---|---|
| `three_point_bound` and its proof structure (`hBV`, `hpair`, `htri`, `ha1T`) | `ThreePoint/Bound.lean` | U1 restates it as an *identity* |
| `Fsum_certH`, `exists_threePointCert_of_tasks` | `ThreePoint/Tasks.lean` | U2: the concrete certificate |
| `pairP_div`, `triP_div` (slack ↔ `pairP/s`, `triP/abc`) | `ThreePoint/Slack.lean` | U2 |
| `certData_bound_eq` (bound `= E(u*)`) | `Tasks.lean` | U2 |
| `separation_of_energy_le` (all `t ≤ 0.5373` when `E ≤ 19.6753`) | `Separation.lean`, used in `Main.lean` | U2 |
| `pairP_tight`, the eight sweeps, `alpha_pos`, `pairP_nonneg_of_Phi` | `Pair/` | U3: strict version |
| the covering with margin `MG = 10⁻¹⁰`: `Goal`, `NumCertU`, `numCertU_of_covers`, `triSorted_of_numCertU` | `Tri5b/Cover.lean`, `Main.lean`, `Skip.lean` | U4: export the margin |
| `triP_swap12`, `triP_swap23`, `Tri5b.of_sorted` | `Linear.lean`, `Tri5b/Symmetry.lean` | U4: sorting |
| `chord`, `touchType`, `chord_inner_*`, `rStar_bounds`, `s2Star_bounds`, `s4Star_bounds` | `Linear.lean`, `Sharp.lean`, `Toolkit.lean` | U4, U6 |
| `tA, tD, tN, tF` (antiprism inner products as functions of `u`) | `Slack.lean` | U6 |
| `gram_det_nonneg`, `inner_eq_of_norm`, `energy_isometry` | `Bound.lean`, `Basic.lean`, `Reduction.lean` | U2, U6 |
| Mathlib: `Matrix.gram`, `det_gram_ne_zero_iff_linearIndependent`, `LinearIndependent.fintype_card_le_finrank`, `LinearMap.quotKerEquivRange`, `LinearIsometry.extend`, `LinearIsometry.toLinearIsometryEquiv`, `Tuple.sort` | — | U5, U6 |

## 2. Numbers everyone should know (at `pivotsNum`; `plans/survey.py` reproduces them)

| quantity | value |
|---|---|
| chords `A, D, N, F` | `1.17125, 1.65639, 1.28769, 1.89689`; smallest gap `0.1164` (`≫ rhoLocal = 1/500`) |
| inner products `tA, tD, tN, tF` | `0.31409, −0.37182, 0.17092, −0.79910` |
| `triP` at the 20 sorted chord triples | the 5 types: `0` (to `10⁻¹⁵`); the 11 other realisable triples (`FDA, FNN, FAA, DDD, DDN, DDA, DNN, DNA, NNN, NAA, AAA`): slack `triP/abc ≥ 6.6·10⁻⁶`; `FFF, FFD, FFN, FDD`: Gram determinant `< 0`, not realisable |
| Task 5b margin on the slack, outside the five cubes | `10⁻¹⁰` (`Tri5b/Params.lean`, `MG`) — `6·10⁴` times smaller than needed |
| `pairP` between the chords | `≥ 4·10⁻⁶` near `1.23` (between `A` and `N`), `≥ 3·10⁻⁵` elsewhere; `Φ''` at the chords `≈ 10⁻²` |
| the aligned `4×4` Gram determinant `(1 − tA)²((1 + tA)² − 4 tN²)` | `0.7574` |
| admissible colourings of `K₈` | `5040 = 2520 + 2520` (antiprism relabellings + aligned); with vertex 0's edges sorted: `8 = 4 + 4`, search tree `1878` nodes |
| vertex degree pattern `(A, D, N, F)` in every admissible colouring | `(2, 1, 2, 2)` — forced |

## 3. The steps

Critical path: **U3 and U4 first** (they are the only edits to existing proofs and the only
re-checks), then U1–U2, U5, U6 in parallel; U7 assembles.  All new code goes in `Thomson/Unique/`
(add `"Thomson.Unique.+"` to the main library's `globs` in `lakefile.toml`); everything is
`decide +kernel` or plain proofs — no new `native_decide` library.

### U1 — the three-point bound as an identity (`Thomson/Unique/Identity.lean`)

Restate the algebra of `three_point_bound` as an exact identity with four nonnegative terms.

```lean
/-- The pair slack of a certificate at the pair `(i, j)`. -/
noncomputable def pairSlack (C : ThreePointCert) (x : Fin 8 → EuclideanSpace ℝ (Fin 3)) (i j : Fin 8) : ℝ :=
  (1 - 18 * C.lam) * ‖x i - x j‖⁻¹ - C.a0 - C.a1 * ⟪x i, x j⟫
    - 3 * Fsum C.L C.D 1 ⟪x i, x j⟫ ⟪x i, x j⟫

/-- The triangle slack at the ordered triple `(i, j, l)`. -/
noncomputable def triSlack (C : ThreePointCert) (x) (i j l : Fin 8) : ℝ :=
  C.lam * (‖x i - x j‖⁻¹ + ‖x i - x l‖⁻¹ + ‖x j - x l‖⁻¹)
    - Fsum C.L C.D ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫

/-- **The three-point identity** (blueprint §12.2, `check_lam2.py`'s
`2E − 2B = BV + pair-slack + triangle-slack + design`). -/
theorem three_point_identity (C : ThreePointCert) (x) (hx : Admissible x) :
    2 * energy x - (64 * C.a0 - 8 * (C.a0 + C.a1) - 8 * Fsum C.L C.D 1 1 1)
      = (∑ i, ∑ j, ∑ l, Fsum C.L C.D ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫)
        + ∑ i, ∑ j ∈ univ.erase i, pairSlack C x i j
        + ∑ i, ∑ j ∈ univ.erase i, ∑ l ∈ (univ.erase i).erase j, triSlack C x i j l
        + C.a1 * ∑ i, ∑ j, ⟪x i, x j⟫

/-- **Equality forces every slack to vanish.** -/
theorem three_point_tight (C : ThreePointCert) (x) (hx : Admissible x)
    (hsep : ∀ i j, i ≠ j → ⟪x i, x j⟫ ≤ 5373 / 10000)
    (hE : energy x = (64 * C.a0 - 8 * (C.a0 + C.a1) - 8 * Fsum C.L C.D 1 1 1) / 2) :
    (∀ i j, i ≠ j → pairSlack C x i j = 0) ∧
    (∀ i j l, i ≠ j → i ≠ l → j ≠ l → triSlack C x i j l = 0)
```

*Proof.*  The identity is the existing proof with `≤` replaced by `=`: `sum_triple_split`,
`hdiag`, `hdist'`, `hmid'`, `energy_eq_half`, and `Fsum_swap12/23` to identify the three
two-equal terms with `3·F(1, t, t)` (the `e1`, `e2` of `hpair`).  It is a `linarith` over the same
equalities.  For `three_point_tight`: the four terms are `≥ 0` (`bv_positivity` through
`D_nonneg`, `C.pair` at each pair via `hsqrt`, `C.tri` at each triple via `gram_det_nonneg`,
`sum_P1_nonneg` with `a1_nonneg`); their sum is `0`, so each is `0`, and
`Finset.sum_eq_zero_iff_of_nonneg` (twice, then three times) gives every summand.  About 150 lines,
most of them copied.  Keep `three_point_bound` as it is (or derive it from the identity — optional).

### U2 — the concrete certificate and the chord/triangle conclusions (`Thomson/Unique/Tight.lean`)

Turn `exists_threePointCert_of_tasks` into a definition and record what its `Fsum` is:

```lean
noncomputable def theCert (h1a : Task1a) (h1b : Task1b) (h5b : Task5b) : ThreePointCert := { … }
  -- the same record as in `exists_threePointCert_of_tasks`, with `A := Classical.choose (certH_factor h1b k)`
theorem theCert_Fsum (h1a h1b h5b) : Fsum (theCert h1a h1b h5b).L (theCert h1a h1b h5b).D = Fh certH
theorem theCert_bound (h1a h1b h5b) :
    (64 * a0Fix - 8 * (a0Fix + a1Fix) - 8 * Fsum (theCert …).L (theCert …).D 1 1 1) / 2 = antiprismEnergy uStar
  -- `theCert_Fsum` + `certData_bound_eq`
```

Then, for `x` with `energy x = antiprismEnergy uStar`: `energy x ≤ 19.6753`
(`antiprismEnergy_uStar_lt`), so `hsep` from `separation_of_energy_le` exactly as in
`thomson_eight_lower_of_cert`, and `three_point_tight` applies.  Convert with `pairP_div`,
`triP_div` (`s = ‖x i − x j‖ > 0`, `t = 1 − s²/2` by `inner_eq_of_norm`):

```lean
theorem tight_pairs (h1a h1b h5b) (x) (hx : Admissible x) (hE : energy x = antiprismEnergy uStar) :
    ∀ i j, i ≠ j → pairP pivots ‖x i - x j‖ = 0
theorem tight_triangles (h1a h1b h5b) (x) (hx) (hE) :
    ∀ i j l, i ≠ j → i ≠ l → j ≠ l → triP pivots ‖x i - x j‖ ‖x i - x l‖ ‖x j - x l‖ = 0
theorem chord_range (x) (hx) (hE) : ∀ i j, i ≠ j → 9619 / 10000 ≤ ‖x i - x j‖ ∧ ‖x i - x j‖ ≤ 2
  -- separation gives `> 0.962 > 0.9619`; `‖x i − x j‖ ≤ ‖x i‖ + ‖x j‖ = 2`
```

About 100 lines.

### U3 — the pair polynomial vanishes only at the chords (edit `Thomson/Pair/Sweep.lean`, `Pair/Main.lean`)

The sweep of `Thomson/Pair/Sweep.lean` carries a lower bound `p` of `Φ` from grid point to grid
point.  Strictness is the same computation with strict tests:

* in `run`: `0 ≤ p` → `0 < p`, and `0 ≤ stepP …` → `0 < stepP …`;
* in `sweepOK`: `0 ≤ cellLo …` → `0 < cellLo …` (the first cell has `Φ'' > 0`) and `xh ≤ g1` → `xh < g1`.

Soundness, alongside the existing `quad_nonneg`/`run_sound`/`sweep_sound` (which remain valid —
the strict checker implies the old one, so *replace* rather than duplicate):

```lean
theorem quad_pos {P D L τ u : ℝ} (hP : 0 < P) (hτ : 0 < τ) (hu0 : 0 ≤ u) (huτ : u ≤ τ)
    (hend : 0 < P + D * τ + L * τ ^ 2 / 2) (hDL : 0 ≤ D ∨ L ≤ 0) : 0 < P + D * u + L * u ^ 2 / 2
  -- concave case: the chord between two positive values; convex case: `≥ P`
theorem run_pos …   : … → ∀ x, g / SCALE ≤ x → x ≤ gEnd / SCALE → 0 < reval p x
theorem sweep_sound_pos … (hf0 : reval p x0 = 0) (hf1 : reval (rder p) x0 = 0) :
    ∀ x, x0 < x → x ≤ (gEnd : ℝ) / SCALE → 0 < reval p x
  -- first cell: `Φ(x) ≥ ½ L (x − x0)² > 0` for `x > x0` since `L > 0`; then `run_pos`
```

The eight certificates `sweepFl … sweepAr` (`SweepXx.lean`, `decide +kernel`) are unchanged data;
their proofs re-run under the strict checker.  Rounding cannot spoil the first step: after the
first cell `p ≈ ½·Φ''·(g₁ − x_h)²` is `≈ 10³²` on the `10⁴⁰` grid.  If a later step reports `p = 0`
(it will not: the sweeps meet where `Φ ≈ 4·10⁻⁶ … 10⁻⁴`), regenerate with `threepoint/pair_gen.py`.

Then in `Pair/Main.lean`, by the same case split as `pairP_nonneg_of` (`Φ > 0` on each side of the
chord of the sub-interval, mirror sweeps via `reval_ralt`), and `Φ = (α − sR)(α + sR)` with
`alpha_pos` (so `Φ > 0 ⟹ pairP > 0`):

```lean
theorem pairP_pos_of (htight) (hclose) :
    ∀ s : ℝ, 24 / 25 ≤ s → s ≤ 2 → (∀ X : Fin 4, s ≠ chord X) → 0 < pairP pivots s
```

and in the main library (next to `pairP_nonneg`):

```lean
theorem pairP_eq_zero_iff (h1a : Task1a) (h1b : Task1b) {s : ℝ} (hs1 : 9619 / 10000 ≤ s) (hs2 : s ≤ 2) :
    pairP pivots s = 0 ↔ ∃ X : Fin 4, s = chord X
```

(`←` is `pairP_tight`; `w = 1 − s²/2` and `s = √(2 − 2w)` are inverse on `s > 0`.)  About 150 lines
plus one re-check of `lake build Pair`.

### U4 — the triangle polynomial is positive at every non-type chord triple (export from `Tri5b`)

The covering already proves `Goal c MG ρ` on every box, i.e. `NumCertU (fun _ => 1/500) (MG/SCALE)`
with `MG/SCALE = 10⁻¹⁰` — it is the `hnum` inside `task5_of_data`.  Export it:

```lean
-- Thomson/Tri5b/Final.lean
theorem numCertU_final (hclose : ∀ j, |pivots j - pivotsNum j| ≤ 1 / 10 ^ 12) :
    NumCertU (fun _ => 1 / 500) (1 / 10 ^ 10)
-- Thomson/ThreePoint/Tasks.lean (default build; `Thomson.Tri5b.Main` is a light module)
def Task5bStrict : Prop := Tri5b.NumCertU (fun _ => 1 / 500) (1 / 10 ^ 10)
-- Thomson/Tri5b/Task5b.lean
theorem task5bStrict : Thomson.Task5bStrict := numCertU_final Thomson.Task1b.task1b
```

`Task5bStrict` is taken as a hypothesis by the `_of_tasks` theorems and discharged in
`Complete.lean`, like `Task5b`.  Then (main library, `Thomson/Unique/Chords.lean`):

```lean
/-- The five types as colour triples, `A = 0, D = 1, N = 2, F = 3`, sorted decreasingly in
chord length (`F > D > N > A`). -/
def allowedTri (X Y Z : Fin 4) : Bool :=  -- multiset ∈ {FFA, FDN, FNA, DAA, NNA}
theorem chord_gaps : ∀ X Y : Fin 4, X ≠ Y → 1 / 500 < |chord X - chord Y|
  -- from `rStar_bounds`, `s2Star_bounds`, `s4Star_bounds`, `sqrt2_bounds`: gaps ≥ 0.116
theorem triP_pos_of_numCertU (h : Task5bStrict) {a b c : ℝ} (hsort : c ≤ b ∧ b ≤ a)
    (hrange : 9619/10000 ≤ c ∧ a ≤ 2) (hg : 0 ≤ gram a b c)
    (hout : ∀ m : Fin 5, 1/500 < |a - (touchType m).1| ∨ 1/500 < |b - (touchType m).2.1| ∨ 1/500 < |c - (touchType m).2.2|) :
    0 < triP pivots a b c
  -- `triSorted_of_numCertU` with the margin kept: `triP = abc · slack ≥ abc · 10⁻¹⁰ > 0`
theorem allowedTri_of_triP_eq_zero (h : Task5bStrict) (X Y Z : Fin 4)
    (hg : 0 ≤ gram (chord X) (chord Y) (chord Z))
    (h0 : triP pivots (chord X) (chord Y) (chord Z) = 0) : allowedTri X Y Z = true
```

*Proof of the last.*  `fin_cases X <;> fin_cases Y <;> fin_cases Z`: 64 goals.  The 21 ordered
type triples close by `decide`.  The 43 others: sort with `triP_swap12/23` (the sorted triple is
one of the 15 non-type sorted triples), then `triP_pos_of_numCertU` contradicts `h0`; its `hout`
hypothesis holds because a non-type sorted chord triple differs from every `touchType m` in some
coordinate by a whole chord gap (`chord_gaps`), and `hg` is carried through the swaps
(`gram_swap12/23`).  About 150 lines; no numerics beyond the four-digit enclosures.

Uniqueness never evaluates `triP` inside a `rhoLocal`-cube, which is why Task 5a is needed only as
it is (nonnegativity, for U1's identity) and not in a strict form.

### U5 — the combinatorial classification (`Thomson/Unique/Graph.lean`, kernel `decide`)

```lean
abbrev Col := Fin 8 → Fin 8 → Fin 4
/-- The antiprism pattern: squares `0..3` and `4..7`, `N(vᵢ) = {wᵢ, wᵢ₊₁}`. -/
def apCol : Col := …   -- a literal table; `apCol i j = A/D` inside a square by `(j−i) mod 4`, `N/F` across
def Valid (c : Col) : Prop :=
  (∀ i j, c i j = c j i) ∧ ∀ i j l, i ≠ j → i ≠ l → j ≠ l → allowedTri (c i j) (c i l) (c j l) = true
def Aligned (c : Col) : Prop := ∃ i j k l, [i, j, k, l].Nodup ∧
  c i j = 0 ∧ c k l = 0 ∧ c i k = 2 ∧ c i l = 2 ∧ c j k = 2 ∧ c j l = 2

theorem classify (c : Col) (hc : Valid c) (hna : ¬ Aligned c) :
    ∃ σ : Equiv.Perm (Fin 8), ∀ i j, i ≠ j → c (σ i) (σ j) = apCol i j
```

*Proof, in three parts.*

1. **Symmetry breaking (30 lines).**  There is `τ : Perm (Fin 8)` with `τ 0 = 0` and
   `k ↦ c 0 (τ k.succ)` monotone on `Fin 7`: `Tuple.sort (fun k : Fin 7 => c 0 k.succ)` with
   `Tuple.monotone_sort`, extended by `0 ↦ 0` (`Equiv.Perm.decomposeFin.symm (0, τ')`, which
fixes `0` by `decomposeFin_symm_apply_zero` and acts as `τ'` on successors by
`decomposeFin_symm_apply_succ`).
   `Valid`/`Aligned` are invariant under relabelling, so it suffices to classify `c ∘ τ`.
2. **A verified search (80 lines).**  Edges `e₀, …, e₂₇` are the pairs `(i, j)`, `i < j`, ordered by
   `j` then `i`, so each new edge closes its triangles with earlier vertices.  For
   `f : Fin 28 → Fin 4`:

   ```lean
   def okUpTo (k : ℕ) (f : Fin 28 → Fin 4) : Bool   -- all triangles with all three edges `< k`, and
                                                      -- `f (0,j−1) ≤ f (0,j)` for the placed vertex-0 edges
   def search : ℕ → (Fin 28 → Fin 4) → Bool
     | 28, f => leafOK f
     | k, f  => !okUpTo k f || (List.finRange 4).all fun a => search (k + 1) (Function.update f ⟨k, _⟩ a)
   theorem okUpTo_congr : (∀ e, (e : ℕ) < k → f e = g e) → okUpTo k f = okUpTo k g
   theorem search_complete : search k f = true → ∀ g, (∀ e, (e : ℕ) < k → g e = f e) →
       okUpTo 28 g = true → leafOK g = true   -- induction on `28 − k`
   theorem search_ok : search 0 (fun _ => 0) = true := by decide   -- 1878 nodes
   ```

   `leafOK f` is membership in the list of the **8 leaves** (printed by
   `python3 plans/unique_enum.py sorted`), each stored with either an explicit permutation
   `σ` (4 leaves: relabelled antiprisms) or an explicit aligned quadruple (4 leaves);
   `theorem leaves_classified : ∀ f ∈ leaves, (∃ σ, …) ∨ Aligned f := by decide`.
3. **Glue (40 lines).**  `c ∘ τ` restricted to the edge list is a `g` with `okUpTo 28 g = true`
   (from `Valid` and monotonicity), so it is a leaf; the aligned alternative contradicts `hna`
   (transported through `τ`); the other gives `σ`, composed with `τ`.

If `decide` on `search_ok` is slow in the kernel (1878 nodes, each a few dozen `Fin` comparisons —
expect seconds to a minute), use `decide +kernel`; `native_decide` is the fallback and would put the
file in its own library like `Task1b`.  A hand proof is possible instead of the search (every
vertex has degree pattern `(2, 1, 2, 2)` because two `D`'s, three `A`'s, three `N`'s or three `F`'s at
a vertex force a forbidden triangle; `A` is two 4-cycles with `D` their diagonals; each `vᵢ` picks
an edge of the other square as its `N`-pair) but it is longer in Lean than the search.

### U6 — geometry: no aligned quadruple, and Gram matrix ⟹ congruence (`Thomson/Unique/Gram.lean`)

```lean
/-- The colour of a pair: the chord its distance equals (U2 + U3 make this total on `i ≠ j`). -/
noncomputable def colOf (x) (i j : Fin 8) : Fin 4 :=
  if ‖x i - x j‖ = chord 0 then 0 else if ‖x i - x j‖ = chord 1 then 1 else if ‖x i - x j‖ = chord 2 then 2 else 3
theorem colOf_spec (…) : i ≠ j → ‖x i - x j‖ = chord (colOf x i j)      -- `pairP_eq_zero_iff` + `tight_pairs`
theorem valid_colOf (h5s : Task5bStrict) (…) : Valid (colOf x)          -- `allowedTri_of_triP_eq_zero` + `tight_triangles` + `gram_det_nonneg`

/-- Four points on `S²` with `ij = kl = A` and `ik = il = jk = jl = N` do not exist in `ℝ³`. -/
theorem not_aligned (…) : ¬ Aligned (colOf x)
```

*Proof of `not_aligned`.*  The Gram matrix of `![x i, x j, x k, x l]` is
`!![1, tA, tN, tN; tA, 1, tN, tN; tN, tN, 1, tA; tN, tN, tA, 1]` with `tA = uStar`
(`chord_inner_zero`) and `tN = −uStar + √2(1 − uStar)/2` (`chord_inner_two`).  Its determinant is
`(1 − tA)² ((1 + tA)² − 4 tN²)` (`Matrix.det_succ_row_zero` with `Fin.sum_univ_succ` down to
`det_fin_three`, then `ring` — there is no `det_fin_four` in Mathlib), which is `≥ 0.75` by `uStar_mem_Icc` and
`sqrt2_bounds` (`nlinarith`).  So by `Matrix.det_gram_ne_zero_iff_linearIndependent` the four
vectors are linearly independent in `EuclideanSpace ℝ (Fin 3)`, contradicting
`LinearIndependent.fintype_card_le_finrank` with `finrank_euclideanSpace_fin`.  About 80 lines.

```lean
/-- The antiprism's inner products, by colour class. -/
theorem inner_antiprism (i j : Fin 8) :
    ⟪antiprism (Real.sqrt uStar) i, antiprism (Real.sqrt uStar) j⟫ = tval (apCol i j)
  -- `tval : Fin 4 → ℝ := ![tA uStar, tD uStar, tN uStar, tF uStar]`; 64 cases by
  -- `fin_cases`, `simp [antiprism, inner_coords]`, `Real.sq_sqrt`, `ring`
theorem inner_of_colOf (…) : i ≠ j → ⟪x i, x j⟫ = tval (colOf x i j)     -- `inner_eq_of_norm`, `chord_inner_*`

/-- **Equal Gram matrices ⟹ congruent** (generic). -/
theorem congruent_of_gram_eq {n : ℕ} (y z : Fin n → EuclideanSpace ℝ (Fin 3))
    (h : ∀ i j, ⟪y i, y j⟫ = ⟪z i, z j⟫) :
    ∃ f : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3), ∀ i, y i = f (z i)
```

*Proof of `congruent_of_gram_eq`.*  Let `T := Fintype.linearCombination ℝ z` and
`S := Fintype.linearCombination ℝ y` (`(Fin n → ℝ) →ₗ[ℝ] E`).  `‖T c‖² = Σᵢⱼ cᵢ cⱼ ⟪z i, z j⟫ = ‖S c‖²`
by `h`, so `ker T = ker S` and `(LinearMap.quotKerEquivRange T).symm.trans
(Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivRange S)` is a linear equivalence
`range T ≃ₗ range S` that preserves norms, hence a `LinearIsometry (range T) →ₗᵢ E`.
`LinearIsometry.extend` makes it a global isometry `E →ₗᵢ E`, and
`LinearIsometry.toLinearIsometryEquiv` (same space, `rfl` on `finrank`) an equivalence `f`; on
`z i = T (Pi.single i 1)` it gives `f (z i) = S (Pi.single i 1) = y i`.  About 120 lines; this is the
one piece of general-purpose mathematics in the plan and could go to Mathlib.

### U7 — assembly (`Thomson/Unique/Main.lean`, `Thomson/Main.lean`, `Thomson/Complete.lean`)

```lean
theorem thomson_eight_unique_of_tasks (h1a : Task1a) (h1b : Task1b) (h5b : Task5b) (h5s : Task5bStrict)
    (x) (hx : Admissible x) (hE : energy x = antiprismEnergy uStar) :
    ∃ (f : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (σ : Equiv.Perm (Fin 8)),
      ∀ i, x i = f (antiprism (Real.sqrt uStar) (σ i)) := by
  -- U2: tight_pairs, tight_triangles, chord_range; U3/U4/U6: valid_colOf, not_aligned;
  -- U5: classify (colOf x) gives σ₀ with colOf x (σ₀ i) (σ₀ j) = apCol i j;
  -- U6: inner_of_colOf + inner_antiprism give ⟪x (σ₀ i), x (σ₀ j)⟫ = ⟪ap i, ap j⟫ (the diagonal
  --     by `OnSphere`), so congruent_of_gram_eq (x ∘ σ₀) ap gives f; take σ := σ₀⁻¹.

-- Complete.lean
theorem thomson_eight_unique (x) (hx : Admissible x) (hE : energy x = thomsonInf 8) : … :=
  thomson_eight_unique_of_tasks Task1b.task1a Task1b.task1b (Tri5b.task5b_of_task5a …) Tri5b.task5bStrict
    x hx (hE.trans thomson_eight)
```

Optional corollaries (each a few lines): the converse — every `f ∘ antiprism (√u*) ∘ σ` is a
minimiser (`energy_isometry`, and permutation invariance of `energy` via `energy_eq_half` and
`Equiv.sum_comp`); and a statement in the `NearAntiprism 0` language of `Reduction.lean`.

## 4. Effort and order

| step | new lines (est.) | kind | depends on |
|---|---|---|---|
| U3 strict sweep | 150 + re-check of `Pair` | edit an existing checker, one soundness proof | — |
| U4 export margin, 64-case lemma | 150 | two-line exports, `fin_cases` + enclosures | — |
| U1 identity, equality case | 150 | copy of `three_point_bound` with `=` | — |
| U2 concrete certificate, tight pairs/triangles | 100 | refactor of `exists_threePointCert_of_tasks` | U1 |
| U5 classification | 150 + 8 leaves as data | verified search, kernel `decide` | — |
| U6 aligned exclusion, Gram ⟹ congruence, antiprism Gram table | 300 | finite-dimensional linear algebra | — |
| U7 assembly | 60 | glue | all |

About 1000 lines, four independent tracks (U3, U4, U1→U2, U5, U6 can be five agents), roughly one
agent-week.  The only build cost is the re-check of the eight sweeps in `lake build Pair`
(`decide +kernel`, minutes) and one small `decide`.

## 5. Acceptance

* `lake build` clean; `#print axioms Thomson.thomson_eight_unique_of_tasks` shows only
  `propext, Classical.choice, Quot.sound` plus `sorryAx` while Task 5a is open — **no
  `Lean.ofReduceBool`** in the default build (the strict Task 5b statement enters as a `Prop`).
* `lake build Complete`: `thomson_eight_unique` with the same axioms as `thomson_eight`.
* `python3 plans/unique_enum.py sorted` prints `nodes 1878, leaves 8` and the eight leaves stored in
  `Graph.lean` are exactly those (the script should be extended to emit them as Lean).

## 6. Risks and what is deliberately not done

* **Strict sweep fails a step.**  Only possible by integer rounding of a `p` that is genuinely tiny;
  the numbers (§2) say every `p` after the first cell is `≥ 10³⁰` on the grid.  Fallback: regenerate
  the cells with `threepoint/pair_gen.py` and a requested margin.
* **Kernel `decide` on the search.**  1878 nodes; if the kernel is slow on `Function.update` over
  `Fin 28 → Fin 4`, represent `f` as a `List (Fin 4)` and index with `getD`, or fall back to
  `native_decide` in a separate library.
* **Mathlib API drift** in `LinearIsometry.extend`/`Tuple.sort`/`Matrix.gram` (all present in the
  pinned revision `db584cd6`; names checked 2026-09-11).
* **Not done, on purpose:** no strict Task 5a (unnecessary: chord triples are far from the cubes);
  no use of the Bachoc–Vallentin or design terms; no analysis of the second local minimum or of
  local uniqueness; no new SDP or certificate.  The blueprint should get a short §13 pointing here
  once U7 lands.
