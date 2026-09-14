# T4 — `pairP_nonneg : ∀ s, 9619/10000 ≤ s → s ≤ 2 → 0 ≤ pairP pivots s`

*Needs: T0, T1b, T1c(i) (through `pairP_tight`).  Output: `Thomson/TriangleLocal/Calculus/Pair.lean`,
generated box list `Cert/PairBoxes.lean`.  Kernel `decide`; a few hundred boxes of one variable.*

Do **not** factor `P = Π(s − s_X)² Q` (the sketch in `Tasks.lean`): the exact division has
coefficients in the number field and cannot be checked without expanding `P`.  Use the local/global
split, exactly as Task 5 does in three variables; here it is cheap.

## 1. Numbers (at `pivotsNum`)

| chord `s_X` | `P''(s_X)` |
|---|---|
| `A = 1.17125` | `1.59·10⁻²` |
| `D = 1.65639` | `7.74·10⁻³` |
| `N = 1.28769` | `7.27·10⁻³` |
| `F = 1.89689` | `4.37·10⁻²` |

`min P` at distance `≥ 0.01 / 0.02 / 0.05` from the four chords: `3.7·10⁻⁷ / 1.2·10⁻⁶ / 4.5·10⁻⁶`.
Third derivative `|P'''| ≲ 1` on `[0.96, 2]` (measure it; it decides the local radius).

## 2. Local part: `pairP_local (X) : ∀ d, |d| ≤ ρ_X → 0 ≤ pairP pivots (chord X + d)`

Fix `X`, `ρ := ρ_X` (expect `≈ 0.01`–`0.02`: need `½ P''(s_X) − (K₃/6) ρ ≥ margin`, i.e. `ρ ≤ 3P''/K₃`).
For `|d| ≤ ρ` let `φ t := pairP pivots (chord X + t·d)`.  With `E`:

* `φ t = pairPE.eval (Function.update (atomVal 0) 0 (chord X + t d))`; derivatives
  `φ' t = (pairPE.deriv 0).eval (…) · d`, `φ'' = (pairPE.deriv 0).deriv 0 … · d²`, `φ''' = … · d³`
  from `E.hasDerivAt_update` composed with `HasDerivAt.comp` on `t ↦ chord X + t d`
  (or `E.hasDerivAt_curve` with `n = 1`).
* `φ 0 = 0`, `φ' 0 = 0` by `pairP_tight X` (the derivative there is `deriv (pairP pivots) (chord X)`;
  connect by `HasDerivAt.deriv` and `pairPE_eval`).
* `φ'' 0 = P''(s_X) · d² ≥ c_X d²` where `c_X` is a rational lower bound of the interval
  `((pairPE.deriv 0).deriv 0).ieval (atomEnv ![chordIv X, _, _])` — checked by `decide +kernel`
  (`chordIv X := (chordE X).ieval atomEnvC`).
* `|φ''' t| ≤ K_X |d|³ ≤ K_X ρ³` for `t ∈ [0,1]`, with `K_X` the rational upper bound of
  `|((pairPE.deriv 0).deriv 0).deriv 0|` on the interval `[s_X − ρ, s_X + ρ]` — one interval
  evaluation on the *whole* interval (`Iv.hull` of the two endpoint boxes), `decide +kernel`,
  crude is fine.
* `taylor3_lower` gives `φ 1 ≥ c_X d²/2 − K_X ρ³/6 ≥ (c_X/2 − K_X ρ /6) d² ≥ 0`... careful: the
  remainder bound must be written as `K_X ρ · d²` (use `|d|³ ≤ ρ d²`), so the condition to check
  is the rational inequality `K_X ρ ≤ 3 c_X` (`norm_num`).

Choose `ρ_X` by Python so that `K_X ρ_X ≤ 3 c_X/2` (factor-2 slack).  Define
`rhoPair : Fin 4 → ℚ` in the data file.

## 3. Global part: `pairP_global : ∀ s ∈ [9619/10000, 2], (∀ X, ρ_X < |s − chord X|) → 0 ≤ pairP pivots s`

A box is an interval `[l, r]` with rational endpoints and centre `c`, half-width `h`; per box the
checker computes, with `env := atomEnv ![·,_,_]`:

* `v := pairPE.ieval (env at c)` (tight: the point is exact rational),
* `g := (pairPE.deriv 0).ieval (env at c)`,
* `H := (pairPE.deriv 0).deriv 0 |>.ieval (env on [l, r])` (crude, on the whole box),
* accept iff `v.lo − g.absHi·h − H.absHi·h²/2 > 0` (scaled integers).

Soundness `boxOK_sound : boxOK b = true → ∀ s ∈ [l, r], 0 ≤ pairP pivots s`: for `s` in the box let
`φ t := P(c + t(s − c))`; `taylor2_lower` with `K := H.absHi·h²` gives
`φ 1 ≥ φ 0 + φ' 0 − K/2 ≥ v.lo − |g|h − K/2 > 0`.

The box list is produced by `scripts/threepoint/pair_boxes.py`.  The local part covers `|s − s_X| ≤ ρ_X`,
but `s_X` is only known through its enclosure `[s_X.lo, s_X.hi]`, so the global list must cover
`[0.9619, 2] \ ⋃_X (s_X.hi − ρ_X, s_X.lo + ρ_X)` — slightly *more* than the complement of the local
intervals.  That overlap is harmless: at distance `ρ_X` from a root `P ≈ ½P''ρ_X² ≈ 4·10⁻⁷`, and the
checker succeeds there with small boxes.  Recursively split while
the checker fails; expected `≈ 300` boxes.  The script must use the same rounding as `Iv`
(`fractions` with floor/ceil at `2^128`, or simply `mpmath.iv` with generous precision and a
safety factor 2 on every bound).

Emit `Cert/PairBoxes.lean`:

```lean
def pairBoxes : List (ℚ × ℚ) := [(9619/10000, 9631/10000), …]
theorem pairBoxes_cover : ∀ s, 9619/10000 ≤ s → s ≤ 2 → (∀ X, ρ_X < |s − chord X|) → ∃ b ∈ pairBoxes, b.1 ≤ s ∧ s ≤ b.2
theorem pairBoxes_ok : pairBoxes.all boxOK = true := by decide +kernel
```

`pairBoxes_cover`: the boxes are consecutive and abut (`b.2 = next.1`) except at the four gaps, and
each gap `(g₁, g₂)` lies inside some `(chord X − ρ_X, chord X + ρ_X)` (from the enclosure of
`chord X`); prove by `rcases` on `s`'s position with `linarith` — or, simpler, state the cover as a
decidable property of the *rational* list (`gaps ⊆ ⋃ (s_X.hi − ρ_X, s_X.lo + ρ_X)`) checked by
`decide`, plus a 10-line real lemma turning it into the statement above.  If `decide +kernel` on
`pairBoxes.all` is slow (300 boxes × ~10⁴ operations ≈ 1 h), split the list into chunks of 30 per
theorem so files compile in parallel.

## 4. Assembly

```lean
theorem pairP_nonneg : ∀ s, 9619/10000 ≤ s → s ≤ 2 → 0 ≤ pairP pivots s := by
  intro s h1 h2
  by_cases hloc : ∃ X, |s − chord X| ≤ ρ_X
  · obtain ⟨X, hX⟩ := hloc; have := pairP_local X (s − chord X) hX; simpa using this
  · push_neg at hloc; exact pairP_global s h1 h2 hloc
```

## 5. Acceptance

`#print axioms Thomson.pairP_nonneg` standard (no `ofReduceBool`).  Budget: data script one day,
Lean one to two days after T0.
