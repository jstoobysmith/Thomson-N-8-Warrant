# T5b — `triP_global`: the triangle polynomial outside the five local cubes

*Needs: T0, T1b, `rho0` from T5a (only the radii; T5a itself can be in progress).  Output:
`Thomson/TriangleGlobal/Checker.lean` (checker + soundness, hand-written), `Thomson/TriangleGlobal/Boxes*.lean`
(generated, many files), `Thomson/TriangleGlobal/Global.lean` (assembly).  `native_decide` for the box
lists — see README §1.1 for what that means and how to downgrade any box to `decide +kernel`.*

## 0. Statement actually proved (after Step 0's edits)

Through `Tri5b.tri_nonneg_of` (Symmetry.lean) the obligation is the sorted one:

```lean
theorem triSorted : ∀ a b c : ℝ, 9619/10000 ≤ c → c ≤ b → b ≤ a → a ≤ 2 → 0 ≤ gram a b c →
    (∀ m, rho0 m < |a − τ_m.1| ∨ rho0 m < |b − τ_m.2.1| ∨ rho0 m < |c − τ_m.2.2|) → 0 ≤ triP pivots a b c
```

All five `τ_m` are sorted (`a ≥ b ≥ c`), so on the sorted cone they are the only zeros.
Region `R := {0.9619 ≤ c ≤ b ≤ a ≤ 2, gram ≥ 0}`, volume `≈ 0.1`.

## 1. Why this is the expensive task, and the shape of the covering

Around each type `T ≈ ½ δᵀ H_m δ` with eigenvalue ratio up to `1 : 250` (README §3).  A box of
half-width `h` at distance `d` from `τ_m` is certified by the second-order centred form only if
`½ ‖H‖ h² ≲ ½ λ_min d²`, i.e. `h ≲ d/16`.  So the shells `d ∈ [2^j ρ, 2^{j+1} ρ]` each need
`O(10³–10⁴)` boxes, there are `≈ 7` shells per type (from `ρ ≈ 10⁻³` to `0.1`), and the bulk
(`T ≳ 10⁻⁶`) needs boxes of width `≈ 3·10⁻³` near the shells growing to `≈ 3·10⁻²` far away:
**expect `10⁵`–`10⁶` boxes in total**, each costing `≈ 3·10⁴` interval operations.  That is
`10¹⁰` operations: minutes with `native_decide`, weeks in the kernel.  Two reductions that are
worth their cost, and one that is not:

* **Worth it — eigen-aligned boxes in the shells.**  Replace `(a,b,c)` near `τ_m` by
  `τ_m + U_m ξ` with `U_m` a rational approximate eigenbasis (orthogonal to 15 digits; exactness is
  irrelevant, it is only a linear change of variables, the substitution is `E.subst`).  With box
  half-widths `h_i ∝ λ_i^{−1/2}` the second-order error is isotropic and `h ≈ d/2` suffices:
  `≈ 8·(Π λ_i/λ_min)^{1/2} ≈ 300` boxes per shell.  This alone divides the shell count by ~30.
* **Worth it — evaluate through the `wsum` form.**  `Fh_Hp_eq_wsum` (`Tri5b/MForm.lean`) writes
  `F = (1/3) Σ_k Σ_{3 pairs} wpoly(M_k, x, y)·Q_k` with `M_k = B_k H_k B_kᵀ` *constant*.  Mirror it:
  `MkIv : Fin 6 → Matrix _ _ Iv` computed **once** (`E.ieval` of `B H Bᵀ` with pivot atoms;
  a lemma `MkIv_mem : (MkIv k i j).mem (Mmat (Hp pivots) k i j)`), and an `E`-term `triWE` over
  atoms `0,1,2` plus *new atoms `100 + idx`* for the `M_k` entries (their env is `MkIv`).  Then one
  evaluation of `T` costs `≈ 2·10³` operations instead of `≈ 3·10⁴`, and its symbolic derivatives
  are proportionally smaller.  Bridge: `triWE.eval (atomVal ++ Mvals) = triP pivots a b c` from
  `Fh_Hp_eq_wsum` + `wpoly` unfolding (`E.eval_sum`).
* **Not worth it — Bernstein forms.**  Same `h²` convergence as the centred form, more code.

## 2. The checker (`Tri5b/Checker.lean`)

Box datum: `structure Box where (U : Matrix (Fin 3) (Fin 3) ℚ) (c : Fin 3 → ℚ) (h : Fin 3 → ℚ) (σ : ℚ)`
meaning the parallelepiped `{U (c + η) : |η_i| ≤ h_i}` (axis boxes have `U = 1`) and an
S-procedure multiplier `σ ≥ 0` (0 for interior boxes).  The polynomial checked on the box is
`Tσ := triP − σ·gram` (`gramE` is a 30-node `E`); on `R` this is `≤ triP`, so `Tσ ≥ 0` suffices
(`nonneg_of_s_procedure`).

```lean
def boxOK (b : Box) : Bool :=
  let e := (triWE − σ·gramE).subst (x ↦ U (c + ξ))          -- E in atoms ξ = 0,1,2
  let envC := atomEnvW ![Iv.ofRat 0, Iv.ofRat 0, Iv.ofRat 0]   -- centre: ξ = 0
  let envB := atomEnvW ![[-h₀,h₀], [-h₁,h₁], [-h₂,h₂]]          -- whole box
  let v := e.ieval envC
  let g := fun i => ((e.deriv i).ieval envC).absHi
  let H := fun i j => (((e.deriv i).deriv j).ieval envB).absHi
  v.lo − Σ_i g i · h_i − ½ Σ_{i,j} H i j · h_i h_j > 0     -- scaled integers

theorem boxOK_sound (b : Box) (h : boxOK b = true) :
    ∀ ξ : Fin 3 → ℝ, (∀ i, |ξ i| ≤ b.h i) →
      0 ≤ triP pivots (x ξ 0) (x ξ 1) (x ξ 2) − b.σ * gram (x ξ 0) (x ξ 1) (x ξ 2)
```

Soundness: `φ t := e.eval(t ξ)`, `E.hasDerivAt_curve` twice, `taylor2_lower` with
`K := Σ_{ij} H_ij h_i h_j`; the interval facts by `E.ieval_mem` with `atomEnvW_mem` (T0's
`atomEnv_mem` extended by `MkIv_mem`).  The substitution `x ↦ U(c + ξ)` is `E.subst` with
`σ i := Σ_j U_ij (c_j + var j)`; `E.eval_subst` turns it back into `triP` at the real point.

Global assembly needs the *cover* lemma: every point of `R` outside the local cubes lies in some
box.  Make it decidable: represent the covering as (i) for each type, a list of shells, each a
list of `ξ`-boxes whose union contains the `ξ`-image of the annulus `{ρ_j ≤ |δ|_∞ ≤ ρ_{j+1}}` — the
generator produces the boxes by bisection *of a superset box*, so the cover is "these boxes
partition the parallelepiped `P_j`", a statement about rational corners, and `P_j ⊇ annulus` is a
short real-arithmetic lemma using `‖U⁻¹‖`; (ii) an axis-aligned partition of a rational superset of
`R \ ⋃ outer parallelepipeds`, plus a check that every axis box either lies inside `R`'s
complement's interior (skipped) or is in the list.  Simplest robust design: **partition the
whole cuboid `[0.9619, 2]³` (sorted or not) into axis boxes by bisection**, and for each box
decide: (a) disjoint from `R` (`gram < 0` on it, or it violates the ordering, checked by interval
arithmetic — then no obligation), or (b) inside a local cube (skipped), or (c) it is checked with
`σ = 0`, or (d) it meets `gram = 0` and is checked with `σ > 0`, or (e) it lies inside a shell of
type `m` and is replaced by the rotated sub-boxes.  The cover lemma is then a decidable statement
about the bisection tree (`treeCovers : Tree → Bool`) with a single soundness proof by induction on
the tree.  Whatever the design, **write the cover lemma before generating boxes**; it dictates the
data format.

## 3. Boundary boxes and `σ`

`triP` is negative outside `R` (down to `−6·10⁻⁴`), so boxes meeting `gram = 0` need `σ > 0`.
For such a box take `σ := max(0, ∇T·n / ∇gram·n)` at the box centre (`n` the normal of `gram = 0`),
so that `T − σ·gram` is flat across the boundary, and then require `T − σ gram ≥ 0` on the whole
box.  If a boundary box fails for every `σ`, bisect.  Also record the corner `c = 0.9619` face:
there `T ≥ 2·10⁻⁵`, no special treatment.

## 4. The generator (`scripts/threepoint/tri_boxes.py`) — do this first, it is the go/no-go

Implement in Python the *same* `Iv` arithmetic (`fractions` with floor/ceil at `2^128`, or
`mpmath.iv` at 60 digits with a safety factor 2 on every bound — the latter is 100× faster and
the Lean check is the ground truth) and the same checker.  Adaptive bisection over the design
of §2, shells with eigen-aligned boxes, `σ` on boundary boxes.  Outputs: box files in chunks of
`≈ 2000` boxes (`Boxes001.lean` …), the cover tree, and a summary: number of boxes per category,
minimal certified margin, total operation count.

Decision table after the prototype:

| total boxes | what to do |
|---|---|
| `≤ 3·10⁴` | `decide +kernel` throughout (days of CPU, parallel over files); no new axiom |
| `3·10⁴`–`3·10⁶` | `native_decide` per chunk file; record `Lean.ofReduceBool` in the blueprint |
| `> 3·10⁶` | stop and revisit: higher-order centred form (add third-derivative term, `h³` error), or split the shells finer in the soft direction only |

## 5. Lean assembly (`Tri5b/Global.lean`)

```lean
theorem allBoxes_ok : (boxes001 ++ … ).all boxOK = true      -- or one theorem per chunk, each `by native_decide`
theorem cover_ok : treeCovers tree = true := by native_decide
theorem triSorted : … := by
  intro a b c …
  obtain ⟨b, hb, hξ⟩ := cover_sound tree cover_ok a b c …           -- the point lies in a checked box
  have := boxOK_sound b (allBoxes_ok_of_mem hb) ξ hξ
  exact nonneg_of_s_procedure … this (by positivity) hgram
```

and in `Tasks.lean`: `triP_global`/`triP_nonneg` from `Tri5b.tri_nonneg_of triP_local triSorted`.

## 6. Acceptance

`lake build` clean; `#print axioms Thomson.thomson_eight_lower` = `propext, Classical.choice,
Quot.sound, Lean.ofReduceBool`.  Add to the blueprint §0: which theorems depend on
`ofReduceBool`, the box count, and the command that re-checks one chunk with `decide +kernel`.
