# Reorganising the `N = 8` Thomson formalisation

*Written 2026-09-12; executed 2026-09-13 (see §6 for what was done and what was deferred).  The "Tasks"
(1a, 1b, …, 5b) were the work-breakdown of the certificate; they are finished and their numbering
carries no mathematical meaning, so the new layout drops it entirely.*

## 1. Goals

1. **Easy to read.**  A reader should be able to follow the proof top-down from one file
   (`Thomson.lean`), directory by directory, in the order of the mathematics: problem → LP bound →
   separation → three-point bound → the certificate → its four inequalities → the theorem →
   uniqueness.  Infrastructure (interval arithmetic, list polynomials, kernel tricks) lives in its
   own directory and is imported, never interleaved with mathematics.
2. **Origin in the literature visible.**  Every directory has a `README.md` and every module
   docstring opens with a *Reference* line naming the paper (or the blueprint section, when the
   argument is ours) the file formalises.  Generated data say which script generated them and from
   what.
3. **Mathlib conventions.**  Module names in `UpperCamelCase`, one concept per file, `namespace
   Thomson` throughout with sub-namespaces per directory, `lowerCamelCase` definitions,
   `snake_case` theorems named after their statement, docstrings on every public declaration, a
   `Main results` section in each module docstring, no `set_option maxHeartbeats` outside generated
   files, no `open … in` at file top unless needed, `theorem` for `Prop`s and `def` otherwise,
   explicit `Real.sqrt`/`Finset.sum` notation as Mathlib writes it, and `#print axioms` checked
   in a `test/` file.

## 2. The proof, in reading order (what the directories will say)

| step | mathematics | literature |
|---|---|---|
| A | energy, admissible configurations, `thomsonInf`, existence of a minimiser, first-order (force-balance) condition | Thomson (1904); the compactness argument is standard (blueprint §1–2) |
| B | the square antiprism family `antiprism h`, closed-form energy, the optimal parameter `u*` (`E′(u*) = 0`, convexity of `E` on the family), the cube as a competitor, enclosures of `u*`, `√2`, the four chords | Erber–Hockney (1991), Ashby–Stucki; blueprint §3–4, §6–11 |
| C | Delsarte–Yudin linear programming bounds: Schoenberg positivity of Legendre sums on `S²` (`P₁…P₄, P₇, P₁₂`), Yudin's bound at degrees 3, 7, 12, the bound in slack form and *separation* (`E ≤ 19.6753 ⟹` all chords `> 0.9619`) | Delsarte–Goethals–Seidel (1977), Yudin (1992), Schoenberg (1942); blueprint §12–13, §8.1 (slack form is ours) |
| D | the three-point (Bachoc–Vallentin / Cohn–Woo) bound for `S²`: positivity of the matrices `S_k`, the certificate structure `ThreePointCert`, the bound, the bound as an identity and its equality case | Bachoc–Vallentin (2008), Cohn–Woo (2012); blueprint §12.2 (our derivation for `S²`, `k ≤ 5`, degree 8 — *not copied from a paper*) |
| E | the concrete certificate: exact kernel bases `B_k` (polynomials in `u*`), 95 fixed rationals, the 24 pivots defined implicitly by the 24 tightness rows, the minimal polynomial of `u*` over `ℚ(√2)`, affine dependence on the pivots (perturbation), the kernel lemma and slack identity along the family, the two redundant rows | ours (blueprint §12.3–12.7); design scripts in `scripts/threepoint/` |
| F | the four numeric inequalities on the certificate, all `decide +kernel`: (i) `pivotMatrix` invertible and pivots enclosed to `2·10⁻²¹` (approximate inverse + contraction); (ii) blocks positive semidefinite (rational `LDLᵀ`); (iii) the pair polynomial `≥ 0` on `[0.9619, 2]` (double zeros + Bernstein/Taylor sweeps); (iv) the triangle polynomial `≥ 0`: locally at the five touching types (fourth-order Taylor + patch covering) and globally (Taylor-model box covering with the S-procedure) | verified interval arithmetic and Taylor models: Moore (1966), Makino–Berz (2003); S-procedure: Yakubovich (1971); the coverings are ours |
| G | assembly: `thomson_eight_lower`, `thomson_eight : thomsonInf 8 = E(u*)` | — |
| H | uniqueness: equality case of the three-point bound ⟹ colouring of `K₈` by the four chords ⟹ combinatorial classification (kernel search) ⟹ Gram matrix ⟹ isometry | ours (`docs/uniqueness.md`); Gram-to-congruence is classical |

## 3. Proposed tree

```
Thomson.lean                       umbrella: imports everything below, in reading order, with a
                                   docstring that is the table of §2
Thomson/
  Basic/
    Energy.lean                    A: `energy`, `Admissible`, `thomsonInf`, invariance under O(3)
    Exists.lean                    A: compactness, `thomsonInf_attained`
    ForceBalance.lean              A: first-order conditions, `sum_local_energy`, covering radius
  Antiprism/
    Family.lean                    B: `antiprism h`, chords, Gram table, closed-form energy
    Derivative.lean                B: `E′`, strict monotonicity, `uStar`, `antiprismEnergy'_uStar`
    Enclosures.lean                B: `u*`, `√2`, `r*, s₂*, s₄*` to 13/25/32/40 digits (merges
                                   Enclosure.lean, ThreePoint/Sharp.lean, Tri5b/UStar.lean, CubeData chord bounds)
    MinPoly.lean                   E: the degree-12 minimal polynomial of `u*` over `ℚ(√2)`
    Cube.lean                      B: the cube, `cube_not_minimal`
  LP/
    Schoenberg.lean                C: Legendre/Gegenbauer positivity on `S²` (solid harmonics)
    Yudin.lean                     C: the LP bound, degrees 3, 7, 12
    Slack.lean                     C: the bound as an identity; separation (`separation_of_energy_le`)
    Reduction.lean                 C: the finite reductions (§14), kept for the record
  ThreePoint/
    BachocVallentin.lean           D: the matrices `S_k`, `bv_positivity`
    Certificate.lean               D: `ThreePointCert`, `three_point_bound`, `pair_of_poly`, `tri_of_poly`
    Identity.lean                  D/H: the bound as an identity, `three_point_tight`
  Certificate/
    Data.lean                      E: GENERATED — bases `B k`, fixed rationals, slots, `pivotsNum`
    Linear.lean                    E: `Fh`, `Hp`, rows, `pivotMatrix`, `pivots`, `rows_vanish`, `IsAff`
    Perturb.lean                   E: affine perturbation bound (`pivots` vs `pivotsNum`)
    Slack.lean                     E: the slack identity along the family
    Kernel/                        E: GENERATED — `Acomb` entries and the double zero, per block
    Redundant.lean                 E: the two dropped rows
    Assemble.lean                  E/G: the obligations as named `Prop`s and `exists_threePointCert_of`
                                   (this is `ThreePoint/Tasks.lean` with the Task table removed)
  Numerics/                        shared infrastructure, no `Thomson`-specific mathematics
    Interval.lean                  fixed-point intervals `Itv` at `10⁻⁴⁰`, soundness
    TaylorModel.lean               quadratic Taylor models `TM`, `loBound`
    PolyList.lean                  coefficient lists: `ev1`, Horner shift, scaling, `Mem1` (from KPoly + Pair/Poly)
    Tensor.lean                    `9×9×9` tensors: `ev`, shift, the nested-list layer and its Taylor model (Tensor, Engine, KPoly, KTM)
    Sqrt.lean                      kernel-friendly integer square root
    README.md                      what the kernel can and cannot reduce; measured speeds (from memory notes)
  Pivots/                          F(i), was Task1b
    Rows.lean, Points.lean, Entries.lean, Residual.lean, System.lean
    Tables/                        GENERATED literal tables, one file per column
    Check.lean                     `η ≤ 10⁻¹¹`, `ρ ≤ 10⁻²¹`, `decide +kernel`
    Main.lean                      `pivotMatrix_det_isUnit`, `pivots_close`
  PSD/                             F(ii), as now (Block0–5, Check, Dom, Main)
  Pair/                            F(iii), as now (Poly → Numerics, Coeff, Taylor, Tables, Sweep*, Main)
  TriangleLocal/                   F(iv-a), merges ThreePoint/Cert/TriLocal* (calculus) and TriLocalCert (numerics)
    Calculus/                      Taylor lower bounds along rays, Fréchet coefficients, polarisation
    Patch.lean, Jet.lean, Ray.lean, Enclose.lean, Compute.lean, Polar.lean
    Types/                         GENERATED: Type0–4, Face*_*
    Main.lean
  TriangleGlobal/                  F(iv-b), was Tri5b
    Domain.lean, Symmetry.lean, Reduce.lean, MForm.lean
    QTensor.lean, Shift1.lean, Bridge.lean   the tensor of `F`
    CertIntervals.lean, CubeData.lean         GENERATED data
    Leaf.lean, Cover.lean, Skip.lean          the box covering and its soundness
    KernelLeaf.lean                           the kernel-checked leaf (KLeaf)
    Covering/                                 GENERATED: Part000–636 and the recombination
    Main.lean                                 `triP_global`, the strict margin
  Uniqueness/                      H, as `Unique/` now, with `Defs, Identity, Tight, PairZero, Chords, Graph, Gram, Congruent, Main`
  Main.lean                        G: `thomson_eight_lower_of`, `thomson_eight_lower`, `thomson_eight`,
                                   `thomson_eight_unique` (merges Main.lean and Complete.lean)
scripts/                           was `scripts/threepoint/` and `docs/history/*.py`: every generator, named after
                                   the file it generates (`gen_certificate_data.py`, `gen_pivot_tables.py`,
                                   `gen_triangle_covering.py`, `mirror_triangle_covering.py`, …)
docs/
  blueprint.md                     was docs/blueprint.md
  uniqueness.md                    was docs/uniqueness.md
  history/                         was docs/history/ (the task files, kept for the record)
test/
  Axioms.lean                      `#print axioms` of the final theorems (must list only propext, Classical.choice, Quot.sound)
```

Library targets in `lakefile.toml` stay as they are in spirit — a default library of everything
cheap and one library per expensive kernel certificate (`Pivots`, `TriangleLocal`,
`TriangleGlobal`) plus `Complete` — but named after the directories.

## 4. Conventions per file

Every module starts with

```lean
/-!
# <Title>

<Two or three sentences: what is proved and why it is needed.>

## Reference
<Author (year), Theorem/Section>, or "Blueprint §n (original argument)".

## Main results
* `foo_bar` — …
* `baz` — …

## Implementation notes
<only if there is something non-obvious: why a `decide +kernel`, why a generated table, …>
-/
```

Generated files begin with `-- GENERATED by scripts/<name>.py from <inputs>; do not edit.` and
contain data and `decide +kernel` theorems only; their soundness lemmas live in hand-written files.
Names: `Thomson.Antiprism.Family.energy`, `Thomson.LP.yudin_bound_seven`, `Thomson.ThreePoint.bound`,
`Thomson.Certificate.pivots_close`, `Thomson.TriangleGlobal.triP_nonneg`, …; theorem names state the
conclusion (`energy_le_of_cert`, `pivotMatrix_det_isUnit`), hypotheses in `_of_` suffixes, and
the final statements keep their current names (`thomson_eight`, `thomson_eight_lower`,
`thomson_eight_unique`).  No name mentions a Task number.

## 5. Order of work

1. Move the infrastructure into `Numerics/` (pure refactor; `Itv`, `TM`, lists, tensors, sqrt) and
   make every certificate library import it; this is the only step that touches many files at once.
2. Rename directories (`Task1b → Pivots`, `TriLocalCert + ThreePoint/Cert → TriangleLocal`,
   `Tri5b → TriangleGlobal`, `Unique → Uniqueness`) and modules; update `lakefile.toml`, the
   generators (paths and headers) and re-run them so that the generated files are reproducible.
3. Split `ThreePoint/Tasks.lean` into `Certificate/Assemble.lean` (statements and assembly) and
   move its status table into the directory `README.md`s; merge `Main.lean`/`Complete.lean`.
4. Rewrite every module docstring to the template of §4 and write the directory `README.md`s
   (one paragraph each, with the reference line and a table of files).
5. Add `test/Axioms.lean`; make it part of `lake build Complete`.

Nothing in this plan changes a statement or a proof; expensive kernel-checked files must be moved
byte-for-byte (a changed comment re-runs the check — `TriLocalCert/CFData.lean` alone is half an
hour and 25 GB).

## 6. Status (2026-09-13)

Done: the tree of §3 (files moved, `import`s and paths rewritten, `lakefile.toml`, `Thomson.lean`,
generators and `scripts/kernel_build/` updated; `threepoint/` → `scripts/threepoint/`, the plans
→ `docs/history/`, blueprint → `docs/blueprint.md`); a `README.md` with a *Reference* line and a
file table in every directory of `Thomson/`; `test/Axioms.lean`; the full rebuild.

Deliberately deferred, because each would change hundreds of proofs for no mathematical gain:
Lean **namespaces and declaration names are unchanged** (`Thomson.Tri5b.*`,
`Thomson.TriLocalCert.*`, `Thomson.Task1b.*`, `Thomson.Unique.*` still name the declarations of
`TriangleGlobal`, `TriangleLocal`, `Pivots`, `Uniqueness`); files were moved, not merged
(`Main.lean`/`Complete.lean`, the three enclosure files, `Tensor`/`TensorEngine`/`PolyList` stay
separate); the module-docstring template of §4 is applied at directory level (the `README.md`s),
not yet to every module.
