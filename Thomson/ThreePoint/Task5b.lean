import Thomson.ThreePoint.Tasks

/-! # Task 5b, as a proposition

Task 5b is **proved**, in the `Tri5b` library (`Thomson/Tri5b/`, a separate `lean_lib` so that the
hour of `native_decide` its box covering costs is not part of the main build).  `lake build Tri5b`
checks it; `Thomson/Tri5b/README.md` describes it.  Here it is only *stated*, and assumed, so that
the main development does not depend on that build.

Two things differ from the `triP_global` of `Tasks.lean`.

* **The chord bound is `9619/10000`, not `24/25`.**  At `24/25` the statement is false: at
  `(a, b, c) = (1.682, 24/25, 24/25)` the chords are in range, `gram = +5.6·10⁻³`, the triple is
  `≥ 0.21` from every touching type, and `triP pivots = −3.7·10⁻⁶`.  The true range from
  `separation_of_energy_le` is `≥ √(2 − 2·0.5373) = 0.9619771…`, which `tri_of_poly` rounds down to
  `24/25`; `Thomson.Tri5b.tri_of_poly'` is the same lemma on the true range, and `Bound.lean`
  and the `tri` field of `exists_threePointCert` need the constant changed to match.
* **Task 1b is needed at `10⁻¹²`, not `10⁻⁶`.**  Just outside a `rhoLocal`-cube `triP` is only
  `≈ ½·λ_min·(1/500)² ≈ 1.2·10⁻⁹`, while `pivotEps = 10⁻⁶` permits a perturbation of
  `10⁻⁶·Σⱼ|Gⱼ| ≈ 1.1·10⁻⁵`: no proof of Task 5b can use Task 1b as currently stated.  The residual
  at `pivotsNum` is `≈ 10⁻²¹`, so this is a matter of digits, not of a new estimate. -/

namespace Thomson

/-- **Task 5b** — global positivity of the triangle polynomial away from the five touching types,
on the *corrected* chord range.  Proved in the `Tri5b` library as `Thomson.Tri5b.task5b`, from
Task 5a and Task 1b at `10⁻¹²`. -/
def Task5b : Prop :=
  ∀ a b c : ℝ, 9619 / 10000 ≤ a → 9619 / 10000 ≤ b → 9619 / 10000 ≤ c →
    a ≤ 2 → b ≤ 2 → c ≤ 2 →
    0 ≤ 1 + 2 * (1 - a ^ 2 / 2) * (1 - b ^ 2 / 2) * (1 - c ^ 2 / 2)
        - (1 - a ^ 2 / 2) ^ 2 - (1 - b ^ 2 / 2) ^ 2 - (1 - c ^ 2 / 2) ^ 2 →
    (∀ m : Fin 5, rhoLocal < |a - (touchType m).1| ∨ rhoLocal < |b - (touchType m).2.1|
      ∨ rhoLocal < |c - (touchType m).2.2|) →
    0 ≤ triP pivots a b c

/-- Task 5b, assumed here and proved in the `Tri5b` library (see the module docstring). -/
theorem task5b : Task5b := sorry

end Thomson
