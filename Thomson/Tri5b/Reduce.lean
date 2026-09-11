import Thomson.Tri5b.Symmetry

/-! # Task 5b, step 3: from the implicit pivots to the rational reference vector

Everything is affine in the pivots, so `triP pivots` differs from `triP pivotsNum` by at most
`ε · Σ_j |G_j|`, where `ε` bounds `‖pivots − pivotsNum‖∞` and
`G_j(a,b,c) = triP e_j (a,b,c) − triP 0 (a,b,c) = −abc · Gh j` is the linear part
(`Thomson.ThreePoint.Perturb`).  This file records that reduction with `ε` as a *parameter*.

**Why the parameter matters — `pivotEps = 10⁻⁶` is too weak for Task 5b.**  The margin available
outside the five excluded cubes is governed by the Hessian of `triP` at the touching types
(smallest eigenvalues `6.2·10⁻⁴ … 3.9·10⁻³` in chord variables) and by the radius
`rhoLocal = 1/500` of the cubes: at the face of a cube the value of `triP` is only
`≈ ½·6.2·10⁻⁴·(1/500)² ≈ 1.2·10⁻⁹`, while `Σ_j |G_j| ≈ 11` there, so the loss allowed by
`pivots_close` is `≈ 1.1·10⁻⁵` — four orders of magnitude larger than the margin.  Since the
hypothesis `‖pivots − pivotsNum‖∞ ≤ 10⁻⁶` is satisfied by vectors `p` for which `triP p` really is
negative just outside a cube, **no** proof of Task 5b can use `pivotEps` alone: Task 1b has to be
sharpened.  Its sketch says the residual at `pivotsNum` is `≈ 2·10⁻²¹` and that only the enclosures
of `u*` limit the estimate, so the sharpening is a matter of digits, not of method
(`Thomson.Tri5b.UStar` supplies the digits).

Task 5a is not affected: there the constant and linear terms of `triP pivots` at the touching type
vanish *exactly* (`triP_tight`), so `ε` only perturbs the Hessian, by
`ε·Σ_j ‖D²G_j‖ ≈ 10⁻⁶ · (95 … 3111) `, which stays below the smallest eigenvalue at all five
types (the worst ratio is `0.83`, at `FFA`). -/

namespace Thomson.Tri5b

open Thomson Finset

/-- The linear part of `triP` in pivot `j`, as a function of the chord triple. -/
noncomputable def Glin (j : Fin 24) (a b c : ℝ) : ℝ := triP (Pi.single j 1) a b c - triP 0 a b c

theorem Glin_eq (j : Fin 24) (a b c : ℝ) :
    Glin j a b c = -(a * b * c) * Gh j (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c ^ 2 / 2) :=
  triP_single_sub j a b c

/-- **The reduction.**  If the pivots are known to `ε` and the reference certificate has margin
`ε · Σ_j |G_j|` at a point, the true certificate is nonnegative there. -/
theorem triP_nonneg_of_num {ε : ℝ} (hclose : ∀ j, |pivots j - pivotsNum j| ≤ ε)
    {a b c : ℝ} (h : ε * ∑ j, |Glin j a b c| ≤ triP pivotsNum a b c) :
    0 ≤ triP pivots a b c :=
  (triP_isAff a b c).nonneg_of_nonneg_sub hclose h

/-- The same with a uniform bound `K` on the ℓ¹-norm of the linear part. -/
theorem triP_nonneg_of_num' {ε K : ℝ} (hclose : ∀ j, |pivots j - pivotsNum j| ≤ ε) (hε : 0 ≤ ε)
    {a b c : ℝ} (hK : ∑ j, |Glin j a b c| ≤ K) (h : ε * K ≤ triP pivotsNum a b c) :
    0 ≤ triP pivots a b c :=
  triP_nonneg_of_num hclose (le_trans (by
    exact mul_le_mul_of_nonneg_left hK hε) h)

/-- The sorted statement for the *reference* certificate: what the box covering has to verify.
`margin` absorbs the pivot uncertainty (`ε · K`). -/
def NumSorted (ρ : Fin 5 → ℝ) (margin : ℝ) : Prop :=
  ∀ a b c : ℝ, chordLo ≤ c → c ≤ b → b ≤ a → a ≤ 2 →
  0 ≤ gram a b c →
  (∀ m : Fin 5, ρ m < |a - (touchType m).1| ∨ ρ m < |b - (touchType m).2.1|
    ∨ ρ m < |c - (touchType m).2.2|) →
  margin ≤ triP pivotsNum a b c

/-- **Task 5b's sorted half, reduced to the reference certificate.** -/
theorem triSorted_of_num {ρ : Fin 5 → ℝ} {ε K : ℝ} (hε : 0 ≤ ε)
    (hclose : ∀ j, |pivots j - pivotsNum j| ≤ ε)
    (hK : ∀ a b c : ℝ, chordLo ≤ c → c ≤ b → b ≤ a → a ≤ 2 → ∑ j, |Glin j a b c| ≤ K)
    (hnum : NumSorted ρ (ε * K)) : TriSorted ρ := by
  intro a b c h1 h2 h3 h4 hg hout
  exact triP_nonneg_of_num' hclose hε (hK a b c h1 h2 h3 h4) (hnum a b c h1 h2 h3 h4 hg hout)

/-- **Task 5, assembled**: Task 5a, a pivot enclosure, an ℓ¹ bound and the box covering. -/
theorem tri_nonneg_of_num {ρ : Fin 5 → ℝ} {ε K : ℝ} (hε : 0 ≤ ε) (hloc : TriLocal ρ)
    (hclose : ∀ j, |pivots j - pivotsNum j| ≤ ε)
    (hK : ∀ a b c : ℝ, chordLo ≤ c → c ≤ b → b ≤ a → a ≤ 2 → ∑ j, |Glin j a b c| ≤ K)
    (hnum : NumSorted ρ (ε * K)) :
    ∀ a b c : ℝ, chordLo ≤ a → chordLo ≤ b → chordLo ≤ c → a ≤ 2 → b ≤ 2 → c ≤ 2 →
      0 ≤ gram a b c → 0 ≤ triP pivots a b c :=
  tri_nonneg_of hloc (triSorted_of_num hε hclose hK hnum)

end Thomson.Tri5b
