import Thomson.Certificate.Perturb
import Thomson.TriangleLocal.Calculus.TriLocalDeriv

/-! # Task 5a, Step 2 (partial): the `pivots`-vs-`pivotsNum` perturbation, for `rayφ2`/`rayφ3`

`Thomson/ThreePoint/Perturb.lean` (read-only) already proves the pattern this file extends: every
quantity built affinely from the 24 pivots — `triP p a b c`, and even `deriv (triD p m c) 0`
(`pivotMatrix_triD_row`, via `IsAff.deriv`) — differs between `p = pivots` and `p = pivotsNum` by at
most `pivotEps` times an explicit, `pivotsNum`-computable ℓ¹ quantity (`IsAff.abs_sub_le`). This
file observes that the *same* argument applies one and two derivatives deeper: `rayφ2 p τ δ 0` and
`rayφ3 p τ δ x` (the second and third ray-derivatives `triP_local_of` needs `hhess`/`hrem` about)
are *also* affine in `p`, because differentiating an affine-in-`p` family (`IsAff.deriv`,
`Linear.lean`) is exactly the induction step, applied twice more.

**Why this matters for Task 5a's numeric side**: it means the eventual certificate never needs to
run any interval arithmetic on `pivots` itself (an inaccessible real algebraic number known only via
`Task1b`'s crude `10⁻¹²` bound) — only on `pivotsNum` (exactly known rational data) and on the fixed
finite ℓ¹-sum of the *linear part* evaluated at the 24 unit pivot vectors, both `pivotsNum`-only
computations. What is **not** done here (still open, see the status report): actually bounding
`rayφ2 pivotsNum (touchType m) δ 0` and the correction sums numerically — these still involve the
genuinely irrational `touchType m` coordinates (`uStar`, `√2`, `rStar`, `s2Star`, `s4Star`), and need
either interval arithmetic on `Sharp.lean`'s rational enclosures of those, or an exact symbolic
reduction; that numeric work is not attempted in this file. -/

namespace Thomson.ThreePoint.Cert

open Thomson

/-! ## `rayφ1`, `rayφ2`, `rayφ3` are affine in `p`

Exactly `Linear.lean`'s `IsAff.deriv`, applied once per derivative order, starting from
`triP_isAff`. -/

theorem rayP_isAff (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) (t : ℝ) :
    IsAff (fun p => rayP p τ δ t) := by
  unfold rayP
  exact triP_isAff _ _ _

theorem rayP_differentiable (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    Differentiable ℝ (rayP p τ δ) :=
  (rayP_contDiff p τ δ).differentiable (by simp)

theorem rayφ1_isAff (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) (t : ℝ) :
    IsAff (fun p => rayφ1 p τ δ t) :=
  IsAff.deriv (F := fun p t => rayP p τ δ t) (fun s => rayP_isAff τ δ s)
    (fun p => rayP_differentiable p τ δ) t

theorem rayφ1_differentiable (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    Differentiable ℝ (rayφ1 p τ δ) :=
  (rayφ1_contDiff p τ δ).differentiable (by simp)

theorem rayφ2_isAff (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) (t : ℝ) :
    IsAff (fun p => rayφ2 p τ δ t) :=
  IsAff.deriv (F := fun p t => rayφ1 p τ δ t) (fun s => rayφ1_isAff τ δ s)
    (fun p => rayφ1_differentiable p τ δ) t

theorem rayφ2_differentiable (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    Differentiable ℝ (rayφ2 p τ δ) :=
  (rayφ2_contDiff p τ δ).differentiable (by simp)

theorem rayφ3_isAff (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) (t : ℝ) :
    IsAff (fun p => rayφ3 p τ δ t) :=
  IsAff.deriv (F := fun p t => rayφ2 p τ δ t) (fun s => rayφ2_isAff τ δ s)
    (fun p => rayφ2_differentiable p τ δ) t

/-! ## The perturbation bounds

Direct instances of `IsAff.abs_sub_le`, exactly mirroring `Thomson.triP_perturb`. -/

theorem rayφ2_perturb {p q : Fin 24 → ℝ} {ε : ℝ} (h : ∀ j, |p j - q j| ≤ ε)
    (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    |rayφ2 p τ δ 0 - rayφ2 q τ δ 0| ≤
      ε * ∑ j, |rayφ2 (Pi.single j 1) τ δ 0 - rayφ2 0 τ δ 0| :=
  (rayφ2_isAff τ δ 0).abs_sub_le h

theorem rayφ3_perturb {p q : Fin 24 → ℝ} {ε : ℝ} (h : ∀ j, |p j - q j| ≤ ε)
    (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) (x : ℝ) :
    |rayφ3 p τ δ x - rayφ3 q τ δ x| ≤
      ε * ∑ j, |rayφ3 (Pi.single j 1) τ δ x - rayφ3 0 τ δ x| :=
  (rayφ3_isAff τ δ x).abs_sub_le h

/-- **The reduction to `pivotsNum`.**  Given the `pivotsNum`-only Hessian margin `hhess0` and
remainder bound `hrem0` *with the perturbation loss already subtracted/added* (i.e. with margins
`lam - ε·(ℓ¹ sum)` / `K + ε·(ℓ¹ sum)`, both explicit finite `pivotsNum`-only quantities), the same
statement holds for `pivots`.  This packages `rayφ2_perturb`/`rayφ3_perturb` into exactly the shape
`triP_local_of`'s `hhess`/`hrem` need, so a future certificate only ever has to bound things at
`pivotsNum`. -/
theorem hhess_of_pivotsNum {ε lam : ℝ} (h : ∀ j, |pivots j - pivotsNum j| ≤ ε) (m : Fin 5)
    (lamNum : ℝ)
    (hmargin : ∀ δ : Fin 3 → ℝ,
      lamNum * (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2)
        - ε * (∑ j, |rayφ2 (Pi.single j 1) (touchType m) δ 0 - rayφ2 0 (touchType m) δ 0|)
        = lam * (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2))
    (hhess0 : ∀ δ : Fin 3 → ℝ,
      lamNum * (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) ≤ rayφ2 pivotsNum (touchType m) δ 0) :
    ∀ δ : Fin 3 → ℝ, lam * (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) ≤ rayφ2 pivots (touchType m) δ 0 := by
  intro δ
  have hp := rayφ2_perturb h (touchType m) δ
  rw [abs_le] at hp
  have h0 := hhess0 δ
  have hm := hmargin δ
  linarith [hp.1]

/-- The analogous reduction for the third-derivative bound `hrem`. -/
theorem hrem_of_pivotsNum {ε K : ℝ} (h : ∀ j, |pivots j - pivotsNum j| ≤ ε) (m : Fin 5)
    (KNum : ℝ)
    (hmargin : ∀ (δ : Fin 3 → ℝ) (x : ℝ),
      KNum * (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2)
        + ε * (∑ j, |rayφ3 (Pi.single j 1) (touchType m) δ x - rayφ3 0 (touchType m) δ x|)
        = K * (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2))
    (hrem0 : ∀ (δ : Fin 3 → ℝ) (x : ℝ),
      |rayφ3 pivotsNum (touchType m) δ x| ≤ KNum * (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2)) :
    ∀ δ : Fin 3 → ℝ, ∀ x : ℝ,
      |rayφ3 pivots (touchType m) δ x| ≤ K * (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) := by
  intro δ x
  have hp := rayφ3_perturb h (touchType m) δ x
  rw [abs_le] at hp
  have h0 := hrem0 δ x
  rw [abs_le] at h0
  have hm := hmargin δ x
  rw [abs_le]
  constructor <;> linarith [hp.1, hp.2, h0.1, h0.2]

end Thomson.ThreePoint.Cert
