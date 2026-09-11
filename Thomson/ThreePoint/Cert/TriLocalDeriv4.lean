import Thomson.ThreePoint.Cert.TriLocalDeriv
import Thomson.ThreePoint.Cert.TriLocal4Box

/-! # Task 5a, redesign: the fourth ray-derivative

One further application of the same `contDiff_infty_iff_deriv` peeling used three times already in
`TriLocalDeriv.lean` (not modified here) — gives `rayφ4` and the `HasDerivAt` chain one order
deeper, exactly the `h1,h2,h3,h4` hypotheses `taylor4_lower` (`TriLocal4Box.lean`) needs. -/

namespace Thomson.ThreePoint.Cert

open Thomson
open scoped ContDiff

noncomputable def rayφ4 (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) : ℝ → ℝ :=
  deriv (rayφ3 p τ δ)

theorem rayφ3_contDiff (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    ContDiff ℝ ∞ (rayφ3 p τ δ) :=
  (contDiff_infty_iff_deriv.mp (rayφ2_contDiff p τ δ)).2

theorem rayφ3_hasDerivAt (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) (x : ℝ) :
    HasDerivAt (rayφ3 p τ δ) (rayφ4 p τ δ x) x :=
  (contDiff_infty_iff_deriv.mp (rayφ3_contDiff p τ δ)).1.differentiableAt.hasDerivAt

/-- **The full quartic lower bound for `triP p`, cubic term exact.**  The direct instantiation of
`taylor4_lower` for `rayP p τ`: given a crude quartic bound `M` on the fourth ray-derivative on the
segment to `τ + δ`, the value at `τ + δ` is bounded below by the exact second- and third-order
Taylor terms at `τ` minus the quartic remainder. Vanishing to second order (`hzero`, `hgrad`) is
supplied by the caller — see `TriLocalDeriv.lean`'s `rayP_zero`/`rayφ1_zero_eq` for how to get it
from `Thomson.triP_tight`. -/
theorem rayP_taylor4_lower (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) {M : ℝ}
    (hzero : ∀ δ : Fin 3 → ℝ, rayP p τ δ 0 = 0) (hgrad : ∀ δ : Fin 3 → ℝ, rayφ1 p τ δ 0 = 0)
    (δ : Fin 3 → ℝ)
    (hrem4 : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |rayφ4 p τ δ x| ≤ M * (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) ^ 2) :
    rayφ2 p τ δ 0 / 2 + rayφ3 p τ δ 0 / 6 - M * (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) ^ 2 / 24
      ≤ rayP p τ δ 1 :=
  taylor4_lower (rayP_hasDerivAt p τ) (rayφ1_hasDerivAt p τ) (rayφ2_hasDerivAt p τ)
    (rayφ3_hasDerivAt p τ) hzero hgrad δ hrem4

end Thomson.ThreePoint.Cert
