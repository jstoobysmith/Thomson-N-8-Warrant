import Thomson.TriLocalCert.Compute
import Thomson.TriLocalCert.Touch
import Thomson.TriLocalCert.CFData

/-! # Task 5a, numeric side: one touching type, from its checked data

`type_certificate` turns the checked data of one touching type — the shifted tensor
(`CS = Ishift CFt a b c`), the interval data (`D = computeD …`) and the six face coverings —
into the two facts Task 5a's calculus needs (`Thomson/ThreePoint/Cert/TriLocalFinal.lean`):
`bracket ≥ 0` on the cube, and the fourth-derivative bound against the same `M`. -/

namespace Thomson.TriLocalCert

open Thomson Thomson.Tri5b Set

theorem type_certificate {p : Fin 24 → ℝ} (hclose : ∀ j, |p j - pivotsNum j| ≤ 1 / 10 ^ 12)
    (m : Fin 5) {CSm : IT} {a b c : ℤ} {D : Data}
    (hCS : ∀ i j k, CSm i j k = Ishift CFt a b c i j k)
    (hD : D = computeD CFt CSm (Tt m).1 (Tt m).2.1 (Tt m).2.2 a b c)
    (hM : 0 ≤ D.M.lo) (trees : Fin 3 → Bool → QT)
    (hok : ∀ f σ, faceOK D f σ (trees f σ) = true) :
    (∀ δ : Fin 3 → ℝ, (∀ i, |δ i| ≤ 1 / 500) →
      0 ≤ bracket (Hpol (Q2 p (touchType m))) (Cpol (K3 p (touchType m)))
        (Mreal CSm (Tt m).1 (Tt m).2.1 (Tt m).2.2 a b c) δ) ∧
    (∀ δ : Fin 3 → ℝ, (∀ i, |δ i| ≤ 1 / 500) → ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (deriv (deriv (deriv (rayR p (touchType m) δ)))) x|
        ≤ Mreal CSm (Tt m).1 (Tt m).2.1 (Tt m).2.2 a b c * N2 δ ^ 2) := by
  have hc := ITMem_CFt hclose
  have hcs : ITMem CSm (shift (cF (Mmat (Hp p))) ((a : ℝ) / SCALE) ((b : ℝ) / SCALE)
      ((c : ℝ) / SCALE)) := fun i j k => by
    rw [hCS]; exact ITMem_Ishift hc a b c i j k
  obtain ⟨h0, h1, h2⟩ := Tt_mem m
  have hmem := computeD_mem (CS := CSm) (a := a) (b := b) (c := c) hc h0 h1 h2
  rw [← hD] at hmem
  exact ⟨bracket_nonneg hmem hM trees hok,
    fun δ hδ x hx => ray4_le_M hcs h0 h1 h2 hδ hx.1 hx.2⟩

end Thomson.TriLocalCert
