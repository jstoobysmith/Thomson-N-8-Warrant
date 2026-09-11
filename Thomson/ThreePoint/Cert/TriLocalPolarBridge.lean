import Thomson.TriLocalCert.Polar
import Thomson.ThreePoint.Cert.TriLocalPolar

/-! # Task 5a: bridge from `Hs`/`Cs` to the peer's generic `Hpol`/`Cpol`

`Thomson/TriLocalCert/Polar.lean` (peer session, main tree, copied verbatim into this worktree,
not edited) generalizes `TriLocalPolar.lean`'s `Hs`/`Cs` into a form-agnostic `Hpol`/`Cpol` taking
the quadratic/cubic form as a function argument. The formulas are identical (same 10 directions,
same `/2`/`/6` polarization structure); this file supplies the `funext`/`fin_cases` identification
and re-derives the interchangeability theorems against `Hpol`/`Cpol`. -/

namespace Thomson.ThreePoint.Cert

open Thomson Thomson.TriLocalCert

theorem dirR_eq (k : Fin 10) :
    dirR k = ![e0, e1, e2, e01, e02, e12, f01, f02, f12, e012] k := by
  fin_cases k <;> funext a <;> fin_cases a <;>
    simp [dirR, dirZ, e0, e1, e2, e01, e02, e12, f01, f02, f12, e012]

theorem Hs_eq_Hpol (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) :
    Hs p τ = Hpol (fun v => rayφ2 p τ v 0) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Hs, Hpol, HpolV, Qv, dirR_eq, e0, e1, e2, e01, e02, e12]

theorem Cs_eq_Cpol (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) :
    Cs p τ = Cpol (fun v => rayφ3 p τ v 0) := by
  funext a b c
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [Cs, Cpol, Svals, msIdx, Kv, dirR_eq, e0, e1, e2, e01, e02, e12, f01, f02, f12, e012] <;>
    ring

theorem Qf_Hpol (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    Thomson.TriLocalCert.Qf (Hpol (fun v => rayφ2 p τ v 0)) δ = rayφ2 p τ δ 0 := by
  rw [← Hs_eq_Hpol]; exact Qf_Hs p τ δ

theorem Kf_Cpol (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    Thomson.TriLocalCert.Kf (Cpol (fun v => rayφ3 p τ v 0)) δ = rayφ3 p τ δ 0 := by
  rw [← Cs_eq_Cpol]; exact Kf_Cs p τ δ

theorem bracket_H_eq_pol (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (M : ℝ) (δ : Fin 3 → ℝ) :
    Thomson.TriLocalCert.bracket (H p τ) (C p τ) M δ =
      Thomson.TriLocalCert.bracket (Hpol (fun v => rayφ2 p τ v 0)) (Cpol (fun v => rayφ3 p τ v 0))
        M δ := by
  rw [← Hs_eq_Hpol, ← Cs_eq_Cpol]; exact bracket_H_eq p τ M δ

end Thomson.ThreePoint.Cert
