import Thomson.TriangleLocal.Patch
import Thomson.TriangleLocal.Ray
import Thomson.TriangleLocal.Calculus.TriLocalHC3
import Thomson.TriangleLocal.Calculus.TriLocalDeriv4

/-! # Task 5a: polarization bridge to the peer session's numeric certificate

`Thomson/TriangleLocal/{Patch,Jet,Ray}.lean` are the peer session's files (main tree), copied
verbatim into this worktree so they can be imported (this worktree cannot see the main tree's
filesystem directly); they are not edited. This file supplies exactly the interface they specified:
`Hs`/`Cs`, the polarization reconstruction of the Hessian/cubic-form coefficients from `rayφ2`/
`rayφ3` evaluated at 10 fixed directions (matching what their interval jets will enclose), together
with the identities showing this reconstruction is interchangeable with `TriLocalHC.lean`/
`TriLocalHC3.lean`'s direct (unsymmetrized) `H`/`C`, and the ray bridge to their `Ray.lean`. -/

namespace Thomson.ThreePoint.Cert

open Thomson Thomson.TriLocalCert

/-! ## Ray bridge -/

theorem rayR_eq_rayP (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    rayR p τ δ = rayP p τ δ := rfl

theorem rayφ2_eq_deriv2 (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    rayφ2 p τ δ 0 = deriv (deriv (rayR p τ δ)) 0 := by rw [rayR_eq_rayP]; rfl

theorem rayφ3_eq_deriv3 (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    rayφ3 p τ δ 0 = deriv (deriv (deriv (rayR p τ δ))) 0 := by rw [rayR_eq_rayP]; rfl

theorem rayφ4_eq_deriv4 (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) (x : ℝ) :
    rayφ4 p τ δ x = deriv (deriv (deriv (deriv (rayR p τ δ)))) x := by rw [rayR_eq_rayP]; rfl

/-! ## Fixed directions and the polarization reconstruction -/

noncomputable def Qv (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (v : Fin 3 → ℝ) : ℝ := rayφ2 p τ v 0
noncomputable def Kv (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (v : Fin 3 → ℝ) : ℝ := rayφ3 p τ v 0

def e0 : Fin 3 → ℝ := ![1, 0, 0]
def e1 : Fin 3 → ℝ := ![0, 1, 0]
def e2 : Fin 3 → ℝ := ![0, 0, 1]
def e01 : Fin 3 → ℝ := ![1, 1, 0]
def e02 : Fin 3 → ℝ := ![1, 0, 1]
def e12 : Fin 3 → ℝ := ![0, 1, 1]
def f01 : Fin 3 → ℝ := ![1, -1, 0]
def f02 : Fin 3 → ℝ := ![1, 0, -1]
def f12 : Fin 3 → ℝ := ![0, 1, -1]
def e012 : Fin 3 → ℝ := ![1, 1, 1]

/-- The Hessian, reconstructed by polarization from `Qv` at 6 directions. Symmetric by
construction. -/
noncomputable def Hs (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) : Fin 3 → Fin 3 → ℝ :=
  let h01 := (Qv p τ e01 - Qv p τ e0 - Qv p τ e1) / 2
  let h02 := (Qv p τ e02 - Qv p τ e0 - Qv p τ e2) / 2
  let h12 := (Qv p τ e12 - Qv p τ e1 - Qv p τ e2) / 2
  ![![Qv p τ e0, h01, h02], ![h01, Qv p τ e1, h12], ![h02, h12, Qv p τ e2]]

/-- The cubic form, reconstructed by polarization from `Kv` at 10 directions. Fully symmetric by
construction. -/
noncomputable def Cs (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) : Fin 3 → Fin 3 → Fin 3 → ℝ :=
  let s001 := (Kv p τ e01 - Kv p τ f01 - 2 * Kv p τ e1) / 6
  let s011 := (Kv p τ e01 + Kv p τ f01 - 2 * Kv p τ e0) / 6
  let s002 := (Kv p τ e02 - Kv p τ f02 - 2 * Kv p τ e2) / 6
  let s022 := (Kv p τ e02 + Kv p τ f02 - 2 * Kv p τ e0) / 6
  let s112 := (Kv p τ e12 - Kv p τ f12 - 2 * Kv p τ e2) / 6
  let s122 := (Kv p τ e12 + Kv p τ f12 - 2 * Kv p τ e1) / 6
  let s000 := Kv p τ e0
  let s111 := Kv p τ e1
  let s222 := Kv p τ e2
  let s012 := (Kv p τ e012 - s000 - s111 - s222 - 3 * (s001 + s011 + s002 + s022 + s112 + s122)) / 6
  ![![![s000, s001, s002], ![s001, s011, s012], ![s002, s012, s022]],
    ![![s001, s011, s012], ![s011, s111, s112], ![s012, s112, s122]],
    ![![s002, s012, s022], ![s012, s112, s122], ![s022, s122, s222]]]

/-! ## Interchangeability with `H`/`C` -/

theorem Qf_H (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    Thomson.TriLocalCert.Qf (H p τ) δ = rayφ2 p τ δ 0 := by
  rw [rayφ2_eq_sum]
  simp only [Thomson.TriLocalCert.Qf, Fin.sum_univ_three]
  ring

theorem Kf_C (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    Thomson.TriLocalCert.Kf (C p τ) δ = rayφ3 p τ δ 0 := by
  rw [rayφ3_eq_sum]
  simp only [Thomson.TriLocalCert.Kf, Fin.sum_univ_three]
  ring

theorem Qf_Hs (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    Thomson.TriLocalCert.Qf (Hs p τ) δ = rayφ2 p τ δ 0 := by
  have key : ∀ v : Fin 3 → ℝ, Qv p τ v = rayφ2 p τ v 0 := fun v => rfl
  rw [rayφ2_eq_sum]
  simp only [Thomson.TriLocalCert.Qf, Hs, key, rayφ2_eq_sum, e0, e1, e2, e01, e02, e12,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Fin.sum_univ_three]
  ring

theorem Kf_Cs (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    Thomson.TriLocalCert.Kf (Cs p τ) δ = rayφ3 p τ δ 0 := by
  have key : ∀ v : Fin 3 → ℝ, Kv p τ v = rayφ3 p τ v 0 := fun v => rfl
  rw [rayφ3_eq_sum]
  simp only [Thomson.TriLocalCert.Kf, Cs, key, rayφ3_eq_sum, e0, e1, e2, e01, e02, e12, f01, f02,
    f12, e012, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Fin.sum_univ_three]
  ring

theorem bracket_H_eq (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (M : ℝ) (δ : Fin 3 → ℝ) :
    Thomson.TriLocalCert.bracket (H p τ) (C p τ) M δ =
      Thomson.TriLocalCert.bracket (Hs p τ) (Cs p τ) M δ := by
  unfold Thomson.TriLocalCert.bracket
  rw [Qf_H, Kf_C, Qf_Hs, Kf_Cs]

end Thomson.ThreePoint.Cert
