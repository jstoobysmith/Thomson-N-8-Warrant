import Thomson.Pivots.Diag

/-! # Task 1b, step 4: the derivative rows

`Thomson.Certificate.Perturb` reduces every entry of `pivotMatrix` to a value of `Gh j` — for the
eight derivative rows, to a *derivative* of one.  Those derivatives are taken here: the chord
variable enters `Gh` through `1 − x²/2`, so each is a product rule and a chain rule away from the
partial derivatives of the tensor (`evD1`, `evD2`, `evD3`, and `evDiagD` for the pair rows, where
the last two arguments move together). -/

namespace Thomson.Task1b

open Thomson Thomson.Tri5b

noncomputable def cG (j : Fin 24) : RT := cF (Mmat (eHmat j))

theorem Gh_eq_ev (j : Fin 24) (u v t : ℝ) : Gh j u v t = ev (cG j) u v t := by
  rw [Gh_eq_Fh, cG, ev_cF_eq_Fh' (eHmat_symm j)]

theorem hasDerivAt_sub_sq (x : ℝ) : HasDerivAt (fun y : ℝ => 1 - y ^ 2 / 2) (-x) x :=
  (((hasDerivAt_pow 2 x).div_const 2).const_sub (1 : ℝ)).congr_deriv (by norm_num)

theorem hasDerivAt_sub_sq_shift (a : ℝ) :
    HasDerivAt (fun d : ℝ => 1 - (a + d) ^ 2 / 2) (-a) 0 := by
  have h0 : HasDerivAt (fun d : ℝ => a + d) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add a
  exact ((hasDerivAt_sub_sq (a + 0)).comp 0 h0).congr_deriv (by ring)

theorem pairDer_eq (j : Fin 24) (s : ℝ) :
    deriv (fun x => -(3 * x) * Gh j 1 (1 - x ^ 2 / 2) (1 - x ^ 2 / 2)) s
      = -3 * ev (cG j) 1 (1 - s ^ 2 / 2) (1 - s ^ 2 / 2)
        + 3 * s ^ 2 * evDiagD (cG j) (1 - s ^ 2 / 2) := by
  have hfun : (fun x => -(3 * x) * Gh j 1 (1 - x ^ 2 / 2) (1 - x ^ 2 / 2))
      = fun x => -(3 * x) * ev (cG j) 1 (1 - x ^ 2 / 2) (1 - x ^ 2 / 2) :=
    funext fun x => by rw [Gh_eq_ev]
  rw [hfun]
  have hcomp0 := (hasDerivAt_evDiag (cG j) (1 - s ^ 2 / 2)).comp s (hasDerivAt_sub_sq s)
  have hcomp : HasDerivAt (fun x => ev (cG j) 1 (1 - x ^ 2 / 2) (1 - x ^ 2 / 2))
      (evDiagD (cG j) (1 - s ^ 2 / 2) * (-s)) s := hcomp0
  have hp : HasDerivAt (fun x : ℝ => -(3 * x)) (-3) s :=
    (((hasDerivAt_id s).const_mul (3 : ℝ)).neg).congr_deriv (by ring)
  rw [(hp.fun_mul hcomp).deriv]
  ring

theorem triD_eq_1 (j : Fin 24) (a b c3 : ℝ) :
    deriv (fun d => -((a + d) * b * c3)
        * Gh j (1 - (a + d) ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2)) 0
      = -(b * c3) * ev (cG j) (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2)
        + a * a * b * c3 * evD1 (cG j) (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2) := by
  have hfun : (fun d => -((a + d) * b * c3)
      * Gh j (1 - (a + d) ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2))
      = fun d => -((a + d) * b * c3)
        * ev (cG j) (1 - (a + d) ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2) :=
    funext fun d => by rw [Gh_eq_ev]
  rw [hfun]
  have hcomp0 := (hasDerivAt_evD1 (cG j) (1 - (a + 0) ^ 2 / 2) (1 - b ^ 2 / 2)
    (1 - c3 ^ 2 / 2)).comp 0 (hasDerivAt_sub_sq_shift a)
  have hcomp : HasDerivAt (fun d => ev (cG j) (1 - (a + d) ^ 2 / 2) (1 - b ^ 2 / 2)
      (1 - c3 ^ 2 / 2))
      (evD1 (cG j) (1 - (a + 0) ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2) * (-a)) 0 := hcomp0
  have hP : HasDerivAt (fun d : ℝ => -((a + d) * b * c3)) (-(b * c3)) 0 := by
    have h0 : HasDerivAt (fun d : ℝ => a + d) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add a
    exact (((h0.mul_const b).mul_const c3).neg).congr_deriv (by ring)
  rw [(hP.fun_mul hcomp).deriv]
  simp only [add_zero]
  ring

theorem triD_eq_2 (j : Fin 24) (a b c3 : ℝ) :
    deriv (fun d => -(a * (b + d) * c3)
        * Gh j (1 - a ^ 2 / 2) (1 - (b + d) ^ 2 / 2) (1 - c3 ^ 2 / 2)) 0
      = -(a * c3) * ev (cG j) (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2)
        + a * b * b * c3 * evD2 (cG j) (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2) := by
  have hfun : (fun d => -(a * (b + d) * c3)
      * Gh j (1 - a ^ 2 / 2) (1 - (b + d) ^ 2 / 2) (1 - c3 ^ 2 / 2))
      = fun d => -(a * (b + d) * c3)
        * ev (cG j) (1 - a ^ 2 / 2) (1 - (b + d) ^ 2 / 2) (1 - c3 ^ 2 / 2) :=
    funext fun d => by rw [Gh_eq_ev]
  rw [hfun]
  have hcomp0 := (hasDerivAt_evD2 (cG j) (1 - a ^ 2 / 2) (1 - (b + 0) ^ 2 / 2)
    (1 - c3 ^ 2 / 2)).comp 0 (hasDerivAt_sub_sq_shift b)
  have hcomp : HasDerivAt (fun d => ev (cG j) (1 - a ^ 2 / 2) (1 - (b + d) ^ 2 / 2)
      (1 - c3 ^ 2 / 2))
      (evD2 (cG j) (1 - a ^ 2 / 2) (1 - (b + 0) ^ 2 / 2) (1 - c3 ^ 2 / 2) * (-b)) 0 := hcomp0
  have hP : HasDerivAt (fun d : ℝ => -(a * (b + d) * c3)) (-(a * c3)) 0 := by
    have h0 : HasDerivAt (fun d : ℝ => b + d) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add b
    exact (((h0.const_mul a).mul_const c3).neg).congr_deriv (by ring)
  rw [(hP.fun_mul hcomp).deriv]
  simp only [add_zero]
  ring

theorem triD_eq_3 (j : Fin 24) (a b c3 : ℝ) :
    deriv (fun d => -(a * b * (c3 + d))
        * Gh j (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - (c3 + d) ^ 2 / 2)) 0
      = -(a * b) * ev (cG j) (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2)
        + a * b * c3 * c3 * evD3 (cG j) (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2) := by
  have hfun : (fun d => -(a * b * (c3 + d))
      * Gh j (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - (c3 + d) ^ 2 / 2))
      = fun d => -(a * b * (c3 + d))
        * ev (cG j) (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - (c3 + d) ^ 2 / 2) :=
    funext fun d => by rw [Gh_eq_ev]
  rw [hfun]
  have hcomp0 := (hasDerivAt_evD3 (cG j) (1 - a ^ 2 / 2) (1 - b ^ 2 / 2)
    (1 - (c3 + 0) ^ 2 / 2)).comp 0 (hasDerivAt_sub_sq_shift c3)
  have hcomp : HasDerivAt (fun d => ev (cG j) (1 - a ^ 2 / 2) (1 - b ^ 2 / 2)
      (1 - (c3 + d) ^ 2 / 2))
      (evD3 (cG j) (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - (c3 + 0) ^ 2 / 2) * (-c3)) 0 := hcomp0
  have hP : HasDerivAt (fun d : ℝ => -(a * b * (c3 + d))) (-(a * b)) 0 := by
    have h0 : HasDerivAt (fun d : ℝ => c3 + d) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add c3
    exact ((h0.const_mul (a * b)).neg).congr_deriv (by ring)
  rw [(hP.fun_mul hcomp).deriv]
  simp only [add_zero]
  ring

end Thomson.Task1b
