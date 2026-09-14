import Thomson.Pivots.GTensor

/-! # Task 1b, step 3: the diagonal `v = t`

The pair rows evaluate `F` at `(1, w, w)`: both of the last two arguments move together, so their
derivative is not one of `evD2`, `evD3` but the derivative of the single-variable polynomial
`y ↦ ev c 1 y y`, whose exponent is `q + r`. -/

namespace Thomson.Task1b

open Thomson Thomson.Tri5b Finset

/-- `ev c 1 y y`, with the two exponents added. -/
noncomputable def evDiag (c : RT) (y : ℝ) : ℝ :=
  ∑ i : Fin 9, ∑ q : Fin 9, ∑ r : Fin 9, c i q r * (1 ^ (i : ℕ) * y ^ ((q : ℕ) + (r : ℕ)))

/-- its derivative -/
noncomputable def evDiagD (c : RT) (y : ℝ) : ℝ :=
  ∑ i : Fin 9, ∑ q : Fin 9, ∑ r : Fin 9,
    c i q r * (1 ^ (i : ℕ) * ((((q : ℕ) + (r : ℕ) : ℕ) : ℝ) * y ^ ((q : ℕ) + (r : ℕ) - 1)))

theorem ev_one_diag (c : RT) (y : ℝ) : ev c 1 y y = evDiag c y := by
  unfold ev evDiag
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun r _ => ?_
  rw [pow_add]
  ring

theorem hasDerivAt_evDiag (c : RT) (y : ℝ) :
    HasDerivAt (fun z => ev c 1 z z) (evDiagD c y) y := by
  have e : (fun z => ev c 1 z z) = fun z => evDiag c z := funext fun z => ev_one_diag c z
  rw [e]
  unfold evDiag evDiagD
  refine HasDerivAt.fun_sum fun i _ => ?_
  refine HasDerivAt.fun_sum fun q _ => ?_
  refine HasDerivAt.fun_sum fun r _ => ?_
  have h1 : HasDerivAt (fun z : ℝ => z ^ ((q : ℕ) + (r : ℕ)))
      ((((q : ℕ) + (r : ℕ) : ℕ) : ℝ) * y ^ ((q : ℕ) + (r : ℕ) - 1)) y := hasDerivAt_pow _ _
  have h2 := (h1.const_mul (1 ^ (i : ℕ) : ℝ)).const_mul (c i q r)
  convert h2 using 1
  try ring

/-! ### the interval versions -/

def evIDiag (C : IT) (Y : Itv) : Itv :=
  Itv.sumL ((List.finRange 9).map (fun i : Fin 9 =>
    Itv.sumL ((List.finRange 9).map (fun q : Fin 9 =>
      Itv.sumL ((List.finRange 9).map (fun r : Fin 9 =>
        Itv.mul (C i q r)
          (Itv.mul (Itv.npow Itv.one (i : ℕ)) (Itv.npow Y ((q : ℕ) + (r : ℕ))))))))))

def evIDiagD (C : IT) (Y : Itv) : Itv :=
  Itv.sumL ((List.finRange 9).map (fun i : Fin 9 =>
    Itv.sumL ((List.finRange 9).map (fun q : Fin 9 =>
      Itv.sumL ((List.finRange 9).map (fun r : Fin 9 =>
        Itv.mul (C i q r)
          (Itv.mul (Itv.npow Itv.one (i : ℕ))
            (Itv.mul (natI ((q : ℕ) + (r : ℕ)))
              (Itv.npow Y ((q : ℕ) + (r : ℕ) - 1))))))))))

theorem mem_evIDiag {C : IT} {c : RT} (hC : ITMem C c) {Y : Itv} {y : ℝ} (hy : Y.Mem y) :
    (evIDiag C Y).Mem (evDiag c y) := by
  unfold evIDiag evDiag
  refine Itv.mem_sum_fin _ _ fun i => Itv.mem_sum_fin _ _ fun q => Itv.mem_sum_fin _ _ fun r => ?_
  exact Itv.mem_mul (hC i q r)
    (Itv.mem_mul (Itv.mem_npow Itv.mem_one _) (Itv.mem_npow hy _))

theorem mem_evIDiagD {C : IT} {c : RT} (hC : ITMem C c) {Y : Itv} {y : ℝ} (hy : Y.Mem y) :
    (evIDiagD C Y).Mem (evDiagD c y) := by
  unfold evIDiagD evDiagD
  refine Itv.mem_sum_fin _ _ fun i => Itv.mem_sum_fin _ _ fun q => Itv.mem_sum_fin _ _ fun r => ?_
  exact Itv.mem_mul (hC i q r)
    (Itv.mem_mul (Itv.mem_npow Itv.mem_one _)
      (Itv.mem_mul (mem_natI _) (Itv.mem_npow hy _)))

end Thomson.Task1b
