import Thomson.Task1b.System

/-! # Task 1b, step 10: the check

With `E := I − N·pivotMatrix` and `r := rowFun · pivotsNum`, two numbers decide everything:
`η = max_i Σ_j |E_ij|` and `ρ = max_i |(N r)_i|`.  They are computed here on the enclosures —
`η ≤ 10⁻¹¹` (it is `5.25·10⁻¹²`) and `ρ ≤ 10⁻²¹` (it is `4.0·10⁻²²`) — in one `native_decide`
of about a minute and a half. -/

namespace Thomson.Task1b

open Thomson Thomson.Tri5b Matrix

/-- The enclosure of `(N·pivotMatrix)_ij`. -/
def NMI (i j : Fin 24) : Itv :=
  Itv.sumL ((List.finRange 24).map fun k : Fin 24 => Itv.mul (Itv.cst (Nq i k)) (Mget k j))

/-- The enclosure of `E_ij = δ_ij − (N·pivotMatrix)_ij`. -/
def EI (i j : Fin 24) : Itv := Itv.sub (if i = j then Itv.one else Itv.zero) (NMI i j)

/-- The enclosure of `(N·r)_i`. -/
def NRI (i : Fin 24) : Itv :=
  Itv.sumL ((List.finRange 24).map fun k : Fin 24 => Itv.mul (Itv.cst (Nq i k)) (Rget k))

/-- `10⁻¹¹` -/
def ETA : ℤ := 100000000000000000000000000000
/-- `10⁻²¹` -/
def RHO : ℤ := 10000000000000000000

def checkOK : Bool :=
  (List.finRange 24).all (fun i => decide (∑ j : Fin 24, maxabs (EI i j) ≤ ETA)) &&
    (List.finRange 24).all (fun i => decide (maxabs (NRI i) ≤ RHO))

theorem check_ok : checkOK = true := by native_decide

/-! ### What the check means -/

theorem mem_NMI (i j : Fin 24) : (NMI i j).Mem ((Nmat * pivotMatrix) i j) := by
  rw [Matrix.mul_apply]
  unfold NMI
  refine Itv.mem_sum_fin _ _ fun k => ?_
  exact Itv.mem_mul (Itv.mem_cst _) (mem_Mget k j)

theorem mem_EI (i j : Fin 24) :
    (EI i j).Mem (((1 : Matrix (Fin 24) (Fin 24) ℝ) - Nmat * pivotMatrix) i j) := by
  rw [Matrix.sub_apply, Matrix.one_apply]
  unfold EI
  refine Itv.mem_sub ?_ (mem_NMI i j)
  split_ifs
  · exact Itv.mem_one
  · exact Itv.mem_zero

theorem mem_NRI (i : Fin 24) :
    (NRI i).Mem ((Nmat *ᵥ fun k => rowFun k pivotsNum) i) := by
  simp only [Matrix.mulVec, dotProduct]
  unfold NRI
  refine Itv.mem_sum_fin _ _ fun k => ?_
  exact Itv.mem_mul (Itv.mem_cst _) (mem_Rget k)

theorem abs_le_of_mem {I : Itv} {x : ℝ} (h : I.Mem x) : |x| ≤ (maxabs I : ℝ) / SCALE := by
  have hS := SCALE_pos'
  have h1 := abs_le_maxabs h
  rw [abs_mul, abs_of_pos hS] at h1
  rw [le_div_iff₀ hS]; exact h1

/-- **The two estimates.** -/
theorem estimates :
    (∀ i : Fin 24, ∑ j : Fin 24, |((1 : Matrix (Fin 24) (Fin 24) ℝ) - Nmat * pivotMatrix) i j|
        ≤ (ETA : ℝ) / SCALE) ∧
      ∀ i : Fin 24, |(Nmat *ᵥ fun k => rowFun k pivotsNum) i| ≤ (RHO : ℝ) / SCALE := by
  have h := check_ok
  simp only [checkOK, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq] at h
  obtain ⟨hE, hR⟩ := h
  have hS := SCALE_pos'
  constructor
  · intro i
    calc ∑ j : Fin 24, |((1 : Matrix (Fin 24) (Fin 24) ℝ) - Nmat * pivotMatrix) i j|
        ≤ ∑ j : Fin 24, (maxabs (EI i j) : ℝ) / SCALE :=
          Finset.sum_le_sum fun j _ => abs_le_of_mem (mem_EI i j)
      _ = ((∑ j : Fin 24, maxabs (EI i j) : ℤ) : ℝ) / SCALE := by
          rw [← Finset.sum_div]; push_cast; rfl
      _ ≤ (ETA : ℝ) / SCALE := by
          gcongr
          exact_mod_cast hE i
  · intro i
    calc |(Nmat *ᵥ fun k => rowFun k pivotsNum) i| ≤ (maxabs (NRI i) : ℝ) / SCALE :=
          abs_le_of_mem (mem_NRI i)
      _ ≤ (RHO : ℝ) / SCALE := by
          gcongr
          exact_mod_cast hR i

end Thomson.Task1b
