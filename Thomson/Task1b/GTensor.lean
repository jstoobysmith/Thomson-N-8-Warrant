import Thomson.Task1b.Eval
import Thomson.ThreePoint.Perturb
import Thomson.Tri5b.CertIntervals

/-! # Task 1b, step 2: the coefficient tensor of `Gh j`

Every entry of `pivotMatrix` is a value (or a derivative) of `Gh j`, the linear part of the
certificate's `F` in pivot `j` (`Thomson.ThreePoint.Perturb`).  And `Gh j` is literally `Fh` of the
*indicator* block of the slot of `j`, so Task 5b's bridge — the coefficient tensor of `Fh H`, built
from `M_k = B_k H_k B_kᵀ` and the tensors of the `Q_k` — applies verbatim, once it is freed of the
`H = Hp p` it was stated for.  The enclosure of `B` (`Thomson.Tri5b.BI`, from `u*` to 32 digits) is
reused unchanged. -/

namespace Thomson.Task1b

open Thomson Thomson.Tri5b Finset Matrix

/-! ### `Fh`'s tensor, for any symmetric block -/

theorem Mmat_symm' {H : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ}
    (hH : ∀ k, (H k)ᵀ = H k) (k : Fin 6) : (Mmat H k)ᵀ = Mmat H k := by
  simp only [Mmat, Matrix.transpose_mul, Matrix.transpose_transpose, hH, Matrix.mul_assoc]

theorem Fh_eq_wsum3 {H : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ}
    (hH : ∀ k, (H k)ᵀ = H k) (u v t : ℝ) :
    Fh H u v t = (1 / 3 : ℝ) * ∑ k : Fin 6,
      (wpoly (Mmat H k) u v * Q3 (k : ℕ) u v t
        + wpoly (Mmat H k) u t * Q3 (k : ℕ) u t v
        + wpoly (Mmat H k) v t * Q3 (k : ℕ) v t u) := by
  rw [Fh_eq_wsum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← wpoly_comm (Mmat_symm' hH k) u v, ← wpoly_comm (Mmat_symm' hH k) u t,
    ← wpoly_comm (Mmat_symm' hH k) v t]
  ring

/-- **The bridge, for any symmetric block.** -/
theorem ev_cF_eq_Fh' {H : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ}
    (hH : ∀ k, (H k)ᵀ = H k) (u v t : ℝ) : ev (cF (Mmat H)) u v t = Fh H u v t := by
  rw [ev_cF, Fh_eq_wsum3 hH]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [wpoly_mul, wpoly_mul, wpoly_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The interval matrix product, for any block enclosure. -/
theorem ITMem_MI' {BI HI : ℕ → ℕ → ℕ → Itv}
    {H : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ}
    (hB : ∀ (k : Fin 6) (i a : Fin (9 - (k : ℕ))), (BI (k : ℕ) (i : ℕ) (a : ℕ)).Mem (B k i a))
    (hH : ∀ (k : Fin 6) (a b : Fin (9 - (k : ℕ))), (HI (k : ℕ) (a : ℕ) (b : ℕ)).Mem (H k a b))
    (k : Fin 6) (i j : Fin (9 - (k : ℕ))) : (MI BI HI k i j).Mem (Mmat H k i j) := by
  rw [Mmat_apply]
  unfold MI
  refine Itv.mem_sum_fin _ _ fun a => ?_
  refine Itv.mem_sum_fin _ _ fun b => ?_
  exact Itv.mem_mul (Itv.mem_mul (hB k i a) (hH k a b)) (hB k j b)

/-- The enclosure of `B` is the one Task 5b uses. -/
theorem ITMem_BI' (k : Fin 6) (i a : Fin (9 - (k : ℕ))) :
    (BI (k : ℕ) (i : ℕ) (a : ℕ)).Mem (B k i a) := by
  have hk : (k : ℕ) < 6 := k.isLt
  have hi : (i : ℕ) < 9 := by have := i.isLt; omega
  have ha : (a : ℕ) < 9 := by have := a.isLt; omega
  exact ITMem_BI _ _ _ hk hi ha

/-! ### The indicator block of a pivot -/

theorem eH_symm (j : Fin 24) (k a b : ℕ) : eH j k b a = eH j k a b := by
  unfold eH
  by_cases h : slot j = (k, a, b) ∨ slot j = (k, b, a)
  · rw [if_pos (Or.symm h), if_pos h]
  · rw [if_neg (fun hc => h (Or.symm hc)), if_neg h]

/-- The block whose only nonzero entries are the slot of pivot `j` (and its mirror). -/
noncomputable def eHmat (j : Fin 24) (k : Fin 6) :
    Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ :=
  Matrix.of fun a b => eH j (k : ℕ) (a : ℕ) (b : ℕ)

theorem eHmat_symm (j : Fin 24) : ∀ k, (eHmat j k)ᵀ = eHmat j k := by
  intro k; ext a b
  show eH j (k : ℕ) (b : ℕ) (a : ℕ) = eH j (k : ℕ) (a : ℕ) (b : ℕ)
  exact eH_symm j (k : ℕ) (a : ℕ) (b : ℕ)

/-- `Gh j` is `Fh` of that block. -/
theorem Gh_eq_Fh (j : Fin 24) (u v t : ℝ) : Gh j u v t = Fh (eHmat j) u v t := rfl

/-! ### and its tensor -/

/-- The interval tensor of `Gh j`. -/
def GIT (j : Fin 24) : IT := CF (MI BI (eHI j))

theorem ITMem_GIT (j : Fin 24) : ITMem (GIT j) (cF (Mmat (eHmat j))) :=
  ITMem_CF _ (ITMem_MI' ITMem_BI' (fun k a b => ITMem_eHI j (k : ℕ) (a : ℕ) (b : ℕ)))

/-- **The value of `Gh j` is enclosed by evaluating its tensor.** -/
theorem mem_evI_GIT (j : Fin 24) {U V T : Itv} {u v t : ℝ}
    (hu : U.Mem u) (hv : V.Mem v) (ht : T.Mem t) :
    (evI (GIT j) U V T).Mem (Gh j u v t) := by
  rw [Gh_eq_Fh, ← ev_cF_eq_Fh' (eHmat_symm j)]
  exact mem_evI (ITMem_GIT j) hu hv ht

end Thomson.Task1b
