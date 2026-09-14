import Thomson.TriangleGlobal.QTensor

/-! # Task 5b, step 14: the coefficient tensor of `F`

`MForm.Fh_Hp_eq_wsum` writes

`F = (1/3) Σ_k Σ_{i,j} M_k[i,j] · (uⁱ vʲ Q_k(u,v,t) + uⁱ tʲ Q_k(u,t,v) + vⁱ tʲ Q_k(v,t,u))`,

with `M_k = B_k (Hp pivotsNum)_k B_kᵀ` constant.  Each bracket is a permutation of the tensor of
`Q_k` shifted by a monomial, so the tensor of `F` is a linear combination of the six `Q`-tensors —
no polynomial multiplication anywhere.  The entries of `M_k` are the only data: they are supplied
as an interval matrix `MI` with its enclosure property. -/

namespace Thomson.Tri5b

open Thomson Finset

/-- `ev` commutes with finite sums of tensors. -/
theorem ev_finsum {ι : Type*} (s : Finset ι) (f : ι → RT) (u v t : ℝ) :
    ev (fun p q r => ∑ x ∈ s, f x p q r) u v t = ∑ x ∈ s, ev (f x) u v t := by
  unfold ev
  have step1 : ∀ p q : Fin 9,
      (∑ r, (∑ x ∈ s, f x p q r) * (u ^ (p : ℕ) * v ^ (q : ℕ) * t ^ (r : ℕ)))
        = ∑ x ∈ s, ∑ r, f x p q r * (u ^ (p : ℕ) * v ^ (q : ℕ) * t ^ (r : ℕ)) := by
    intro p q
    have h : ∀ r : Fin 9, (∑ x ∈ s, f x p q r) * (u ^ (p : ℕ) * v ^ (q : ℕ) * t ^ (r : ℕ))
        = ∑ x ∈ s, f x p q r * (u ^ (p : ℕ) * v ^ (q : ℕ) * t ^ (r : ℕ)) :=
      fun r => Finset.sum_mul _ _ _
    simp only [h]
    exact Finset.sum_comm
  simp only [step1]
  have step2 : ∀ p : Fin 9,
      (∑ q, ∑ x ∈ s, ∑ r, f x p q r * (u ^ (p : ℕ) * v ^ (q : ℕ) * t ^ (r : ℕ)))
        = ∑ x ∈ s, ∑ q, ∑ r, f x p q r * (u ^ (p : ℕ) * v ^ (q : ℕ) * t ^ (r : ℕ)) :=
    fun p => Finset.sum_comm
  simp only [step2]
  exact Finset.sum_comm

/-- The bracket attached to `(k, i, j)`. -/
noncomputable def termRT (k i j : ℕ) : RT := fun p q r =>
  (mupN (mup2N (QRT k) j) i) p q r + (mupN (mup3N (perm23 (QRT k)) j) i) p q r
    + (mup2N (mup3N (permCyc (QRT k)) j) i) p q r

def termIT (k i j : ℕ) : IT := fun p q r =>
  Itv.add (Itv.add ((ImupN (Imup2N (QIT k) j) i) p q r)
    ((ImupN (Imup3N (Iperm23 (QIT k)) j) i) p q r))
    ((Imup2N (Imup3N (IpermCyc (QIT k)) j) i) p q r)

theorem ITMem_termIT (k i j : ℕ) : ITMem (termIT k i j) (termRT k i j) := by
  intro p q r
  exact Itv.mem_add (Itv.mem_add
    (ITMem_mupN (ITMem_mup2N (ITMem_QIT k) j) i p q r)
    (ITMem_mupN (ITMem_mup3N (ITMem_perm23 (ITMem_QIT k)) j) i p q r))
    (ITMem_mup2N (ITMem_mup3N (ITMem_permCyc (ITMem_QIT k)) j) i p q r)

theorem ev_termRT (k : Fin 6) (i j : ℕ) (hi : (k : ℕ) + i ≤ 8) (hj : (k : ℕ) + j ≤ 8)
    (u v t : ℝ) :
    ev (termRT (k : ℕ) i j) u v t
      = u ^ i * v ^ j * Q3 (k : ℕ) u v t + u ^ i * t ^ j * Q3 (k : ℕ) u t v
        + v ^ i * t ^ j * Q3 (k : ℕ) v t u := by
  have hQ := DegAll_QRT k
  have e1 : ev (mupN (mup2N (QRT (k : ℕ)) j) i) u v t = u ^ i * (v ^ j * ev (QRT (k : ℕ)) u v t) := by
    rw [ev_mupN (Deg1_mup2N hQ.deg1 j) i hi, ev_mup2N hQ.deg2 j hj]
  have e2 : ev (mupN (mup3N (perm23 (QRT (k : ℕ))) j) i) u v t
      = u ^ i * (t ^ j * ev (perm23 (QRT (k : ℕ))) u v t) := by
    rw [ev_mupN (Deg1_mup3N hQ.perm23.deg1 j) i hi, ev_mup3N hQ.perm23.deg3 j hj]
  have e3 : ev (mup2N (mup3N (permCyc (QRT (k : ℕ))) j) i) u v t
      = v ^ i * (t ^ j * ev (permCyc (QRT (k : ℕ))) u v t) := by
    rw [ev_mup2N (Deg2_mup3N hQ.permCyc.deg2 j) i hi, ev_mup3N hQ.permCyc.deg3 j hj]
  have hsum : ev (termRT (k : ℕ) i j) u v t
      = ev (mupN (mup2N (QRT (k : ℕ)) j) i) u v t
        + ev (mupN (mup3N (perm23 (QRT (k : ℕ))) j) i) u v t
        + ev (mup2N (mup3N (permCyc (QRT (k : ℕ))) j) i) u v t := by
    unfold termRT
    rw [ev_add (fun p q r => (mupN (mup2N (QRT (k : ℕ)) j) i) p q r
        + (mupN (mup3N (perm23 (QRT (k : ℕ))) j) i) p q r)
      (mup2N (mup3N (permCyc (QRT (k : ℕ))) j) i) u v t,
      ev_add (mupN (mup2N (QRT (k : ℕ)) j) i) (mupN (mup3N (perm23 (QRT (k : ℕ))) j) i) u v t]
  rw [hsum, e1, e2, e3, ev_QRT k, ev_perm23, ev_QRT k, ev_permCyc, ev_QRT k]
  ring


/-! ### The tensor of `F` -/

variable (M : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ)

/-- One block's contribution. -/
noncomputable def cFblock (k : Fin 6) : RT := fun p q r =>
  ∑ i, ∑ j, M k i j * termRT (k : ℕ) (i : ℕ) (j : ℕ) p q r

/-- The coefficient tensor of `F`. -/
noncomputable def cF : RT := fun p q r => (1 / 3 : ℝ) * ∑ k : Fin 6, cFblock M k p q r

def CFblock (MI : (k : Fin 6) → Fin (9 - (k : ℕ)) → Fin (9 - (k : ℕ)) → Itv) (k : Fin 6) : IT :=
  fun p q r => Itv.sumL ((List.finRange (9 - (k : ℕ))).map (fun i : Fin (9 - (k : ℕ)) =>
    Itv.sumL ((List.finRange (9 - (k : ℕ))).map (fun j : Fin (9 - (k : ℕ)) =>
      Itv.mul (MI k i j) (termIT (k : ℕ) (i : ℕ) (j : ℕ) p q r)))))

def CF (MI : (k : Fin 6) → Fin (9 - (k : ℕ)) → Fin (9 - (k : ℕ)) → Itv) : IT := fun p q r =>
  Itv.mul (Itv.ofDiv 1 3) (Itv.sumL ((List.finRange 6).map (fun k => CFblock MI k p q r)))

theorem ITMem_CF {MI : (k : Fin 6) → Fin (9 - (k : ℕ)) → Fin (9 - (k : ℕ)) → Itv}
    (hMI : ∀ k i j, (MI k i j).Mem (M k i j)) : ITMem (CF MI) (cF M) := by
  intro p q r
  refine Itv.mem_mul ?_ ?_
  · have h := Itv.mem_ofDiv (n := 1) (d := 3) (by norm_num)
    norm_num at h ⊢
    exact h
  · refine Itv.mem_sum_fin _ _ fun k => ?_
    refine Itv.mem_sum_fin _ _ fun i => ?_
    refine Itv.mem_sum_fin _ _ fun j => ?_
    exact Itv.mem_mul (hMI k i j) (ITMem_termIT (k : ℕ) (i : ℕ) (j : ℕ) p q r)

theorem ev_cF (u v t : ℝ) :
    ev (cF M) u v t = (1 / 3 : ℝ) * ∑ k : Fin 6, ∑ i, ∑ j, M k i j *
      (u ^ (i : ℕ) * v ^ (j : ℕ) * Q3 (k : ℕ) u v t
        + u ^ (i : ℕ) * t ^ (j : ℕ) * Q3 (k : ℕ) u t v
        + v ^ (i : ℕ) * t ^ (j : ℕ) * Q3 (k : ℕ) v t u) := by
  unfold cF
  rw [ev_smul (1 / 3 : ℝ) (fun p q r => ∑ k : Fin 6, cFblock M k p q r) u v t,
    ev_finsum Finset.univ (fun k => cFblock M k) u v t]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold cFblock
  rw [ev_finsum Finset.univ (fun i => fun p q r => ∑ j, M k i j * termRT (k : ℕ) (i : ℕ) (j : ℕ) p q r) u v t]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ev_finsum Finset.univ (fun j => fun p q r => M k i j * termRT (k : ℕ) (i : ℕ) (j : ℕ) p q r) u v t]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ev_smul (M k i j) (termRT (k : ℕ) (i : ℕ) (j : ℕ)) u v t,
    ev_termRT k (i : ℕ) (j : ℕ) ?_ ?_]
  · have := i.isLt; have := k.isLt; omega
  · have := j.isLt; have := k.isLt; omega


theorem wpoly_mul {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) (x y Q : ℝ) :
    wpoly N x y * Q = ∑ i, ∑ j, N i j * (x ^ (i : ℕ) * y ^ (j : ℕ) * Q) := by
  unfold wpoly
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The bridge.**  The tensor built from the constant matrices `M_k` represents `F`. -/
theorem ev_cF_eq_Fh (p : Fin 24 → ℝ) (u v t : ℝ) :
    ev (cF (Mmat (Hp p))) u v t = Fh (Hp p) u v t := by
  rw [ev_cF, Fh_Hp_eq_wsum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [wpoly_mul, wpoly_mul, wpoly_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring


/-! ### The constant matrices `M_k = B_k H_k B_kᵀ` as interval data -/

/-- The interval matrix product, entry by entry. -/
def MI (BI : ℕ → ℕ → ℕ → Itv) (HI : ℕ → ℕ → ℕ → Itv) (k : Fin 6)
    (i j : Fin (9 - (k : ℕ))) : Itv :=
  Itv.sumL ((List.finRange (9 - (k : ℕ))).map (fun a : Fin (9 - (k : ℕ)) =>
    Itv.sumL ((List.finRange (9 - (k : ℕ))).map (fun b : Fin (9 - (k : ℕ)) =>
      Itv.mul (Itv.mul (BI (k : ℕ) (i : ℕ) (a : ℕ)) (HI (k : ℕ) (a : ℕ) (b : ℕ)))
        (BI (k : ℕ) (j : ℕ) (b : ℕ))))))

theorem Mmat_apply (H : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ)
    (k : Fin 6) (i j : Fin (9 - (k : ℕ))) :
    Mmat H k i j = ∑ a, ∑ b, B k i a * H k a b * B k j b := by
  unfold Mmat
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem ITMem_MI {BI HI : ℕ → ℕ → ℕ → Itv} {p : Fin 24 → ℝ}
    (hB : ∀ (k : Fin 6) (i a : Fin (9 - (k : ℕ))), (BI (k : ℕ) (i : ℕ) (a : ℕ)).Mem (B k i a))
    (hH : ∀ (k : Fin 6) (a b : Fin (9 - (k : ℕ))), (HI (k : ℕ) (a : ℕ) (b : ℕ)).Mem (Hp p k a b))
    (k : Fin 6) (i j : Fin (9 - (k : ℕ))) :
    (MI BI HI k i j).Mem (Mmat (Hp p) k i j) := by
  rw [Mmat_apply]
  unfold MI
  refine Itv.mem_sum_fin _ _ fun a => ?_
  refine Itv.mem_sum_fin _ _ fun b => ?_
  exact Itv.mem_mul (Itv.mem_mul (hB k i a) (hH k a b)) (hB k j b)

end Thomson.Tri5b
