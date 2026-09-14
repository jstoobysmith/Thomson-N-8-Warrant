import Thomson.TriangleGlobal.CertIntervals
import Thomson.PSD.Dom

/-! # Task 2, step 2: the check of one block

For block `k` (size `n = 9 − k`) the data are a factor `L` and a diagonal `d` on the fixed-point
grid `10⁻⁴⁰` (`Thomson/PSD/Block*.lean`, the `LDLᵀ` factors of `Hp pivotsNum k − μ·P`).  Then

`Hp p k = L D Lᵀ + N`, `N := Hp p k − L D Lᵀ`,

and `L D Lᵀ ⪰ 0` as soon as `d ≥ 0`, while `N ≈ μ·P` is diagonally dominant.  `blockOK` checks
both, `N` through Task 5b's enclosure `HIe` of `Hp p k`, valid for every `p` within `10⁻¹²` of
`pivotsNum` (`ITMem_HIe`).  So the check covers the true certificate given Task 1b. -/

namespace Thomson.PSD

open Thomson Thomson.Tri5b Matrix

/-- Entry `(a, r)` of a table. -/
def zget (L : List (List ℤ)) (a r : ℕ) : ℤ := (L.getD a []).getD r 0

/-- Entry `r` of a list. -/
def dget (d : List ℤ) (r : ℕ) : ℤ := d.getD r 0

/-- An upper bound (× `SCALE`) for `|x|` on an interval. -/
def aHi (I : Itv) : ℤ := max I.hi (-I.lo)

theorem abs_le_aHi {I : Itv} {x : ℝ} (h : I.Mem x) : |x| * SCALE ≤ (aHi I : ℝ) := by
  obtain ⟨h1, h2⟩ := h
  have hS := SCALE_pos'
  have e : |x| * SCALE = |x * SCALE| := by rw [abs_mul, abs_of_pos hS]
  rw [e, aHi]
  push_cast
  rcases le_total 0 (x * SCALE) with h | h
  · rw [abs_of_nonneg h]; exact le_max_of_le_left h2
  · rw [abs_of_nonpos h]; exact le_max_of_le_right (by linarith)

/-- `N = Hp p k − L D Lᵀ`, entry `(a, b)`, enclosed. -/
def NI (k : Fin 6) (L : List (List ℤ)) (d : List ℤ) (a b : Fin (9 - (k : ℕ))) : Itv :=
  Itv.sub (HIe k a b) (Itv.sumL ((List.finRange (9 - (k : ℕ))).map fun (r : Fin (9 - (k : ℕ))) =>
    Itv.mul (Itv.mul (Itv.cst (zget L a r)) (Itv.cst (dget d r))) (Itv.cst (zget L b r))))

/-- **The check of block `k`.**  `d ≥ 0`, and every row of `N` is diagonally dominant. -/
def blockOK (k : Fin 6) (L : List (List ℤ)) (d : List ℤ) : Bool :=
  (List.finRange (9 - (k : ℕ))).all (fun (r : Fin (9 - (k : ℕ))) => decide (0 ≤ dget d r)) &&
  (List.finRange (9 - (k : ℕ))).all fun a =>
    decide (((List.finRange (9 - (k : ℕ))).map fun b => aHi (NI k L d a b)).sum
      ≤ 2 * (NI k L d a a).lo)

/-- The real factor. -/
noncomputable def Lr (k : Fin 6) (L : List (List ℤ)) : Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ :=
  Matrix.of fun a r => (zget L a r : ℝ) / SCALE

/-- The real diagonal. -/
noncomputable def dr (k : Fin 6) (d : List ℤ) : Fin (9 - (k : ℕ)) → ℝ := fun r => (dget d r : ℝ) / SCALE

theorem LDLt_apply (k : Fin 6) (L : List (List ℤ)) (d : List ℤ) (a b : Fin (9 - (k : ℕ))) :
    (Lr k L * diagonal (dr k d) * (Lr k L)ᵀ) a b
      = ∑ r : Fin (9 - (k : ℕ)),
        (zget L a r : ℝ) / SCALE * ((dget d r : ℝ) / SCALE) * ((zget L b r : ℝ) / SCALE) := by
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply, Lr, dr,
    Matrix.of_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem mem_NI {p : Fin 24 → ℝ} (hclose : ∀ j, |p j - pivotsNum j| ≤ (EPS : ℝ) / SCALE)
    (k : Fin 6) (L : List (List ℤ)) (d : List ℤ) (a b : Fin (9 - (k : ℕ))) :
    (NI k L d a b).Mem ((Hp p k - Lr k L * diagonal (dr k d) * (Lr k L)ᵀ) a b) := by
  rw [Matrix.sub_apply, LDLt_apply]
  unfold NI
  refine Itv.mem_sub (ITMem_HIe hclose k a b) (Itv.mem_sum_fin
    (fun r => Itv.mul (Itv.mul (Itv.cst (zget L a r)) (Itv.cst (dget d r))) (Itv.cst (zget L b r)))
    (fun r => (zget L a r : ℝ) / SCALE * ((dget d r : ℝ) / SCALE) * ((zget L b r : ℝ) / SCALE))
    fun r => ?_)
  exact Itv.mem_mul (Itv.mem_mul (Itv.mem_cst _) (Itv.mem_cst _)) (Itv.mem_cst _)

/-- **Soundness of the check.** -/
theorem posSemidef_of_blockOK {p : Fin 24 → ℝ}
    (hclose : ∀ j, |p j - pivotsNum j| ≤ 1 / 10 ^ 12) {k : Fin 6} {L : List (List ℤ)}
    {d : List ℤ} (hok : blockOK k L d = true) : (Hp p k).PosSemidef := by
  have hS : (0 : ℝ) < SCALE := SCALE_pos'
  have hc : ∀ j, |p j - pivotsNum j| ≤ (EPS : ℝ) / SCALE := by
    intro j; rw [show (EPS : ℝ) / SCALE = 1 / 10 ^ 12 by norm_num [EPS, SCALE]]; exact hclose j
  simp only [blockOK, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq] at hok
  obtain ⟨hd, hdom⟩ := hok
  set LL := Lr k L * diagonal (dr k d) * (Lr k L)ᵀ with hLL
  have hsplit : Hp p k = LL + (Hp p k - LL) := by abel
  rw [hsplit]
  refine PosSemidef.add ?_ ?_
  · -- `L D Lᵀ`
    have hD : (diagonal (dr k d)).PosSemidef :=
      posSemidef_diagonal_iff.mpr fun r => div_nonneg (by exact_mod_cast hd r) hS.le
    have := hD.mul_mul_conjTranspose_same (Lr k L)
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  · -- `N`, diagonally dominant
    refine posSemidef_of_dom _ ?_ fun a => ?_
    · rw [Matrix.transpose_sub, Tri5b.Hp_symm, hLL, Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose, Matrix.diagonal_transpose, Matrix.mul_assoc]
    · have hrow : ∑ b, |(Hp p k - LL) a b| * SCALE ≤ ((∑ b, aHi (NI k L d a b) : ℤ) : ℝ) := by
        push_cast
        exact Finset.sum_le_sum fun b _ => abs_le_aHi (mem_NI hc k L d a b)
      have hsum : (∑ b, aHi (NI k L d a b) : ℤ) ≤ 2 * (NI k L d a a).lo := by
        rw [Fin.sum_univ_def]; exact hdom a
      have hdiag := (mem_NI hc k L d a a).1
      have hsum' : ((∑ b, aHi (NI k L d a b) : ℤ) : ℝ) ≤ 2 * ((NI k L d a a).lo : ℝ) := by
        exact_mod_cast hsum
      rw [← Finset.sum_mul] at hrow
      have : (∑ b, |(Hp p k - LL) a b|) * SCALE ≤ (2 * (Hp p k - LL) a a) * SCALE := by
        nlinarith
      exact le_of_mul_le_mul_right this hS

end Thomson.PSD
