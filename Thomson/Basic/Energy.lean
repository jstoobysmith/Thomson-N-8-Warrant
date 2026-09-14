import Mathlib

namespace Thomson
open Finset
open scoped RealInnerProductSpace

/-! ## 1. Definitions -/

noncomputable def energy {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ i, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹
def OnSphere {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) : Prop := ∀ i, ‖x i‖ = 1
def Admissible {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) : Prop :=
  OnSphere x ∧ Function.Injective x
def Separated {n : ℕ} (δ : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∀ i j, i ≠ j → δ ≤ ‖x i - x j‖

noncomputable def thomsonInf (n : ℕ) : ℝ :=
  sInf (energy '' {x : Fin n → EuclideanSpace ℝ (Fin 3) | Admissible x})

/-! ## 2. Elementary facts -/

theorem energy_nonneg {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) : 0 ≤ energy x := by
  apply Finset.sum_nonneg; intro i _; apply Finset.sum_nonneg; intro j _; positivity

/-- The junk-value trap: a collapsed configuration has energy `0`, not `∞`. -/
theorem energy_const {n : ℕ} (p : EuclideanSpace ℝ (Fin 3)) :
    energy (fun _ : Fin n => p) = 0 := by simp [energy]

theorem term_le_energy {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) {i j : Fin n}
    (hlt : i < j) : ‖x i - x j‖⁻¹ ≤ energy x := by
  have hnn : ∀ k : Fin n, k ∈ univ → 0 ≤ ∑ l ∈ Finset.Ioi k, ‖x k - x l‖⁻¹ := by
    intro k _; apply Finset.sum_nonneg; intro l _; positivity
  have inner : ‖x i - x j‖⁻¹ ≤ ∑ l ∈ Finset.Ioi i, ‖x i - x l‖⁻¹ :=
    Finset.single_le_sum (f := fun l => ‖x i - x l‖⁻¹)
      (fun l _ => inv_nonneg.mpr (norm_nonneg _)) (Finset.mem_Ioi.mpr hlt)
  exact inner.trans (Finset.single_le_sum hnn (Finset.mem_univ i))

theorem dist_ge_of_energy_le {n : ℕ} {x : Fin n → EuclideanSpace ℝ (Fin 3)} {M : ℝ}
    (hinj : Function.Injective x) (hM : energy x ≤ M) {i j : Fin n} (hij : i ≠ j) :
    M⁻¹ ≤ ‖x i - x j‖ := by
  have key : ∀ a b : Fin n, a < b → M⁻¹ ≤ ‖x a - x b‖ := by
    intro a b hab
    have hne : x a ≠ x b := fun h => (ne_of_lt hab) (hinj h)
    have hpos : 0 < ‖x a - x b‖ := by simpa [sub_eq_zero] using hne
    have h1 : ‖x a - x b‖⁻¹ ≤ M := le_trans (term_le_energy x hab) hM
    have hM0 : 0 < M := lt_of_lt_of_le (inv_pos.mpr hpos) h1
    exact (inv_le_comm₀ hpos hM0).mp h1
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · rw [← norm_sub_rev]; exact key j i h

/-! ## 3. Explicit 3-vector arithmetic -/

theorem sub_e3 (a b c d e f : ℝ) :
    (!₂[a, b, c] : EuclideanSpace ℝ (Fin 3)) - !₂[d, e, f] = !₂[a - d, b - e, c - f] := by
  ext i; fin_cases i <;> simp
theorem norm_e3 (a b c : ℝ) :
    ‖(!₂[a, b, c] : EuclideanSpace ℝ (Fin 3))‖ = Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp [Matrix.cons_val_two, Matrix.tail_cons]
theorem e3_inj {a b c d e f : ℝ}
    (h : (!₂[a, b, c] : EuclideanSpace ℝ (Fin 3)) = !₂[d, e, f]) : a = d ∧ b = e ∧ c = f := by
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v.ofLp 0) h; simpa using this
  · have := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v.ofLp 1) h; simpa using this
  · have := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v.ofLp 2) h; simpa using this

/-! ## 4. Existence of a minimiser -/

/-- Explicit admissible configuration: points `(i/n, √(1-(i/n)²), 0)`. -/
theorem exists_admissible (n : ℕ) :
    ∃ x : Fin n → EuclideanSpace ℝ (Fin 3), Admissible x := by
  refine ⟨fun i => !₂[(i : ℝ) / n, Real.sqrt (1 - ((i : ℝ) / n) ^ 2), 0], ?_, ?_⟩
  · intro i
    have hn : (0:ℝ) < n := by exact_mod_cast i.pos
    have h0 : 0 ≤ (i : ℝ) / n := by positivity
    have h1 : (i : ℝ) / n ≤ 1 := by
      rw [div_le_one hn]; exact_mod_cast i.isLt.le
    have hsq : ((i : ℝ) / n) ^ 2 ≤ 1 := pow_le_one₀ h0 h1
    rw [norm_e3, Real.sq_sqrt (by linarith)]
    norm_num
  · intro i j h
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast i.pos.ne'
    have h0 := (e3_inj h).1
    have : (i : ℝ) = j := by
      have := congrArg (· * (n:ℝ)) h0
      simpa [div_mul_cancel₀, hn] using this
    exact Fin.ext (by exact_mod_cast this)

theorem exists_minimiser (n : ℕ) (hn : 2 ≤ n) :
    ∃ x : Fin n → EuclideanSpace ℝ (Fin 3), Admissible x ∧
      ∀ y : Fin n → EuclideanSpace ℝ (Fin 3), Admissible y → energy x ≤ energy y := by
  obtain ⟨x₀, hx₀⟩ := exists_admissible n
  set M := energy x₀ with hM
  have hMpos : 0 < M := by
    have h01 : (⟨0, by omega⟩ : Fin n) < ⟨1, by omega⟩ := by simp [Fin.lt_def]
    have hle := term_le_energy x₀ h01
    have hne : x₀ ⟨0, by omega⟩ ≠ x₀ ⟨1, by omega⟩ := fun h => by
      have := hx₀.2 h; simp [Fin.ext_iff] at this
    have hpos : 0 < ‖x₀ ⟨0, by omega⟩ - x₀ ⟨1, by omega⟩‖ := by simpa [sub_eq_zero] using hne
    exact lt_of_lt_of_le (inv_pos.mpr hpos) hle
  have hMinv : 0 < M⁻¹ := inv_pos.mpr hMpos
  let K : Set (Fin n → EuclideanSpace ℝ (Fin 3)) :=
    {x | ∀ i, ‖x i‖ = 1} ∩ {x | ∀ i j, i ≠ j → M⁻¹ ≤ ‖x i - x j‖}
  have hKsub : K ⊆ Set.univ.pi (fun _ => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    intro x hx i _; simpa using hx.1 i
  have hKclosed : IsClosed K := by
    apply IsClosed.inter
    · simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const
    · simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_le continuous_const (by fun_prop)
  have hK : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_sphere 0 1).of_isClosed_subset hKclosed hKsub
  have hx₀K : x₀ ∈ K := ⟨hx₀.1, fun i j hij => dist_ge_of_energy_le hx₀.2 le_rfl hij⟩
  have hcont : ContinuousOn energy K := by
    unfold energy
    apply continuousOn_finset_sum; intro i _
    apply continuousOn_finset_sum; intro j hj
    apply ContinuousOn.inv₀
    · exact (by fun_prop : Continuous fun x : Fin n → EuclideanSpace ℝ (Fin 3) =>
        ‖x i - x j‖).continuousOn
    · intro x hx
      have hij : i ≠ j := (Finset.mem_Ioi.mp hj).ne
      have := hx.2 i j hij
      linarith
  obtain ⟨x, hxK, hxmin⟩ := hK.exists_isMinOn ⟨x₀, hx₀K⟩ hcont
  refine ⟨x, ⟨hxK.1, ?_⟩, ?_⟩
  · intro i j hij
    by_contra hne
    have := hxK.2 i j hne
    rw [hij, sub_self, norm_zero] at this
    linarith
  · intro y hy
    by_cases h : energy y ≤ M
    · exact hxmin ⟨hy.1, fun i j hij => dist_ge_of_energy_le hy.2 h hij⟩
    · push_neg at h
      exact le_trans (hxmin hx₀K) h.le

end Thomson
