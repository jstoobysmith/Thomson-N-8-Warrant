import Mathlib
import Thomson.ForceBalance
import Thomson.Reduction
import Thomson.Unique.Tight
import Thomson.Unique.Chords
import Thomson.Unique.Graph
import Thomson.Unique.Gram

/-! # U7: uniqueness of the minimiser — assembly

`UniquenessPlan.md`, step U7.  At a configuration with `energy x = E(u*)`:

* every distance is a zero of `pairP pivots` in `[0.9619, 2]` (U2, `tight_pairs`, `chord_range`),
  hence one of the four chords (U3, here the hypothesis `PairZeroOnlyAtChords`), which defines the
  colouring `colOf x` of `K₈` (`colOf_spec`);
* every triangle is a zero of `triP pivots` (U2, `tight_triangles`) and realisable (Gram
  determinant `≥ 0`), hence one of the five antiprism types (U4) — `colOf x` is `Valid`;
* no aligned quadruple is realisable in `ℝ³` (U6) — `colOf x` is not `Aligned`;

so `colOf x` is a relabelled antiprism pattern (U5, `classify`), and eight unit vectors with the
antiprism distance pattern are congruent to the optimal antiprism (U6, `congruent_antiprism`). -/

namespace Thomson.Unique

open Thomson
open scoped RealInnerProductSpace

/-- **U3's conclusion, as a hypothesis**: on the chord range, `pairP pivots` vanishes only at the
four antiprism chords (`pairP_eq_zero_iff`, direction `→`). -/
def PairZeroOnlyAtChords : Prop :=
  ∀ s : ℝ, 9619 / 10000 ≤ s → s ≤ 2 → pairP pivots s = 0 → ∃ X : Fin 4, s = chord X

/-! ## The colouring of a configuration -/

/-- The colour of a distance: the chord it equals (`3` if it is none of `chord 0, 1, 2`). -/
noncomputable def colOfDist (s : ℝ) : Fin 4 := by
  classical
  exact if s = chord 0 then 0 else if s = chord 1 then 1 else if s = chord 2 then 2 else 3

theorem chord_injective : Function.Injective chord := by
  intro X Y h
  by_contra hne
  have := chord_gaps X Y hne
  rw [h, sub_self, abs_zero] at this
  norm_num at this

theorem colOfDist_spec {s : ℝ} (h : ∃ X : Fin 4, s = chord X) : s = chord (colOfDist s) := by
  obtain ⟨X, rfl⟩ := h
  unfold colOfDist
  split_ifs with h0 h1 h2
  · exact h0
  · exact h1
  · exact h2
  · have hX : X = 3 := by
      fin_cases X
      · exact absurd rfl h0
      · exact absurd rfl h1
      · exact absurd rfl h2
      · rfl
    rw [hX]

theorem colOfDist_chord (X : Fin 4) : colOfDist (chord X) = X :=
  chord_injective (colOfDist_spec ⟨X, rfl⟩).symm

/-- The colouring of `K₈` defined by a configuration: the chord each distance equals. -/
noncomputable def colOf (x : Fin 8 → EuclideanSpace ℝ (Fin 3)) : Col :=
  fun i j => colOfDist ‖x i - x j‖

theorem colOf_symm (x : Fin 8 → EuclideanSpace ℝ (Fin 3)) (i j : Fin 8) :
    colOf x i j = colOf x j i := by
  unfold colOf; rw [norm_sub_rev]

/-- The plan's antiprism pattern `apCol` (U5) and U6's `apColPlan` agree. -/
theorem apCol_eq_apColPlan : ∀ i j : Fin 8, apCol i j = apColPlan i j := by decide

section minimiser

variable (h1a : Task1a) (h1b : Task1b) (h5b : Task5b) (h5s : Task5bStrict)
  (hpz : PairZeroOnlyAtChords)
  {x : Fin 8 → EuclideanSpace ℝ (Fin 3)}

include h1a h1b h5b hpz in
/-- Every distance of a minimiser is the chord of its colour. -/
theorem colOf_spec (hx : Admissible x) (hE : energy x = antiprismEnergy uStar) {i j : Fin 8}
    (hij : i ≠ j) : ‖x i - x j‖ = chord (colOf x i j) := by
  obtain ⟨r1, r2⟩ := chord_range hx hE i j hij
  exact colOfDist_spec (hpz _ r1 r2 (tight_pairs h1a h1b h5b hx hE i j hij))

/-- The Gram polynomial of three distances of unit vectors is their (nonnegative) Gram
determinant. -/
theorem gram_nonneg_of_norm (a b c : EuclideanSpace ℝ (Fin 3)) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hc : ‖c‖ = 1) : 0 ≤ Tri5b.gram ‖a - b‖ ‖a - c‖ ‖b - c‖ := by
  have h := gram_det_nonneg a b c ha hb hc
  rw [inner_eq_of_norm a b ha hb, inner_eq_of_norm a c ha hc, inner_eq_of_norm b c hb hc] at h
  exact h

include h1a h1b h5b h5s hpz in
/-- **The colouring of a minimiser is valid**: every triangle is one of the five types. -/
theorem valid_colOf (hx : Admissible x) (hE : energy x = antiprismEnergy uStar) :
    Valid (colOf x) := by
  refine ⟨colOf_symm x, fun i j l hij hil hjl => ?_⟩
  have eij := colOf_spec h1a h1b h5b hpz hx hE hij
  have eil := colOf_spec h1a h1b h5b hpz hx hE hil
  have ejl := colOf_spec h1a h1b h5b hpz hx hE hjl
  have hg := gram_nonneg_of_norm (x i) (x j) (x l) (hx.1 i) (hx.1 j) (hx.1 l)
  have h0 := tight_triangles h1a h1b h5b hx hE i j l hij hil hjl
  rw [eij, eil, ejl] at hg h0
  exact allowedTri_of_triP_eq_zero h5s _ _ _ hg h0

include h1a h1b h5b hpz in
/-- **No aligned quadruple** in the colouring of a minimiser (U6). -/
theorem not_aligned (hx : Admissible x) (hE : energy x = antiprismEnergy uStar) :
    ¬ Aligned (colOf x) := by
  rintro ⟨i, j, k, l, hn, h1, h2, h3, h4, h5, h6⟩
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hn
  obtain ⟨⟨hij, hik, hil⟩, ⟨hjk, hjl⟩, hkl⟩ := hn
  have sp := fun {a b : Fin 8} (hab : a ≠ b) => colOf_spec h1a h1b h5b hpz hx hE hab
  refine no_aligned_chords (x i) (x j) (x k) (x l) (hx.1 i) (hx.1 j) (hx.1 k) (hx.1 l) ?_ ?_ ?_ ?_
    ?_ ?_
  · rw [sp hij, h1]
  · rw [sp hkl, h2]
  · rw [sp hik, h3]
  · rw [sp hil, h4]
  · rw [sp hjk, h5]
  · rw [sp hjl, h6]

include h1a h1b h5b h5s hpz in
/-- **Uniqueness of the minimiser** (with the tasks and U3 as hypotheses): every admissible
configuration of energy `E(u*)` is an orthogonal image of a relabelling of the optimal square
antiprism. -/
theorem thomson_eight_unique_of_tasks (x : Fin 8 → EuclideanSpace ℝ (Fin 3)) (hx : Admissible x)
    (hE : energy x = antiprismEnergy uStar) :
    ∃ (f : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (σ : Equiv.Perm (Fin 8)),
      ∀ i, x i = f (antiprism (Real.sqrt uStar) (σ i)) := by
  obtain ⟨σ₀, hσ₀⟩ := classify (colOf x) (valid_colOf h1a h1b h5b h5s hpz hx hE)
    (not_aligned h1a h1b h5b hpz hx hE)
  obtain ⟨f, hf⟩ := congruent_antiprism (fun i => x (σ₀ i)) (fun i => hx.1 (σ₀ i))
    (fun i j hij => by
      rw [colOf_spec h1a h1b h5b hpz hx hE (σ₀.injective.ne hij), hσ₀ i j hij,
        apCol_eq_apColPlan])
  refine ⟨f, σ₀.symm.trans apPerm, fun i => ?_⟩
  have := hf (σ₀.symm i)
  simp only [Equiv.apply_symm_apply] at this
  exact this

end minimiser

/-! ## The converse: every congruent relabelled copy of the antiprism is a minimiser -/

/-- `energy` is invariant under relabelling. -/
theorem energy_comp_perm (y : Fin 8 → EuclideanSpace ℝ (Fin 3)) (σ : Equiv.Perm (Fin 8)) :
    energy (fun i => y (σ i)) = energy y := by
  have key : ∀ z : Fin 8 → EuclideanSpace ℝ (Fin 3),
      energy z = (1 / 2) * ∑ i, ∑ j, ‖z i - z j‖⁻¹ := by
    intro z
    rw [energy_eq_half]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), sub_self, norm_zero, inv_zero, zero_add]
  rw [key, key]
  congr 1
  rw [← Equiv.sum_comp σ (fun i => ∑ j, ‖y i - y j‖⁻¹)]
  exact Finset.sum_congr rfl fun i _ => Equiv.sum_comp σ (fun j => ‖y (σ i) - y j‖⁻¹)

theorem antiprism_minimiser_admissible (f : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (σ : Equiv.Perm (Fin 8)) :
    Admissible (fun i => f (antiprism (Real.sqrt uStar) (σ i))) :=
  ⟨fun i => by rw [LinearIsometryEquiv.norm_map, norm_antiprism],
    f.injective.comp ((antiprism_injective sqrt_uStar_pos sqrt_uStar_lt_one).comp σ.injective)⟩

theorem antiprism_minimiser_energy (f : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (σ : Equiv.Perm (Fin 8)) :
    energy (fun i => f (antiprism (Real.sqrt uStar) (σ i))) = antiprismEnergy uStar := by
  rw [energy_isometry (fun i => antiprism (Real.sqrt uStar) (σ i)) f, energy_comp_perm,
    antiprism_energy_eq sqrt_uStar_pos sqrt_uStar_lt_one,
    Real.sq_sqrt (by linarith [uStar_mem_Icc.1])]

/-- **Characterisation of the minimisers** (with the tasks and U3 as hypotheses): an admissible
configuration has energy `E(u*)` iff it is an orthogonal image of a relabelled optimal antiprism. -/
theorem minimiser_iff_of_tasks (h1a : Task1a) (h1b : Task1b) (h5b : Task5b)
    (h5s : Task5bStrict) (hpz : PairZeroOnlyAtChords) (x : Fin 8 → EuclideanSpace ℝ (Fin 3)) :
    (Admissible x ∧ energy x = antiprismEnergy uStar) ↔
    ∃ (f : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (σ : Equiv.Perm (Fin 8)),
      ∀ i, x i = f (antiprism (Real.sqrt uStar) (σ i)) := by
  constructor
  · rintro ⟨hx, hE⟩
    exact thomson_eight_unique_of_tasks h1a h1b h5b h5s hpz x hx hE
  · rintro ⟨f, σ, h⟩
    have hx : x = fun i => f (antiprism (Real.sqrt uStar) (σ i)) := funext h
    subst hx
    exact ⟨antiprism_minimiser_admissible f σ, antiprism_minimiser_energy f σ⟩

end Thomson.Unique
