import Mathlib
import Thomson.LP.Yudin
import Thomson.Antiprism.Family

namespace Thomson
open Finset
open scoped RealInnerProductSpace

/-! ## 14. Breaking the open problem into steps

The remaining gap is a *global* search problem.  This section proves the reductions that turn
it into a finite one, so that what is left is explicitly a compactness-plus-certificates
argument rather than an unstructured minimisation. -/

/-- Every admissible configuration of at least two points has strictly positive energy. -/
theorem energy_pos {n : ℕ} (hn : 2 ≤ n) {x : Fin n → EuclideanSpace ℝ (Fin 3)}
    (hx : Admissible x) : 0 < energy x := by
  have h01 : (⟨0, by omega⟩ : Fin n) < ⟨1, by omega⟩ := by simp [Fin.lt_def]
  have hne : x ⟨0, by omega⟩ ≠ x ⟨1, by omega⟩ := fun h => by
    have := hx.2 h; simp [Fin.ext_iff] at this
  have hpos : 0 < ‖x ⟨0, by omega⟩ - x ⟨1, by omega⟩‖ := by simpa [sub_eq_zero] using hne
  exact lt_of_lt_of_le (inv_pos.mpr hpos) (term_le_energy x h01)

/-- **Step 1.**  The infimum is attained, so the open inequality is a statement about a single
configuration rather than about a limit. -/
theorem thomsonInf_attained (n : ℕ) (hn : 2 ≤ n) :
    ∃ x : Fin n → EuclideanSpace ℝ (Fin 3), Admissible x ∧ thomsonInf n = energy x := by
  obtain ⟨x, hx, hmin⟩ := exists_minimiser n hn
  refine ⟨x, hx, le_antisymm ?_ ?_⟩
  · exact csInf_le ⟨0, by rintro e ⟨y, -, rfl⟩; exact energy_nonneg y⟩ ⟨x, hx, rfl⟩
  · exact le_csInf ⟨_, x, hx, rfl⟩ (by rintro e ⟨y, hy, rfl⟩; exact hmin y hy)

/-- **Step 2.**  It is enough to bound the energy of configurations that already beat the
target: the search may be restricted to the sublevel set `{energy ≤ B}`. -/
theorem lower_bound_of_near_optimal {n : ℕ} (hn : 2 ≤ n) (B : ℝ)
    (h : ∀ x : Fin n → EuclideanSpace ℝ (Fin 3), Admissible x → energy x ≤ B → B ≤ energy x) :
    B ≤ thomsonInf n := by
  obtain ⟨y, hy, hxy⟩ := thomsonInf_attained n hn
  rw [hxy]
  by_contra hlt
  push_neg at hlt
  exact absurd (h y hy hlt.le) (not_le.mpr hlt)

/-- **Step 3 (gauge).**  Energy is invariant under every linear isometry of `ℝ³`, so a search
may fix the rotation freedom. -/
theorem energy_isometry {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3))
    (f : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    energy (fun i => f (x i)) = energy x := by
  unfold energy
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← f.map_sub, f.norm_map]

theorem admissible_isometry {n : ℕ} {x : Fin n → EuclideanSpace ℝ (Fin 3)} (hx : Admissible x)
    (f : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    Admissible (fun i => f (x i)) :=
  ⟨fun i => by rw [f.norm_map]; exact hx.1 i, fun i j hij => hx.2 (f.injective hij)⟩

/-- **Step 4 (separation).**  Any configuration that beats the antiprism has all pairwise
distances at least `1/19.6753 > 0.0508`. -/
theorem separated_of_near_optimal {x : Fin 8 → EuclideanSpace ℝ (Fin 3)}
    (hx : Admissible x) (hE : energy x ≤ 19.6753) : Separated (1 / 19.6753) x := by
  intro i j hij
  have := dist_ge_of_energy_le hx.2 hE hij
  rwa [← one_div] at this

/-- Updating one point of an injective configuration to a genuinely new point keeps it
injective. -/
theorem injective_update {n : ℕ} {x : Fin n → EuclideanSpace ℝ (Fin 3)}
    (hinj : Function.Injective x) (i : Fin n) {p : EuclideanSpace ℝ (Fin 3)}
    (hp : ∀ j, p ≠ x j) : Function.Injective (Function.update x i p) := by
  intro a b hab
  by_cases ha : a = i <;> by_cases hb : b = i
  · rw [ha, hb]
  · rw [ha, Function.update_self, Function.update_of_ne hb] at hab
    exact absurd hab (hp b)
  · rw [hb, Function.update_self, Function.update_of_ne ha] at hab
    exact absurd hab.symm (hp a)
  · rw [Function.update_of_ne ha, Function.update_of_ne hb] at hab
    exact hinj hab

/-- The local energies `λᵢ = Σ_{j≠i} ‖xᵢ-xⱼ‖⁻¹` sum to twice the energy, so some point
carries at least the average `2E/n`.  This is the pigeonhole behind the covering bound. -/
theorem sum_local_energy {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) :
    ∑ i, ∑ j ∈ univ.erase i, ‖x i - x j‖⁻¹ = 2 * energy x := by
  rw [energy_eq_half]; ring

/-- **Step 5 (covering).**  At a minimiser there are no holes: every point of the sphere lies
within `n(n-1)/(2E)` of one of the points.  Proof: some point carries local energy at least
the average `2E/n`; if a hole existed, moving that point into the hole would strictly lower
the energy, contradicting minimality. -/
theorem covering_radius {n : ℕ} (hn : 2 ≤ n) {x : Fin n → EuclideanSpace ℝ (Fin 3)}
    (hx : Admissible x) (hmin : ∀ y : Fin n → EuclideanSpace ℝ (Fin 3), Admissible y →
      energy x ≤ energy y) {p : EuclideanSpace ℝ (Fin 3)} (hp : ‖p‖ = 1) :
    ∃ i, ‖p - x i‖ ≤ (n * (n - 1)) / (2 * energy x) := by
  have hE : 0 < energy x := energy_pos hn hx
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  set ρ : ℝ := (n * (n - 1)) / (2 * energy x) with hρ
  have hρpos : 0 < ρ := by rw [hρ]; apply div_pos (by nlinarith) (by linarith)
  by_contra hcon
  push_neg at hcon
  -- `(n-1)/ρ` is exactly the average local energy
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hρE : ((n : ℝ) - 1) / ρ = 2 * energy x / n := by
    rw [hρ, div_div_eq_mul_div, div_eq_iff (mul_ne_zero hn0 hn1), div_mul_eq_mul_div,
      eq_div_iff hn0]
    ring
  -- some point carries at least the average local energy
  have hsum := sum_local_energy x
  have hex : ∃ i : Fin n, 2 * energy x / n ≤ ∑ j ∈ univ.erase i, ‖x i - x j‖⁻¹ := by
    by_contra hno
    push_neg at hno
    have hlt : ∑ i : Fin n, ∑ j ∈ univ.erase i, ‖x i - x j‖⁻¹
        < ∑ _i : Fin n, 2 * energy x / n :=
      Finset.sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ (fun i _ => hno i)
    rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
    have heq : (n : ℝ) * (2 * energy x / n) = 2 * energy x := by field_simp
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨i, hi⟩ := hex
  -- the moved configuration is admissible
  have hpne : ∀ j, p ≠ x j := by
    intro j h
    have hlt := hcon j
    rw [← h, sub_self, norm_zero] at hlt
    linarith
  have hadm : Admissible (Function.update x i p) := by
    refine ⟨fun k => ?_, injective_update hx.2 i hpne⟩
    by_cases hk : k = i
    · rw [hk, Function.update_self]; exact hp
    · rw [Function.update_of_ne hk]; exact hx.1 k
  -- moving into the hole strictly lowers the energy
  have hne : (univ.erase i).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    omega
  have hnew : energy (Function.update x i p) < ((n : ℝ) - 1) / ρ + rest x i := by
    rw [energy_update]
    have hlt : ∑ j ∈ univ.erase i, ‖p - x j‖⁻¹ < ∑ _j ∈ univ.erase i, ρ⁻¹ := by
      refine Finset.sum_lt_sum_of_nonempty hne fun j _ => ?_
      rw [inv_eq_one_div, inv_eq_one_div]
      exact one_div_lt_one_div_of_lt hρpos (hcon j)
    have hcard : ∑ _j ∈ univ.erase i, ρ⁻¹ = ((n : ℝ) - 1) / ρ := by
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega)]
      simp [div_eq_mul_inv]
    rw [hcard] at hlt
    linarith
  have hold : energy x = (∑ j ∈ univ.erase i, ‖x i - x j‖⁻¹) + rest x i := by
    conv_lhs => rw [← Function.update_eq_self i x]
    rw [energy_update]
  have hchain := (hmin _ hadm).trans_lt hnew
  rw [hρE] at hchain
  linarith

/-- For eight points, the covering radius of a minimiser is below `1.4253`: there is no hole
of angular radius `49°` or more.  This is the quantitative form of "a minimiser is spread
out", and it is what makes the remaining search region compact and explicit. -/
theorem covering_radius_eight {x : Fin 8 → EuclideanSpace ℝ (Fin 3)} (hx : Admissible x)
    (hmin : ∀ y : Fin 8 → EuclideanSpace ℝ (Fin 3), Admissible y → energy x ≤ energy y)
    {p : EuclideanSpace ℝ (Fin 3)} (hp : ‖p‖ = 1) :
    ∃ i, ‖p - x i‖ ≤ 1.4253 := by
  obtain ⟨i, hi⟩ := covering_radius (by norm_num) hx hmin hp
  refine ⟨i, hi.trans ?_⟩
  have hge : (19.6462 : ℝ) < energy x := by
    have hle : thomsonInf 8 ≤ energy x :=
      csInf_le ⟨0, by rintro e ⟨y, -, rfl⟩; exact energy_nonneg y⟩ ⟨x, hx, rfl⟩
    have := thomsonInf_gt'
    linarith
  rw [div_le_iff₀ (by positivity)]
  push_cast
  nlinarith [hge]

/-! ### The open problem as two named steps -/

/-- `x` is within `ε` of a rotated, relabelled copy of the optimal antiprism. -/
def NearAntiprism (ε : ℝ) (x : Fin 8 → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∃ (f : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (σ : Equiv.Perm (Fin 8)),
    ∀ i, ‖x i - f (antiprism (Real.sqrt uStar) (σ i))‖ < ε

/-- **The open inequality, split into two independent steps.**

`H1` is *local minimality at the antiprism*: the transverse Hessian statement of the blueprint
(§5.5), a finite algebraic computation, listed there as reachable.

`H2` is *the global search*: every configuration at least as good as the antiprism is already
near it.  This is where the whole difficulty of `N = 8` sits, and it is what interval
branch-and-bound over the 13-dimensional reduced space would establish.

Neither step is proved here.  What is proved is that they suffice, so the open problem is now
two clearly separated statements rather than one. -/
theorem thomson_eight_lower_of (ε : ℝ)
    (H1 : ∀ x : Fin 8 → EuclideanSpace ℝ (Fin 3), Admissible x → NearAntiprism ε x →
      antiprismEnergy uStar ≤ energy x)
    (H2 : ∀ x : Fin 8 → EuclideanSpace ℝ (Fin 3), Admissible x →
      energy x ≤ antiprismEnergy uStar → NearAntiprism ε x) :
    antiprismEnergy uStar ≤ thomsonInf 8 :=
  lower_bound_of_near_optimal (by norm_num) _ fun x hx hle => H1 x hx (H2 x hx hle)


end Thomson
