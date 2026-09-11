import Thomson.Tri5b.Engine

/-! # Task 5b, step 12: multiplication by a monomial

The tensor of `F` is built from `MForm.Fh_Hp_eq_wsum`:

`F = (1/3) Σ_k Σ_{i,j} M_k[i,j] · (uⁱ vʲ Q_k(u,v,t) + uⁱ tʲ Q_k(u,t,v) + vⁱ tʲ Q_k(v,t,u))`,

so the only tensor product needed is by a *monomial* — a pure index shift, not a convolution.
Shifting by one is a nine-term identity; the general shift follows by induction, carrying the
degree bound that keeps the shift inside the `9×9×9` grid. -/

namespace Thomson.Tri5b

open Finset

/-- `c` has degree at most `d` in the first variable. -/
def Deg1 (c : RT) (d : ℕ) : Prop := ∀ (a : Fin 9) (q r : Fin 9), d < (a : ℕ) → c a q r = 0

/-- Multiply by the first variable: shift the first index up by one. -/
def mup1 (c : RT) : RT := fun p q r =>
  if h : 0 < (p : ℕ) then c ⟨(p : ℕ) - 1, by omega⟩ q r else 0

/-- The same on interval tensors. -/
def Imup1 (C : IT) : IT := fun p q r =>
  if h : 0 < (p : ℕ) then C ⟨(p : ℕ) - 1, by omega⟩ q r else Itv.zero

theorem ITMem_mup1 {C : IT} {c : RT} (h : ITMem C c) : ITMem (Imup1 C) (mup1 c) := by
  intro p q r
  unfold Imup1 mup1
  split
  · exact h _ q r
  · exact Itv.mem_zero

theorem Deg1_mup1 {c : RT} {d : ℕ} (h : Deg1 c d) : Deg1 (mup1 c) (d + 1) := by
  intro a q r ha
  unfold mup1
  split
  · rename_i hp
    refine h _ q r ?_
    simp only [Fin.val_mk]
    omega
  · rfl

theorem ev_mup1 {c : RT} (hdeg : Deg1 c 7) (u v t : ℝ) :
    ev (mup1 c) u v t = u * ev c u v t := by
  have hz : (∑ q, ∑ r, (mup1 c) 0 q r * (v ^ (q : ℕ) * t ^ (r : ℕ))) = 0 := by
    have hmz : ∀ q r : Fin 9, (mup1 c) 0 q r = 0 := by
      intro q r; simp [mup1]
    simp [hmz]
  have h8 : (∑ q, ∑ r, c (Fin.last 8) q r * (v ^ (q : ℕ) * t ^ (r : ℕ))) = 0 := by
    refine Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun r _ => ?_
    rw [hdeg (Fin.last 8) q r (by norm_num), zero_mul]
  rw [ev_eq_outer, ev_eq_outer, Finset.mul_sum]
  conv_lhs => rw [Fin.sum_univ_succ]
  conv_rhs => rw [Fin.sum_univ_castSucc]
  rw [hz, h8]
  simp only [zero_mul, zero_add, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : ((i.succ : Fin 9) : ℕ) = (i : ℕ) + 1 := Fin.val_succ i
  have hcast : ((i.castSucc : Fin 9) : ℕ) = (i : ℕ) := Fin.coe_castSucc i
  have hshift : ∀ q r : Fin 9, (mup1 c) i.succ q r = c i.castSucc q r := by
    intro q r
    unfold mup1
    rw [dif_pos (by rw [hi]; omega)]
    congr 1
  simp only [hshift, hi, hcast, pow_succ]
  ring

/-- Multiply by `uⁿ`. -/
def mupN (c : RT) : ℕ → RT
  | 0 => c
  | (n + 1) => mup1 (mupN c n)

def ImupN (C : IT) : ℕ → IT
  | 0 => C
  | (n + 1) => Imup1 (ImupN C n)

theorem ITMem_mupN {C : IT} {c : RT} (h : ITMem C c) : ∀ n, ITMem (ImupN C n) (mupN c n)
  | 0 => h
  | (n + 1) => ITMem_mup1 (ITMem_mupN h n)

theorem Deg1_mupN {c : RT} {d : ℕ} (h : Deg1 c d) : ∀ n, Deg1 (mupN c n) (d + n)
  | 0 => h
  | (n + 1) => Deg1_mup1 (Deg1_mupN h n)

theorem ev_mupN {c : RT} {d : ℕ} (hdeg : Deg1 c d) :
    ∀ n, d + n ≤ 8 → ∀ u v t : ℝ, ev (mupN c n) u v t = u ^ n * ev c u v t
  | 0, _, u, v, t => by simp [mupN]
  | (n + 1), h, u, v, t => by
      have hd : Deg1 (mupN c n) (d + n) := Deg1_mupN hdeg n
      have hd7 : Deg1 (mupN c n) 7 := by
        intro a q r ha; exact hd a q r (by omega)
      rw [mupN, ev_mup1 hd7, ev_mupN hdeg n (by omega)]
      ring


/-! ### The other two axes, and the remaining permutations -/

theorem perm12_perm12 (c : RT) : perm12 (perm12 c) = c := rfl
theorem perm13_perm13 (c : RT) : perm13 (perm13 c) = c := rfl

/-- Swap the last two axes. -/
def perm23 (c : RT) : RT := fun i j k => c i k j
/-- The cyclic permutation with `ev (permCyc c) u v t = ev c v t u`. -/
def permCyc (c : RT) : RT := fun a b l => c b l a

def Iperm23 (C : IT) : IT := fun i j k => C i k j
def IpermCyc (C : IT) : IT := fun a b l => C b l a

theorem ITMem_perm23 {C : IT} {c : RT} (h : ITMem C c) : ITMem (Iperm23 C) (perm23 c) :=
  fun i j k => h i k j
theorem ITMem_permCyc {C : IT} {c : RT} (h : ITMem C c) : ITMem (IpermCyc C) (permCyc c) :=
  fun a b l => h b l a

theorem ev_perm23 (c : RT) (u v t : ℝ) : ev (perm23 c) u v t = ev c u t v := by
  unfold ev perm23
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem ev_permCyc (c : RT) (u v t : ℝ) : ev (permCyc c) u v t = ev c v t u := by
  unfold ev permCyc
  calc ∑ a, ∑ b, ∑ l, c b l a * (u ^ (a : ℕ) * v ^ (b : ℕ) * t ^ (l : ℕ))
      = ∑ b, ∑ a, ∑ l, c b l a * (u ^ (a : ℕ) * v ^ (b : ℕ) * t ^ (l : ℕ)) := Finset.sum_comm
    _ = ∑ b, ∑ l, ∑ a, c b l a * (u ^ (a : ℕ) * v ^ (b : ℕ) * t ^ (l : ℕ)) :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, c i j k * (v ^ (i : ℕ) * t ^ (j : ℕ) * u ^ (k : ℕ)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => by ring

/-- Degree in the second and third variables. -/
def Deg2 (c : RT) (d : ℕ) : Prop := Deg1 (perm12 c) d
def Deg3 (c : RT) (d : ℕ) : Prop := Deg1 (perm13 c) d

def mup2N (c : RT) (n : ℕ) : RT := perm12 (mupN (perm12 c) n)
def mup3N (c : RT) (n : ℕ) : RT := perm13 (mupN (perm13 c) n)
def Imup2N (C : IT) (n : ℕ) : IT := Iperm12 (ImupN (Iperm12 C) n)
def Imup3N (C : IT) (n : ℕ) : IT := Iperm13 (ImupN (Iperm13 C) n)

theorem ITMem_mup2N {C : IT} {c : RT} (h : ITMem C c) (n : ℕ) :
    ITMem (Imup2N C n) (mup2N c n) :=
  ITMem_perm12 (ITMem_mupN (ITMem_perm12 h) n)
theorem ITMem_mup3N {C : IT} {c : RT} (h : ITMem C c) (n : ℕ) :
    ITMem (Imup3N C n) (mup3N c n) :=
  ITMem_perm13 (ITMem_mupN (ITMem_perm13 h) n)

theorem ev_mup2N {c : RT} {d : ℕ} (hdeg : Deg2 c d) (n : ℕ) (h : d + n ≤ 8) (u v t : ℝ) :
    ev (mup2N c n) u v t = v ^ n * ev c u v t := by
  unfold mup2N
  rw [ev_perm12, ev_mupN hdeg n h, ev_perm12]

theorem ev_mup3N {c : RT} {d : ℕ} (hdeg : Deg3 c d) (n : ℕ) (h : d + n ≤ 8) (u v t : ℝ) :
    ev (mup3N c n) u v t = t ^ n * ev c u v t := by
  unfold mup3N
  rw [ev_perm13, ev_mupN hdeg n h, ev_perm13]

/-! ### Degrees under the operations we use -/

/-- `mup1` cannot create nonzero entries where the last two indices are forbidden. -/
theorem mup1_preserves {c : RT} {p : Fin 9 → Fin 9 → Prop}
    (h : ∀ a q r, p q r → c a q r = 0) : ∀ a q r, p q r → (mup1 c) a q r = 0 := by
  intro a q r hp
  unfold mup1
  split
  · exact h _ q r hp
  · rfl

theorem mupN_preserves {c : RT} {p : Fin 9 → Fin 9 → Prop}
    (h : ∀ a q r, p q r → c a q r = 0) : ∀ (n : ℕ) (a q r), p q r → (mupN c n) a q r = 0
  | 0 => h
  | (n + 1) => mup1_preserves (mupN_preserves h n)

/-- Everything vanishes above the degree, in every variable. -/
def DegAll (c : RT) (d : ℕ) : Prop :=
  ∀ (a q r : Fin 9), (d < (a : ℕ) ∨ d < (q : ℕ) ∨ d < (r : ℕ)) → c a q r = 0

theorem DegAll.deg1 {c : RT} {d : ℕ} (h : DegAll c d) : Deg1 c d :=
  fun a q r ha => h a q r (Or.inl ha)
theorem DegAll.deg2 {c : RT} {d : ℕ} (h : DegAll c d) : Deg2 c d :=
  fun a q r ha => h q a r (Or.inr (Or.inl ha))
theorem DegAll.deg3 {c : RT} {d : ℕ} (h : DegAll c d) : Deg3 c d :=
  fun a q r ha => h r q a (Or.inr (Or.inr ha))
theorem DegAll.perm23 {c : RT} {d : ℕ} (h : DegAll c d) : DegAll (Thomson.Tri5b.perm23 c) d := by
  intro a q r ha
  exact h a r q (by rcases ha with h' | h' | h' <;> tauto)
theorem DegAll.permCyc {c : RT} {d : ℕ} (h : DegAll c d) : DegAll (Thomson.Tri5b.permCyc c) d := by
  intro a q r ha
  exact h q r a (by rcases ha with h' | h' | h' <;> tauto)

/-- Shifting along the second axis leaves the degree in the first alone. -/
theorem Deg1_mup2N {c : RT} {d : ℕ} (h : Deg1 c d) (n : ℕ) : Deg1 (mup2N c n) d := by
  intro a q r ha
  exact mupN_preserves (p := fun x _ => d < (x : ℕ))
    (fun x y z hy => h y x z hy) n q a r ha

/-- Shifting along the third axis leaves the degree in the first alone. -/
theorem Deg1_mup3N {c : RT} {d : ℕ} (h : Deg1 c d) (n : ℕ) : Deg1 (mup3N c n) d := by
  intro a q r ha
  exact mupN_preserves (p := fun _ z => d < (z : ℕ))
    (fun x y z hz => h z y x hz) n r q a ha

/-- Shifting along the third axis leaves the degree in the second alone. -/
theorem Deg2_mup3N {c : RT} {d : ℕ} (h : Deg2 c d) (n : ℕ) : Deg2 (mup3N c n) d := by
  intro a q r ha
  exact mupN_preserves (p := fun x _ => d < (x : ℕ))
    (fun x y z hy => h y z x hy) n r a q ha

end Thomson.Tri5b
