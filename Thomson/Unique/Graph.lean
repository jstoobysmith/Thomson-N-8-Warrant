import Thomson.Unique.Defs

/-! # Uniqueness, step U5: the combinatorial classification

`UniquenessPlan.md`, U5.  An edge colouring `c` of `K₈` by the four chords whose every triangle is
one of the five antiprism types (`Valid`) and which has no "aligned" quadruple (`Aligned`) is a
relabelling of the antiprism pattern `apCol` (`classify`).

Proof: relabel so that vertex `0`'s colours are sorted (`exists_sorted`, via `Tuple.sort`), then a
depth-first search over the 28 edges (ordered by `j` then `i`, so that every triangle is checked
when its last edge is placed) is run by the kernel (`search_ok`, `decide +kernel`, 1878 nodes,
about 15 s); `search_sound` says every colouring passing all the checks satisfies `leafL`: it is
`apCol` up to one of the four stored permutations `apWits`, or it has one of the aligned
quadruples `alWits` (`python3 plans/unique_enum.py sorted lean` reproduces both lists). -/

namespace Thomson.Unique

/-- An edge colouring of `K₈` by the four chords `A = 0, D = 1, N = 2, F = 3`. -/
abbrev Col := Fin 8 → Fin 8 → Fin 4

/-- The antiprism pattern: squares `0..3` and `4..7`; inside a square `A` for neighbours and
`D` for diagonals; across, `N(vᵢ) = {wᵢ, wᵢ₊₁}` and the rest `F`.  (Diagonal value `0`.) -/
def apCol : Col := fun i j =>
  if i = j then 0 else
  if (max i.val j.val < 4 ∨ 4 ≤ min i.val j.val) then
    (if (max i.val j.val - min i.val j.val) % 2 = 1 then 0 else 1)
  else
    (if (max i.val j.val - min i.val j.val) % 4 ≤ 1 then 2 else 3)

def Valid (c : Col) : Prop :=
  (∀ i j, c i j = c j i) ∧
    ∀ i j l, i ≠ j → i ≠ l → j ≠ l → allowedTri (c i j) (c i l) (c j l) = true

def Aligned (c : Col) : Prop := ∃ i j k l : Fin 8, [i, j, k, l].Nodup ∧
  c i j = 0 ∧ c k l = 0 ∧ c i k = 2 ∧ c i l = 2 ∧ c j k = 2 ∧ c j l = 2

instance (c : Col) : Decidable (Valid c) := by unfold Valid; infer_instance
instance (c : Col) : Decidable (Aligned c) := by unfold Aligned; infer_instance

theorem apCol_valid : Valid apCol := by decide +kernel

theorem apCol_not_aligned : ¬ Aligned apCol := by decide +kernel

/-! ### Edge indexing -/

/-- Index of the edge `{i, j}`: edges `(i, j)`, `i < j`, ordered by `j` then `i`. -/
def eidx (i j : Fin 8) : ℕ :=
  max i.val j.val * (max i.val j.val - 1) / 2 + min i.val j.val

def edgeList : List (Fin 8 × Fin 8) :=
  [(0,1), (0,2), (1,2), (0,3), (1,3), (2,3), (0,4), (1,4), (2,4), (3,4),
   (0,5), (1,5), (2,5), (3,5), (4,5), (0,6), (1,6), (2,6), (3,6), (4,6), (5,6),
   (0,7), (1,7), (2,7), (3,7), (4,7), (5,7), (6,7)]

def edgeOf (k : ℕ) : Fin 8 × Fin 8 := edgeList.getD k (0, 1)

def allF8 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

theorem mem_allF8 (l : Fin 8) : l ∈ allF8 := by revert l; decide

/-! ### The search -/

/-- The checks when edge `k = (i, j)` is placed: every triangle `i j l` with `l < i` is allowed,
and at vertex `0` the colours are weakly increasing. -/
def chk (k : ℕ) (f : ℕ → Fin 4) : Bool :=
  allF8.all fun l =>
    if (edgeOf k).1 = 0 then
      (if 0 < l ∧ l < (edgeOf k).2 then decide (f (eidx 0 l) ≤ f k) else true)
    else
      (if l < (edgeOf k).1 then
        allowedTri (f k) (f (eidx (edgeOf k).1 l)) (f (eidx (edgeOf k).2 l)) else true)

/-- The colouring of a list of 28 edge colours. -/
def toColL (L : List (Fin 4)) : Col := fun i j => L.getD (eidx i j) 0

/-- The relabellings of the antiprism among the leaves. -/
def apWits : List (Equiv.Perm (Fin 8)) :=
  [Equiv.swap 2 3 * Equiv.swap 4 5, Equiv.swap 2 3 * Equiv.swap 4 5 * Equiv.swap 6 7,
   Equiv.swap 2 3, Equiv.swap 2 3 * Equiv.swap 6 7]

/-- The aligned quadruples among the leaves. -/
def alWits : List (Fin 8 × Fin 8 × Fin 8 × Fin 8) := [(0, 1, 4, 5), (0, 2, 4, 5)]

def AlignedAt (c : Col) (q : Fin 8 × Fin 8 × Fin 8 × Fin 8) : Prop :=
  [q.1, q.2.1, q.2.2.1, q.2.2.2].Nodup ∧
  c q.1 q.2.1 = 0 ∧ c q.2.2.1 q.2.2.2 = 0 ∧ c q.1 q.2.2.1 = 2 ∧ c q.1 q.2.2.2 = 2 ∧
    c q.2.1 q.2.2.1 = 2 ∧ c q.2.1 q.2.2.2 = 2

instance (c : Col) (q : Fin 8 × Fin 8 × Fin 8 × Fin 8) : Decidable (AlignedAt c q) := by unfold AlignedAt; infer_instance

def leafL (L : List (Fin 4)) : Bool :=
  apWits.any (fun σ => decide (∀ i j : Fin 8, i ≠ j → toColL L (σ i) (σ j) = apCol i j)) ||
    alWits.any (fun q => decide (AlignedAt (toColL L) q))

def leafOK (f : ℕ → Fin 4) : Bool := leafL ((List.range 28).map f)

def upd (f : ℕ → Fin 4) (k : ℕ) (a : Fin 4) : ℕ → Fin 4 := fun e => if e = k then a else f e

def search : ℕ → ℕ → (ℕ → Fin 4) → Bool
  | 0, _, f => leafOK f
  | n + 1, k, f => [0, 1, 2, 3].all fun a => !chk k (upd f k a) || search n (k + 1) (upd f k a)

set_option maxRecDepth 100000 in
theorem search_ok : search 28 0 (fun _ => 0) = true := by decide +kernel

/-! ### Facts about the edge tables -/

theorem edgeOf_lt : ∀ k, k < 28 → (edgeOf k).1 < (edgeOf k).2 := by decide

theorem eidx_edgeOf : ∀ k, k < 28 → eidx (edgeOf k).1 (edgeOf k).2 = k := by decide

theorem edgeOf_eidx : ∀ i j : Fin 8, i ≠ j →
    eidx i j < 28 ∧ (edgeOf (eidx i j) = (i, j) ∨ edgeOf (eidx i j) = (j, i)) := by decide

theorem eidx_read : ∀ k, k < 28 → ∀ l : Fin 8,
    (l < (edgeOf k).1 → eidx (edgeOf k).1 l < k ∧ eidx (edgeOf k).2 l < k) ∧
    (0 < l → l < (edgeOf k).2 → eidx 0 l < k) := by decide

theorem chk_congr {k : ℕ} (hk : k < 28) {f g : ℕ → Fin 4} (h : ∀ e, e ≤ k → f e = g e) :
    chk k f = chk k g := by
  unfold chk
  congr 1
  funext l
  have hr := eidx_read k hk l
  split_ifs with h1 h2 h3
  · rw [h k le_rfl, h _ (hr.2 h2.1 h2.2).le]
  · rfl
  · rw [h k le_rfl, h _ (hr.1 h3).1.le, h _ (hr.1 h3).2.le]
  · rfl

theorem leafOK_congr {f g : ℕ → Fin 4} (h : ∀ e, e < 28 → f e = g e) :
    leafOK f = leafOK g := by
  unfold leafOK
  congr 1
  exact List.map_congr_left fun e he => h e (List.mem_range.mp he)

theorem search_sound : ∀ n k (f : ℕ → Fin 4), search n k f = true → k + n = 28 →
    ∀ g : ℕ → Fin 4, (∀ e, e < k → g e = f e) → (∀ e, k ≤ e → e < 28 → chk e g = true) →
    leafOK g = true := by
  intro n
  induction n with
  | zero =>
    intro k f hs hk g hg _
    simp only [search] at hs
    rw [leafOK_congr (fun e he => hg e (by omega)), hs]
  | succ n ih =>
    intro k f hs hk g hg hc
    simp only [search, List.all_eq_true] at hs
    have hmem : ∀ a : Fin 4, a ∈ [0, 1, 2, 3] := by decide
    have ha := hs (g k) (hmem _)
    have hgk : ∀ e, e ≤ k → upd f k (g k) e = g e := by
      intro e he
      unfold upd
      split_ifs with h
      · rw [h]
      · exact (hg e (by omega)).symm
    rw [chk_congr (by omega) hgk, hc k le_rfl (by omega)] at ha
    simp only [Bool.not_true, Bool.false_or] at ha
    refine ih (k + 1) _ ha (by omega) g (fun e he => (hgk e (by omega)).symm) ?_
    intro e he1 he2
    exact hc e (by omega) he2

/-! ### Glue -/

/-- Edge colours of a colouring, indexed by edge number. -/
def edgeCol (c : Col) (e : ℕ) : Fin 4 := c (edgeOf e).1 (edgeOf e).2

theorem edgeCol_eidx {c : Col} (hs : ∀ i j, c i j = c j i) {i j : Fin 8} (hij : i ≠ j) :
    edgeCol c (eidx i j) = c i j := by
  unfold edgeCol
  rcases (edgeOf_eidx i j hij).2 with h | h <;> rw [h]
  exact hs j i

theorem chk_of_valid {c : Col} (hc : Valid c)
    (hmono : ∀ l m : Fin 8, 0 < l → l < m → c 0 l ≤ c 0 m) :
    ∀ k, k < 28 → chk k (edgeCol c) = true := by
  intro k hk
  unfold chk
  rw [List.all_eq_true]
  intro l _
  have hlt := edgeOf_lt k hk
  have hkk : edgeCol c k = c (edgeOf k).1 (edgeOf k).2 := rfl
  split_ifs with h1 h2 h3
  · rw [decide_eq_true_eq, hkk, edgeCol_eidx hc.1 (ne_of_lt h2.1), h1]
    exact hmono l _ h2.1 h2.2
  · rfl
  · rw [hkk, edgeCol_eidx hc.1 (ne_of_gt h3), edgeCol_eidx hc.1 (ne_of_gt (h3.trans hlt))]
    exact hc.2 _ _ _ (ne_of_lt hlt) (ne_of_gt h3) (ne_of_gt (h3.trans hlt))
  · rfl

theorem toColL_edgeCol {c : Col} (hs : ∀ i j, c i j = c j i) {i j : Fin 8} (hij : i ≠ j) :
    toColL ((List.range 28).map (edgeCol c)) i j = c i j := by
  unfold toColL
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (edgeOf_eidx i j hij).1]
  simp only [Option.map_some, Option.getD_some]
  exact edgeCol_eidx hs hij

/-- Symmetry breaking: relabel so that vertex `0`'s colours are sorted. -/
theorem exists_sorted (c : Col) : ∃ τ : Equiv.Perm (Fin 8), τ 0 = 0 ∧
    ∀ l m : Fin 8, 0 < l → l < m → c 0 (τ l) ≤ c 0 (τ m) := by
  let f : Fin 7 → Fin 4 := fun k => c 0 k.succ
  refine ⟨Equiv.Perm.decomposeFin.symm (0, Tuple.sort f), by simp, ?_⟩
  intro l m hl hlm
  obtain ⟨l', rfl⟩ := Fin.exists_succ_eq.mpr (ne_of_gt hl)
  obtain ⟨m', rfl⟩ := Fin.exists_succ_eq.mpr (ne_of_gt (hl.trans hlm))
  simp only [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
  exact Tuple.monotone_sort f (Fin.succ_lt_succ_iff.mp hlm).le

theorem valid_comp {c : Col} (hc : Valid c) (τ : Equiv.Perm (Fin 8)) :
    Valid (fun a b => c (τ a) (τ b)) :=
  ⟨fun _ _ => hc.1 _ _, fun _ _ _ hij hil hjl =>
    hc.2 _ _ _ (τ.injective.ne hij) (τ.injective.ne hil) (τ.injective.ne hjl)⟩

theorem aligned_of_comp {c : Col} (τ : Equiv.Perm (Fin 8))
    (h : Aligned (fun a b => c (τ a) (τ b))) : Aligned c := by
  obtain ⟨i, j, k, l, hn, h1⟩ := h
  exact ⟨τ i, τ j, τ k, τ l, hn.map τ.injective, h1⟩

/-- **The classification.**  Every valid colouring without an aligned quadruple is a relabelled
antiprism pattern. -/
theorem classify (c : Col) (hc : Valid c) (hna : ¬ Aligned c) :
    ∃ σ : Equiv.Perm (Fin 8), ∀ i j, i ≠ j → c (σ i) (σ j) = apCol i j := by
  obtain ⟨τ, hτ0, hτ⟩ := exists_sorted c
  set c' : Col := fun a b => c (τ a) (τ b) with hc'
  have hv : Valid c' := valid_comp hc τ
  have hmono : ∀ l m : Fin 8, 0 < l → l < m → c' 0 l ≤ c' 0 m := by
    intro l m hl hlm
    simp only [hc', hτ0]
    exact hτ l m hl hlm
  have hleaf : leafOK (edgeCol c') = true :=
    search_sound 28 0 _ search_ok rfl _ (fun e he => absurd he (Nat.not_lt_zero e))
      (fun e _ he => chk_of_valid hv hmono e he)
  have hL := fun {i j : Fin 8} (hij : i ≠ j) => toColL_edgeCol hv.1 hij
  unfold leafOK leafL at hleaf
  rw [Bool.or_eq_true, List.any_eq_true, List.any_eq_true] at hleaf
  rcases hleaf with ⟨σ, _, hσ⟩ | ⟨q, _, hq⟩
  · refine ⟨σ.trans τ, fun i j hij => ?_⟩
    have := of_decide_eq_true hσ i j hij
    rw [hL (σ.injective.ne hij)] at this
    exact this
  · exfalso
    apply hna
    apply aligned_of_comp τ
    have hq' := of_decide_eq_true hq
    obtain ⟨hn, h1, h2, h3, h4, h5, h6⟩ := hq'
    have hn' := hn
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true] at hn'
    obtain ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩ := hn'
    refine ⟨q.1, q.2.1, q.2.2.1, q.2.2.2, hn, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hL hab] at h1; exact h1
    · rw [hL hcd] at h2; exact h2
    · rw [hL hac] at h3; exact h3
    · rw [hL had] at h4; exact h4
    · rw [hL hbc] at h5; exact h5
    · rw [hL hbd] at h6; exact h6

end Thomson.Unique
