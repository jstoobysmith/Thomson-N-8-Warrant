import Thomson.Tri5b.Leaf

/-! # Task 5b, step 10: the covering tree

The boxes are produced by recursive bisection, so the covering is proved the same way: a binary
tree whose leaves are either *checked* (`leaf_sound` applies) or *skipped* (the point carries no
obligation there).  Everything about a leaf — the tangent chords, the S-procedure multiplier, the
splitting axis and the splitting point — is *computed* by the checker, so the certificate itself is
nothing but the shape of the tree, carried as a stream of bits inside a single natural number. -/

namespace Thomson.Tri5b

open Thomson

/-- A box with fixed-point endpoints. -/
structure Bx where
  ulo : ℤ
  uhi : ℤ
  vlo : ℤ
  vhi : ℤ
  tlo : ℤ
  thi : ℤ
deriving Repr, Inhabited, DecidableEq

/-- The points of a box. -/
def Bx.Mem (B : Bx) (u v t : ℝ) : Prop :=
  ((B.ulo : ℝ) ≤ u * SCALE ∧ u * SCALE ≤ (B.uhi : ℝ))
    ∧ ((B.vlo : ℝ) ≤ v * SCALE ∧ v * SCALE ≤ (B.vhi : ℝ))
    ∧ ((B.tlo : ℝ) ≤ t * SCALE ∧ t * SCALE ≤ (B.thi : ℝ))

/-- The three lower endpoints.  A match, not a `![…]` vector: the checker reads these per node,
and one `Matrix.vecCons` read costs the interpreter more than a whole box. -/
def Bx.lo (B : Bx) : Fin 3 → ℤ := fun i =>
  match (i : ℕ) with | 0 => B.ulo | 1 => B.vlo | _ => B.tlo
def Bx.hi (B : Bx) : Fin 3 → ℤ := fun i =>
  match (i : ℕ) with | 0 => B.uhi | 1 => B.vhi | _ => B.thi

/-- Centre of an interval, rounded down. -/
def ctr (lo hi : ℤ) : ℤ := (lo + hi) / 2
/-- A half-width that covers both ends of the interval from that centre. -/
def hal (lo hi : ℤ) : ℤ := max (hi - ctr lo hi) (ctr lo hi - lo)

theorem hal_pos {lo hi : ℤ} (h : lo < hi) : 0 < hal lo hi := by
  unfold hal ctr
  have h1 : lo + hi - 2 * ((lo + hi) / 2) = (lo + hi) % 2 := by omega
  have h2 := Int.emod_nonneg (lo + hi) (by norm_num : (2:ℤ) ≠ 0)
  have h3 := Int.emod_lt_of_pos (lo + hi) (by norm_num : (0:ℤ) < 2)
  omega

theorem mem_ctr {lo hi : ℤ} {x : ℝ} (h1 : (lo : ℝ) ≤ x * SCALE) (h2 : x * SCALE ≤ (hi : ℝ)) :
    |x - (ctr lo hi : ℝ) / SCALE| ≤ (hal lo hi : ℝ) / SCALE := by
  have hS := SCALE_pos'
  have i1 : ctr lo hi ≤ hal lo hi + lo := by
    have h := le_max_right (hi - ctr lo hi) (ctr lo hi - lo)
    simp only [hal]; omega
  have i2 : hi ≤ hal lo hi + ctr lo hi := by
    have h := le_max_left (hi - ctr lo hi) (ctr lo hi - lo)
    simp only [hal]; omega
  have e1 : (ctr lo hi : ℝ) ≤ (hal lo hi : ℝ) + (lo : ℝ) := by exact_mod_cast i1
  have e2 : (hi : ℝ) ≤ (hal lo hi : ℝ) + (ctr lo hi : ℝ) := by exact_mod_cast i2
  have key : |x * SCALE - (ctr lo hi : ℝ)| ≤ (hal lo hi : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  have hrw : x - (ctr lo hi : ℝ) / SCALE = (x * SCALE - (ctr lo hi : ℝ)) / SCALE := by
    field_simp
  rw [hrw, abs_div, abs_of_pos hS]
  gcongr

/-- Restrict a box to the part below `m` along one axis. -/
def Bx.lower (B : Bx) (ax : Fin 3) (m : ℤ) : Bx :=
  match ax with
  | 0 => { B with uhi := m }
  | 1 => { B with vhi := m }
  | 2 => { B with thi := m }

/-- Restrict a box to the part above `m` along one axis. -/
def Bx.upper (B : Bx) (ax : Fin 3) (m : ℤ) : Bx :=
  match ax with
  | 0 => { B with ulo := m }
  | 1 => { B with vlo := m }
  | 2 => { B with tlo := m }

theorem Bx.mem_split {B : Bx} {u v t : ℝ} (h : B.Mem u v t) (ax : Fin 3) (m : ℤ) :
    (B.lower ax m).Mem u v t ∨ (B.upper ax m).Mem u v t := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := h
  fin_cases ax
  · rcases le_total (u * SCALE) (m : ℝ) with hm | hm
    · exact Or.inl ⟨⟨a1, hm⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩
    · exact Or.inr ⟨⟨hm, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩
  · rcases le_total (v * SCALE) (m : ℝ) with hm | hm
    · exact Or.inl ⟨⟨a1, a2⟩, ⟨b1, hm⟩, ⟨c1, c2⟩⟩
    · exact Or.inr ⟨⟨a1, a2⟩, ⟨hm, b2⟩, ⟨c1, c2⟩⟩
  · rcases le_total (t * SCALE) (m : ℝ) with hm | hm
    · exact Or.inl ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, hm⟩⟩
    · exact Or.inr ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨hm, c2⟩⟩

/-- The statement the covering establishes at a point. -/
def Goal (c : RT) (mg : ℤ) (ρ : Fin 5 → ℝ) (u v t : ℝ) : Prop :=
  u ≤ v → v ≤ t → u < 1 → v < 1 → t < 1 → 0 ≤ gramU u v t →
  (∀ m : Fin 5, ρ m < |Real.sqrt (2 - 2 * u) - (touchType m).1|
    ∨ ρ m < |Real.sqrt (2 - 2 * v) - (touchType m).2.1|
    ∨ ρ m < |Real.sqrt (2 - 2 * t) - (touchType m).2.2|) →
  ev c u v t + (mg : ℝ) / SCALE ≤ lamFix * ((Real.sqrt (2 - 2 * u))⁻¹
    + (Real.sqrt (2 - 2 * v))⁻¹ + (Real.sqrt (2 - 2 * t))⁻¹)

/-! ### What a leaf checks

The tangent chord of each axis is the integer square root of `SCALE·(2·SCALE − 2·centre)`, which is
`SCALE·√(2−2u)` to within one unit — any positive value is *sound* (`inv_sqrt_tangent` holds for
every `a₀ > 0`), so no proof obligation attaches to the choice. -/

/-- `⌊SCALE·√(2−2·(c/SCALE))⌋`, the tangent chord at the centre `c`. -/
def tanChord (c : ℤ) : ℤ := Int.sqrt (SCALE * (2 * SCALE - 2 * c))

/-- The S-procedure multipliers tried, in units of `SCALE⁻¹`. -/
def sigmas : List ℤ :=
  [0, 1000000000000000000000000000000000000, 3000000000000000000000000000000000000, 10000000000000000000000000000000000000, 30000000000000000000000000000000000000, 100000000000000000000000000000000000000, 300000000000000000000000000000000000000, 1000000000000000000000000000000000000000, 3000000000000000000000000000000000000000, 10000000000000000000000000000000000000000, 30000000000000000000000000000000000000000, 100000000000000000000000000000000000000000, 300000000000000000000000000000000000000000, 1000000000000000000000000000000000000000000]

/-- The check performed at a leaf, for one multiplier. -/
def leafCheck (C : IT) (mg : ℤ) (B : Bx) (n1 n2 n3 s : ℤ) : Bool :=
  0 < n1 && 0 < n2 && 0 < n3 && 0 ≤ s && B.ulo < B.uhi && B.vlo < B.vhi && B.tlo < B.thi &&
    TM.geBound mg (toTM (IshiftA (toITA (ITsub (ITsub (tanIT n1 n2 n3) C)
      (ITsmul (Itv.cst s) gramIT))).get
      (ctr B.ulo B.uhi) (ctr B.vlo B.vhi) (ctr B.tlo B.thi)).get
      (hal B.ulo B.uhi) (hal B.vlo B.vhi) (hal B.tlo B.thi))

/-- The check performed at a leaf: try each multiplier. -/
def leafAuto (C : IT) (mg : ℤ) (B : Bx) : Bool :=
  sigmas.any (fun s => leafCheck C mg B (tanChord (ctr B.ulo B.uhi))
    (tanChord (ctr B.vlo B.vhi)) (tanChord (ctr B.tlo B.thi)) s)

theorem leafCheck_sound {C : IT} {c : RT} (hC : ITMem C c) {ρ : Fin 5 → ℝ} {mg : ℤ} {B : Bx}
    {n1 n2 n3 s : ℤ} (h : leafCheck C mg B n1 n2 n3 s = true) {u v t : ℝ} (hm : B.Mem u v t) :
    Goal c mg ρ u v t := by
  simp only [leafCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩, k8⟩ := h
  intro _ _ hu1 hv1 ht1 hg _
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := hm
  exact leaf_sound hC k1 k2 k3 k4 mg _ _ _ _ _ _
    (hal_pos k5) (hal_pos k6) (hal_pos k7) k8 (mem_ctr a1 a2) (mem_ctr b1 b2) (mem_ctr c1 c2)
    hu1 hv1 ht1 hg

theorem leafAuto_sound {C : IT} {c : RT} (hC : ITMem C c) {ρ : Fin 5 → ℝ} {mg : ℤ} {B : Bx}
    (h : leafAuto C mg B = true) {u v t : ℝ} (hm : B.Mem u v t) : Goal c mg ρ u v t := by
  simp only [leafAuto, List.any_eq_true] at h
  obtain ⟨s, -, hs⟩ := h
  exact leafCheck_sound hC hs hm

end Thomson.Tri5b
