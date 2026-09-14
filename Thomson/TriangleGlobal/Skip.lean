import Thomson.TriangleGlobal.Cover
import Thomson.TriangleGlobal.Main

/-! # Task 5b, step 11: pruning, the bit-stream checker, and the assembly

A leaf may be *skipped* when the point carries no obligation there: the box misses the sorted cone
`u ≤ v ≤ t`, or `gram < 0` throughout it, or it lies inside one of the five local cubes where Task
5a takes over.  The only numerical data are fixed-point endpoints for the image of each cube under
`u ↦ √(2−2u)`; everything else the checker computes.

The certificate is then a single natural number, read as a stream of bits in pre-order: `0` closes
a leaf, `1` splits the box (longest axis; at a cube face if one crosses it, else at the midpoint). -/

namespace Thomson.Tri5b

open Thomson

/-- The `i`-th chord of the `m`-th touching type. -/
noncomputable def chordOf (m : Fin 5) : Fin 3 → ℝ :=
  ![(touchType m).1, (touchType m).2.1, (touchType m).2.2]

/-- A box of `u`-values inside the image of a cube. -/
theorem in_cube_of_u {τ ρ u : ℝ} (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ - ρ)
    (h1 : 1 - (τ + ρ) ^ 2 / 2 ≤ u) (h2 : u ≤ 1 - (τ - ρ) ^ 2 / 2) :
    |Real.sqrt (2 - 2 * u) - τ| ≤ ρ := by
  have e1 : (τ - ρ) ^ 2 ≤ 2 - 2 * u := by nlinarith
  have e2 : 2 - 2 * u ≤ (τ + ρ) ^ 2 := by nlinarith
  have hlo : τ - ρ ≤ Real.sqrt (2 - 2 * u) := by
    rw [show τ - ρ = Real.sqrt ((τ - ρ) ^ 2) from (Real.sqrt_sq hτ).symm]
    exact Real.sqrt_le_sqrt e1
  have hhi : Real.sqrt (2 - 2 * u) ≤ τ + ρ := by
    rw [show τ + ρ = Real.sqrt ((τ + ρ) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt e2
  rw [abs_le]; constructor <;> linarith

/-- Fixed-point endpoints for the image of each local cube. -/
structure CubeData where
  lo : Fin 5 → Fin 3 → ℤ
  hi : Fin 5 → Fin 3 → ℤ

/-- The endpoints are correct. -/
def CubeSound (D : CubeData) (ρ : Fin 5 → ℝ) : Prop :=
  ∀ (m : Fin 5) (i : Fin 3) (u : ℝ), (D.lo m i : ℝ) ≤ u * SCALE → u * SCALE ≤ (D.hi m i : ℝ) →
    |Real.sqrt (2 - 2 * u) - chordOf m i| ≤ ρ m

/-- `-gram`, tabulated.  A closed term: the interpreter builds it once for the whole run, not
once per node. -/
def negGramA : ITA := toITA (ITsmul (Itv.cst (-SCALE)) gramIT)

/-- The three pruning tests. -/
def skipOK (D : CubeData) (C : IT) (B : Bx) : Bool :=
  (B.vhi < B.ulo) || (B.thi < B.vlo) ||
  (B.ulo < B.uhi && B.vlo < B.vhi && B.tlo < B.thi &&
    TM.geBound 1 (toTM (IshiftA negGramA.get
      (ctr B.ulo B.uhi) (ctr B.vlo B.vhi) (ctr B.tlo B.thi)).get
      (hal B.ulo B.uhi) (hal B.vlo B.vhi) (hal B.tlo B.thi))) ||
  (List.finRange 5).any (fun m =>
    D.lo m 0 ≤ B.ulo && B.uhi ≤ D.hi m 0 && D.lo m 1 ≤ B.vlo && B.vhi ≤ D.hi m 1 &&
    D.lo m 2 ≤ B.tlo && B.thi ≤ D.hi m 2)

set_option maxRecDepth 8000 in
theorem skipOK_sound {D : CubeData} {ρ : Fin 5 → ℝ} (hD : CubeSound D ρ) {C : IT} {c : RT}
    {mg : ℤ} (B : Bx) (h : skipOK D C B = true) (u v t : ℝ) (hm : B.Mem u v t) :
    Goal c mg ρ u v t := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := hm
  intro huv hvt hu1 hv1 ht1 hg hout
  simp only [skipOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  have hS := SCALE_pos'
  rcases h with ((hs1 | hs2) | hgram) | hcube
  · exfalso
    have : ((B.vhi : ℤ) : ℝ) < ((B.ulo : ℤ) : ℝ) := by exact_mod_cast hs1
    nlinarith
  · exfalso
    have : ((B.thi : ℤ) : ℝ) < ((B.vlo : ℤ) : ℝ) := by exact_mod_cast hs2
    nlinarith
  · exfalso
    obtain ⟨⟨⟨k1, k2⟩, k3⟩, k4⟩ := hgram
    have hb := box_sound (C := negGramA.get)
      (ITMem_toITA (ITMem_smul (Itv.mem_cst (-SCALE)) ITMem_gram)) 1
      (ctr B.ulo B.uhi) (ctr B.vlo B.vhi) (ctr B.tlo B.thi)
      (hal B.ulo B.uhi) (hal B.vlo B.vhi) (hal B.tlo B.thi)
      (hal_pos k1) (hal_pos k2) (hal_pos k3) k4 (mem_ctr a1 a2) (mem_ctr b1 b2) (mem_ctr c1 c2)
    rw [ev_smul, ev_gramRT] at hb
    have hneg : ((-SCALE : ℤ) : ℝ) / SCALE = -1 := by
      push_cast; rw [neg_div, div_self (ne_of_gt hS)]
    rw [hneg] at hb
    have h1 : (0:ℝ) < (1:ℝ) / SCALE := by positivity
    clear k4        -- its statement mentions `toITA`, which `nlinarith` would try to unfold
    nlinarith
  · exfalso
    obtain ⟨m, -, hm5⟩ := hcube
    obtain ⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩ := hm5
    have q1 : ((D.lo m 0 : ℤ) : ℝ) ≤ (B.ulo : ℝ) := by exact_mod_cast p1
    have q2 : ((B.uhi : ℤ) : ℝ) ≤ (D.hi m 0 : ℝ) := by exact_mod_cast p2
    have q3 : ((D.lo m 1 : ℤ) : ℝ) ≤ (B.vlo : ℝ) := by exact_mod_cast p3
    have q4 : ((B.vhi : ℤ) : ℝ) ≤ (D.hi m 1 : ℝ) := by exact_mod_cast p4
    have q5 : ((D.lo m 2 : ℤ) : ℝ) ≤ (B.tlo : ℝ) := by exact_mod_cast p5
    have q6 : ((B.thi : ℤ) : ℝ) ≤ (D.hi m 2 : ℝ) := by exact_mod_cast p6
    have c0 := hD m 0 u (by linarith) (by linarith)
    have c1' := hD m 1 v (by linarith) (by linarith)
    have c2' := hD m 2 t (by linarith) (by linarith)
    simp only [chordOf, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at c0 c1' c2'
    rcases hout m with h' | h' | h' <;> linarith

/-! ### The splitting rule and the bit-stream checker -/

def splitAxis (B : Bx) : Fin 3 :=
  if B.vhi - B.vlo ≤ B.uhi - B.ulo ∧ B.thi - B.tlo ≤ B.uhi - B.ulo then 0
  else if B.thi - B.tlo ≤ B.vhi - B.vlo then 1 else 2

def facesIn (D : CubeData) (B : Bx) (ax : Fin 3) : List ℤ :=
  ((List.finRange 5).flatMap (fun m => [D.lo m ax, D.hi m ax])).filter
    (fun f => B.lo ax < f && f < B.hi ax)

def splitPoint (D : CubeData) (B : Bx) (ax : Fin 3) : ℤ :=
  match facesIn D B ax with
  | [] => ctr (B.lo ax) (B.hi ax)
  | f :: fs => fs.foldl min f

/-- The checker: read the tree from the bits of `n`, in pre-order. -/
def bcheck (C : IT) (mg : ℤ) (D : CubeData) : ℕ → ℕ → Bx → Option ℕ
  | 0, _, _ => none
  | fuel + 1, bits, B =>
      if bits % 2 = 0 then
        (if skipOK D C B || leafAuto C mg B then some (bits / 2) else none)
      else
        match bcheck C mg D fuel (bits / 2)
            (B.lower (splitAxis B) (splitPoint D B (splitAxis B))) with
        | none => none
        | some r => bcheck C mg D fuel r (B.upper (splitAxis B) (splitPoint D B (splitAxis B)))

theorem bcheck_sound {C : IT} {c : RT} (hC : ITMem C c) {ρ : Fin 5 → ℝ} {mg : ℤ} {D : CubeData}
    (hD : CubeSound D ρ) :
    ∀ (fuel bits : ℕ) (B : Bx) (r : ℕ), bcheck C mg D fuel bits B = some r →
      ∀ u v t : ℝ, B.Mem u v t → Goal c mg ρ u v t := by
  intro fuel
  induction fuel with
  | zero => intro bits B r h; simp [bcheck] at h
  | succ fuel ih =>
      intro bits B r h u v t hm
      rw [bcheck] at h
      split at h
      · -- a leaf
        split at h
        · rename_i hok
          rcases Bool.or_eq_true _ _ |>.mp hok with hs | hl
          · exact skipOK_sound hD B hs u v t hm
          · exact leafAuto_sound hC hl hm
        · simp at h
      · -- a split
        rcases Bx.mem_split hm (splitAxis B) (splitPoint D B (splitAxis B)) with hl | hr
        · revert h
          split
          · intro h; simp at h
          · rename_i r' hc
            intro _
            exact ih _ _ _ hc u v t hl
        · revert h
          split
          · intro h; simp at h
          · rename_i r' hc
            intro h
            exact ih _ _ _ h u v t hr


/-! ### Covering a box in several pieces

A box may be covered piece by piece, each piece checked by its own `decide +kernel` (the kernel
layer, `KLeaf.lean`; about 4 s per leaf) in its own module — which `lake` then builds in
parallel. -/

/-- Every point of `B` satisfies the goal. -/
def Covers (c : RT) (mg : ℤ) (ρ : Fin 5 → ℝ) (B : Bx) : Prop :=
  ∀ u v t : ℝ, B.Mem u v t → Goal c mg ρ u v t

theorem covers_of_bcheck {C : IT} {c : RT} (hC : ITMem C c) {ρ : Fin 5 → ℝ} {mg : ℤ}
    {D : CubeData} (hD : CubeSound D ρ) (fuel bits : ℕ) (B : Bx) (r : ℕ)
    (h : bcheck C mg D fuel bits B = some r) : Covers c mg ρ B :=
  fun u v t hm => bcheck_sound hC hD fuel bits B r h u v t hm

theorem covers_split {c : RT} {mg : ℤ} {ρ : Fin 5 → ℝ} {B : Bx} (ax : Fin 3) (m : ℤ)
    (hlo : Covers c mg ρ (B.lower ax m)) (hhi : Covers c mg ρ (B.upper ax m)) :
    Covers c mg ρ B := by
  intro u v t hm
  rcases Bx.mem_split hm ax m with h | h
  · exact hlo u v t h
  · exact hhi u v t h

/-! ## From the covering to Task 5 -/

/-- `uHi` on the fixed-point grid: `1 − (9619/10000)²/2 = 107474839/200000000`. -/
def UHI : ℤ := 5373741950000000000000000000000000000000

theorem uHi_mul_SCALE : uHi * SCALE = (UHI : ℝ) := by
  unfold uHi chordLo UHI SCALE
  norm_num

/-- **The covering gives `NumCertU`.** -/
theorem numCertU_of_covers {c : RT}
    (hev : ∀ u v t : ℝ, ev c u v t = Fh (Hp pivots) u v t)
    {ρ : Fin 5 → ℝ} {mg : ℤ}
    (root : Bx) (hcov : Covers c mg ρ root)
    (h1 : root.ulo ≤ -SCALE) (h2 : UHI ≤ root.uhi)
    (h3 : root.vlo ≤ -SCALE) (h4 : UHI ≤ root.vhi)
    (h5 : root.tlo ≤ -SCALE) (h6 : UHI ≤ root.thi) :
    NumCertU ρ ((mg : ℝ) / SCALE) := by
  intro u v t hu1 huv hvt htU hg hout
  have hS := SCALE_pos'
  have hone : uHi < 1 := by unfold uHi chordLo; norm_num
  have hv1 : (-1:ℝ) ≤ v := le_trans hu1 huv
  have ht1 : (-1:ℝ) ≤ t := le_trans hv1 hvt
  have f1 : (-SCALE : ℝ) ≤ u * SCALE := by nlinarith
  have f2 : (-SCALE : ℝ) ≤ v * SCALE := by nlinarith
  have f3 : (-SCALE : ℝ) ≤ t * SCALE := by nlinarith
  have g1 : u * SCALE ≤ (UHI : ℝ) := by
    rw [← uHi_mul_SCALE]; nlinarith [le_trans huv (le_trans hvt htU)]
  have g2 : v * SCALE ≤ (UHI : ℝ) := by
    rw [← uHi_mul_SCALE]; nlinarith [le_trans hvt htU]
  have g3 : t * SCALE ≤ (UHI : ℝ) := by rw [← uHi_mul_SCALE]; nlinarith
  have c1 : ((root.ulo : ℤ) : ℝ) ≤ -SCALE := by exact_mod_cast h1
  have c2 : ((UHI : ℤ) : ℝ) ≤ (root.uhi : ℝ) := by exact_mod_cast h2
  have c3 : ((root.vlo : ℤ) : ℝ) ≤ -SCALE := by exact_mod_cast h3
  have c4 : ((UHI : ℤ) : ℝ) ≤ (root.vhi : ℝ) := by exact_mod_cast h4
  have c5 : ((root.tlo : ℤ) : ℝ) ≤ -SCALE := by exact_mod_cast h5
  have c6 : ((UHI : ℤ) : ℝ) ≤ (root.thi : ℝ) := by exact_mod_cast h6
  have hmem : root.Mem u v t :=
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have := hcov u v t hmem huv hvt
    (by linarith [le_trans huv (le_trans hvt htU)]) (by linarith [le_trans hvt htU])
    (by linarith) hg hout
  rw [hev] at this
  linarith

/-- **Task 5 from the covering data.**  The hypotheses are: the tensor of `F` for the *true*
certificate and its correctness; the images of the five cubes; the covering tree with its margin
and a root box containing the whole inner-product range; and Task 5a. -/
theorem task5_of_data {c : RT}
    (hev : ∀ u v t : ℝ, ev c u v t = Fh (Hp pivots) u v t)
    {ρ : Fin 5 → ℝ} {mg : ℤ} (hmg : 0 ≤ mg) (root : Bx) (hcov : Covers c mg ρ root)
    (h1 : root.ulo ≤ -SCALE) (h2 : UHI ≤ root.uhi)
    (h3 : root.vlo ≤ -SCALE) (h4 : UHI ≤ root.vhi)
    (h5 : root.tlo ≤ -SCALE) (h6 : UHI ≤ root.thi)
    (hloc : TriLocal ρ) :
    ∀ a b c : ℝ, chordLo ≤ a → chordLo ≤ b → chordLo ≤ c → a ≤ 2 → b ≤ 2 → c ≤ 2 →
      0 ≤ gram a b c → 0 ≤ triP pivots a b c := by
  have hnum : NumCertU ρ ((mg : ℝ) / SCALE) :=
    numCertU_of_covers hev root hcov h1 h2 h3 h4 h5 h6
  have hm0 : (0:ℝ) ≤ (mg : ℝ) / SCALE := by
    apply div_nonneg _ (le_of_lt SCALE_pos'); exact_mod_cast hmg
  exact tri_nonneg_of_numCertU (ρ := ρ) hm0 hloc hnum

end Thomson.Tri5b