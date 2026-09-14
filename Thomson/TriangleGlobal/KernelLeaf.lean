import Thomson.Numerics.ListTaylorModel
import Thomson.TriangleGlobal.Skip

/-! # Task 5b, kernel layer, step 3: the leaf, the pruning tests and the bit-stream checker

The kernel versions of `Leaf.leafAuto`, `Skip.skipOK` and `Skip.bcheck`.  The tree, its splitting
rule and its bit stream are exactly those of `Skip.lean` (`splitAxis`, `splitPoint`, `Bx.lower`,
`Bx.upper` are reused); only the arithmetic of a leaf changes:

* the polynomial `λ(L(u)+L(v)+L(t)) − F − σ·gram` is shifted to the centre of the box and
  normalised to it by `KPoly.shsc` on nested lists, and its Taylor model is read by `KTM.toTML`;
* the S-procedure term is shifted separately (`gram` is a `3×3×3` list) so that the fourteen
  multipliers cost one shift of `F`, not fourteen;
* the tangent chord is an integer square root computed by Newton's iteration with fuel
  (`nsqrt`), which the kernel can run — `Int.sqrt` is well-founded recursion, which it cannot. -/

namespace Thomson.Tri5b

open Thomson

/-! ### An integer square root the kernel can run -/

/-- Newton's iteration from above, stopped when it no longer decreases. -/
def sqrtIter : ℕ → ℕ → ℕ → ℕ
  | 0, _, x => x
  | fuel + 1, n, x => let y := (x + n / x) / 2; if x ≤ y then x else sqrtIter fuel n y

/-- `⌊√n⌋`, started from a power of two above `√n`.  Only positivity is ever used. -/
def nsqrt (n : ℕ) : ℕ := if n = 0 then 0 else sqrtIter 200 n (2 ^ (Nat.log2 n / 2 + 1))

/-- The tangent chord at the centre `c`: `⌊SCALE·√(2 − 2·(c/SCALE))⌋`. -/
def tanChordK (c : ℤ) : ℤ := (nsqrt (Int.toNat (SCALE * (2 * SCALE - 2 * c))) : ℤ)

/-! ### The tangent minorant and `gram`, as small nested lists -/

def tanAI (n : ℤ) : Itv :=
  Itv.mulC LAM (Itv.ofDiv (SCALE * (3 * (n * n) - 2 * SCALE2)) (2 * (n * n * n)))
def tanBI (n : ℤ) : Itv := Itv.mulC LAM (Itv.ofDiv SCALE3 (n * n * n))

/-- `λ(L(u) + L(v) + L(t))`: constant term, then the three slopes. -/
def tanL (n1 n2 n3 : ℤ) : IL3 :=
  [[[Itv.add (Itv.add (tanAI n1) (tanAI n2)) (tanAI n3), tanBI n3], [tanBI n2]], [[tanBI n1]]]

noncomputable def tanR (n1 n2 n3 : ℤ) : RL3 :=
  [[[lamFix * (tanA n1 + tanA n2 + tanA n3), lamFix * tanB n3], [lamFix * tanB n2]],
   [[lamFix * tanB n1]]]

theorem lamFix_eq : lamFix = (LAM : ℝ) / SCALE := by unfold lamFix LAM SCALE; norm_num

theorem mem_tanAI {n : ℤ} (hn : 0 < n) : (tanAI n).Mem (lamFix * tanA n) := by
  rw [lamFix_eq]; unfold tanAI tanA
  exact Itv.mem_mulC (Itv.mem_ofDiv (by positivity)) LAM

theorem mem_tanBI {n : ℤ} (hn : 0 < n) : (tanBI n).Mem (lamFix * tanB n) := by
  rw [lamFix_eq]; unfold tanBI tanB
  exact Itv.mem_mulC (Itv.mem_ofDiv (by positivity)) LAM

theorem Mem3_tanL {n1 n2 n3 : ℤ} (h1 : 0 < n1) (h2 : 0 < n2) (h3 : 0 < n3) :
    Mem3 (tanL n1 n2 n3) (tanR n1 n2 n3) := by
  have hA : (Itv.add (Itv.add (tanAI n1) (tanAI n2)) (tanAI n3)).Mem
      (lamFix * (tanA n1 + tanA n2 + tanA n3)) := by
    have := Itv.mem_add (Itv.mem_add (mem_tanAI h1) (mem_tanAI h2)) (mem_tanAI h3)
    rwa [show lamFix * (tanA n1 + tanA n2 + tanA n3)
        = lamFix * tanA n1 + lamFix * tanA n2 + lamFix * tanA n3 by ring]
  unfold tanL tanR Mem3 Mem2 Mem1
  exact List.Forall₂.cons
    (List.Forall₂.cons (List.Forall₂.cons hA (List.Forall₂.cons (mem_tanBI h3) List.Forall₂.nil))
      (List.Forall₂.cons (List.Forall₂.cons (mem_tanBI h2) List.Forall₂.nil) List.Forall₂.nil))
    (List.Forall₂.cons (List.Forall₂.cons (List.Forall₂.cons (mem_tanBI h1) List.Forall₂.nil)
      List.Forall₂.nil) List.Forall₂.nil)

theorem ev3_tanR (n1 n2 n3 : ℤ) (u v t : ℝ) :
    ev3 (tanR n1 n2 n3) u v t
      = lamFix * (tanA n1 + tanB n1 * u) + lamFix * (tanA n2 + tanB n2 * v)
        + lamFix * (tanA n3 + tanB n3 * t) := by
  simp [tanR]; ring

/-- `gram = 1 + 2uvt − u² − v² − t²` as a sparse nested list. -/
def gramL : IL3 :=
  [[[Itv.cst SCALE, Itv.zero, Itv.cst (-SCALE)], [], [Itv.cst (-SCALE)]],
   [[], [Itv.zero, Itv.cst (2 * SCALE)]],
   [[Itv.cst (-SCALE)]]]

def gramR : RL3 := [[[1, 0, -1], [], [-1]], [[], [0, 2]], [[-1]]]

theorem mem_cst_SCALE : (Itv.cst SCALE).Mem 1 := by
  have := Itv.mem_cst SCALE
  rwa [div_self (ne_of_gt SCALE_pos')] at this

theorem mem_cst_two_SCALE : (Itv.cst (2 * SCALE)).Mem 2 := by
  have := Itv.mem_cst (2 * SCALE)
  rwa [Int.cast_mul, mul_div_assoc, div_self (ne_of_gt SCALE_pos'), mul_one] at this

theorem mem_cst_neg_SCALE : (Itv.cst (-SCALE)).Mem (-1) := by
  have := Itv.mem_cst (-SCALE)
  rwa [Int.cast_neg, neg_div, div_self (ne_of_gt SCALE_pos')] at this

theorem Mem3_gramL : Mem3 gramL gramR := by
  unfold gramL gramR Mem3 Mem2 Mem1
  exact List.Forall₂.cons
    (List.Forall₂.cons (List.Forall₂.cons mem_cst_SCALE (List.Forall₂.cons Itv.mem_zero
        (List.Forall₂.cons mem_cst_neg_SCALE List.Forall₂.nil)))
      (List.Forall₂.cons List.Forall₂.nil
        (List.Forall₂.cons (List.Forall₂.cons mem_cst_neg_SCALE List.Forall₂.nil) List.Forall₂.nil)))
    (List.Forall₂.cons
      (List.Forall₂.cons List.Forall₂.nil
        (List.Forall₂.cons (List.Forall₂.cons Itv.mem_zero
          (List.Forall₂.cons mem_cst_two_SCALE List.Forall₂.nil)) List.Forall₂.nil))
      (List.Forall₂.cons
        (List.Forall₂.cons (List.Forall₂.cons mem_cst_neg_SCALE List.Forall₂.nil) List.Forall₂.nil)
        List.Forall₂.nil))

theorem ev3_gramR (u v t : ℝ) : ev3 gramR u v t = gramU u v t := by
  simp [gramR, gramU]; ring

/-! ### A Taylor model on a box, in normalised coordinates -/

/-- The normalised coordinate of `u` in the box `centre ± half`. -/
noncomputable def nc (u : ℝ) (a h : ℤ) : ℝ := (u - (a : ℝ) / SCALE) / ((h : ℝ) / SCALE)

theorem nc_abs_le {u : ℝ} {a h : ℤ} (hh : 0 < h) (hu : |u - (a : ℝ) / SCALE| ≤ (h : ℝ) / SCALE) :
    |nc u a h| ≤ 1 := by
  have p : (0:ℝ) < (h : ℝ) / SCALE := by
    apply div_pos _ SCALE_pos'; exact_mod_cast hh
  rw [nc, abs_div, abs_of_pos p, div_le_one p]; exact hu

theorem nc_eq {u : ℝ} {a h : ℤ} (hh : 0 < h) :
    (a : ℝ) / SCALE + (h : ℝ) / SCALE * nc u a h = u := by
  have p : (0:ℝ) < (h : ℝ) / SCALE := by
    apply div_pos _ SCALE_pos'; exact_mod_cast hh
  have : (h : ℝ) / SCALE * nc u a h = u - (a : ℝ) / SCALE := by
    rw [nc, mul_div_cancel₀ _ (ne_of_gt p)]
  linarith

/-- A Taylor model certified on the normalised box bounds the real polynomial there. -/
theorem tm_box_sound {U : IL3} {uR : RL3} (hU : Mem3 U uR) (mg : ℤ) (a b d h1 h2 h3 : ℤ)
    (hh1 : 0 < h1) (hh2 : 0 < h2) (hh3 : 0 < h3)
    (hpos : TM.geBound mg (toTML U) = true) {u v w : ℝ}
    (hu : |u - (a : ℝ) / SCALE| ≤ (h1 : ℝ) / SCALE)
    (hv : |v - (b : ℝ) / SCALE| ≤ (h2 : ℝ) / SCALE)
    (hw : |w - (d : ℝ) / SCALE| ≤ (h3 : ℝ) / SCALE) :
    (mg : ℝ) / SCALE ≤ ev3 uR (nc u a h1) (nc v b h2) (nc w d h3) := by
  have hbox : TM.Box (nc u a h1) (nc v b h2) (nc w d h3) :=
    ⟨nc_abs_le hh1 hu, nc_abs_le hh2 hv, nc_abs_le hh3 hw⟩
  exact TM.geBound_sound hbox (toTML_mem hU hbox) hpos

/-! ### The pruning tests -/

/-- `gram < 0` on the whole box: `−gram ≥ SCALE⁻¹` by its Taylor model. -/
def kgramOut (B : Bx) : Bool :=
  B.ulo < B.uhi && B.vlo < B.vhi && B.tlo < B.thi &&
    TM.geBound 1 (toTML (shsc (ctr B.ulo B.uhi) (ctr B.vlo B.vhi) (ctr B.tlo B.thi)
      (hal B.ulo B.uhi) (hal B.vlo B.vhi) (hal B.tlo B.thi) (smulI3 (-SCALE) gramL)))

theorem kgramOut_sound {B : Bx} (h : kgramOut B = true) {u v t : ℝ} (hm : B.Mem u v t)
    (hg : 0 ≤ gramU u v t) : False := by
  simp only [kgramOut, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨k1, k2⟩, k3⟩, k4⟩ := h
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := hm
  have hb := tm_box_sound (Mem3_shsc (Mem3_smulI3 Mem3_gramL (-SCALE)) _ _ _
      (hal_pos k1).le (hal_pos k2).le (hal_pos k3).le) 1 _ _ _ _ _ _
    (hal_pos k1) (hal_pos k2) (hal_pos k3) k4 (mem_ctr a1 a2) (mem_ctr b1 b2) (mem_ctr c1 c2)
  rw [ev3_shscR, nc_eq (hal_pos k1), nc_eq (hal_pos k2), nc_eq (hal_pos k3), ev3_smulR3,
    ev3_gramR] at hb
  have hneg : ((-SCALE : ℤ) : ℝ) / SCALE = -1 := by
    push_cast; rw [neg_div, div_self (ne_of_gt SCALE_pos')]
  rw [hneg] at hb
  have hpos : (0:ℝ) < 1 / SCALE := by have := SCALE_pos'; positivity
  push_cast at hb
  linarith

/-- The three pruning tests: sorted cone, `gram < 0`, inside a local cube. -/
def kskipOK (D : CubeData) (B : Bx) : Bool :=
  (B.vhi < B.ulo) || (B.thi < B.vlo) || kgramOut B ||
  (List.finRange 5).any (fun m =>
    D.lo m 0 ≤ B.ulo && B.uhi ≤ D.hi m 0 && D.lo m 1 ≤ B.vlo && B.vhi ≤ D.hi m 1 &&
    D.lo m 2 ≤ B.tlo && B.thi ≤ D.hi m 2)

theorem kskipOK_sound {D : CubeData} {ρ : Fin 5 → ℝ} (hD : CubeSound D ρ) {c : RT}
    {mg : ℤ} (B : Bx) (h : kskipOK D B = true) (u v t : ℝ) (hm : B.Mem u v t) :
    Goal c mg ρ u v t := by
  have hm' := hm
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := hm
  intro huv hvt hu1 hv1 ht1 hg hout
  simp only [kskipOK, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
    Bool.and_eq_true] at h
  have hS := SCALE_pos'
  rcases h with ((hs1 | hs2) | hgram) | hcube
  · exfalso
    have : ((B.vhi : ℤ) : ℝ) < ((B.ulo : ℤ) : ℝ) := by exact_mod_cast hs1
    nlinarith
  · exfalso
    have : ((B.thi : ℤ) : ℝ) < ((B.vlo : ℤ) : ℝ) := by exact_mod_cast hs2
    nlinarith
  · exact (kgramOut_sound hgram hm' hg).elim
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

/-! ### The leaf -/

/-- The check at a leaf: one shift of `λ(L(u)+L(v)+L(t)) − F`, one of `gram`, and the fourteen
S-procedure multipliers tried on the two. -/
def kleafCheck (CL : IL3) (mg : ℤ) (B : Bx) : Bool :=
  let a := ctr B.ulo B.uhi
  let b := ctr B.vlo B.vhi
  let d := ctr B.tlo B.thi
  let h1 := hal B.ulo B.uhi
  let h2 := hal B.vlo B.vhi
  let h3 := hal B.tlo B.thi
  let n1 := tanChordK a
  let n2 := tanChordK b
  let n3 := tanChordK d
  0 < n1 && 0 < n2 && 0 < n3 && B.ulo < B.uhi && B.vlo < B.vhi && B.tlo < B.thi &&
  (let S := shsc a b d h1 h2 h3 (subI3 (tanL n1 n2 n3) CL)
   let T := shsc a b d h1 h2 h3 gramL
   sigmas.any fun s => 0 ≤ s && TM.geBound mg (toTML (subI3 S (smulI3 s T))))

set_option maxRecDepth 8000 in
/-- **One leaf.**  The list version of `Leaf.leaf_sound`. -/
theorem kleaf_sound {CL : IL3} {c : RT} (hC : Mem3 CL (ofRT c))
    {n1 n2 n3 : ℤ} (hn1 : 0 < n1) (hn2 : 0 < n2) (hn3 : 0 < n3)
    {s : ℤ} (hs : 0 ≤ s) (mg : ℤ)
    (a b d h1 h2 h3 : ℤ) (hh1 : 0 < h1) (hh2 : 0 < h2) (hh3 : 0 < h3)
    (hcheck : TM.geBound mg (toTML (subI3 (shsc a b d h1 h2 h3 (subI3 (tanL n1 n2 n3) CL))
        (smulI3 s (shsc a b d h1 h2 h3 gramL)))) = true)
    {u v t : ℝ}
    (hu : |u - (a : ℝ) / SCALE| ≤ (h1 : ℝ) / SCALE)
    (hv : |v - (b : ℝ) / SCALE| ≤ (h2 : ℝ) / SCALE)
    (ht : |t - (d : ℝ) / SCALE| ≤ (h3 : ℝ) / SCALE)
    (hu1 : u < 1) (hv1 : v < 1) (ht1 : t < 1) (hgram : 0 ≤ gramU u v t) :
    ev c u v t + (mg : ℝ) / SCALE ≤ lamFix * ((Real.sqrt (2 - 2 * u))⁻¹
      + (Real.sqrt (2 - 2 * v))⁻¹ + (Real.sqrt (2 - 2 * t))⁻¹) := by
  have hmem := Mem3_subI3
    (Mem3_shsc (Mem3_subI3 (Mem3_tanL hn1 hn2 hn3) hC) a b d hh1.le hh2.le hh3.le)
    (Mem3_smulI3 (Mem3_shsc Mem3_gramL a b d hh1.le hh2.le hh3.le) s)
  have hpos := tm_box_sound hmem mg a b d h1 h2 h3 hh1 hh2 hh3 hcheck hu hv ht
  rw [ev3_subR3, ev3_smulR3, ev3_shscR, ev3_shscR, nc_eq hh1, nc_eq hh2, nc_eq hh3,
    ev3_subR3, ev3_tanR, ev3_ofRT, ev3_gramR] at hpos
  have hσ : (0:ℝ) ≤ (s : ℝ) / SCALE := by
    apply div_nonneg _ (le_of_lt SCALE_pos'); exact_mod_cast hs
  have hlam : (0:ℝ) < lamFix := by unfold lamFix; norm_num
  have l1 := tan_le hn1 hu1
  have l2 := tan_le hn2 hv1
  have l3 := tan_le hn3 ht1
  have hprod : 0 ≤ (s : ℝ) / SCALE * gramU u v t := mul_nonneg hσ hgram
  have m1 := mul_le_mul_of_nonneg_left l1 hlam.le
  have m2 := mul_le_mul_of_nonneg_left l2 hlam.le
  have m3 := mul_le_mul_of_nonneg_left l3 hlam.le
  clear hcheck hmem l1 l2 l3
  linarith

theorem kleafCheck_sound {CL : IL3} {c : RT} (hC : Mem3 CL (ofRT c)) {ρ : Fin 5 → ℝ} {mg : ℤ}
    {B : Bx} (h : kleafCheck CL mg B = true) {u v t : ℝ} (hm : B.Mem u v t) :
    Goal c mg ρ u v t := by
  simp only [kleafCheck, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, s, -, hs, hge⟩ := h
  intro _ _ hu1 hv1 ht1 hg _
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := hm
  exact kleaf_sound hC k1 k2 k3 hs mg _ _ _ _ _ _ (hal_pos k4) (hal_pos k5) (hal_pos k6) hge
    (mem_ctr a1 a2) (mem_ctr b1 b2) (mem_ctr c1 c2) hu1 hv1 ht1 hg

/-! ### The bit-stream checker -/

/-- The checker: read the tree from the bits of `n`, in pre-order (`Skip.bcheck`, with the
kernel leaf and pruning tests). -/
def kbcheck (CL : IL3) (mg : ℤ) (D : CubeData) : ℕ → ℕ → Bx → Option ℕ
  | 0, _, _ => none
  | fuel + 1, bits, B =>
      if bits % 2 = 0 then
        (if kskipOK D B || kleafCheck CL mg B then some (bits / 2) else none)
      else
        match kbcheck CL mg D fuel (bits / 2)
            (B.lower (splitAxis B) (splitPoint D B (splitAxis B))) with
        | none => none
        | some r => kbcheck CL mg D fuel r (B.upper (splitAxis B) (splitPoint D B (splitAxis B)))

theorem kbcheck_sound {CL : IL3} {c : RT} (hC : Mem3 CL (ofRT c)) {ρ : Fin 5 → ℝ} {mg : ℤ}
    {D : CubeData} (hD : CubeSound D ρ) :
    ∀ (fuel bits : ℕ) (B : Bx) (r : ℕ), kbcheck CL mg D fuel bits B = some r →
      ∀ u v t : ℝ, B.Mem u v t → Goal c mg ρ u v t := by
  intro fuel
  induction fuel with
  | zero => intro bits B r h; simp [kbcheck] at h
  | succ fuel ih =>
      intro bits B r h u v t hm
      rw [kbcheck] at h
      split at h
      · split at h
        · rename_i hok
          rcases Bool.or_eq_true _ _ |>.mp hok with hs | hl
          · exact kskipOK_sound hD B hs u v t hm
          · exact kleafCheck_sound hC hl hm
        · simp at h
      · rcases Bx.mem_split hm (splitAxis B) (splitPoint D B (splitAxis B)) with hl | hr
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

theorem covers_of_kbcheck {CL : IL3} {c : RT} (hC : Mem3 CL (ofRT c)) {ρ : Fin 5 → ℝ} {mg : ℤ}
    {D : CubeData} (hD : CubeSound D ρ) (fuel bits : ℕ) (B : Bx) (r : ℕ)
    (h : kbcheck CL mg D fuel bits B = some r) : Covers c mg ρ B :=
  fun u v t hm => kbcheck_sound hC hD fuel bits B r h u v t hm

end Thomson.Tri5b
