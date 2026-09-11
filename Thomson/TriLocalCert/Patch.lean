import Thomson.Tri5b.Interval

/-! # Task 5a, numeric side, step 1: the bracket on the cube, by a patch covering

Task 5a's calculus (`Thomson/ThreePoint/Cert/TriLocal4*.lean`) bounds `triP p (τ + δ)` below by

`B(δ) = Q(δ)/2 + K(δ)/6 − M·‖δ‖⁴/24`,  `Q(δ) = Σ H_ab δ_a δ_b`, `K(δ) = Σ C_abc δ_a δ_b δ_c`,

with `H`, `C` the second and third partial derivatives of `triP p` at the touching type and `M` a
bound for the fourth derivative on the cube `|δ_i| ≤ ρ`, `ρ = 1/500`.  This file proves `B ≥ 0` on
the cube for **every** `H`, `C`, `M` in given interval data, from a `Bool` check:

* by homogeneity, `B(s·e) ≥ s²·g(e)` for `0 ≤ s ≤ 1`, where `g(e) = Q(e)/2 − |K(e)|/6 − M‖e‖⁴/24`
  (`bracket_ge`); every point of the cube is `s·e` with `e` on its surface;
* each of the six faces `e_f = ±ρ` is covered by a quadtree of square patches (`qtOK`), and on each
  patch `g ≥ 0` is checked in interval arithmetic (`boxOK`): `Q` in centred form (it is small only
  near the softest Hessian direction, where its gradient is small too), `K` and `‖e‖⁴` directly.

Everything is fixed point at `10⁻⁴⁰` (`Thomson.Tri5b.Itv`); `decide +kernel` runs the check. -/

namespace Thomson.TriLocalCert

open Thomson.Tri5b Finset

/-! ## The forms -/

/-- `Q(e) = Σ_{a,b} H_ab e_a e_b`. -/
noncomputable def Qf (H : Fin 3 → Fin 3 → ℝ) (e : Fin 3 → ℝ) : ℝ := ∑ a, ∑ b, H a b * e a * e b

/-- `K(e) = Σ_{a,b,c} C_abc e_a e_b e_c`. -/
noncomputable def Kf (C : Fin 3 → Fin 3 → Fin 3 → ℝ) (e : Fin 3 → ℝ) : ℝ :=
  ∑ a, ∑ b, ∑ c, C a b c * e a * e b * e c

/-- `‖e‖²`, written as in Task 5a's `taylor4_lower`. -/
noncomputable def N2 (e : Fin 3 → ℝ) : ℝ := e 0 ^ 2 + e 1 ^ 2 + e 2 ^ 2

/-- The bracket of `taylor4_lower`. -/
noncomputable def bracket (H : Fin 3 → Fin 3 → ℝ) (C : Fin 3 → Fin 3 → Fin 3 → ℝ) (M : ℝ) (δ : Fin 3 → ℝ) : ℝ :=
  Qf H δ / 2 + Kf C δ / 6 - M * N2 δ ^ 2 / 24

theorem Qf_smul (H : Fin 3 → Fin 3 → ℝ) (s : ℝ) (e : Fin 3 → ℝ) :
    Qf H (fun a => s * e a) = s ^ 2 * Qf H e := by
  simp only [Qf, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem Kf_smul (C : Fin 3 → Fin 3 → Fin 3 → ℝ) (s : ℝ) (e : Fin 3 → ℝ) :
    Kf C (fun a => s * e a) = s ^ 3 * Kf C e := by
  simp only [Kf, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => by ring

theorem N2_smul (s : ℝ) (e : Fin 3 → ℝ) : N2 (fun a => s * e a) = s ^ 2 * N2 e := by
  simp only [N2]; ring

/-- **Homogeneity.**  On the segment `s·e`, `0 ≤ s ≤ 1`, the bracket is at least `s²·g(e)`. -/
theorem bracket_ge (H : Fin 3 → Fin 3 → ℝ) (C : Fin 3 → Fin 3 → Fin 3 → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (e : Fin 3 → ℝ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s ^ 2 * (Qf H e / 2 - |Kf C e| / 6 - M * N2 e ^ 2 / 24) ≤ bracket H C M (fun a => s * e a) := by
  unfold bracket
  rw [Qf_smul, Kf_smul, N2_smul]
  have hK : -(s ^ 2 * |Kf C e|) ≤ s ^ 3 * Kf C e := by
    have h1 : s ^ 3 * |Kf C e| ≤ s ^ 2 * |Kf C e| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      calc s ^ 3 = s ^ 2 * s := by ring
        _ ≤ s ^ 2 * 1 := mul_le_mul_of_nonneg_left hs1 (by positivity)
        _ = s ^ 2 := by ring
    have h2 : -(s ^ 3 * |Kf C e|) ≤ s ^ 3 * Kf C e := by
      rw [neg_le, ← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_le.mp (neg_abs_le _)) (by positivity)
    linarith
  have hR : M * (s ^ 2 * N2 e) ^ 2 ≤ s ^ 2 * (M * N2 e ^ 2) := by
    have hs4 : s ^ 4 ≤ s ^ 2 := by
      calc s ^ 4 = s ^ 2 * s ^ 2 := by ring
        _ ≤ s ^ 2 * 1 := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
        _ = s ^ 2 := by ring
    have : 0 ≤ M * N2 e ^ 2 := mul_nonneg hM (sq_nonneg _)
    nlinarith
  nlinarith

/-! ## Interval data -/

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

/-- Interval data for one touching type: `H`, `C` as tables, `M` as an interval. -/
structure Data where
  H : List (List Itv)
  C : List (List (List Itv))
  M : Itv
deriving DecidableEq

def Data.h (D : Data) (a b : Fin 3) : Itv := (D.H.getD a []).getD b Itv.zero
def Data.c (D : Data) (a b c : Fin 3) : Itv := ((D.C.getD a []).getD b []).getD c Itv.zero

/-- `(H, C, M)` lies in the data. -/
structure Data.Mem (D : Data) (H : Fin 3 → Fin 3 → ℝ) (C : Fin 3 → Fin 3 → Fin 3 → ℝ) (M : ℝ) :
    Prop where
  hH : ∀ a b, (D.h a b).Mem (H a b)
  hC : ∀ a b c, (D.c a b c).Mem (C a b c)
  hM : D.M.Mem M

/-! ## One patch -/

/-- The sum over `Fin 3` in interval arithmetic. -/
def isum (f : Fin 3 → Itv) : Itv := Itv.sumL ((List.finRange 3).map f)

theorem mem_isum {f : Fin 3 → Itv} {g : Fin 3 → ℝ} (h : ∀ a, (f a).Mem (g a)) :
    (isum f).Mem (∑ a, g a) := Itv.mem_sum_fin f g h

/-- `g` on the box `e₀ ± r` (`r ≥ 0`, fixed point), enclosed from below: `Q` centred at `e₀`. -/
def boxG (D : Data) (e0 r : Fin 3 → ℤ) : Itv :=
  let E : Fin 3 → Itv := fun a => ⟨e0 a - r a, e0 a + r a⟩
  let d : Fin 3 → Itv := fun a => ⟨-r a, r a⟩
  let Q := isum fun a => isum fun b =>
    Itv.add (Itv.add (Itv.mul (D.h a b) (Itv.mul (Itv.cst (e0 a)) (Itv.cst (e0 b))))
      (Itv.mul (D.h a b) (Itv.add (Itv.mul (Itv.cst (e0 a)) (d b)) (Itv.mul (d a) (Itv.cst (e0 b))))))
      (Itv.mul (D.h a b) (Itv.mul (d a) (d b)))
  let K := isum fun a => isum fun b => isum fun c =>
    Itv.mul (D.c a b c) (Itv.mul (Itv.mul (E a) (E b)) (E c))
  let n2 := Itv.add (Itv.add (Itv.mul (E 0) (E 0)) (Itv.mul (E 1) (E 1))) (Itv.mul (E 2) (E 2))
  Itv.sub (Itv.sub (Itv.mul Q (Itv.ofDiv 1 2)) (Itv.mul (Itv.cst (aHi K)) (Itv.ofDiv 1 6)))
    (Itv.mul (Itv.mul D.M (Itv.mul n2 n2)) (Itv.ofDiv 1 24))

/-- The patch check. -/
def boxOK (D : Data) (e0 r : Fin 3 → ℤ) : Bool :=
  decide (0 ≤ (boxG D e0 r).lo) && decide (0 ≤ r 0 ∧ 0 ≤ r 1 ∧ 0 ≤ r 2)

theorem mem_half : (Itv.ofDiv 1 2).Mem (1 / 2) := by
  have := Itv.mem_ofDiv (n := 1) (d := 2) (by norm_num); norm_num at this ⊢; exact this
theorem mem_sixth : (Itv.ofDiv 1 6).Mem (1 / 6) := by
  have := Itv.mem_ofDiv (n := 1) (d := 6) (by norm_num); norm_num at this ⊢; exact this
theorem mem_24th : (Itv.ofDiv 1 24).Mem (1 / 24) := by
  have := Itv.mem_ofDiv (n := 1) (d := 24) (by norm_num); norm_num at this ⊢; exact this

/-- **Soundness of one patch.** -/
theorem boxOK_sound {D : Data} {H C M} (hD : D.Mem H C M) {e0 r : Fin 3 → ℤ}
    (hok : boxOK D e0 r = true) {e : Fin 3 → ℝ}
    (he : ∀ a, |e a * SCALE - e0 a| ≤ r a) :
    0 ≤ Qf H e / 2 - |Kf C e| / 6 - M * N2 e ^ 2 / 24 := by
  have hS : (0 : ℝ) < SCALE := SCALE_pos'
  simp only [boxOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hG, -⟩ := hok
  -- the point and the displacement, enclosed
  have hE : ∀ a, (⟨e0 a - r a, e0 a + r a⟩ : Itv).Mem (e a) := fun a => by
    have := abs_le.mp (he a); constructor <;> push_cast <;> linarith [this.1, this.2]
  have hd : ∀ a, (⟨-r a, r a⟩ : Itv).Mem (e a - e0 a / SCALE) := fun a => by
    have := abs_le.mp (he a)
    have e1 : (e a - e0 a / SCALE) * SCALE = e a * SCALE - e0 a := by field_simp
    constructor <;> rw [e1] <;> push_cast <;> linarith [this.1, this.2]
  have hc : ∀ a, (Itv.cst (e0 a)).Mem ((e0 a : ℝ) / SCALE) := fun a => Itv.mem_cst _
  -- `Q`, centred
  have hQ : (isum fun a => isum fun b =>
      Itv.add (Itv.add (Itv.mul (D.h a b) (Itv.mul (Itv.cst (e0 a)) (Itv.cst (e0 b))))
        (Itv.mul (D.h a b) (Itv.add (Itv.mul (Itv.cst (e0 a)) (⟨-r b, r b⟩ : Itv))
          (Itv.mul (⟨-r a, r a⟩ : Itv) (Itv.cst (e0 b))))))
        (Itv.mul (D.h a b) (Itv.mul (⟨-r a, r a⟩ : Itv) (⟨-r b, r b⟩ : Itv)))).Mem (Qf H e) := by
    unfold Qf
    refine mem_isum fun a => ?_
    refine mem_isum fun b => ?_
    have key := Itv.mem_add (Itv.mem_add (Itv.mem_mul (hD.hH a b) (Itv.mem_mul (hc a) (hc b)))
      (Itv.mem_mul (hD.hH a b) (Itv.mem_add (Itv.mem_mul (hc a) (hd b))
        (Itv.mem_mul (hd a) (hc b))))) (Itv.mem_mul (hD.hH a b) (Itv.mem_mul (hd a) (hd b)))
    convert key using 1
    ring
  have hK : (isum fun a => isum fun b => isum fun c =>
      Itv.mul (D.c a b c) (Itv.mul (Itv.mul (⟨e0 a - r a, e0 a + r a⟩ : Itv)
        (⟨e0 b - r b, e0 b + r b⟩ : Itv)) (⟨e0 c - r c, e0 c + r c⟩ : Itv))).Mem (Kf C e) := by
    unfold Kf
    refine mem_isum fun a => mem_isum fun b => mem_isum fun c => ?_
    have := Itv.mem_mul (hD.hC a b c) (Itv.mem_mul (Itv.mem_mul (hE a) (hE b)) (hE c))
    convert this using 1
    ring
  have hn2 := Itv.mem_add (Itv.mem_add (Itv.mem_mul (hE 0) (hE 0)) (Itv.mem_mul (hE 1) (hE 1)))
    (Itv.mem_mul (hE 2) (hE 2))
  set A := aHi (isum fun a => isum fun b => isum fun c =>
      Itv.mul (D.c a b c) (Itv.mul (Itv.mul (⟨e0 a - r a, e0 a + r a⟩ : Itv)
        (⟨e0 b - r b, e0 b + r b⟩ : Itv)) (⟨e0 c - r c, e0 c + r c⟩ : Itv))) with hA
  have hAK : |Kf C e| ≤ (A : ℝ) / SCALE := by rw [le_div_iff₀ hS]; exact abs_le_aHi hK
  have hG' := Itv.mem_sub (Itv.mem_sub (Itv.mem_mul hQ mem_half)
      (Itv.mem_mul (Itv.mem_cst A) mem_sixth))
    (Itv.mem_mul (Itv.mem_mul hD.hM (Itv.mem_mul hn2 hn2)) mem_24th)
  have hlo := hG'.1
  have hG0 : (0 : ℝ) ≤ ((boxG D e0 r).lo : ℝ) := by exact_mod_cast hG
  have hN : N2 e = e 0 * e 0 + e 1 * e 1 + e 2 * e 2 := by simp only [N2]; ring
  have hval : 0 ≤ Qf H e * (1 / 2) - (A : ℝ) / SCALE * (1 / 6)
      - M * (N2 e * N2 e) * (1 / 24) := by
    have : ((boxG D e0 r).lo : ℝ) ≤ (Qf H e * (1 / 2) - (A : ℝ) / SCALE * (1 / 6)
        - M * (N2 e * N2 e) * (1 / 24)) * SCALE := by
      rw [hN]; exact hlo
    nlinarith
  nlinarith [hval, hAK]

/-! ## A face, by a quadtree -/

/-- `ρ = 1/500` on the grid. -/
def RHO : ℤ := 20000000000000000000000000000000000000

/-- The first of the two coordinates other than `f`. -/
def fst (f : Fin 3) : Fin 3 := if f = 0 then 1 else 0

/-- The point of face `f` with face coordinate `s` and other coordinates `x` (at `fst f`), `y`. -/
def faceVec (f : Fin 3) (s x y : ℤ) : Fin 3 → ℤ := fun a =>
  if a = f then s else if a = fst f then x else y

/-- The same, on `ℝ`. -/
noncomputable def faceVecR (f : Fin 3) (s x y : ℝ) : Fin 3 → ℝ := fun a =>
  if a = f then s else if a = fst f then x else y

/-- **The quadtree check** of the face `f` with face coordinate `s`, on the square
`[x₀ ± h] × [y₀ ± h]`; the tree is a list of bits in preorder (`true`: split into four).
Returns the unread bits. -/
def qtOK (D : Data) (f : Fin 3) (s : ℤ) : ℕ → List Bool → ℤ → ℤ → ℤ → Option (List Bool)
  | 0, _, _, _, _ => none
  | _ + 1, [], _, _, _ => none
  | _ + 1, false :: rest, x0, y0, h =>
      if boxOK D (faceVec f s x0 y0) (faceVec f 0 h h) then some rest else none
  | n + 1, true :: rest, x0, y0, h =>
      if 2 * (h / 2) = h then
        match qtOK D f s n rest (x0 - h / 2) (y0 - h / 2) (h / 2) with
        | none => none
        | some r1 => match qtOK D f s n r1 (x0 - h / 2) (y0 + h / 2) (h / 2) with
          | none => none
          | some r2 => match qtOK D f s n r2 (x0 + h / 2) (y0 - h / 2) (h / 2) with
            | none => none
            | some r3 => qtOK D f s n r3 (x0 + h / 2) (y0 + h / 2) (h / 2)
      else none

theorem faceVecR_mem {f : Fin 3} {s x y : ℤ} {h : ℤ} {X Y : ℝ}
    (hx : |X * SCALE - x| ≤ h) (hy : |Y * SCALE - y| ≤ h) :
    ∀ a, |faceVecR f ((s : ℝ) / SCALE) X Y a * SCALE - faceVec f s x y a| ≤ faceVec f 0 h h a := by
  have hS : (0 : ℝ) < SCALE := SCALE_pos'
  intro a
  simp only [faceVecR, faceVec]
  split_ifs
  · rw [div_mul_cancel₀ _ hS.ne']; simp
  · exact_mod_cast hx
  · exact_mod_cast hy

/-- **Soundness of the quadtree**: every point of the square satisfies `g ≥ 0`. -/
theorem qtOK_sound {D : Data} {H C M} (hD : D.Mem H C M) {f : Fin 3} {s : ℤ} :
    ∀ (n : ℕ) (bits : List Bool) (x0 y0 h : ℤ) (rest : List Bool),
      qtOK D f s n bits x0 y0 h = some rest →
      ∀ X Y : ℝ, |X * SCALE - x0| ≤ h → |Y * SCALE - y0| ≤ h →
        0 ≤ Qf H (faceVecR f ((s : ℝ) / SCALE) X Y) / 2
          - |Kf C (faceVecR f ((s : ℝ) / SCALE) X Y)| / 6
          - M * N2 (faceVecR f ((s : ℝ) / SCALE) X Y) ^ 2 / 24 := by
  intro n
  induction n with
  | zero => intro bits x0 y0 h rest hq; simp [qtOK] at hq
  | succ n ih =>
    intro bits x0 y0 h rest hq X Y hx hy
    match bits, hq with
    | [], hq => simp [qtOK] at hq
    | false :: r, hq =>
      simp only [qtOK] at hq
      split_ifs at hq with hb
      exact boxOK_sound hD hb (faceVecR_mem hx hy)
    | true :: r, hq =>
      simp only [qtOK] at hq
      split_ifs at hq with hev
      set k := h / 2 with hk
      have hh : (h : ℝ) = 2 * k := by exact_mod_cast hev.symm
      have hx' := abs_le.mp hx; have hy' := abs_le.mp hy
      -- the child containing `(X, Y)`
      have child : ∀ (cx cy : ℤ), |X * SCALE - cx| ≤ k → |Y * SCALE - cy| ≤ k →
          (∃ r', qtOK D f s n r x0 y0 h = some r') ∨ True := fun _ _ _ _ => Or.inr trivial
      clear child
      rcases le_total (X * SCALE) x0 with hxl | hxl <;> rcases le_total (Y * SCALE) y0 with hyl | hyl
      · -- lower-left
        cases h1 : qtOK D f s n r (x0 - k) (y0 - k) k with
        | none => simp [h1] at hq
        | some r1 =>
          refine ih r (x0 - k) (y0 - k) k r1 h1 X Y ?_ ?_
          · rw [abs_le]; push_cast; constructor <;> linarith
          · rw [abs_le]; push_cast; constructor <;> linarith
      · -- lower-left in x, upper in y
        cases h1 : qtOK D f s n r (x0 - k) (y0 - k) k with
        | none => simp [h1] at hq
        | some r1 =>
          simp only [h1] at hq
          cases h2 : qtOK D f s n r1 (x0 - k) (y0 + k) k with
          | none => simp [h2] at hq
          | some r2 =>
            refine ih r1 (x0 - k) (y0 + k) k r2 h2 X Y ?_ ?_
            · rw [abs_le]; push_cast; constructor <;> linarith
            · rw [abs_le]; push_cast; constructor <;> linarith
      · cases h1 : qtOK D f s n r (x0 - k) (y0 - k) k with
        | none => simp [h1] at hq
        | some r1 =>
          simp only [h1] at hq
          cases h2 : qtOK D f s n r1 (x0 - k) (y0 + k) k with
          | none => simp [h2] at hq
          | some r2 =>
            simp only [h2] at hq
            cases h3 : qtOK D f s n r2 (x0 + k) (y0 - k) k with
            | none => simp [h3] at hq
            | some r3 =>
              refine ih r2 (x0 + k) (y0 - k) k r3 h3 X Y ?_ ?_
              · rw [abs_le]; push_cast; constructor <;> linarith
              · rw [abs_le]; push_cast; constructor <;> linarith
      · cases h1 : qtOK D f s n r (x0 - k) (y0 - k) k with
        | none => simp [h1] at hq
        | some r1 =>
          simp only [h1] at hq
          cases h2 : qtOK D f s n r1 (x0 - k) (y0 + k) k with
          | none => simp [h2] at hq
          | some r2 =>
            simp only [h2] at hq
            cases h3 : qtOK D f s n r2 (x0 + k) (y0 - k) k with
            | none => simp [h3] at hq
            | some r3 =>
              simp only [h3] at hq
              refine ih r3 (x0 + k) (y0 + k) k rest hq X Y ?_ ?_
              · rw [abs_le]; push_cast; constructor <;> linarith
              · rw [abs_le]; push_cast; constructor <;> linarith

/-! ## The cube -/

/-- The check of one face (sign `σ`: `true` for `e_f = +ρ`). -/
def faceOK (D : Data) (f : Fin 3) (σ : Bool) (depth : ℕ) (bits : List Bool) : Bool :=
  (qtOK D f (if σ then RHO else -RHO) depth bits 0 0 RHO).isSome

theorem faceOK_sound {D : Data} {H C M} (hD : D.Mem H C M) {f : Fin 3} {σ : Bool} {depth : ℕ}
    {bits : List Bool} (hok : faceOK D f σ depth bits = true) :
    ∀ X Y : ℝ, |X| ≤ 1 / 500 → |Y| ≤ 1 / 500 →
      0 ≤ Qf H (faceVecR f (if σ then 1 / 500 else -(1 / 500)) X Y) / 2
        - |Kf C (faceVecR f (if σ then 1 / 500 else -(1 / 500)) X Y)| / 6
        - M * N2 (faceVecR f (if σ then 1 / 500 else -(1 / 500)) X Y) ^ 2 / 24 := by
  have hS : (0 : ℝ) < SCALE := SCALE_pos'
  intro X Y hX hY
  unfold faceOK at hok
  obtain ⟨rest, hq⟩ := Option.isSome_iff_exists.mp hok
  have hs : ((if σ then RHO else -RHO : ℤ) : ℝ) / SCALE = if σ then 1 / 500 else -(1 / 500) := by
    split_ifs <;> simp only [RHO, SCALE] <;> norm_num
  have := qtOK_sound hD depth bits 0 0 RHO rest hq X Y ?_ ?_
  · rwa [hs] at this
  · have : |X * SCALE| ≤ (RHO : ℝ) := by
      rw [abs_mul, abs_of_pos hS]; simp only [RHO, SCALE] at hX ⊢; push_cast; nlinarith
    simpa using this
  · have : |Y * SCALE| ≤ (RHO : ℝ) := by
      rw [abs_mul, abs_of_pos hS]; simp only [RHO, SCALE] at hY ⊢; push_cast; nlinarith
    simpa using this

/-- The second of the two coordinates other than `f`. -/
def snd (f : Fin 3) : Fin 3 := if f = 2 then 1 else 2

theorem faceVecR_eq (f : Fin 3) (e : Fin 3 → ℝ) :
    faceVecR f (e f) (e (fst f)) (e (snd f)) = e := by
  funext a
  fin_cases f <;> fin_cases a <;> simp [faceVecR, fst, snd]

/-- **The bracket is `≥ 0` on the cube**, given `g ≥ 0` on the six faces. -/
theorem bracket_nonneg_of_faces {H : Fin 3 → Fin 3 → ℝ} {C : Fin 3 → Fin 3 → Fin 3 → ℝ} {M : ℝ}
    (hM : 0 ≤ M)
    (hface : ∀ (f : Fin 3) (σ : Bool) (X Y : ℝ), |X| ≤ 1 / 500 → |Y| ≤ 1 / 500 →
      0 ≤ Qf H (faceVecR f (if σ then 1 / 500 else -(1 / 500)) X Y) / 2
        - |Kf C (faceVecR f (if σ then 1 / 500 else -(1 / 500)) X Y)| / 6
        - M * N2 (faceVecR f (if σ then 1 / 500 else -(1 / 500)) X Y) ^ 2 / 24)
    (δ : Fin 3 → ℝ) (hδ : ∀ i, |δ i| ≤ 1 / 500) : 0 ≤ bracket H C M δ := by
  -- a coordinate of maximal size
  obtain ⟨f, -, hf'⟩ := Finset.exists_max_image Finset.univ (fun a => |δ a|) Finset.univ_nonempty
  have hf : ∀ a, |δ a| ≤ |δ f| := fun a => hf' a (Finset.mem_univ a)
  set t := |δ f| with ht
  rcases (abs_nonneg (δ f)).lt_or_eq with htp | ht0
  · -- `δ = s • e`, `s = 500 t ∈ (0, 1]`, `e` on the face `f`
    set s : ℝ := 500 * t with hs
    have hs0 : 0 < s := by positivity
    have hs1 : s ≤ 1 := by have := hδ f; rw [hs]; linarith
    set e : Fin 3 → ℝ := fun a => δ a / s with he
    have hδe : δ = fun a => s * e a := by funext a; simp only [he]; field_simp
    have heb : ∀ a, |e a| ≤ 1 / 500 := fun a => by
      simp only [he, abs_div, abs_of_pos hs0]
      rw [div_le_iff₀ hs0, hs]; have := hf a; linarith
    have hne : δ f ≠ 0 := fun h0 => by simp [h0] at htp
    have hef : e f = if 0 ≤ δ f then 1 / 500 else -(1 / 500) := by
      simp only [he, hs, ht]
      split_ifs with h
      · rw [abs_of_nonneg h]; field_simp
      · rw [abs_of_neg (not_le.mp h)]; field_simp
    have key := hface f (decide (0 ≤ δ f)) (e (fst f)) (e (snd f)) (heb _) (heb _)
    have hσ : (if decide (0 ≤ δ f) = true then (1 / 500 : ℝ) else -(1 / 500))
        = if 0 ≤ δ f then 1 / 500 else -(1 / 500) := by simp
    rw [hσ, ← hef, faceVecR_eq] at key
    rw [hδe]
    exact le_trans (mul_nonneg (sq_nonneg s) key) (bracket_ge H C hM e hs0.le hs1)
  · -- `δ = 0`
    have h0 : ∀ a, δ a = 0 := fun a => by
      have := hf a; rw [ht, ← ht0] at this; exact abs_nonpos_iff.mp this
    have : δ = fun _ => 0 := funext h0
    subst this
    simp [bracket, Qf, Kf, N2]

/-- **Part (2) of Task 5a's numeric side**: a checked covering gives `bracket ≥ 0` on the cube
for every `(H, C, M)` in the data. -/
theorem bracket_nonneg {D : Data} {H C M} (hD : D.Mem H C M) (hM : 0 ≤ D.M.lo)
    (depth : Fin 3 → Bool → ℕ) (bits : Fin 3 → Bool → List Bool)
    (hok : ∀ f σ, faceOK D f σ (depth f σ) (bits f σ) = true) :
    ∀ δ : Fin 3 → ℝ, (∀ i, |δ i| ≤ 1 / 500) → 0 ≤ bracket H C M δ := by
  have hS : (0 : ℝ) < SCALE := SCALE_pos'
  have hM0 : 0 ≤ M := by
    have := hD.hM.1
    have h0 : (0 : ℝ) ≤ D.M.lo := by exact_mod_cast hM
    nlinarith
  exact bracket_nonneg_of_faces hM0 fun f σ X Y hX hY =>
    faceOK_sound hD (hok f σ) X Y hX hY

end Thomson.TriLocalCert
