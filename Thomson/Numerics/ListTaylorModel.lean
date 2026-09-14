import Thomson.Numerics.PolyList

/-! # Task 5b, kernel layer, step 2: the Taylor model of a nested list

`toTML` reads the quadratic Taylor model of a normalised box off the nested list of its
coefficients: the ten coefficients of total degree `≤ 2` (their lower endpoints) and the radius
`rad3` — the widths of those ten and the whole of every other entry.  `toTML_mem` is the same
statement as `Engine.toTM_mem`, proved by three inductions on the nested list instead of a sum
over `Fin 9 × Fin 9 × Fin 9`. -/

namespace Thomson.Tri5b

/-- The radius contribution of an entry of total degree `d`. -/
def radEnt (d : ℕ) (I : Itv) : ℤ := if d ≤ 2 then I.hi - I.lo else maxabs I

def rad1 : ℕ → IL1 → ℤ
  | _, [] => 0
  | d, I :: P => radEnt d I + rad1 (d + 1) P
def rad2 : ℕ → IL2 → ℤ
  | _, [] => 0
  | d, R :: P => rad1 d R + rad2 (d + 1) P
def rad3 : ℕ → IL3 → ℤ
  | _, [] => 0
  | d, R :: P => rad2 d R + rad3 (d + 1) P

/-- The quadratic Taylor model read off a nested list of coefficients on the normalised box. -/
def toTML (U : IL3) : TM where
  c := (getL U 0 0 0).lo
  g1 := (getL U 1 0 0).lo
  g2 := (getL U 0 1 0).lo
  g3 := (getL U 0 0 1).lo
  q11 := (getL U 2 0 0).lo
  q12 := (getL U 1 1 0).lo
  q13 := (getL U 1 0 1).lo
  q22 := (getL U 0 2 0).lo
  q23 := (getL U 0 1 1).lo
  q33 := (getL U 0 0 2).lo
  r := rad3 0 U

/-! ### The low-degree part, as a real number -/

/-- The lower endpoint of an entry of total degree `≤ 2`, `0` otherwise. -/
def lowEnt (d : ℕ) (I : Itv) : ℝ := if d ≤ 2 then (I.lo : ℝ) else 0

def low1 : ℕ → IL1 → ℝ → ℝ
  | _, [], _ => 0
  | d, I :: P, e => lowEnt d I + e * low1 (d + 1) P e
def low2 : ℕ → IL2 → ℝ → ℝ → ℝ
  | _, [], _, _ => 0
  | d, R :: P, e2, e3 => low1 d R e3 + e2 * low2 (d + 1) P e2 e3
def low3 : ℕ → IL3 → ℝ → ℝ → ℝ → ℝ
  | _, [], _, _, _ => 0
  | d, R :: P, e1, e2, e3 => low2 d R e2 e3 + e1 * low3 (d + 1) P e1 e2 e3

theorem abs_ent {I : Itv} {x : ℝ} (hI : I.Mem x) (d : ℕ) :
    |x * SCALE - lowEnt d I| ≤ (radEnt d I : ℝ) := by
  unfold lowEnt radEnt
  obtain ⟨a1, a2⟩ := hI
  split_ifs
  · push_cast; rw [abs_le]; constructor <;> linarith
  · simpa using abs_le_maxabs ⟨a1, a2⟩

theorem abs_ev1_sub_low1 {P : IL1} {p : RL1} (h : Mem1 P p) (d : ℕ) {e : ℝ} (he : |e| ≤ 1) :
    |ev1 p e * SCALE - low1 d P e| ≤ (rad1 d P : ℝ) := by
  unfold Mem1 at h
  induction h generalizing d with
  | nil => simp [low1, rad1]
  | @cons I x P p hI hP ih =>
      simp only [ev1_cons, low1, rad1]
      push_cast
      have h1 := abs_ent hI d
      have h2 := ih (d + 1)
      have h3 : |e * (ev1 p e * SCALE - low1 (d + 1) P e)| ≤ (rad1 (d + 1) P : ℝ) := by
        rw [abs_mul]
        calc |e| * |ev1 p e * SCALE - low1 (d + 1) P e| ≤ 1 * (rad1 (d + 1) P : ℝ) :=
              mul_le_mul he h2 (abs_nonneg _) zero_le_one
          _ = _ := one_mul _
      calc |(x + e * ev1 p e) * SCALE - (lowEnt d I + e * low1 (d + 1) P e)|
          = |(x * SCALE - lowEnt d I) + e * (ev1 p e * SCALE - low1 (d + 1) P e)| := by ring_nf
        _ ≤ |x * SCALE - lowEnt d I| + |e * (ev1 p e * SCALE - low1 (d + 1) P e)| := abs_add_le _ _
        _ ≤ (radEnt d I : ℝ) + (rad1 (d + 1) P : ℝ) := add_le_add h1 h3

theorem abs_ev2_sub_low2 {P : IL2} {p : RL2} (h : Mem2 P p) (d : ℕ) {e2 e3 : ℝ}
    (he2 : |e2| ≤ 1) (he3 : |e3| ≤ 1) :
    |ev2 p e2 e3 * SCALE - low2 d P e2 e3| ≤ (rad2 d P : ℝ) := by
  unfold Mem2 at h
  induction h generalizing d with
  | nil => simp [low2, rad2]
  | @cons R r P p hR hP ih =>
      simp only [ev2_cons, low2, rad2]
      push_cast
      have h1 := abs_ev1_sub_low1 hR d he3
      have h2 := ih (d + 1)
      have h3 : |e2 * (ev2 p e2 e3 * SCALE - low2 (d + 1) P e2 e3)| ≤ (rad2 (d + 1) P : ℝ) := by
        rw [abs_mul]
        calc |e2| * |ev2 p e2 e3 * SCALE - low2 (d + 1) P e2 e3| ≤ 1 * (rad2 (d + 1) P : ℝ) :=
              mul_le_mul he2 h2 (abs_nonneg _) zero_le_one
          _ = _ := one_mul _
      calc |(ev1 r e3 + e2 * ev2 p e2 e3) * SCALE - (low1 d R e3 + e2 * low2 (d + 1) P e2 e3)|
          = |(ev1 r e3 * SCALE - low1 d R e3)
              + e2 * (ev2 p e2 e3 * SCALE - low2 (d + 1) P e2 e3)| := by ring_nf
        _ ≤ |ev1 r e3 * SCALE - low1 d R e3|
              + |e2 * (ev2 p e2 e3 * SCALE - low2 (d + 1) P e2 e3)| := abs_add_le _ _
        _ ≤ (rad1 d R : ℝ) + (rad2 (d + 1) P : ℝ) := add_le_add h1 h3

theorem abs_ev3_sub_low3 {P : IL3} {p : RL3} (h : Mem3 P p) (d : ℕ) {e1 e2 e3 : ℝ}
    (he1 : |e1| ≤ 1) (he2 : |e2| ≤ 1) (he3 : |e3| ≤ 1) :
    |ev3 p e1 e2 e3 * SCALE - low3 d P e1 e2 e3| ≤ (rad3 d P : ℝ) := by
  unfold Mem3 at h
  induction h generalizing d with
  | nil => simp [low3, rad3]
  | @cons R r P p hR hP ih =>
      simp only [ev3_cons, low3, rad3]
      push_cast
      have h1 := abs_ev2_sub_low2 hR d he2 he3
      have h2 := ih (d + 1)
      have h3 : |e1 * (ev3 p e1 e2 e3 * SCALE - low3 (d + 1) P e1 e2 e3)|
          ≤ (rad3 (d + 1) P : ℝ) := by
        rw [abs_mul]
        calc |e1| * |ev3 p e1 e2 e3 * SCALE - low3 (d + 1) P e1 e2 e3|
              ≤ 1 * (rad3 (d + 1) P : ℝ) := mul_le_mul he1 h2 (abs_nonneg _) zero_le_one
          _ = _ := one_mul _
      calc |(ev2 r e2 e3 + e1 * ev3 p e1 e2 e3) * SCALE
              - (low2 d R e2 e3 + e1 * low3 (d + 1) P e1 e2 e3)|
          = |(ev2 r e2 e3 * SCALE - low2 d R e2 e3)
              + e1 * (ev3 p e1 e2 e3 * SCALE - low3 (d + 1) P e1 e2 e3)| := by ring_nf
        _ ≤ |ev2 r e2 e3 * SCALE - low2 d R e2 e3|
              + |e1 * (ev3 p e1 e2 e3 * SCALE - low3 (d + 1) P e1 e2 e3)| := abs_add_le _ _
        _ ≤ (rad2 d R : ℝ) + (rad3 (d + 1) P : ℝ) := add_le_add h1 h3

/-! ### The low part is the polynomial of the Taylor model -/

theorem low1_of_ge {d : ℕ} (hd : 3 ≤ d) (P : IL1) (e : ℝ) : low1 d P e = 0 := by
  induction P generalizing d with
  | nil => rfl
  | cons I P ih =>
      simp only [low1, lowEnt]
      rw [if_neg (by omega), ih (by omega)]
      ring

theorem low2_of_ge {d : ℕ} (hd : 3 ≤ d) (P : IL2) (e2 e3 : ℝ) : low2 d P e2 e3 = 0 := by
  induction P generalizing d with
  | nil => rfl
  | cons R P ih =>
      simp only [low2]
      rw [low1_of_ge hd, ih (by omega)]
      ring

theorem low3_of_ge {d : ℕ} (hd : 3 ≤ d) (P : IL3) (e1 e2 e3 : ℝ) : low3 d P e1 e2 e3 = 0 := by
  induction P generalizing d with
  | nil => rfl
  | cons R P ih =>
      simp only [low3]
      rw [low2_of_ge hd, ih (by omega)]
      ring

@[simp] theorem lowEnt_zero (d : ℕ) : lowEnt d Itv.zero = 0 := by
  simp [lowEnt, Itv.zero, Itv.cst]

theorem low1_three (d : ℕ) (P : IL1) (e : ℝ) :
    low1 d P e = lowEnt d (P.getD 0 Itv.zero)
      + e * (lowEnt (d + 1) (P.getD 1 Itv.zero)
      + e * (lowEnt (d + 2) (P.getD 2 Itv.zero) + e * low1 (d + 3) (P.drop 3) e)) := by
  match P with
  | [] => simp [low1]
  | [a] => simp [low1]
  | [a, b] => simp [low1]
  | a :: b :: c :: rest => simp [low1]

theorem low2_three (d : ℕ) (P : IL2) (e2 e3 : ℝ) :
    low2 d P e2 e3 = low1 d (P.getD 0 []) e3
      + e2 * (low1 (d + 1) (P.getD 1 []) e3
      + e2 * (low1 (d + 2) (P.getD 2 []) e3 + e2 * low2 (d + 3) (P.drop 3) e2 e3)) := by
  match P with
  | [] => simp [low2, low1]
  | [a] => simp [low2, low1]
  | [a, b] => simp [low2, low1]
  | a :: b :: c :: rest => simp [low2]

theorem low3_three (d : ℕ) (P : IL3) (e1 e2 e3 : ℝ) :
    low3 d P e1 e2 e3 = low2 d (P.getD 0 []) e2 e3
      + e1 * (low2 (d + 1) (P.getD 1 []) e2 e3
      + e1 * (low2 (d + 2) (P.getD 2 []) e2 e3 + e1 * low3 (d + 3) (P.drop 3) e1 e2 e3)) := by
  match P with
  | [] => simp [low3, low2]
  | [a] => simp [low3, low2]
  | [a, b] => simp [low3, low2]
  | a :: b :: c :: rest => simp [low3]

theorem low3_val (U : IL3) (e1 e2 e3 : ℝ) : low3 0 U e1 e2 e3 = (toTML U).val e1 e2 e3 := by
  rw [low3_three, low3_of_ge (by norm_num)]
  rw [low2_three 0, low2_three 1, low2_three 2,
    low2_of_ge (by norm_num), low2_of_ge (by norm_num), low2_of_ge (by norm_num)]
  rw [low1_three 0, low1_three 1, low1_three 2, low1_three 1, low1_three 2, low1_three 3,
    low1_three 2, low1_three 3, low1_three 4]
  simp only [low1_of_ge (by norm_num : 3 ≤ 0 + 3), low1_of_ge (by norm_num : 3 ≤ 1 + 3),
    low1_of_ge (by norm_num : 3 ≤ 2 + 3), low1_of_ge (by norm_num : 3 ≤ 3 + 3),
    low1_of_ge (by norm_num : 3 ≤ 4 + 3)]
  simp only [lowEnt, TM.val, toTML, getL]
  norm_num
  ring

/-- **The Taylor model of a nested list.** -/
theorem toTML_mem {U : IL3} {u : RL3} (h : Mem3 U u) {e1 e2 e3 : ℝ} (he : TM.Box e1 e2 e3) :
    (toTML U).Mem (ev3 u e1 e2 e3) e1 e2 e3 := by
  obtain ⟨h1, h2, h3⟩ := he
  show |ev3 u e1 e2 e3 * SCALE - (toTML U).val e1 e2 e3| ≤ ((toTML U).r : ℝ)
  rw [← low3_val]
  exact abs_ev3_sub_low3 h 0 h1 h2 h3

/-- **One box, from a nested list.**  The list version of `Engine.box_sound`. -/
theorem kbox_sound {T : IL3} {t : RL3} (hT : Mem3 T t) (mg : ℤ) (a b d h1 h2 h3 : ℤ)
    (hh1 : 0 < h1) (hh2 : 0 < h2) (hh3 : 0 < h3)
    (hpos : TM.geBound mg (toTML (shsc a b d h1 h2 h3 T)) = true)
    {u v w : ℝ}
    (hu : |u - (a : ℝ) / SCALE| ≤ (h1 : ℝ) / SCALE)
    (hv : |v - (b : ℝ) / SCALE| ≤ (h2 : ℝ) / SCALE)
    (hw : |w - (d : ℝ) / SCALE| ≤ (h3 : ℝ) / SCALE) :
    (mg : ℝ) / SCALE ≤ ev3 t u v w := by
  have hS := SCALE_pos'
  have p1 : (0:ℝ) < (h1 : ℝ) / SCALE := by
    apply div_pos _ hS; exact_mod_cast hh1
  have p2 : (0:ℝ) < (h2 : ℝ) / SCALE := by
    apply div_pos _ hS; exact_mod_cast hh2
  have p3 : (0:ℝ) < (h3 : ℝ) / SCALE := by
    apply div_pos _ hS; exact_mod_cast hh3
  set e1 := (u - (a : ℝ) / SCALE) / ((h1 : ℝ) / SCALE) with he1
  set e2 := (v - (b : ℝ) / SCALE) / ((h2 : ℝ) / SCALE) with he2
  set e3 := (w - (d : ℝ) / SCALE) / ((h3 : ℝ) / SCALE) with he3
  have b1 : |e1| ≤ 1 := by
    rw [he1, abs_div, abs_of_pos p1, div_le_one p1]; exact hu
  have b2 : |e2| ≤ 1 := by
    rw [he2, abs_div, abs_of_pos p2, div_le_one p2]; exact hv
  have b3 : |e3| ≤ 1 := by
    rw [he3, abs_div, abs_of_pos p3, div_le_one p3]; exact hw
  have hbox : TM.Box e1 e2 e3 := ⟨b1, b2, b3⟩
  have hu' : (a : ℝ) / SCALE + (h1 : ℝ) / SCALE * e1 = u := by
    have : (h1 : ℝ) / SCALE * e1 = u - (a : ℝ) / SCALE := by
      rw [he1, mul_div_cancel₀ _ (ne_of_gt p1)]
    linarith
  have hv' : (b : ℝ) / SCALE + (h2 : ℝ) / SCALE * e2 = v := by
    have : (h2 : ℝ) / SCALE * e2 = v - (b : ℝ) / SCALE := by
      rw [he2, mul_div_cancel₀ _ (ne_of_gt p2)]
    linarith
  have hw' : (d : ℝ) / SCALE + (h3 : ℝ) / SCALE * e3 = w := by
    have : (h3 : ℝ) / SCALE * e3 = w - (d : ℝ) / SCALE := by
      rw [he3, mul_div_cancel₀ _ (ne_of_gt p3)]
    linarith
  have hmem := toTML_mem (Mem3_shsc hT a b d hh1.le hh2.le hh3.le) hbox
  rw [ev3_shscR, hu', hv', hw'] at hmem
  exact TM.geBound_sound hbox hmem hpos

end Thomson.Tri5b
