import Thomson.Tri5b.Tensor

/-! # Task 5b, step 8: the box engine

Interval coefficient tensors, their Taylor shift, and the extraction of a quadratic Taylor model
on a box.  Together with `TM.nonneg_sound` this is everything a single box needs. -/

namespace Thomson.Tri5b

open Finset

/-- An interval coefficient tensor. -/
abbrev IT := Fin 9 → Fin 9 → Fin 9 → Itv

/-- `C` encloses the real tensor `c` entrywise. -/
def ITMem (C : IT) (c : RT) : Prop := ∀ i j k, (C i j k).Mem (c i j k)

/-! ### Memoisation

Lean is pure and has no memoisation, so `Ish3 (Ish2 (Ish1 C a) b) d` — a *function* — recomputes
the inner shifts at every one of the `9³` reads: `9³` base reads per entry, `≈5·10⁵` interval
products per box instead of `≈2·10⁴`.  Nor can a memo be hidden behind a function type: the
compiler eta-expands `fun C => let tbl := …; fun i j k => tbl …` back to arity `4`, rebuilding the
table on each read.  The table must therefore be a *value*: `ITA` is a tensor tabulated into an
`Array`, and `ITA.get A`, a partial application, evaluates `A` once and reads it thereafter. -/

/-- A tensor tabulated into `729` entries, indexed by `81i + 9j + k`. -/
structure ITA where
  arr : Array Itv

/-- Read a tabulated tensor. -/
def ITA.get (A : ITA) (i j k : Fin 9) : Itv :=
  A.arr.getD ((i : ℕ) * 81 + (j : ℕ) * 9 + (k : ℕ)) Itv.zero

/-- Tabulate a tensor.  All `729` entries are computed here, once. -/
def toITA (C : IT) : ITA :=
  ⟨Array.ofFn (n := 729) fun n : Fin 729 =>
    C ⟨(n : ℕ) / 81, by have := n.isLt; omega⟩ ⟨(n : ℕ) / 9 % 9, by omega⟩
      ⟨(n : ℕ) % 9, by omega⟩⟩

set_option maxRecDepth 4000 in
@[simp] theorem toITA_get (C : IT) (i j k : Fin 9) : (toITA C).get i j k = C i j k := by
  have hi := i.isLt; have hj := j.isLt; have hk := k.isLt
  have hn : (i : ℕ) * 81 + (j : ℕ) * 9 + (k : ℕ) < 729 := by omega
  simp only [ITA.get, toITA, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hn, dif_pos,
    Option.getD_some]
  congr 1
  · exact Fin.ext (by simp; omega)
  · exact Fin.ext (by simp; omega)
  · exact Fin.ext (by simp; omega)

theorem ITMem_toITA {C : IT} {c : RT} (h : ITMem C c) : ITMem (toITA C).get c := by
  intro i j k; rw [toITA_get]; exact h i j k

/-! ### The interval shift -/

/-- Shift the first variable by `a/SCALE`. -/
def Ish1 (C : IT) (a : ℤ) : IT := fun j y z =>
  Itv.sumL ((List.finRange 9).map (fun i : Fin 9 =>
    if (j : ℕ) ≤ (i : ℕ) then
      Itv.mul (Itv.mul (C i y z) (Itv.cst (((i : ℕ).choose (j : ℕ) : ℤ) * SCALE)))
        (Itv.npow (Itv.cst a) ((i : ℕ) - (j : ℕ)))
    else Itv.zero))

theorem ITMem_Ish1 {C : IT} {c : RT} (h : ITMem C c) (a : ℤ) :
    ITMem (Ish1 C a) (sh1 c ((a : ℝ) / SCALE)) := by
  intro j y z
  unfold Ish1 sh1
  refine Itv.mem_sum_fin _ _ ?_
  intro i
  by_cases hij : (j : ℕ) ≤ (i : ℕ)
  · rw [if_pos hij, if_pos hij]
    have h1 : (Itv.cst (((i : ℕ).choose (j : ℕ) : ℤ) * SCALE)).Mem ((i : ℕ).choose (j : ℕ) : ℝ) := by
      have := Itv.mem_cst (((i : ℕ).choose (j : ℕ) : ℤ) * SCALE)
      rw [Int.cast_mul, mul_div_assoc, div_self (ne_of_gt SCALE_pos'), mul_one] at this
      exact this
    exact Itv.mem_mul (Itv.mem_mul (h i y z) h1) (Itv.mem_npow (Itv.mem_cst a) _)
  · rw [if_neg hij, if_neg hij]; exact Itv.mem_zero


/-! ### The other axes and the full shift -/

def Iperm12 (C : IT) : IT := fun i j k => C j i k
def Iperm13 (C : IT) : IT := fun i j k => C k j i

theorem ITMem_perm12 {C : IT} {c : RT} (h : ITMem C c) : ITMem (Iperm12 C) (perm12 c) :=
  fun i j k => h j i k
theorem ITMem_perm13 {C : IT} {c : RT} (h : ITMem C c) : ITMem (Iperm13 C) (perm13 c) :=
  fun i j k => h k j i

def Ish2 (C : IT) (a : ℤ) : IT := Iperm12 (Ish1 (Iperm12 C) a)
def Ish3 (C : IT) (a : ℤ) : IT := Iperm13 (Ish1 (Iperm13 C) a)

theorem ITMem_Ish2 {C : IT} {c : RT} (h : ITMem C c) (a : ℤ) :
    ITMem (Ish2 C a) (sh2 c ((a : ℝ) / SCALE)) :=
  ITMem_perm12 (ITMem_Ish1 (ITMem_perm12 h) a)
theorem ITMem_Ish3 {C : IT} {c : RT} (h : ITMem C c) (a : ℤ) :
    ITMem (Ish3 C a) (sh3 c ((a : ℝ) / SCALE)) :=
  ITMem_perm13 (ITMem_Ish1 (ITMem_perm13 h) a)

/-- The full Taylor shift, at fixed-point centres. -/
def Ishift (C : IT) (a b d : ℤ) : IT := Ish3 (Ish2 (Ish1 C a) b) d

theorem ITMem_Ishift {C : IT} {c : RT} (h : ITMem C c) (a b d : ℤ) :
    ITMem (Ishift C a b d) (shift c ((a : ℝ) / SCALE) ((b : ℝ) / SCALE) ((d : ℝ) / SCALE)) :=
  ITMem_Ish3 (ITMem_Ish2 (ITMem_Ish1 h a) b) d

/-- The powers `(a/SCALE)ᵈ`, `d < 9`.  `Ish1` needs them at all `9³` entries; computing them
there costs more than the products they multiply. -/
def powA (a : ℤ) : Array Itv := Array.ofFn (n := 9) (fun d : Fin 9 => Itv.npow (Itv.cst a) (d : ℕ))

theorem powA_get (a : ℤ) {d : ℕ} (h : d < 9) :
    (powA a).getD d Itv.zero = Itv.npow (Itv.cst a) d := by
  simp only [powA, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, h, dif_pos,
    Option.getD_some]

/-- `Ish1`, tabulated, with the powers of the shift hoisted out. -/
def Ish1A (C : IT) (a : ℤ) : ITA :=
  let pw : Array Itv := powA a
  toITA (fun j y z =>
    Itv.sumL ((List.finRange 9).map (fun i : Fin 9 =>
      if (j : ℕ) ≤ (i : ℕ) ∧ ¬ ((C i y z).lo = 0 ∧ (C i y z).hi = 0) then
        Itv.mul (Itv.mul (C i y z) (Itv.cst (((i : ℕ).choose (j : ℕ) : ℤ) * SCALE)))
          (pw.getD ((i : ℕ) - (j : ℕ)) Itv.zero)
      else Itv.zero)))

theorem Ish1A_get (C : IT) (a : ℤ) (j y z : Fin 9) : (Ish1A C a).get j y z = Ish1 C a j y z := by
  simp only [Ish1A, toITA_get, Ish1]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hij : (j : ℕ) ≤ (i : ℕ)
  · by_cases hz : (C i y z).lo = 0 ∧ (C i y z).hi = 0
    · have hm : Itv.mul (C i y z) (Itv.cst (((i : ℕ).choose (j : ℕ) : ℤ) * SCALE)) = Itv.zero :=
        Itv.mul_zero_left hz.1 hz.2
      rw [if_neg (by tauto), if_pos hij, hm, Itv.mul_zero_left rfl rfl]
    · rw [if_pos ⟨hij, hz⟩, if_pos hij, powA_get a (by have := i.isLt; omega)]
  · rw [if_neg (by tauto), if_neg hij]

theorem ITMem_Ish1A {C : IT} {c : RT} (h : ITMem C c) (a : ℤ) :
    ITMem (Ish1A C a).get (sh1 c ((a : ℝ) / SCALE)) := by
  intro j y z; rw [Ish1A_get]; exact ITMem_Ish1 h a j y z

/-- The full Taylor shift, tabulated after each axis: this is the executable version. -/
def IshiftA (C : IT) (a b d : ℤ) : ITA :=
  toITA (Iperm13 (Ish1A (Iperm13 (Iperm12 (Ish1A (Iperm12 (Ish1A C a).get) b).get)) d).get)

theorem ITMem_IshiftA {C : IT} {c : RT} (h : ITMem C c) (a b d : ℤ) :
    ITMem (IshiftA C a b d).get
      (shift c ((a : ℝ) / SCALE) ((b : ℝ) / SCALE) ((d : ℝ) / SCALE)) :=
  ITMem_toITA (ITMem_perm13 (ITMem_Ish1A (ITMem_perm13 (ITMem_perm12
    (ITMem_Ish1A (ITMem_perm12 (ITMem_Ish1A h a)) b))) d))

/-! ### Extraction of a Taylor model on a box -/

/-- The largest absolute value in an interval. -/
def maxabs (I : Itv) : ℤ := max |I.lo| |I.hi|

theorem abs_le_maxabs {I : Itv} {x : ℝ} (h : I.Mem x) : |x * SCALE| ≤ (maxabs I : ℝ) := by
  obtain ⟨h1, h2⟩ := h
  have e1 : (I.lo : ℝ) ≤ |(I.lo : ℤ)| := by exact_mod_cast le_abs_self I.lo
  have e2 : (I.hi : ℝ) ≤ |(I.hi : ℤ)| := by exact_mod_cast le_abs_self I.hi
  have e3 : -((|I.lo| : ℤ) : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast neg_abs_le I.lo
  have e4 : -((|I.hi| : ℤ) : ℝ) ≤ (I.hi : ℝ) := by exact_mod_cast neg_abs_le I.hi
  have m1 : ((|I.lo| : ℤ) : ℝ) ≤ (maxabs I : ℝ) := by
    have : (|I.lo| : ℤ) ≤ maxabs I := le_max_left _ _
    exact_mod_cast this
  have m2 : ((|I.hi| : ℤ) : ℝ) ≤ (maxabs I : ℝ) := by
    have : (|I.hi| : ℤ) ≤ maxabs I := le_max_right _ _
    exact_mod_cast this
  rw [abs_le]
  constructor <;> linarith

/-- The coefficient of `e₁ⁱ e₂ʲ e₃ᵏ` for a box with half-widths `hₙ/SCALE`. -/
def coefIT (C : IT) (h1 h2 h3 : ℤ) (i j k : Fin 9) : Itv :=
  Itv.mul (Itv.mul (Itv.mul (C i j k) (Itv.npow (Itv.cst h1) (i : ℕ)))
    (Itv.npow (Itv.cst h2) (j : ℕ))) (Itv.npow (Itv.cst h3) (k : ℕ))

theorem coefIT_mem {C : IT} {c : RT} (hC : ITMem C c) (h1 h2 h3 : ℤ) (i j k : Fin 9) :
    (coefIT C h1 h2 h3 i j k).Mem
      (c i j k * (((h1 : ℝ) / SCALE) ^ (i : ℕ) * ((h2 : ℝ) / SCALE) ^ (j : ℕ)
        * ((h3 : ℝ) / SCALE) ^ (k : ℕ))) := by
  have m1 := Itv.mem_npow (Itv.mem_cst h1) (i : ℕ)
  have m2 := Itv.mem_npow (Itv.mem_cst h2) (j : ℕ)
  have m3 := Itv.mem_npow (Itv.mem_cst h3) (k : ℕ)
  have := Itv.mem_mul (Itv.mem_mul (Itv.mem_mul (hC i j k) m1) m2) m3
  unfold coefIT
  have e : c i j k * (((h1 : ℝ) / SCALE) ^ (i : ℕ) * ((h2 : ℝ) / SCALE) ^ (j : ℕ)
      * ((h3 : ℝ) / SCALE) ^ (k : ℕ))
      = c i j k * ((h1 : ℝ) / SCALE) ^ (i : ℕ) * ((h2 : ℝ) / SCALE) ^ (j : ℕ)
        * ((h3 : ℝ) / SCALE) ^ (k : ℕ) := by ring
  rw [e]; exact this

/-- The radius: the widths of the ten kept coefficients plus the whole of the rest. -/
def radius (C : IT) (h1 h2 h3 : ℤ) : ℤ :=
  ∑ i : Fin 9, ∑ j : Fin 9, ∑ k : Fin 9,
    (if (i : ℕ) + (j : ℕ) + (k : ℕ) ≤ 2
      then (coefIT C h1 h2 h3 i j k).hi - (coefIT C h1 h2 h3 i j k).lo
      else maxabs (coefIT C h1 h2 h3 i j k))

/-- The quadratic Taylor model of `ev c` on the box. -/
def toTM (C : IT) (h1 h2 h3 : ℤ) : TM where
  c := (coefIT C h1 h2 h3 0 0 0).lo
  g1 := (coefIT C h1 h2 h3 1 0 0).lo
  g2 := (coefIT C h1 h2 h3 0 1 0).lo
  g3 := (coefIT C h1 h2 h3 0 0 1).lo
  q11 := (coefIT C h1 h2 h3 2 0 0).lo
  q12 := (coefIT C h1 h2 h3 1 1 0).lo
  q13 := (coefIT C h1 h2 h3 1 0 1).lo
  q22 := (coefIT C h1 h2 h3 0 2 0).lo
  q23 := (coefIT C h1 h2 h3 0 1 1).lo
  q33 := (coefIT C h1 h2 h3 0 0 2).lo
  r := radius C h1 h2 h3

set_option maxHeartbeats 1000000 in
/-- Expansion of the degree `≤ 2` part of a `9×9×9` sum. -/
theorem low_expand (f : Fin 9 → Fin 9 → Fin 9 → ℝ) :
    ∑ i : Fin 9, ∑ j : Fin 9, ∑ k : Fin 9,
      (if (i : ℕ) + (j : ℕ) + (k : ℕ) ≤ 2 then f i j k else 0)
      = f 0 0 0 + f 1 0 0 + f 0 1 0 + f 0 0 1 + f 2 0 0 + f 1 1 0 + f 1 0 1 + f 0 2 0
        + f 0 1 1 + f 0 0 2 := by
  simp [Fin.sum_univ_succ]
  ring


theorem abs_mono_le_one {e1 e2 e3 : ℝ} (he : TM.Box e1 e2 e3) (i j k : Fin 9) :
    |e1 ^ (i : ℕ) * e2 ^ (j : ℕ) * e3 ^ (k : ℕ)| ≤ 1 := by
  obtain ⟨h1, h2, h3⟩ := he
  have p1 : |e1 ^ (i : ℕ)| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) h1
  have p2 : |e2 ^ (j : ℕ)| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) h2
  have p3 : |e3 ^ (k : ℕ)| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) h3
  rw [abs_mul, abs_mul]
  calc |e1 ^ (i : ℕ)| * |e2 ^ (j : ℕ)| * |e3 ^ (k : ℕ)| ≤ 1 * 1 * 1 := by
        apply mul_le_mul (mul_le_mul p1 p2 (abs_nonneg _) zero_le_one) p3 (abs_nonneg _)
        norm_num
    _ = 1 := by norm_num

/-- **The box engine.**  The Taylor model extracted from the shifted tensor models the polynomial
on the whole normalised box. -/
theorem toTM_mem {C : IT} {c : RT} (hC : ITMem C c) (h1 h2 h3 : ℤ) {e1 e2 e3 : ℝ}
    (he : TM.Box e1 e2 e3) :
    (toTM C h1 h2 h3).Mem
      (ev c ((h1 : ℝ) / SCALE * e1) ((h2 : ℝ) / SCALE * e2) ((h3 : ℝ) / SCALE * e3)) e1 e2 e3 := by
  set K : Fin 9 → Fin 9 → Fin 9 → ℝ := fun i j k =>
    c i j k * (((h1 : ℝ) / SCALE) ^ (i : ℕ) * ((h2 : ℝ) / SCALE) ^ (j : ℕ)
      * ((h3 : ℝ) / SCALE) ^ (k : ℕ)) with hK
  set M : Fin 9 → Fin 9 → Fin 9 → ℝ := fun i j k =>
    e1 ^ (i : ℕ) * e2 ^ (j : ℕ) * e3 ^ (k : ℕ) with hM
  have hmem : ∀ i j k, (coefIT C h1 h2 h3 i j k).Mem (K i j k) := coefIT_mem hC h1 h2 h3
  have hev : ev c ((h1 : ℝ) / SCALE * e1) ((h2 : ℝ) / SCALE * e2) ((h3 : ℝ) / SCALE * e3)
      = ∑ i, ∑ j, ∑ k, K i j k * M i j k := by
    unfold ev
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    simp only [hK, hM, mul_pow]
    ring
  have hval : (toTM C h1 h2 h3).val e1 e2 e3
      = ∑ i : Fin 9, ∑ j : Fin 9, ∑ k : Fin 9, (if (i : ℕ) + (j : ℕ) + (k : ℕ) ≤ 2
          then ((coefIT C h1 h2 h3 i j k).lo : ℝ) * M i j k else 0) := by
    rw [low_expand (fun i j k => ((coefIT C h1 h2 h3 i j k).lo : ℝ) * M i j k)]
    simp only [TM.val, toTM, hM]
    norm_num
    ring
  have expand : (∑ i : Fin 9, ∑ j : Fin 9, ∑ k : Fin 9, K i j k * M i j k) * SCALE
      - (∑ i : Fin 9, ∑ j : Fin 9, ∑ k : Fin 9, (if (i : ℕ) + (j : ℕ) + (k : ℕ) ≤ 2
          then ((coefIT C h1 h2 h3 i j k).lo : ℝ) * M i j k else 0))
      = ∑ i : Fin 9, ∑ j : Fin 9, ∑ k : Fin 9, (if (i : ℕ) + (j : ℕ) + (k : ℕ) ≤ 2
          then (K i j k * SCALE - ((coefIT C h1 h2 h3 i j k).lo : ℝ)) * M i j k
          else K i j k * SCALE * M i j k) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with h <;> ring
  have hterm : ∀ i j k : Fin 9,
      |(if (i : ℕ) + (j : ℕ) + (k : ℕ) ≤ 2
          then (K i j k * SCALE - ((coefIT C h1 h2 h3 i j k).lo : ℝ)) * M i j k
          else K i j k * SCALE * M i j k)|
        ≤ ((if (i : ℕ) + (j : ℕ) + (k : ℕ) ≤ 2
            then (coefIT C h1 h2 h3 i j k).hi - (coefIT C h1 h2 h3 i j k).lo
            else maxabs (coefIT C h1 h2 h3 i j k) : ℤ) : ℝ) := by
    intro i j k
    have hm := abs_mono_le_one he i j k
    have hm' : |M i j k| ≤ 1 := hm
    obtain ⟨hlo, hhi⟩ := hmem i j k
    split_ifs with h
    · rw [abs_mul]
      have hb1 : |K i j k * SCALE - ((coefIT C h1 h2 h3 i j k).lo : ℝ)|
          ≤ ((coefIT C h1 h2 h3 i j k).hi : ℝ) - ((coefIT C h1 h2 h3 i j k).lo : ℝ) := by
        rw [abs_le]; constructor <;> linarith
      have hb0 : (0:ℝ) ≤ ((coefIT C h1 h2 h3 i j k).hi : ℝ)
          - ((coefIT C h1 h2 h3 i j k).lo : ℝ) := by linarith
      push_cast
      calc |K i j k * SCALE - ((coefIT C h1 h2 h3 i j k).lo : ℝ)| * |M i j k|
          ≤ (((coefIT C h1 h2 h3 i j k).hi : ℝ) - ((coefIT C h1 h2 h3 i j k).lo : ℝ)) * 1 :=
            mul_le_mul hb1 hm' (abs_nonneg _) hb0
        _ = _ := by ring
    · rw [abs_mul]
      have hb1 := abs_le_maxabs (hmem i j k)
      have hb0 : (0:ℝ) ≤ (maxabs (coefIT C h1 h2 h3 i j k) : ℝ) := le_trans (abs_nonneg _) hb1
      calc |K i j k * SCALE| * |M i j k|
          ≤ (maxabs (coefIT C h1 h2 h3 i j k) : ℝ) * 1 := mul_le_mul hb1 hm' (abs_nonneg _) hb0
        _ = _ := by ring
  show |_ * (SCALE : ℝ) - _| ≤ _
  rw [hev, hval, expand]
  have hr : ((toTM C h1 h2 h3).r : ℝ)
      = ∑ i : Fin 9, ∑ j : Fin 9, ∑ k : Fin 9, ((if (i : ℕ) + (j : ℕ) + (k : ℕ) ≤ 2
          then (coefIT C h1 h2 h3 i j k).hi - (coefIT C h1 h2 h3 i j k).lo
          else maxabs (coefIT C h1 h2 h3 i j k) : ℤ) : ℝ) := by
    simp only [toTM, radius]
    push_cast
    rfl
  rw [hr]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ => ?_)
  exact hterm i j k


/-- **One box, complete.**  If the Taylor model extracted from the tensor shifted to the centre
`(a,b,d)/SCALE` certifies the margin `mg/SCALE` on the normalised box, then the polynomial is at
least that on the box `centre ± (h₁,h₂,h₃)/SCALE`. -/
theorem box_sound {C : IT} {c : RT} (hC : ITMem C c) (mg : ℤ) (a b d h1 h2 h3 : ℤ)
    (hh1 : 0 < h1) (hh2 : 0 < h2) (hh3 : 0 < h3)
    (hpos : TM.geBound mg (toTM (IshiftA C a b d).get h1 h2 h3) = true)
    {u v t : ℝ}
    (hu : |u - (a : ℝ) / SCALE| ≤ (h1 : ℝ) / SCALE)
    (hv : |v - (b : ℝ) / SCALE| ≤ (h2 : ℝ) / SCALE)
    (ht : |t - (d : ℝ) / SCALE| ≤ (h3 : ℝ) / SCALE) :
    (mg : ℝ) / SCALE ≤ ev c u v t := by
  have hS := SCALE_pos'
  have p1 : (0:ℝ) < (h1 : ℝ) / SCALE := by
    apply div_pos _ hS; exact_mod_cast hh1
  have p2 : (0:ℝ) < (h2 : ℝ) / SCALE := by
    apply div_pos _ hS; exact_mod_cast hh2
  have p3 : (0:ℝ) < (h3 : ℝ) / SCALE := by
    apply div_pos _ hS; exact_mod_cast hh3
  set e1 := (u - (a : ℝ) / SCALE) / ((h1 : ℝ) / SCALE) with he1
  set e2 := (v - (b : ℝ) / SCALE) / ((h2 : ℝ) / SCALE) with he2
  set e3 := (t - (d : ℝ) / SCALE) / ((h3 : ℝ) / SCALE) with he3
  have b1 : |e1| ≤ 1 := by
    rw [he1, abs_div, abs_of_pos p1, div_le_one p1]; exact hu
  have b2 : |e2| ≤ 1 := by
    rw [he2, abs_div, abs_of_pos p2, div_le_one p2]; exact hv
  have b3 : |e3| ≤ 1 := by
    rw [he3, abs_div, abs_of_pos p3, div_le_one p3]; exact ht
  have hbox : TM.Box e1 e2 e3 := ⟨b1, b2, b3⟩
  have hu' : (a : ℝ) / SCALE + (h1 : ℝ) / SCALE * e1 = u := by
    have : (h1 : ℝ) / SCALE * e1 = u - (a : ℝ) / SCALE := by
      rw [he1, mul_div_cancel₀ _ (ne_of_gt p1)]
    linarith
  have hv' : (b : ℝ) / SCALE + (h2 : ℝ) / SCALE * e2 = v := by
    have : (h2 : ℝ) / SCALE * e2 = v - (b : ℝ) / SCALE := by
      rw [he2, mul_div_cancel₀ _ (ne_of_gt p2)]
    linarith
  have ht' : (d : ℝ) / SCALE + (h3 : ℝ) / SCALE * e3 = t := by
    have : (h3 : ℝ) / SCALE * e3 = t - (d : ℝ) / SCALE := by
      rw [he3, mul_div_cancel₀ _ (ne_of_gt p3)]
    linarith
  have key : ev (shift c ((a : ℝ) / SCALE) ((b : ℝ) / SCALE) ((d : ℝ) / SCALE))
      ((h1 : ℝ) / SCALE * e1) ((h2 : ℝ) / SCALE * e2) ((h3 : ℝ) / SCALE * e3) = ev c u v t := by
    rw [ev_shift, hu', hv', ht']
  have := TM.geBound_sound hbox
    (toTM_mem (ITMem_IshiftA hC a b d) h1 h2 h3 hbox) hpos
  rwa [key] at this


/-! ### Tensor arithmetic used to assemble a box's polynomial -/

def ITadd (C D : IT) : IT := fun i j k => Itv.add (C i j k) (D i j k)
def ITsub (C D : IT) : IT := fun i j k => Itv.sub (C i j k) (D i j k)
def ITsmul (s : Itv) (C : IT) : IT := fun i j k => Itv.mul s (C i j k)

theorem ITMem_add {C D : IT} {c d : RT} (hC : ITMem C c) (hD : ITMem D d) :
    ITMem (ITadd C D) (fun i j k => c i j k + d i j k) :=
  fun i j k => Itv.mem_add (hC i j k) (hD i j k)

theorem ITMem_sub {C D : IT} {c d : RT} (hC : ITMem C c) (hD : ITMem D d) :
    ITMem (ITsub C D) (fun i j k => c i j k - d i j k) :=
  fun i j k => Itv.mem_sub (hC i j k) (hD i j k)

theorem ITMem_smul {s : Itv} {x : ℝ} (hs : s.Mem x) {C : IT} {c : RT} (hC : ITMem C c) :
    ITMem (ITsmul s C) (fun i j k => x * c i j k) :=
  fun i j k => Itv.mem_mul hs (hC i j k)

theorem ev_add (c d : RT) (u v t : ℝ) :
    ev (fun i j k => c i j k + d i j k) u v t = ev c u v t + ev d u v t := by
  unfold ev
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem ev_sub (c d : RT) (u v t : ℝ) :
    ev (fun i j k => c i j k - d i j k) u v t = ev c u v t - ev d u v t := by
  unfold ev
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem ev_smul (x : ℝ) (c : RT) (u v t : ℝ) :
    ev (fun i j k => x * c i j k) u v t = x * ev c u v t := by
  unfold ev
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ### The tangent-line minorant of `1/√x`

`1/√x` is convex, so every tangent line lies below it; the tangent at a *rational* `a₀ > 0` has
rational coefficients, which is what keeps the whole box computation inside `ℤ`.  The proof is the
factorisation `(a − a₀)²(a + 2a₀) ≥ 0`. -/

theorem inv_sqrt_tangent {a0 x : ℝ} (h0 : 0 < a0) (hx : 0 < x) :
    1 / a0 - (x - a0 ^ 2) / (2 * a0 ^ 3) ≤ (Real.sqrt x)⁻¹ := by
  set a := Real.sqrt x with ha
  have hapos : 0 < a := Real.sqrt_pos.mpr hx
  have hsq : a ^ 2 = x := Real.sq_sqrt hx.le
  rw [← hsq, inv_eq_one_div, ← sub_nonneg]
  have hid : 1 / a - (1 / a0 - (a ^ 2 - a0 ^ 2) / (2 * a0 ^ 3))
      = ((a - a0) ^ 2 * (a + 2 * a0)) / (2 * a * a0 ^ 3) := by
    field_simp
    ring
  rw [hid]
  positivity

end Thomson.Tri5b
