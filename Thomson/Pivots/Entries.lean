import Thomson.Pivots.Points

/-! # Task 1b, step 6: an enclosure of every entry of the pivot system

`entI i j` encloses `pivotMatrix i j`.  By row type:

* the bound row is `−4·Gh j (1,1,1)`;
* a pair-value row is `−3x·Gh j (1,w,w)`, `w = 1 − x²/2`, at a chord `x`;
* a pair-derivative row is `−3·G(1,w,w) + 3x²·∂_w G(1,w,w)` (`pairDer_eq`);
* a triangle-value row is `−abc·Gh j (u,v,t)` at a touching type;
* a triangle-derivative row is `−(bc)·G + a²bc·∂_u G`, and its two mirror images (`triD_eq_k`). -/

namespace Thomson.Task1b

open Thomson Thomson.Tri5b

theorem ITMem_GIT' (j : Fin 24) : ITMem (GIT j) (cG j) := ITMem_GIT j

/-- An integer, as an exact interval. -/
def intI (n : ℤ) : Itv := Itv.cst (n * SCALE)

theorem mem_intI (n : ℤ) : (intI n).Mem (n : ℝ) := by
  have h := Itv.mem_cst (n * SCALE)
  rwa [Int.cast_mul, mul_div_assoc, div_self (ne_of_gt SCALE_pos'), mul_one] at h

/-! ### The five row types -/

def entBound (C : IT) : Itv := Itv.mul (intI (-4)) (evI C Itv.one Itv.one Itv.one)

theorem mem_entBound {C : IT} {j : Fin 24} (hC : ITMem C (cG j)) :
    (entBound C).Mem (pivotMatrix 0 j) := by
  rw [pivotMatrix_bound_row, Gh_eq_ev]
  have h := Itv.mem_mul (mem_intI (-4)) (mem_evI hC Itv.mem_one Itv.mem_one Itv.mem_one)
  simpa [entBound] using h

def entPairVal (C : IT) (X : Itv) : Itv :=
  Itv.mul (Itv.neg (Itv.mul (intI 3) X)) (evI C Itv.one (subSqI X) (subSqI X))

theorem mem_entPairVal {C : IT} {j : Fin 24} (hC : ITMem C (cG j)) {i : Fin 24} {X : Fin 4}
    (h : rowSpec i = .pairVal X) : (entPairVal C (chordI X)).Mem (pivotMatrix i j) := by
  rw [pivotMatrix_pairVal_row h, Gh_eq_ev]
  have hx := mem_chordI X
  have hw := mem_subSqI hx
  have hm := Itv.mem_mul (Itv.mem_neg (Itv.mem_mul (mem_intI 3) hx)) (mem_evI hC Itv.mem_one hw hw)
  simpa [entPairVal] using hm

def entPairDer (C : IT) (X : Itv) : Itv :=
  Itv.add (Itv.mul (intI (-3)) (evI C Itv.one (subSqI X) (subSqI X)))
    (Itv.mul (Itv.mul (intI 3) (Itv.mul X X)) (evIDiagD C (subSqI X)))

theorem mem_entPairDer {C : IT} {j : Fin 24} (hC : ITMem C (cG j)) {i : Fin 24} {X : Fin 4}
    (h : rowSpec i = .pairDer X) : (entPairDer C (chordI X)).Mem (pivotMatrix i j) := by
  rw [pivotMatrix_pairDer_row h, pairDer_eq]
  have hx := mem_chordI X
  have hw := mem_subSqI hx
  have hm := Itv.mem_add (Itv.mem_mul (mem_intI (-3)) (mem_evI hC Itv.mem_one hw hw))
    (Itv.mem_mul (Itv.mem_mul (mem_intI 3) (Itv.mem_mul hx hx)) (mem_evIDiagD hC hw))
  have e : ((-3 : ℤ) : ℝ) * ev (cG j) 1 (1 - chord X ^ 2 / 2) (1 - chord X ^ 2 / 2)
      + ((3 : ℤ) : ℝ) * (chord X * chord X) * evDiagD (cG j) (1 - chord X ^ 2 / 2)
      = -3 * ev (cG j) 1 (1 - chord X ^ 2 / 2) (1 - chord X ^ 2 / 2)
        + 3 * chord X ^ 2 * evDiagD (cG j) (1 - chord X ^ 2 / 2) := by push_cast; ring
  rwa [e] at hm

def entTriVal (G : IT) (A B C : Itv) : Itv :=
  Itv.mul (Itv.neg (Itv.mul (Itv.mul A B) C)) (evI G (subSqI A) (subSqI B) (subSqI C))

theorem mem_entTriVal {G : IT} {j : Fin 24} (hG : ITMem G (cG j)) {i : Fin 24} {m : Fin 5}
    (h : rowSpec i = .triVal m) :
    (entTriVal G (typeI m).1 (typeI m).2.1 (typeI m).2.2).Mem (pivotMatrix i j) := by
  rw [pivotMatrix_triVal_row h, Gh_eq_ev]
  obtain ⟨ha, hb, hc⟩ := mem_typeI m
  exact Itv.mem_mul (Itv.mem_neg (Itv.mem_mul (Itv.mem_mul ha hb) hc))
    (mem_evI hG (mem_subSqI ha) (mem_subSqI hb) (mem_subSqI hc))

/-- The three triangle-derivative rows, by the moving coordinate. -/
def entTriD (G : IT) (A B C : Itv) (c : Fin 3) : Itv :=
  let UA := subSqI A
  let UB := subSqI B
  let UC := subSqI C
  match (c : ℕ) with
  | 0 => Itv.add (Itv.mul (Itv.neg (Itv.mul B C)) (evI G UA UB UC))
      (Itv.mul (Itv.mul (Itv.mul (Itv.mul A A) B) C) (evID1 G UA UB UC))
  | 1 => Itv.add (Itv.mul (Itv.neg (Itv.mul A C)) (evI G UA UB UC))
      (Itv.mul (Itv.mul (Itv.mul (Itv.mul A B) B) C) (evID2 G UA UB UC))
  | _ => Itv.add (Itv.mul (Itv.neg (Itv.mul A B)) (evI G UA UB UC))
      (Itv.mul (Itv.mul (Itv.mul (Itv.mul A B) C) C) (evID3 G UA UB UC))

/-- The derivative along coordinate `c`, whatever `c` is. -/
theorem triD_row_eq (j : Fin 24) (a b c3 : ℝ) (c : Fin 3) :
    deriv (fun d => -((a + (if c = 0 then 1 else 0) * d) * (b + (if c = 1 then 1 else 0) * d)
        * (c3 + (if c = 2 then 1 else 0) * d))
        * Gh j (1 - (a + (if c = 0 then 1 else 0) * d) ^ 2 / 2)
          (1 - (b + (if c = 1 then 1 else 0) * d) ^ 2 / 2)
          (1 - (c3 + (if c = 2 then 1 else 0) * d) ^ 2 / 2)) 0
      = match (c : ℕ) with
        | 0 => -(b * c3) * ev (cG j) (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2)
            + a * a * b * c3 * evD1 (cG j) (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2)
        | 1 => -(a * c3) * ev (cG j) (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2)
            + a * b * b * c3 * evD2 (cG j) (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2)
        | _ => -(a * b) * ev (cG j) (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2)
            + a * b * c3 * c3 * evD3 (cG j) (1 - a ^ 2 / 2) (1 - b ^ 2 / 2) (1 - c3 ^ 2 / 2) := by
  fin_cases c
  · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, one_mul, Fin.reduceEq, zero_mul, add_zero]
    exact triD_eq_1 j a b c3
  · simp only [Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte, zero_mul, add_zero, one_mul]
    exact triD_eq_2 j a b c3
  · simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte, zero_mul, add_zero,
      one_mul]
    exact triD_eq_3 j a b c3

theorem mem_entTriD {G : IT} {j : Fin 24} (hG : ITMem G (cG j)) {i : Fin 24} {m : Fin 5}
    {c : Fin 3} (h : rowSpec i = .triD m c) :
    (entTriD G (typeI m).1 (typeI m).2.1 (typeI m).2.2 c).Mem (pivotMatrix i j) := by
  rw [pivotMatrix_triD_row h, triD_row_eq]
  obtain ⟨ha, hb, hc⟩ := mem_typeI m
  have hua := mem_subSqI ha
  have hub := mem_subSqI hb
  have huc := mem_subSqI hc
  fin_cases c
  · exact Itv.mem_add (Itv.mem_mul (Itv.mem_neg (Itv.mem_mul hb hc)) (mem_evI hG hua hub huc))
      (Itv.mem_mul (Itv.mem_mul (Itv.mem_mul (Itv.mem_mul ha ha) hb) hc) (mem_evID1 hG hua hub huc))
  · exact Itv.mem_add (Itv.mem_mul (Itv.mem_neg (Itv.mem_mul ha hc)) (mem_evI hG hua hub huc))
      (Itv.mem_mul (Itv.mem_mul (Itv.mem_mul (Itv.mem_mul ha hb) hb) hc) (mem_evID2 hG hua hub huc))
  · exact Itv.mem_add (Itv.mem_mul (Itv.mem_neg (Itv.mem_mul ha hb)) (mem_evI hG hua hub huc))
      (Itv.mem_mul (Itv.mem_mul (Itv.mem_mul (Itv.mem_mul ha hb) hc) hc) (mem_evID3 hG hua hub huc))

end Thomson.Task1b
