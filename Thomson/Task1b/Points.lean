import Thomson.Task1b.Rows
import Thomson.Tri5b.CubeData

/-! # Task 1b, step 5: the evaluation points

The rows of the pivot system are evaluated at the four antiprism chords `√2 r*, 2r*, s₂*, s₄*`.
Task 5b already enclosed them to 32 digits (`Thomson.Tri5b.chordA_bounds` …), with denominators
dividing `10³²`, so on the `10⁻⁴⁰` grid the enclosures are exact. -/

namespace Thomson.Task1b

open Thomson Thomson.Tri5b

def chordAI : Itv := ⟨11712477381927344687859652885067900000000, 11712477381927344687859652885068300000000⟩
def chordDI : Itv := ⟨16563944362509771876618635911157400000000, 16563944362509771876618635911157800000000⟩
def chordNI : Itv := ⟨12876935261433174061741833895703400000000, 12876935261433174061741833895703900000000⟩
def chordFI : Itv := ⟨18968929475026778646313590239647800000000, 18968929475026778646313590239648200000000⟩

theorem mem_chordAI : chordAI.Mem (Real.sqrt 2 * rStar) := by
  obtain ⟨h1, h2⟩ := chordA_bounds
  constructor <;> simp only [chordAI, SCALE] <;> push_cast <;> linarith

theorem mem_chordDI : chordDI.Mem (2 * rStar) := by
  obtain ⟨h1, h2⟩ := chordD_bounds
  constructor <;> simp only [chordDI, SCALE] <;> push_cast <;> linarith

theorem mem_chordNI : chordNI.Mem s2Star := by
  obtain ⟨h1, h2⟩ := chordN_bounds
  constructor <;> simp only [chordNI, SCALE] <;> push_cast <;> linarith

theorem mem_chordFI : chordFI.Mem s4Star := by
  obtain ⟨h1, h2⟩ := chordF_bounds
  constructor <;> simp only [chordFI, SCALE] <;> push_cast <;> linarith

/-- The chords, by index (a match: see `Thomson.Tri5b.pivQn` on `![…]` at run time). -/
def chordI (X : Fin 4) : Itv :=
  match (X : ℕ) with
  | 0 => chordAI | 1 => chordDI | 2 => chordNI | _ => chordFI

theorem mem_chordI (X : Fin 4) : (chordI X).Mem (chord X) := by
  fin_cases X
  · exact mem_chordAI
  · exact mem_chordDI
  · exact mem_chordNI
  · exact mem_chordFI

/-- The touching types, coordinate by coordinate. -/
def typeI (m : Fin 5) : Itv × Itv × Itv :=
  match (m : ℕ) with
  | 0 => (chordFI, chordFI, chordAI)
  | 1 => (chordFI, chordDI, chordNI)
  | 2 => (chordFI, chordNI, chordAI)
  | 3 => (chordDI, chordAI, chordAI)
  | _ => (chordNI, chordNI, chordAI)

theorem mem_typeI (m : Fin 5) :
    (typeI m).1.Mem (touchType m).1 ∧ (typeI m).2.1.Mem (touchType m).2.1
      ∧ (typeI m).2.2.Mem (touchType m).2.2 := by
  fin_cases m
  · exact ⟨mem_chordFI, mem_chordFI, mem_chordAI⟩
  · exact ⟨mem_chordFI, mem_chordDI, mem_chordNI⟩
  · exact ⟨mem_chordFI, mem_chordNI, mem_chordAI⟩
  · exact ⟨mem_chordDI, mem_chordAI, mem_chordAI⟩
  · exact ⟨mem_chordNI, mem_chordNI, mem_chordAI⟩

/-! ### `x ↦ 1 − x²/2` -/

/-- `1/2`. -/
def halfI : Itv := Itv.cst 5000000000000000000000000000000000000000

theorem mem_halfI : halfI.Mem (1 / 2) := by
  have h := Itv.mem_cst 5000000000000000000000000000000000000000
  have e : ((5000000000000000000000000000000000000000 : ℤ) : ℝ) / SCALE = 1 / 2 := by
    unfold SCALE; norm_num
  rwa [e] at h

def subSqI (X : Itv) : Itv := Itv.sub Itv.one (Itv.mul (Itv.mul X X) halfI)

theorem mem_subSqI {X : Itv} {x : ℝ} (hx : X.Mem x) : (subSqI X).Mem (1 - x ^ 2 / 2) := by
  have h := Itv.mem_sub Itv.mem_one (Itv.mem_mul (Itv.mem_mul hx hx) mem_halfI)
  have e : (1 : ℝ) - x * x * (1 / 2) = 1 - x ^ 2 / 2 := by ring
  rwa [e] at h

end Thomson.Task1b
