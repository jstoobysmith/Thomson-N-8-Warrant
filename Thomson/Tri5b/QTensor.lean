import Thomson.Tri5b.Shift1
import Thomson.Tri5b.MForm

/-! # Task 5b, step 13: the coefficient tensors of `Q_k`

`Q3 k` is an explicit polynomial of degree `k` in each variable — 65 nonzero coefficients over all
six blocks.  They are written out here and each is checked against the definition of `Q3` once. -/

namespace Thomson.Tri5b

open Thomson

/-- Coefficients of `Q3 0`. -/
def QC0 : ℕ → ℕ → ℕ → ℤ
  | 0, 0, 0 => 1
  | _, _, _ => 0

/-- Coefficients of `Q3 1`. -/
def QC1 : ℕ → ℕ → ℕ → ℤ
  | 0, 0, 1 => 1
  | 1, 1, 0 => -1
  | _, _, _ => 0

/-- Coefficients of `Q3 2`. -/
def QC2 : ℕ → ℕ → ℕ → ℤ
  | 0, 0, 0 => -1
  | 0, 0, 2 => 2
  | 0, 2, 0 => 1
  | 1, 1, 1 => -4
  | 2, 0, 0 => 1
  | 2, 2, 0 => 1
  | _, _, _ => 0

/-- Coefficients of `Q3 3`. -/
def QC3 : ℕ → ℕ → ℕ → ℤ
  | 0, 0, 1 => -3
  | 0, 0, 3 => 4
  | 0, 2, 1 => 3
  | 1, 1, 0 => 3
  | 1, 1, 2 => -12
  | 1, 3, 0 => -3
  | 2, 0, 1 => 3
  | 2, 2, 1 => 9
  | 3, 1, 0 => -3
  | 3, 3, 0 => -1
  | _, _, _ => 0

/-- Coefficients of `Q3 4`. -/
def QC4 : ℕ → ℕ → ℕ → ℤ
  | 0, 0, 0 => 1
  | 0, 0, 2 => -8
  | 0, 0, 4 => 8
  | 0, 2, 0 => -2
  | 0, 2, 2 => 8
  | 0, 4, 0 => 1
  | 1, 1, 1 => 16
  | 1, 1, 3 => -32
  | 1, 3, 1 => -16
  | 2, 0, 0 => -2
  | 2, 0, 2 => 8
  | 2, 2, 0 => -4
  | 2, 2, 2 => 40
  | 2, 4, 0 => 6
  | 3, 1, 1 => -16
  | 3, 3, 1 => -16
  | 4, 0, 0 => 1
  | 4, 2, 0 => 6
  | 4, 4, 0 => 1
  | _, _, _ => 0

/-- Coefficients of `Q3 5`. -/
def QC5 : ℕ → ℕ → ℕ → ℤ
  | 0, 0, 1 => 5
  | 0, 0, 3 => -20
  | 0, 0, 5 => 16
  | 0, 2, 1 => -10
  | 0, 2, 3 => 20
  | 0, 4, 1 => 5
  | 1, 1, 0 => -5
  | 1, 1, 2 => 60
  | 1, 1, 4 => -80
  | 1, 3, 0 => 10
  | 1, 3, 2 => -60
  | 1, 5, 0 => -5
  | 2, 0, 1 => -10
  | 2, 0, 3 => 20
  | 2, 2, 1 => -40
  | 2, 2, 3 => 140
  | 2, 4, 1 => 50
  | 3, 1, 0 => 10
  | 3, 1, 2 => -60
  | 3, 3, 2 => -100
  | 3, 5, 0 => -10
  | 4, 0, 1 => 5
  | 4, 2, 1 => 50
  | 4, 4, 1 => 25
  | 5, 1, 0 => -5
  | 5, 3, 0 => -10
  | 5, 5, 0 => -1
  | _, _, _ => 0

/-- The coefficient of `uⁱ vʲ tˡ` in `Q3 k`. -/
def QCk : ℕ → ℕ → ℕ → ℕ → ℤ
  | 0 => QC0
  | 1 => QC1
  | 2 => QC2
  | 3 => QC3
  | 4 => QC4
  | 5 => QC5
  | _ => fun _ _ _ => 0

/-- `Q3 k` as a real coefficient tensor. -/
noncomputable def QRT (k : ℕ) : RT := fun i j l => ((QCk k i j l : ℤ) : ℝ)

/-- and on the fixed-point grid -/
def QIT (k : ℕ) : IT := fun i j l => Itv.cst (QCk k i j l * SCALE)

theorem ITMem_QIT (k : ℕ) : ITMem (QIT k) (QRT k) := by
  intro i j l
  unfold QIT QRT
  have h := Itv.mem_cst (QCk k i j l * SCALE)
  rwa [Int.cast_mul, mul_div_assoc, div_self (ne_of_gt SCALE_pos'), mul_one] at h

theorem QCk_deg (k : Fin 6) (a q r : Fin 9)
    (h : (k : ℕ) < (a : ℕ) ∨ (k : ℕ) < (q : ℕ) ∨ (k : ℕ) < (r : ℕ)) : QCk k a q r = 0 := by
  revert h
  fin_cases k <;> revert a q r <;> decide

theorem DegAll_QRT (k : Fin 6) : DegAll (QRT (k : ℕ)) (k : ℕ) := by
  intro a q r ha
  unfold QRT
  rw [QCk_deg k a q r ha]
  norm_num

/-! ### `ev (QRT k) = Q3 k` -/

set_option maxHeartbeats 0 in
theorem ev_QRT0 (u v t : ℝ) : ev (QRT 0) u v t = Q3 0 u v t := by
  have hq : Q3 0 u v t = 1 := by simp only [Q3]
  rw [hq]
  simp only [ev, QRT, QCk, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp (config := { maxSteps := 4000000, decide := true }) [QC0]
  try ring

set_option maxHeartbeats 0 in
theorem ev_QRT1 (u v t : ℝ) : ev (QRT 1) u v t = Q3 1 u v t := by
  have hq : Q3 1 u v t = t - u * v := by simp only [Q3]
  rw [hq]
  simp only [ev, QRT, QCk, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp (config := { maxSteps := 4000000, decide := true }) [QC1]
  try ring

set_option maxHeartbeats 0 in
theorem ev_QRT2 (u v t : ℝ) : ev (QRT 2) u v t = Q3 2 u v t := by
  have hq : Q3 2 u v t = 2 * (t - u * v) ^ 2 - (1 - u ^ 2) * (1 - v ^ 2) := by simp only [Q3]
  rw [hq]
  simp only [ev, QRT, QCk, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp (config := { maxSteps := 4000000, decide := true }) [QC2]
  try ring

set_option maxHeartbeats 0 in
theorem ev_QRT3 (u v t : ℝ) : ev (QRT 3) u v t = Q3 3 u v t := by
  have hq : Q3 3 u v t = 4 * (t - u * v) ^ 3 - 3 * (t - u * v) * ((1 - u ^ 2) * (1 - v ^ 2)) := by simp only [Q3]
  rw [hq]
  simp only [ev, QRT, QCk, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp (config := { maxSteps := 4000000, decide := true }) [QC3]
  try ring

set_option maxHeartbeats 0 in
theorem ev_QRT4 (u v t : ℝ) : ev (QRT 4) u v t = Q3 4 u v t := by
  have hq : Q3 4 u v t = 8 * (t - u * v) ^ 4 - 8 * (t - u * v) ^ 2 * ((1 - u ^ 2) * (1 - v ^ 2))
      + ((1 - u ^ 2) * (1 - v ^ 2)) ^ 2 := by simp only [Q3]
  rw [hq]
  simp only [ev, QRT, QCk, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp (config := { maxSteps := 4000000, decide := true }) [QC4]
  try ring

set_option maxHeartbeats 0 in
theorem ev_QRT5 (u v t : ℝ) : ev (QRT 5) u v t = Q3 5 u v t := by
  have hq : Q3 5 u v t = 16 * (t - u * v) ^ 5 - 20 * (t - u * v) ^ 3 * ((1 - u ^ 2) * (1 - v ^ 2))
      + 5 * (t - u * v) * ((1 - u ^ 2) * (1 - v ^ 2)) ^ 2 := by simp only [Q3]
  rw [hq]
  simp only [ev, QRT, QCk, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp (config := { maxSteps := 4000000, decide := true }) [QC5]
  try ring

theorem ev_QRT (k : Fin 6) (u v t : ℝ) : ev (QRT (k : ℕ)) u v t = Q3 (k : ℕ) u v t := by
  fin_cases k
  · exact ev_QRT0 u v t
  · exact ev_QRT1 u v t
  · exact ev_QRT2 u v t
  · exact ev_QRT3 u v t
  · exact ev_QRT4 u v t
  · exact ev_QRT5 u v t

end Thomson.Tri5b
