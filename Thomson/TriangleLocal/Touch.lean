import Thomson.TriangleGlobal.CubeData
import Thomson.Antiprism.SharpChords

/-! # Task 5a, numeric side: fixed-point enclosures of the touching-type coordinates

Rational (`10⁻⁴⁰`-grid) enclosures of the four chord lengths, from `Thomson.TriangleGlobal.CubeData`'s
`chordA_bounds`/`chordD_bounds`/`chordN_bounds`/`chordF_bounds` (25–34 digit rational bounds), and
of the five touching types, from `Thomson.Antiprism.SharpChords`'s `touchType_zero`..`touchType_four`. -/

namespace Thomson.TriLocalCert

open Thomson Thomson.Tri5b

def TA : Itv := ⟨11712477381927344687859652885067900000000,
  11712477381927344687859652885068300000000⟩
def TD : Itv := ⟨16563944362509771876618635911157400000000,
  16563944362509771876618635911157800000000⟩
def TN : Itv := ⟨12876935261433174061741833895703400000000,
  12876935261433174061741833895703900000000⟩
def TF : Itv := ⟨18968929475026778646313590239647800000000,
  18968929475026778646313590239648200000000⟩

theorem mem_TA : TA.Mem (chord 0) := by
  rw [chord_zero]
  obtain ⟨c1, c2⟩ := chordA_bounds
  have h1 := mul_le_mul_of_nonneg_right c1 SCALE_pos'.le
  have h2 := mul_le_mul_of_nonneg_right c2 SCALE_pos'.le
  constructor <;> unfold TA <;> norm_num [SCALE] at h1 h2 ⊢ <;> linarith

theorem mem_TD : TD.Mem (chord 1) := by
  rw [chord_one]
  obtain ⟨c1, c2⟩ := chordD_bounds
  have h1 := mul_le_mul_of_nonneg_right c1 SCALE_pos'.le
  have h2 := mul_le_mul_of_nonneg_right c2 SCALE_pos'.le
  constructor <;> unfold TD <;> norm_num [SCALE] at h1 h2 ⊢ <;> linarith

theorem mem_TN : TN.Mem (chord 2) := by
  rw [chord_two]
  obtain ⟨c1, c2⟩ := chordN_bounds
  have h1 := mul_le_mul_of_nonneg_right c1 SCALE_pos'.le
  have h2 := mul_le_mul_of_nonneg_right c2 SCALE_pos'.le
  constructor <;> unfold TN <;> norm_num [SCALE] at h1 h2 ⊢ <;> linarith

theorem mem_TF : TF.Mem (chord 3) := by
  rw [chord_three]
  obtain ⟨c1, c2⟩ := chordF_bounds
  have h1 := mul_le_mul_of_nonneg_right c1 SCALE_pos'.le
  have h2 := mul_le_mul_of_nonneg_right c2 SCALE_pos'.le
  constructor <;> unfold TF <;> norm_num [SCALE] at h1 h2 ⊢ <;> linarith

/-- The five touching types, as chord-`Itv` triples, following `touchType_zero`..`touchType_four`
(`FFA, FDN, FNA, DAA, NNA`). -/
def Tt : Fin 5 → Itv × Itv × Itv :=
  ![(TF, TF, TA), (TF, TD, TN), (TF, TN, TA), (TD, TA, TA), (TN, TN, TA)]

theorem Tt_mem (m : Fin 5) :
    (Tt m).1.Mem (touchType m).1 ∧ (Tt m).2.1.Mem (touchType m).2.1 ∧
      (Tt m).2.2.Mem (touchType m).2.2 := by
  fin_cases m
  · simp only [Tt]; exact ⟨mem_TF, mem_TF, mem_TA⟩
  · simp only [Tt]; exact ⟨mem_TF, mem_TD, mem_TN⟩
  · rw [show (⟨2, by omega⟩ : Fin 5) = 2 from rfl]
    simp only [Tt, touchType_two]; exact ⟨mem_TF, mem_TN, mem_TA⟩
  · rw [show (⟨3, by omega⟩ : Fin 5) = 3 from rfl]
    simp only [Tt, touchType_three]; exact ⟨mem_TD, mem_TA, mem_TA⟩
  · rw [show (⟨4, by omega⟩ : Fin 5) = 4 from rfl]
    simp only [Tt, touchType_four]; exact ⟨mem_TN, mem_TN, mem_TA⟩

end Thomson.TriLocalCert
