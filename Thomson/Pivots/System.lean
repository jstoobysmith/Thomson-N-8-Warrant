import Thomson.Pivots.Tab

/-! # Task 1b, step 9: the pivot system and the residual, enclosed

`entAt C i` is the enclosure of row `i` of column `j` of `pivotMatrix`, from the tensor `C` of
`Gh j`; `resAt C i` the enclosure of `rowFun i pivotsNum` from the tensor `C` of `F` at
`pivotsNum`.  The dispatch follows `rowSpec`. -/

namespace Thomson.Task1b

open Thomson Thomson.Tri5b

def entAt (C : IT) (i : ℕ) : Itv :=
  match i with
  | 0 => entBound C
  | 1 => entPairDer C (chordI 0)
  | 2 => entPairVal C (chordI 1)
  | 3 => entPairDer C (chordI 1)
  | 4 => entPairVal C (chordI 2)
  | 5 => entPairDer C (chordI 2)
  | 6 => entPairVal C (chordI 3)
  | 7 => entPairDer C (chordI 3)
  | 8 => entTriVal C (typeI 0).1 (typeI 0).2.1 (typeI 0).2.2
  | 9 => entTriD C (typeI 0).1 (typeI 0).2.1 (typeI 0).2.2 0
  | 10 => entTriD C (typeI 0).1 (typeI 0).2.1 (typeI 0).2.2 2
  | 11 => entTriVal C (typeI 1).1 (typeI 1).2.1 (typeI 1).2.2
  | 12 => entTriD C (typeI 1).1 (typeI 1).2.1 (typeI 1).2.2 0
  | 13 => entTriD C (typeI 1).1 (typeI 1).2.1 (typeI 1).2.2 2
  | 14 => entTriVal C (typeI 2).1 (typeI 2).2.1 (typeI 2).2.2
  | 15 => entTriD C (typeI 2).1 (typeI 2).2.1 (typeI 2).2.2 0
  | 16 => entTriD C (typeI 2).1 (typeI 2).2.1 (typeI 2).2.2 1
  | 17 => entTriD C (typeI 2).1 (typeI 2).2.1 (typeI 2).2.2 2
  | 18 => entTriVal C (typeI 3).1 (typeI 3).2.1 (typeI 3).2.2
  | 19 => entTriD C (typeI 3).1 (typeI 3).2.1 (typeI 3).2.2 0
  | 20 => entTriD C (typeI 3).1 (typeI 3).2.1 (typeI 3).2.2 1
  | 21 => entTriVal C (typeI 4).1 (typeI 4).2.1 (typeI 4).2.2
  | 22 => entTriD C (typeI 4).1 (typeI 4).2.1 (typeI 4).2.2 0
  | 23 => entTriD C (typeI 4).1 (typeI 4).2.1 (typeI 4).2.2 2
  | _ => Itv.zero

theorem mem_entAt {C : IT} {j : Fin 24} (hC : ITMem C (cG j)) (i : Fin 24) :
    (entAt C i).Mem (pivotMatrix i j) := by
  fin_cases i
  · exact mem_entBound hC
  · exact mem_entPairDer hC (X := 0) rfl
  · exact mem_entPairVal hC (X := 1) rfl
  · exact mem_entPairDer hC (X := 1) rfl
  · exact mem_entPairVal hC (X := 2) rfl
  · exact mem_entPairDer hC (X := 2) rfl
  · exact mem_entPairVal hC (X := 3) rfl
  · exact mem_entPairDer hC (X := 3) rfl
  · exact mem_entTriVal hC (m := 0) rfl
  · exact mem_entTriD hC (m := 0) (c := 0) rfl
  · exact mem_entTriD hC (m := 0) (c := 2) rfl
  · exact mem_entTriVal hC (m := 1) rfl
  · exact mem_entTriD hC (m := 1) (c := 0) rfl
  · exact mem_entTriD hC (m := 1) (c := 2) rfl
  · exact mem_entTriVal hC (m := 2) rfl
  · exact mem_entTriD hC (m := 2) (c := 0) rfl
  · exact mem_entTriD hC (m := 2) (c := 1) rfl
  · exact mem_entTriD hC (m := 2) (c := 2) rfl
  · exact mem_entTriVal hC (m := 3) rfl
  · exact mem_entTriD hC (m := 3) (c := 0) rfl
  · exact mem_entTriD hC (m := 3) (c := 1) rfl
  · exact mem_entTriVal hC (m := 4) rfl
  · exact mem_entTriD hC (m := 4) (c := 0) rfl
  · exact mem_entTriD hC (m := 4) (c := 2) rfl

def resAt (C : IT) (i : ℕ) : Itv :=
  match i with
  | 0 => resBound C
  | 1 => resPairDer C (chordI 0)
  | 2 => resPairVal C (chordI 1)
  | 3 => resPairDer C (chordI 1)
  | 4 => resPairVal C (chordI 2)
  | 5 => resPairDer C (chordI 2)
  | 6 => resPairVal C (chordI 3)
  | 7 => resPairDer C (chordI 3)
  | 8 => resTriVal C (typeI 0).1 (typeI 0).2.1 (typeI 0).2.2
  | 9 => resTriD C (typeI 0).1 (typeI 0).2.1 (typeI 0).2.2 0
  | 10 => resTriD C (typeI 0).1 (typeI 0).2.1 (typeI 0).2.2 2
  | 11 => resTriVal C (typeI 1).1 (typeI 1).2.1 (typeI 1).2.2
  | 12 => resTriD C (typeI 1).1 (typeI 1).2.1 (typeI 1).2.2 0
  | 13 => resTriD C (typeI 1).1 (typeI 1).2.1 (typeI 1).2.2 2
  | 14 => resTriVal C (typeI 2).1 (typeI 2).2.1 (typeI 2).2.2
  | 15 => resTriD C (typeI 2).1 (typeI 2).2.1 (typeI 2).2.2 0
  | 16 => resTriD C (typeI 2).1 (typeI 2).2.1 (typeI 2).2.2 1
  | 17 => resTriD C (typeI 2).1 (typeI 2).2.1 (typeI 2).2.2 2
  | 18 => resTriVal C (typeI 3).1 (typeI 3).2.1 (typeI 3).2.2
  | 19 => resTriD C (typeI 3).1 (typeI 3).2.1 (typeI 3).2.2 0
  | 20 => resTriD C (typeI 3).1 (typeI 3).2.1 (typeI 3).2.2 1
  | 21 => resTriVal C (typeI 4).1 (typeI 4).2.1 (typeI 4).2.2
  | 22 => resTriD C (typeI 4).1 (typeI 4).2.1 (typeI 4).2.2 0
  | 23 => resTriD C (typeI 4).1 (typeI 4).2.1 (typeI 4).2.2 2
  | _ => Itv.zero

theorem mem_resAt {C : IT} (hC : ITMem C cFnum) (i : Fin 24) :
    (resAt C i).Mem (rowFun i pivotsNum) := by
  fin_cases i
  · exact mem_resBound hC
  · exact mem_resPairDer hC (X := 0) rfl
  · exact mem_resPairVal hC (X := 1) rfl
  · exact mem_resPairDer hC (X := 1) rfl
  · exact mem_resPairVal hC (X := 2) rfl
  · exact mem_resPairDer hC (X := 2) rfl
  · exact mem_resPairVal hC (X := 3) rfl
  · exact mem_resPairDer hC (X := 3) rfl
  · exact mem_resTriVal hC (m := 0) rfl
  · exact mem_resTriD hC (m := 0) (c := 0) rfl
  · exact mem_resTriD hC (m := 0) (c := 2) rfl
  · exact mem_resTriVal hC (m := 1) rfl
  · exact mem_resTriD hC (m := 1) (c := 0) rfl
  · exact mem_resTriD hC (m := 1) (c := 2) rfl
  · exact mem_resTriVal hC (m := 2) rfl
  · exact mem_resTriD hC (m := 2) (c := 0) rfl
  · exact mem_resTriD hC (m := 2) (c := 1) rfl
  · exact mem_resTriD hC (m := 2) (c := 2) rfl
  · exact mem_resTriVal hC (m := 3) rfl
  · exact mem_resTriD hC (m := 3) (c := 0) rfl
  · exact mem_resTriD hC (m := 3) (c := 1) rfl
  · exact mem_resTriVal hC (m := 4) rfl
  · exact mem_resTriD hC (m := 4) (c := 0) rfl
  · exact mem_resTriD hC (m := 4) (c := 2) rfl

end Thomson.Task1b
