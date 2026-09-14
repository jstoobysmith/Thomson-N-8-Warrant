import Thomson.Pivots.KT00
import Thomson.Pivots.KT01
import Thomson.Pivots.KT02
import Thomson.Pivots.KT03
import Thomson.Pivots.KT04
import Thomson.Pivots.KT05
import Thomson.Pivots.KT06
import Thomson.Pivots.KT07
import Thomson.Pivots.KT08
import Thomson.Pivots.KT09
import Thomson.Pivots.KT10
import Thomson.Pivots.KT11
import Thomson.Pivots.KT12
import Thomson.Pivots.KT13
import Thomson.Pivots.KT14
import Thomson.Pivots.KT15
import Thomson.Pivots.KT16
import Thomson.Pivots.KT17
import Thomson.Pivots.KT18
import Thomson.Pivots.KT19
import Thomson.Pivots.KT20
import Thomson.Pivots.KT21
import Thomson.Pivots.KT22
import Thomson.Pivots.KT23
import Thomson.Pivots.KTF

/-! # Task 1b, step 9b: the pivot system and the residual, as literal tables

The 24 columns of the enclosure of `pivotMatrix` (`KT00`–`KT23`) and the residual (`KTF`) are
literal lists, each checked against its definition by `decide +kernel` in its own module.  Here
they are assembled into `Mtab`/`Rtab`, which is all the final check (`Check`) reads: from here on
the kernel only walks a list of numerals, never a tensor again. -/

namespace Thomson.Task1b

open Thomson Thomson.Tri5b

/-- The enclosure of `pivotMatrix`, column by column. -/
def Mtab (i j : ℕ) : Itv :=
  match j with
  | 0 => col00.getD i Itv.zero
  | 1 => col01.getD i Itv.zero
  | 2 => col02.getD i Itv.zero
  | 3 => col03.getD i Itv.zero
  | 4 => col04.getD i Itv.zero
  | 5 => col05.getD i Itv.zero
  | 6 => col06.getD i Itv.zero
  | 7 => col07.getD i Itv.zero
  | 8 => col08.getD i Itv.zero
  | 9 => col09.getD i Itv.zero
  | 10 => col10.getD i Itv.zero
  | 11 => col11.getD i Itv.zero
  | 12 => col12.getD i Itv.zero
  | 13 => col13.getD i Itv.zero
  | 14 => col14.getD i Itv.zero
  | 15 => col15.getD i Itv.zero
  | 16 => col16.getD i Itv.zero
  | 17 => col17.getD i Itv.zero
  | 18 => col18.getD i Itv.zero
  | 19 => col19.getD i Itv.zero
  | 20 => col20.getD i Itv.zero
  | 21 => col21.getD i Itv.zero
  | 22 => col22.getD i Itv.zero
  | 23 => col23.getD i Itv.zero
  | _ => Itv.zero

theorem mem_Mtab (i j : Fin 24) : (Mtab i j).Mem (pivotMatrix i j) := by
  fin_cases j
  · exact mem_col00 i
  · exact mem_col01 i
  · exact mem_col02 i
  · exact mem_col03 i
  · exact mem_col04 i
  · exact mem_col05 i
  · exact mem_col06 i
  · exact mem_col07 i
  · exact mem_col08 i
  · exact mem_col09 i
  · exact mem_col10 i
  · exact mem_col11 i
  · exact mem_col12 i
  · exact mem_col13 i
  · exact mem_col14 i
  · exact mem_col15 i
  · exact mem_col16 i
  · exact mem_col17 i
  · exact mem_col18 i
  · exact mem_col19 i
  · exact mem_col20 i
  · exact mem_col21 i
  · exact mem_col22 i
  · exact mem_col23 i

/-- The enclosure of the residual. -/
def Rtab (i : ℕ) : Itv := resL.getD i Itv.zero

theorem mem_Rtab (i : Fin 24) : (Rtab i).Mem (rowFun i pivotsNum) := mem_resL i

end Thomson.Task1b
