import Mathlib

/-! # Uniqueness — shared combinatorial definitions

`UniquenessPlan.md`.  Colours of a chord: `A = 0, D = 1, N = 2, F = 3`, matching
`Thomson.chord = ![√2·r*, 2r*, s2*, s4*]`.  A triangle is *allowed* if its colour multiset is one
of the five antiprism types `FFA, FDN, FNA, DAA, NNA` (`Thomson.touchType`). -/

namespace Thomson.Unique

/-- Number of entries of `(X, Y, Z)` equal to `k`. -/
def cnt (X Y Z k : Fin 4) : ℕ :=
  (if X = k then 1 else 0) + (if Y = k then 1 else 0) + (if Z = k then 1 else 0)

/-- The colour-count vector `(#A, #D, #N, #F)` of a triple. -/
def cntVec (X Y Z : Fin 4) : ℕ × ℕ × ℕ × ℕ :=
  (cnt X Y Z 0, cnt X Y Z 1, cnt X Y Z 2, cnt X Y Z 3)

/-- The five antiprism triangle types as count vectors `(#A, #D, #N, #F)`:
`FFA, FDN, FNA, DAA, NNA`. -/
def allowedVecs : List (ℕ × ℕ × ℕ × ℕ) :=
  [(1, 0, 0, 2), (0, 1, 1, 1), (1, 0, 1, 1), (2, 1, 0, 0), (1, 0, 2, 0)]

/-- A colour triple is one of the five antiprism triangle types (as a multiset). -/
def allowedTri (X Y Z : Fin 4) : Bool := allowedVecs.contains (cntVec X Y Z)

theorem allowedTri_perm12 (X Y Z : Fin 4) : allowedTri X Y Z = allowedTri Y X Z := by
  revert X Y Z; decide

theorem allowedTri_perm23 (X Y Z : Fin 4) : allowedTri X Y Z = allowedTri X Z Y := by
  revert X Y Z; decide

/-- 21 ordered allowed triples (3 + 6 + 6 + 3 + 3). -/
theorem allowedTri_card :
    ((Finset.univ : Finset (Fin 4 × Fin 4 × Fin 4)).filter
      (fun t => allowedTri t.1 t.2.1 t.2.2 = true)).card = 21 := by decide

end Thomson.Unique
