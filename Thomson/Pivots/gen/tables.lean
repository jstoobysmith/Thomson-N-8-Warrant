import Thomson.Pivots.System

/-! # The generator of `KT00`–`KT23` and `KTF` — not part of the library

Run it in the compiled interpreter (about four minutes), then turn its output into the modules:

    lake env lean Thomson/Pivots/gen/tables.lean > out.txt
    python3 Thomson/Pivots/gen/mk_tables.py out.txt Thomson/Task1b

Nothing here is trusted: every table it prints is checked against its definition by
`decide +kernel` in the module it lands in. -/

namespace Thomson.Task1b
open Thomson Thomson.Tri5b

def itvStr (I : Itv) : String := "⟨" ++ toString I.lo ++ ", " ++ toString I.hi ++ "⟩"
def l1 (L : List Itv) : String := "[" ++ String.intercalate ", " (L.map itvStr) ++ "]"
def l2 (L : List (List Itv)) : String := "[" ++ String.intercalate ", " (L.map l1) ++ "]"
def l3 (L : List (List (List Itv))) : String := "[" ++ String.intercalate ", " (L.map l2) ++ "]"

def mitab (HI : ℕ → ℕ → ℕ → Itv) : List (List (List Itv)) :=
  (List.finRange 6).map fun k : Fin 6 =>
    (List.finRange (9 - (k : ℕ))).map fun i : Fin (9 - (k : ℕ)) =>
      (List.finRange (9 - (k : ℕ))).map fun j : Fin (9 - (k : ℕ)) => MI BI HI k i j

def getM (L : List (List (List Itv))) (k i j : ℕ) : Itv :=
  ((L.getD k []).getD i []).getD j Itv.zero

def mif (L : List (List (List Itv))) : (k : Fin 6) → Fin (9 - (k : ℕ)) → Fin (9 - (k : ℕ)) → Itv :=
  fun k i j => getM L (k : ℕ) (i : ℕ) (j : ℕ)

def gten (L : List (List (List Itv))) : List (List (List Itv)) :=
  (List.finRange 9).map fun p : Fin 9 => (List.finRange 9).map fun q : Fin 9 =>
    (List.finRange 9).map fun r : Fin 9 => CF (mif L) p q r

def getL3 (L : List (List (List Itv))) : IT := fun p q r =>
  ((L.getD (p : ℕ) []).getD (q : ℕ) []).getD (r : ℕ) Itv.zero

def run : IO Unit := do
  for j in List.finRange 24 do
    let M := mitab (eHI j)
    let G := gten M
    IO.println s!"MI {j.val} {l3 M}"
    IO.println s!"G {j.val} {l3 G}"
    IO.println s!"COL {j.val} {l1 ((List.finRange 24).map fun i : Fin 24 => entAt (getL3 G) i)}"
  let M := mitab HI
  let G := gten M
  IO.println s!"MI 24 {l3 M}"
  IO.println s!"G 24 {l3 G}"
  IO.println s!"RES {l1 ((List.finRange 24).map fun i : Fin 24 => resAt (getL3 G) i)}"

#eval run

end Thomson.Task1b
