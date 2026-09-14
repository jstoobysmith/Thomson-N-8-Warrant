import Thomson.Pivots.System

/-! # Task 1b, step 9a: literal tables, and what they mean

The kernel cannot reduce well-founded recursion, so none of the `Array`-based tables of Task 5b's
engine (`Array.ofFn`, hence `toITA` and `Tab3`) can be used here: `decide +kernel` is the only
evaluator, and its diet is `List.getD`, structural recursion and `match` on numerals.

It is also not enough to hand the kernel the *definition* of a tensor and ask for an entry of the
pivot system: the kernel caches every closed subterm it reduces, so a single `entAt (GIT j) i` does
carry its `≈2·10⁵` interval products only once — but it keeps them all, and one such entry was
measured at `14 GB` before it finished.  The work is therefore cut into pieces, each small enough
to be a `decide +kernel` of its own (the cache is dropped between declarations):

* `MItab⟨j⟩` — the six blocks `M_k = B_k H_k B_kᵀ`, checked against `MI BI (eHI j)`;
* `Gtab⟨j⟩` — the `9³` coefficients of the tensor, checked slice by slice against `CF` of the
  *table* `MItab⟨j⟩` (never against `MI` again);
* `col⟨j⟩` — the 24 entries of the column, checked in four chunks of six against `entAt` of the
  *table* `Gtab⟨j⟩`.

`KT00`–`KT23` do this for the tensors of `Gh j`, `KTF` for the tensor of `F` at `pivotsNum` and
the residual.  This file holds the reading functions and the two soundness lemmas that turn a
checked table into an enclosure. -/

namespace Thomson.Task1b

open Thomson Thomson.Tri5b

/-- A table of intervals indexed by three naturals, as nested lists (the blocks `M_k` are ragged,
the tensors are `9 × 9 × 9`). -/
abbrev ITab := List (List (List Itv))

/-- Read a table with `ℕ` indices. -/
def getM (L : ITab) (k i j : ℕ) : Itv := ((L.getD k []).getD i []).getD j Itv.zero

/-- The blocks `M_k`, read back with the `Fin` indices `MI` and `CF` use. -/
def mif (L : ITab) : (k : Fin 6) → Fin (9 - (k : ℕ)) → Fin (9 - (k : ℕ)) → Itv :=
  fun k i j => getM L (k : ℕ) (i : ℕ) (j : ℕ)

/-- A table read back as a coefficient tensor. -/
def getT (L : ITab) : IT := fun p q r => getM L (p : ℕ) (q : ℕ) (r : ℕ)

/-- A checked block table encloses the blocks of the indicator block of pivot `j`. -/
theorem ITMem_mif_G {L : ITab} {j : Fin 24}
    (hM : ∀ (k : Fin 6) (i j' : Fin (9 - (k : ℕ))), mif L k i j' = MI BI (eHI j) k i j')
    (k : Fin 6) (i j' : Fin (9 - (k : ℕ))) : (mif L k i j').Mem (Mmat (eHmat j) k i j') := by
  rw [hM]
  exact ITMem_MI' ITMem_BI' (fun k a b => ITMem_eHI j (k : ℕ) (a : ℕ) (b : ℕ)) k i j'

/-- A checked block table encloses the blocks of `Hp pivotsNum`. -/
theorem ITMem_mif_F {L : ITab}
    (hM : ∀ (k : Fin 6) (i j' : Fin (9 - (k : ℕ))), mif L k i j' = MI BI HI k i j')
    (k : Fin 6) (i j' : Fin (9 - (k : ℕ))) : (mif L k i j').Mem (Mmat (Hp pivotsNum) k i j') := by
  rw [hM]; exact ITMem_MI' ITMem_BI' ITMem_HI k i j'

/-- **A checked tensor table encloses the tensor of `Gh j`.** -/
theorem ITMem_getT_G {L M : ITab} {j : Fin 24}
    (hM : ∀ (k : Fin 6) (i j' : Fin (9 - (k : ℕ))), mif M k i j' = MI BI (eHI j) k i j')
    (hL : ∀ p q r : Fin 9, getT L p q r = CF (mif M) p q r) : ITMem (getT L) (cG j) := by
  intro p q r
  rw [hL]
  exact ITMem_CF (Mmat (eHmat j)) (ITMem_mif_G hM) p q r

/-- **A checked tensor table encloses the tensor of `F` at `pivotsNum`.** -/
theorem ITMem_getT_F {L M : ITab}
    (hM : ∀ (k : Fin 6) (i j' : Fin (9 - (k : ℕ))), mif M k i j' = MI BI HI k i j')
    (hL : ∀ p q r : Fin 9, getT L p q r = CF (mif M) p q r) : ITMem (getT L) cFnum := by
  intro p q r
  rw [hL]
  exact ITMem_CF (Mmat (Hp pivotsNum)) (ITMem_mif_F hM) p q r

end Thomson.Task1b
