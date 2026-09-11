import Thomson.TriLocalCert.Jet
import Thomson.Tri5b.Bridge

/-! # Task 5a, numeric side, step 3: `triP` along a ray, as a polynomial

Along the ray `t ↦ τ + t·δ` the triangle polynomial is a polynomial in `t`:

`triP p (τ + tδ) = λ(BC + AC + AB) − ABC · F(U, V, W)`,

`A = τ₁ + tδ₀`, `U = 1 − A²/2`, …, with `F = ev (cF (Mmat (Hp p)))` the coefficient tensor of
Task 5b's bridge.  `gL` builds that polynomial as a coefficient list (`rayR_eq`), so its iterated
derivatives are lists too (`deriv_iter_rayR`): the second and third derivatives at `0` are `2·g₂`
and `6·g₃`, and the fourth derivative is bounded through a majorant of `gL` (`Thomson.TriLocalCert.Jet`).
`rayR` is Task 5a's `rayP` (`Thomson/ThreePoint/Cert/TriLocalDeriv.lean`), written out. -/

namespace Thomson.TriLocalCert

open Thomson Thomson.Pair Thomson.Tri5b Finset

/-- `Uⁿ`. -/
noncomputable def rpowL (U : List ℝ) : ℕ → List ℝ
  | 0 => [1]
  | n + 1 => rmul U (rpowL U n)

theorem reval_rpowL (U : List ℝ) (x : ℝ) : ∀ n, reval (rpowL U n) x = reval U x ^ n
  | 0 => by simp [rpowL]
  | n + 1 => by rw [rpowL, reval_rmul, reval_rpowL U x n, pow_succ, mul_comm]

theorem reval_foldr' {α : Type*} (L : List α) (f : α → List ℝ → List ℝ) (g : α → ℝ) (x : ℝ)
    (hf : ∀ a acc, reval (f a acc) x = g a + reval acc x) :
    reval (L.foldr f []) x = (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.foldr_cons, hf, ih, List.map_cons, List.sum_cons]

/-- `Σ_{i,j,k} c_ijk Uⁱ Vʲ Wᵏ`, nested (Horner in the tensor index). -/
noncomputable def FL (c : RT) (U V W : List ℝ) : List ℝ :=
  (List.finRange 9).foldr (fun (i : Fin 9) acc => radd (rmul (rpowL U i)
    ((List.finRange 9).foldr (fun (j : Fin 9) acc' => radd (rmul (rpowL V j)
      ((List.finRange 9).foldr (fun (k : Fin 9) acc'' =>
        radd (rsmul (c i j k) (rpowL W k)) acc'') [])) acc') [])) acc) []

theorem reval_FL (c : RT) (U V W : List ℝ) (x : ℝ) :
    reval (FL c U V W) x = ev c (reval U x) (reval V x) (reval W x) := by
  set u := reval U x; set v := reval V x; set w := reval W x
  have hk : ∀ i j : Fin 9, reval ((List.finRange 9).foldr (fun (k : Fin 9) acc'' =>
      radd (rsmul (c i j k) (rpowL W k)) acc'') []) x = ∑ k : Fin 9, c i j k * w ^ (k : ℕ) := by
    intro i j
    rw [reval_foldr' _ _ (fun (k : Fin 9) => c i j k * w ^ (k : ℕ)) x, ← Fin.sum_univ_def]
    intro k acc; rw [reval_radd, reval_rsmul, reval_rpowL]
  have hj : ∀ i : Fin 9, reval ((List.finRange 9).foldr (fun (j : Fin 9) acc' =>
      radd (rmul (rpowL V j) ((List.finRange 9).foldr (fun (k : Fin 9) acc'' =>
        radd (rsmul (c i j k) (rpowL W k)) acc'') [])) acc') []) x
      = ∑ j : Fin 9, v ^ (j : ℕ) * ∑ k : Fin 9, c i j k * w ^ (k : ℕ) := by
    intro i
    rw [reval_foldr' _ _ (fun (j : Fin 9) => v ^ (j : ℕ) * ∑ k : Fin 9, c i j k * w ^ (k : ℕ)) x,
      ← Fin.sum_univ_def]
    intro j acc; rw [reval_radd, reval_rmul, reval_rpowL, hk]
  unfold FL
  rw [reval_foldr' _ _ (fun (i : Fin 9) => u ^ (i : ℕ) * ∑ j : Fin 9, v ^ (j : ℕ) *
      ∑ k : Fin 9, c i j k * w ^ (k : ℕ)) x, ← Fin.sum_univ_def]
  · unfold ev
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · intro i acc; rw [reval_radd, reval_rmul, reval_rpowL, hj]

/-- `1 − (a + x d)²/2`. -/
noncomputable def uL (a d : ℝ) : List ℝ := radd [1] (rsmul (-1 / 2) (rmul [a, d] [a, d]))

theorem reval_uL (a d x : ℝ) : reval (uL a d) x = 1 - (a + x * d) ^ 2 / 2 := by
  simp only [uL, reval_radd, reval_rsmul, reval_rmul, reval_cons, reval_nil]; ring

/-- **The ray polynomial** of `triP p` from `τ` in direction `δ`. -/
noncomputable def gL (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) : List ℝ :=
  radd (rsmul lamFix (radd (radd (rmul [τ.2.1, δ 1] [τ.2.2, δ 2]) (rmul [τ.1, δ 0] [τ.2.2, δ 2]))
      (rmul [τ.1, δ 0] [τ.2.1, δ 1])))
    (rsmul (-1) (rmul (rmul (rmul [τ.1, δ 0] [τ.2.1, δ 1]) [τ.2.2, δ 2])
      (FL (cF (Mmat (Hp p))) (uL τ.1 (δ 0)) (uL τ.2.1 (δ 1)) (uL τ.2.2 (δ 2)))))

/-- The ray function (Task 5a's `rayP`). -/
noncomputable def rayR (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  triP p (τ.1 + t * δ 0) (τ.2.1 + t * δ 1) (τ.2.2 + t * δ 2)

theorem rayR_eq (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    rayR p τ δ = reval (gL p τ δ) := by
  funext x
  simp only [rayR, gL, reval_radd, reval_rsmul, reval_rmul, reval_FL, reval_uL, reval_cons,
    reval_nil, ev_cF_eq_Fh, triP]
  ring

/-- **The derivatives along the ray are lists.** -/
theorem deriv_iter_rayR (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    ∀ k, deriv^[k] (rayR p τ δ) = reval (rderN k (gL p τ δ))
  | 0 => by simp [rderN, rayR_eq]
  | k + 1 => by
      rw [Function.iterate_succ_apply', deriv_iter_rayR p τ δ k, rderN]
      funext x
      exact (hasDerivAt_reval _ x).deriv

theorem ray2_zero (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    deriv (deriv (rayR p τ δ)) 0 = 2 * co (gL p τ δ) 2 := by
  rw [show deriv (deriv (rayR p τ δ)) = deriv^[2] (rayR p τ δ) from rfl, deriv_iter_rayR,
    reval_rderN_zero]
  norm_num

theorem ray3_zero (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) :
    deriv (deriv (deriv (rayR p τ δ))) 0 = 6 * co (gL p τ δ) 3 := by
  rw [show deriv (deriv (deriv (rayR p τ δ))) = deriv^[3] (rayR p τ δ) from rfl, deriv_iter_rayR,
    reval_rderN_zero]
  norm_num [Nat.factorial]

theorem ray4 (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) (x : ℝ) :
    deriv (deriv (deriv (deriv (rayR p τ δ)))) x = reval (rderN 4 (gL p τ δ)) x := by
  rw [show deriv (deriv (deriv (deriv (rayR p τ δ)))) = deriv^[4] (rayR p τ δ) from rfl,
    deriv_iter_rayR]

end Thomson.TriLocalCert
