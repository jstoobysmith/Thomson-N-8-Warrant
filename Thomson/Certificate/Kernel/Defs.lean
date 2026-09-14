import Thomson.Certificate.Slack

/-! # Task 1c, part 2: the kernel lemma — definitions

`psi k a b u`, the `(a, b)` entry of `B_kᵀ Acomb_k(u) B_k`, is a polynomial in `u` and `u*` (the
kernel bases `B` are polynomials in `u*`).  The kernel lemma is that it has a double zero at
`u = u*`, for every `(k, a, b)`: `B` was built from the kernel vectors of the family, and the identity
holds with `u*` replaced by a free variable.  It is proved entry by entry (the generated files
`Thomson/Certificate/Kernel/*.lean`, `scripts/threepoint/kernel_lean.py`), in two steps:

* `Entries<k>.lean`: each entry of `Acomb_k(u)` is an explicit polynomial in `u` with rational
  coefficients.  The irrationality `√2` enters `Acomb` only through `cU u = √2(1−u)/2`, in the
  inner products `−u ± cU u` of the two cross chords, and cancels between them: each identity is a
  `linear_combination` of `cU_sq : cU u ² = (1 − u)²/2`.
* `Psi<k>.lean`: `psi k a b u = (u − u*)²·χ(u)`, an identity of polynomials in `u, u*` (`ring`).

To keep the generated statements free of `Fin` arithmetic, everything is restated here with
natural-number indices (`S3N`, `AcombN`, `psiN`). -/

namespace Thomson
open Finset Matrix

/-- The entry `(i, j)` of `S3 k x y z`, with natural-number indices. -/
noncomputable def S3N (k i j : ℕ) (x y z : ℝ) : ℝ :=
  (1 / 6) * (x ^ i * y ^ j * Q3 k x y z + x ^ i * z ^ j * Q3 k x z y
    + y ^ i * x ^ j * Q3 k y x z + y ^ i * z ^ j * Q3 k y z x
    + z ^ i * x ^ j * Q3 k z x y + z ^ i * y ^ j * Q3 k z y x)

theorem S3_apply (k : ℕ) (x y z : ℝ) (i j : Fin (9 - k)) :
    S3 k x y z i j = S3N k i j x y z := by
  simp only [S3, Y3, S3N, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, smul_eq_mul]

/-- The entry `(i, j)` of `Acomb k u`, with natural-number indices. -/
noncomputable def AcombN (k i j : ℕ) (u : ℝ) : ℝ :=
  8 * S3N k i j 1 1 1
    + 48 * S3N k i j 1 (tA u) (tA u) + 24 * S3N k i j 1 (tD u) (tD u)
    + 48 * S3N k i j 1 (tN u) (tN u) + 48 * S3N k i j 1 (tF u) (tF u)
    + 48 * S3N k i j (tF u) (tF u) (tA u) + 96 * S3N k i j (tF u) (tD u) (tN u)
    + 96 * S3N k i j (tF u) (tN u) (tA u) + 48 * S3N k i j (tD u) (tA u) (tA u)
    + 48 * S3N k i j (tN u) (tN u) (tA u)

theorem Acomb_apply (k : ℕ) (u : ℝ) (i j : Fin (9 - k)) : Acomb k u i j = AcombN k i j u := by
  simp only [Acomb, AcombN, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, S3_apply]

/-- `psi` with natural-number indices: `Σ_{i,j} B_k[i,a] · Acomb_k(u)[i,j] · B_k[j,b]`. -/
noncomputable def psiN (k a b : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ range (9 - k), ∑ i ∈ range (9 - k), Bpoly k i a * AcombN k i j u * Bpoly k j b

theorem psi_eq_psiN (k : Fin 6) (a b : Fin (9 - (k : ℕ))) (u : ℝ) :
    psi k a b u = psiN k a b u := by
  unfold psi psiN
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Acomb_apply, B,
    Matrix.of_apply]
  rw [Finset.sum_congr rfl fun (j : Fin (9 - (k : ℕ))) _ =>
    Fin.sum_univ_eq_sum_range (fun i => Bpoly k i a * AcombN k i j u * Bpoly k j b) _]
  exact Fin.sum_univ_eq_sum_range (fun j => ∑ i ∈ range (9 - (k : ℕ)),
    Bpoly k i a * AcombN k i j u * Bpoly k j b) _

/-! ### Symmetry: only the entries `i ≤ j` (and `a ≤ b`) are computed -/

theorem Q3_swap (k : ℕ) (x y z : ℝ) : Q3 k x y z = Q3 k y x z := by
  match k with
  | 0 => simp only [Q3]
  | 1 => simp only [Q3]; ring
  | 2 => simp only [Q3]; ring
  | 3 => simp only [Q3]; ring
  | 4 => simp only [Q3]; ring
  | 5 => simp only [Q3]; ring
  | k + 6 => simp only [Q3]

theorem S3N_symm (k i j : ℕ) (x y z : ℝ) : S3N k i j x y z = S3N k j i x y z := by
  unfold S3N
  rw [Q3_swap k x y z, Q3_swap k x z y, Q3_swap k y z x]
  ring

theorem AcombN_symm (k i j : ℕ) (u : ℝ) : AcombN k i j u = AcombN k j i u := by
  unfold AcombN; simp only [S3N_symm k i j]

theorem psiN_symm (k a b : ℕ) (u : ℝ) : psiN k a b u = psiN k b a u := by
  unfold psiN
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [AcombN_symm k j i]; ring

theorem DoubleZero.congr {f g : ℝ → ℝ} {x₀ : ℝ} (h : DoubleZero f x₀) (e : ∀ u, f u = g u) :
    DoubleZero g x₀ := by
  obtain ⟨G, hG, hf⟩ := h
  exact ⟨G, hG, fun u => by rw [← e, hf]⟩

end Thomson
