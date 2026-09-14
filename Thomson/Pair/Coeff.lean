import Thomson.Numerics.Poly
import Thomson.TriangleGlobal.CertIntervals

/-! # Task 4, step 4: the pair polynomial as a polynomial in `w = 1 − s²/2`

`pairP p s = α − s·R(w)` with `w = 1 − s²/2`, `α = 1 − 18λ` and `R(w) = a₀ + a₁w + 3F(1, w, w)`,
and `F(1, w, w)` is a polynomial of degree `16` in `w` (`S3_one_apply`):

`F(1, w, w) = (1/3) Σ_k Σ_{i,j} M_k[i,j] (w^{i+j} (1 − w²)ᵏ + [k = 0] (wⁱ + wʲ))`,

with `M_k = B_k H_k B_kᵀ` the constant matrices of Task 5b (`Thomson.Tri5b.Mmat`).  So

`Φ(w) := α² − (2 − 2w) R(w)² = (α − sR)(α + sR) = pairP·(2α − pairP)`

is a polynomial of degree `33` in `w ∈ [−1, 1]`, and `Φ ≥ 0` gives `pairP ≥ 0` (`pairP_nonneg_of_Phi`).
This file builds the coefficient lists of `F(1,w,w)` (`rD`), `R` (`rR`) and `Φ` (`rPhi`) on `ℝ`,
their interval mirrors (`ID`, `IR`, `IPhi`) with the enclosure lemmas, and transfers the double
zeros of `pairP` at the chords to `Φ` (`Phi_tight`). -/

namespace Thomson.Pair

open Thomson Thomson.Tri5b Finset

/-! ## Folds -/

theorem reval_foldr {α : Type*} (L : List α) (f : α → List ℝ → List ℝ) (g : α → ℝ) (x : ℝ)
    (hf : ∀ a acc, reval (f a acc) x = reval acc x + g a) (l0 : List ℝ) :
    reval (L.foldr f l0) x = reval l0 x + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.foldr_cons, hf, ih, List.map_cons, List.sum_cons]; ring

theorem LMem_foldr {α : Type*} (L : List α) (F : α → List Itv → List Itv)
    (f : α → List ℝ → List ℝ) (hF : ∀ a Acc acc, LMem Acc acc → LMem (F a Acc) (f a acc))
    {A0 : List Itv} {a0 : List ℝ} (h0 : LMem A0 a0) : LMem (L.foldr F A0) (L.foldr f a0) := by
  induction L with
  | nil => exact h0
  | cons a L ih => exact hF a _ _ ih

/-! ## The coefficients of `F(1, w, w)` -/

section real

variable (M : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ)

/-- `Σ_{i,j} M_k[i,j] w^{i+j}`. -/
noncomputable def rmu (k : Fin 6) : List ℝ :=
  (List.finRange (9 - (k : ℕ))).foldr (fun (i : Fin (9 - (k : ℕ))) acc =>
    (List.finRange (9 - (k : ℕ))).foldr (fun (j : Fin (9 - (k : ℕ))) acc' => raddAt ((i : ℕ) + j) (M k i j) acc') acc) []

/-- `(1 − w²)ⁿ`. -/
noncomputable def rom : ℕ → List ℝ
  | 0 => [1]
  | n + 1 => rmul [1, 0, -1] (rom n)

/-- `Σ_{i,j} M_0[i,j] (wⁱ + wʲ)`, written as a sum over all blocks. -/
noncomputable def rrho : List ℝ :=
  (List.finRange 6).foldr (fun (k : Fin 6) acc =>
    (List.finRange (9 - (k : ℕ))).foldr (fun (i : Fin (9 - (k : ℕ))) acc' =>
      (List.finRange (9 - (k : ℕ))).foldr (fun (j : Fin (9 - (k : ℕ))) acc'' =>
        if (k : ℕ) = 0 then raddAt (i : ℕ) (M k i j) (raddAt (j : ℕ) (M k i j) acc'') else acc'')
        acc') acc) []

/-- The coefficients of `F(1, w, w)`. -/
noncomputable def rD : List ℝ :=
  rsmul (1 / 3) (radd ((List.finRange 6).foldr (fun (k : Fin 6) acc => radd (rmul (rmu M k) (rom k)) acc) [])
    (rrho M))

theorem reval_rom (w : ℝ) : ∀ n, reval (rom n) w = (1 - w ^ 2) ^ n
  | 0 => by simp [rom]
  | n + 1 => by
      rw [rom, reval_rmul, reval_rom w n, pow_succ]
      simp only [reval_cons, reval_nil]; ring

theorem reval_rmu (k : Fin 6) (w : ℝ) :
    reval (rmu M k) w = ∑ i, ∑ j, M k i j * w ^ ((i : ℕ) + j) := by
  unfold rmu
  rw [reval_foldr _ _ (fun (i : Fin (9 - (k : ℕ))) => ∑ j, M k i j * w ^ ((i : ℕ) + j)) w,
    reval_nil, zero_add,
    Fin.sum_univ_def]
  intro i acc
  rw [reval_foldr _ _ (fun (j : Fin (9 - (k : ℕ))) => M k i j * w ^ ((i : ℕ) + j)) w,
    Fin.sum_univ_def]
  intro j acc'
  exact reval_raddAt _ _ _ _

theorem reval_rrho (w : ℝ) :
    reval (rrho M) w = ∑ k : Fin 6, ∑ i, ∑ j,
      (if (k : ℕ) = 0 then M k i j * (w ^ (i : ℕ) + w ^ (j : ℕ)) else 0) := by
  unfold rrho
  rw [reval_foldr _ _ (fun (k : Fin 6) => ∑ i, ∑ j,
      (if (k : ℕ) = 0 then M k i j * (w ^ (i : ℕ) + w ^ (j : ℕ)) else 0)) w, reval_nil, zero_add,
    Fin.sum_univ_def]
  intro k acc
  rw [reval_foldr _ _ (fun (i : Fin (9 - (k : ℕ))) => ∑ j,
      (if (k : ℕ) = 0 then M k i j * (w ^ (i : ℕ) + w ^ (j : ℕ)) else 0)) w, Fin.sum_univ_def]
  intro i acc'
  rw [reval_foldr _ _ (fun (j : Fin (9 - (k : ℕ))) =>
      (if (k : ℕ) = 0 then M k i j * (w ^ (i : ℕ) + w ^ (j : ℕ)) else 0)) w, Fin.sum_univ_def]
  intro j acc''
  split_ifs
  · rw [reval_raddAt, reval_raddAt]; ring
  · ring

theorem reval_rD (w : ℝ) :
    reval (rD M) w = ∑ k : Fin 6, ∑ i, ∑ j, M k i j * S3 (k : ℕ) 1 w w i j := by
  unfold rD
  rw [reval_rsmul, reval_radd, reval_rrho,
    reval_foldr _ _
      (fun (k : Fin 6) => (∑ i, ∑ j, M k i j * w ^ ((i : ℕ) + j)) * (1 - w ^ 2) ^ (k : ℕ)) w,
    reval_nil, zero_add, ← Fin.sum_univ_def, ← Finset.sum_add_distrib, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [S3_one_apply (k : ℕ) (by omega) w i j]
    split_ifs <;> ring
  · intro k acc
    rw [reval_radd, reval_rmul, reval_rmu, reval_rom]
    ring

/-- **`F(1, w, w)` is the polynomial `rD`.** -/
theorem Fh_one_eq (H : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ) (w : ℝ) :
    Fh H 1 w w = reval (rD (Mmat H)) w := by
  rw [reval_rD, Fh_eq_Msum]

end real

/-! ## `R`, `Φ`, and the pair polynomial -/

/-- `α = 1 − 18λ`. -/
noncomputable def alpha : ℝ := 1 - 18 * lamFix

theorem alpha_pos : 0 < alpha := by norm_num [alpha, lamFix]

/-- `R(w) = a₀ + a₁ w + 3 F(1, w, w)`. -/
noncomputable def rR (D : List ℝ) : List ℝ := radd [a0Fix, a1Fix] (rsmul 3 D)

/-- `Φ(w) = α² − (2 − 2w) R(w)²`. -/
noncomputable def rPhi (R : List ℝ) : List ℝ :=
  radd [alpha ^ 2] (rsmul (-1) (rmul [2, -2] (rmul R R)))

theorem reval_rR (D : List ℝ) (w : ℝ) :
    reval (rR D) w = a0Fix + a1Fix * w + 3 * reval D w := by
  simp only [rR, reval_radd, reval_rsmul, reval_cons, reval_nil]; ring

theorem reval_rPhi (R : List ℝ) (w : ℝ) :
    reval (rPhi R) w = alpha ^ 2 - (2 - 2 * w) * reval R w ^ 2 := by
  simp only [rPhi, reval_radd, reval_rsmul, reval_rmul, reval_cons, reval_nil]; ring

/-- The `R` of the certificate with pivots `p`. -/
noncomputable def Rcert (p : Fin 24 → ℝ) : List ℝ := rR (rD (Mmat (Hp p)))

theorem pairP_eq (p : Fin 24 → ℝ) (s : ℝ) :
    pairP p s = alpha - s * reval (Rcert p) (1 - s ^ 2 / 2) := by
  rw [Rcert, reval_rR, ← Fh_one_eq, pairP, alpha]

/-- **`Φ ≥ 0` gives the pair inequality.** -/
theorem pairP_nonneg_of_Phi {p : Fin 24 → ℝ} {s : ℝ}
    (h : 0 ≤ reval (rPhi (Rcert p)) (1 - s ^ 2 / 2)) : 0 ≤ pairP p s := by
  rw [reval_rPhi] at h
  rw [pairP_eq]
  set R := reval (Rcert p) (1 - s ^ 2 / 2)
  have ha := alpha_pos
  have e : (2 - 2 * (1 - s ^ 2 / 2)) * R ^ 2 = (s * R) ^ 2 := by ring
  rw [e] at h
  by_contra hneg
  push Not at hneg
  nlinarith

/-- The derivative of `α − s·R(1 − s²/2)`. -/
theorem hasDerivAt_alpha_sub (R : List ℝ) (s : ℝ) :
    HasDerivAt (fun y => alpha - y * reval R (1 - y ^ 2 / 2))
      (-(reval R (1 - s ^ 2 / 2)) + s ^ 2 * reval (rder R) (1 - s ^ 2 / 2)) s := by
  have hw : HasDerivAt (fun y : ℝ => 1 - y ^ 2 / 2) (-s) s := by
    have := ((hasDerivAt_pow 2 s).div_const 2).const_sub (1 : ℝ)
    exact this.congr_deriv (by norm_num)
  have hR : HasDerivAt (fun y => reval R (1 - y ^ 2 / 2))
      (reval (rder R) (1 - s ^ 2 / 2) * (-s)) s :=
    (hasDerivAt_reval R (1 - s ^ 2 / 2)).comp s hw
  exact (((hasDerivAt_id' s).mul hR).const_sub alpha).congr_deriv (by ring)

/-- The derivative of the pair polynomial, through `R`. -/
theorem hasDerivAt_pairP (p : Fin 24 → ℝ) (s : ℝ) :
    HasDerivAt (pairP p) (-(reval (Rcert p) (1 - s ^ 2 / 2))
      + s ^ 2 * reval (rder (Rcert p)) (1 - s ^ 2 / 2)) s := by
  have hfun : pairP p = fun y => alpha - y * reval (Rcert p) (1 - y ^ 2 / 2) :=
    funext fun y => pairP_eq p y
  rw [hfun]
  exact hasDerivAt_alpha_sub _ s

/-- The derivative of `Φ`, in terms of `R`. -/
theorem rder_rPhi_eq (R : List ℝ) (w : ℝ) :
    reval (rder (rPhi R)) w = 2 * reval R w ^ 2 - (2 - 2 * w) * (2 * reval R w * reval (rder R) w) := by
  have h1 := hasDerivAt_reval (rPhi R) w
  have hfun : reval (rPhi R) = fun y => alpha ^ 2 - (2 - 2 * y) * reval R y ^ 2 := by
    funext y; exact reval_rPhi R y
  have hl : HasDerivAt (fun y : ℝ => 2 - 2 * y) (-2) w :=
    ((hasDerivAt_id' w).const_mul 2).const_sub 2 |>.congr_deriv (by ring)
  have h2 : HasDerivAt (fun y => alpha ^ 2 - (2 - 2 * y) * reval R y ^ 2)
      (-(-2 * reval R w ^ 2 + (2 - 2 * w) * (2 * reval R w * reval (rder R) w))) w := by
    have hsq := (hasDerivAt_reval R w).fun_pow 2
    have := (hl.mul hsq).const_sub (alpha ^ 2)
    exact this.congr_deriv (by push_cast; ring)
  rw [hfun] at h1
  rw [h1.unique h2]; ring

/-- **The double zeros move to `Φ`.**  At `w = 1 − s²/2` for a double zero `s > 0` of `pairP`,
`Φ` and `Φ'` vanish. -/
theorem Phi_tight {p : Fin 24 → ℝ} {s : ℝ} (h0 : pairP p s = 0) (h1 : deriv (pairP p) s = 0) :
    reval (rPhi (Rcert p)) (1 - s ^ 2 / 2) = 0 ∧
      reval (rder (rPhi (Rcert p))) (1 - s ^ 2 / 2) = 0 := by
  rw [pairP_eq] at h0
  rw [(hasDerivAt_pairP p s).deriv] at h1
  have e : 2 - 2 * (1 - s ^ 2 / 2) = s ^ 2 := by ring
  refine ⟨?_, ?_⟩
  · rw [reval_rPhi, e]
    have : alpha = s * reval (Rcert p) (1 - s ^ 2 / 2) := by linarith
    rw [this]; ring
  · rw [rder_rPhi_eq, e]
    have : reval (Rcert p) (1 - s ^ 2 / 2)
        = s ^ 2 * reval (rder (Rcert p)) (1 - s ^ 2 / 2) := by linarith
    rw [this]; ring

/-- The mirror image: `Φ(−·)` and its derivative vanish at `−w`. -/
theorem ralt_tight {q : List ℝ} {w : ℝ} (h0 : reval q w = 0) (h1 : reval (rder q) w = 0) :
    reval (ralt q) (-w) = 0 ∧ reval (rder (ralt q)) (-w) = 0 := by
  refine ⟨by rw [reval_ralt, neg_neg, h0], ?_⟩
  have hA := hasDerivAt_reval (ralt q) (-w)
  have hfun : reval (ralt q) = fun y => reval q (-y) := funext fun y => reval_ralt q y
  have hB : HasDerivAt (fun y => reval q (-y)) (-reval (rder q) (-(-w))) (-w) :=
    ((hasDerivAt_reval q (-(-w))).comp (-w) (hasDerivAt_neg (-w))).congr_deriv (by ring)
  rw [hfun] at hA
  rw [hA.unique hB, neg_neg, h1, neg_zero]

/-! ## The interval mirror -/

section interval

variable (MI : (k : Fin 6) → Fin (9 - (k : ℕ)) → Fin (9 - (k : ℕ)) → Itv)

def Imu (k : Fin 6) : List Itv :=
  (List.finRange (9 - (k : ℕ))).foldr (fun (i : Fin (9 - (k : ℕ))) acc =>
    (List.finRange (9 - (k : ℕ))).foldr (fun (j : Fin (9 - (k : ℕ))) acc' => laddAt ((i : ℕ) + j) (MI k i j) acc') acc) []

def Iom : ℕ → List Itv
  | 0 => [Itv.one]
  | n + 1 => lmul [Itv.one, Itv.zero, Itv.cst (-SCALE)] (Iom n)

def Irho : List Itv :=
  (List.finRange 6).foldr (fun (k : Fin 6) acc =>
    (List.finRange (9 - (k : ℕ))).foldr (fun (i : Fin (9 - (k : ℕ))) acc' =>
      (List.finRange (9 - (k : ℕ))).foldr (fun (j : Fin (9 - (k : ℕ))) acc'' =>
        if (k : ℕ) = 0 then laddAt (i : ℕ) (MI k i j) (laddAt (j : ℕ) (MI k i j) acc'') else acc'')
        acc') acc) []

def ID : List Itv :=
  lsmul (Itv.ofDiv 1 3) (ladd ((List.finRange 6).foldr (fun (k : Fin 6) acc => ladd (lmul (Imu MI k) (Iom k)) acc) [])
    (Irho MI))

end interval

/-- `a₀`, `a₁`, `α²` on the grid (exact). -/
def a0Q : ℤ := 9443687221010000000000000000000000000000
def a1Q : ℤ := 2445383048987000000000000000000000000000
def alpha2Q : ℤ := 6785178949568748588416131600000000000000

def IR (D : List Itv) : List Itv := ladd [Itv.cst a0Q, Itv.cst a1Q] (lsmul (Itv.cst (3 * SCALE)) D)

def IPhi (R : List Itv) : List Itv :=
  ladd [Itv.cst alpha2Q] (lsmul (Itv.cst (-SCALE)) (lmul [Itv.cst (2 * SCALE), Itv.cst (-2 * SCALE)]
    (lmul R R)))

theorem mem_cst_int (n : ℤ) : (Itv.cst (n * SCALE)).Mem (n : ℝ) := by
  have h := Itv.mem_cst (n * SCALE)
  have e : ((n * SCALE : ℤ) : ℝ) / SCALE = n := by
    push_cast; field_simp [SCALE_pos'.ne']
  rwa [e] at h

theorem LMem_Iom : ∀ n, LMem (Iom n) (rom n)
  | 0 => LMem.cons Itv.mem_one LMem.nil
  | n + 1 => by
      refine LMem_lmul ?_ (LMem_Iom n)
      refine LMem.cons Itv.mem_one (LMem.cons Itv.mem_zero (LMem.cons ?_ LMem.nil))
      simpa using mem_cst_int (-1)

theorem LMem_ID {MI : (k : Fin 6) → Fin (9 - (k : ℕ)) → Fin (9 - (k : ℕ)) → Itv}
    {M : (k : Fin 6) → Matrix (Fin (9 - (k : ℕ))) (Fin (9 - (k : ℕ))) ℝ}
    (hM : ∀ k i j, (MI k i j).Mem (M k i j)) : LMem (ID MI) (rD M) := by
  have stepmu : ∀ (k : Fin 6) (i j : Fin (9 - (k : ℕ))) (A : List Itv) (a : List ℝ), LMem A a →
      LMem (laddAt ((i : ℕ) + j) (MI k i j) A) (raddAt ((i : ℕ) + j) (M k i j) a) :=
    fun k i j _ _ h => LMem_laddAt (hM k i j) _ h
  have steprho : ∀ (k : Fin 6) (i j : Fin (9 - (k : ℕ))) (A : List Itv) (a : List ℝ), LMem A a →
      LMem (if (k : ℕ) = 0 then laddAt (i : ℕ) (MI k i j) (laddAt (j : ℕ) (MI k i j) A) else A)
        (if (k : ℕ) = 0 then raddAt (i : ℕ) (M k i j) (raddAt (j : ℕ) (M k i j) a) else a) := by
    intro k i j A a h
    split_ifs
    · exact LMem_laddAt (hM k i j) _ (LMem_laddAt (hM k i j) _ h)
    · exact h
  have hmu : ∀ k, LMem (Imu MI k) (rmu M k) := fun k => by
    unfold Imu rmu
    exact LMem_foldr _ _ _ (fun i _ _ h => LMem_foldr _ _ _
      (fun j A a h' => stepmu k i j A a h') h) LMem.nil
  have hrho : LMem (Irho MI) (rrho M) := by
    unfold Irho rrho
    exact LMem_foldr _ _ _ (fun k _ _ h => LMem_foldr _ _ _ (fun i _ _ h' => LMem_foldr _ _ _
      (fun j A a h'' => steprho k i j A a h'') h') h) LMem.nil
  have hthird : (Itv.ofDiv 1 3).Mem (1 / 3) := by
    have := Itv.mem_ofDiv (n := 1) (d := 3) (by norm_num)
    norm_num at this ⊢; exact this
  unfold ID rD
  exact LMem_lsmul hthird (LMem_ladd (LMem_foldr _ _ _
    (fun k _ _ h => LMem_ladd (LMem_lmul (hmu k) (LMem_Iom k)) h) LMem.nil) hrho)

theorem LMem_IR {D : List Itv} {d : List ℝ} (h : LMem D d) : LMem (IR D) (rR d) := by
  refine LMem_ladd (LMem.cons ?_ (LMem.cons ?_ LMem.nil)) (LMem_lsmul (mem_cst_int 3) h)
  · have := Itv.mem_cst a0Q
    rwa [show ((a0Q : ℤ) : ℝ) / SCALE = a0Fix by norm_num [a0Q, a0Fix, SCALE]] at this
  · have := Itv.mem_cst a1Q
    rwa [show ((a1Q : ℤ) : ℝ) / SCALE = a1Fix by norm_num [a1Q, a1Fix, SCALE]] at this

theorem LMem_IPhi {R : List Itv} {r : List ℝ} (h : LMem R r) : LMem (IPhi R) (rPhi r) := by
  refine LMem_ladd (LMem.cons ?_ LMem.nil)
    (LMem_lsmul (by simpa using mem_cst_int (-1)) (LMem_lmul ?_ (LMem_lmul h h)))
  · have := Itv.mem_cst alpha2Q
    rwa [show ((alpha2Q : ℤ) : ℝ) / SCALE = alpha ^ 2 by
      norm_num [alpha2Q, alpha, lamFix, SCALE]] at this
  · exact LMem.cons (by simpa using mem_cst_int 2)
      (LMem.cons (by simpa using mem_cst_int (-2)) LMem.nil)

/-- **The certificate's `Φ`, enclosed**, for any pivots within `10⁻¹²` of `pivotsNum`. -/
theorem LMem_IPhi_cert {p : Fin 24 → ℝ} (hclose : ∀ j, |p j - pivotsNum j| ≤ 1 / 10 ^ 12) :
    LMem (IPhi (IR (ID MIedata))) (rPhi (Rcert p)) := by
  have hc : ∀ j, |p j - pivotsNum j| ≤ (EPS : ℝ) / SCALE := by
    intro j; rw [show (EPS : ℝ) / SCALE = 1 / 10 ^ 12 by norm_num [EPS, SCALE]]; exact hclose j
  exact LMem_IPhi (LMem_IR (LMem_ID (ITMem_MIedata hc)))

end Thomson.Pair
