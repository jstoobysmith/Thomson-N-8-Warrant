import Thomson.TriLocalCert.Ray
import Thomson.Tri5b.Engine

/-! # Task 5a, numeric side, step 4: enclosing the ray polynomial

Two computations on the ray polynomial `gL p τ δ` (`Thomson.TriLocalCert.Ray`), both from an
interval tensor `CF` enclosing `F`'s coefficients (`ITMem CF (cF (Mmat (Hp p)))`):

* **jets** — for a *fixed* direction, the first four coefficients, in interval arithmetic
  truncated at degree `3` (`JMem`, `jmul`): they give the second and third derivatives at `0`;
* **majorants** — for *every* direction with `|δ_i| ≤ s`, a list `P` with `|g_n| ≤ P_n sⁿ`
  (`WMaj`), built from upper bounds of `|c_ijk|` and `|τ_i|`: it bounds the fourth derivative. -/

namespace Thomson.TriLocalCert

open Thomson Thomson.Pair Thomson.Tri5b Finset

/-! ## Jets -/

/-- The jet of a list (its first four coefficients) is enclosed by `J`. -/
def JMem (J : List Itv) (p : List ℝ) : Prop := ∀ n, n < 4 → (J.getD n Itv.zero).Mem (co p n)

theorem sum_map_range (h : ℕ → ℝ) : ∀ n, ((List.range n).map h).sum = ∑ i ∈ range n, h i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, sum_map_range h n,
      Finset.sum_range_succ]; simp

theorem mem_sumL_list {g : ℕ → Itv} {h : ℕ → ℝ} :
    ∀ l : List ℕ, (∀ i ∈ l, (g i).Mem (h i)) → (Itv.sumL (l.map g)).Mem ((l.map h).sum)
  | [], _ => by simpa [Itv.sumL] using Itv.mem_zero
  | a :: l, hl => by
      simpa [Itv.sumL, List.foldr] using Itv.mem_add (hl a (by simp))
        (mem_sumL_list l fun i hi => hl i (by simp [hi]))

theorem mem_sumL_range {g : ℕ → Itv} {h : ℕ → ℝ} (n : ℕ) (hg : ∀ i < n, (g i).Mem (h i)) :
    (Itv.sumL ((List.range n).map g)).Mem (∑ i ∈ range n, h i) := by
  rw [← sum_map_range]; exact mem_sumL_list _ fun i hi => hg i (List.mem_range.mp hi)

/-- Jet addition. -/
def jadd (J K : List Itv) : List Itv := (List.range 4).map fun n => Itv.add (J.getD n Itv.zero) (K.getD n Itv.zero)

/-- Jet multiplication, truncated at degree `3`. -/
def jmul (J K : List Itv) : List Itv := (List.range 4).map fun n =>
  Itv.sumL ((List.range (n + 1)).map fun i => Itv.mul (J.getD i Itv.zero) (K.getD (n - i) Itv.zero))

/-- Jet scaling. -/
def jsmul (c : Itv) (J : List Itv) : List Itv := (List.range 4).map fun n => Itv.mul c (J.getD n Itv.zero)

theorem getD_range4 (f : ℕ → Itv) {n : ℕ} (hn : n < 4) : ((List.range 4).map f).getD n Itv.zero = f n := by
  rw [List.getD_eq_getElem _ _ (by simpa using hn)]; simp

theorem JMem.add {J K : List Itv} {p q : List ℝ} (hJ : JMem J p) (hK : JMem K q) :
    JMem (jadd J K) (radd p q) := fun n hn => by
  rw [jadd, getD_range4 _ hn, co_radd]; exact Itv.mem_add (hJ n hn) (hK n hn)

theorem JMem.mul {J K : List Itv} {p q : List ℝ} (hJ : JMem J p) (hK : JMem K q) :
    JMem (jmul J K) (rmul p q) := fun n hn => by
  rw [jmul, getD_range4 _ hn, co_rmul]
  exact mem_sumL_range (n + 1) fun i hi =>
    Itv.mem_mul (hJ i (by omega)) (hK (n - i) (by omega))

theorem JMem.smul {c : Itv} {x : ℝ} (hc : c.Mem x) {J : List Itv} {p : List ℝ} (hJ : JMem J p) :
    JMem (jsmul c J) (rsmul x p) := fun n hn => by
  rw [jsmul, getD_range4 _ hn, co_rsmul]; exact Itv.mem_mul hc (hJ n hn)

theorem LMem_getD {J : List Itv} {p : List ℝ} (h : LMem J p) :
    ∀ n, (J.getD n Itv.zero).Mem (co p n) := by
  induction h with
  | nil => intro n; simpa [co] using Itv.mem_zero
  | cons hab _ ih =>
    intro n
    cases n with
    | zero => simpa [co] using hab
    | succ n => simpa [co] using ih n

theorem JMem.of_LMem {J : List Itv} {p : List ℝ} (h : LMem J p) : JMem J p :=
  fun n _ => LMem_getD h n

/-- `Uⁿ`, as a jet. -/
def jpow (U : List Itv) : ℕ → List Itv
  | 0 => [Itv.one]
  | n + 1 => jmul U (jpow U n)

theorem JMem.pow {U : List Itv} {u : List ℝ} (h : JMem U u) : ∀ n, JMem (jpow U n) (rpowL u n)
  | 0 => JMem.of_LMem (LMem.cons Itv.mem_one LMem.nil)
  | n + 1 => h.mul (JMem.pow h n)

theorem JMem.nil : JMem [] [] := JMem.of_LMem LMem.nil

theorem JMem.foldr {α : Type*} (L : List α) (F : α → List Itv → List Itv)
    (f : α → List ℝ → List ℝ) (hF : ∀ a Acc acc, JMem Acc acc → JMem (F a Acc) (f a acc)) :
    JMem (L.foldr F []) (L.foldr f []) := by
  induction L with
  | nil => exact JMem.nil
  | cons a L ih => exact hF a _ _ ih

/-- `F(U, V, W)` as a jet, mirroring `FL`. -/
def JFL (CF : IT) (U V W : List Itv) : List Itv :=
  (List.finRange 9).foldr (fun (i : Fin 9) acc => jadd (jmul (jpow U i)
    ((List.finRange 9).foldr (fun (j : Fin 9) acc' => jadd (jmul (jpow V j)
      ((List.finRange 9).foldr (fun (k : Fin 9) acc'' =>
        jadd (jsmul (CF i j k) (jpow W k)) acc'') [])) acc') [])) acc) []

theorem JMem_JFL {CF : IT} {c : RT} (hc : ITMem CF c) {U V W : List Itv} {u v w : List ℝ}
    (hU : JMem U u) (hV : JMem V v) (hW : JMem W w) : JMem (JFL CF U V W) (FL c u v w) := by
  unfold JFL FL
  refine JMem.foldr (List.finRange 9) _ _ (fun (i : Fin 9) Acc acc h => ?_)
  refine JMem.add (JMem.mul (JMem.pow hU i) ?_) h
  refine JMem.foldr (List.finRange 9) _ _ (fun (j : Fin 9) Acc' acc' h' => ?_)
  refine JMem.add (JMem.mul (JMem.pow hV j) ?_) h'
  refine JMem.foldr (List.finRange 9) _ _ (fun (k : Fin 9) Acc'' acc'' h'' => ?_)
  exact JMem.add (JMem.smul (hc i j k) (JMem.pow hW k)) h''

/-- `1 − (a + x d)²/2`, as a jet. -/
def JuL (A D : Itv) : List Itv :=
  jadd [Itv.one] (jsmul (Itv.ofDiv (-1) 2) (jmul [A, D] [A, D]))

theorem mem_mhalf : (Itv.ofDiv (-1) 2).Mem (-1 / 2) := by
  have := Itv.mem_ofDiv (n := -1) (d := 2) (by norm_num); norm_num at this ⊢; exact this

theorem JMem_JuL {A D : Itv} {a d : ℝ} (hA : A.Mem a) (hD : D.Mem d) :
    JMem (JuL A D) (uL a d) := by
  have h2 : JMem [A, D] [a, d] := JMem.of_LMem (LMem.cons hA (LMem.cons hD LMem.nil))
  exact (JMem.of_LMem (LMem.cons Itv.mem_one LMem.nil)).add (JMem.smul mem_mhalf (h2.mul h2))

/-- **The jet of the ray polynomial** (`gL`), from enclosures of `F`'s tensor, of `τ` and of `δ`. -/
def JgL (CF : IT) (lam : Itv) (T0 T1 T2 D0 D1 D2 : Itv) : List Itv :=
  jadd (jsmul lam (jadd (jadd (jmul [T1, D1] [T2, D2]) (jmul [T0, D0] [T2, D2]))
      (jmul [T0, D0] [T1, D1])))
    (jsmul (Itv.cst (-SCALE)) (jmul (jmul (jmul [T0, D0] [T1, D1]) [T2, D2])
      (JFL CF (JuL T0 D0) (JuL T1 D1) (JuL T2 D2))))

theorem JMem_JgL {p : Fin 24 → ℝ} {CF : IT} (hc : ITMem CF (cF (Mmat (Hp p))))
    {lam : Itv} (hlam : lam.Mem lamFix) {τ : ℝ × ℝ × ℝ} {δ : Fin 3 → ℝ}
    {T0 T1 T2 D0 D1 D2 : Itv} (h0 : T0.Mem τ.1) (h1 : T1.Mem τ.2.1) (h2 : T2.Mem τ.2.2)
    (e0 : D0.Mem (δ 0)) (e1 : D1.Mem (δ 1)) (e2 : D2.Mem (δ 2)) :
    JMem (JgL CF lam T0 T1 T2 D0 D1 D2) (gL p τ δ) := by
  have l0 : JMem [T0, D0] [τ.1, δ 0] := JMem.of_LMem (LMem.cons h0 (LMem.cons e0 LMem.nil))
  have l1 : JMem [T1, D1] [τ.2.1, δ 1] := JMem.of_LMem (LMem.cons h1 (LMem.cons e1 LMem.nil))
  have l2 : JMem [T2, D2] [τ.2.2, δ 2] := JMem.of_LMem (LMem.cons h2 (LMem.cons e2 LMem.nil))
  have hm1 : (Itv.cst (-SCALE)).Mem (-1) := by
    have := Itv.mem_cst (-SCALE)
    rwa [show ((-SCALE : ℤ) : ℝ) / SCALE = -1 by push_cast; field_simp [SCALE_pos'.ne']] at this
  unfold JgL gL
  exact (JMem.smul hlam ((l1.mul l2).add (l0.mul l2) |>.add (l0.mul l1))).add
    (JMem.smul hm1 (((l0.mul l1).mul l2).mul
      (JMem_JFL hc (JMem_JuL h0 e0) (JMem_JuL h1 e1) (JMem_JuL h2 e2))))

/-! ## Majorants -/

theorem WMaj.nil (s : ℝ) : WMaj s [] [] := ⟨fun n => by simp, fun n => by simp⟩

theorem WMaj.one {s : ℝ} : WMaj s [1] [1] := by
  refine ⟨fun n => ?_, fun n => ?_⟩ <;> cases n <;> simp

theorem WMaj.lin {s A a d : ℝ} (hA : |a| ≤ A) (hd : |d| ≤ s) : WMaj s [A, 1] [a, d] := by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · rcases n with _ | _ | n
    · simpa using (abs_nonneg a).trans hA
    · simp
    · simp
  · rcases n with _ | _ | n
    · simpa using hA
    · simpa using hd
    · simp

theorem WMaj.pow {s : ℝ} (hs : 0 ≤ s) {P p : List ℝ} (h : WMaj s P p) :
    ∀ n, WMaj s (rpowL P n) (rpowL p n)
  | 0 => WMaj.one
  | n + 1 => WMaj.rmul hs h (WMaj.pow hs h n)

theorem WMaj.foldr {s : ℝ} {α : Type*} (L : List α) (F f : α → List ℝ → List ℝ)
    (hF : ∀ a Acc acc, WMaj s Acc acc → WMaj s (F a Acc) (f a acc)) :
    WMaj s (L.foldr F []) (L.foldr f []) := by
  induction L with
  | nil => exact WMaj.nil s
  | cons a L ih => exact hF a _ _ ih

theorem WMaj_FL {s : ℝ} (hs : 0 ≤ s) {cb c : RT} (hc : ∀ i j k, |c i j k| ≤ cb i j k)
    {PU PV PW U V W : List ℝ} (hU : WMaj s PU U) (hV : WMaj s PV V) (hW : WMaj s PW W) :
    WMaj s (FL cb PU PV PW) (FL c U V W) := by
  unfold FL
  refine WMaj.foldr (List.finRange 9) _ _ (fun (i : Fin 9) Acc acc h => ?_)
  refine WMaj.radd (WMaj.rmul hs (hU.pow hs i) ?_) h
  refine WMaj.foldr (List.finRange 9) _ _ (fun (j : Fin 9) Acc' acc' h' => ?_)
  refine WMaj.radd (WMaj.rmul hs (hV.pow hs j) ?_) h'
  refine WMaj.foldr (List.finRange 9) _ _ (fun (k : Fin 9) Acc'' acc'' h'' => ?_)
  exact WMaj.radd (WMaj.rsmul (hc i j k) (hW.pow hs k)) h''

/-- The majorant of `1 − (a + x d)²/2`. -/
noncomputable def PuL (A : ℝ) : List ℝ := radd [1] (rsmul (1 / 2) (rmul [A, 1] [A, 1]))

theorem WMaj_uL {s A a d : ℝ} (hs : 0 ≤ s) (hA : |a| ≤ A) (hd : |d| ≤ s) :
    WMaj s (PuL A) (uL a d) := by
  have h := WMaj.lin hA hd
  exact WMaj.radd WMaj.one (WMaj.rsmul (by norm_num) (WMaj.rmul hs h h))

/-- **The majorant of the ray polynomial**: `|τ_i| ≤ A_i`, `|c_ijk| ≤ cb_ijk`, `|λ| ≤ Λ`. -/
noncomputable def PgL (cb : RT) (Λ A0 A1 A2 : ℝ) : List ℝ :=
  radd (rsmul Λ (radd (radd (rmul [A1, 1] [A2, 1]) (rmul [A0, 1] [A2, 1])) (rmul [A0, 1] [A1, 1])))
    (rsmul 1 (rmul (rmul (rmul [A0, 1] [A1, 1]) [A2, 1]) (FL cb (PuL A0) (PuL A1) (PuL A2))))

theorem WMaj_gL {p : Fin 24 → ℝ} {τ : ℝ × ℝ × ℝ} {δ : Fin 3 → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hδ : ∀ i, |δ i| ≤ s) {cb : RT} (hc : ∀ i j k, |cF (Mmat (Hp p)) i j k| ≤ cb i j k)
    {Λ A0 A1 A2 : ℝ} (hΛ : |lamFix| ≤ Λ) (h0 : |τ.1| ≤ A0) (h1 : |τ.2.1| ≤ A1)
    (h2 : |τ.2.2| ≤ A2) : WMaj s (PgL cb Λ A0 A1 A2) (gL p τ δ) := by
  have l0 := WMaj.lin h0 (hδ 0); have l1 := WMaj.lin h1 (hδ 1); have l2 := WMaj.lin h2 (hδ 2)
  unfold PgL gL
  exact WMaj.radd (WMaj.rsmul hΛ (WMaj.radd (WMaj.radd (WMaj.rmul hs l1 l2) (WMaj.rmul hs l0 l2))
      (WMaj.rmul hs l0 l1)))
    (WMaj.rsmul (by norm_num) (WMaj.rmul hs (WMaj.rmul hs (WMaj.rmul hs l0 l1) l2)
      (WMaj_FL hs hc (WMaj_uL hs h0 (hδ 0)) (WMaj_uL hs h1 (hδ 1)) (WMaj_uL hs h2 (hδ 2)))))

/-- **The fourth derivative along any ray from `τ`, uniformly**: for `|δ_i| ≤ s ≤ ρ` and
`0 ≤ x ≤ 1`, `|(d/dx)⁴ triP p (τ + xδ)| ≤ s⁴ · P⁗(ρ)`. -/
theorem abs_ray4_le {p : Fin 24 → ℝ} {τ : ℝ × ℝ × ℝ} {δ : Fin 3 → ℝ} {s ρ x : ℝ} (hs : 0 ≤ s)
    (hsρ : s ≤ ρ) (hδ : ∀ i, |δ i| ≤ s) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {cb : RT}
    (hc : ∀ i j k, |cF (Mmat (Hp p)) i j k| ≤ cb i j k) {Λ A0 A1 A2 : ℝ} (hΛ : |lamFix| ≤ Λ)
    (h0 : |τ.1| ≤ A0) (h1 : |τ.2.1| ≤ A1) (h2 : |τ.2.2| ≤ A2) :
    |deriv (deriv (deriv (deriv (rayR p τ δ)))) x|
      ≤ s ^ 4 * reval (rderN 4 (PgL cb Λ A0 A1 A2)) ρ := by
  rw [ray4]
  exact abs_rder4_le hs hsρ hx0 hx1 (WMaj_gL hs hδ hc hΛ h0 h1 h2)

/-! ### The majorant in interval arithmetic -/

/-- `Uⁿ`, full lists. -/
def lpowL (U : List Itv) : ℕ → List Itv
  | 0 => [Itv.one]
  | n + 1 => lmul U (lpowL U n)

/-- `FL` in interval arithmetic, full lists. -/
def LFL (CF : IT) (U V W : List Itv) : List Itv :=
  (List.finRange 9).foldr (fun (i : Fin 9) acc => ladd (lmul (lpowL U i)
    ((List.finRange 9).foldr (fun (j : Fin 9) acc' => ladd (lmul (lpowL V j)
      ((List.finRange 9).foldr (fun (k : Fin 9) acc'' =>
        ladd (lsmul (CF i j k) (lpowL W k)) acc'') [])) acc') [])) acc) []

theorem LMem.pow {U : List Itv} {u : List ℝ} (h : LMem U u) : ∀ n, LMem (lpowL U n) (rpowL u n)
  | 0 => LMem.cons Itv.mem_one LMem.nil
  | n + 1 => LMem_lmul h (LMem.pow h n)

theorem LMem.foldr {α : Type*} (L : List α) (F : α → List Itv → List Itv)
    (f : α → List ℝ → List ℝ) (hF : ∀ a Acc acc, LMem Acc acc → LMem (F a Acc) (f a acc)) :
    LMem (L.foldr F []) (L.foldr f []) := by
  induction L with
  | nil => exact LMem.nil
  | cons a L ih => exact hF a _ _ ih

theorem LMem_LFL {CF : IT} {c : RT} (hc : ITMem CF c) {U V W : List Itv} {u v w : List ℝ}
    (hU : LMem U u) (hV : LMem V v) (hW : LMem W w) : LMem (LFL CF U V W) (FL c u v w) := by
  unfold LFL FL
  refine LMem.foldr (List.finRange 9) _ _ (fun (i : Fin 9) Acc acc h => ?_)
  refine LMem_ladd (LMem_lmul (LMem.pow hU i) ?_) h
  refine LMem.foldr (List.finRange 9) _ _ (fun (j : Fin 9) Acc' acc' h' => ?_)
  refine LMem_ladd (LMem_lmul (LMem.pow hV j) ?_) h'
  refine LMem.foldr (List.finRange 9) _ _ (fun (k : Fin 9) Acc'' acc'' h'' => ?_)
  exact LMem_ladd (LMem_lsmul (hc i j k) (LMem.pow hW k)) h''

/-- The majorant `PgL` in interval arithmetic (all inputs are nonnegative upper bounds). -/
def IPgL (CB : IT) (Λ A0 A1 A2 : Itv) : List Itv :=
  let one := Itv.one
  let PU := fun A : Itv => ladd [one] (lsmul (Itv.ofDiv 1 2) (lmul [A, one] [A, one]))
  ladd (lsmul Λ (ladd (ladd (lmul [A1, one] [A2, one]) (lmul [A0, one] [A2, one]))
      (lmul [A0, one] [A1, one])))
    (lsmul one (lmul (lmul (lmul [A0, one] [A1, one]) [A2, one]) (LFL CB (PU A0) (PU A1) (PU A2))))

theorem LMem_IPgL {CB : IT} {cb : RT} (hc : ITMem CB cb) {Λi A0i A1i A2i : Itv}
    {Λ A0 A1 A2 : ℝ} (hΛ : Λi.Mem Λ) (h0 : A0i.Mem A0) (h1 : A1i.Mem A1) (h2 : A2i.Mem A2) :
    LMem (IPgL CB Λi A0i A1i A2i) (PgL cb Λ A0 A1 A2) := by
  have hh : (Itv.ofDiv 1 2).Mem (1 / 2) := by
    have := Itv.mem_ofDiv (n := 1) (d := 2) (by norm_num); norm_num at this ⊢; exact this
  have l : ∀ {Ai : Itv} {A : ℝ}, Ai.Mem A → LMem [Ai, Itv.one] [A, 1] :=
    fun h => LMem.cons h (LMem.cons Itv.mem_one LMem.nil)
  have pu : ∀ {Ai : Itv} {A : ℝ}, Ai.Mem A →
      LMem (ladd [Itv.one] (lsmul (Itv.ofDiv 1 2) (lmul [Ai, Itv.one] [Ai, Itv.one]))) (PuL A) :=
    fun h => LMem_ladd (LMem.cons Itv.mem_one LMem.nil) (LMem_lsmul hh (LMem_lmul (l h) (l h)))
  unfold IPgL PgL
  exact LMem_ladd (LMem_lsmul hΛ (LMem_ladd (LMem_ladd (LMem_lmul (l h1) (l h2))
      (LMem_lmul (l h0) (l h2))) (LMem_lmul (l h0) (l h1))))
    (LMem_lsmul Itv.mem_one (LMem_lmul (LMem_lmul (LMem_lmul (l h0) (l h1)) (l h2))
      (LMem_LFL hc (pu h0) (pu h1) (pu h2))))

/-! ## The shifted majorant

The monomial tensor of `F` has large alternating coefficients, so majorizing it directly loses all
cancellation (`M ≈ 10¹¹`).  Shifting it to a grid point `(a, b, c)` next to `(u₀, v₀, t₀)` first
(Task 5b's `shift`, `Ishift`) makes its coefficients the Taylor coefficients there, and the
majorant then tracks the true fourth derivative to within a factor `≲ 2`. -/

/-- `1 − (t + x d)²/2 − a`, with its (small) constant term kept exact. -/
noncomputable def uLs (t d a : ℝ) : List ℝ := [1 - t ^ 2 / 2 - a, -(t * d), -(d ^ 2 / 2)]

theorem reval_uLs (t d a x : ℝ) : reval (uLs t d a) x = 1 - (t + x * d) ^ 2 / 2 - a := by
  simp only [uLs, reval_cons, reval_nil]; ring

/-- The ray polynomial, through the shifted tensor. -/
noncomputable def gLs (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) (a b c : ℝ) : List ℝ :=
  radd (rsmul lamFix (radd (radd (rmul [τ.2.1, δ 1] [τ.2.2, δ 2]) (rmul [τ.1, δ 0] [τ.2.2, δ 2]))
      (rmul [τ.1, δ 0] [τ.2.1, δ 1])))
    (rsmul (-1) (rmul (rmul (rmul [τ.1, δ 0] [τ.2.1, δ 1]) [τ.2.2, δ 2])
      (FL (shift (cF (Mmat (Hp p))) a b c) (uLs τ.1 (δ 0) a) (uLs τ.2.1 (δ 1) b)
        (uLs τ.2.2 (δ 2) c))))

theorem rayR_eq_s (p : Fin 24 → ℝ) (τ : ℝ × ℝ × ℝ) (δ : Fin 3 → ℝ) (a b c : ℝ) :
    rayR p τ δ = reval (gLs p τ δ a b c) := by
  funext x
  simp only [rayR, gLs, reval_radd, reval_rsmul, reval_rmul, reval_FL, reval_uLs, reval_cons,
    reval_nil, ev_shift, add_sub_cancel, ev_cF_eq_Fh, triP]
  ring

theorem deriv_iter_of_eq {f : ℝ → ℝ} {L : List ℝ} (h : f = reval L) :
    ∀ k, deriv^[k] f = reval (rderN k L)
  | 0 => by simp [rderN, h]
  | k + 1 => by
      rw [Function.iterate_succ_apply', deriv_iter_of_eq h k, rderN]
      funext x
      exact (hasDerivAt_reval _ x).deriv

theorem WMaj_uLs {s t d a E A : ℝ} (hs : 0 ≤ s) (hE : |1 - t ^ 2 / 2 - a| ≤ E) (hA : |t| ≤ A)
    (hd : |d| ≤ s) : WMaj s [E, A, 1 / 2] (uLs t d a) := by
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hE
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hA
  refine ⟨fun n => ?_, fun n => ?_⟩
  · rcases n with _ | _ | _ | n <;> simp [hE0, hA0]
  · rcases n with _ | _ | _ | n
    · simpa [uLs] using hE
    · simp only [uLs, co_cons_succ, co_cons_zero, abs_neg, abs_mul, zero_add, pow_one]
      exact mul_le_mul hA hd (abs_nonneg _) hA0
    · simp only [uLs, co_cons_succ, co_cons_zero, abs_neg]
      rw [abs_div, abs_of_nonneg (sq_nonneg d), abs_two]
      have : d ^ 2 ≤ s ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
      linarith
    · simp [uLs]

/-- The majorant of the shifted ray polynomial. -/
noncomputable def PgLs (cb : RT) (Λ A0 A1 A2 E0 E1 E2 : ℝ) : List ℝ :=
  radd (rsmul Λ (radd (radd (rmul [A1, 1] [A2, 1]) (rmul [A0, 1] [A2, 1])) (rmul [A0, 1] [A1, 1])))
    (rsmul 1 (rmul (rmul (rmul [A0, 1] [A1, 1]) [A2, 1])
      (FL cb [E0, A0, 1 / 2] [E1, A1, 1 / 2] [E2, A2, 1 / 2])))

theorem WMaj_gLs {p : Fin 24 → ℝ} {τ : ℝ × ℝ × ℝ} {δ : Fin 3 → ℝ} {s a b c : ℝ} (hs : 0 ≤ s)
    (hδ : ∀ i, |δ i| ≤ s) {cb : RT}
    (hc : ∀ i j k, |shift (cF (Mmat (Hp p))) a b c i j k| ≤ cb i j k)
    {Λ A0 A1 A2 E0 E1 E2 : ℝ} (hΛ : |lamFix| ≤ Λ) (h0 : |τ.1| ≤ A0) (h1 : |τ.2.1| ≤ A1)
    (h2 : |τ.2.2| ≤ A2) (e0 : |1 - τ.1 ^ 2 / 2 - a| ≤ E0) (e1 : |1 - τ.2.1 ^ 2 / 2 - b| ≤ E1)
    (e2 : |1 - τ.2.2 ^ 2 / 2 - c| ≤ E2) :
    WMaj s (PgLs cb Λ A0 A1 A2 E0 E1 E2) (gLs p τ δ a b c) := by
  have l0 := WMaj.lin h0 (hδ 0); have l1 := WMaj.lin h1 (hδ 1); have l2 := WMaj.lin h2 (hδ 2)
  unfold PgLs gLs
  exact WMaj.radd (WMaj.rsmul hΛ (WMaj.radd (WMaj.radd (WMaj.rmul hs l1 l2) (WMaj.rmul hs l0 l2))
      (WMaj.rmul hs l0 l1)))
    (WMaj.rsmul (by norm_num) (WMaj.rmul hs (WMaj.rmul hs (WMaj.rmul hs l0 l1) l2)
      (WMaj_FL hs hc (WMaj_uLs hs e0 h0 (hδ 0)) (WMaj_uLs hs e1 h1 (hδ 1))
        (WMaj_uLs hs e2 h2 (hδ 2)))))

/-- **The fourth derivative along any ray, through the shifted majorant.** -/
theorem abs_ray4_le_s {p : Fin 24 → ℝ} {τ : ℝ × ℝ × ℝ} {δ : Fin 3 → ℝ} {s ρ x a b c : ℝ}
    (hs : 0 ≤ s) (hsρ : s ≤ ρ) (hδ : ∀ i, |δ i| ≤ s) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {cb : RT}
    (hc : ∀ i j k, |shift (cF (Mmat (Hp p))) a b c i j k| ≤ cb i j k)
    {Λ A0 A1 A2 E0 E1 E2 : ℝ} (hΛ : |lamFix| ≤ Λ) (h0 : |τ.1| ≤ A0) (h1 : |τ.2.1| ≤ A1)
    (h2 : |τ.2.2| ≤ A2) (e0 : |1 - τ.1 ^ 2 / 2 - a| ≤ E0) (e1 : |1 - τ.2.1 ^ 2 / 2 - b| ≤ E1)
    (e2 : |1 - τ.2.2 ^ 2 / 2 - c| ≤ E2) :
    |deriv (deriv (deriv (deriv (rayR p τ δ)))) x|
      ≤ s ^ 4 * reval (rderN 4 (PgLs cb Λ A0 A1 A2 E0 E1 E2)) ρ := by
  rw [show deriv (deriv (deriv (deriv (rayR p τ δ)))) = deriv^[4] (rayR p τ δ) from rfl,
    deriv_iter_of_eq (rayR_eq_s p τ δ a b c)]
  exact abs_rder4_le hs hsρ hx0 hx1 (WMaj_gLs hs hδ hc hΛ h0 h1 h2 e0 e1 e2)

/-- The shifted majorant in interval arithmetic. -/
def IPgLs (CB : IT) (Λ A0 A1 A2 E0 E1 E2 : Itv) : List Itv :=
  let one := Itv.one
  ladd (lsmul Λ (ladd (ladd (lmul [A1, one] [A2, one]) (lmul [A0, one] [A2, one]))
      (lmul [A0, one] [A1, one])))
    (lsmul one (lmul (lmul (lmul [A0, one] [A1, one]) [A2, one])
      (LFL CB [E0, A0, Itv.ofDiv 1 2] [E1, A1, Itv.ofDiv 1 2] [E2, A2, Itv.ofDiv 1 2])))

theorem LMem_IPgLs {CB : IT} {cb : RT} (hc : ITMem CB cb) {Λi A0i A1i A2i E0i E1i E2i : Itv}
    {Λ A0 A1 A2 E0 E1 E2 : ℝ} (hΛ : Λi.Mem Λ) (h0 : A0i.Mem A0) (h1 : A1i.Mem A1)
    (h2 : A2i.Mem A2) (g0 : E0i.Mem E0) (g1 : E1i.Mem E1) (g2 : E2i.Mem E2) :
    LMem (IPgLs CB Λi A0i A1i A2i E0i E1i E2i) (PgLs cb Λ A0 A1 A2 E0 E1 E2) := by
  have hh : (Itv.ofDiv 1 2).Mem (1 / 2) := by
    have := Itv.mem_ofDiv (n := 1) (d := 2) (by norm_num); norm_num at this ⊢; exact this
  have l : ∀ {Ai : Itv} {A : ℝ}, Ai.Mem A → LMem [Ai, Itv.one] [A, 1] :=
    fun h => LMem.cons h (LMem.cons Itv.mem_one LMem.nil)
  have pu : ∀ {Ai Ei : Itv} {A E : ℝ}, Ai.Mem A → Ei.Mem E →
      LMem [Ei, Ai, Itv.ofDiv 1 2] [E, A, 1 / 2] :=
    fun h g => LMem.cons g (LMem.cons h (LMem.cons hh LMem.nil))
  unfold IPgLs PgLs
  exact LMem_ladd (LMem_lsmul hΛ (LMem_ladd (LMem_ladd (LMem_lmul (l h1) (l h2))
      (LMem_lmul (l h0) (l h2))) (LMem_lmul (l h0) (l h1))))
    (LMem_lsmul Itv.mem_one (LMem_lmul (LMem_lmul (LMem_lmul (l h0) (l h1)) (l h2))
      (LMem_LFL hc (pu h0 g0) (pu h1 g1) (pu h2 g2))))

end Thomson.TriLocalCert
