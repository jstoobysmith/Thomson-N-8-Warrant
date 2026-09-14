import Thomson.TriangleGlobal.Bridge

/-! # Task 1b, step 1: evaluating a coefficient tensor at enclosed points

Task 5b evaluates tensors on *boxes*, through a Taylor model.  Task 1b needs something much
simpler: the value of a tensor at a single point, known only to lie in a small interval — the
points are the chords `√2 r*, 2r*, s₂*, s₄*`, and the entries of the pivot system are the values of
the tensors of `Gh j` there.  `evI` is the interval evaluation, and `dU/dV/dT` the partial
derivatives, which the derivative rows of the system need. -/

namespace Thomson.Task1b

open Thomson Thomson.Tri5b

/-- Interval evaluation of a tensor at enclosed points. -/
def evI (C : IT) (U V T : Itv) : Itv :=
  Itv.sumL ((List.finRange 9).map (fun i : Fin 9 =>
    Itv.sumL ((List.finRange 9).map (fun q : Fin 9 =>
      Itv.sumL ((List.finRange 9).map (fun r : Fin 9 =>
        Itv.mul (C i q r)
          (Itv.mul (Itv.mul (Itv.npow U (i : ℕ)) (Itv.npow V (q : ℕ))) (Itv.npow T (r : ℕ)))))))))

theorem mem_evI {C : IT} {c : RT} (hC : ITMem C c) {U V T : Itv} {u v t : ℝ}
    (hu : U.Mem u) (hv : V.Mem v) (ht : T.Mem t) : (evI C U V T).Mem (ev c u v t) := by
  unfold evI ev
  refine Itv.mem_sum_fin _ _ fun i => ?_
  refine Itv.mem_sum_fin _ _ fun q => ?_
  refine Itv.mem_sum_fin _ _ fun r => ?_
  exact Itv.mem_mul (hC i q r)
    (Itv.mem_mul (Itv.mem_mul (Itv.mem_npow hu _) (Itv.mem_npow hv _)) (Itv.mem_npow ht _))

/-! ### The partial derivatives

`ev c` is a polynomial, so its partial derivatives are the same sum with one exponent lowered.  The
index `i - 1` is truncated subtraction, which is harmless: at `i = 0` the factor `(i : ℝ)` kills the
term. -/

/-- `∂₁ (ev c)`, as a sum in the same shape as `ev`. -/
noncomputable def evD1 (c : RT) (u v t : ℝ) : ℝ :=
  ∑ i : Fin 9, ∑ q : Fin 9, ∑ r : Fin 9,
    c i q r * (((i : ℕ) : ℝ) * u ^ ((i : ℕ) - 1) * v ^ (q : ℕ) * t ^ (r : ℕ))

/-- `∂₂ (ev c)`. -/
noncomputable def evD2 (c : RT) (u v t : ℝ) : ℝ :=
  ∑ i : Fin 9, ∑ q : Fin 9, ∑ r : Fin 9,
    c i q r * (u ^ (i : ℕ) * (((q : ℕ) : ℝ) * v ^ ((q : ℕ) - 1)) * t ^ (r : ℕ))

/-- `∂₃ (ev c)`. -/
noncomputable def evD3 (c : RT) (u v t : ℝ) : ℝ :=
  ∑ i : Fin 9, ∑ q : Fin 9, ∑ r : Fin 9,
    c i q r * (u ^ (i : ℕ) * v ^ (q : ℕ) * (((r : ℕ) : ℝ) * t ^ ((r : ℕ) - 1)))

theorem hasDerivAt_evD1 (c : RT) (u v t : ℝ) :
    HasDerivAt (fun x => ev c x v t) (evD1 c u v t) u := by
  unfold ev evD1
  refine HasDerivAt.fun_sum fun i _ => ?_
  refine HasDerivAt.fun_sum fun q _ => ?_
  refine HasDerivAt.fun_sum fun r _ => ?_
  have h1 : HasDerivAt (fun x : ℝ => x ^ (i : ℕ)) (((i : ℕ) : ℝ) * u ^ ((i : ℕ) - 1)) u :=
    hasDerivAt_pow _ _
  have h2 := (h1.mul_const (v ^ (q : ℕ))).mul_const (t ^ (r : ℕ))
  have h3 := h2.const_mul (c i q r)
  convert h3 using 1
  try ring

theorem hasDerivAt_evD2 (c : RT) (u v t : ℝ) :
    HasDerivAt (fun y => ev c u y t) (evD2 c u v t) v := by
  unfold ev evD2
  refine HasDerivAt.fun_sum fun i _ => ?_
  refine HasDerivAt.fun_sum fun q _ => ?_
  refine HasDerivAt.fun_sum fun r _ => ?_
  have h1 : HasDerivAt (fun y : ℝ => y ^ (q : ℕ)) (((q : ℕ) : ℝ) * v ^ ((q : ℕ) - 1)) v :=
    hasDerivAt_pow _ _
  have h2 := ((h1.const_mul (u ^ (i : ℕ))).mul_const (t ^ (r : ℕ))).const_mul (c i q r)
  convert h2 using 1
  try ring

theorem hasDerivAt_evD3 (c : RT) (u v t : ℝ) :
    HasDerivAt (fun z => ev c u v z) (evD3 c u v t) t := by
  unfold ev evD3
  refine HasDerivAt.fun_sum fun i _ => ?_
  refine HasDerivAt.fun_sum fun q _ => ?_
  refine HasDerivAt.fun_sum fun r _ => ?_
  have h1 : HasDerivAt (fun z : ℝ => z ^ (r : ℕ)) (((r : ℕ) : ℝ) * t ^ ((r : ℕ) - 1)) t :=
    hasDerivAt_pow _ _
  have h2 := (h1.const_mul (u ^ (i : ℕ) * v ^ (q : ℕ))).const_mul (c i q r)
  convert h2 using 1
  try ring

/-! ### and their interval versions -/

/-- The integer `n`, as an exact interval. -/
def natI (n : ℕ) : Itv := Itv.cst ((n : ℤ) * SCALE)

theorem mem_natI (n : ℕ) : (natI n).Mem ((n : ℕ) : ℝ) := by
  have h := Itv.mem_cst ((n : ℤ) * SCALE)
  rwa [Int.cast_mul, mul_div_assoc, div_self (ne_of_gt SCALE_pos'), mul_one, Int.cast_natCast] at h

def evID1 (C : IT) (U V T : Itv) : Itv :=
  Itv.sumL ((List.finRange 9).map (fun i : Fin 9 =>
    Itv.sumL ((List.finRange 9).map (fun q : Fin 9 =>
      Itv.sumL ((List.finRange 9).map (fun r : Fin 9 =>
        Itv.mul (C i q r)
          (Itv.mul (Itv.mul (Itv.mul (natI (i : ℕ)) (Itv.npow U ((i : ℕ) - 1)))
            (Itv.npow V (q : ℕ))) (Itv.npow T (r : ℕ)))))))))

def evID2 (C : IT) (U V T : Itv) : Itv :=
  Itv.sumL ((List.finRange 9).map (fun i : Fin 9 =>
    Itv.sumL ((List.finRange 9).map (fun q : Fin 9 =>
      Itv.sumL ((List.finRange 9).map (fun r : Fin 9 =>
        Itv.mul (C i q r)
          (Itv.mul (Itv.mul (Itv.npow U (i : ℕ))
            (Itv.mul (natI (q : ℕ)) (Itv.npow V ((q : ℕ) - 1)))) (Itv.npow T (r : ℕ)))))))))

def evID3 (C : IT) (U V T : Itv) : Itv :=
  Itv.sumL ((List.finRange 9).map (fun i : Fin 9 =>
    Itv.sumL ((List.finRange 9).map (fun q : Fin 9 =>
      Itv.sumL ((List.finRange 9).map (fun r : Fin 9 =>
        Itv.mul (C i q r)
          (Itv.mul (Itv.mul (Itv.npow U (i : ℕ)) (Itv.npow V (q : ℕ)))
            (Itv.mul (natI (r : ℕ)) (Itv.npow T ((r : ℕ) - 1))))))))))

theorem mem_evID1 {C : IT} {c : RT} (hC : ITMem C c) {U V T : Itv} {u v t : ℝ}
    (hu : U.Mem u) (hv : V.Mem v) (ht : T.Mem t) : (evID1 C U V T).Mem (evD1 c u v t) := by
  unfold evID1 evD1
  refine Itv.mem_sum_fin _ _ fun i => Itv.mem_sum_fin _ _ fun q => Itv.mem_sum_fin _ _ fun r => ?_
  exact Itv.mem_mul (hC i q r)
    (Itv.mem_mul (Itv.mem_mul (Itv.mem_mul (mem_natI _) (Itv.mem_npow hu _)) (Itv.mem_npow hv _))
      (Itv.mem_npow ht _))

theorem mem_evID2 {C : IT} {c : RT} (hC : ITMem C c) {U V T : Itv} {u v t : ℝ}
    (hu : U.Mem u) (hv : V.Mem v) (ht : T.Mem t) : (evID2 C U V T).Mem (evD2 c u v t) := by
  unfold evID2 evD2
  refine Itv.mem_sum_fin _ _ fun i => Itv.mem_sum_fin _ _ fun q => Itv.mem_sum_fin _ _ fun r => ?_
  exact Itv.mem_mul (hC i q r)
    (Itv.mem_mul (Itv.mem_mul (Itv.mem_npow hu _) (Itv.mem_mul (mem_natI _) (Itv.mem_npow hv _)))
      (Itv.mem_npow ht _))

theorem mem_evID3 {C : IT} {c : RT} (hC : ITMem C c) {U V T : Itv} {u v t : ℝ}
    (hu : U.Mem u) (hv : V.Mem v) (ht : T.Mem t) : (evID3 C U V T).Mem (evD3 c u v t) := by
  unfold evID3 evD3
  refine Itv.mem_sum_fin _ _ fun i => Itv.mem_sum_fin _ _ fun q => Itv.mem_sum_fin _ _ fun r => ?_
  exact Itv.mem_mul (hC i q r)
    (Itv.mem_mul (Itv.mem_mul (Itv.mem_npow hu _) (Itv.mem_npow hv _))
      (Itv.mem_mul (mem_natI _) (Itv.mem_npow ht _)))

end Thomson.Task1b
