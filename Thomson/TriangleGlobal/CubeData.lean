import Thomson.TriangleGlobal.Skip
import Thomson.TriangleGlobal.CertIntervals

/-! # Task 5b, step 16: the five local cubes — GENERATED

Fixed-point endpoints for the image of each cube `|chord − τ| ≤ 1/500` under `u ↦ √(2−2u)`,
taken strictly inside the true image, together with the enclosures of the four touching chords
that justify them (32 digits, from `uStar_mem_Icc_sharper` and `sqrt2_bounds_45`). -/

namespace Thomson.Tri5b

open Thomson

theorem chordA_bounds : (117124773819273446878596528850679 / 100000000000000000000000000000000 : ℝ) ≤ Real.sqrt 2 * rStar ∧ Real.sqrt 2 * rStar ≤ 117124773819273446878596528850683 / 100000000000000000000000000000000 := by
  have hu1 := uStar_lo
  have hu2 := uStar_hi
  obtain ⟨hs1, hs2⟩ := sqrt2_bounds_45
  have hr := rStar_pos
  have hsq : (Real.sqrt 2 * rStar) ^ 2 = 2 * (1 - uStar) := by rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), rStar_sq]
  have hpos : (0:ℝ) < Real.sqrt 2 * rStar := by positivity
  constructor <;> nlinarith [hsq, hpos, hu1, hu2, hs1, hs2, rStar_pos, s2Star_pos, s4Star_pos]

theorem chordD_bounds : (82819721812548859383093179555787 / 50000000000000000000000000000000 : ℝ) ≤ 2 * rStar ∧ 2 * rStar ≤ 82819721812548859383093179555789 / 50000000000000000000000000000000 := by
  have hu1 := uStar_lo
  have hu2 := uStar_hi
  obtain ⟨hs1, hs2⟩ := sqrt2_bounds_45
  have hr := rStar_pos
  have hsq : (2 * rStar) ^ 2 = 4 * (1 - uStar) := by rw [mul_pow, rStar_sq]; ring
  have hpos : (0:ℝ) < 2 * rStar := by positivity
  constructor <;> nlinarith [hsq, hpos, hu1, hu2, hs1, hs2, rStar_pos, s2Star_pos, s4Star_pos]

theorem chordN_bounds : (64384676307165870308709169478517 / 50000000000000000000000000000000 : ℝ) ≤ s2Star ∧ s2Star ≤ 128769352614331740617418338957039 / 100000000000000000000000000000000 := by
  have hu1 := uStar_lo
  have hu2 := uStar_hi
  obtain ⟨hs1, hs2⟩ := sqrt2_bounds_45
  have hr := rStar_pos
  have hsq : (s2Star) ^ 2 = 2 + 2 * uStar - Real.sqrt 2 * (1 - uStar) := by exact s2Star_sq
  have hpos : (0:ℝ) < s2Star := s2Star_pos
  constructor <;> nlinarith [hsq, hpos, hu1, hu2, hs1, hs2, rStar_pos, s2Star_pos, s4Star_pos]

theorem chordF_bounds : (94844647375133893231567951198239 / 50000000000000000000000000000000 : ℝ) ≤ s4Star ∧ s4Star ≤ 94844647375133893231567951198241 / 50000000000000000000000000000000 := by
  have hu1 := uStar_lo
  have hu2 := uStar_hi
  obtain ⟨hs1, hs2⟩ := sqrt2_bounds_45
  have hr := rStar_pos
  have hsq : (s4Star) ^ 2 = 2 + 2 * uStar + Real.sqrt 2 * (1 - uStar) := by exact s4Star_sq
  have hpos : (0:ℝ) < s4Star := s4Star_pos
  constructor <;> nlinarith [hsq, hpos, hu1, hu2, hs1, hs2, rStar_pos, s2Star_pos, s4Star_pos]

theorem cube_A {u : ℝ} (h1 : ((3117448724128163984436613313837871208033 : ℤ) : ℝ) ≤ u * SCALE) (h2 : u * SCALE ≤ ((3164298633655873363188051925377675108937 : ℤ) : ℝ)) :
    |Real.sqrt (2 - 2 * u) - (Real.sqrt 2 * rStar)| ≤ 1 / 500 := by
  obtain ⟨c1, c2⟩ := chordA_bounds
  have hS : (0:ℝ) < (SCALE : ℝ) := SCALE_pos'
  have hSv : ((SCALE : ℤ) : ℝ) = 10 ^ 40 := by unfold SCALE; push_cast; ring
  rw [hSv] at h1 h2
  push_cast at h1 h2
  refine in_cube_of_u (by norm_num) (by nlinarith) ?_ ?_
  · nlinarith
  · nlinarith

theorem cube_D {u : ℝ} (h1 : ((-3751360530940982196128572032606513950176 : ℤ) : ℝ) ≤ u * SCALE) (h2 : u * SCALE ≤ ((-3685104753490943108622097488962546107951 : ℤ) : ℝ)) :
    |Real.sqrt (2 - 2 * u) - (2 * rStar)| ≤ 1 / 500 := by
  obtain ⟨c1, c2⟩ := chordD_bounds
  have hS : (0:ℝ) < (SCALE : ℝ) := SCALE_pos'
  have hSv : ((SCALE : ℤ) : ℝ) = 10 ^ 40 := by unfold SCALE; push_cast; ring
  rw [hSv] at h1 h2
  push_cast at h1 h2
  refine in_cube_of_u (by norm_num) (by nlinarith) ?_ ?_
  · nlinarith
  · nlinarith

theorem cube_N {u : ℝ} (h1 : ((1683453043120081310837733146781486508045 : ℤ) : ℝ) ≤ u * SCALE) (h2 : u * SCALE ≤ ((1734960784165814007084700482363657261281 : ℤ) : ℝ)) :
    |Real.sqrt (2 - 2 * u) - (s2Star)| ≤ 1 / 500 := by
  obtain ⟨c1, c2⟩ := chordN_bounds
  have hS : (0:ℝ) < (SCALE : ℝ) := SCALE_pos'
  have hSv : ((SCALE : ℤ) : ℝ) = 10 ^ 40 := by unfold SCALE; push_cast; ring
  rw [hSv] at h1 h2
  push_cast at h1 h2
  refine in_cube_of_u (by norm_num) (by nlinarith) ?_ ?_
  · nlinarith
  · nlinarith

theorem cube_F {u : ℝ} (h1 : ((-8028972130377038563878509234266961721897 : ℤ) : ℝ) ≤ u * SCALE) (h2 : u * SCALE ≤ ((-7953096412476931449293254873309128479077 : ℤ) : ℝ)) :
    |Real.sqrt (2 - 2 * u) - (s4Star)| ≤ 1 / 500 := by
  obtain ⟨c1, c2⟩ := chordF_bounds
  have hS : (0:ℝ) < (SCALE : ℝ) := SCALE_pos'
  have hSv : ((SCALE : ℤ) : ℝ) = 10 ^ 40 := by unfold SCALE; push_cast; ring
  rw [hSv] at h1 h2
  push_cast at h1 h2
  refine in_cube_of_u (by norm_num) (by nlinarith) ?_ ?_
  · nlinarith
  · nlinarith

/-- The endpoints, as matches on `ℕ`: the checker reads them at every node, and a `![…]` read
costs the interpreter `≈10⁻¹` s (see `Thomson.Tri5b.pivQn`). -/
def cubeLoN : ℕ → ℕ → ℤ
  | 0, 0 => -8028972130377038563878509234266961721897
  | 0, 1 => -8028972130377038563878509234266961721897
  | 0, 2 => 3117448724128163984436613313837871208033
  | 1, 0 => -8028972130377038563878509234266961721897
  | 1, 1 => -3751360530940982196128572032606513950176
  | 1, 2 => 1683453043120081310837733146781486508045
  | 2, 0 => -8028972130377038563878509234266961721897
  | 2, 1 => 1683453043120081310837733146781486508045
  | 2, 2 => 3117448724128163984436613313837871208033
  | 3, 0 => -3751360530940982196128572032606513950176
  | 3, 1 => 3117448724128163984436613313837871208033
  | 3, 2 => 3117448724128163984436613313837871208033
  | 4, 0 => 1683453043120081310837733146781486508045
  | 4, 1 => 1683453043120081310837733146781486508045
  | 4, 2 => 3117448724128163984436613313837871208033
  | _, _ => 0

def cubeHiN : ℕ → ℕ → ℤ
  | 0, 0 => -7953096412476931449293254873309128479077
  | 0, 1 => -7953096412476931449293254873309128479077
  | 0, 2 => 3164298633655873363188051925377675108937
  | 1, 0 => -7953096412476931449293254873309128479077
  | 1, 1 => -3685104753490943108622097488962546107951
  | 1, 2 => 1734960784165814007084700482363657261281
  | 2, 0 => -7953096412476931449293254873309128479077
  | 2, 1 => 1734960784165814007084700482363657261281
  | 2, 2 => 3164298633655873363188051925377675108937
  | 3, 0 => -3685104753490943108622097488962546107951
  | 3, 1 => 3164298633655873363188051925377675108937
  | 3, 2 => 3164298633655873363188051925377675108937
  | 4, 0 => 1734960784165814007084700482363657261281
  | 4, 1 => 1734960784165814007084700482363657261281
  | 4, 2 => 3164298633655873363188051925377675108937
  | _, _ => 0

/-- The fixed-point images of the five cubes. -/
def cubeD : CubeData where
  lo := fun m i => cubeLoN (m : ℕ) (i : ℕ)
  hi := fun m i => cubeHiN (m : ℕ) (i : ℕ)

theorem cubeSound : CubeSound cubeD (fun _ => 1 / 500) := by
  intro m i u h1 h2
  fin_cases m <;> fin_cases i
  · exact cube_F h1 h2
  · exact cube_F h1 h2
  · exact cube_A h1 h2
  · exact cube_F h1 h2
  · exact cube_D h1 h2
  · exact cube_N h1 h2
  · exact cube_F h1 h2
  · exact cube_N h1 h2
  · exact cube_A h1 h2
  · exact cube_D h1 h2
  · exact cube_A h1 h2
  · exact cube_A h1 h2
  · exact cube_N h1 h2
  · exact cube_N h1 h2
  · exact cube_A h1 h2

end Thomson.Tri5b
