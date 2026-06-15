import Homogenization.Deterministic.ConstantCoefficientDirichletBesov.OverlapPoincare

namespace Homogenization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Pointwise

/-- The value of one competitor in the discrete cube vector K-functional. -/
noncomputable def cubeVectorKFunctionalCompetitorValue {d : ℕ}
    (Q : TriadicCube d) (t : ℝ) (F : Vec d → Vec d)
    (G : CubeVectorH1Function Q) : ℝ :=
  Real.sqrt
    ((cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x => F x - G.toField x)) ^ 2 +
      t ^ 2 * (G.relativeGradientCoordL2NormSum) ^ 2)

/-- Discrete cube K-functional for vector fields, with `t` as the smoothing
scale. -/
noncomputable def cubeVectorKFunctional {d : ℕ}
    (Q : TriadicCube d) (t : ℝ) (F : Vec d → Vec d) : ℝ :=
  sInf (Set.range fun G : CubeVectorH1Function Q =>
    cubeVectorKFunctionalCompetitorValue Q t F G)

theorem cubeVectorKFunctionalCompetitorValue_nonneg {d : ℕ}
    (Q : TriadicCube d) (t : ℝ) (F : Vec d → Vec d)
    (G : CubeVectorH1Function Q) :
    0 ≤ cubeVectorKFunctionalCompetitorValue Q t F G :=
  Real.sqrt_nonneg _

theorem sqrt_cubeBesovOverlappingPositiveVectorDepthAverage_le_mul_cubeVectorKFunctionalCompetitorValue_of_overlapPoincare
    {d : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hPoincare : CubeVectorH1OverlapPoincareEstimate d C)
    (Q : TriadicCube d) (F : Vec d → Vec d) (j : ℕ)
    (G : CubeVectorH1Function Q)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q F j) ≤
      (8 * (3 ^ d : ℝ) + 2 * C ^ 2 + 1) *
        cubeVectorKFunctionalCompetitorValue Q
          (Real.rpow (3 : ℝ) (-(j : ℝ))) F G := by
  let R : Vec d → Vec d := fun x => F x - G.toField x
  let t : ℝ := Real.rpow (3 : ℝ) (-(j : ℝ))
  let A : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) R
  let B : ℝ := G.relativeGradientCoordL2NormSum
  let M : ℝ := 8 * (3 ^ d : ℝ) + 2 * C ^ 2
  let K : ℝ := M + 1
  have hGparent :
      MeasureTheory.MemLp G.toField (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    G.memLp_toField_normalizedCubeMeasure
  have hRparent :
      MeasureTheory.MemLp R (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa [R] using hF.sub hGparent
  have hRloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp R (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S) := by
    intro S hS
    exact memLp_normalizedOverlapCubeMeasure_of_memLp_normalizedCubeMeasure hS hRparent
  have hGloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp G.toField (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S) := by
    intro S hS
    exact memLp_normalizedOverlapCubeMeasure_of_memLp_normalizedCubeMeasure hS hGparent
  have hF_split :
      cubeBesovOverlappingPositiveVectorDepthAverage Q F j =
        cubeBesovOverlappingPositiveVectorDepthAverage
          Q (fun x => R x + G.toField x) j := by
    have hfield : (fun x => R x + G.toField x) = F := by
      funext x i
      simp [R]
    rw [hfield]
  have hsplit :
      cubeBesovOverlappingPositiveVectorDepthAverage Q F j ≤
        2 * cubeBesovOverlappingPositiveVectorDepthAverage Q R j +
          2 * cubeBesovOverlappingPositiveVectorDepthAverage Q G.toField j := by
    rw [hF_split]
    exact cubeBesovOverlappingPositiveVectorDepthAverage_add_le Q R G.toField j
      hRloc hGloc
  have hres :
      cubeBesovOverlappingPositiveVectorDepthAverage Q R j ≤
        4 * (3 ^ d : ℝ) * A ^ 2 := by
    simpa [A, R] using
      cubeBesovOverlappingPositiveVectorDepthAverage_residual_le
        Q R j hRparent hRloc
  have hcomp :
      cubeBesovOverlappingPositiveVectorDepthAverage Q G.toField j ≤
        (C * t * B) ^ 2 := by
    simpa [t, B] using
      cubeBesovOverlappingPositiveVectorDepthAverage_toField_le_of_overlapPoincare
        hC hPoincare Q j G
  have hdepth_coeff :
      cubeBesovOverlappingPositiveVectorDepthAverage Q F j ≤
        8 * (3 ^ d : ℝ) * A ^ 2 + 2 * (C * t * B) ^ 2 := by
    calc
      cubeBesovOverlappingPositiveVectorDepthAverage Q F j
          ≤
            2 * cubeBesovOverlappingPositiveVectorDepthAverage Q R j +
              2 * cubeBesovOverlappingPositiveVectorDepthAverage Q G.toField j :=
            hsplit
      _ ≤ 2 * (4 * (3 ^ d : ℝ) * A ^ 2) + 2 * ((C * t * B) ^ 2) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hres (by norm_num))
              (mul_le_mul_of_nonneg_left hcomp (by norm_num))
      _ = 8 * (3 ^ d : ℝ) * A ^ 2 + 2 * (C * t * B) ^ 2 := by
            ring
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact cubeLpNorm_nonneg Q (2 : ℝ≥0∞) R
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact G.relativeGradientCoordL2NormSum_nonneg
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    linarith
  have hK_sq :
      M ≤ K ^ 2 := by
    have hK_eq : K = M + 1 := by rfl
    rw [hK_eq]
    nlinarith [sq_nonneg M, hM_nonneg]
  have hdepth_M :
      cubeBesovOverlappingPositiveVectorDepthAverage Q F j ≤
        M * (A ^ 2 + t ^ 2 * B ^ 2) := by
    have hcoefA : 8 * (3 ^ d : ℝ) ≤ M := by
      dsimp [M]
      nlinarith [sq_nonneg C]
    have hcoefB : 2 * C ^ 2 ≤ M := by
      dsimp [M]
      have hpow_nonneg : 0 ≤ (3 ^ d : ℝ) := by positivity
      nlinarith
    calc
      cubeBesovOverlappingPositiveVectorDepthAverage Q F j
          ≤ 8 * (3 ^ d : ℝ) * A ^ 2 + 2 * (C * t * B) ^ 2 :=
            hdepth_coeff
      _ =
          (8 * (3 ^ d : ℝ)) * A ^ 2 +
            (2 * C ^ 2) * (t ^ 2 * B ^ 2) := by
            ring
      _ ≤ M * A ^ 2 + M * (t ^ 2 * B ^ 2) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_right hcoefA (sq_nonneg A))
              (mul_le_mul_of_nonneg_right hcoefB
                (mul_nonneg (sq_nonneg t) (sq_nonneg B)))
      _ = M * (A ^ 2 + t ^ 2 * B ^ 2) := by
            ring
  have hY_nonneg : 0 ≤ A ^ 2 + t ^ 2 * B ^ 2 := by
    exact add_nonneg (sq_nonneg A)
      (mul_nonneg (sq_nonneg t) (sq_nonneg B))
  have hdepth_K :
      cubeBesovOverlappingPositiveVectorDepthAverage Q F j ≤
        K ^ 2 * (A ^ 2 + t ^ 2 * B ^ 2) := by
    exact hdepth_M.trans
      (mul_le_mul_of_nonneg_right hK_sq hY_nonneg)
  calc
    Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q F j)
        ≤ Real.sqrt (K ^ 2 * (A ^ 2 + t ^ 2 * B ^ 2)) :=
          Real.sqrt_le_sqrt hdepth_K
    _ = Real.sqrt (K ^ 2) * Real.sqrt (A ^ 2 + t ^ 2 * B ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg K)]
    _ = K * Real.sqrt (A ^ 2 + t ^ 2 * B ^ 2) := by
          rw [Real.sqrt_sq hK_nonneg]
    _ =
        (8 * (3 ^ d : ℝ) + 2 * C ^ 2 + 1) *
          cubeVectorKFunctionalCompetitorValue Q
            (Real.rpow (3 : ℝ) (-(j : ℝ))) F G := by
          dsimp [cubeVectorKFunctionalCompetitorValue, A, B, K, M, t, R]

theorem cubeVectorKFunctional_range_nonempty {d : ℕ}
    (Q : TriadicCube d) (t : ℝ) (F : Vec d → Vec d) :
    (Set.range fun G : CubeVectorH1Function Q =>
      cubeVectorKFunctionalCompetitorValue Q t F G).Nonempty :=
  ⟨cubeVectorKFunctionalCompetitorValue Q t F default, ⟨default, rfl⟩⟩

theorem cubeVectorKFunctional_range_bddBelow {d : ℕ}
    (Q : TriadicCube d) (t : ℝ) (F : Vec d → Vec d) :
    BddBelow (Set.range fun G : CubeVectorH1Function Q =>
      cubeVectorKFunctionalCompetitorValue Q t F G) := by
  refine ⟨0, ?_⟩
  rintro y ⟨G, rfl⟩
  exact cubeVectorKFunctionalCompetitorValue_nonneg Q t F G

theorem cubeVectorKFunctional_nonneg {d : ℕ}
    (Q : TriadicCube d) (t : ℝ) (F : Vec d → Vec d) :
    0 ≤ cubeVectorKFunctional Q t F := by
  unfold cubeVectorKFunctional
  exact le_csInf (cubeVectorKFunctional_range_nonempty Q t F) fun y hy => by
    rcases hy with ⟨G, rfl⟩
    exact cubeVectorKFunctionalCompetitorValue_nonneg Q t F G

theorem cubeVectorKFunctional_le_competitor {d : ℕ}
    (Q : TriadicCube d) (t : ℝ) (F : Vec d → Vec d)
    (G : CubeVectorH1Function Q) :
    cubeVectorKFunctional Q t F ≤
      cubeVectorKFunctionalCompetitorValue Q t F G := by
  unfold cubeVectorKFunctional
  exact csInf_le (cubeVectorKFunctional_range_bddBelow Q t F) ⟨G, rfl⟩

theorem cubeVectorKFunctionalCompetitorValue_le_of_endpoint_bounds {d : ℕ}
    (Q : TriadicCube d) (t C : ℝ) (F H : Vec d → Vec d)
    (V G : CubeVectorH1Function Q) (hC : 0 ≤ C)
    (hL2 :
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => F x - V.toField x) ≤
        C * cubeLpNorm Q (2 : ℝ≥0∞) (fun x => H x - G.toField x))
    (hGrad :
      V.gradientCoordL2NormSum ≤ C * G.gradientCoordL2NormSum) :
    cubeVectorKFunctionalCompetitorValue Q t F V ≤
      C * cubeVectorKFunctionalCompetitorValue Q t H G := by
  let Aout : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) (fun x => F x - V.toField x)
  let Ain : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) (fun x => H x - G.toField x)
  let Bout : ℝ := V.relativeGradientCoordL2NormSum
  let Bin : ℝ := G.relativeGradientCoordL2NormSum
  have hAout_nonneg : 0 ≤ Aout := by
    dsimp [Aout]
    exact cubeLpNorm_nonneg Q (2 : ℝ≥0∞) (fun x => F x - V.toField x)
  have hAin_nonneg : 0 ≤ Ain := by
    dsimp [Ain]
    exact cubeLpNorm_nonneg Q (2 : ℝ≥0∞) (fun x => H x - G.toField x)
  have hBout_nonneg : 0 ≤ Bout := by
    dsimp [Bout]
    exact V.relativeGradientCoordL2NormSum_nonneg
  have hBin_nonneg : 0 ≤ Bin := by
    dsimp [Bin]
    exact G.relativeGradientCoordL2NormSum_nonneg
  have hCAin_nonneg : 0 ≤ C * Ain := mul_nonneg hC hAin_nonneg
  have hCBin_nonneg : 0 ≤ C * Bin := mul_nonneg hC hBin_nonneg
  have hA_sq : Aout ^ 2 ≤ C ^ 2 * Ain ^ 2 := by
    have hsq : Aout ^ 2 ≤ (C * Ain) ^ 2 :=
      (sq_le_sq₀ hAout_nonneg hCAin_nonneg).mpr (by
        simpa [Aout, Ain] using hL2)
    calc
      Aout ^ 2 ≤ (C * Ain) ^ 2 := hsq
      _ = C ^ 2 * Ain ^ 2 := by ring
  have hB_sq : Bout ^ 2 ≤ C ^ 2 * Bin ^ 2 := by
    have hGradRel :
        V.relativeGradientCoordL2NormSum ≤
          C * G.relativeGradientCoordL2NormSum :=
      CubeVectorH1Function.relativeGradientCoordL2NormSum_le_mul_of_gradientCoordL2NormSum_le
        hGrad
    have hsq : Bout ^ 2 ≤ (C * Bin) ^ 2 :=
      (sq_le_sq₀ hBout_nonneg hCBin_nonneg).mpr (by
        simpa [Bout, Bin] using hGradRel)
    calc
      Bout ^ 2 ≤ (C * Bin) ^ 2 := hsq
      _ = C ^ 2 * Bin ^ 2 := by ring
  have ht_sq_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
  have hsum :
      Aout ^ 2 + t ^ 2 * Bout ^ 2 ≤
        C ^ 2 * (Ain ^ 2 + t ^ 2 * Bin ^ 2) := by
    calc
      Aout ^ 2 + t ^ 2 * Bout ^ 2
          ≤ C ^ 2 * Ain ^ 2 + t ^ 2 * (C ^ 2 * Bin ^ 2) := by
            exact add_le_add hA_sq (mul_le_mul_of_nonneg_left hB_sq ht_sq_nonneg)
      _ = C ^ 2 * (Ain ^ 2 + t ^ 2 * Bin ^ 2) := by
            ring
  calc
    cubeVectorKFunctionalCompetitorValue Q t F V
        = Real.sqrt (Aout ^ 2 + t ^ 2 * Bout ^ 2) := by
          rfl
    _ ≤ Real.sqrt (C ^ 2 * (Ain ^ 2 + t ^ 2 * Bin ^ 2)) :=
          Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (C ^ 2) * Real.sqrt (Ain ^ 2 + t ^ 2 * Bin ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg C)]
    _ = C * Real.sqrt (Ain ^ 2 + t ^ 2 * Bin ^ 2) := by
          rw [Real.sqrt_sq hC]
    _ = C * cubeVectorKFunctionalCompetitorValue Q t H G := by
          rfl

theorem cubeVectorKFunctional_le_of_forall_competitorValue_le {d : ℕ}
    (Q : TriadicCube d) (t C : ℝ) (F H : Vec d → Vec d)
    (hC : 0 ≤ C)
    (hcomp :
      ∀ G : CubeVectorH1Function Q,
        ∃ V : CubeVectorH1Function Q,
          cubeVectorKFunctionalCompetitorValue Q t F V ≤
            C * cubeVectorKFunctionalCompetitorValue Q t H G) :
    cubeVectorKFunctional Q t F ≤ C * cubeVectorKFunctional Q t H := by
  by_cases hC_zero : C = 0
  · rcases hcomp default with ⟨V, hV⟩
    have hout_le_zero :
        cubeVectorKFunctional Q t F ≤ 0 := by
      calc
        cubeVectorKFunctional Q t F
            ≤ cubeVectorKFunctionalCompetitorValue Q t F V :=
              cubeVectorKFunctional_le_competitor Q t F V
        _ ≤ 0 := by simpa [hC_zero] using hV
    simpa [hC_zero] using hout_le_zero
  · have hC_pos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC_zero)
    have hdiv_le :
        cubeVectorKFunctional Q t F / C ≤ cubeVectorKFunctional Q t H := by
      unfold cubeVectorKFunctional
      refine le_csInf (cubeVectorKFunctional_range_nonempty Q t H) ?_
      rintro y ⟨G, rfl⟩
      rcases hcomp G with ⟨V, hV⟩
      have hout_le :
          sInf (Set.range fun W : CubeVectorH1Function Q =>
              cubeVectorKFunctionalCompetitorValue Q t F W) ≤
            C * cubeVectorKFunctionalCompetitorValue Q t H G :=
        (csInf_le (cubeVectorKFunctional_range_bddBelow Q t F) ⟨V, rfl⟩).trans hV
      exact (div_le_iff₀ hC_pos).2 (by simpa [mul_comm] using hout_le)
    exact (div_le_iff₀ hC_pos).1 hdiv_le |>.trans_eq (by ring)

/-- Depth-`j` K-functional contribution to the positive `q = 2` scale. -/
noncomputable def cubeKBesovVectorDepthSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (j : ℕ) : ℝ :=
  Real.rpow (3 : ℝ) (s * (j : ℝ)) *
    cubeVectorKFunctional Q (Real.rpow (3 : ℝ) (-(j : ℝ))) F

theorem cubeKBesovVectorDepthSeminorm_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (j : ℕ) :
    0 ≤ cubeKBesovVectorDepthSeminorm Q s F j := by
  unfold cubeKBesovVectorDepthSeminorm
  exact mul_nonneg
    (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    (cubeVectorKFunctional_nonneg Q (Real.rpow (3 : ℝ) (-(j : ℝ))) F)

theorem sqrt_cubeBesovOverlappingPositiveVectorDepthAverage_le_mul_cubeVectorKFunctional_of_forall_competitorValue
    {d : ℕ} (Q : TriadicCube d) (C : ℝ) (F : Vec d → Vec d) (j : ℕ)
    (hC : 0 ≤ C)
    (hcomp :
      ∀ G : CubeVectorH1Function Q,
        Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q F j) ≤
          C *
            cubeVectorKFunctionalCompetitorValue Q
              (Real.rpow (3 : ℝ) (-(j : ℝ))) F G) :
    Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q F j) ≤
      C * cubeVectorKFunctional Q (Real.rpow (3 : ℝ) (-(j : ℝ))) F := by
  let A : ℝ := Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q F j)
  let t : ℝ := Real.rpow (3 : ℝ) (-(j : ℝ))
  by_cases hC_zero : C = 0
  · have hA_le_zero : A ≤ 0 := by
      simpa [A, t, hC_zero] using hcomp default
    simpa [A, t, hC_zero] using hA_le_zero
  · have hC_pos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC_zero)
    have hdiv_le : A / C ≤ cubeVectorKFunctional Q t F := by
      unfold cubeVectorKFunctional
      refine le_csInf (cubeVectorKFunctional_range_nonempty Q t F) ?_
      rintro y ⟨G, rfl⟩
      exact (div_le_iff₀ hC_pos).2 (by
        simpa [A, t, mul_comm] using hcomp G)
    have hA_le : A ≤ cubeVectorKFunctional Q t F * C :=
      (div_le_iff₀ hC_pos).1 hdiv_le
    simpa [A, t, mul_comm] using hA_le

theorem cubeBesovOverlappingPositiveVectorDepthSeminorm_le_mul_cubeKBesovVectorDepthSeminorm_of_forall_competitorValue
    {d : ℕ} (Q : TriadicCube d) (s C : ℝ) (F : Vec d → Vec d) (j : ℕ)
    (hC : 0 ≤ C)
    (hcomp :
      ∀ G : CubeVectorH1Function Q,
        Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q F j) ≤
          C *
            cubeVectorKFunctionalCompetitorValue Q
              (Real.rpow (3 : ℝ) (-(j : ℝ))) F G) :
    cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j ≤
      C * cubeKBesovVectorDepthSeminorm Q s F j := by
  let W : ℝ := Real.rpow (3 : ℝ) (s * (j : ℝ))
  have hW : 0 ≤ W := Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hbase :
      Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q F j) ≤
        C * cubeVectorKFunctional Q (Real.rpow (3 : ℝ) (-(j : ℝ))) F :=
    sqrt_cubeBesovOverlappingPositiveVectorDepthAverage_le_mul_cubeVectorKFunctional_of_forall_competitorValue
      Q C F j hC hcomp
  calc
    cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j
        =
          W * Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q F j) := by
            rfl
    _ ≤ W * (C * cubeVectorKFunctional Q (Real.rpow (3 : ℝ) (-(j : ℝ))) F) :=
          mul_le_mul_of_nonneg_left hbase hW
    _ = C * cubeKBesovVectorDepthSeminorm Q s F j := by
          unfold cubeKBesovVectorDepthSeminorm W
          ring

theorem cubeKBesovVectorDepthSeminorm_le_of_kFunctional_le {d : ℕ}
    (Q : TriadicCube d) (s C : ℝ) (F G : Vec d → Vec d) (j : ℕ)
    (hK :
      cubeVectorKFunctional Q (Real.rpow (3 : ℝ) (-(j : ℝ))) F ≤
        C * cubeVectorKFunctional Q (Real.rpow (3 : ℝ) (-(j : ℝ))) G) :
    cubeKBesovVectorDepthSeminorm Q s F j ≤
      C * cubeKBesovVectorDepthSeminorm Q s G j := by
  let W : ℝ := Real.rpow (3 : ℝ) (s * (j : ℝ))
  have hW : 0 ≤ W := Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  calc
    cubeKBesovVectorDepthSeminorm Q s F j
        = W * cubeVectorKFunctional Q (Real.rpow (3 : ℝ) (-(j : ℝ))) F := by
          rfl
    _ ≤ W * (C * cubeVectorKFunctional Q (Real.rpow (3 : ℝ) (-(j : ℝ))) G) :=
          mul_le_mul_of_nonneg_left hK hW
    _ = C * cubeKBesovVectorDepthSeminorm Q s G j := by
          unfold cubeKBesovVectorDepthSeminorm W
          ring

/-- Finite-depth discrete K-functional Besov seminorm. -/
noncomputable def cubeKBesovVectorPartialSeminormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (F : Vec d → Vec d) : ℝ :=
  Real.sqrt <|
    Finset.sum (Finset.range (N + 1)) fun j =>
      (cubeKBesovVectorDepthSeminorm Q s F j) ^ 2

theorem cubeKBesovVectorPartialSeminormTwo_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (F : Vec d → Vec d) :
    0 ≤ cubeKBesovVectorPartialSeminormTwo Q s N F :=
  Real.sqrt_nonneg _

theorem sq_cubeKBesovVectorPartialSeminormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (F : Vec d → Vec d) :
    (cubeKBesovVectorPartialSeminormTwo Q s N F) ^ 2 =
      Finset.sum (Finset.range (N + 1)) fun j =>
        (cubeKBesovVectorDepthSeminorm Q s F j) ^ 2 := by
  unfold cubeKBesovVectorPartialSeminormTwo
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg fun j _ => sq_nonneg _

theorem cubeKBesovVectorPartialSeminormTwo_le_of_forall_depthSeminorm_le
    {d : ℕ} (Q : TriadicCube d) (s C : ℝ) (N : ℕ)
    (F G : Vec d → Vec d) (hC : 0 ≤ C)
    (hdepth :
      ∀ j ∈ Finset.range (N + 1),
        cubeKBesovVectorDepthSeminorm Q s F j ≤
          C * cubeKBesovVectorDepthSeminorm Q s G j) :
    cubeKBesovVectorPartialSeminormTwo Q s N F ≤
      C * cubeKBesovVectorPartialSeminormTwo Q s N G := by
  let S := Finset.range (N + 1)
  have hsum :
      Finset.sum S (fun j =>
        (cubeKBesovVectorDepthSeminorm Q s F j) ^ 2) ≤
        C ^ 2 *
          Finset.sum S (fun j =>
            (cubeKBesovVectorDepthSeminorm Q s G j) ^ 2) := by
    calc
      Finset.sum S (fun j =>
          (cubeKBesovVectorDepthSeminorm Q s F j) ^ 2)
          ≤ Finset.sum S (fun j =>
              (C * cubeKBesovVectorDepthSeminorm Q s G j) ^ 2) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            have hF_nonneg :
                0 ≤ cubeKBesovVectorDepthSeminorm Q s F j :=
              cubeKBesovVectorDepthSeminorm_nonneg Q s F j
            have hG_nonneg :
                0 ≤ cubeKBesovVectorDepthSeminorm Q s G j :=
              cubeKBesovVectorDepthSeminorm_nonneg Q s G j
            have hCG_nonneg :
                0 ≤ C * cubeKBesovVectorDepthSeminorm Q s G j :=
              mul_nonneg hC hG_nonneg
            exact (sq_le_sq₀ hF_nonneg hCG_nonneg).mpr (hdepth j hj)
      _ = Finset.sum S (fun j =>
            C ^ 2 * (cubeKBesovVectorDepthSeminorm Q s G j) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            ring
      _ = C ^ 2 *
            Finset.sum S (fun j =>
              (cubeKBesovVectorDepthSeminorm Q s G j) ^ 2) := by
            rw [Finset.mul_sum]
  calc
    cubeKBesovVectorPartialSeminormTwo Q s N F
        = Real.sqrt
            (Finset.sum S (fun j =>
              (cubeKBesovVectorDepthSeminorm Q s F j) ^ 2)) := by
          rfl
    _ ≤ Real.sqrt
          (C ^ 2 *
            Finset.sum S (fun j =>
              (cubeKBesovVectorDepthSeminorm Q s G j) ^ 2)) :=
          Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (C ^ 2) *
          Real.sqrt
            (Finset.sum S (fun j =>
              (cubeKBesovVectorDepthSeminorm Q s G j) ^ 2)) := by
          rw [Real.sqrt_mul (sq_nonneg C)]
    _ = C *
          Real.sqrt
            (Finset.sum S (fun j =>
              (cubeKBesovVectorDepthSeminorm Q s G j) ^ 2)) := by
          rw [Real.sqrt_sq hC]
    _ = C * cubeKBesovVectorPartialSeminormTwo Q s N G := by
          rfl

theorem cubeKBesovVectorPartialSeminormTwo_le_of_forall_kFunctional_le
    {d : ℕ} (Q : TriadicCube d) (s C : ℝ) (N : ℕ)
    (F G : Vec d → Vec d) (hC : 0 ≤ C)
    (hK :
      ∀ j ∈ Finset.range (N + 1),
        cubeVectorKFunctional Q (Real.rpow (3 : ℝ) (-(j : ℝ))) F ≤
          C * cubeVectorKFunctional Q (Real.rpow (3 : ℝ) (-(j : ℝ))) G) :
    cubeKBesovVectorPartialSeminormTwo Q s N F ≤
      C * cubeKBesovVectorPartialSeminormTwo Q s N G :=
  cubeKBesovVectorPartialSeminormTwo_le_of_forall_depthSeminorm_le
    Q s C N F G hC fun j hj =>
      cubeKBesovVectorDepthSeminorm_le_of_kFunctional_le
        Q s C F G j (hK j hj)

theorem cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_mul_cubeKBesovVectorPartialSeminormTwo_of_forall_depthSeminorm_le
    {d : ℕ} (Q : TriadicCube d) (s C : ℝ) (N : ℕ)
    (F : Vec d → Vec d) (hC : 0 ≤ C)
    (hdepth :
      ∀ j ∈ Finset.range (N + 1),
        cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j ≤
          C * cubeKBesovVectorDepthSeminorm Q s F j) :
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F ≤
      C * cubeKBesovVectorPartialSeminormTwo Q s N F := by
  let S := Finset.range (N + 1)
  have hsum :
      Finset.sum S (fun j =>
        (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j) ^ 2) ≤
        C ^ 2 *
          Finset.sum S (fun j =>
            (cubeKBesovVectorDepthSeminorm Q s F j) ^ 2) := by
    calc
      Finset.sum S (fun j =>
          (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j) ^ 2)
          ≤ Finset.sum S (fun j =>
              (C * cubeKBesovVectorDepthSeminorm Q s F j) ^ 2) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            have hOverlap_nonneg :
                0 ≤ cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j :=
              cubeBesovOverlappingPositiveVectorDepthSeminorm_nonneg Q s F j
            have hK_nonneg :
                0 ≤ cubeKBesovVectorDepthSeminorm Q s F j :=
              cubeKBesovVectorDepthSeminorm_nonneg Q s F j
            have hCK_nonneg :
                0 ≤ C * cubeKBesovVectorDepthSeminorm Q s F j :=
              mul_nonneg hC hK_nonneg
            exact (sq_le_sq₀ hOverlap_nonneg hCK_nonneg).mpr (hdepth j hj)
      _ = Finset.sum S (fun j =>
            C ^ 2 * (cubeKBesovVectorDepthSeminorm Q s F j) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            ring
      _ = C ^ 2 *
            Finset.sum S (fun j =>
              (cubeKBesovVectorDepthSeminorm Q s F j) ^ 2) := by
            rw [Finset.mul_sum]
  calc
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F
        = Real.sqrt
            (Finset.sum S (fun j =>
              (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j) ^ 2)) := by
          rfl
    _ ≤ Real.sqrt
          (C ^ 2 *
            Finset.sum S (fun j =>
              (cubeKBesovVectorDepthSeminorm Q s F j) ^ 2)) :=
          Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (C ^ 2) *
          Real.sqrt
            (Finset.sum S (fun j =>
              (cubeKBesovVectorDepthSeminorm Q s F j) ^ 2)) := by
          rw [Real.sqrt_mul (sq_nonneg C)]
    _ = C *
          Real.sqrt
            (Finset.sum S (fun j =>
              (cubeKBesovVectorDepthSeminorm Q s F j) ^ 2)) := by
          rw [Real.sqrt_sq hC]
    _ = C * cubeKBesovVectorPartialSeminormTwo Q s N F := by
          rfl

theorem cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_mul_cubeKBesovVectorPartialSeminormTwo_of_forall_competitorValue
    {d : ℕ} (Q : TriadicCube d) (s C : ℝ) (N : ℕ)
    (F : Vec d → Vec d) (hC : 0 ≤ C)
    (hcomp :
      ∀ j ∈ Finset.range (N + 1),
        ∀ G : CubeVectorH1Function Q,
          Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q F j) ≤
            C *
              cubeVectorKFunctionalCompetitorValue Q
                (Real.rpow (3 : ℝ) (-(j : ℝ))) F G) :
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F ≤
      C * cubeKBesovVectorPartialSeminormTwo Q s N F :=
  cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_mul_cubeKBesovVectorPartialSeminormTwo_of_forall_depthSeminorm_le
    Q s C N F hC fun j hj =>
      cubeBesovOverlappingPositiveVectorDepthSeminorm_le_mul_cubeKBesovVectorDepthSeminorm_of_forall_competitorValue
        Q s C F j hC (hcomp j hj)

theorem cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_mul_cubeKBesovVectorPartialSeminormTwo_of_overlapPoincare
    {d : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hPoincare : CubeVectorH1OverlapPoincareEstimate d C)
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (F : Vec d → Vec d)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F ≤
      (8 * (3 ^ d : ℝ) + 2 * C ^ 2 + 1) *
        cubeKBesovVectorPartialSeminormTwo Q s N F := by
  let K : ℝ := 8 * (3 ^ d : ℝ) + 2 * C ^ 2 + 1
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  exact
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_mul_cubeKBesovVectorPartialSeminormTwo_of_forall_competitorValue
      Q s K N F hK_nonneg fun j hj G => by
        simpa [K] using
          sqrt_cubeBesovOverlappingPositiveVectorDepthAverage_le_mul_cubeVectorKFunctionalCompetitorValue_of_overlapPoincare
            hC hPoincare Q F j G hF

/-- Assemble the reverse finite-level comparison from a depthwise
K-functional bound by the corrected overlapping depth seminorm.

This is the square-sum part of the remaining interpolation proof.  The hard
analytic construction still has to provide the depthwise estimate, but once it
does, no additional summability argument is needed. -/
theorem cubeKBesovVectorPartialSeminormTwo_le_mul_cubeBesovOverlappingPositiveVectorPartialSeminormTwo_of_forall_depthSeminorm_le
    {d : ℕ} (Q : TriadicCube d) (s C : ℝ) (N : ℕ)
    (F : Vec d → Vec d) (hC : 0 ≤ C)
    (hdepth :
      ∀ j ∈ Finset.range (N + 1),
        cubeKBesovVectorDepthSeminorm Q s F j ≤
          C * cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j) :
    cubeKBesovVectorPartialSeminormTwo Q s N F ≤
      C * cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F := by
  let S := Finset.range (N + 1)
  have hsum :
      Finset.sum S (fun j =>
        (cubeKBesovVectorDepthSeminorm Q s F j) ^ 2) ≤
        C ^ 2 *
          Finset.sum S (fun j =>
            (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j) ^ 2) := by
    calc
      Finset.sum S (fun j =>
          (cubeKBesovVectorDepthSeminorm Q s F j) ^ 2)
          ≤ Finset.sum S (fun j =>
              (C * cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j) ^ 2) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            have hK_nonneg :
                0 ≤ cubeKBesovVectorDepthSeminorm Q s F j :=
              cubeKBesovVectorDepthSeminorm_nonneg Q s F j
            have hOverlap_nonneg :
                0 ≤ cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j :=
              cubeBesovOverlappingPositiveVectorDepthSeminorm_nonneg Q s F j
            have hCOverlap_nonneg :
                0 ≤ C * cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j :=
              mul_nonneg hC hOverlap_nonneg
            exact (sq_le_sq₀ hK_nonneg hCOverlap_nonneg).mpr (hdepth j hj)
      _ = Finset.sum S (fun j =>
            C ^ 2 * (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            ring
      _ = C ^ 2 *
            Finset.sum S (fun j =>
              (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j) ^ 2) := by
            rw [Finset.mul_sum]
  calc
    cubeKBesovVectorPartialSeminormTwo Q s N F
        = Real.sqrt
            (Finset.sum S (fun j =>
              (cubeKBesovVectorDepthSeminorm Q s F j) ^ 2)) := by
          rfl
    _ ≤ Real.sqrt
          (C ^ 2 *
            Finset.sum S (fun j =>
              (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j) ^ 2)) :=
          Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (C ^ 2) *
          Real.sqrt
            (Finset.sum S (fun j =>
              (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j) ^ 2)) := by
          rw [Real.sqrt_mul (sq_nonneg C)]
    _ = C *
          Real.sqrt
            (Finset.sum S (fun j =>
              (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j) ^ 2)) := by
          rw [Real.sqrt_sq hC]
    _ = C * cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F := by
          rfl

/-- Full discrete K-functional Besov seminorm. -/
noncomputable def cubeKBesovVectorSeminormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) : ℝ :=
  sSup (Set.range fun N : ℕ => cubeKBesovVectorPartialSeminormTwo Q s N F)

theorem cubeKBesovVectorSeminormTwo_le_of_partialBound {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) {B : ℝ}
    (hB : ∀ N : ℕ, cubeKBesovVectorPartialSeminormTwo Q s N F ≤ B) :
    cubeKBesovVectorSeminormTwo Q s F ≤ B := by
  unfold cubeKBesovVectorSeminormTwo
  refine csSup_le ?_ ?_
  · exact ⟨cubeKBesovVectorPartialSeminormTwo Q s 0 F, ⟨0, rfl⟩⟩
  · rintro x ⟨N, rfl⟩
    exact hB N

theorem cubeKBesovVectorPartialSeminormTwo_le_seminorm_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeKBesovVectorPartialSeminormTwo Q s N F))
    (N : ℕ) :
    cubeKBesovVectorPartialSeminormTwo Q s N F ≤
      cubeKBesovVectorSeminormTwo Q s F := by
  unfold cubeKBesovVectorSeminormTwo
  exact le_csSup hBdd ⟨N, rfl⟩

theorem cubeKBesovVectorSeminormTwo_nonneg_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeKBesovVectorPartialSeminormTwo Q s N F)) :
    0 ≤ cubeKBesovVectorSeminormTwo Q s F := by
  have h0_le :
      cubeKBesovVectorPartialSeminormTwo Q s 0 F ≤
        cubeKBesovVectorSeminormTwo Q s F :=
    cubeKBesovVectorPartialSeminormTwo_le_seminorm_of_bddAbove
      Q s F hBdd 0
  exact (cubeKBesovVectorPartialSeminormTwo_nonneg Q s 0 F).trans h0_le

theorem cubeKBesovVectorSeminormTwo_le_of_forall_partialSeminormTwo_le
    {d : ℕ} (Q : TriadicCube d) (s C : ℝ) (F G : Vec d → Vec d)
    (hC : 0 ≤ C)
    (hG_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeKBesovVectorPartialSeminormTwo Q s N G))
    (hpartial :
      ∀ N : ℕ,
        cubeKBesovVectorPartialSeminormTwo Q s N F ≤
          C * cubeKBesovVectorPartialSeminormTwo Q s N G) :
    cubeKBesovVectorSeminormTwo Q s F ≤
      C * cubeKBesovVectorSeminormTwo Q s G :=
  cubeKBesovVectorSeminormTwo_le_of_partialBound Q s F fun N =>
    (hpartial N).trans
      (mul_le_mul_of_nonneg_left
        (cubeKBesovVectorPartialSeminormTwo_le_seminorm_of_bddAbove
          Q s G hG_bdd N)
        hC)

theorem cubeKBesovVectorSeminormTwo_le_of_forall_kFunctional_le
    {d : ℕ} (Q : TriadicCube d) (s C : ℝ) (F G : Vec d → Vec d)
    (hC : 0 ≤ C)
    (hG_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeKBesovVectorPartialSeminormTwo Q s N G))
    (hK :
      ∀ j : ℕ,
        cubeVectorKFunctional Q (Real.rpow (3 : ℝ) (-(j : ℝ))) F ≤
          C * cubeVectorKFunctional Q (Real.rpow (3 : ℝ) (-(j : ℝ))) G) :
    cubeKBesovVectorSeminormTwo Q s F ≤
      C * cubeKBesovVectorSeminormTwo Q s G :=
  cubeKBesovVectorSeminormTwo_le_of_forall_partialSeminormTwo_le
    Q s C F G hC hG_bdd fun N =>
      cubeKBesovVectorPartialSeminormTwo_le_of_forall_kFunctional_le
        Q s C N F G hC fun j _hj => hK j

/-- Full discrete K-functional Besov norm with the same mean term as the
note-normalized positive triadic norm. -/
noncomputable def cubeKBesovVectorNormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) : ℝ :=
  Real.sqrt (vecNormSq (cubeAverageVec Q F)) +
    cubeKBesovVectorSeminormTwo Q s F

theorem cubeKBesovVectorNormTwo_le_of_average_and_seminorm {d : ℕ}
    (Q : TriadicCube d) (s C : ℝ) (F G : Vec d → Vec d)
    (havg :
      Real.sqrt (vecNormSq (cubeAverageVec Q F)) ≤
        C * Real.sqrt (vecNormSq (cubeAverageVec Q G)))
    (hsemi :
      cubeKBesovVectorSeminormTwo Q s F ≤
        C * cubeKBesovVectorSeminormTwo Q s G) :
    cubeKBesovVectorNormTwo Q s F ≤
      C * cubeKBesovVectorNormTwo Q s G := by
  unfold cubeKBesovVectorNormTwo
  calc
    Real.sqrt (vecNormSq (cubeAverageVec Q F)) +
        cubeKBesovVectorSeminormTwo Q s F
        ≤
          C * Real.sqrt (vecNormSq (cubeAverageVec Q G)) +
            C * cubeKBesovVectorSeminormTwo Q s G :=
          add_le_add havg hsemi
    _ =
          C *
            (Real.sqrt (vecNormSq (cubeAverageVec Q G)) +
              cubeKBesovVectorSeminormTwo Q s G) := by
          ring

/-- The canonical K-functional Besov norm model used by the revised proof. -/
noncomputable def cubeKBesovNormModel (d : ℕ) : CubeKBesovNormModel d :=
  fun Q s F => cubeKBesovVectorNormTwo Q s F

/-- Pure function-space bridge between a K-functional Besov norm and the
corrected overlapping positive `B^s_{2,2}` norm. -/
def CubeKBesovOverlappingEquivalence
    {d : ℕ} (K : CubeKBesovNormModel d) : Prop :=
  ∀ {s : ℝ}, 0 < s → s < 1 →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Q : TriadicCube d) (F : Vec d → Vec d),
        cubeBesovOverlappingPositiveVectorNormTwo Q s F ≤ C * K Q s F ∧
          K Q s F ≤ C * cubeBesovOverlappingPositiveVectorNormTwo Q s F

/-- K-functional regularity estimate for the Dirichlet divergence solution
operator. This is the PDE-plus-K-functional part of the revised proof, before
the pure norm-equivalence bridge back to the triadic Besov norm. -/
def CubeKBesovDirichletRegularity
    {d : ℕ} (K : CubeKBesovNormModel d) : Prop :=
  ∀ {s : ℝ}, 0 < s → s < 1 →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Q : TriadicCube d) (h : Vec d → Vec d)
        (w : H10Function (openCubeSet Q)),
        CubeVectorOverlappingBesovHRegularity Q s h →
        CubeDirichletDivergenceProblem Q w h →
          K Q s (fun x => w.toH1Function.grad x) ≤ C * K Q s h

/-- Uniform-in-`s` version of `CubeKBesovDirichletRegularity`.  This is the
form needed by downstream arguments which must track the entire `s`-profile
instead of choosing a fresh constant after `s` has been fixed. -/
def CubeKBesovDirichletRegularityUniform
    {d : ℕ} (K : CubeKBesovNormModel d) (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ {s : ℝ}, 0 < s → s < 1 →
      ∀ (Q : TriadicCube d) (h : Vec d → Vec d)
        (w : H10Function (openCubeSet Q)),
        CubeVectorOverlappingBesovHRegularity Q s h →
        CubeDirichletDivergenceProblem Q w h →
          K Q s (fun x => w.toH1Function.grad x) ≤ C * K Q s h

theorem CubeKBesovDirichletRegularityUniform.to_dirichletRegularity
    {d : ℕ} {K : CubeKBesovNormModel d} {C : ℝ}
    (h : CubeKBesovDirichletRegularityUniform K C) :
    CubeKBesovDirichletRegularity K := by
  intro s hs_pos hs_lt
  exact ⟨C, h.1, h.2 hs_pos hs_lt⟩

/-- Boundedness bridge needed to read the `sSup` defining the K-functional
Besov seminorm as a genuine supremum for inputs known to have the corrected
overlapping positive Besov regularity. -/
def CubeKBesovInputBoundednessOfOverlappingHRegularity
    (d : ℕ) : Prop :=
  ∀ {s : ℝ}, 0 < s → s < 1 →
    ∀ (Q : TriadicCube d) (h : Vec d → Vec d),
      CubeVectorOverlappingBesovHRegularity Q s h →
        BddAbove (Set.range fun N : ℕ =>
          cubeKBesovVectorPartialSeminormTwo Q s N h)

/-- Finite-level pure K/overlapping comparison strong enough to make the
`sSup`-based K-functional seminorm honest on every datum with overlapping
positive Besov regularity.

This is the boundedness half of the pure Besov theory in a form that avoids
talking about the full K-seminorm before boundedness has been established. -/
def CubeKBesovPartialBoundByOverlappingPositive
    (d : ℕ) : Prop :=
  ∀ {s : ℝ}, 0 < s → s < 1 →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Q : TriadicCube d) (h : Vec d → Vec d) (N : ℕ),
        MeasureTheory.MemLp h (2 : ℝ≥0∞) (normalizedCubeMeasure Q) →
        cubeKBesovVectorPartialSeminormTwo Q s N h ≤
          C *
            (Real.sqrt (vecNormSq (cubeAverageVec Q h)) +
              cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N h)

/-- Uniform-in-`s` finite-level K/overlap comparison. -/
def CubeKBesovPartialBoundByOverlappingPositiveUniform
    (d : ℕ) (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ {s : ℝ}, 0 < s → s < 1 →
      ∀ (Q : TriadicCube d) (h : Vec d → Vec d) (N : ℕ),
        MeasureTheory.MemLp h (2 : ℝ≥0∞) (normalizedCubeMeasure Q) →
        cubeKBesovVectorPartialSeminormTwo Q s N h ≤
          C *
            (Real.sqrt (vecNormSq (cubeAverageVec Q h)) +
              cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N h)

theorem CubeKBesovPartialBoundByOverlappingPositiveUniform.to_partialBound
    {d : ℕ} {C : ℝ}
    (h : CubeKBesovPartialBoundByOverlappingPositiveUniform d C) :
    CubeKBesovPartialBoundByOverlappingPositive d := by
  intro s hs_pos hs_lt
  exact ⟨C, h.1, h.2 hs_pos hs_lt⟩

/-- One-depth competitor estimate expected from the overlap averaging
operator.

For every parent cube, field, and depth, there is an `H¹` competitor whose
residual and scaled gradient are both controlled by the corrected overlapping
oscillation at that depth. -/
def CubeKBesovOverlapAveragingCompetitorEstimate
    (d : ℕ) (C : ℝ) : Prop :=
  ∀ (Q : TriadicCube d) (h : Vec d → Vec d) (j : ℕ),
    MeasureTheory.MemLp h (2 : ℝ≥0∞) (normalizedCubeMeasure Q) →
    ∃ G : CubeVectorH1Function Q,
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => h x - G.toField x) ≤
          C * Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q h j) ∧
        Real.rpow (3 : ℝ) (-(j : ℝ)) *
            G.relativeGradientCoordL2NormSum ≤
          C * Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q h j)

/-- Depthwise reverse K/overlap estimate supplied by the planned smoothing
operator.

This is now the precise analytic target for the hard interpolation step: build
an `H¹` competitor at scale `3^{-j}` whose K-functional value is controlled by
the corrected overlapping oscillation at the same depth. -/
def CubeKBesovDepthBoundByOverlappingPositive
    (d : ℕ) : Prop :=
  ∀ {s : ℝ}, 0 < s → s < 1 →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Q : TriadicCube d) (h : Vec d → Vec d) (j : ℕ),
        MeasureTheory.MemLp h (2 : ℝ≥0∞) (normalizedCubeMeasure Q) →
        cubeKBesovVectorDepthSeminorm Q s h j ≤
          C * cubeBesovOverlappingPositiveVectorDepthSeminorm Q s h j

/-- Uniform-in-`s` depthwise K/overlap comparison. -/
def CubeKBesovDepthBoundByOverlappingPositiveUniform
    (d : ℕ) (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ {s : ℝ}, 0 < s → s < 1 →
      ∀ (Q : TriadicCube d) (h : Vec d → Vec d) (j : ℕ),
        MeasureTheory.MemLp h (2 : ℝ≥0∞) (normalizedCubeMeasure Q) →
        cubeKBesovVectorDepthSeminorm Q s h j ≤
          C * cubeBesovOverlappingPositiveVectorDepthSeminorm Q s h j

theorem CubeKBesovDepthBoundByOverlappingPositiveUniform.to_depthBound
    {d : ℕ} {C : ℝ}
    (h : CubeKBesovDepthBoundByOverlappingPositiveUniform d C) :
    CubeKBesovDepthBoundByOverlappingPositive d := by
  intro s hs_pos hs_lt
  exact ⟨C, h.1, h.2 hs_pos hs_lt⟩

/-- Uniform residual-plus-gradient control implies the uniform depthwise
K/overlap estimate. -/
theorem cubeKBesovDepthBoundByOverlappingPositiveUniform_of_overlapAveragingCompetitorEstimate
    {d : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hcomp : CubeKBesovOverlapAveragingCompetitorEstimate d C) :
    CubeKBesovDepthBoundByOverlappingPositiveUniform d (2 * C) := by
  refine ⟨mul_nonneg (by norm_num) hC, ?_⟩
  intro s _hs_pos _hs_lt Q h j hh
  rcases hcomp Q h j hh with ⟨G, hres, hgrad⟩
  let t : ℝ := Real.rpow (3 : ℝ) (-(j : ℝ))
  let A : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) (fun x => h x - G.toField x)
  let B : ℝ := t * G.relativeGradientCoordL2NormSum
  let D : ℝ := cubeBesovOverlappingPositiveVectorDepthAverage Q h j
  let Y : ℝ := C * Real.sqrt D
  let W : ℝ := Real.rpow (3 : ℝ) (s * (j : ℝ))
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact cubeLpNorm_nonneg Q (2 : ℝ≥0∞) (fun x => h x - G.toField x)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg ht_nonneg G.relativeGradientCoordL2NormSum_nonneg
  have hY_nonneg : 0 ≤ Y := by
    dsimp [Y]
    exact mul_nonneg hC (Real.sqrt_nonneg D)
  have hW_nonneg : 0 ≤ W := by
    dsimp [W]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hres' : A ≤ Y := by
    simpa [A, D, Y] using hres
  have hgrad' : B ≤ Y := by
    simpa [B, D, Y, t] using hgrad
  have hcomp_value_le_sum :
      cubeVectorKFunctionalCompetitorValue Q t h G ≤ A + B := by
    have hright_nonneg : 0 ≤ A + B := add_nonneg hA_nonneg hB_nonneg
    have hsq :
        A ^ 2 + t ^ 2 * G.relativeGradientCoordL2NormSum ^ 2 ≤
          (A + B) ^ 2 := by
      have hBsq : B ^ 2 = t ^ 2 * G.relativeGradientCoordL2NormSum ^ 2 := by
        dsimp [B]
        ring
      rw [← hBsq]
      nlinarith [mul_nonneg hA_nonneg hB_nonneg]
    simpa [cubeVectorKFunctionalCompetitorValue, A, B] using
      (Real.sqrt_le_iff.mpr ⟨hright_nonneg, hsq⟩)
  have hcomp_value_le :
      cubeVectorKFunctionalCompetitorValue Q t h G ≤ 2 * Y := by
    calc
      cubeVectorKFunctionalCompetitorValue Q t h G
          ≤ A + B := hcomp_value_le_sum
      _ ≤ Y + Y := add_le_add hres' hgrad'
      _ = 2 * Y := by ring
  have hK_le :
      cubeVectorKFunctional Q t h ≤ 2 * Y :=
    (cubeVectorKFunctional_le_competitor Q t h G).trans hcomp_value_le
  calc
    cubeKBesovVectorDepthSeminorm Q s h j
        = W * cubeVectorKFunctional Q t h := by
          rfl
    _ ≤ W * (2 * Y) :=
          mul_le_mul_of_nonneg_left hK_le hW_nonneg
    _ = (2 * C) *
          (W * Real.sqrt
            (cubeBesovOverlappingPositiveVectorDepthAverage Q h j)) := by
          simp [Y, D]
          ring
    _ = (2 * C) *
          cubeBesovOverlappingPositiveVectorDepthSeminorm Q s h j := by
          rfl

/-- Residual plus scaled-gradient control for the planned overlap averaging
competitor implies the depthwise K/overlap estimate. -/
theorem cubeKBesovDepthBoundByOverlappingPositive_of_overlapAveragingCompetitorEstimate
    {d : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hcomp : CubeKBesovOverlapAveragingCompetitorEstimate d C) :
    CubeKBesovDepthBoundByOverlappingPositive d := by
  exact
    (cubeKBesovDepthBoundByOverlappingPositiveUniform_of_overlapAveragingCompetitorEstimate
      hC hcomp).to_depthBound


end

end Homogenization
