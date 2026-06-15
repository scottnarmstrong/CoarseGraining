import Homogenization.Besov.Poincare.HarmonicGradient.LocalMultiscale

namespace Homogenization

open scoped BigOperators ENNReal

variable {d : ℕ}

/-! # Final Local Estimate Adapter for Vector Poincare -/

/-- Convert a vector projected dual estimate into the corresponding vector
local-multiscale estimate at the inflated note constant. The proof
splits the right-hand sum coordinatewise and reuses the scalar bridges
`cubeBesovDualMeanZeroSeminorm_le_note_constant_mul_cubeBesovCircNorm` and
`cubeBesovCircNorm_projection_le_three_halves_mul_cubeBesovCircPartialNorm_of_memLp`. -/
theorem CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate.to_localEstimate
    {Q : TriadicCube d} {C : ℝ} {u : Vec d → ℝ} {G : Vec d → Vec d} {M : ℕ}
    (hproj :
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C u G M)
    (hG :
      ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hC : 0 ≤ C) :
    CubeLocalMultiscalePoincareVectorEstimate Q
      ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) u G M := by
  intro j hj R hR
  have hdual := hproj j hj R hR
  -- per-component MemLp on the descendant R
  have hGR : ∀ i, MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞)
      (normalizedCubeMeasure R) := by
    intro i
    exact memLp_on_descendant_of_memLp (Q := Q) (R := R) (j := j) hR (hG i)
  -- per-component bound chaining dual ≤ note·circ ≤ note·(3/2)·circPartial
  have hcoord :
      ∀ i : Fin d,
        cubeBesovDualMeanZeroSeminorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (cubeProjection R (M - j) (fun x => G x i)) ≤
          (3 : ℝ) ^ ((d : ℝ) + 1) *
            ((3 / 2 : ℝ) *
              cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M - j)
                (fun x => G x i)) := by
    intro i
    set gi : Vec d → ℝ := fun x => G x i with hgi_def
    have hgiR : MeasureTheory.MemLp gi (2 : ℝ≥0∞) (normalizedCubeMeasure R) := hGR i
    have hprojiMem :
        MeasureTheory.MemLp (cubeProjection R (M - j) gi)
          (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
      cubeProjection_memLp R (M - j) (2 : ℝ≥0∞) gi
    have hconj_eq :
        cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
      simpa [cubeBesovConjExponent] using
        (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
    have hdualLeNote :
        cubeBesovDualMeanZeroSeminorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (cubeProjection R (M - j) gi) ≤
          (3 : ℝ) ^ ((d : ℝ) + 1) *
            cubeBesovCircNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (cubeProjection R (M - j) gi) := by
      simpa using
        cubeBesovDualMeanZeroSeminorm_le_note_constant_mul_cubeBesovCircNorm
          (Q := R) (s := 1) (p := (2 : ℝ≥0∞)) (q := (1 : ℝ≥0∞))
          (u := cubeProjection R (M - j) gi)
          (by norm_num) hprojiMem (by norm_num) (by norm_num)
          (by intro htop; simp [hconj_eq] at htop)
          (by norm_num)
    have hCircLePartial :
        cubeBesovCircNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (cubeProjection R (M - j) gi) ≤
          (3 / 2 : ℝ) *
            cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M - j) gi :=
      cubeBesovCircNorm_projection_le_three_halves_mul_cubeBesovCircPartialNorm_of_memLp
        (Q := R) (u := gi) (M := M - j) hgiR
    have hnote_nonneg : 0 ≤ (3 : ℝ) ^ ((d : ℝ) + 1) :=
      Real.rpow_nonneg (by positivity) _
    calc
      cubeBesovDualMeanZeroSeminorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (cubeProjection R (M - j) gi)
          ≤ (3 : ℝ) ^ ((d : ℝ) + 1) *
              cubeBesovCircNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (cubeProjection R (M - j) gi) := hdualLeNote
      _ ≤ (3 : ℝ) ^ ((d : ℝ) + 1) *
            ((3 / 2 : ℝ) *
              cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M - j) gi) :=
            mul_le_mul_of_nonneg_left hCircLePartial hnote_nonneg
  -- sum over coordinates
  have hSum :
      ∑ i : Fin d,
          cubeBesovDualMeanZeroSeminorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (cubeProjection R (M - j) (fun x => G x i)) ≤
        ∑ i : Fin d,
          (3 : ℝ) ^ ((d : ℝ) + 1) *
            ((3 / 2 : ℝ) *
              cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M - j)
                (fun x => G x i)) := by
    refine Finset.sum_le_sum ?_
    intro i _
    exact hcoord i
  have hSum_factored :
      ∑ i : Fin d,
          (3 : ℝ) ^ ((d : ℝ) + 1) *
            ((3 / 2 : ℝ) *
              cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M - j)
                (fun x => G x i)) =
        (3 : ℝ) ^ ((d : ℝ) + 1) * (3 / 2 : ℝ) *
          ∑ i : Fin d,
            cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M - j)
              (fun x => G x i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  have hC_chain : 0 ≤ C := hC
  calc
    cubeBesovOscillation R (2 : ℝ≥0∞) u
        ≤ C * ∑ i : Fin d,
            cubeBesovDualMeanZeroSeminorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (cubeProjection R (M - j) (fun x => G x i)) := hdual
    _ ≤ C * ((3 : ℝ) ^ ((d : ℝ) + 1) * (3 / 2 : ℝ) *
            ∑ i : Fin d,
              cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M - j)
                (fun x => G x i)) := by
          have hsum_bound : ∑ i : Fin d,
              cubeBesovDualMeanZeroSeminorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (cubeProjection R (M - j) (fun x => G x i)) ≤
              (3 : ℝ) ^ ((d : ℝ) + 1) * (3 / 2 : ℝ) *
                ∑ i : Fin d,
                  cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M - j)
                    (fun x => G x i) :=
            le_trans hSum (le_of_eq hSum_factored)
          exact mul_le_mul_of_nonneg_left hsum_bound hC_chain
    _ = ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ∑ i : Fin d,
            cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M - j)
              (fun x => G x i) := by ring


end Homogenization
