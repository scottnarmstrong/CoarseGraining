import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.ScalarReduction
import Homogenization.Book.Ch05.Theorems.Section56.VarianceEstimateQuadratic.Triangle
import Homogenization.Book.Ch05.Theorems.Section57.ProbeEnvelope
import Homogenization.HighContrast.EntryScale.NoDropResponse
import Homogenization.HighContrast.EntryScale.BadMaximal.P1

open MeasureTheory
open scoped ENNReal
open scoped Matrix.Norms.Elementwise
open scoped MatrixOrder

namespace Homogenization.HighContrast.EntryScale

noncomputable section

theorem coarseBlockMatrix_upperLeft_matLoewnerLE_barSigma_mul_one_add_terminalSpectralPositivePartAtScale
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.RegCoeffField d)
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a) :
    Homogenization.MatLoewnerLE
      (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).upperLeft
      ((hP.barSigmaAtScale hStruct (m : ℤ) *
          (1 + terminalSpectralPositivePartAtScale hP hStruct m Q a)) •
        (1 : Homogenization.Mat d)) := by
  intro e
  let b := hP.barSigmaAtScale hStruct (m : ℤ)
  let T := terminalSpectralPositivePartAtScale hP hStruct m Q a
  let xu : Homogenization.FullBlockVec d :=
    Homogenization.toFullBlockVec ((Real.sqrt b) • e, 0)
  let obs :=
    Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockNormalizedQuadraticObservable
      hP hStruct (m : ℤ) xu (Homogenization.cubeSet Q) a
  let qdot := dotProduct xu xu
  have hb : 0 < b := by
    simpa [b] using
      Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
        hP hStruct hP4 m
  have hSymm :=
    coarseBlockMatrix_cubeSet_symm_of_aelocallyUniformlyEllipticField Q ha
  have hobs_le : obs - qdot ≤ T * qdot := by
    dsimp [obs, qdot, T, xu]
    exact
      fullBlockNormalizedQuadraticObservable_sub_dotProduct_le_terminalSpectralPositivePartAtScale_mul_dotProduct
        hP hStruct hP4 m Q a hSymm xu
  have hobs_eq :
      obs =
        Homogenization.vecDot e
          (Homogenization.matVecMul
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).upperLeft e) := by
    dsimp [obs, xu, b]
    exact fullBlockNormalizedQuadraticObservable_upperLift_eq hP hStruct hP4 m Q a e
  have hdot_eq : qdot = b * Homogenization.vecDot e e := by
    dsimp [qdot, xu]
    exact upperLift_dotProduct_eq hb.le e
  have hquad :
      Homogenization.vecDot e
          (Homogenization.matVecMul
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).upperLeft e) ≤
        (b * (1 + T)) * Homogenization.vecDot e e := by
    calc
      Homogenization.vecDot e
          (Homogenization.matVecMul
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).upperLeft e) =
          obs := hobs_eq.symm
      _ = (obs - qdot) + qdot := by ring
      _ ≤ T * qdot + qdot := by linarith
      _ = (b * (1 + T)) * Homogenization.vecDot e e := by
          rw [hdot_eq]
          ring
  have hhalf := mul_le_mul_of_nonneg_left hquad (by norm_num : 0 ≤ (1 / 2 : ℝ))
  calc
    (1 / 2 : ℝ) *
        Homogenization.vecDot e
          (Homogenization.matVecMul
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).upperLeft e)
        ≤ (1 / 2 : ℝ) * ((b * (1 + T)) * Homogenization.vecDot e e) := hhalf
    _ =
        (1 / 2 : ℝ) *
          Homogenization.vecDot e
            (Homogenization.matVecMul
              (((b * (1 + T)) • (1 : Homogenization.Mat d))) e) := by
          rw [vecDot_matVecMul_smul_one]

theorem coarseBlockMatrix_lowerRight_matLoewnerLE_barSigmaStar_inv_mul_one_add_terminalSpectralPositivePartAtScale
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.RegCoeffField d)
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a) :
    Homogenization.MatLoewnerLE
      (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).lowerRight
      (((hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ *
          (1 + terminalSpectralPositivePartAtScale hP hStruct m Q a)) •
        (1 : Homogenization.Mat d)) := by
  intro e
  let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let T := terminalSpectralPositivePartAtScale hP hStruct m Q a
  let xl : Homogenization.FullBlockVec d :=
    Homogenization.toFullBlockVec (0, (Real.sqrt c)⁻¹ • e)
  let obs :=
    Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockNormalizedQuadraticObservable
      hP hStruct (m : ℤ) xl (Homogenization.cubeSet Q) a
  let qdot := dotProduct xl xl
  have hc : 0 < c := by
    simpa [c] using
      Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
        hP hStruct hP4 m
  have hSymm :=
    coarseBlockMatrix_cubeSet_symm_of_aelocallyUniformlyEllipticField Q ha
  have hobs_le : obs - qdot ≤ T * qdot := by
    dsimp [obs, qdot, T, xl]
    exact
      fullBlockNormalizedQuadraticObservable_sub_dotProduct_le_terminalSpectralPositivePartAtScale_mul_dotProduct
        hP hStruct hP4 m Q a hSymm xl
  have hobs_eq :
      obs =
        Homogenization.vecDot e
          (Homogenization.matVecMul
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).lowerRight e) := by
    dsimp [obs, xl, c]
    exact fullBlockNormalizedQuadraticObservable_lowerLift_eq hP hStruct hP4 m Q a e
  have hdot_eq : qdot = c⁻¹ * Homogenization.vecDot e e := by
    dsimp [qdot, xl]
    exact lowerLift_dotProduct_eq hc.le e
  have hquad :
      Homogenization.vecDot e
          (Homogenization.matVecMul
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).lowerRight e) ≤
        (c⁻¹ * (1 + T)) * Homogenization.vecDot e e := by
    calc
      Homogenization.vecDot e
          (Homogenization.matVecMul
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).lowerRight e) =
          obs := hobs_eq.symm
      _ = (obs - qdot) + qdot := by ring
      _ ≤ T * qdot + qdot := by linarith
      _ = (c⁻¹ * (1 + T)) * Homogenization.vecDot e e := by
          rw [hdot_eq]
          ring
  have hhalf := mul_le_mul_of_nonneg_left hquad (by norm_num : 0 ≤ (1 / 2 : ℝ))
  calc
    (1 / 2 : ℝ) *
        Homogenization.vecDot e
          (Homogenization.matVecMul
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).lowerRight e)
        ≤ (1 / 2 : ℝ) * ((c⁻¹ * (1 + T)) * Homogenization.vecDot e e) := hhalf
    _ =
        (1 / 2 : ℝ) *
          Homogenization.vecDot e
            (Homogenization.matVecMul
              (((c⁻¹ * (1 + T)) • (1 : Homogenization.Mat d))) e) := by
          rw [vecDot_matVecMul_smul_one]

theorem coarseBlockMatrix_upperLeft_matrixNorm_le_barSigma_mul_one_add_terminalSpectralPositivePartAtScale
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.RegCoeffField d)
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a) :
    Homogenization.Book.Ch02.matrixNorm
        (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).upperLeft ≤
      hP.barSigmaAtScale hStruct (m : ℤ) *
        (1 + terminalSpectralPositivePartAtScale hP hStruct m Q a) := by
  let A := Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a
  let c :=
    hP.barSigmaAtScale hStruct (m : ℤ) *
      (1 + terminalSpectralPositivePartAtScale hP hStruct m Q a)
  have hSymm := coarseBlockMatrix_cubeSet_symm_of_aelocallyUniformlyEllipticField Q ha
  have hPos := coarseBlockMatrix_cubeSet_blockPosDef_of_aelocallyUniformlyEllipticField Q ha
  have hApsd : A.upperLeft.PosSemidef :=
    upperLeft_posSemidef_of_isSymmetricBlockMat_of_blockPosDef hSymm hPos
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg
      (Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
        hP hStruct hP4 m).le
      (by nlinarith [terminalSpectralPositivePartAtScale_nonneg hP hStruct m Q a])
  have hBpsd : (c • (1 : Homogenization.Mat d)).PosSemidef :=
    scalar_one_posSemidef_of_nonneg hc_nonneg
  have hLE :
      Homogenization.MatLoewnerLE A.upperLeft (c • (1 : Homogenization.Mat d)) := by
    dsimp [A, c]
    exact
      coarseBlockMatrix_upperLeft_matLoewnerLE_barSigma_mul_one_add_terminalSpectralPositivePartAtScale
        hP hStruct hP4 m Q a ha
  calc
    Homogenization.Book.Ch02.matrixNorm A.upperLeft ≤
        Homogenization.Book.Ch02.matrixNorm (c • (1 : Homogenization.Mat d)) :=
          Homogenization.Book.Ch02.matrixNorm_le_of_matLoewnerLE_of_posSemidef
            hApsd hBpsd hLE
    _ = c :=
          Homogenization.Book.Ch05.Section52.matrixNorm_smul_one_eq_of_nonneg hc_nonneg
    _ =
        hP.barSigmaAtScale hStruct (m : ℤ) *
          (1 + terminalSpectralPositivePartAtScale hP hStruct m Q a) := by
          rfl

theorem coarseBlockMatrix_lowerRight_matrixNorm_le_barSigmaStar_inv_mul_one_add_terminalSpectralPositivePartAtScale
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.RegCoeffField d)
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a) :
    Homogenization.Book.Ch02.matrixNorm
        (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).lowerRight ≤
      (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ *
        (1 + terminalSpectralPositivePartAtScale hP hStruct m Q a) := by
  let A := Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a
  let c :=
    (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ *
      (1 + terminalSpectralPositivePartAtScale hP hStruct m Q a)
  have hSymm := coarseBlockMatrix_cubeSet_symm_of_aelocallyUniformlyEllipticField Q ha
  have hPos := coarseBlockMatrix_cubeSet_blockPosDef_of_aelocallyUniformlyEllipticField Q ha
  have hApsd : A.lowerRight.PosSemidef :=
    lowerRight_posSemidef_of_isSymmetricBlockMat_of_blockPosDef hSymm hPos
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg
      (Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_inv_pos_of_P4
        hP hStruct hP4 m).le
      (by nlinarith [terminalSpectralPositivePartAtScale_nonneg hP hStruct m Q a])
  have hBpsd : (c • (1 : Homogenization.Mat d)).PosSemidef :=
    scalar_one_posSemidef_of_nonneg hc_nonneg
  have hLE :
      Homogenization.MatLoewnerLE A.lowerRight (c • (1 : Homogenization.Mat d)) := by
    dsimp [A, c]
    exact
      coarseBlockMatrix_lowerRight_matLoewnerLE_barSigmaStar_inv_mul_one_add_terminalSpectralPositivePartAtScale
        hP hStruct hP4 m Q a ha
  calc
    Homogenization.Book.Ch02.matrixNorm A.lowerRight ≤
        Homogenization.Book.Ch02.matrixNorm (c • (1 : Homogenization.Mat d)) :=
          Homogenization.Book.Ch02.matrixNorm_le_of_matLoewnerLE_of_posSemidef
            hApsd hBpsd hLE
    _ = c :=
          Homogenization.Book.Ch05.Section52.matrixNorm_smul_one_eq_of_nonneg hc_nonneg
    _ =
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ *
          (1 + terminalSpectralPositivePartAtScale hP hStruct m Q a) := by
          rfl

private theorem positivePart_sub_le_base_mul_of_le_base_mul_one_add
    {x base t : ℝ} (hbase : 0 ≤ base) (ht : 0 ≤ t)
    (hx : x ≤ base * (1 + t)) :
    max (x - base) 0 ≤ base * t := by
  have hright_nonneg : 0 ≤ base * t := mul_nonneg hbase ht
  have hleft : x - base ≤ base * t := by
    nlinarith
  exact max_le hleft hright_nonneg

/--
Source labels `e.M.def` and `p.HC.CR`: one terminal block's upper matrix-norm
positive excess is controlled by the spectral positive part of the same
terminally normalized full-block fluctuation.
-/
theorem upperLeft_terminalPositiveExcess_le_barSigma_mul_terminalSpectralPositivePartAtScale
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.RegCoeffField d)
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a) :
    max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).upperLeft -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0 ≤
      hP.barSigmaAtScale hStruct (m : ℤ) *
        terminalSpectralPositivePartAtScale hP hStruct m Q a := by
  exact
    positivePart_sub_le_base_mul_of_le_base_mul_one_add
      (Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
        hP hStruct hP4 m).le
      (terminalSpectralPositivePartAtScale_nonneg hP hStruct m Q a)
      (coarseBlockMatrix_upperLeft_matrixNorm_le_barSigma_mul_one_add_terminalSpectralPositivePartAtScale
        hP hStruct hP4 m Q a ha)

/--
Source labels `e.M.def` and `p.HC.CR`: one terminal block's lower matrix-norm
positive excess is controlled by the spectral positive part of the same
terminally normalized full-block fluctuation.
-/
theorem lowerRight_terminalPositiveExcess_le_barSigmaStar_inv_mul_terminalSpectralPositivePartAtScale
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.RegCoeffField d)
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a) :
    max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).lowerRight -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0 ≤
      (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ *
        terminalSpectralPositivePartAtScale hP hStruct m Q a := by
  exact
    positivePart_sub_le_base_mul_of_le_base_mul_one_add
      (Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_inv_pos_of_P4
        hP hStruct hP4 m).le
      (terminalSpectralPositivePartAtScale_nonneg hP hStruct m Q a)
      (coarseBlockMatrix_lowerRight_matrixNorm_le_barSigmaStar_inv_mul_one_add_terminalSpectralPositivePartAtScale
        hP hStruct hP4 m Q a ha)

/--
Source labels `e.M.def` and `p.HC.CR`: the weighted upper/lower terminal
matrix-norm positive excess on one block is bounded by the same block's
spectral positive part with the exact scalar terminal normalizer prefactor.
-/
theorem terminalMatrixPositiveExcessWeight_le_terminalNormalizer_mul_terminalSpectralPositivePartAtScale
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.RegCoeffField d)
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a) :
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let upperExcess : ℝ :=
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).upperLeft -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0
    let lowerExcess : ℝ :=
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).lowerRight -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0
    σ * lowerExcess + σ⁻¹ * upperExcess ≤
      (σ * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ +
          σ⁻¹ * hP.barSigmaAtScale hStruct (m : ℤ)) *
        terminalSpectralPositivePartAtScale hP hStruct m Q a := by
  dsimp only
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let spec := terminalSpectralPositivePartAtScale hP hStruct m Q a
  let upperExcess : ℝ :=
    max
      (Homogenization.Book.Ch02.matrixNorm
          (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).upperLeft -
        hP.barSigmaAtScale hStruct (m : ℤ))
      0
  let lowerExcess : ℝ :=
    max
      (Homogenization.Book.Ch02.matrixNorm
          (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).lowerRight -
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
      0
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, Homogenization.Book.Ch05.sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hlower :
      lowerExcess ≤
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ * spec := by
    simpa [lowerExcess, spec] using
      lowerRight_terminalPositiveExcess_le_barSigmaStar_inv_mul_terminalSpectralPositivePartAtScale
        hP hStruct hP4 m Q a ha
  have hupper :
      upperExcess ≤ hP.barSigmaAtScale hStruct (m : ℤ) * spec := by
    simpa [upperExcess, spec] using
      upperLeft_terminalPositiveExcess_le_barSigma_mul_terminalSpectralPositivePartAtScale
        hP hStruct hP4 m Q a ha
  calc
    σ * lowerExcess + σ⁻¹ * upperExcess
        ≤
          σ * ((hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ * spec) +
            σ⁻¹ * (hP.barSigmaAtScale hStruct (m : ℤ) * spec) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hlower hσ_nonneg)
            (mul_le_mul_of_nonneg_left hupper hσ_inv_nonneg)
    _ =
        (σ * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ +
            σ⁻¹ * hP.barSigmaAtScale hStruct (m : ℤ)) * spec := by
          ring

/--
Source labels `e.M.def` and `p.HC.CR`: exact terminal scalar normalizer.
This is the faithful terminal normalizer `2 * sqrt(theta_m)` before weakening
it to `2 * (1 + F_m)`.
-/
theorem terminalPositiveExcessNormalizer_eq_two_mul_sqrt_thetaAtScale_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) :
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    σ * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ +
        σ⁻¹ * hP.barSigmaAtScale hStruct (m : ℤ) =
      2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) := by
  dsimp only
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let θ := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
  let bm := hP.barSigmaAtScale hStruct (m : ℤ)
  let cm := hP.barSigmaStarAtScale hStruct (m : ℤ)
  have hbm_pos : 0 < bm := by
    simpa [bm] using
      Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
        hP hStruct hP4 m
  have hcm_pos : 0 < cm := by
    simpa [cm] using
      Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
        hP hStruct hP4 m
  have hsqrt_star :
      σ * cm⁻¹ = Real.sqrt θ := by
    simpa [σ, θ, bm, cm] using
      Homogenization.Book.Ch05.Section54.GoodScale.sigma_mul_inv_star_eq_sqrt_theta
        hbm_pos hcm_pos (by rfl) (by rfl)
  have hsqrt_bar :
      bm * σ⁻¹ = Real.sqrt θ := by
    simpa [σ, θ, bm, cm] using
      Homogenization.Book.Ch05.Section54.GoodScale.barSigma_mul_inv_sigma_eq_sqrt_theta
        hbm_pos hcm_pos (by rfl) (by rfl)
  have hsqrt_bar' :
      σ⁻¹ * bm = Real.sqrt θ := by
    rw [mul_comm, hsqrt_bar]
  rw [hsqrt_star, hsqrt_bar']
  ring

/--
Source labels `e.M.def` and `p.HC.CR`: the weighted terminal upper/lower
matrix-norm positive excess on one block is bounded by the terminal spectral
positive part with the sharper faithful terminal normalizer `2 * sqrt(theta_m)`.
-/
theorem terminalMatrixPositiveExcessWeight_le_two_mul_sqrt_thetaAtScale_mul_terminalSpectralPositivePartAtScale
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.RegCoeffField d)
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a) :
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let upperExcess : ℝ :=
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).upperLeft -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0
    let lowerExcess : ℝ :=
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).lowerRight -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0
    σ * lowerExcess + σ⁻¹ * upperExcess ≤
      2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
        terminalSpectralPositivePartAtScale hP hStruct m Q a := by
  dsimp only
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let upperExcess : ℝ :=
    max
      (Homogenization.Book.Ch02.matrixNorm
          (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).upperLeft -
        hP.barSigmaAtScale hStruct (m : ℤ))
      0
  let lowerExcess : ℝ :=
    max
      (Homogenization.Book.Ch02.matrixNorm
          (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a).lowerRight -
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
      0
  let spec := terminalSpectralPositivePartAtScale hP hStruct m Q a
  have hweight :
      σ * lowerExcess + σ⁻¹ * upperExcess ≤
        (σ * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ +
            σ⁻¹ * hP.barSigmaAtScale hStruct (m : ℤ)) * spec := by
    simpa [σ, upperExcess, lowerExcess, spec] using
      terminalMatrixPositiveExcessWeight_le_terminalNormalizer_mul_terminalSpectralPositivePartAtScale
        hP hStruct hP4 m Q a ha
  have hnormalizer :
      σ * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ +
          σ⁻¹ * hP.barSigmaAtScale hStruct (m : ℤ) ≤
        2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) := by
    have hnormalizer_eq :
        σ * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ +
            σ⁻¹ * hP.barSigmaAtScale hStruct (m : ℤ) =
          2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) := by
      simpa [σ] using
        terminalPositiveExcessNormalizer_eq_two_mul_sqrt_thetaAtScale_of_P4
          hP hStruct hP4 m
    exact hnormalizer_eq.le
  have hspec_nonneg : 0 ≤ spec := by
    simpa [spec] using terminalSpectralPositivePartAtScale_nonneg hP hStruct m Q a
  exact hweight.trans (mul_le_mul_of_nonneg_right hnormalizer hspec_nonneg)

/--
Source label `e.M.def`: the high-scale part of the manuscript bad maximal
observable as an ENNReal finite maximum over `N <= j <= m` and terminal
descendants of `Q`.
-/
noncomputable def terminalSpectralPositivePartSourceEnvelope
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hc : HighContrastExponents d) (N m : ℕ)
    (Q : Homogenization.TriadicCube d)
    (a : Ω → Homogenization.RegCoeffField d) : Ω → ENNReal :=
  fun ω => (Finset.Icc N m).sup
    (fun j => (Homogenization.descendantsAtDepth Q (m - j)).sup
      (fun R =>
        ENNReal.ofReal
          ((terminalStochasticWeakWeight (d := d) hc m j R).toReal *
            terminalSpectralPositivePartAtScale hP hStruct m R (a ω))))

/--
Source label `e.M.def`: real-valued high-scale spectral positive-part
maximal observable.
-/
noncomputable def terminalSpectralPositivePartSourceMax
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hc : HighContrastExponents d) (N m : ℕ)
    (Q : Homogenization.TriadicCube d)
    (a : Ω → Homogenization.RegCoeffField d) : Ω → ℝ :=
  fun ω =>
    (terminalSpectralPositivePartSourceEnvelope hP hStruct hc N m Q a ω).toReal

/--
Finite-sup measurability of the literal source envelope, assuming
measurability of each terminal spectral positive-part scale term.

This isolates the remaining analytic input: measurability of
`terminalSpectralPositivePartAtScale`, i.e. the CFC positive-part norm applied
to the library's measurable normalized fluctuation matrix.
-/
theorem aemeasurable_terminalSpectralPositivePartSourceEnvelope_of_aemeasurable_terminalSpectralPositivePartAtScale
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hc : HighContrastExponents d) (N m : ℕ)
    (Q : Homogenization.TriadicCube d)
    (a : Ω → Homogenization.RegCoeffField d)
    (hterm :
      ∀ (j : ℕ), j ∈ Finset.Icc N m →
        ∀ R ∈ Homogenization.descendantsAtDepth Q (m - j),
          AEMeasurable
            (fun ω =>
              terminalSpectralPositivePartAtScale hP hStruct m R (a ω)) μ) :
    AEMeasurable
      (terminalSpectralPositivePartSourceEnvelope hP hStruct hc N m Q a) μ := by
  classical
  change AEMeasurable
    (fun ω => (Finset.Icc N m).sup
      (fun j => (Homogenization.descendantsAtDepth Q (m - j)).sup
        (fun R =>
          ENNReal.ofReal
            ((terminalStochasticWeakWeight (d := d) hc m j R).toReal *
              terminalSpectralPositivePartAtScale hP hStruct m R (a ω))))) μ
  refine aemeasurable_finset_sup_ennreal (Finset.Icc N m) _ ?_
  intro j hj
  refine aemeasurable_finset_sup_ennreal
    (Homogenization.descendantsAtDepth Q (m - j)) _ ?_
  intro R hR
  have hspec :
      AEMeasurable
        (fun ω => terminalSpectralPositivePartAtScale hP hStruct m R (a ω)) μ :=
    hterm j hj R hR
  have hweighted :
      AEMeasurable
        (fun ω =>
          (terminalStochasticWeakWeight (d := d) hc m j R).toReal *
            terminalSpectralPositivePartAtScale hP hStruct m R (a ω)) μ := by
    simpa [mul_comm] using
      hspec.const_mul ((terminalStochasticWeakWeight (d := d) hc m j R).toReal)
  exact hweighted.ennreal_ofReal

/--
Finite-sup measurability of the real-valued literal source maximum, assuming
measurability of each terminal spectral positive-part scale term.
-/
theorem aestronglyMeasurable_terminalSpectralPositivePartSourceMax_of_aemeasurable_terminalSpectralPositivePartAtScale
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hc : HighContrastExponents d) (N m : ℕ)
    (Q : Homogenization.TriadicCube d)
    (a : Ω → Homogenization.RegCoeffField d)
    (hterm :
      ∀ (j : ℕ), j ∈ Finset.Icc N m →
        ∀ R ∈ Homogenization.descendantsAtDepth Q (m - j),
          AEMeasurable
            (fun ω =>
              terminalSpectralPositivePartAtScale hP hStruct m R (a ω)) μ) :
    AEStronglyMeasurable
      (terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a) μ := by
  exact
    ((aemeasurable_terminalSpectralPositivePartSourceEnvelope_of_aemeasurable_terminalSpectralPositivePartAtScale
      hP hStruct hc N m Q a hterm).ennreal_toReal).aestronglyMeasurable

theorem aestronglyMeasurable_terminalSpectralPositivePartSourceMax_origin
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hc : HighContrastExponents d) (N m : ℕ) :
    AEStronglyMeasurable
      (terminalSpectralPositivePartSourceMax hP hStruct hc N m
        (Homogenization.originCube d (m : ℤ))
        (fun x : Homogenization.RegCoeffField d => x)) P := by
  refine
    aestronglyMeasurable_terminalSpectralPositivePartSourceMax_of_aemeasurable_terminalSpectralPositivePartAtScale
      hP hStruct hc N m (Homogenization.originCube d (m : ℤ))
      (fun x : Homogenization.RegCoeffField d => x) ?_
  intro _j _hj R _hR
  exact aemeasurable_terminalSpectralPositivePartAtScale hP hStruct m R

theorem terminalSpectralPositivePartSourceMax_nonneg
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hc : HighContrastExponents d) (N m : ℕ)
    (Q : Homogenization.TriadicCube d)
    (a : Ω → Homogenization.RegCoeffField d) :
    ∀ ω, 0 ≤ terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a ω := by
  intro ω
  dsimp [terminalSpectralPositivePartSourceMax]
  exact ENNReal.toReal_nonneg

/-- The finite ENNReal source envelope is never `⊤`. -/
theorem terminalSpectralPositivePartSourceEnvelope_ne_top
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hc : HighContrastExponents d) (N m : ℕ)
    (Q : Homogenization.TriadicCube d)
    (a : Ω → Homogenization.RegCoeffField d) (ω : Ω) :
    terminalSpectralPositivePartSourceEnvelope hP hStruct hc N m Q a ω ≠ ⊤ := by
  classical
  intro htop
  dsimp [terminalSpectralPositivePartSourceEnvelope] at htop
  rw [Finset.sup_eq_top_iff] at htop
  rcases htop with ⟨i, hi, hinner_top⟩
  rw [Finset.sup_eq_top_iff] at hinner_top
  rcases hinner_top with ⟨R, hR, hofReal_top⟩
  exact ENNReal.ofReal_ne_top hofReal_top

/--
Source label `e.M.def`: enlarging the source window can only increase the
terminal spectral positive-part ENNReal envelope.
-/
theorem terminalSpectralPositivePartSourceEnvelope_le_of_start_le
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hc : HighContrastExponents d) {N k m : ℕ}
    (hNk : N ≤ k)
    (Q : Homogenization.TriadicCube d)
    (a : Ω → Homogenization.RegCoeffField d) (ω : Ω) :
    terminalSpectralPositivePartSourceEnvelope hP hStruct hc k m Q a ω ≤
      terminalSpectralPositivePartSourceEnvelope hP hStruct hc N m Q a ω := by
  classical
  dsimp [terminalSpectralPositivePartSourceEnvelope]
  refine Finset.sup_le ?_
  intro j hj
  have hj_bounds := Finset.mem_Icc.mp hj
  have hj_global : j ∈ Finset.Icc N m :=
    Finset.mem_Icc.mpr ⟨hNk.trans hj_bounds.1, hj_bounds.2⟩
  exact Finset.le_sup
    (s := Finset.Icc N m)
    (f := fun i =>
      (Homogenization.descendantsAtDepth Q (m - i)).sup
        (fun R =>
          ENNReal.ofReal
            ((terminalStochasticWeakWeight (d := d) hc m i R).toReal *
              terminalSpectralPositivePartAtScale hP hStruct m R (a ω))))
    hj_global

/--
Source label `e.M.def`: the real-valued source maximum is monotone in the
lower endpoint of the finite source window.
-/
theorem terminalSpectralPositivePartSourceMax_le_of_start_le
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hc : HighContrastExponents d) {N k m : ℕ}
    (hNk : N ≤ k)
    (Q : Homogenization.TriadicCube d)
    (a : Ω → Homogenization.RegCoeffField d) (ω : Ω) :
    terminalSpectralPositivePartSourceMax hP hStruct hc k m Q a ω ≤
      terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a ω := by
  dsimp [terminalSpectralPositivePartSourceMax]
  exact ENNReal.toReal_mono
    (terminalSpectralPositivePartSourceEnvelope_ne_top
      hP hStruct hc N m Q a ω)
    (terminalSpectralPositivePartSourceEnvelope_le_of_start_le
      hP hStruct hc hNk Q a ω)

/-- The bad-event truncation is monotone pointwise. -/
theorem badEventTruncation_mono
    {Ω : Type*} {M M' : Ω → ℝ} {ω : Ω}
    (hMM' : M ω ≤ M' ω) :
    badEventTruncation M ω ≤ badEventTruncation M' ω := by
  by_cases hbad : 1 < M ω
  · have hbad' : 1 < M' ω := hbad.trans_le hMM'
    simp [badEventTruncation, hbad, hbad', hMM']
  · by_cases hbad' : 1 < M' ω
    · simp [badEventTruncation, hbad, hbad']
      linarith
    · simp [badEventTruncation, hbad, hbad']

/--
Source label `e.M.def`: the bad-event truncation of the local source window is
bounded by the bad-event truncation of any enlarged source window.
-/
theorem badEventTruncation_terminalSpectralPositivePartSourceMax_le_of_start_le
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hc : HighContrastExponents d) {N k m : ℕ}
    (hNk : N ≤ k)
    (Q : Homogenization.TriadicCube d)
    (a : Ω → Homogenization.RegCoeffField d) (ω : Ω) :
    badEventTruncation
        (terminalSpectralPositivePartSourceMax hP hStruct hc k m Q a) ω ≤
      badEventTruncation
        (terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a) ω := by
  exact badEventTruncation_mono
    (terminalSpectralPositivePartSourceMax_le_of_start_le
      hP hStruct hc hNk Q a ω)

/--
Source label `e.M.def`: any weighted terminal spectral positive part appearing
in the manuscript finite source maximum is bounded by that maximum.
-/
theorem weighted_terminalSpectralPositivePartAtScale_le_terminalSpectralPositivePartSourceMax
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hc : HighContrastExponents d) {N m j : ℕ}
    (Q : Homogenization.TriadicCube d)
    (a : Ω → Homogenization.RegCoeffField d) (ω : Ω)
    {R : Homogenization.TriadicCube d}
    (hj : j ∈ Finset.Icc N m)
    (hR : R ∈ Homogenization.descendantsAtDepth Q (m - j)) :
    (terminalStochasticWeakWeight (d := d) hc m j R).toReal *
        terminalSpectralPositivePartAtScale hP hStruct m R (a ω) ≤
      terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a ω := by
  classical
  let weak : ℕ → Homogenization.TriadicCube d → ENNReal :=
    terminalStochasticWeakWeight (d := d) hc m
  let spec : Homogenization.TriadicCube d → ENNReal :=
    fun S =>
      ENNReal.ofReal
        ((weak j S).toReal *
          terminalSpectralPositivePartAtScale hP hStruct m S (a ω))
  let env :=
    terminalSpectralPositivePartSourceEnvelope hP hStruct hc N m Q a
  have hinner :
      spec R ≤ (Homogenization.descendantsAtDepth Q (m - j)).sup spec := by
    exact Finset.le_sup
      (s := Homogenization.descendantsAtDepth Q (m - j)) (f := spec) hR
  have hterm : spec R ≤ env ω := by
    have houter :
        (Homogenization.descendantsAtDepth Q (m - j)).sup spec ≤ env ω := by
      dsimp [env, terminalSpectralPositivePartSourceEnvelope, spec, weak]
      exact Finset.le_sup
        (s := Finset.Icc N m)
        (f := fun i =>
          (Homogenization.descendantsAtDepth Q (m - i)).sup
            (fun S =>
              ENNReal.ofReal
                ((terminalStochasticWeakWeight (d := d) hc m i S).toReal *
                  terminalSpectralPositivePartAtScale hP hStruct m S (a ω))))
        hj
    exact hinner.trans houter
  have henv_ne_top : env ω ≠ ⊤ := by
    intro htop
    dsimp [env, terminalSpectralPositivePartSourceEnvelope]
      at htop
    rw [Finset.sup_eq_top_iff] at htop
    rcases htop with ⟨i, hi, hinner_top⟩
    rw [Finset.sup_eq_top_iff] at hinner_top
    rcases hinner_top with ⟨S, hS, hofReal_top⟩
    exact ENNReal.ofReal_ne_top hofReal_top
  have htoReal :
      (spec R).toReal ≤ (env ω).toReal :=
    ENNReal.toReal_mono henv_ne_top hterm
  have harg_nonneg :
      0 ≤ (weak j R).toReal *
        terminalSpectralPositivePartAtScale hP hStruct m R (a ω) := by
    exact mul_nonneg ENNReal.toReal_nonneg
      (terminalSpectralPositivePartAtScale_nonneg hP hStruct m R (a ω))
  have hspec_toReal :
      (spec R).toReal =
        (weak j R).toReal *
          terminalSpectralPositivePartAtScale hP hStruct m R (a ω) := by
    dsimp [spec]
    exact ENNReal.toReal_ofReal harg_nonneg
  change
    (weak j R).toReal *
        terminalSpectralPositivePartAtScale hP hStruct m R (a ω) ≤
      (env ω).toReal
  rw [← hspec_toReal]
  exact htoReal

/--
Source labels `e.M.def` and `p.HC.CR`: faithful weighted terminal
matrix-norm positive-excess slot selected in the manuscript source maximum.
This is the same source-max selection as
`weighted_terminalMatrixPositiveExcessWeight_le_two_mul_one_add_contrastExcessAtScale_mul_terminalSpectralPositivePartSourceMax`,
but it keeps the terminal lower-edge normalizer as `2 * sqrt(theta_m)`.
-/
theorem weighted_terminalMatrixPositiveExcessWeight_le_two_mul_sqrt_thetaAtScale_mul_terminalSpectralPositivePartSourceMax
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {N m j : ℕ}
    (Q : Homogenization.TriadicCube d)
    (a : Ω → Homogenization.RegCoeffField d) (ω : Ω)
    {R : Homogenization.TriadicCube d}
    (hj : j ∈ Finset.Icc N m)
    (hR : R ∈ Homogenization.descendantsAtDepth Q (m - j))
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField (a ω)) :
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let upperExcess : ℝ :=
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).upperLeft -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0
    let lowerExcess : ℝ :=
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).lowerRight -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0
    (terminalStochasticWeakWeight (d := d) hc m j R).toReal *
        (σ * lowerExcess + σ⁻¹ * upperExcess) ≤
      2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
        terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a ω := by
  dsimp only
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let upperExcess : ℝ :=
    max
      (Homogenization.Book.Ch02.matrixNorm
          (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).upperLeft -
        hP.barSigmaAtScale hStruct (m : ℤ))
      0
  let lowerExcess : ℝ :=
    max
      (Homogenization.Book.Ch02.matrixNorm
          (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).lowerRight -
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
      0
  let w : ℝ := (terminalStochasticWeakWeight (d := d) hc m j R).toReal
  let spec : ℝ := terminalSpectralPositivePartAtScale hP hStruct m R (a ω)
  let source : ℝ := terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a ω
  let T : ℝ := 2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))
  have hw_nonneg : 0 ≤ w := by
    dsimp [w]
    exact ENNReal.toReal_nonneg
  have hblock :
      σ * lowerExcess + σ⁻¹ * upperExcess ≤ T * spec := by
    simpa [σ, upperExcess, lowerExcess, spec, T] using
      terminalMatrixPositiveExcessWeight_le_two_mul_sqrt_thetaAtScale_mul_terminalSpectralPositivePartAtScale
        hP hStruct hP4 m R (a ω) ha
  have hsource : w * spec ≤ source := by
    simpa [w, spec, source] using
      weighted_terminalSpectralPositivePartAtScale_le_terminalSpectralPositivePartSourceMax
        hP hStruct hc Q a ω hj hR
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  calc
    w * (σ * lowerExcess + σ⁻¹ * upperExcess)
        ≤ w * (T * spec) := mul_le_mul_of_nonneg_left hblock hw_nonneg
    _ = T * (w * spec) := by ring
    _ ≤ T * source := mul_le_mul_of_nonneg_left hsource hT_nonneg
    _ =
      2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
        source := by rfl

end

end Homogenization.HighContrast.EntryScale
