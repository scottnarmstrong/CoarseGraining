import Homogenization.Book.Ch04.Theorems.Expectations
import Homogenization.Book.Ch04.Theorems.Scalarization
import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
import Homogenization.CoarseGraining.Translation
import Homogenization.Probability.LocalObservable

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Stationary response expectations

This file is the public Chapter 4 surface for the stationarity step used by
the expectation/moment arguments: at nonnegative scales, deterministic child
cubes are integer translates of the origin cube at the same scale, so
stationarity identifies their annealed response expectations.

The statements are phrased directly in terms of the clean response expectation
objects from `Expectations.lean`.
-/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise

/-- Integer shift taking a nonnegative-scale origin cube to a cube at the same
scale. -/
def scaleTranslationShift {d : ℕ} (k : ℤ) (R : TriadicCube d) : Fin d → ℤ :=
  fun i => Int.ofNat (3 ^ Int.toNat k) * R.index i

/-- At nonnegative scale, every triadic cube is an integer translate of the
origin cube at the same scale. -/
theorem cubeSet_eq_translateSet_originCube_of_nonneg_scale {d : ℕ}
    {R : TriadicCube d} (hk : 0 ≤ R.scale) :
    cubeSet R =
      translateSet (intVecToRealVec (scaleTranslationShift R.scale R))
        (cubeSet (originCube d R.scale)) := by
  calc
    cubeSet R =
        translateSet (fun i => (R.index i : ℝ) * cubeScaleFactor R)
          (cubeSet (originCube d R.scale)) :=
      cubeSet_eq_translateSet_originCube_of_triadicCube R
    _ =
        translateSet (intVecToRealVec (scaleTranslationShift R.scale R))
          (cubeSet (originCube d R.scale)) := by
          congr 1
          funext i
          have hpow :
              (((Int.ofNat (3 ^ Int.toNat R.scale) : ℤ) : ℝ)) = cubeScaleFactor R := by
            calc
              (((Int.ofNat (3 ^ Int.toNat R.scale) : ℤ) : ℝ))
                  = (((3 ^ Int.toNat R.scale : ℕ) : ℝ)) := by
                      simp
              _ = (3 : ℝ) ^ Int.toNat R.scale := by
                    simp [Nat.cast_pow]
              _ = (3 : ℝ) ^ R.scale := by
                    symm
                    calc
                      (3 : ℝ) ^ R.scale = (3 : ℝ) ^ ((Int.toNat R.scale : ℤ)) := by
                        rw [Int.toNat_of_nonneg hk]
                      _ = (3 : ℝ) ^ Int.toNat R.scale := by
                        rw [zpow_natCast]
              _ = cubeScaleFactor R := by
                    simp [cubeScaleFactor]
          calc
            (R.index i : ℝ) * cubeScaleFactor R
                = (R.index i : ℝ) *
                    (((Int.ofNat (3 ^ Int.toNat R.scale) : ℤ) : ℝ)) := by
                      rw [hpow.symm]
            _ = (((Int.ofNat (3 ^ Int.toNat R.scale) : ℤ) : ℝ)) *
                  (R.index i : ℝ) := by
                    ring
            _ = intVecToRealVec (scaleTranslationShift R.scale R) i := by
                    simp [intVecToRealVec, scaleTranslationShift]

/-- Descendants of the origin cube at a fixed scale have that scale. -/
theorem scale_eq_of_mem_descendantsAtScale_originCube {d : ℕ}
    {n m : ℤ} {R : TriadicCube d} (hnm : n ≤ m)
    (hR : R ∈ descendantsAtScale (originCube d m) n) :
    R.scale = n := by
  calc
    R.scale = (originCube d m).scale - Int.toNat ((originCube d m).scale - n) := by
      exact scale_eq_sub_of_mem_descendantsAtScale (Q := originCube d m) hnm hR
    _ = m - Int.toNat (m - n) := by
      rfl
    _ = n := by
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hnm)]
      ring

/-- A descendant of a nonnegative-scale origin cube is an integer translate of
the origin cube at the descendant scale. -/
theorem cubeSet_eq_translateSet_originCube_of_mem_descendantsAtScale_originCube
    {d : ℕ} {n m : ℤ} {R : TriadicCube d} (hn : 0 ≤ n) (hnm : n ≤ m)
    (hR : R ∈ descendantsAtScale (originCube d m) n) :
    cubeSet R =
      translateSet (intVecToRealVec (scaleTranslationShift n R))
        (cubeSet (originCube d n)) := by
  have hscaleR : R.scale = n :=
    scale_eq_of_mem_descendantsAtScale_originCube hnm hR
  have hscale_nonneg : 0 ≤ R.scale := by
    simpa [hscaleR] using hn
  calc
    cubeSet R =
        translateSet (intVecToRealVec (scaleTranslationShift R.scale R))
          (cubeSet (originCube d R.scale)) :=
      cubeSet_eq_translateSet_originCube_of_nonneg_scale hscale_nonneg
    _ =
        translateSet (intVecToRealVec (scaleTranslationShift n R))
          (cubeSet (originCube d n)) := by
        simp [hscaleR]

/-- Scalar response is translation-covariant as a set-indexed coefficient-field
observable. -/
theorem responseJCubeSet_translation_covariant {d : ℕ} (p q : Vec d) :
    IsTranslationCovariant
      (fun U : Set (Vec d) => fun a : CoeffField d => ResponseJ U p q a) := by
  intro U z a
  simpa [translateByInt] using
    ResponseJ_translateSet_eq_translateCoeffField (intVecToRealVec z) U p q a

/-- Coarse block matrix entries are translation-covariant as set-indexed
coefficient-field observables. -/
theorem coarseBlockMatrix_entry_translation_covariant {d : ℕ}
    (α β : BlockCoord d) :
    IsTranslationCovariant
      (fun U : Set (Vec d) => fun a : CoeffField d =>
        blockMatEntry (coarseBlockMatrix U a) α β) := by
  intro U z a
  simpa [translateByInt] using
    congrArg (fun A : BlockMat d => blockMatEntry A α β)
      (coarseBlockMatrix_translateSet_eq_translateCoeffField
        (intVecToRealVec z) U a)

/-- Scalar block diagonal center used to normalize full-block fluctuations at a
structural-law scale.  The lower-right block is the inverse starred scalar. -/
noncomputable def scalarAnnealedBlockMatrixAtScale {d : ℕ} [NeZero d]
    {P : CoeffLaw d} (hP : LawCarrier P) (hStruct : StructuralLaw P)
    (m : ℤ) : BlockMat d :=
  Ch02.blockDiag
    (hP.barSigmaAtScale hStruct m • (1 : Mat d))
    ((hP.barSigmaStarAtScale hStruct m)⁻¹ • (1 : Mat d))

/-- Diagonal full-block normalization associated with scalar blocks `b,c`. -/
noncomputable def scalarFullBlockInvSqrtDiag {d : ℕ} (b c : ℝ) :
    BlockCoord d → ℝ
  | Sum.inl _ => (Real.sqrt b)⁻¹
  | Sum.inr _ => Real.sqrt c

/-- Manuscript normalized full-block fluctuation observable at center scale
`m`, written for an arbitrary deterministic set.  The norm is the Euclidean
operator norm of the associated full block matrix. -/
noncomputable def fullBlockNormalizedFluctuationOperatorNormSq
    {d : ℕ} [NeZero d] {P : CoeffLaw d}
    (hP : LawCarrier P) (hStruct : StructuralLaw P)
    (m : ℤ) (U : Set (Vec d)) (a : CoeffField d) : ℝ :=
  let b := hP.barSigmaAtScale hStruct m
  let c := hP.barSigmaStarAtScale hStruct m
  let D : FullBlockMat d := Matrix.diagonal (scalarFullBlockInvSqrtDiag b c)
  let A := coarseBlockMatrix U a
  let Abar := scalarAnnealedBlockMatrixAtScale hP hStruct m
  ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
      (D * (toFullBlockMat A - toFullBlockMat Abar) * D)‖ ^ 2

/-- Manuscript normalized full-block fluctuation observable on a triadic cube.
The norm is the Euclidean operator norm, not the Frobenius norm. -/
noncomputable def fullBlockNormalizedFluctuationOperatorNormSqAtScale
    {d : ℕ} [NeZero d] {P : CoeffLaw d}
    (hP : LawCarrier P) (hStruct : StructuralLaw P)
    (m : ℤ) (R : TriadicCube d) (a : CoeffField d) : ℝ :=
  fullBlockNormalizedFluctuationOperatorNormSq hP hStruct m (cubeSet R) a

/-- The normalized full-block fluctuation observable is translation-covariant
in its deterministic set argument. -/
theorem fullBlockNormalizedFluctuationOperatorNormSq_translation_covariant
    {d : ℕ} [NeZero d] {P : CoeffLaw d}
    (hP : LawCarrier P) (hStruct : StructuralLaw P) (m : ℤ) :
    IsTranslationCovariant
      (fun U : Set (Vec d) => fun a : CoeffField d =>
        fullBlockNormalizedFluctuationOperatorNormSq hP hStruct m U a) := by
  intro U z a
  simp [fullBlockNormalizedFluctuationOperatorNormSq, translateByInt,
    coarseBlockMatrix_translateSet_eq_translateCoeffField]

namespace LawCarrier

/-- Under stationarity, the annealed response on a nonnegative-scale cube is
the annealed response on the origin cube at the same scale. -/
theorem expectedResponseJCubeSet_eq_originCube_of_stationary
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hstat : StationaryLaw P) (R : TriadicCube d) (hR_nonneg : 0 ≤ R.scale)
    (p q : Vec d) :
    expectedResponseJCubeSet P R p q =
      expectedResponseJCubeSet P (originCube d R.scale) p q := by
  have hshift :=
    cubeSet_eq_translateSet_originCube_of_nonneg_scale (R := R) hR_nonneg
  calc
    expectedResponseJCubeSet P R p q
        = ∫ a, ResponseJ (cubeSet R) p q a ∂P := by
          rfl
    _ =
        ∫ a,
          ResponseJ
            (translateSet (intVecToRealVec (scaleTranslationShift R.scale R))
              (cubeSet (originCube d R.scale))) p q a ∂P := by
          rw [hshift]
    _ = ∫ a, ResponseJ (cubeSet (originCube d R.scale)) p q a ∂P := by
          exact
            integral_eq_of_isTranslationCovariant_of_isStationary_aestronglyMeasurable
              (P := P) hstat
              (U := cubeSet (originCube d R.scale))
              (by
                simpa [responseJObservableCubeSet] using
                  hP.aestronglyMeasurable_responseJObservableCubeSet
                    (originCube d R.scale) p q)
              (responseJCubeSet_translation_covariant p q)
              (scaleTranslationShift R.scale R)
    _ = expectedResponseJCubeSet P (originCube d R.scale) p q := by
          rfl

/-- Under stationarity, every coarse block matrix entry on a nonnegative-scale
cube has the same expectation as the corresponding origin-cube entry. -/
theorem integral_coarseBlockMatrix_entry_cubeSet_eq_originCube_of_stationary
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hstat : StationaryLaw P) (R : TriadicCube d) (hR_nonneg : 0 ≤ R.scale)
    (α β : BlockCoord d) :
    ∫ a, blockMatEntry (coarseBlockMatrix (cubeSet R) a) α β ∂P =
      ∫ a,
        blockMatEntry (coarseBlockMatrix (cubeSet (originCube d R.scale)) a) α β ∂P := by
  have hshift :=
    cubeSet_eq_translateSet_originCube_of_nonneg_scale (R := R) hR_nonneg
  have hmeas :
      AEStronglyMeasurable
        (fun a : CoeffField d =>
          blockMatEntry (coarseBlockMatrix (cubeSet (originCube d R.scale)) a) α β) P := by
    cases α with
    | inl i =>
        cases β with
        | inl j =>
            simpa [blockMatEntry] using
              (hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet
                (originCube d R.scale) i j).aestronglyMeasurable
        | inr j =>
            simpa [blockMatEntry] using
              (hP.aemeasurable_coarseBlockMatrix_upperRight_apply_cubeSet
                (originCube d R.scale) i j).aestronglyMeasurable
    | inr i =>
        cases β with
        | inl j =>
            simpa [blockMatEntry] using
              (hP.aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet
                (originCube d R.scale) i j).aestronglyMeasurable
        | inr j =>
            simpa [blockMatEntry] using
              (hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet
                (originCube d R.scale) i j).aestronglyMeasurable
  calc
    ∫ a, blockMatEntry (coarseBlockMatrix (cubeSet R) a) α β ∂P
        =
      ∫ a,
        blockMatEntry
          (coarseBlockMatrix
            (translateSet (intVecToRealVec (scaleTranslationShift R.scale R))
              (cubeSet (originCube d R.scale))) a) α β ∂P := by
          rw [hshift]
    _ =
      ∫ a,
        blockMatEntry (coarseBlockMatrix (cubeSet (originCube d R.scale)) a) α β ∂P := by
          exact
            integral_eq_of_isTranslationCovariant_of_isStationary_aestronglyMeasurable
              (P := P) hstat
              (U := cubeSet (originCube d R.scale)) hmeas
              (coarseBlockMatrix_entry_translation_covariant α β)
              (scaleTranslationShift R.scale R)

/-- Under stationarity, a child cube of an origin cube has the same annealed
response as the origin cube at the child scale. -/
theorem expectedResponseJCubeSet_eq_originCube_of_mem_descendantsAtScale_originCube
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hstat : StationaryLaw P) {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d m) n)
    (p q : Vec d) :
    expectedResponseJCubeSet P R p q =
      expectedResponseJCubeSet P (originCube d n) p q := by
  have hscale : R.scale = n :=
    scale_eq_of_mem_descendantsAtScale_originCube hnm hR
  have hR_nonneg : 0 ≤ R.scale := by
    simpa [hscale] using hn
  calc
    expectedResponseJCubeSet P R p q =
        expectedResponseJCubeSet P (originCube d R.scale) p q :=
      hP.expectedResponseJCubeSet_eq_originCube_of_stationary hstat R hR_nonneg p q
    _ = expectedResponseJCubeSet P (originCube d n) p q := by
      rw [hscale]

/-- Under stationarity, every coarse block matrix entry on a child cube of an
origin cube has the same expectation as the corresponding origin-cube entry at
the child scale. -/
theorem integral_coarseBlockMatrix_entry_cubeSet_eq_originCube_of_mem_descendantsAtScale_originCube
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hstat : StationaryLaw P) {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d m) n)
    (α β : BlockCoord d) :
    ∫ a, blockMatEntry (coarseBlockMatrix (cubeSet R) a) α β ∂P =
      ∫ a, blockMatEntry (coarseBlockMatrix (cubeSet (originCube d n)) a) α β ∂P := by
  have hscale : R.scale = n :=
    scale_eq_of_mem_descendantsAtScale_originCube hnm hR
  have hR_nonneg : 0 ≤ R.scale := by
    simpa [hscale] using hn
  calc
    ∫ a, blockMatEntry (coarseBlockMatrix (cubeSet R) a) α β ∂P
        =
      ∫ a,
        blockMatEntry (coarseBlockMatrix (cubeSet (originCube d R.scale)) a) α β ∂P :=
        hP.integral_coarseBlockMatrix_entry_cubeSet_eq_originCube_of_stationary
          hstat R hR_nonneg α β
    _ =
      ∫ a, blockMatEntry (coarseBlockMatrix (cubeSet (originCube d n)) a) α β ∂P := by
        rw [hscale]

/-- Under stationarity, the normalized full-block fluctuation on a
nonnegative-scale cube has the same expectation as the corresponding
origin-cube fluctuation.  The norm is the Euclidean operator norm of the full
block matrix. -/
theorem integral_fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq_originCube_of_stationary
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hstat : StationaryLaw P) (hStruct : StructuralLaw P) (center : ℤ)
    (R : TriadicCube d) (hR_nonneg : 0 ≤ R.scale)
    (hOrigin :
      Integrable
        (fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d R.scale)) P) :
    ∫ a, fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct center R a ∂P =
      ∫ a,
        fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d R.scale) a ∂P := by
  have hshift :=
    cubeSet_eq_translateSet_originCube_of_nonneg_scale (R := R) hR_nonneg
  calc
    ∫ a, fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct center R a ∂P
        =
      ∫ a,
        fullBlockNormalizedFluctuationOperatorNormSq hP hStruct center
          (translateSet (intVecToRealVec (scaleTranslationShift R.scale R))
            (cubeSet (originCube d R.scale))) a ∂P := by
          simp [fullBlockNormalizedFluctuationOperatorNormSqAtScale, hshift]
    _ =
      ∫ a,
        fullBlockNormalizedFluctuationOperatorNormSq hP hStruct center
          (cubeSet (originCube d R.scale)) a ∂P := by
          exact
            integral_eq_of_isTranslationCovariant_of_isStationary_aestronglyMeasurable
              (P := P) hstat
              (U := cubeSet (originCube d R.scale))
              (by
                simpa [fullBlockNormalizedFluctuationOperatorNormSqAtScale] using
                  hOrigin.aestronglyMeasurable)
              (fullBlockNormalizedFluctuationOperatorNormSq_translation_covariant
                hP hStruct center)
              (scaleTranslationShift R.scale R)
    _ =
      ∫ a,
        fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d R.scale) a ∂P := by
          rfl

/-- Under stationarity, integrability of the origin-cube normalized full-block
fluctuation transfers to every same-scale cube. -/
theorem integrable_fullBlockNormalizedFluctuationOperatorNormSqAtScale_of_stationary
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hstat : StationaryLaw P) (hStruct : StructuralLaw P) (center : ℤ)
    (R : TriadicCube d) (hR_nonneg : 0 ≤ R.scale)
    (hOrigin :
      Integrable
        (fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d R.scale)) P) :
    Integrable
      (fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct center R) P := by
  let z : Fin d → ℤ := scaleTranslationShift R.scale R
  have hset :
      cubeSet R =
        translateSet (intVecToRealVec z) (cubeSet (originCube d R.scale)) := by
    simpa [z] using
      cubeSet_eq_translateSet_originCube_of_nonneg_scale (R := R) hR_nonneg
  have hcomp :
      Integrable
        (fun a : CoeffField d =>
          fullBlockNormalizedFluctuationOperatorNormSq hP hStruct center
            (cubeSet (originCube d R.scale)) (translateByInt z a)) P := by
    have hOrigin_map :
        Integrable
          (fun a : CoeffField d =>
            fullBlockNormalizedFluctuationOperatorNormSq hP hStruct center
              (cubeSet (originCube d R.scale)) a)
          (Measure.map (translateByInt z) P) := by
      simpa [hstat z, fullBlockNormalizedFluctuationOperatorNormSqAtScale] using hOrigin
    simpa [Function.comp_def] using
      hOrigin_map.comp_measurable (measurable_translateByInt z)
  have hae :
      (fun a : CoeffField d =>
        fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct center R a) =ᵐ[P]
        fun a : CoeffField d =>
          fullBlockNormalizedFluctuationOperatorNormSq hP hStruct center
            (cubeSet (originCube d R.scale)) (translateByInt z a) := by
    filter_upwards with a
    rw [fullBlockNormalizedFluctuationOperatorNormSqAtScale, hset]
    exact
      fullBlockNormalizedFluctuationOperatorNormSq_translation_covariant
        hP hStruct center (cubeSet (originCube d R.scale)) z a
  exact hcomp.congr hae.symm

/-- Under stationarity, integrability of the origin-cube normalized full-block
fluctuation at the child scale transfers to descendants of a larger origin
cube. -/
theorem integrable_fullBlockNormalizedFluctuationOperatorNormSqAtScale_of_mem_descendantsAtScale_originCube
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hstat : StationaryLaw P) (hStruct : StructuralLaw P) (center : ℤ)
    {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d m) n)
    (hOrigin :
      Integrable
        (fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d n)) P) :
    Integrable
      (fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct center R) P := by
  have hscale : R.scale = n :=
    scale_eq_of_mem_descendantsAtScale_originCube hnm hR
  have hR_nonneg : 0 ≤ R.scale := by
    simpa [hscale] using hn
  exact
    hP.integrable_fullBlockNormalizedFluctuationOperatorNormSqAtScale_of_stationary
      hstat hStruct center R hR_nonneg (by simpa [hscale] using hOrigin)

/-- Under stationarity, the expectation of a descendant average of normalized
full-block fluctuation observables is the corresponding origin-cube
expectation at the descendant scale.  The observable uses the Euclidean
operator norm of the full block matrix. -/
theorem integral_descendantsAverage_fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq_originCube_of_stationary
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hstat : StationaryLaw P) (hStruct : StructuralLaw P) (center : ℤ)
    {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    (hOrigin :
      Integrable
        (fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d n)) P) :
    ∫ a,
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (fun R =>
            fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct center R a) ∂P =
      ∫ a,
        fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d n) a ∂P := by
  classical
  let Q : TriadicCube d := originCube d m
  let j : ℕ := Int.toNat (m - n)
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hDepth :
      ∀ R, R ∈ descendantsAtDepth Q j →
        Integrable
          (fullBlockNormalizedFluctuationOperatorNormSqAtScale
            hP hStruct center R) P := by
    intro R hR
    have hRscale : R ∈ descendantsAtScale (originCube d m) n := by
      simpa [Q, j, descendantsAtScale_eq_descendantsAtDepth (originCube d m) hnm] using hR
    exact
      hP.integrable_fullBlockNormalizedFluctuationOperatorNormSqAtScale_of_mem_descendantsAtScale_originCube
        hstat hStruct center hn hnm hRscale hOrigin
  calc
    ∫ a,
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (fun R =>
            fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct center R a) ∂P
        =
      descendantsAverage Q j
        (fun R =>
          ∫ a,
            fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct center R a ∂P) :=
        integral_descendantsAverage_eq_descendantsAverage_integral
          (P := P) (Q := Q) (j := j)
          (F := fun R a =>
            fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct center R a) hDepth
    _ =
      descendantsAverage Q j
        (fun _R =>
          ∫ a,
            fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct center (originCube d n) a ∂P) := by
        unfold descendantsAverage
        refine congrArg (fun t : ℝ => ((D.card : ℝ)⁻¹) * t) ?_
        refine Finset.sum_congr rfl ?_
        intro R hR
        have hRscale : R ∈ descendantsAtScale (originCube d m) n := by
          simpa [Q, j, descendantsAtScale_eq_descendantsAtDepth (originCube d m) hnm] using hR
        have hscale : R.scale = n :=
          scale_eq_of_mem_descendantsAtScale_originCube hnm hRscale
        have hR_nonneg : 0 ≤ R.scale := by
          simpa [hscale] using hn
        calc
          ∫ a,
              fullBlockNormalizedFluctuationOperatorNormSqAtScale
                hP hStruct center R a ∂P
              =
            ∫ a,
              fullBlockNormalizedFluctuationOperatorNormSqAtScale
                hP hStruct center (originCube d R.scale) a ∂P :=
              hP.integral_fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq_originCube_of_stationary
                hstat hStruct center R hR_nonneg (by simpa [hscale] using hOrigin)
          _ =
            ∫ a,
              fullBlockNormalizedFluctuationOperatorNormSqAtScale
                hP hStruct center (originCube d n) a ∂P := by
              rw [hscale]
    _ =
      ∫ a,
        fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d n) a ∂P := by
        simp [descendantsAverage_const]

/-- Full coarse-block integrability transfers from the origin cube at scale
`n` to every scale-`n` descendant of the origin cube at a larger scale.  This
is the stationarity source theorem for the descendant integrability hypotheses
in annealed subadditivity. -/
theorem integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (_hP : LawCarrier P)
    (hstat : StationaryLaw P) {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d m) n)
    (hOrigin : Integrable (coarseFullBlockMatrixAtCube (originCube d n)) P) :
    Integrable (coarseFullBlockMatrixAtCube R) P := by
  let z : Fin d → ℤ := scaleTranslationShift n R
  have hset :
      cubeSet R =
        translateSet (intVecToRealVec z) (cubeSet (originCube d n)) := by
    simpa [z] using
      cubeSet_eq_translateSet_originCube_of_mem_descendantsAtScale_originCube
        hn hnm hR
  refine MeasureTheory.Integrable.of_eval ?_
  intro α
  refine MeasureTheory.Integrable.of_eval ?_
  intro β
  have hOriginEntry :
      Integrable
        (fun a : CoeffField d =>
          blockMatEntry (coarseBlockMatrix (cubeSet (originCube d n)) a) α β) P := by
    have hα :
        Integrable (fun a : CoeffField d => coarseFullBlockMatrixAtCube (originCube d n) a α) P :=
      MeasureTheory.Integrable.eval hOrigin α
    have hαβ :
        Integrable
          (fun a : CoeffField d => coarseFullBlockMatrixAtCube (originCube d n) a α β) P :=
      MeasureTheory.Integrable.eval hα β
    simpa [coarseFullBlockMatrixAtCube, coarseFullBlockMatrixObservable, toFullBlockMat,
      blockMatEntry] using hαβ
  have hcomp :
      Integrable
        (fun a : CoeffField d =>
          blockMatEntry (coarseBlockMatrix (cubeSet (originCube d n)) (translateByInt z a))
            α β) P := by
    have hOriginEntry_map :
        Integrable
          (fun a : CoeffField d =>
            blockMatEntry (coarseBlockMatrix (cubeSet (originCube d n)) a) α β)
          (Measure.map (translateByInt z) P) := by
      simpa [hstat z] using hOriginEntry
    simpa [Function.comp_def] using
      hOriginEntry_map.comp_measurable (measurable_translateByInt z)
  have hae :
      (fun a : CoeffField d => blockMatEntry (coarseBlockMatrix (cubeSet R) a) α β) =ᵐ[P]
        fun a : CoeffField d =>
          blockMatEntry (coarseBlockMatrix (cubeSet (originCube d n)) (translateByInt z a))
            α β := by
    filter_upwards with a
    have hmat :
        coarseBlockMatrix (cubeSet R) a =
          coarseBlockMatrix (cubeSet (originCube d n)) (translateByInt z a) := by
      rw [hset, coarseBlockMatrix_translateSet_eq_translateCoeffField]
      rfl
    exact congrArg (fun A => blockMatEntry A α β) hmat
  have hentry := hcomp.congr hae.symm
  simpa [coarseFullBlockMatrixAtCube, coarseFullBlockMatrixObservable, toFullBlockMat,
    blockMatEntry] using hentry

/-- Under stationarity, the finite descendant average of child annealed
responses equals the annealed response on the origin cube at the child scale. -/
theorem expectedDescendantsAverageResponseJCubeSet_eq_originCube_of_stationary
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hstat : StationaryLaw P) {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    (p q : Vec d) :
    expectedDescendantsAverageResponseJCubeSet P (originCube d m)
        (Int.toNat (m - n)) p q =
      expectedResponseJCubeSet P (originCube d n) p q := by
  classical
  let D : Finset (TriadicCube d) :=
    descendantsAtDepth (originCube d m) (Int.toNat (m - n))
  have hDscale : D = descendantsAtScale (originCube d m) n := by
    simpa [D, originCube] using
      (descendantsAtScale_eq_descendantsAtDepth (originCube d m) hnm).symm
  have hD_nonempty : D.Nonempty := by
    simpa [D] using descendantsAtDepth_nonempty (originCube d m) (Int.toNat (m - n))
  have hcard_ne : ((D.card : ℝ) ≠ 0) := by
    exact_mod_cast Finset.card_ne_zero.mpr hD_nonempty
  calc
    expectedDescendantsAverageResponseJCubeSet P (originCube d m)
        (Int.toNat (m - n)) p q
        =
      (D.card : ℝ)⁻¹ *
        (∑ R ∈ D, expectedResponseJCubeSet P R p q) := by
          simp [expectedDescendantsAverageResponseJCubeSet, descendantsAverage, D]
    _ =
      (D.card : ℝ)⁻¹ *
        (∑ _R ∈ D, expectedResponseJCubeSet P (originCube d n) p q) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro R hR
          exact
            hP.expectedResponseJCubeSet_eq_originCube_of_mem_descendantsAtScale_originCube
              hstat hn hnm (by simpa [hDscale] using hR) p q
    _ = expectedResponseJCubeSet P (originCube d n) p q := by
          simp [Finset.sum_const, nsmul_eq_mul, hcard_ne]

/-- Under stationarity, the expectation of the finite descendant average of
response observables is the annealed response on the origin cube at the child
scale. -/
theorem integral_descendantsAverage_responseJObservableCubeSet_eq_originCube_of_stationary
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hstat : StationaryLaw P) {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    (p q : Vec d)
    (hJ : ∀ R, R ∈ descendantsAtScale (originCube d m) n →
      Integrable (responseJObservableCubeSet R p q) P) :
    ∫ a,
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (fun R => responseJObservableCubeSet R p q a) ∂P =
      expectedResponseJCubeSet P (originCube d n) p q := by
  have hJ_depth :
      ∀ R, R ∈ descendantsAtDepth (originCube d m) (Int.toNat (m - n)) →
        Integrable (responseJObservableCubeSet R p q) P := by
    intro R hR
    exact hJ R (by
      simpa [descendantsAtScale_eq_descendantsAtDepth (originCube d m) hnm] using hR)
  calc
    ∫ a,
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (fun R => responseJObservableCubeSet R p q a) ∂P
        =
      expectedDescendantsAverageResponseJCubeSet P (originCube d m)
        (Int.toNat (m - n)) p q :=
        integral_descendantsAverage_responseJObservableCubeSet_eq_expectedDescendantsAverageResponseJCubeSet
          (P := P) (Q := originCube d m) (j := Int.toNat (m - n)) p q hJ_depth
    _ = expectedResponseJCubeSet P (originCube d n) p q :=
        hP.expectedDescendantsAverageResponseJCubeSet_eq_originCube_of_stationary
          hstat hn hnm p q

/-- Weighted finite descendant response averages reduce to the average of the
deterministic weights times the origin-cube expectation under stationarity.

This is the source theorem for the cancellation step in Section 5.3: Ch5
supplies the cutoff weights and the scalar identity saying their finite
descendant average is zero. -/
theorem integral_weightedDescendantsAverage_responseJObservableCubeSet_eq_weight_average_mul_originCube_of_stationary
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hstat : StationaryLaw P) {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    (weight : TriadicCube d → ℝ) (p q : Vec d)
    (hJ : ∀ R, R ∈ descendantsAtScale (originCube d m) n →
      Integrable (responseJObservableCubeSet R p q) P) :
    ∫ a,
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (fun R => weight R * responseJObservableCubeSet R p q a) ∂P =
      descendantsAverage (originCube d m) (Int.toNat (m - n)) weight *
        expectedResponseJCubeSet P (originCube d n) p q := by
  classical
  let Q : TriadicCube d := originCube d m
  let j : ℕ := Int.toNat (m - n)
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hJ_depth :
      ∀ R, R ∈ descendantsAtDepth Q j →
        Integrable (fun a : CoeffField d =>
          weight R * responseJObservableCubeSet R p q a) P := by
    intro R hR
    have hRscale : R ∈ descendantsAtScale (originCube d m) n := by
      simpa [Q, j, descendantsAtScale_eq_descendantsAtDepth (originCube d m) hnm] using hR
    exact (hJ R hRscale).const_mul (weight R)
  calc
    ∫ a,
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (fun R => weight R * responseJObservableCubeSet R p q a) ∂P
        =
      descendantsAverage (originCube d m) (Int.toNat (m - n))
        (fun R => ∫ a, weight R * responseJObservableCubeSet R p q a ∂P) :=
        integral_descendantsAverage_eq_descendantsAverage_integral
          (P := P) (Q := Q) (j := j)
          (F := fun R a => weight R * responseJObservableCubeSet R p q a) hJ_depth
    _ =
      descendantsAverage (originCube d m) (Int.toNat (m - n))
        (fun R => weight R * expectedResponseJCubeSet P (originCube d n) p q) := by
        unfold descendantsAverage
        refine congrArg (fun t : ℝ => ((D.card : ℝ)⁻¹) * t) ?_
        refine Finset.sum_congr rfl ?_
        intro R hR
        have hRscale : R ∈ descendantsAtScale (originCube d m) n := by
          simpa [Q, j, descendantsAtScale_eq_descendantsAtDepth (originCube d m) hnm] using hR
        have hstationary :
            expectedResponseJCubeSet P R p q =
              expectedResponseJCubeSet P (originCube d n) p q :=
          hP.expectedResponseJCubeSet_eq_originCube_of_mem_descendantsAtScale_originCube
            hstat hn hnm hRscale p q
        rw [integral_const_mul]
        change weight R * expectedResponseJCubeSet P R p q =
          weight R * expectedResponseJCubeSet P (originCube d n) p q
        rw [hstationary]
    _ =
      descendantsAverage (originCube d m) (Int.toNat (m - n)) weight *
        expectedResponseJCubeSet P (originCube d n) p q := by
        let C : ℝ := expectedResponseJCubeSet P (originCube d n) p q
        change ((D.card : ℝ)⁻¹ * ∑ R ∈ D, weight R * C) =
          (((D.card : ℝ)⁻¹ * ∑ R ∈ D, weight R) * C)
        rw [← Finset.sum_mul]
        ring

end LawCarrier

end

end Ch04
end Book
end Homogenization
