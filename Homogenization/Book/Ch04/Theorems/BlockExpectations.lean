import Homogenization.Book.Ch04.Theorems.StationaryExpectations

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Block-response expectations

This file is the public Chapter 4 surface for expectations of the block
response observable.  The Ch4-facing observable is the manuscript half-sum of
one scalar response and one adjointed scalar response, so downstream sections
never supply a separate `BlockJ = half-sum` a.e. bridge.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

/-- The standard half-sum expression for the block response: one scalar
response for `a`, and one scalar response for the adjointed field. -/
noncomputable def blockJHalfResponseAdjointSumSet {d : ℕ}
    (U : Set (Vec d)) (p pStar q qStar : Vec d) : CoeffField d → ℝ :=
  fun a =>
    (1 / 2 : ℝ) * ResponseJ U (p - pStar) (qStar - q) a +
      (1 / 2 : ℝ) * ResponseJ U (pStar + p) (qStar + q) (adjointCoeffField a)

/-- Cube-set specialization of the standard half-sum expression. -/
noncomputable def blockJHalfResponseAdjointSumCubeSet {d : ℕ}
    (Q : TriadicCube d) (p pStar q qStar : Vec d) : CoeffField d → ℝ :=
  blockJHalfResponseAdjointSumSet (cubeSet Q) p pStar q qStar

@[simp]
theorem blockJHalfResponseAdjointSumCubeSet_apply {d : ℕ}
    (Q : TriadicCube d) (p pStar q qStar : Vec d) (a : CoeffField d) :
    blockJHalfResponseAdjointSumCubeSet Q p pStar q qStar a =
      (1 / 2 : ℝ) * responseJObservableCubeSet Q (p - pStar) (qStar - q) a +
        (1 / 2 : ℝ) *
          responseJObservableCubeSet Q (pStar + p) (qStar + q) (adjointCoeffField a) :=
  rfl

/-- Ch4-facing block response observable on a deterministic triadic cube.
It is definitionally the manuscript half-sum expression. -/
noncomputable def blockJObservableCubeSet {d : ℕ}
    (Q : TriadicCube d) (p pStar q qStar : Vec d) : CoeffField d → ℝ :=
  blockJHalfResponseAdjointSumCubeSet Q p pStar q qStar

@[simp]
theorem blockJObservableCubeSet_apply {d : ℕ}
    (Q : TriadicCube d) (p pStar q qStar : Vec d) (a : CoeffField d) :
    blockJObservableCubeSet Q p pStar q qStar a =
      (1 / 2 : ℝ) * responseJObservableCubeSet Q (p - pStar) (qStar - q) a +
        (1 / 2 : ℝ) *
          responseJObservableCubeSet Q (pStar + p) (qStar + q) (adjointCoeffField a) :=
  rfl

/-- The Ch4 block observable is definitionally the standard half-sum. -/
theorem blockJObservableCubeSet_eq_half_responseJ_adjoint_sum {d : ℕ}
    (Q : TriadicCube d) (p pStar q qStar : Vec d) :
    blockJObservableCubeSet Q p pStar q qStar =
      blockJHalfResponseAdjointSumCubeSet Q p pStar q qStar :=
  rfl

/-- Annealed block response on a deterministic triadic cube. -/
noncomputable def expectedBlockJCubeSet {d : ℕ}
    (P : CoeffLaw d) (Q : TriadicCube d) (p pStar q qStar : Vec d) : ℝ :=
  ∫ a, blockJObservableCubeSet Q p pStar q qStar a ∂P

/-- Annealed finite descendant average of block responses. -/
noncomputable def expectedDescendantsAverageBlockJCubeSet {d : ℕ}
    (P : CoeffLaw d) (Q : TriadicCube d) (j : ℕ)
    (p pStar q qStar : Vec d) : ℝ :=
  descendantsAverage Q j (fun R => expectedBlockJCubeSet P R p pStar q qStar)

/-- Finite descendant averages of block responses are integrable if the child
block responses are integrable. -/
theorem integrable_descendantsAverage_blockJObservableCubeSet
    {d : ℕ} {P : CoeffLaw d} {Q : TriadicCube d} {j : ℕ}
    {p pStar q qStar : Vec d}
    (hB : ∀ R, R ∈ descendantsAtDepth Q j →
      Integrable (blockJObservableCubeSet R p pStar q qStar) P) :
    Integrable
      (fun a : CoeffField d =>
        descendantsAverage Q j (fun R => blockJObservableCubeSet R p pStar q qStar a)) P :=
  integrable_descendantsAverage
    (P := P) (Q := Q) (j := j)
    (F := fun R a => blockJObservableCubeSet R p pStar q qStar a) hB

/-- Finite descendant averages of block responses are in `L^r` if the child
block responses are in `L^r`. -/
theorem memLp_descendantsAverage_blockJObservableCubeSet
    {d : ℕ} {P : CoeffLaw d} {Q : TriadicCube d} {j : ℕ} {r : ℝ≥0∞}
    {p pStar q qStar : Vec d}
    (hB : ∀ R, R ∈ descendantsAtDepth Q j →
      MemLp (blockJObservableCubeSet R p pStar q qStar) r P) :
    MemLp
      (fun a : CoeffField d =>
        descendantsAverage Q j (fun R => blockJObservableCubeSet R p pStar q qStar a)) r P :=
  memLp_descendantsAverage
    (P := P) (Q := Q) (j := j) (r := r)
    (F := fun R a => blockJObservableCubeSet R p pStar q qStar a) hB

/-- Finite descendant block-response averages commute with expectation,
assuming childwise integrability. -/
theorem integral_descendantsAverage_blockJObservableCubeSet_eq_expectedDescendantsAverageBlockJCubeSet
    {d : ℕ} {P : CoeffLaw d}
    (Q : TriadicCube d) (j : ℕ) (p pStar q qStar : Vec d)
    (hB : ∀ R, R ∈ descendantsAtDepth Q j →
      Integrable (blockJObservableCubeSet R p pStar q qStar) P) :
    ∫ a,
        descendantsAverage Q j (fun R => blockJObservableCubeSet R p pStar q qStar a) ∂P =
      expectedDescendantsAverageBlockJCubeSet P Q j p pStar q qStar := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  calc
    ∫ a,
        descendantsAverage Q j (fun R => blockJObservableCubeSet R p pStar q qStar a) ∂P
        =
      ∫ a,
        (D.card : ℝ)⁻¹ *
          (∑ R ∈ D, blockJObservableCubeSet R p pStar q qStar a) ∂P := by
          rfl
    _ =
      (D.card : ℝ)⁻¹ *
        ∫ a, ∑ R ∈ D, blockJObservableCubeSet R p pStar q qStar a ∂P := by
          rw [integral_const_mul]
    _ =
      (D.card : ℝ)⁻¹ *
        (∑ R ∈ D, ∫ a, blockJObservableCubeSet R p pStar q qStar a ∂P) := by
          rw [MeasureTheory.integral_finset_sum D
            (fun R hR => hB R (by simpa [D] using hR))]
    _ = expectedDescendantsAverageBlockJCubeSet P Q j p pStar q qStar := by
          simp [expectedDescendantsAverageBlockJCubeSet, expectedBlockJCubeSet,
            descendantsAverage, D]

/-- The half-sum expression is integrable when the two scalar responses are
integrable.  The second scalar response is composed with `adjointCoeffField`
using adjoint-invariance of the law. -/
theorem integrable_blockJHalfResponseAdjointSumCubeSet_of_integrable
    {d : ℕ} {P : CoeffLaw d} (hAdj : AdjointInvariantLaw P)
    (Q : TriadicCube d) (p pStar q qStar : Vec d)
    (hJ :
      Integrable (responseJObservableCubeSet Q (p - pStar) (qStar - q)) P)
    (hJAdjBase :
      Integrable (responseJObservableCubeSet Q (pStar + p) (qStar + q)) P) :
    Integrable (blockJHalfResponseAdjointSumCubeSet Q p pStar q qStar) P := by
  have hJAdj :
      Integrable
        (fun a : CoeffField d =>
          responseJObservableCubeSet Q (pStar + p) (qStar + q) (adjointCoeffField a)) P :=
    integrable_comp_adjointCoeffField_of_isAdjointInvariantInLaw hAdj
      (responseJObservableCubeSet Q (pStar + p) (qStar + q)) hJAdjBase
  refine ((hJ.const_mul (1 / 2 : ℝ)).add (hJAdj.const_mul (1 / 2 : ℝ))).congr ?_
  exact Filter.Eventually.of_forall (by
    intro a
    simp [blockJHalfResponseAdjointSumCubeSet, blockJHalfResponseAdjointSumSet])

/-- The Ch4 block response observable is integrable when the two scalar
responses in its half-sum representation are integrable. -/
theorem integrable_blockJObservableCubeSet_of_integrable
    {d : ℕ} {P : CoeffLaw d} (hAdj : AdjointInvariantLaw P)
    (Q : TriadicCube d) (p pStar q qStar : Vec d)
    (hJ :
      Integrable (responseJObservableCubeSet Q (p - pStar) (qStar - q)) P)
    (hJAdjBase :
      Integrable (responseJObservableCubeSet Q (pStar + p) (qStar + q)) P) :
    Integrable (blockJObservableCubeSet Q p pStar q qStar) P := by
  simpa [blockJObservableCubeSet] using
    integrable_blockJHalfResponseAdjointSumCubeSet_of_integrable
      hAdj Q p pStar q qStar hJ hJAdjBase

/-- The expectation of the half-sum expression is the half-sum of the two
ordinary response expectations under adjoint-invariance. -/
theorem integral_blockJHalfResponseAdjointSumCubeSet_eq_half_expectedResponseJCubeSet_add
    {d : ℕ} {P : CoeffLaw d} (hAdj : AdjointInvariantLaw P)
    (Q : TriadicCube d) (p pStar q qStar : Vec d)
    (hJ :
      Integrable (responseJObservableCubeSet Q (p - pStar) (qStar - q)) P)
    (hJAdjBase :
      Integrable (responseJObservableCubeSet Q (pStar + p) (qStar + q)) P) :
    ∫ a, blockJHalfResponseAdjointSumCubeSet Q p pStar q qStar a ∂P =
      (1 / 2 : ℝ) * expectedResponseJCubeSet P Q (p - pStar) (qStar - q) +
        (1 / 2 : ℝ) * expectedResponseJCubeSet P Q (pStar + p) (qStar + q) := by
  have hJAdj :
      Integrable
        (fun a : CoeffField d =>
          responseJObservableCubeSet Q (pStar + p) (qStar + q) (adjointCoeffField a)) P :=
    integrable_comp_adjointCoeffField_of_isAdjointInvariantInLaw hAdj
      (responseJObservableCubeSet Q (pStar + p) (qStar + q)) hJAdjBase
  calc
    ∫ a, blockJHalfResponseAdjointSumCubeSet Q p pStar q qStar a ∂P
        =
      ∫ a,
        (1 / 2 : ℝ) * responseJObservableCubeSet Q (p - pStar) (qStar - q) a +
          (1 / 2 : ℝ) *
            responseJObservableCubeSet Q (pStar + p) (qStar + q) (adjointCoeffField a) ∂P := by
          rfl
    _ =
      ∫ a, (1 / 2 : ℝ) * responseJObservableCubeSet Q (p - pStar) (qStar - q) a ∂P +
        ∫ a,
          (1 / 2 : ℝ) *
            responseJObservableCubeSet Q (pStar + p) (qStar + q) (adjointCoeffField a) ∂P := by
          rw [integral_add (hJ.const_mul (1 / 2 : ℝ)) (hJAdj.const_mul (1 / 2 : ℝ))]
    _ =
      (1 / 2 : ℝ) * ∫ a, responseJObservableCubeSet Q (p - pStar) (qStar - q) a ∂P +
        (1 / 2 : ℝ) *
          ∫ a, responseJObservableCubeSet Q (pStar + p) (qStar + q) (adjointCoeffField a) ∂P := by
          rw [integral_const_mul, integral_const_mul]
    _ =
      (1 / 2 : ℝ) * expectedResponseJCubeSet P Q (p - pStar) (qStar - q) +
        (1 / 2 : ℝ) * expectedResponseJCubeSet P Q (pStar + p) (qStar + q) := by
          rw [integral_comp_adjointCoeffField_eq_of_isAdjointInvariantInLaw hAdj
            (responseJObservableCubeSet Q (pStar + p) (qStar + q))
            hJAdjBase.aestronglyMeasurable]
          rfl

/-- The Ch4 block-response expectation is the half-sum of ordinary response
expectations under adjoint-invariance. -/
theorem integral_blockJObservableCubeSet_eq_half_expectedResponseJCubeSet_add
    {d : ℕ} {P : CoeffLaw d} (hAdj : AdjointInvariantLaw P)
    (Q : TriadicCube d) (p pStar q qStar : Vec d)
    (hJ :
      Integrable (responseJObservableCubeSet Q (p - pStar) (qStar - q)) P)
    (hJAdjBase :
      Integrable (responseJObservableCubeSet Q (pStar + p) (qStar + q)) P) :
    ∫ a, blockJObservableCubeSet Q p pStar q qStar a ∂P =
      (1 / 2 : ℝ) * expectedResponseJCubeSet P Q (p - pStar) (qStar - q) +
        (1 / 2 : ℝ) * expectedResponseJCubeSet P Q (pStar + p) (qStar + q) := by
  simpa [blockJObservableCubeSet] using
    integral_blockJHalfResponseAdjointSumCubeSet_eq_half_expectedResponseJCubeSet_add
      hAdj Q p pStar q qStar hJ hJAdjBase

/-- The Ch4 block response half-sum is translation-covariant as a set-indexed
coefficient-field observable. -/
theorem blockJHalfResponseAdjointSumSet_translation_covariant {d : ℕ}
    (p pStar q qStar : Vec d) :
    IsTranslationCovariant
      (fun U : Set (Vec d) =>
        blockJHalfResponseAdjointSumSet U p pStar q qStar) := by
  intro U z a
  have hCoeff :
      translateCoeffField (intVecToRealVec z) (adjointCoeffField a) =
        adjointCoeffField (translateCoeffField (intVecToRealVec z) a) := by
    rfl
  simp [blockJHalfResponseAdjointSumSet, translateByInt, hCoeff,
    ResponseJ_translateSet_eq_translateCoeffField]

namespace LawCarrier

/-- The standard half-sum expression for `BlockJ` is a.e.-measurable under a
law carrier and adjoint-invariant law. -/
theorem aemeasurable_blockJHalfResponseAdjointSumCubeSet
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hAdj : AdjointInvariantLaw P)
    (Q : TriadicCube d) (p pStar q qStar : Vec d) :
    AEMeasurable (blockJHalfResponseAdjointSumCubeSet Q p pStar q qStar) P := by
  have hJ :
      AEMeasurable (responseJObservableCubeSet Q (p - pStar) (qStar - q)) P :=
    hP.aemeasurable_responseJObservableCubeSet Q (p - pStar) (qStar - q)
  have hJAdj :
      AEMeasurable
        (fun a : CoeffField d =>
          responseJObservableCubeSet Q (pStar + p) (qStar + q) (adjointCoeffField a)) P :=
    aemeasurable_comp_adjointCoeffField_of_adjointInvariantLaw hAdj
      (hP.aemeasurable_responseJObservableCubeSet Q (pStar + p) (qStar + q))
  refine ((hJ.const_mul (1 / 2 : ℝ)).add (hJAdj.const_mul (1 / 2 : ℝ))).congr ?_
  exact Filter.Eventually.of_forall (by
    intro a
    simp [blockJHalfResponseAdjointSumCubeSet, blockJHalfResponseAdjointSumSet])

/-- The Ch4 block response observable is a.e.-measurable under a law carrier
and adjoint-invariant law. -/
theorem aemeasurable_blockJObservableCubeSet
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hAdj : AdjointInvariantLaw P)
    (Q : TriadicCube d) (p pStar q qStar : Vec d) :
    AEMeasurable (blockJObservableCubeSet Q p pStar q qStar) P := by
  simpa [blockJObservableCubeSet] using
    hP.aemeasurable_blockJHalfResponseAdjointSumCubeSet hAdj Q p pStar q qStar

/-- The Ch4 block response observable is a.e.-strongly-measurable under a law
carrier and adjoint-invariant law. -/
theorem aestronglyMeasurable_blockJObservableCubeSet
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hAdj : AdjointInvariantLaw P)
    (Q : TriadicCube d) (p pStar q qStar : Vec d) :
    AEStronglyMeasurable (blockJObservableCubeSet Q p pStar q qStar) P :=
  (hP.aemeasurable_blockJObservableCubeSet hAdj Q p pStar q qStar).aestronglyMeasurable

/-- Under stationarity, the annealed block response on a nonnegative-scale cube
is the annealed block response on the origin cube at the same scale. -/
theorem expectedBlockJCubeSet_eq_originCube_of_stationary
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hstat : StationaryLaw P) (hAdj : AdjointInvariantLaw P)
    (R : TriadicCube d) (hR_nonneg : 0 ≤ R.scale) (p pStar q qStar : Vec d) :
    expectedBlockJCubeSet P R p pStar q qStar =
      expectedBlockJCubeSet P (originCube d R.scale) p pStar q qStar := by
  have hshift :=
    cubeSet_eq_translateSet_originCube_of_nonneg_scale (R := R) hR_nonneg
  calc
    expectedBlockJCubeSet P R p pStar q qStar
        =
        ∫ a, blockJHalfResponseAdjointSumSet (cubeSet R) p pStar q qStar a ∂P := by
          rfl
    _ =
        ∫ a,
          blockJHalfResponseAdjointSumSet
            (translateSet (intVecToRealVec (scaleTranslationShift R.scale R))
              (cubeSet (originCube d R.scale))) p pStar q qStar a ∂P := by
          rw [hshift]
    _ =
        ∫ a,
          blockJHalfResponseAdjointSumSet (cubeSet (originCube d R.scale))
            p pStar q qStar a ∂P := by
          exact
            integral_eq_of_isTranslationCovariant_of_isStationary_aestronglyMeasurable
              (P := P) hstat
              (U := cubeSet (originCube d R.scale))
              (by
                simpa [blockJObservableCubeSet, blockJHalfResponseAdjointSumCubeSet] using
                  hP.aestronglyMeasurable_blockJObservableCubeSet hAdj
                    (originCube d R.scale) p pStar q qStar)
              (blockJHalfResponseAdjointSumSet_translation_covariant p pStar q qStar)
              (scaleTranslationShift R.scale R)
    _ = expectedBlockJCubeSet P (originCube d R.scale) p pStar q qStar := by
          rfl

/-- Under stationarity, a child cube of an origin cube has the same annealed
block response as the origin cube at the child scale. -/
theorem expectedBlockJCubeSet_eq_originCube_of_mem_descendantsAtScale_originCube
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hstat : StationaryLaw P) (hAdj : AdjointInvariantLaw P)
    {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m)
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (originCube d m) n)
    (p pStar q qStar : Vec d) :
    expectedBlockJCubeSet P R p pStar q qStar =
      expectedBlockJCubeSet P (originCube d n) p pStar q qStar := by
  have hshift :=
    cubeSet_eq_translateSet_originCube_of_mem_descendantsAtScale_originCube
      (d := d) hn hnm hR
  calc
    expectedBlockJCubeSet P R p pStar q qStar
        =
        ∫ a, blockJHalfResponseAdjointSumSet (cubeSet R) p pStar q qStar a ∂P := by
          rfl
    _ =
        ∫ a,
          blockJHalfResponseAdjointSumSet
            (translateSet (intVecToRealVec (scaleTranslationShift n R))
              (cubeSet (originCube d n))) p pStar q qStar a ∂P := by
          rw [hshift]
    _ =
        ∫ a,
          blockJHalfResponseAdjointSumSet (cubeSet (originCube d n))
            p pStar q qStar a ∂P := by
          exact
            integral_eq_of_isTranslationCovariant_of_isStationary_aestronglyMeasurable
              (P := P) hstat
              (U := cubeSet (originCube d n))
              (by
                simpa [blockJObservableCubeSet, blockJHalfResponseAdjointSumCubeSet] using
                  hP.aestronglyMeasurable_blockJObservableCubeSet hAdj
                    (originCube d n) p pStar q qStar)
              (blockJHalfResponseAdjointSumSet_translation_covariant p pStar q qStar)
              (scaleTranslationShift n R)
    _ = expectedBlockJCubeSet P (originCube d n) p pStar q qStar := by
          rfl

/-- Under stationarity, the finite average of child annealed block responses
equals the annealed block response on the origin cube at the child scale. -/
theorem expectedDescendantsAverageBlockJCubeSet_eq_originCube_of_stationary
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hstat : StationaryLaw P) (hAdj : AdjointInvariantLaw P)
    {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m) (p pStar q qStar : Vec d) :
    expectedDescendantsAverageBlockJCubeSet P (originCube d m)
        (Int.toNat (m - n)) p pStar q qStar =
      expectedBlockJCubeSet P (originCube d n) p pStar q qStar := by
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
    expectedDescendantsAverageBlockJCubeSet P (originCube d m)
        (Int.toNat (m - n)) p pStar q qStar
        =
      (D.card : ℝ)⁻¹ *
        (∑ R ∈ D, expectedBlockJCubeSet P R p pStar q qStar) := by
          simp [expectedDescendantsAverageBlockJCubeSet, descendantsAverage, D]
    _ =
      (D.card : ℝ)⁻¹ *
        (∑ _R ∈ D, expectedBlockJCubeSet P (originCube d n) p pStar q qStar) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro R hR
          exact
            hP.expectedBlockJCubeSet_eq_originCube_of_mem_descendantsAtScale_originCube
              hstat hAdj hn hnm (by simpa [hDscale] using hR) p pStar q qStar
    _ = expectedBlockJCubeSet P (originCube d n) p pStar q qStar := by
          simp [Finset.sum_const, nsmul_eq_mul, hcard_ne]

/-- Under stationarity and childwise integrability, the expectation of the
descendant-average block response observable is the annealed block response on
the origin cube at the child scale. -/
theorem integral_descendantsAverage_blockJObservableCubeSet_eq_originCube_of_stationary
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hstat : StationaryLaw P) (hAdj : AdjointInvariantLaw P)
    {n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m) (p pStar q qStar : Vec d)
    (hB : ∀ R, R ∈ descendantsAtScale (originCube d m) n →
      Integrable (blockJObservableCubeSet R p pStar q qStar) P) :
    ∫ a,
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (fun R => blockJObservableCubeSet R p pStar q qStar a) ∂P =
      expectedBlockJCubeSet P (originCube d n) p pStar q qStar := by
  have hB_depth :
      ∀ R, R ∈ descendantsAtDepth (originCube d m) (Int.toNat (m - n)) →
        Integrable (blockJObservableCubeSet R p pStar q qStar) P := by
    intro R hR
    exact hB R (by
      simpa [descendantsAtScale_eq_descendantsAtDepth (originCube d m) hnm] using hR)
  calc
    ∫ a,
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (fun R => blockJObservableCubeSet R p pStar q qStar a) ∂P
        =
      expectedDescendantsAverageBlockJCubeSet P (originCube d m)
        (Int.toNat (m - n)) p pStar q qStar :=
        integral_descendantsAverage_blockJObservableCubeSet_eq_expectedDescendantsAverageBlockJCubeSet
          (P := P) (Q := originCube d m) (j := Int.toNat (m - n))
          p pStar q qStar hB_depth
    _ = expectedBlockJCubeSet P (originCube d n) p pStar q qStar :=
        hP.expectedDescendantsAverageBlockJCubeSet_eq_originCube_of_stationary
          hstat hAdj hn hnm p pStar q qStar

end LawCarrier

end

end Ch04
end Book
end Homogenization
