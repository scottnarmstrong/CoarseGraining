import Homogenization.HighContrast.EntryScale.ResponseFluctuation
import Homogenization.HighContrast.EntryScale.ResponseMoment
import Homogenization.HighContrast.EntryScale.TerminalLowerEdge
import Homogenization.HighContrast.EntryScale.BadEventResponse
import Homogenization.HighContrast.EntryScale.RawHighContrastWeakNorm.P6
import Homogenization.HighContrast.EntryScale.RawHighContrastWeakNorm.P7
import Homogenization.HighContrast.EntryScale.RawHighContrastWeakNorm.P8

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization
open scoped Matrix.Norms.Elementwise

namespace Homogenization.HighContrast.EntryScale

noncomputable section

/--
Source labels `p.HC.CR`, `e.W.first.sum`, and `e.tau.sum.absorb`:
the library's linear weak-norm terms and cutoff-product Cauchy term, after the
special-vector absorption step, are bounded by the centering square plus the
local component slots.  This is the bridge from the library's
`linearProductTerms_special_le_centering_add_pairedWeakNormSquares` to the
local component theorem above; the four component terms remain explicit.
-/
theorem linearProductTerms_special_le_centering_add_componentIntegrals_with_local_mismatch_slots
    {d : ℕ} [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
        (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
        (_hstat : Homogenization.Book.Ch04.RestrictionStationaryLaw P)
        (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
        {k m : ℕ}, k < m → ∀ e : Homogenization.Vec d,
        Homogenization.vecNormSq e = 1 →
        ∀ {eps : ℝ}, 0 < eps → eps ≤ 1 →
        let β := section53CoarseFluctuationBeta hP4
        let s := hP4.sLower + 2 * β
        let s' := hP4.sLower + β
        let t := hP4.sUpper + 2 * β
        let t' := hP4.sUpper + β
        let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
        let p_e :=
          Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
        let q_e :=
          Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
        let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
        let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
        let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
        let θ := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
        let K :=
          Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d
        let gradWeak := fun a : Homogenization.RegCoeffField d =>
          Homogenization.Book.Ch04.canonicalScalarResponseGradientWeakNormCubeSet
            Q s p_e q_e p0_e a.toFun
        let fluxWeak := fun a : Homogenization.RegCoeffField d =>
          Homogenization.Book.Ch04.canonicalScalarResponseFluxWeakNormCubeSet
            Q t p_e q_e q0_e a.toFun
        let gradCoeff :=
          (Fintype.card (Fin d) : ℝ) *
            ((3 : ℝ) ^ ((d : ℝ) + s) *
              Homogenization.cubeBesovScaleWeight (-s) Q *
                Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound
                  Q s)
        let fluxCoeff :=
          (Fintype.card (Fin d) : ℝ) *
            ((3 : ℝ) ^ ((d : ℝ) + t) *
              Homogenization.cubeBesovScaleWeight (-t) Q *
                Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound
                  Q t)
        let productCoeff :=
          Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffProductCoeff
            Q s t
        let G := ∫ a, (gradWeak a) ^ 2 ∂P
        let F := ∫ a, (fluxWeak a) ^ 2 ∂P
        let highScaleAverage : ℝ :=
          ∫ a,
            (σ *
                (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientAverageTermAtScale
                  (m : ℤ) (k : ℤ) s p_e q_e p0_e a) ^ 2 +
              σ⁻¹ *
                (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxAverageTermAtScale
                  (m : ℤ) (k : ℤ) t p_e q_e q0_e a) ^ 2) ∂P
        let lowScaleTail : ℝ :=
          ∫ a,
            (σ *
                (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientLowScaleTailAtScale
                  (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
              σ⁻¹ *
                (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxLowScaleTailAtScale
                  (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P
        let constantTail : ℝ :=
          σ *
              (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientConstantTailAtScale
                (m : ℤ) (k : ℤ) s p0_e) ^ 2 +
            σ⁻¹ *
              (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxConstantTailAtScale
                (m : ℤ) (k : ℤ) t q0_e) ^ 2
        let lowerExcess := fun a : Homogenization.RegCoeffField d =>
          max
            ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
              (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹)
            0
        let upperExcess := fun a : Homogenization.RegCoeffField d =>
          max
            (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
              hP.barSigmaAtScale hStruct (k : ℤ))
            0
        let defectSum := fun a : Homogenization.RegCoeffField d =>
          ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
            Real.rpow (3 : ℝ)
                (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
              Real.sqrt
                (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
                  (m : ℤ) n p_e q_e a)
        let lowerEdge : ℝ :=
          ∫ a,
            (σ * lowerExcess a + σ⁻¹ * upperExcess a) * defectSum a ^ 2 ∂P
        let localSlots : ℝ :=
          (1 + contrastExcessAtScale hP hStruct m) *
              coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m +
            (5 * localWeakNormScalarWeightAtScales hP hStruct k m * β⁻¹) *
              weightedTauSumAtScales hP hStruct hP4 k m e +
            lowerEdge +
            (1 + contrastExcessAtScale hP hStruct m) * 0
        (1 / 2 : ℝ) * ‖q0_e‖ * (gradCoeff * ∫ a, gradWeak a ∂P) +
            (1 / 2 : ℝ) * ‖p0_e‖ * (fluxCoeff * ∫ a, fluxWeak a ∂P) +
              productCoeff * (Real.sqrt G * Real.sqrt F)
          ≤
            C * eps * (Real.sqrt θ - 1) ^ 2 +
              C * eps⁻¹ *
                (16 *
                  (highScaleAverage + K ^ 2 * localSlots +
                    K ^ 2 * lowScaleTail + K ^ 2 * constantTail)) := by
  classical
  rcases linearProductTerms_special_le_centering_add_pairedWeakNormSquares
      (d := d) with ⟨C, hC_nonneg, hLin_all⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro P hP hstat hStruct hP4 k m hkm e he eps heps_pos heps_le
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let s' := hP4.sLower + β
  let t := hP4.sUpper + 2 * β
  let t' := hP4.sUpper + β
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let θ := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
  let K :=
    Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d
  let gradWeak := fun a : Homogenization.RegCoeffField d =>
    Homogenization.Book.Ch04.canonicalScalarResponseGradientWeakNormCubeSet
      Q s p_e q_e p0_e a.toFun
  let fluxWeak := fun a : Homogenization.RegCoeffField d =>
    Homogenization.Book.Ch04.canonicalScalarResponseFluxWeakNormCubeSet
      Q t p_e q_e q0_e a.toFun
  let gradCoeff :=
    (Fintype.card (Fin d) : ℝ) *
      ((3 : ℝ) ^ ((d : ℝ) + s) *
        Homogenization.cubeBesovScaleWeight (-s) Q *
          Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound
            Q s)
  let fluxCoeff :=
    (Fintype.card (Fin d) : ℝ) *
      ((3 : ℝ) ^ ((d : ℝ) + t) *
        Homogenization.cubeBesovScaleWeight (-t) Q *
          Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound
            Q t)
  let productCoeff :=
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffProductCoeff
      Q s t
  let G := ∫ a, (gradWeak a) ^ 2 ∂P
  let F := ∫ a, (fluxWeak a) ^ 2 ∂P
  let pairedSquares : ℝ := σ * G + σ⁻¹ * F
  let highScaleAverage : ℝ :=
    ∫ a,
      (σ *
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientAverageTermAtScale
            (m : ℤ) (k : ℤ) s p_e q_e p0_e a) ^ 2 +
        σ⁻¹ *
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxAverageTermAtScale
            (m : ℤ) (k : ℤ) t p_e q_e q0_e a) ^ 2) ∂P
  let lowScaleTail : ℝ :=
    ∫ a,
      (σ *
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientLowScaleTailAtScale
            (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
        σ⁻¹ *
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxLowScaleTailAtScale
            (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P
  let constantTail : ℝ :=
    σ *
        (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientConstantTailAtScale
          (m : ℤ) (k : ℤ) s p0_e) ^ 2 +
      σ⁻¹ *
        (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxConstantTailAtScale
          (m : ℤ) (k : ℤ) t q0_e) ^ 2
  let lowerExcess := fun a : Homogenization.RegCoeffField d =>
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹)
      0
  let upperExcess := fun a : Homogenization.RegCoeffField d =>
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
        hP.barSigmaAtScale hStruct (k : ℤ))
      0
  let defectSum := fun a : Homogenization.RegCoeffField d =>
    ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
      Real.rpow (3 : ℝ)
          (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
        Real.sqrt
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
            (m : ℤ) n p_e q_e a)
  let lowerEdge : ℝ :=
    ∫ a, (σ * lowerExcess a + σ⁻¹ * upperExcess a) * defectSum a ^ 2 ∂P
  let localSlots : ℝ :=
    (1 + contrastExcessAtScale hP hStruct m) *
        coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m +
      (5 * localWeakNormScalarWeightAtScales hP hStruct k m * β⁻¹) *
        weightedTauSumAtScales hP hStruct hP4 k m e +
      lowerEdge +
      (1 + contrastExcessAtScale hP hStruct m) * 0
  let componentSlots : ℝ :=
    highScaleAverage + K ^ 2 * localSlots +
      K ^ 2 * lowScaleTail + K ^ 2 * constantTail
  let linProd : ℝ :=
    (1 / 2 : ℝ) * ‖q0_e‖ * (gradCoeff * ∫ a, gradWeak a ∂P) +
      (1 / 2 : ℝ) * ‖p0_e‖ * (fluxCoeff * ∫ a, fluxWeak a ∂P) +
        productCoeff * (Real.sqrt G * Real.sqrt F)
  have hGradSq : MeasureTheory.Integrable (fun a => (gradWeak a) ^ 2) P := by
    have hbase :
        MeasureTheory.Integrable
          (Internal.specialGradientWeakNormSquare hP hStruct hP4 m e) P :=
      integrable_specialGradientWeakNormSquare_from_weakNormMaximizer
        hP hstat hStruct hP4 hkm e he
    unfold Internal.specialGradientWeakNormSquare at hbase
    simpa [gradWeak, Q, s, p_e, q_e, p0_e, β] using hbase
  have hFluxSq : MeasureTheory.Integrable (fun a => (fluxWeak a) ^ 2) P := by
    have hbase :
        MeasureTheory.Integrable
          (Internal.specialFluxWeakNormSquare hP hStruct hP4 m e) P :=
      integrable_specialFluxWeakNormSquare_from_weakNormMaximizer
        hP hstat hStruct hP4 hkm e he
    unfold Internal.specialFluxWeakNormSquare at hbase
    simpa [fluxWeak, Q, t, p_e, q_e, q0_e, β] using hbase
  have hLin :
      linProd ≤ C * eps * (Real.sqrt θ - 1) ^ 2 +
        C * eps⁻¹ * pairedSquares := by
    simpa [linProd, pairedSquares, β, s, t, Q, p_e, q_e, p0_e, q0_e,
      σ, θ, gradWeak, fluxWeak, gradCoeff, fluxCoeff, productCoeff, G, F] using
      hLin_all hP hStruct hP4 hkm e he heps_pos heps_le
        hGradSq hFluxSq
  have hPair :
      pairedSquares ≤ 16 * componentSlots := by
    simpa [pairedSquares, componentSlots, highScaleAverage, localSlots,
      lowScaleTail, constantTail, lowerEdge, lowerExcess, upperExcess,
      defectSum, β, s, s', t, t', Q, p_e, q_e, p0_e, q0_e, σ, K,
      gradWeak, fluxWeak, G, F] using
      paired_weakNormSquares_special_le_componentIntegrals_with_local_mismatch_slots
        hP hstat hStruct hP4 hkm e he
  have hfactor_nonneg : 0 ≤ C * eps⁻¹ :=
    mul_nonneg hC_nonneg (inv_nonneg.mpr heps_pos.le)
  have hPair_scaled :
      C * eps⁻¹ * pairedSquares ≤ C * eps⁻¹ * (16 * componentSlots) :=
    mul_le_mul_of_nonneg_left hPair hfactor_nonneg
  calc
    linProd
        ≤ C * eps * (Real.sqrt θ - 1) ^ 2 +
            C * eps⁻¹ * pairedSquares := hLin
    _ ≤ C * eps * (Real.sqrt θ - 1) ^ 2 +
            C * eps⁻¹ * (16 * componentSlots) := by
          exact add_le_add le_rfl hPair_scaled

/--
Source labels `p.HC.CR` and `e.W.low.tail`: start-window split of the Section
5.2 low-tail child-response integral.  The below-window tail (scales `n < k`)
is bounded by the deep below-start tail (scales `n < N`) plus the sharp
summed-weight first-power source term over the FULL start window `[N, m]`
(the `min(sourceMax,1) + badEventTruncation` pairing with the
`2 * sqrt(theta_m)` normalizer).  This replaces the mis-sized scale-zero-gap
budget for the `[N, k)` scales by source content payable through the resized
budget's stochastic/polynomial/drift roots.
-/
theorem integral_section52LowTail_childResponseAverage_special_le_belowStart_add_sourceMaxStart_minBad
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hstat : Homogenization.Book.Ch04.RestrictionStationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d)
    (hm : HighCenteredMomentParameters d hc)
    (hparams : hP4.params = hm.p4Params) {N k m : ℕ}
    (hNk : N ≤ k) (hkm : k < m)
    (hHM :
      HighCenteredMomentEstimate hm P N
        (intermediateCoarseBlockDeviation hP hStruct
          (fun x : Homogenization.RegCoeffField d => x)))
    (e : Homogenization.Vec d) :
    let β := section53CoarseFluctuationBeta hP4
    let s' := hP4.sLower + β
    let t' := hP4.sUpper + β
    let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let childAvg := fun a : Homogenization.RegCoeffField d =>
      Homogenization.descendantsAverage Q (m - k)
        (fun R => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
    let response := fun a : Homogenization.RegCoeffField d =>
      (5 * β⁻¹) ^ 2 * childAvg a
    let lowerSlot : Homogenization.RegCoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
      let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa [Q, Homogenization.originCube] using
            Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
      let lowerExcess : Homogenization.TriadicCube d → ℝ := fun R =>
        max
          (Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix
                (Homogenization.cubeSet R) a).lowerRight -
            (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
          0
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
        (σ * parents.sup' hparents lowerExcess) * response a
    let upperSlot : Homogenization.RegCoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
      let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa [Q, Homogenization.originCube] using
            Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
      let upperExcess : Homogenization.TriadicCube d → ℝ := fun R =>
        max
          (Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix
                (Homogenization.cubeSet R) a).upperLeft -
            hP.barSigmaAtScale hStruct (m : ℤ))
          0
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
        (σ⁻¹ * parents.sup' hparents upperExcess) * response a
    let lowSum := fun a : Homogenization.RegCoeffField d =>
      S.attach.sum fun n =>
        if k ≤ Int.toNat n.1 then 0 else lowerSlot a n + upperSlot a n
    let lowSumBelow := fun a : Homogenization.RegCoeffField d =>
      S.attach.sum fun n =>
        if N ≤ Int.toNat n.1 then 0 else lowerSlot a n + upperSlot a n
    let sourceMax :=
      terminalSpectralPositivePartSourceMax hP hStruct hc N m Q
        (fun x : Homogenization.RegCoeffField d => x)
    let weightLossSup : {n : ℤ // n ∈ S} → ℝ := fun n =>
      let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa [Q, Homogenization.originCube] using
            Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
      parents.sup' hparents
        (fun R =>
          ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n.1) R)⁻¹).toReal)
    let edgeWeightLoss : ℝ :=
      S.attach.sum fun n =>
        if N ≤ Int.toNat n.1 then
          (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 +
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1) *
            weightLossSup n
        else 0
    ∫ a, lowSum a ∂P ≤
      ∫ a, lowSumBelow a ∂P +
        edgeWeightLoss *
            (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
          ((∫ a, min (sourceMax a) 1 * response a ∂P) +
            (∫ a, badEventTruncation sourceMax a * response a ∂P)) := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let childAvg : Homogenization.RegCoeffField d → ℝ := fun a =>
    Homogenization.descendantsAverage Q (m - k)
      (fun R => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
  let response : Homogenization.RegCoeffField d → ℝ := fun a =>
    (5 * β⁻¹) ^ 2 * childAvg a
  let lowerSlot : Homogenization.RegCoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa [Q, Homogenization.originCube] using
          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
    let lowerExcess : Homogenization.TriadicCube d → ℝ := fun R =>
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix
              (Homogenization.cubeSet R) a).lowerRight -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
      (σ * parents.sup' hparents lowerExcess) * response a
  let upperSlot : Homogenization.RegCoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa [Q, Homogenization.originCube] using
          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
    let upperExcess : Homogenization.TriadicCube d → ℝ := fun R =>
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix
              (Homogenization.cubeSet R) a).upperLeft -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
      (σ⁻¹ * parents.sup' hparents upperExcess) * response a
  let lowSum : Homogenization.RegCoeffField d → ℝ := fun a =>
    S.attach.sum fun n =>
      if k ≤ Int.toNat n.1 then 0 else lowerSlot a n + upperSlot a n
  let lowSumBelow : Homogenization.RegCoeffField d → ℝ := fun a =>
    S.attach.sum fun n =>
      if N ≤ Int.toNat n.1 then 0 else lowerSlot a n + upperSlot a n
  let sourceMax : Homogenization.RegCoeffField d → ℝ :=
    terminalSpectralPositivePartSourceMax hP hStruct hc N m Q
      (fun x : Homogenization.RegCoeffField d => x)
  let weightLossSup : {n : ℤ // n ∈ S} → ℝ := fun n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa [Q, Homogenization.originCube] using
          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
    parents.sup' hparents
      (fun R =>
        ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n.1) R)⁻¹).toReal)
  let edgeWeightLoss : ℝ :=
    S.attach.sum fun n =>
      if N ≤ Int.toNat n.1 then
        (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 +
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1) *
          weightLossSup n
      else 0
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hs'_nonneg : 0 ≤ s' := by
    have := hP4.sLower_nonneg
    dsimp [s']
    linarith
  have ht'_nonneg : 0 ≤ t' := by
    have := hP4.sUpper_nonneg
    dsimp [t']
    linarith
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, Homogenization.Book.Ch05.sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hchild_nonneg : ∀ a, 0 ≤ childAvg a := by
    intro a
    dsimp [childAvg]
    exact Homogenization.descendantsAverage_nonneg Q (m - k)
      (fun R => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
      (fun R _hR =>
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet_nonneg R p_e q_e a)
  have hresp_nonneg : ∀ a, 0 ≤ response a := fun a =>
    mul_nonneg (sq_nonneg _) (hchild_nonneg a)
  have hslot_nonneg :
      ∀ (a : Homogenization.RegCoeffField d) (n : {n : ℤ // n ∈ S}),
        0 ≤ lowerSlot a n + upperSlot a n := by
    intro a n
    obtain ⟨R0, hR0⟩ :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa [Q, Homogenization.originCube] using
          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
    have hlower : 0 ≤ lowerSlot a n := by
      dsimp [lowerSlot]
      refine mul_nonneg (mul_nonneg ?_ ?_) (hresp_nonneg a)
      · exact Homogenization.Book.Ch05.Section52.section52LargeScaleWeight_nonneg
          m hs'_nonneg n.1
      · refine mul_nonneg hσ_nonneg ?_
        refine le_trans (le_max_right _ 0)
          (Finset.le_sup'
            (f := fun R : Homogenization.TriadicCube d =>
              max
                (Homogenization.Book.Ch02.matrixNorm
                    (Homogenization.coarseBlockMatrix
                      (Homogenization.cubeSet R) a).lowerRight -
                  (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
                0) hR0)
    have hupper : 0 ≤ upperSlot a n := by
      dsimp [upperSlot]
      refine mul_nonneg (mul_nonneg ?_ ?_) (hresp_nonneg a)
      · exact Homogenization.Book.Ch05.Section52.section52LargeScaleWeight_nonneg
          m ht'_nonneg n.1
      · refine mul_nonneg (inv_nonneg.mpr hσ_nonneg) ?_
        refine le_trans (le_max_right _ 0)
          (Finset.le_sup'
            (f := fun R : Homogenization.TriadicCube d =>
              max
                (Homogenization.Book.Ch02.matrixNorm
                    (Homogenization.coarseBlockMatrix
                      (Homogenization.cubeSet R) a).upperLeft -
                  hP.barSigmaAtScale hStruct (m : ℤ))
                0) hR0)
    exact add_nonneg hlower hupper
  have hLowInt : MeasureTheory.Integrable lowSum P := by
    simpa [lowSum, β, s', t', S, Q, p_e, q_e, σ, childAvg, response,
      lowerSlot, upperSlot] using
      (integrable_section52LowTail_childResponseAverage_special_and_integral_le_responseMoment
        hP hstat hStruct hP4 hkm e).1
  have hLowBelowInt : MeasureTheory.Integrable lowSumBelow P := by
    simpa [lowSumBelow, β, s', t', S, Q, p_e, q_e, σ, childAvg, response,
      lowerSlot, upperSlot] using
      (integrable_section52LowTailBelow_childResponseAverage_special_and_integral_le_responseMoment
        hP hstat hStruct hP4 N hkm e).1
  have hMinChildInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          min (sourceMax a) 1 * childAvg a) P := by
    simpa [β, Q, p_e, q_e, childAvg, sourceMax] using
      integrable_min_terminalSourceMax_start_one_mul_childResponseAverage_special
        hP hstat hStruct hP4 hc hNk hkm e
  have hBadChildPair :=
    integral_badEventTruncation_terminalSourceMax_start_mul_childResponseAverage_le_responseMoment_mul_global_polynomialRoot_add_drift
      hP hstat hStruct hP4 hc hm hparams hNk hkm hHM e
  have hBadChildInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          badEventTruncation sourceMax a * childAvg a) P := by
    simpa [β, Q, p_e, q_e, childAvg, sourceMax] using hBadChildPair.1
  have hMinRespInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          min (sourceMax a) 1 * response a) P := by
    refine (hMinChildInt.const_mul ((5 * β⁻¹) ^ 2)).congr ?_
    filter_upwards with a
    dsimp [response]
    ring
  have hBadRespInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          badEventTruncation sourceMax a * response a) P := by
    refine (hBadChildInt.const_mul ((5 * β⁻¹) ^ 2)).congr ?_
    filter_upwards with a
    dsimp [response]
    ring
  have hRHSInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          lowSumBelow a +
            edgeWeightLoss *
              (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
                (min (sourceMax a) 1 * response a +
                  badEventTruncation sourceMax a * response a))) P := by
    refine hLowBelowInt.add ?_
    refine ((hMinRespInt.add hBadRespInt).const_mul
      (edgeWeightLoss *
        (2 * Real.sqrt
          (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))))).congr ?_
    filter_upwards with a
    simp only [Pi.add_apply]
    ring
  have hpoint :
      ∀ᵐ a ∂P,
        lowSum a ≤
          lowSumBelow a +
            edgeWeightLoss *
              (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
                (min (sourceMax a) 1 * response a +
                  badEventTruncation sourceMax a * response a)) := by
    filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
    have hhigh :=
      section52LargeScale_terminalPositiveExcess_highSum_mul_le_edgeWeightLoss_mul_sqrt_thetaAtScale_sourceMax_min_one_add_badEventTruncation_mul_response
        (hP := hP) (hStruct := hStruct) (hP4 := hP4) (hc := hc)
        (N := N) (m := m) hs'_nonneg ht'_nonneg
        (a := fun x : Homogenization.RegCoeffField d => x) (ω := a) ha
        (J := response a) (hresp_nonneg a)
    have hhigh' :
        (S.attach.sum fun n =>
          if N ≤ Int.toNat n.1 then lowerSlot a n + upperSlot a n else 0) ≤
          edgeWeightLoss *
            (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
              (min (sourceMax a) 1 * response a +
                badEventTruncation sourceMax a * response a)) := by
      simpa [β, s', t', S, Q, σ, sourceMax, weightLossSup, edgeWeightLoss,
        lowerSlot, upperSlot, response, childAvg, p_e, q_e] using hhigh
    have hsplit :
        lowSum a ≤
          lowSumBelow a +
            (S.attach.sum fun n =>
              if N ≤ Int.toNat n.1 then lowerSlot a n + upperSlot a n else 0) := by
      dsimp [lowSum, lowSumBelow]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum ?_
      intro n _hn
      by_cases hkn : k ≤ Int.toNat n.1
      · have hNn : N ≤ Int.toNat n.1 := hNk.trans hkn
        simp only [if_pos hkn, if_pos hNn]
        have := hslot_nonneg a n
        linarith
      · by_cases hNn : N ≤ Int.toNat n.1
        · simp only [if_neg hkn, if_pos hNn]
          have := hslot_nonneg a n
          linarith
        · simp only [if_neg hkn, if_neg hNn]
          have := hslot_nonneg a n
          linarith
    linarith [hsplit, hhigh']
  calc
    ∫ a, lowSum a ∂P ≤
        ∫ a,
          (lowSumBelow a +
            edgeWeightLoss *
              (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
                (min (sourceMax a) 1 * response a +
                  badEventTruncation sourceMax a * response a))) ∂P :=
      MeasureTheory.integral_mono_ae hLowInt hRHSInt hpoint
    _ = ∫ a, lowSumBelow a ∂P +
          edgeWeightLoss *
              (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
            ((∫ a, min (sourceMax a) 1 * response a ∂P) +
              (∫ a, badEventTruncation sourceMax a * response a ∂P)) := by
        have hInt2 :
            MeasureTheory.Integrable
              (fun a : Homogenization.RegCoeffField d =>
                edgeWeightLoss *
                  (2 * Real.sqrt
                      (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
                    (min (sourceMax a) 1 * response a +
                      badEventTruncation sourceMax a * response a))) P :=
          ((hMinRespInt.add hBadRespInt).const_mul
            (2 * Real.sqrt
              (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)))).const_mul
            edgeWeightLoss
        rw [MeasureTheory.integral_add hLowBelowInt hInt2,
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_add hMinRespInt hBadRespInt]
        ring

end

end Homogenization.HighContrast.EntryScale
