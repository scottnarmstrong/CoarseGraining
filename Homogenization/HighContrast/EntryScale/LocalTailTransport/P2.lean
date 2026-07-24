import Homogenization.HighContrast.EntryScale.ResponseMoment
import Homogenization.Book.Ch04.Theorems.DilationResponse
import Homogenization.HighContrast.EntryScale.LocalTailTransport.P1
import Homogenization.HighContrast.EntryScale.RawHighContrastWeakNorm.P4
import Homogenization.HighContrast.EntryScale.RawHighContrastWeakNorm.P9

open Homogenization
open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization.Book.Ch05.Section54.OneStepContraction

namespace Homogenization.HighContrast.EntryScale

noncomputable section

/--
Source labels `p.HC.CR`, `e.W.first.sum`, `e.J.moment.bound`, and `a.HM`:
paired low-scale plus affine constant-tail estimate with the low-scale
child-response branch routed through the SHARP summed-weight first-power
source split (min/bad against the response with the `2 * sqrt(theta_m)`
normalizer) instead of the mis-sized Holder package.
-/
theorem paired_lowScaleTail_add_constantTail_special_le_responseBaseline_add_sourceMax_minBad_childResponseAverage_terms_localWindow
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hstat : Homogenization.Book.Ch04.StationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d)
    (hm : HighCenteredMomentParameters d hc)
    (hparams : hP4.params = hm.p4Params) {N k m : ℕ}
    (hNk : N ≤ k) (hkm : k < m)
    (hHM :
      HighCenteredMomentEstimate hm P N
        (intermediateCoarseBlockDeviation hP hStruct
          (fun x : Homogenization.CoeffField d => x)))
    (e : Homogenization.Vec d)
    (he : Homogenization.vecNormSq e = 1)
    (hSmallInt :
      let β := section53CoarseFluctuationBeta hP4
      let s' := hP4.sLower + β
      let t' := hP4.sUpper + β
      let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
      let p_e :=
        Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
      let q_e :=
        Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
      let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
      let childAvg := fun a : Homogenization.CoeffField d =>
        Homogenization.descendantsAverage Q (m - k)
          (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
      let response := fun a : Homogenization.CoeffField d =>
        (5 * β⁻¹) ^ 2 * childAvg a
      let lowerSmall := fun a : Homogenization.CoeffField d =>
        Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
            (d := d) m s' a ^ 2 /
          Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
      let upperSmall := fun a : Homogenization.CoeffField d =>
        Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
            (d := d) m t' a ^ 2 /
          Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
      MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d =>
          (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a) P)
    (hLowInt :
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
      let childAvg := fun a : Homogenization.CoeffField d =>
        Homogenization.descendantsAverage Q (m - k)
          (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
      let response := fun a : Homogenization.CoeffField d =>
        (5 * β⁻¹) ^ 2 * childAvg a
      let lowerSlot : Homogenization.CoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
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
      let upperSlot : Homogenization.CoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
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
      let lowSum := fun a : Homogenization.CoeffField d =>
        S.attach.sum fun n =>
          if k ≤ Int.toNat n.1 then 0 else lowerSlot a n + upperSlot a n
      MeasureTheory.Integrable lowSum P) :
    let β := section53CoarseFluctuationBeta hP4
    let s := hP4.sLower + 2 * β
    let s' := hP4.sLower + β
    let t := hP4.sUpper + 2 * β
    let t' := hP4.sUpper + β
    let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
    let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let childAvg := fun a : Homogenization.CoeffField d =>
      Homogenization.descendantsAverage Q (m - k)
        (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
    let response := fun a : Homogenization.CoeffField d =>
      (5 * β⁻¹) ^ 2 * childAvg a
    let lowerSmall := fun a : Homogenization.CoeffField d =>
      Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
          (d := d) m s' a ^ 2 /
        Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
    let upperSmall := fun a : Homogenization.CoeffField d =>
      Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
          (d := d) m t' a ^ 2 /
        Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
    let lowerSlot : Homogenization.CoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
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
    let upperSlot : Homogenization.CoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
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
    let lowSum := fun a : Homogenization.CoeffField d =>
      S.attach.sum fun n =>
        if k ≤ Int.toNat n.1 then 0 else lowerSlot a n + upperSlot a n
    let sourceMax :=
      terminalSpectralPositivePartSourceMax hP hStruct hc k m Q
        (fun x : Homogenization.CoeffField d => x)
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
        if k ≤ Int.toNat n.1 then
          (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 +
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1) *
            weightLossSup n
        else 0
    let responseTerm : ℝ :=
      coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
    let sourceTerm : ℝ :=
      edgeWeightLoss *
          (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
          (∫ a, min (sourceMax a) 1 * response a ∂P) +
        edgeWeightLoss *
          (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
          (∫ a, badEventTruncation sourceMax a * response a ∂P)
    let tailFactor : ℝ :=
      (β ^ 2)⁻¹ *
        Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))
    let responseBaselineCoeff : ℝ :=
      tailFactor * localWeakNormScalarWeightAtScales hP hStruct k m
    let constantCoeff : ℝ := tailFactor * contrastExcessAtScale hP hStruct m
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
    lowScaleTail + constantTail ≤
      responseBaselineCoeff * responseTerm + 2 * constantCoeff +
        tailFactor *
          (∫ a, (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a ∂P +
            ∫ a, lowSum a ∂P +
            sourceTerm) := by
  classical
  dsimp only at hSmallInt hLowInt ⊢
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let s' := hP4.sLower + β
  let t := hP4.sUpper + 2 * β
  let t' := hP4.sUpper + β
  let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let childAvg : Homogenization.CoeffField d → ℝ := fun a =>
    Homogenization.descendantsAverage Q (m - k)
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
  let response : Homogenization.CoeffField d → ℝ := fun a =>
    (5 * β⁻¹) ^ 2 * childAvg a
  let lowerSmall : Homogenization.CoeffField d → ℝ := fun a =>
    Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
        (d := d) m s' a ^ 2 /
      Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
  let upperSmall : Homogenization.CoeffField d → ℝ := fun a =>
    Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
        (d := d) m t' a ^ 2 /
      Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
  let lowerSlot : Homogenization.CoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
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
  let upperSlot : Homogenization.CoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
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
  let lowSum : Homogenization.CoeffField d → ℝ := fun a =>
    S.attach.sum fun n =>
      if k ≤ Int.toNat n.1 then 0 else lowerSlot a n + upperSlot a n
  let sourceMax : Homogenization.CoeffField d → ℝ :=
    terminalSpectralPositivePartSourceMax hP hStruct hc k m Q
      (fun x : Homogenization.CoeffField d => x)
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
      if k ≤ Int.toNat n.1 then
        (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 +
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1) *
          weightLossSup n
      else 0
  let responseTerm : ℝ :=
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  let sourceTerm : ℝ :=
    edgeWeightLoss *
        (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
        (∫ a, min (sourceMax a) 1 * response a ∂P) +
      edgeWeightLoss *
        (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
        (∫ a, badEventTruncation sourceMax a * response a ∂P)
  let tailFactor : ℝ :=
    (β ^ 2)⁻¹ *
      Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))
  let responseBaselineCoeff : ℝ :=
    tailFactor * localWeakNormScalarWeightAtScales hP hStruct k m
  let constantCoeff : ℝ := tailFactor * contrastExcessAtScale hP hStruct m
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
  have hlow :
      lowScaleTail ≤
        responseBaselineCoeff * responseTerm +
          tailFactor *
            (∫ a, (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a ∂P +
              ∫ a, lowSum a ∂P +
              sourceTerm) := by
    have h :=
      integral_paired_lowScaleTailSquares_special_le_responseBaseline_add_sourceMax_minBad_childResponseAverage_terms
        hP hstat hStruct hP4 hc hm hparams hNk hkm hHM e hSmallInt hLowInt
    simpa only [β, s, s', t, t', S, Q, p_e, q_e, σ, childAvg, response,
      lowScaleTail, tailFactor, responseBaselineCoeff, responseTerm, lowerSmall,
      upperSmall, lowerSlot, upperSlot, lowSum, sourceMax, weightLossSup,
      edgeWeightLoss, sourceTerm] using h
  have hconst : constantTail ≤ 2 * constantCoeff := by
    simpa only [β, s, t, p_e, q_e, p0_e, q0_e, σ, constantTail,
      constantCoeff, tailFactor] using
      paired_constantTail_special_le_contrastExcess_lowScaleTail_unweighted
        hP hStruct hP4 hkm e he
  calc
    lowScaleTail + constantTail
        ≤
          (responseBaselineCoeff * responseTerm +
              tailFactor *
                (∫ a, (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a ∂P +
                  ∫ a, lowSum a ∂P +
                  sourceTerm)) +
            2 * constantCoeff :=
            add_le_add hlow hconst
    _ = responseBaselineCoeff * responseTerm + 2 * constantCoeff +
        tailFactor *
          (∫ a, (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a ∂P +
            ∫ a, lowSum a ∂P +
            sourceTerm) := by ring


/--
Source labels `l.Jtilde.energy.bound`, `p.HC.CR`, `e.W.first.sum`,
`e.J.moment.bound`, and `a.HM`: local-window linear/product estimate for the
SHARP source-max child-response route.  The low/constant child-response tail
and the local positive-excess lower edge are paid from caller-supplied
small/low child-response budgets plus the sharp summed-weight first-power
source budget (`min(sourceMax,1) + badEventTruncation` against the response
with the `2 * sqrt(theta_m)` normalizer); no Holder package and no stale
window-moment response coefficient is assumed.
-/
theorem linearProductTerms_special_le_centering_add_componentIntegrals_with_sourceMax_minBad_childResponse_lowerTailBudget_localWindow
    {d : ℕ} [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Homogenization.Book.Ch04.CoeffLaw d}
        (hP : Homogenization.Book.Ch04.LawCarrier P)
        (hstat : Homogenization.Book.Ch04.StationaryLaw P)
        (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
        (hc : HighContrastExponents d)
        (hm : HighCenteredMomentParameters d hc)
        (hparams : hP4.params = hm.p4Params) {N k m : ℕ},
        N ≤ k → k < m →
        HighCenteredMomentEstimate hm P N
          (intermediateCoarseBlockDeviation hP hStruct
            (fun x : Homogenization.CoeffField d => x)) →
        ∀ e : Homogenization.Vec d, Homogenization.vecNormSq e = 1 →
        ∀ {eps : ℝ}, 0 < eps → eps ≤ 1 →
        ∀ {smallBudget lowBudget sourceBudget childTailBudget lowerTailBudget : ℝ},
        (let β := section53CoarseFluctuationBeta hP4
         let s' := hP4.sLower + β
         let t' := hP4.sUpper + β
         let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
         let p_e :=
          Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
         let q_e :=
          Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
         let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
         let childAvg := fun a : Homogenization.CoeffField d =>
          Homogenization.descendantsAverage Q (m - k)
            (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
         let response := fun a : Homogenization.CoeffField d =>
          (5 * β⁻¹) ^ 2 * childAvg a
         let lowerSmall := fun a : Homogenization.CoeffField d =>
          Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
              (d := d) m s' a ^ 2 /
            Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
         let upperSmall := fun a : Homogenization.CoeffField d =>
          Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
              (d := d) m t' a ^ 2 /
            Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
         MeasureTheory.Integrable
          (fun a : Homogenization.CoeffField d =>
            (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a) P) →
        (let β := section53CoarseFluctuationBeta hP4
         let s' := hP4.sLower + β
         let t' := hP4.sUpper + β
         let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
         let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
         let p_e :=
          Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
         let q_e :=
          Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
         let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
         let childAvg := fun a : Homogenization.CoeffField d =>
          Homogenization.descendantsAverage Q (m - k)
            (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
         let response := fun a : Homogenization.CoeffField d =>
          (5 * β⁻¹) ^ 2 * childAvg a
         let lowerSlot : Homogenization.CoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
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
         let upperSlot : Homogenization.CoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
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
         let lowSum := fun a : Homogenization.CoeffField d =>
          S.attach.sum fun n =>
            if k ≤ Int.toNat n.1 then 0 else lowerSlot a n + upperSlot a n
         MeasureTheory.Integrable lowSum P) →
        (let β := section53CoarseFluctuationBeta hP4
         let s' := hP4.sLower + β
         let t' := hP4.sUpper + β
         let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
         let p_e :=
          Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
         let q_e :=
          Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
         let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
         let childAvg := fun a : Homogenization.CoeffField d =>
          Homogenization.descendantsAverage Q (m - k)
            (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
         let response := fun a : Homogenization.CoeffField d =>
          (5 * β⁻¹) ^ 2 * childAvg a
         let lowerSmall := fun a : Homogenization.CoeffField d =>
          Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
              (d := d) m s' a ^ 2 /
            Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
         let upperSmall := fun a : Homogenization.CoeffField d =>
          Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
              (d := d) m t' a ^ 2 /
            Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
         ∫ a, (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a ∂P ≤
          smallBudget) →
        (let β := section53CoarseFluctuationBeta hP4
         let s' := hP4.sLower + β
         let t' := hP4.sUpper + β
         let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
         let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
         let p_e :=
          Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
         let q_e :=
          Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
         let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
         let childAvg := fun a : Homogenization.CoeffField d =>
          Homogenization.descendantsAverage Q (m - k)
            (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
         let response := fun a : Homogenization.CoeffField d =>
          (5 * β⁻¹) ^ 2 * childAvg a
         let lowerSlot : Homogenization.CoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
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
         let upperSlot : Homogenization.CoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
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
         let lowSum := fun a : Homogenization.CoeffField d =>
          S.attach.sum fun n =>
            if k ≤ Int.toNat n.1 then 0 else lowerSlot a n + upperSlot a n
         ∫ a, lowSum a ∂P ≤ lowBudget) →
        (let β := section53CoarseFluctuationBeta hP4
         let s' := hP4.sLower + β
         let t' := hP4.sUpper + β
         let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
         let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
         let p_e :=
          Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
         let q_e :=
          Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
         let childAvg := fun a : Homogenization.CoeffField d =>
          Homogenization.descendantsAverage Q (m - k)
            (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
         let response := fun a : Homogenization.CoeffField d =>
          (5 * β⁻¹) ^ 2 * childAvg a
         let sourceMax :=
          terminalSpectralPositivePartSourceMax hP hStruct hc k m Q
            (fun x : Homogenization.CoeffField d => x)
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
            if k ≤ Int.toNat n.1 then
              (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 +
                Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1) *
                weightLossSup n
            else 0
         edgeWeightLoss *
            (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
            (∫ a, min (sourceMax a) 1 * response a ∂P) +
          edgeWeightLoss *
            (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
            (∫ a, badEventTruncation sourceMax a * response a ∂P) ≤ sourceBudget) →
        (let β := section53CoarseFluctuationBeta hP4
         let tailFactor : ℝ :=
          (β ^ 2)⁻¹ *
            Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))
         let responseBaselineCoeff : ℝ :=
          tailFactor * localWeakNormScalarWeightAtScales hP hStruct k m
         let responseTerm : ℝ :=
          coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
         let constantCoeff : ℝ := tailFactor * contrastExcessAtScale hP hStruct m
         responseBaselineCoeff * responseTerm + 2 * constantCoeff +
            tailFactor * (smallBudget + lowBudget + sourceBudget) ≤
          childTailBudget) →
        childTailBudget + smallBudget + lowBudget + sourceBudget ≤ lowerTailBudget →
        let β := section53CoarseFluctuationBeta hP4
        let s := hP4.sLower + 2 * β
        let t := hP4.sUpper + 2 * β
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
        let gradWeak :=
          Homogenization.Book.Ch04.canonicalScalarResponseGradientWeakNormCubeSet
            Q s p_e q_e p0_e
        let fluxWeak :=
          Homogenization.Book.Ch04.canonicalScalarResponseFluxWeakNormCubeSet
            Q t p_e q_e q0_e
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
        let localSlots : ℝ :=
          (1 + contrastExcessAtScale hP hStruct m) *
              coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m +
            (5 * localWeakNormScalarWeightAtScales hP hStruct k m * β⁻¹) *
              weightedTauSumAtScales hP hStruct hP4 k m e +
            (1 + contrastExcessAtScale hP hStruct m) * 0
        (1 / 2 : ℝ) * ‖q0_e‖ * (gradCoeff * ∫ a, gradWeak a ∂P) +
            (1 / 2 : ℝ) * ‖p0_e‖ * (fluxCoeff * ∫ a, fluxWeak a ∂P) +
              productCoeff * (Real.sqrt G * Real.sqrt F)
          ≤
            C * eps * (Real.sqrt θ - 1) ^ 2 +
              C * eps⁻¹ *
                (16 *
                  (highScaleAverage + K ^ 2 * localSlots +
                    K ^ 2 * lowerTailBudget)) := by
  classical
  rcases linearProductTerms_special_le_centering_add_componentIntegrals_with_local_mismatch_slots
      (d := d) with ⟨C, hC_nonneg, hLin_all⟩
  refine ⟨C, hC_nonneg, ?_⟩
  rintro P hP hstat hStruct hP4 hc hm hparams N k m hNk hkm hHM e he eps heps_pos heps_le
    smallBudget lowBudget sourceBudget childTailBudget lowerTailBudget hSmallInt hLowInt
    hSmallBound hLowBound hSourceBudget hChildTailBudget htailBudget
  dsimp only at hSmallInt hLowInt hSmallBound hLowBound hSourceBudget hChildTailBudget ⊢
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let s' := hP4.sLower + β
  let t := hP4.sUpper + 2 * β
  let t' := hP4.sUpper + β
  let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let θ := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
  let K :=
    Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d
  let gradWeak :=
    Homogenization.Book.Ch04.canonicalScalarResponseGradientWeakNormCubeSet
      Q s p_e q_e p0_e
  let fluxWeak :=
    Homogenization.Book.Ch04.canonicalScalarResponseFluxWeakNormCubeSet
      Q t p_e q_e q0_e
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
  let lowerExcess := fun a : Homogenization.CoeffField d =>
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹)
      0
  let upperExcess := fun a : Homogenization.CoeffField d =>
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
        hP.barSigmaAtScale hStruct (k : ℤ))
      0
  let lowerTerminal := fun a : Homogenization.CoeffField d =>
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
      0
  let upperTerminal := fun a : Homogenization.CoeffField d =>
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
        hP.barSigmaAtScale hStruct (m : ℤ))
      0
  let defectSum := fun a : Homogenization.CoeffField d =>
    ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
      Real.rpow (3 : ℝ)
          (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
        Real.sqrt
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
            (m : ℤ) n p_e q_e a)
  let lowerEdge : ℝ :=
    ∫ a, (σ * lowerExcess a + σ⁻¹ * upperExcess a) * defectSum a ^ 2 ∂P
  let terminalEdge : ℝ :=
    ∫ a, (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) * defectSum a ^ 2 ∂P
  let localSlots : ℝ :=
    (1 + contrastExcessAtScale hP hStruct m) *
        coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m +
      (5 * localWeakNormScalarWeightAtScales hP hStruct k m * β⁻¹) *
        weightedTauSumAtScales hP hStruct hP4 k m e +
      (1 + contrastExcessAtScale hP hStruct m) * 0
  let localSlotsWithEdge : ℝ := localSlots + lowerEdge
  let childAvg : Homogenization.CoeffField d → ℝ := fun a =>
    Homogenization.descendantsAverage Q (m - k)
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
  let response : Homogenization.CoeffField d → ℝ := fun a =>
    (5 * β⁻¹) ^ 2 * childAvg a
  let lowerSmall : Homogenization.CoeffField d → ℝ := fun a =>
    Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
        (d := d) m s' a ^ 2 /
      Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
  let upperSmall : Homogenization.CoeffField d → ℝ := fun a =>
    Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
        (d := d) m t' a ^ 2 /
      Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
  let lowerSlot : Homogenization.CoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
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
  let upperSlot : Homogenization.CoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
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
  let lowSum : Homogenization.CoeffField d → ℝ := fun a =>
    S.attach.sum fun n =>
      if k ≤ Int.toNat n.1 then 0 else lowerSlot a n + upperSlot a n
  let sourceMax : Homogenization.CoeffField d → ℝ :=
    terminalSpectralPositivePartSourceMax hP hStruct hc k m Q
      (fun x : Homogenization.CoeffField d => x)
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
      if k ≤ Int.toNat n.1 then
        (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 +
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1) *
          weightLossSup n
      else 0
  let responseTerm : ℝ :=
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  let sourceMinTerm : ℝ :=
    edgeWeightLoss *
        (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
      (∫ a, min (sourceMax a) 1 * response a ∂P)
  let sourceBadTerm : ℝ :=
    edgeWeightLoss *
        (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
      (∫ a, badEventTruncation sourceMax a * response a ∂P)
  let sourceTerm : ℝ := sourceMinTerm + sourceBadTerm
  let tailFactor : ℝ :=
    (β ^ 2)⁻¹ *
      Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))
  let responseBaselineCoeff : ℝ :=
    tailFactor * localWeakNormScalarWeightAtScales hP hStruct k m
  let constantCoeff : ℝ := tailFactor * contrastExcessAtScale hP hStruct m
  let smallIntegral : ℝ := ∫ a, (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a ∂P
  let lowIntegral : ℝ := ∫ a, lowSum a ∂P
  let linProd : ℝ :=
    (1 / 2 : ℝ) * ‖q0_e‖ * (gradCoeff * ∫ a, gradWeak a ∂P) +
      (1 / 2 : ℝ) * ‖p0_e‖ * (fluxCoeff * ∫ a, fluxWeak a ∂P) +
        productCoeff * (Real.sqrt G * Real.sqrt F)
  let componentSlots : ℝ :=
    highScaleAverage + K ^ 2 * localSlotsWithEdge +
      K ^ 2 * lowScaleTail + K ^ 2 * constantTail
  let absorbedSlots : ℝ :=
    highScaleAverage + K ^ 2 * localSlots + K ^ 2 * lowerTailBudget
  have hLin :
      linProd ≤ C * eps * (Real.sqrt θ - 1) ^ 2 +
        C * eps⁻¹ * (16 * componentSlots) := by
    simpa [linProd, componentSlots, localSlotsWithEdge, localSlots, lowerEdge,
      lowerExcess, upperExcess, defectSum, highScaleAverage, lowScaleTail,
      constantTail, β, s, s', t, t', Q, p_e, q_e, p0_e, q0_e, σ, θ, K,
      gradWeak, fluxWeak, gradCoeff, fluxCoeff, productCoeff, G, F] using
      hLin_all hP hstat hStruct hP4 hkm e he heps_pos heps_le
  have htail_nonneg : 0 ≤ tailFactor := by
    dsimp [tailFactor]
    exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hchild_raw :
      lowScaleTail + constantTail ≤
        responseBaselineCoeff * responseTerm + 2 * constantCoeff +
          tailFactor * (smallIntegral + lowIntegral + sourceTerm) := by
    have h :=
      paired_lowScaleTail_add_constantTail_special_le_responseBaseline_add_sourceMax_minBad_childResponseAverage_terms_localWindow
        hP hstat hStruct hP4 hc hm hparams hNk hkm hHM e he hSmallInt hLowInt
    simpa only [β, s, s', t, t', S, Q, p_e, q_e, p0_e, q0_e, σ,
      childAvg, response, lowerSmall, upperSmall, lowerSlot, upperSlot,
      lowSum, sourceMax, weightLossSup, edgeWeightLoss,
      responseTerm, sourceTerm, sourceMinTerm, sourceBadTerm, tailFactor,
      responseBaselineCoeff,
      constantCoeff, lowScaleTail, constantTail, smallIntegral, lowIntegral] using h
  have hsmall_bound : smallIntegral ≤ smallBudget := by
    simpa only [β, s', t', Q, p_e, q_e, σ, childAvg, response, lowerSmall,
      upperSmall, smallIntegral] using hSmallBound
  have hlow_bound : lowIntegral ≤ lowBudget := by
    simpa only [β, s', t', S, Q, p_e, q_e, σ, childAvg, response, lowerSlot,
      upperSlot, lowSum, lowIntegral] using hLowBound
  have hsource_bound : sourceTerm ≤ sourceBudget := by
    simpa only [β, s', t', S, Q, p_e, q_e, childAvg, response, sourceMax,
      weightLossSup, edgeWeightLoss, responseTerm,
      sourceTerm, sourceMinTerm, sourceBadTerm] using hSourceBudget
  have htail_terms : smallIntegral + lowIntegral + sourceTerm ≤
      smallBudget + lowBudget + sourceBudget := by
    linarith only [hsmall_bound, hlow_bound, hsource_bound]
  have hchild_budget : lowScaleTail + constantTail ≤ childTailBudget := by
    calc
      lowScaleTail + constantTail
          ≤ responseBaselineCoeff * responseTerm + 2 * constantCoeff +
              tailFactor * (smallIntegral + lowIntegral + sourceTerm) := hchild_raw
      _ ≤ responseBaselineCoeff * responseTerm + 2 * constantCoeff +
              tailFactor * (smallBudget + lowBudget + sourceBudget) := by
            have hmul := mul_le_mul_of_nonneg_left htail_terms htail_nonneg
            linarith only [hmul]
      _ ≤ childTailBudget := by
            simpa only [β, tailFactor, responseBaselineCoeff, responseTerm,
              constantCoeff] using hChildTailBudget
  have hTerminalEdgeInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d =>
          (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) *
            defectSum a ^ 2) P := by
    simpa only [β, s', t', Q, p_e, q_e, σ, lowerTerminal, upperTerminal,
      defectSum] using
      integrable_terminalPositiveExcess_defectSum_sq_special_of_P4
        hP hstat hStruct hP4 hkm e
  have hlocal_to_terminal : lowerEdge ≤ terminalEdge := by
    simpa only [β, s', t', Q, p_e, q_e, σ, lowerExcess, upperExcess,
      lowerTerminal, upperTerminal, defectSum, lowerEdge, terminalEdge] using
      integral_localPositiveExcess_defectSum_sq_special_le_terminalPositiveExcess
        hP hStruct hP4 hkm.le e hTerminalEdgeInt
  have hMinChildInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d =>
          min (sourceMax a) 1 * childAvg a) P := by
    simpa only [β, Q, p_e, q_e, childAvg, sourceMax] using
      integrable_min_terminalSourceMax_one_mul_childResponseAverage_special
        hP hstat hStruct hP4 hc hkm e
  have hBadChildPair :=
    integral_badEventTruncation_terminalSourceMax_mul_childResponseAverage_le_responseMoment_mul_global_polynomialRoot_add_drift_of_start_le
      hP hstat hStruct hP4 hc hm hparams hNk hkm hHM e
  have hBadChildInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d =>
          badEventTruncation sourceMax a * childAvg a) P := by
    simpa only [β, Q, p_e, q_e, childAvg, sourceMax] using hBadChildPair.1
  have hMinRespInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d =>
          min (sourceMax a) 1 * response a) P := by
    refine (hMinChildInt.const_mul ((5 * β⁻¹) ^ 2)).congr ?_
    filter_upwards with a
    dsimp [response]
    ring
  have hBadRespInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d =>
          badEventTruncation sourceMax a * response a) P := by
    refine (hBadChildInt.const_mul ((5 * β⁻¹) ^ 2)).congr ?_
    filter_upwards with a
    dsimp [response]
    ring
  have htail_glue :
      smallBudget + lowBudget + sourceMinTerm + sourceBadTerm ≤
        smallBudget + lowBudget + sourceBudget := by
    have hsb : sourceMinTerm + sourceBadTerm ≤ sourceBudget := by
      simpa only [sourceTerm] using hsource_bound
    linarith only [hsb]
  have hterminal_budget : terminalEdge ≤ smallBudget + lowBudget + sourceBudget := by
    simpa only [β, s', t', Q, p_e, q_e, σ, lowerTerminal, upperTerminal,
      defectSum, terminalEdge] using
      integral_terminalPositiveExcess_defectSum_sq_le_lowerTailBudget_of_sourceMax_min_one_add_badEventTruncation_childResponseAverage
        hP hstat hStruct hP4 hc hkm e
        (smallBudget := smallBudget) (lowBudget := lowBudget)
        (sourceMinBudget := sourceMinTerm)
        (sourceBadBudget := sourceBadTerm)
        (lowerTailBudget := smallBudget + lowBudget + sourceBudget)
        hSmallInt hLowInt hMinRespInt hBadRespInt hSmallBound hLowBound
        le_rfl le_rfl htail_glue
  have hlower_budget : lowerEdge ≤ smallBudget + lowBudget + sourceBudget :=
    hlocal_to_terminal.trans hterminal_budget
  have htotal_tail : lowerEdge + lowScaleTail + constantTail ≤ lowerTailBudget := by
    linarith only [hlower_budget, hchild_budget, htailBudget]
  have htail_scaled :
      K ^ 2 * lowerEdge + K ^ 2 * lowScaleTail + K ^ 2 * constantTail ≤
        K ^ 2 * lowerTailBudget := by
    calc
      K ^ 2 * lowerEdge + K ^ 2 * lowScaleTail + K ^ 2 * constantTail
          = K ^ 2 * (lowerEdge + lowScaleTail + constantTail) := by ring
      _ ≤ K ^ 2 * lowerTailBudget :=
          mul_le_mul_of_nonneg_left htotal_tail (sq_nonneg K)
  have hslots : componentSlots ≤ absorbedSlots := by
    dsimp [componentSlots, absorbedSlots, localSlotsWithEdge]
    linarith only [htail_scaled]
  have hcomponent_scaled :
      C * eps⁻¹ * (16 * componentSlots) ≤
        C * eps⁻¹ * (16 * absorbedSlots) := by
    have h16 : 16 * componentSlots ≤ 16 * absorbedSlots :=
      mul_le_mul_of_nonneg_left hslots (by norm_num : (0 : ℝ) ≤ 16)
    exact mul_le_mul_of_nonneg_left h16
      (mul_nonneg hC_nonneg (inv_nonneg.mpr heps_pos.le))
  calc
    linProd
        ≤ C * eps * (Real.sqrt θ - 1) ^ 2 +
            C * eps⁻¹ * (16 * componentSlots) := hLin
    _ ≤ C * eps * (Real.sqrt θ - 1) ^ 2 +
            C * eps⁻¹ * (16 * absorbedSlots) := by
          exact add_le_add le_rfl hcomponent_scaled
    _ =
        C * eps * (Real.sqrt θ - 1) ^ 2 +
          C * eps⁻¹ *
            (16 *
              (highScaleAverage + K ^ 2 * localSlots +
                K ^ 2 * lowerTailBudget)) := by
        dsimp [absorbedSlots]

end

end Homogenization.HighContrast.EntryScale
