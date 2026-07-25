import Homogenization.HighContrast.EntryScale.ResponseFluctuation
import Homogenization.HighContrast.EntryScale.ResponseMoment
import Homogenization.HighContrast.EntryScale.TerminalLowerEdge
import Homogenization.HighContrast.EntryScale.BadEventResponse
import Homogenization.HighContrast.EntryScale.RawHighContrastWeakNorm.P2
import Homogenization.HighContrast.EntryScale.RawHighContrastWeakNorm.P3

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization
open scoped Matrix.Norms.Elementwise

namespace Homogenization.HighContrast.EntryScale

noncomputable section

/--
Source labels `p.HC.CR`, `e.weaknorms.moreproto`, `e.M.def`, and `a.HM`:
expectation-level summed-weight first-power source decomposition.  The
Section 5.2 small tail and low sum are kept in their child-response-average
budget shapes, while the exact summed `edgeWeightLoss` coefficient multiplies
the sharp normalization `2 * sqrt(theta_m) = 2 * r_m` and the first-power
source pair `min(sourceMax, 1) * response + badEventTruncation(sourceMax) *
response`.  This is the sharp hybrid of the crude
`2 * (1 + F_m)`/squared-truncation split and the sup-weight sharp chain.
-/
theorem integral_terminalPositiveExcess_defectSum_sq_le_section52SmallTail_childResponseAverage_add_lowSum_add_edgeWeightLoss_mul_sqrtThetaAtScale_sourceMax_min_one_add_badEventTruncation_mul_childResponseAverage
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hstat : Homogenization.Book.Ch04.StationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {k m : ℕ}
    (hkm : k < m) (e : Homogenization.Vec d)
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
      let childAvg := fun a : Homogenization.RegCoeffField d =>
        Homogenization.descendantsAverage Q (m - k)
          (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
      let response := fun a : Homogenization.RegCoeffField d =>
        (5 * β⁻¹) ^ 2 * childAvg a
      let lowerSmall := fun a : Homogenization.RegCoeffField d =>
        Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
            (d := d) m s' a ^ 2 /
          Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
      let upperSmall := fun a : Homogenization.RegCoeffField d =>
        Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
            (d := d) m t' a ^ 2 /
          Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
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
      let childAvg := fun a : Homogenization.RegCoeffField d =>
        Homogenization.descendantsAverage Q (m - k)
          (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
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
      MeasureTheory.Integrable lowSum P)
    (hMinInt :
      let β := section53CoarseFluctuationBeta hP4
      let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
      let p_e :=
        Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
      let q_e :=
        Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
      let childAvg := fun a : Homogenization.RegCoeffField d =>
        Homogenization.descendantsAverage Q (m - k)
          (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
      let response := fun a : Homogenization.RegCoeffField d =>
        (5 * β⁻¹) ^ 2 * childAvg a
      let sourceMax :=
        terminalSpectralPositivePartSourceMax hP hStruct hc k m Q
          (fun x : Homogenization.RegCoeffField d => x)
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          min (sourceMax a) 1 * response a) P)
    (hBadInt :
      let β := section53CoarseFluctuationBeta hP4
      let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
      let p_e :=
        Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
      let q_e :=
        Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
      let childAvg := fun a : Homogenization.RegCoeffField d =>
        Homogenization.descendantsAverage Q (m - k)
          (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
      let response := fun a : Homogenization.RegCoeffField d =>
        (5 * β⁻¹) ^ 2 * childAvg a
      let sourceMax :=
        terminalSpectralPositivePartSourceMax hP hStruct hc k m Q
          (fun x : Homogenization.RegCoeffField d => x)
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          badEventTruncation sourceMax a * response a) P) :
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
    let defectSum := fun a : Homogenization.RegCoeffField d =>
      ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
        Real.rpow (3 : ℝ)
            (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          Real.sqrt
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
              (m : ℤ) n p_e q_e a)
    let childAvg := fun a : Homogenization.RegCoeffField d =>
      Homogenization.descendantsAverage Q (m - k)
        (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
    let response := fun a : Homogenization.RegCoeffField d =>
      (5 * β⁻¹) ^ 2 * childAvg a
    let lowerTerminal := fun a : Homogenization.RegCoeffField d =>
      max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0
    let upperTerminal := fun a : Homogenization.RegCoeffField d =>
      max
        (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0
    let lowerSmall := fun a : Homogenization.RegCoeffField d =>
      Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
          (d := d) m s' a ^ 2 /
        Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
    let upperSmall := fun a : Homogenization.RegCoeffField d =>
      Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
          (d := d) m t' a ^ 2 /
        Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
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
    let sourceMax :=
      terminalSpectralPositivePartSourceMax hP hStruct hc k m Q
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
        if k ≤ Int.toNat n.1 then
          (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 +
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1) *
            weightLossSup n
        else 0
    ∫ a,
        (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) *
          defectSum a ^ 2 ∂P
      ≤
        ∫ a, (σ * lowerSmall a + σ⁻¹ * upperSmall a) *
          response a ∂P +
        ∫ a, lowSum a ∂P +
        edgeWeightLoss *
          (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
          ((∫ a, min (sourceMax a) 1 * response a ∂P) +
            ∫ a, badEventTruncation sourceMax a * response a ∂P) := by
  classical
  dsimp only at hSmallInt hLowInt hMinInt hBadInt ⊢
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let defectSum : Homogenization.RegCoeffField d → ℝ := fun a =>
    ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
      Real.rpow (3 : ℝ)
          (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
        Real.sqrt
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
            (m : ℤ) n p_e q_e a)
  let childAvg : Homogenization.RegCoeffField d → ℝ := fun a =>
    Homogenization.descendantsAverage Q (m - k)
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
  let response : Homogenization.RegCoeffField d → ℝ := fun a =>
    (5 * β⁻¹) ^ 2 * childAvg a
  let lowerTerminal : Homogenization.RegCoeffField d → ℝ := fun a =>
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
      0
  let upperTerminal : Homogenization.RegCoeffField d → ℝ := fun a =>
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
        hP.barSigmaAtScale hStruct (m : ℤ))
      0
  let lowerSmall : Homogenization.RegCoeffField d → ℝ := fun a =>
    Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
        (d := d) m s' a ^ 2 /
      Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
  let upperSmall : Homogenization.RegCoeffField d → ℝ := fun a =>
    Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
        (d := d) m t' a ^ 2 /
      Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
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
  let sourceMax : Homogenization.RegCoeffField d → ℝ :=
    terminalSpectralPositivePartSourceMax hP hStruct hc k m Q
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
      if k ≤ Int.toNat n.1 then
        (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 +
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1) *
          weightLossSup n
      else 0
  let C : ℝ :=
    edgeWeightLoss *
      (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)))
  let left : Homogenization.RegCoeffField d → ℝ := fun a =>
    (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) * defectSum a ^ 2
  let smallTerm : Homogenization.RegCoeffField d → ℝ := fun a =>
    (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a
  let minTerm : Homogenization.RegCoeffField d → ℝ := fun a =>
    min (sourceMax a) 1 * response a
  let badTerm : Homogenization.RegCoeffField d → ℝ := fun a =>
    badEventTruncation sourceMax a * response a
  let stochTerm : Homogenization.RegCoeffField d → ℝ := fun a =>
    C * (minTerm a + badTerm a)
  have hLeftInt : MeasureTheory.Integrable left P := by
    simpa only [left, β, s', t', Q, p_e, q_e, σ, lowerTerminal,
      upperTerminal, defectSum] using
      integrable_terminalPositiveExcess_defectSum_sq_special_of_P4
        hP hstat hStruct hP4 hkm e
  have hSmallInt' : MeasureTheory.Integrable smallTerm P := by
    simpa only [smallTerm, β, s', t', Q, p_e, q_e, σ, childAvg, response,
      lowerSmall, upperSmall] using hSmallInt
  have hLowInt' : MeasureTheory.Integrable lowSum P := by
    simpa only [lowSum, β, s', t', S, Q, p_e, q_e, σ, childAvg, response,
      lowerSlot, upperSlot] using hLowInt
  have hMinInt' : MeasureTheory.Integrable minTerm P := by
    simpa only [minTerm, β, Q, p_e, q_e, childAvg, response, sourceMax] using hMinInt
  have hBadInt' : MeasureTheory.Integrable badTerm P := by
    simpa only [badTerm, β, Q, p_e, q_e, childAvg, response, sourceMax] using hBadInt
  have hStochInt : MeasureTheory.Integrable stochTerm P := by
    simpa only [stochTerm] using (hMinInt'.add hBadInt').const_mul C
  have hRightInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          smallTerm a + lowSum a + stochTerm a) P :=
    (hSmallInt'.add hLowInt').add hStochInt
  have hPoint :
      left ≤ᵐ[P]
        (fun a : Homogenization.RegCoeffField d =>
          smallTerm a + lowSum a + stochTerm a) := by
    filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
    have hpt :
        left a ≤
          smallTerm a + lowSum a +
            edgeWeightLoss *
              (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
                (minTerm a + badTerm a)) := by
      simpa only [left, smallTerm, lowSum, minTerm, badTerm, β, s', t', S, Q,
        p_e, q_e, σ, defectSum, childAvg, response, lowerTerminal,
        upperTerminal, lowerSmall, upperSmall, lowerSlot, upperSlot,
        sourceMax, weightLossSup, edgeWeightLoss] using
        terminalPositiveExcessWeight_mul_defectSum_sq_le_section52SmallTail_mul_childResponseAverage_add_lowSum_childResponseAverage_add_edgeWeightLoss_mul_sqrtThetaAtScale_sourceMax_min_one_add_badEventTruncation_mul_childResponseAverage
          (hP := hP) (hStruct := hStruct) (hP4 := hP4) (hc := hc)
          (k := k) (m := m) hkm e
          (fun x : Homogenization.RegCoeffField d => x) a ha
    have hCeq :
        edgeWeightLoss *
            (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
              (minTerm a + badTerm a)) = stochTerm a := by
      dsimp [stochTerm, C]
      ring
    calc
      left a ≤
          smallTerm a + lowSum a +
            edgeWeightLoss *
              (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
                (minTerm a + badTerm a)) := hpt
      _ = smallTerm a + lowSum a + stochTerm a := by rw [hCeq]
  have hmono :
      ∫ a, left a ∂P ≤
        ∫ a, smallTerm a + lowSum a + stochTerm a ∂P :=
    MeasureTheory.integral_mono_ae hLeftInt hRightInt hPoint
  have hstoch_eq :
      ∫ a, stochTerm a ∂P =
        C * ((∫ a, minTerm a ∂P) + ∫ a, badTerm a ∂P) := by
    calc
      ∫ a, stochTerm a ∂P = C * ∫ a, minTerm a + badTerm a ∂P := by
        dsimp [stochTerm]
        rw [MeasureTheory.integral_const_mul]
      _ = C * ((∫ a, minTerm a ∂P) + ∫ a, badTerm a ∂P) := by
        rw [MeasureTheory.integral_add hMinInt' hBadInt']
  calc
    ∫ a,
        (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) *
          defectSum a ^ 2 ∂P
        = ∫ a, left a ∂P := by rfl
    _ ≤ ∫ a, smallTerm a + lowSum a + stochTerm a ∂P := hmono
    _ = ∫ a, (smallTerm + lowSum) a + stochTerm a ∂P := by rfl
    _ = ∫ a, (smallTerm + lowSum) a ∂P +
          ∫ a, stochTerm a ∂P := by
          rw [MeasureTheory.integral_add (hSmallInt'.add hLowInt') hStochInt]
    _ = (∫ a, smallTerm a + lowSum a ∂P) +
          ∫ a, stochTerm a ∂P := by rfl
    _ = (∫ a, smallTerm a ∂P + ∫ a, lowSum a ∂P) +
          ∫ a, stochTerm a ∂P := by
          rw [MeasureTheory.integral_add hSmallInt' hLowInt']
    _ = ∫ a, smallTerm a ∂P + ∫ a, lowSum a ∂P +
          C * ((∫ a, minTerm a ∂P) + ∫ a, badTerm a ∂P) := by
          rw [hstoch_eq]
    _ =
        ∫ a, (σ * lowerSmall a + σ⁻¹ * upperSmall a) *
          response a ∂P +
        ∫ a, lowSum a ∂P +
        edgeWeightLoss *
          (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
          ((∫ a, min (sourceMax a) 1 * response a ∂P) +
            ∫ a, badEventTruncation sourceMax a * response a ∂P) := by rfl

/--
The exact Section 5.2 high-scale edge-loss coefficient is nonnegative.  This
keeps later absorption estimates free of an artificial nonnegativity
hypothesis on the scalar edge coefficient.
-/
theorem section52LargeScale_terminalPositiveExcess_edgeWeightLoss_nonneg_of_P4_beta
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {N m : ℕ} :
    let β := section53CoarseFluctuationBeta hP4
    let s' := hP4.sLower + β
    let t' := hP4.sUpper + β
    let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
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
    0 ≤ edgeWeightLoss := by
  classical
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
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
    simpa only [β] using section53CoarseFluctuationBeta_pos hP4
  have hs'_pos : 0 < s' := by
    dsimp [s']
    linarith [hP4.sLower_pos, hβ_pos]
  have ht'_pos : 0 < t' := by
    dsimp [t']
    linarith [hP4.sUpper_pos, hβ_pos]
  have hweightLossSup_nonneg :
      ∀ n : {n : ℤ // n ∈ S}, 0 ≤ weightLossSup n := by
    intro n
    dsimp [weightLossSup]
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa [Q, Homogenization.originCube] using
          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
    rcases hparents with ⟨R0, hR0⟩
    have hval_nonneg :
        0 ≤
          ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n.1) R0)⁻¹).toReal := by
      rw [terminalStochasticWeakWeight_inv_toReal_eq]
      positivity
    exact
      Finset.le_sup'_of_le
        (fun R =>
          ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n.1) R)⁻¹).toReal)
        hR0 hval_nonneg
  refine Finset.sum_nonneg ?_
  intro n _hn
  by_cases hNn : N ≤ Int.toNat n.1
  · simp [hNn]
    have hcoeff_nonneg :
        0 ≤
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 +
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 := by
      exact add_nonneg
        (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight_nonneg
          m hs'_pos.le n.1)
        (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight_nonneg
          m ht'_pos.le n.1)
    exact mul_nonneg hcoeff_nonneg
      (by simpa [weightLossSup] using hweightLossSup_nonneg n)
  · simp [hNn]

/--
Source labels `p.HC.CR`, `e.weaknorms.moreproto`, `e.M.def`, and `a.HM`:
budget form of the sharp summed-weight first-power source split.  The
Section 5.2 small and low tails are paid by their response budgets, while the
two exact edge-loss source integrals `min(sourceMax, 1) * response` and
`badEventTruncation(sourceMax) * response`, each carrying the sharp
`edgeWeightLoss * 2 * sqrt(theta_m)` coefficient, are paid by the free scalar
budgets `sourceMinBudget` and `sourceBadBudget`.
-/
theorem integral_terminalPositiveExcess_defectSum_sq_le_lowerTailBudget_of_sourceMax_min_one_add_badEventTruncation_childResponseAverage
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hstat : Homogenization.Book.Ch04.StationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {k m : ℕ}
    (hkm : k < m) (e : Homogenization.Vec d)
    {smallBudget lowBudget sourceMinBudget sourceBadBudget
      lowerTailBudget : ℝ}
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
      let childAvg := fun a : Homogenization.RegCoeffField d =>
        Homogenization.descendantsAverage Q (m - k)
          (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
      let response := fun a : Homogenization.RegCoeffField d =>
        (5 * β⁻¹) ^ 2 * childAvg a
      let lowerSmall := fun a : Homogenization.RegCoeffField d =>
        Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
            (d := d) m s' a ^ 2 /
          Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
      let upperSmall := fun a : Homogenization.RegCoeffField d =>
        Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
            (d := d) m t' a ^ 2 /
          Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
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
      let childAvg := fun a : Homogenization.RegCoeffField d =>
        Homogenization.descendantsAverage Q (m - k)
          (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
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
      MeasureTheory.Integrable lowSum P)
    (hMinInt :
      let β := section53CoarseFluctuationBeta hP4
      let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
      let p_e :=
        Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
      let q_e :=
        Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
      let childAvg := fun a : Homogenization.RegCoeffField d =>
        Homogenization.descendantsAverage Q (m - k)
          (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
      let response := fun a : Homogenization.RegCoeffField d =>
        (5 * β⁻¹) ^ 2 * childAvg a
      let sourceMax :=
        terminalSpectralPositivePartSourceMax hP hStruct hc k m Q
          (fun x : Homogenization.RegCoeffField d => x)
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          min (sourceMax a) 1 * response a) P)
    (hBadInt :
      let β := section53CoarseFluctuationBeta hP4
      let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
      let p_e :=
        Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
      let q_e :=
        Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
      let childAvg := fun a : Homogenization.RegCoeffField d =>
        Homogenization.descendantsAverage Q (m - k)
          (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
      let response := fun a : Homogenization.RegCoeffField d =>
        (5 * β⁻¹) ^ 2 * childAvg a
      let sourceMax :=
        terminalSpectralPositivePartSourceMax hP hStruct hc k m Q
          (fun x : Homogenization.RegCoeffField d => x)
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          badEventTruncation sourceMax a * response a) P)
    (hSmallBound :
      let β := section53CoarseFluctuationBeta hP4
      let s' := hP4.sLower + β
      let t' := hP4.sUpper + β
      let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
      let p_e :=
        Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
      let q_e :=
        Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
      let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
      let childAvg := fun a : Homogenization.RegCoeffField d =>
        Homogenization.descendantsAverage Q (m - k)
          (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
      let response := fun a : Homogenization.RegCoeffField d =>
        (5 * β⁻¹) ^ 2 * childAvg a
      let lowerSmall := fun a : Homogenization.RegCoeffField d =>
        Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
            (d := d) m s' a ^ 2 /
          Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
      let upperSmall := fun a : Homogenization.RegCoeffField d =>
        Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
            (d := d) m t' a ^ 2 /
          Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
      ∫ a, (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a ∂P ≤
        smallBudget)
    (hLowBound :
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
          (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
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
      ∫ a, lowSum a ∂P ≤ lowBudget)
    (hMinBound :
      let β := section53CoarseFluctuationBeta hP4
      let s' := hP4.sLower + β
      let t' := hP4.sUpper + β
      let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
      let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
      let p_e :=
        Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
      let q_e :=
        Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
      let childAvg := fun a : Homogenization.RegCoeffField d =>
        Homogenization.descendantsAverage Q (m - k)
          (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
      let response := fun a : Homogenization.RegCoeffField d =>
        (5 * β⁻¹) ^ 2 * childAvg a
      let sourceMax :=
        terminalSpectralPositivePartSourceMax hP hStruct hc k m Q
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
          if k ≤ Int.toNat n.1 then
            (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 +
              Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1) *
              weightLossSup n
          else 0
      edgeWeightLoss *
          (2 * Real.sqrt
            (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
          (∫ a, min (sourceMax a) 1 * response a ∂P) ≤
        sourceMinBudget)
    (hBadBound :
      let β := section53CoarseFluctuationBeta hP4
      let s' := hP4.sLower + β
      let t' := hP4.sUpper + β
      let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
      let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
      let p_e :=
        Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
      let q_e :=
        Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
      let childAvg := fun a : Homogenization.RegCoeffField d =>
        Homogenization.descendantsAverage Q (m - k)
          (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
      let response := fun a : Homogenization.RegCoeffField d =>
        (5 * β⁻¹) ^ 2 * childAvg a
      let sourceMax :=
        terminalSpectralPositivePartSourceMax hP hStruct hc k m Q
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
          if k ≤ Int.toNat n.1 then
            (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 +
              Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1) *
              weightLossSup n
          else 0
      edgeWeightLoss *
          (2 * Real.sqrt
            (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
          (∫ a, badEventTruncation sourceMax a * response a ∂P) ≤
        sourceBadBudget)
    (htailBudget :
      smallBudget + lowBudget + sourceMinBudget + sourceBadBudget ≤
        lowerTailBudget) :
    let β := section53CoarseFluctuationBeta hP4
    let s' := hP4.sLower + β
    let t' := hP4.sUpper + β
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let defectSum := fun a : Homogenization.RegCoeffField d =>
      ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
        Real.rpow (3 : ℝ)
            (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          Real.sqrt
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
              (m : ℤ) n p_e q_e a)
    let lowerTerminal := fun a : Homogenization.RegCoeffField d =>
      max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0
    let upperTerminal := fun a : Homogenization.RegCoeffField d =>
      max
        (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0
    ∫ a,
        (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) *
          defectSum a ^ 2 ∂P ≤
      lowerTailBudget := by
  classical
  dsimp only at hSmallInt hLowInt hMinInt hBadInt hSmallBound hLowBound ⊢
  dsimp only at hMinBound hBadBound
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let defectSum : Homogenization.RegCoeffField d → ℝ := fun a =>
    ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
      Real.rpow (3 : ℝ)
          (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
        Real.sqrt
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
            (m : ℤ) n p_e q_e a)
  let childAvg : Homogenization.RegCoeffField d → ℝ := fun a =>
    Homogenization.descendantsAverage Q (m - k)
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
  let response : Homogenization.RegCoeffField d → ℝ := fun a =>
    (5 * β⁻¹) ^ 2 * childAvg a
  let lowerTerminal : Homogenization.RegCoeffField d → ℝ := fun a =>
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
      0
  let upperTerminal : Homogenization.RegCoeffField d → ℝ := fun a =>
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
        hP.barSigmaAtScale hStruct (m : ℤ))
      0
  let lowerSmall : Homogenization.RegCoeffField d → ℝ := fun a =>
    Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
        (d := d) m s' a ^ 2 /
      Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
  let upperSmall : Homogenization.RegCoeffField d → ℝ := fun a =>
    Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
        (d := d) m t' a ^ 2 /
      Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
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
  let sourceMax : Homogenization.RegCoeffField d → ℝ :=
    terminalSpectralPositivePartSourceMax hP hStruct hc k m Q
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
      if k ≤ Int.toNat n.1 then
        (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 +
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1) *
          weightLossSup n
      else 0
  have hdecomp :=
    integral_terminalPositiveExcess_defectSum_sq_le_section52SmallTail_childResponseAverage_add_lowSum_add_edgeWeightLoss_mul_sqrtThetaAtScale_sourceMax_min_one_add_badEventTruncation_mul_childResponseAverage
      hP hstat hStruct hP4 hc hkm e hSmallInt hLowInt hMinInt hBadInt
  have hSmall_le :
      ∫ a, (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a ∂P ≤
        smallBudget := by
    simpa only [β, s', t', Q, p_e, q_e, σ, childAvg, response, lowerSmall,
      upperSmall] using hSmallBound
  have hLow_le : ∫ a, lowSum a ∂P ≤ lowBudget := by
    simpa only [β, s', t', S, Q, p_e, q_e, σ, childAvg, response, lowerSlot,
      upperSlot, lowSum] using hLowBound
  have hMin_le :
      edgeWeightLoss *
          (2 * Real.sqrt
            (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
          (∫ a, min (sourceMax a) 1 * response a ∂P) ≤
        sourceMinBudget := by
    simpa only [β, s', t', S, Q, p_e, q_e, childAvg, response, sourceMax,
      weightLossSup, edgeWeightLoss] using hMinBound
  have hBad_le :
      edgeWeightLoss *
          (2 * Real.sqrt
            (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
          (∫ a, badEventTruncation sourceMax a * response a ∂P) ≤
        sourceBadBudget := by
    simpa only [β, s', t', S, Q, p_e, q_e, childAvg, response, sourceMax,
      weightLossSup, edgeWeightLoss] using hBadBound
  calc
    ∫ a,
        (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) *
          defectSum a ^ 2 ∂P
        ≤
          ∫ a, (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a ∂P +
            ∫ a, lowSum a ∂P +
            edgeWeightLoss *
              (2 * Real.sqrt
                (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
              ((∫ a, min (sourceMax a) 1 * response a ∂P) +
                ∫ a, badEventTruncation sourceMax a * response a ∂P) := by
          simpa only [β, s', t', S, Q, p_e, q_e, σ, defectSum, childAvg, response,
            lowerTerminal, upperTerminal, lowerSmall, upperSmall, lowerSlot,
            upperSlot, lowSum, sourceMax, weightLossSup, edgeWeightLoss]
            using hdecomp
    _ =
        ∫ a, (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a ∂P +
          ∫ a, lowSum a ∂P +
          (edgeWeightLoss *
              (2 * Real.sqrt
                (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
              (∫ a, min (sourceMax a) 1 * response a ∂P) +
            edgeWeightLoss *
              (2 * Real.sqrt
                (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
              (∫ a, badEventTruncation sourceMax a * response a ∂P)) := by
          ring
    _ ≤ smallBudget + lowBudget + (sourceMinBudget + sourceBadBudget) :=
          add_le_add (add_le_add hSmall_le hLow_le)
            (add_le_add hMin_le hBad_le)
    _ ≤ lowerTailBudget := by linarith

end

end Homogenization.HighContrast.EntryScale
