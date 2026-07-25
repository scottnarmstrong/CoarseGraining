import Mathlib.Tactic.Linarith
import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations
import Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.CenteredResponses
import Homogenization.HighContrast.EntryScale.Inputs
import Homogenization.HighContrast.EntryScale.MaximalResponse
import Homogenization.HighContrast.EntryScale.ResponseFluctuation
import Homogenization.HighContrast.EntryScale.ResponseMoment
import Homogenization.HighContrast.EntryScale.RawHighContrastWeakNorm
import Homogenization.HighContrast.EntryScale.LocalTailTransport
import Homogenization.HighContrast.EntryScale.RawHighContrastEnergy.P1

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization.Book.Ch05.Section54.OneStepContraction
open scoped Matrix.Norms.Elementwise

namespace Homogenization.HighContrast.EntryScale

noncomputable section

/--
Below-start crude coefficient of the Section 5.2 low tail: the scale-zero-gap
coefficient sum restricted to scales `n < N0`.  Every summand carries the
geometric weight `3^{-s'(m-n)} <= 3^{-s'(m-N0)}`, so at `N0 := N` the `Nstar`
buffer kills the scale-zero moment factors.
-/
noncomputable def section52LowTailBelowStartCoeff
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (N0 m : ℕ) : ℝ :=
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let dimCoeff : ℝ := (Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)
  let lowerGap : ℝ :=
    (hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ -
      (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹
  let upperGap : ℝ :=
    hP.barSigmaAtScale hStruct (0 : ℤ) -
      hP.barSigmaAtScale hStruct (m : ℤ)
  let lowerRootCoeff : {n : ℤ // n ∈ S} → ℝ := fun n =>
    dimCoeff *
      Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff
        d hP4.xi s' m n.1 *
      Homogenization.Book.Ch04.lambdaInvMomentAtScale
        P 0 hP4.sLower hP4.xi
  let upperRootCoeff : {n : ℤ // n ∈ S} → ℝ := fun n =>
    dimCoeff *
      Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff
        d hP4.xi t' m n.1 *
      Homogenization.Book.Ch04.LambdaMomentAtScale
        P 0 hP4.sUpper hP4.xi
  let gapCoeff : {n : ℤ // n ∈ S} → ℝ := fun n =>
    σ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
        lowerGap +
      σ⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
        upperGap
  let coeffTerm : {n : ℤ // n ∈ S} → ℝ := fun n =>
    σ * lowerRootCoeff n + σ⁻¹ * upperRootCoeff n + gapCoeff n
  S.attach.sum fun n =>
    if N0 ≤ Int.toNat n.1 then 0 else coeffTerm n

/--
Sharp low-tail budget at scales `k <= m` with start scale `N`: the buffered
below-start crude budget plus a second copy of the resized first-power source
budget (whose bracket carries the same stochastic/polynomial/drift roots as
the source channel).
-/
noncomputable def lowTailSharpBudgetAtScales
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) (N k m : ℕ) (hNm : N ≤ m)
    (e : Homogenization.Vec d) (stochRoot polyRoot : ℝ) : ℝ :=
  (5 * (section53CoarseFluctuationBeta hP4)⁻¹) ^ 2 *
      section52LowTailBelowStartCoeff hP hStruct hP4 N m *
      coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e +
    sourceMaxResizedBudgetAtScales hP hStruct hP4 hc N k m hNm e
      stochRoot polyRoot

/--
Source labels `p.HC.CR`, `e.W.low.tail`, `a.HM`, `M_m^st`, and
`l.union.bound`: the Section 5.2 low-tail child-response integral is paid by
the sharp low-tail budget.  The `[N, k)` scales ride the start-window source
maximum through the mixed-scale L-C/L-D pairings into the resized-budget
bracket; only the `n < N` crude tail keeps scale-zero coefficients, with
buffer-killable weights.
-/
theorem integral_section52LowTail_childResponseAverage_special_le_lowTailSharpBudgetAtScales
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) (hcparams : hP4.params = hc.params)
    (hm : HighCenteredMomentParameters d hc)
    (hparams : hP4.params = hm.p4Params) {N k m : ℕ}
    (hNk : N ≤ k) (hkm : k < m)
    (hHM :
      HighCenteredMomentEstimate hm P N
        (intermediateCoarseBlockDeviation hP hStruct
          (fun x : Homogenization.RegCoeffField d => x)))
    (M_sub : ℕ → Homogenization.RegCoeffField d → ℝ)
    (hMsub : AEMeasurable (M_sub m) P)
    {stochRoot polyRoot : ℝ}
    (hfin :
      (∫⁻ ω, ‖terminalCoarseBlockStochasticMax hP hStruct hc N m
          (Homogenization.originCube d (m : ℤ))
          (fun x : Homogenization.RegCoeffField d => x) ω‖ₑ ^ (2 : ℝ) ∂P) +
        (∫⁻ ω, ‖M_sub m ω‖ₑ ^ (2 : ℝ) ∂P) ≠ ⊤)
    (hstochRoot :
      2 * (((∫⁻ ω, ‖terminalCoarseBlockStochasticMax hP hStruct hc N m
            (Homogenization.originCube d (m : ℤ))
            (fun x : Homogenization.RegCoeffField d => x) ω‖ₑ ^ (2 : ℝ) ∂P) +
          (∫⁻ ω, ‖M_sub m ω‖ₑ ^ (2 : ℝ) ∂P)).toReal ^ (1 / (hP4.xi : ℝ))) ≤
        stochRoot)
    (hpolyRoot :
      ((ENNReal.ofReal
          (((2 +
            Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
            (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
              (3 : ℝ) ^
                (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                  ((m - N : ℕ) : ℝ))))) ^ (1 / hm.Q)).toReal ≤ polyRoot))
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
    ∫ a, lowSum a ∂P ≤
      lowTailSharpBudgetAtScales hP hStruct hP4 hc N k m
        (hNk.trans hkm.le) e stochRoot polyRoot := by
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
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
  let response : Homogenization.RegCoeffField d → ℝ := fun a =>
    (5 * β⁻¹) ^ 2 * childAvg a
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
  let responseMoment : ℝ :=
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  let edgeLossBudget : ℝ :=
    Homogenization.geometricDiscount s' 1 /
        Homogenization.geometricDiscount (s' - hc.rhoM) 1 +
      Homogenization.geometricDiscount t' 1 /
        Homogenization.geometricDiscount (t' - hc.rhoM) 1
  have hassembly :=
    integral_section52LowTail_childResponseAverage_special_le_belowStart_add_sourceMaxStart_minBad
      hP hStruct.stationary hStruct hP4 hc hm hparams hNk hkm hHM e
  have hbelow :=
    (integrable_section52LowTailBelow_childResponseAverage_special_and_integral_le_responseMoment
      hP hStruct.stationary hStruct hP4 N hkm e).2
  have hMinChild :
      ∫ a, min (sourceMax a) 1 * childAvg a ∂P ≤
        (stochRoot +
            min (terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) 1) *
          responseMoment := by
    simpa [Q, p_e, q_e, childAvg, sourceMax, responseMoment] using
      integral_min_terminalSourceMax_start_one_mul_childResponseAverage_le_stochasticRoot_add_min_drift_one_mul_responseMoment
        hP hStruct.stationary hStruct hP4 hc hNk hkm M_sub hMsub e hfin hstochRoot
  have hBadChildPair :=
    integral_badEventTruncation_terminalSourceMax_start_mul_childResponseAverage_le_responseMoment_mul_global_polynomialRoot_add_drift
      hP hStruct.stationary hStruct hP4 hc hm hparams hNk hkm hHM e
  have hBadChildRaw :
      ∫ a, badEventTruncation sourceMax a * childAvg a ∂P ≤
        responseMoment *
          ((ENNReal.ofReal
            (((2 +
              Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
              (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
                (3 : ℝ) ^
                  (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                    ((m - N : ℕ) : ℝ))))) ^ (1 / hm.Q)).toReal +
            terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) := by
    simpa [Q, p_e, q_e, childAvg, sourceMax, responseMoment] using hBadChildPair.2
  have hRM_nonneg : 0 ≤ responseMoment := by
    simpa [responseMoment] using
      coarseFluctuationResponseMomentAtScale_nonneg hP hStruct hP4 k m e
  have hBadChild :
      ∫ a, badEventTruncation sourceMax a * childAvg a ∂P ≤
        responseMoment *
          (polyRoot + terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) := by
    refine hBadChildRaw.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hRM_nonneg
    have h := hpolyRoot
    linarith
  have hMinRespEq :
      ∫ a, min (sourceMax a) 1 * response a ∂P =
        (5 * β⁻¹) ^ 2 * ∫ a, min (sourceMax a) 1 * childAvg a ∂P := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with a
    dsimp [response]
    ring
  have hBadRespEq :
      ∫ a, badEventTruncation sourceMax a * response a ∂P =
        (5 * β⁻¹) ^ 2 * ∫ a, badEventTruncation sourceMax a * childAvg a ∂P := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with a
    dsimp [response]
    ring
  have hLowerGapX : 0 < hP4.sLower + section53CoarseFluctuationBeta hP4 - hc.rhoM :=
    sub_pos.mpr (hc.sourceMaxLowerGap_of_params hP4 hcparams)
  have hUpperGapX : 0 < hP4.sUpper + section53CoarseFluctuationBeta hP4 - hc.rhoM :=
    sub_pos.mpr (hc.sourceMaxUpperGap_of_params hP4 hcparams)
  have hedgeX : edgeWeightLoss ≤ edgeLossBudget := by
    have hraw :=
      section52LargeScale_terminalPositiveExcess_edgeWeightLoss_le_discountRatio_of_P4_beta
        (d := d) (P := P) hP4 hc (N := N) (m := m)
        (by simpa [β, s'] using hLowerGapX)
        (by simpa [β, t'] using hUpperGapX)
    simpa [β, s', t', S, Q, weightLossSup, edgeWeightLoss, edgeLossBudget] using hraw
  have hEWL_nonneg : 0 ≤ edgeWeightLoss := by
    simpa [β, s', t', S, Q, weightLossSup, edgeWeightLoss] using
      section52LargeScale_terminalPositiveExcess_edgeWeightLoss_nonneg_of_P4_beta
        (d := d) (P := P) hP4 hc (N := N) (m := m)
  have hchild_nonneg : ∀ a, 0 ≤ childAvg a := by
    intro a
    dsimp [childAvg]
    exact Homogenization.descendantsAverage_nonneg Q (m - k)
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
      (fun R _hR =>
        Homogenization.Book.Ch04.responseJObservableCubeSet_nonneg R p_e q_e a)
  have hsrc_nonneg : ∀ a, 0 ≤ sourceMax a :=
    terminalSpectralPositivePartSourceMax_nonneg hP hStruct hc N m Q
      (fun x : Homogenization.RegCoeffField d => x)
  have hdrift_nonneg : 0 ≤ terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le) :=
    terminalBadMaximalDriftSup_nonneg hP hStruct hc (hNk.trans hkm.le)
  have hstochRoot_nonneg : 0 ≤ stochRoot := by
    refine le_trans ?_ hstochRoot
    positivity
  have hpolyRoot_nonneg : 0 ≤ polyRoot :=
    le_trans ENNReal.toReal_nonneg hpolyRoot
  have hsqrtθ_nonneg :
      0 ≤ 2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) := by
    positivity
  have hr_sq_nonneg : 0 ≤ (5 * β⁻¹) ^ 2 := sq_nonneg _
  have hIsum :
      (∫ a, min (sourceMax a) 1 * childAvg a ∂P) +
          (∫ a, badEventTruncation sourceMax a * childAvg a ∂P) ≤
        responseMoment *
          (stochRoot + polyRoot +
            2 * terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) := by
    have hmin_le :
        min (terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) 1 ≤
          terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le) := min_le_left _ _
    have hsum0 := add_le_add hMinChild hBadChild
    have hstep :
        (stochRoot +
              min (terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) 1) *
            responseMoment +
          responseMoment *
            (polyRoot + terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) ≤
        responseMoment *
          (stochRoot + polyRoot +
            2 * terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) := by
      have h1 :
          (stochRoot +
                min (terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) 1) *
              responseMoment +
            responseMoment *
              (polyRoot + terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) =
          responseMoment *
            (stochRoot + polyRoot +
              terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le) +
              min (terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) 1) := by
        ring
      rw [h1]
      refine mul_le_mul_of_nonneg_left ?_ hRM_nonneg
      linarith
    exact hsum0.trans hstep
  have hsource_term :
      edgeWeightLoss *
          (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
        ((∫ a, min (sourceMax a) 1 * response a ∂P) +
          (∫ a, badEventTruncation sourceMax a * response a ∂P)) ≤
      sourceMaxResizedBudgetAtScales hP hStruct hP4 hc N k m
        (hNk.trans hkm.le) e stochRoot polyRoot := by
    have hbracket_nonneg :
        0 ≤ stochRoot + polyRoot +
          2 * terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le) := by
      linarith
    have hX_nonneg :
        0 ≤ (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
          ((5 * β⁻¹) ^ 2 *
            (responseMoment *
              (stochRoot + polyRoot +
                2 * terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)))) :=
      mul_nonneg hsqrtθ_nonneg
        (mul_nonneg hr_sq_nonneg (mul_nonneg hRM_nonneg hbracket_nonneg))
    calc
      edgeWeightLoss *
          (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
        ((∫ a, min (sourceMax a) 1 * response a ∂P) +
          (∫ a, badEventTruncation sourceMax a * response a ∂P)) =
          edgeWeightLoss *
              (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
            ((5 * β⁻¹) ^ 2 *
              ((∫ a, min (sourceMax a) 1 * childAvg a ∂P) +
                (∫ a, badEventTruncation sourceMax a * childAvg a ∂P))) := by
          rw [hMinRespEq, hBadRespEq]
          ring
      _ ≤ edgeWeightLoss *
              (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
            ((5 * β⁻¹) ^ 2 *
              (responseMoment *
                (stochRoot + polyRoot +
                  2 * terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)))) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg hEWL_nonneg hsqrtθ_nonneg)
          exact mul_le_mul_of_nonneg_left hIsum hr_sq_nonneg
      _ = edgeWeightLoss *
            ((2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
              ((5 * β⁻¹) ^ 2 *
                (responseMoment *
                  (stochRoot + polyRoot +
                    2 * terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le))))) := by
          ring
      _ ≤ edgeLossBudget *
            ((2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
              ((5 * β⁻¹) ^ 2 *
                (responseMoment *
                  (stochRoot + polyRoot +
                    2 * terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)))))
        := mul_le_mul_of_nonneg_right hedgeX hX_nonneg
      _ = sourceMaxResizedBudgetAtScales hP hStruct hP4 hc N k m
            (hNk.trans hkm.le) e stochRoot polyRoot := by
          dsimp [sourceMaxResizedBudgetAtScales, edgeLossBudget,
            responseMoment, β, s', t']
          ring
  have hassembly' :
      ∫ a,
          (S.attach.sum fun n =>
            if k ≤ Int.toNat n.1 then 0 else
              (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
                  (σ *
                    (Homogenization.descendantsAtScale Q n.1).sup'
                      (Homogenization.descendantsAtScale_nonempty Q
                        (by simpa [Q, Homogenization.originCube] using
                          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2))
                      (fun R =>
                        max
                          (Homogenization.Book.Ch02.matrixNorm
                              (Homogenization.coarseBlockMatrix
                                (Homogenization.cubeSet R) a).lowerRight -
                            (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
                          0)) * response a +
                Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
                  (σ⁻¹ *
                    (Homogenization.descendantsAtScale Q n.1).sup'
                      (Homogenization.descendantsAtScale_nonempty Q
                        (by simpa [Q, Homogenization.originCube] using
                          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2))
                      (fun R =>
                        max
                          (Homogenization.Book.Ch02.matrixNorm
                              (Homogenization.coarseBlockMatrix
                                (Homogenization.cubeSet R) a).upperLeft -
                            hP.barSigmaAtScale hStruct (m : ℤ))
                          0)) * response a)) ∂P ≤
        (∫ a,
          (S.attach.sum fun n =>
            if N ≤ Int.toNat n.1 then 0 else
              (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
                  (σ *
                    (Homogenization.descendantsAtScale Q n.1).sup'
                      (Homogenization.descendantsAtScale_nonempty Q
                        (by simpa [Q, Homogenization.originCube] using
                          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2))
                      (fun R =>
                        max
                          (Homogenization.Book.Ch02.matrixNorm
                              (Homogenization.coarseBlockMatrix
                                (Homogenization.cubeSet R) a).lowerRight -
                            (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
                          0)) * response a +
                Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
                  (σ⁻¹ *
                    (Homogenization.descendantsAtScale Q n.1).sup'
                      (Homogenization.descendantsAtScale_nonempty Q
                        (by simpa [Q, Homogenization.originCube] using
                          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2))
                      (fun R =>
                        max
                          (Homogenization.Book.Ch02.matrixNorm
                              (Homogenization.coarseBlockMatrix
                                (Homogenization.cubeSet R) a).upperLeft -
                            hP.barSigmaAtScale hStruct (m : ℤ))
                          0)) * response a)) ∂P) +
          edgeWeightLoss *
              (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
            ((∫ a, min (sourceMax a) 1 * response a ∂P) +
              (∫ a, badEventTruncation sourceMax a * response a ∂P)) := by
    simpa [β, s', t', S, Q, p_e, q_e, σ, childAvg, response, sourceMax,
      weightLossSup, edgeWeightLoss] using hassembly
  have hbelow' :
      ∫ a,
          (S.attach.sum fun n =>
            if N ≤ Int.toNat n.1 then 0 else
              (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
                  (σ *
                    (Homogenization.descendantsAtScale Q n.1).sup'
                      (Homogenization.descendantsAtScale_nonempty Q
                        (by simpa [Q, Homogenization.originCube] using
                          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2))
                      (fun R =>
                        max
                          (Homogenization.Book.Ch02.matrixNorm
                              (Homogenization.coarseBlockMatrix
                                (Homogenization.cubeSet R) a).lowerRight -
                            (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
                          0)) * response a +
                Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
                  (σ⁻¹ *
                    (Homogenization.descendantsAtScale Q n.1).sup'
                      (Homogenization.descendantsAtScale_nonempty Q
                        (by simpa [Q, Homogenization.originCube] using
                          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2))
                      (fun R =>
                        max
                          (Homogenization.Book.Ch02.matrixNorm
                              (Homogenization.coarseBlockMatrix
                                (Homogenization.cubeSet R) a).upperLeft -
                            hP.barSigmaAtScale hStruct (m : ℤ))
                          0)) * response a)) ∂P ≤
        (5 * β⁻¹) ^ 2 * section52LowTailBelowStartCoeff hP hStruct hP4 N m *
          responseMoment := by
    simpa [β, s', t', S, Q, p_e, q_e, σ, childAvg, response, responseMoment,
      section52LowTailBelowStartCoeff] using hbelow
  dsimp only [lowTailSharpBudgetAtScales]
  calc
    ∫ a,
        (S.attach.sum fun n =>
          if k ≤ Int.toNat n.1 then 0 else
            (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
                (σ *
                  (Homogenization.descendantsAtScale Q n.1).sup'
                    (Homogenization.descendantsAtScale_nonempty Q
                      (by simpa [Q, Homogenization.originCube] using
                        Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2))
                    (fun R =>
                      max
                        (Homogenization.Book.Ch02.matrixNorm
                            (Homogenization.coarseBlockMatrix
                              (Homogenization.cubeSet R) a).lowerRight -
                          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
                        0)) * response a +
              Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
                (σ⁻¹ *
                  (Homogenization.descendantsAtScale Q n.1).sup'
                    (Homogenization.descendantsAtScale_nonempty Q
                      (by simpa [Q, Homogenization.originCube] using
                        Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2))
                    (fun R =>
                      max
                        (Homogenization.Book.Ch02.matrixNorm
                            (Homogenization.coarseBlockMatrix
                              (Homogenization.cubeSet R) a).upperLeft -
                          hP.barSigmaAtScale hStruct (m : ℤ))
                        0)) * response a)) ∂P ≤
        (∫ a,
          (S.attach.sum fun n =>
            if N ≤ Int.toNat n.1 then 0 else
              (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
                  (σ *
                    (Homogenization.descendantsAtScale Q n.1).sup'
                      (Homogenization.descendantsAtScale_nonempty Q
                        (by simpa [Q, Homogenization.originCube] using
                          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2))
                      (fun R =>
                        max
                          (Homogenization.Book.Ch02.matrixNorm
                              (Homogenization.coarseBlockMatrix
                                (Homogenization.cubeSet R) a).lowerRight -
                            (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
                          0)) * response a +
                Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
                  (σ⁻¹ *
                    (Homogenization.descendantsAtScale Q n.1).sup'
                      (Homogenization.descendantsAtScale_nonempty Q
                        (by simpa [Q, Homogenization.originCube] using
                          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2))
                      (fun R =>
                        max
                          (Homogenization.Book.Ch02.matrixNorm
                              (Homogenization.coarseBlockMatrix
                                (Homogenization.cubeSet R) a).upperLeft -
                            hP.barSigmaAtScale hStruct (m : ℤ))
                          0)) * response a)) ∂P) +
          edgeWeightLoss *
              (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
            ((∫ a, min (sourceMax a) 1 * response a ∂P) +
              (∫ a, badEventTruncation sourceMax a * response a ∂P)) := hassembly'
    _ ≤ (5 * β⁻¹) ^ 2 * section52LowTailBelowStartCoeff hP hStruct hP4 N m *
            responseMoment +
          sourceMaxResizedBudgetAtScales hP hStruct hP4 hc N k m
            (hNk.trans hkm.le) e stochRoot polyRoot :=
        add_le_add hbelow' hsource_term
    _ = (5 * (section53CoarseFluctuationBeta hP4)⁻¹) ^ 2 *
            section52LowTailBelowStartCoeff hP hStruct hP4 N m *
            coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e +
          sourceMaxResizedBudgetAtScales hP hStruct hP4 hc N k m
            (hNk.trans hkm.le) e stochRoot polyRoot := by
        dsimp [β, responseMoment]

/--
Source labels `e.W.small.tail` and `a.HM` (buffer): the Section 5.2 small-tail
terminal budget coefficient is buffer-small.  The small-tail weight equals
`3^{-s'·m}` exactly, the descendant-card root contributes `3^{(d/ξ)·m}`, and
the paired `σ·λ₀⁻¹`-moment factors are bounded by `2·θ̃₀`; since
`d/ξ < min(sLower, sUpper)`, the whole coefficient decays like
`θ̃₀·3^{-β·m}`, which the `Nstar` buffer drives below any positive target.
-/
theorem exists_bufferExponent_section52SmallTailTerminalResponseBudget_le_eta_mul_terminal_of_Nstar
    {d : ℕ} [NeZero d]
    (params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {P : Homogenization.Book.Ch04.CoeffLaw d}
        (hP : Homogenization.Book.Ch04.LawCarrier P)
        (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P),
        hP4.params = params →
        ∀ {N k m : ℕ},
          N + Nat.ceil
              (B * Real.logb 3
                (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) ≤
            m →
          k ≤ m →
          ∀ e : Homogenization.Vec d,
            section52SmallTailTerminalResponseBudgetAtScales hP hStruct hP4 k m e ≤
              eta *
                (terminalPAtScales hP hStruct k m *
                  coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e) := by
  classical
  let βp : ℝ := section53CoarseFluctuationBetaParams params
  have hβp_pos : 0 < βp := by
    dsimp [βp]
    exact
      Homogenization.Book.Ch05.Section51.section53CoarseFluctuationBetaParams_pos
        params
  let Cp : ℝ :=
    (5 * βp⁻¹) ^ 2 *
      (2 * ((25 * params.sLower⁻¹ * βp⁻¹) ^ 2 +
        (25 * params.sUpper⁻¹ * βp⁻¹) ^ 2))
  have hCp_nonneg : 0 ≤ Cp := by
    dsimp [Cp]
    positivity
  obtain ⟨B, hB_one, hB⟩ :=
    exists_bufferExponent_for_polynomial_geometric_envelope_no_linear_le
      (C := Cp) (A := 1) (c := βp) (η := eta) hCp_nonneg hβp_pos heta
  refine ⟨B, hB_one, ?_⟩
  intro P hP hStruct hP4 hparams N k m hNstar hkm e
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let T : ℝ := Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4
  let L0 : ℝ :=
    Homogenization.Book.Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi
  let l0 : ℝ :=
    Homogenization.Book.Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi
  have hβ_eq : β = βp := by
    dsimp [β, βp]
    simpa [hparams] using
      (section53CoarseFluctuationBetaParams_eq_of_P4 hP4).symm
  have hβ_pos : 0 < β := by
    rw [hβ_eq]; exact hβp_pos
  have hsL_eq : hP4.sLower = params.sLower := by
    rw [← hparams]
    simp
  have hsU_eq : hP4.sUpper = params.sUpper := by
    rw [← hparams]
    simp
  have hT_one : 1 ≤ T := by
    simpa [T] using one_le_initialWidetildeTheta_of_P4 hP hStruct hP4
  have hT_nonneg : 0 ≤ T := by linarith
  have hs'_pos : 0 < s' := by
    have := hP4.sLower_nonneg
    dsimp [s']
    linarith
  have ht'_pos : 0 < t' := by
    have := hP4.sUpper_nonneg
    dsimp [t']
    linarith
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, Homogenization.Book.Ch05.sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hL0_nonneg : 0 ≤ L0 := by
    simpa [L0] using
      Homogenization.Book.Ch04.LambdaMomentAtScale_nonneg P 0 hP4.xi
        hP4.sUpper_pos
  have hl0_nonneg : 0 ≤ l0 := by
    simpa [l0] using
      Homogenization.Book.Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi
        hP4.sLower_pos
  have hpair :=
    coarseFluctuationUnitMomentWeightAtScale_le_two_widetildeTheta_zero
      hP hStruct hP4 m
  have hpair' : σ * l0 + σ⁻¹ * L0 ≤ 2 * T := by
    simpa [coarseFluctuationUnitMomentWeightAtScale, σ, l0, L0, T] using hpair
  have hσl0_le : σ * l0 ≤ 2 * T := by
    have h2 : 0 ≤ σ⁻¹ * L0 :=
      mul_nonneg (inv_nonneg.mpr hσ_nonneg) hL0_nonneg
    linarith
  have hσL0_le : σ⁻¹ * L0 ≤ 2 * T := by
    have h1 : 0 ≤ σ * l0 := mul_nonneg hσ_nonneg hl0_nonneg
    linarith
  -- the descendant-card root at scale 0 of the scale-m cube
  have hm_int_nonneg : (0 : ℤ) ≤ (m : ℤ) := by exact_mod_cast Nat.zero_le m
  have hcard_rpow :
      (((Homogenization.descendantsAtScale
          (Homogenization.originCube d (m : ℤ)) 0).card : ℝ) ^
        (1 / (hP4.xi : ℝ))) =
      Real.rpow (3 : ℝ)
        (((d : ℝ) / (hP4.xi : ℝ)) * (Int.toNat ((m : ℤ) - 0) : ℝ)) := by
    simpa using
      Homogenization.Book.Ch05.Section52.section52_descendantsAtScale_originCube_large_card_rpow
        d hP4.xi m hm_int_nonneg
  have htoNat_m : (Int.toNat ((m : ℤ) - 0) : ℝ) = (m : ℝ) := by
    norm_num
  -- weight identities
  have hW_s' :
      Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m =
        Real.rpow (3 : ℝ) (-s' * (m : ℝ)) :=
    Homogenization.Book.Ch05.Section52.section52SmallTailWeight_eq_rpow
      hs'_pos m
  have hW_t' :
      Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m =
        Real.rpow (3 : ℝ) (-t' * (m : ℝ)) :=
    Homogenization.Book.Ch05.Section52.section52SmallTailWeight_eq_rpow
      ht'_pos m
  have hr_s'_pos : 0 < Real.rpow (3 : ℝ) (-s' * (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hr_t'_pos : 0 < Real.rpow (3 : ℝ) (-t' * (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  -- collapse of the squared-tail-over-weight ratios
  have hratio_s' :
      (25 * hP4.sLower⁻¹ * (s' - hP4.sLower)⁻¹ *
          Real.rpow (3 : ℝ) (-s' * (m : ℝ))) ^ 2 /
        Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m =
      (25 * hP4.sLower⁻¹ * β⁻¹) ^ 2 * Real.rpow (3 : ℝ) (-s' * (m : ℝ)) := by
    rw [hW_s']
    have hs'_sub : s' - hP4.sLower = β := by
      dsimp [s']
      ring
    rw [hs'_sub]
    field_simp
  have hratio_t' :
      (25 * hP4.sUpper⁻¹ * (t' - hP4.sUpper)⁻¹ *
          Real.rpow (3 : ℝ) (-t' * (m : ℝ))) ^ 2 /
        Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m =
      (25 * hP4.sUpper⁻¹ * β⁻¹) ^ 2 * Real.rpow (3 : ℝ) (-t' * (m : ℝ)) := by
    rw [hW_t']
    have ht'_sub : t' - hP4.sUpper = β := by
      dsimp [t']
      ring
    rw [ht'_sub]
    field_simp
  -- rpow decay collection: 3^{-s'·m}·3^{(d/ξ)·m} ≤ 3^{-β·(m-N)}
  have hd_div_lt_sL : (d : ℝ) / (hP4.xi : ℝ) < hP4.sLower :=
    hP4.dim_div_xi_lt_sLower
  have hd_div_lt_sU : (d : ℝ) / (hP4.xi : ℝ) < hP4.sUpper :=
    hP4.dim_div_xi_lt_sUpper
  have hexp_s' :
      Real.rpow (3 : ℝ) (-s' * (m : ℝ)) *
        Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ)) ≤
      Real.rpow (3 : ℝ) (-β * ((m - N : ℕ) : ℝ)) := by
    have hadd :
        Real.rpow (3 : ℝ) (-s' * (m : ℝ)) *
            Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ)) =
          Real.rpow (3 : ℝ)
            (-s' * (m : ℝ) + ((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ)) :=
      (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
    rw [hadd]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hmN_le : ((m - N : ℕ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast Nat.cast_le.mpr (Nat.sub_le m N)
    have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hkey : -s' * (m : ℝ) + ((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ) ≤
        -β * (m : ℝ) := by
      have hgap : (0 : ℝ) ≤ s' - ((d : ℝ) / (hP4.xi : ℝ)) - β := by
        dsimp [s']
        linarith only [hd_div_lt_sL]
      linarith only [mul_nonneg hgap hm_nonneg]
    refine hkey.trans ?_
    have hβ_nonneg : 0 ≤ β := le_of_lt hβ_pos
    linarith only [mul_le_mul_of_nonneg_left hmN_le hβ_nonneg]
  have hexp_t' :
      Real.rpow (3 : ℝ) (-t' * (m : ℝ)) *
        Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ)) ≤
      Real.rpow (3 : ℝ) (-β * ((m - N : ℕ) : ℝ)) := by
    have hadd :
        Real.rpow (3 : ℝ) (-t' * (m : ℝ)) *
            Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ)) =
          Real.rpow (3 : ℝ)
            (-t' * (m : ℝ) + ((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ)) :=
      (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
    rw [hadd]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hmN_le : ((m - N : ℕ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast Nat.cast_le.mpr (Nat.sub_le m N)
    have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hkey : -t' * (m : ℝ) + ((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ) ≤
        -β * (m : ℝ) := by
      have hgap : (0 : ℝ) ≤ t' - ((d : ℝ) / (hP4.xi : ℝ)) - β := by
        dsimp [t']
        linarith only [hd_div_lt_sU]
      linarith only [mul_nonneg hgap hm_nonneg]
    refine hkey.trans ?_
    have hβ_nonneg : 0 ≤ β := le_of_lt hβ_pos
    linarith only [mul_le_mul_of_nonneg_left hmN_le hβ_nonneg]
  -- envelope discharge
  have hceil_gap : Nat.ceil (B * Real.logb 3 (2 + T)) ≤ m - N := by
    have hNstarT :
        N + Nat.ceil (B * Real.logb 3 (2 + T)) ≤ m := by
      simpa [T] using hNstar
    omega
  have hbuf : B * Real.logb 3 (2 + T) ≤ ((m - N : ℕ) : ℝ) :=
    (Nat.ceil_le).mp hceil_gap
  have henv := hB (T := T) (n := m - N) hT_one hbuf
  have henv' :
      Cp * ((2 + T) * Real.rpow (3 : ℝ) (-βp * ((m - N : ℕ) : ℝ))) ≤ eta := by
    simpa [Real.rpow_one] using henv
  -- assemble the coefficient bound
  have hcoeff_le :
      (5 * β⁻¹) ^ 2 *
          (σ * ((25 * hP4.sLower⁻¹ * β⁻¹) ^ 2 *
              Real.rpow (3 : ℝ) (-s' * (m : ℝ))) *
            ((((Homogenization.descendantsAtScale
                (Homogenization.originCube d (m : ℤ)) 0).card : ℝ) ^
              (1 / (hP4.xi : ℝ))) * l0) +
            σ⁻¹ * ((25 * hP4.sUpper⁻¹ * β⁻¹) ^ 2 *
              Real.rpow (3 : ℝ) (-t' * (m : ℝ))) *
            ((((Homogenization.descendantsAtScale
                (Homogenization.originCube d (m : ℤ)) 0).card : ℝ) ^
              (1 / (hP4.xi : ℝ))) * L0)) ≤ eta := by
    rw [hcard_rpow, htoNat_m]
    have hbound1 :
        σ * ((25 * hP4.sLower⁻¹ * β⁻¹) ^ 2 *
            Real.rpow (3 : ℝ) (-s' * (m : ℝ))) *
          (Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ)) * l0) =
        (25 * hP4.sLower⁻¹ * β⁻¹) ^ 2 * (σ * l0) *
          (Real.rpow (3 : ℝ) (-s' * (m : ℝ)) *
            Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ))) := by
      ring
    have hbound2 :
        σ⁻¹ * ((25 * hP4.sUpper⁻¹ * β⁻¹) ^ 2 *
            Real.rpow (3 : ℝ) (-t' * (m : ℝ))) *
          (Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ)) * L0) =
        (25 * hP4.sUpper⁻¹ * β⁻¹) ^ 2 * (σ⁻¹ * L0) *
          (Real.rpow (3 : ℝ) (-t' * (m : ℝ)) *
            Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ))) := by
      ring
    rw [hbound1, hbound2]
    have hprod_s'_nonneg :
        0 ≤ Real.rpow (3 : ℝ) (-s' * (m : ℝ)) *
          Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ)) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.rpow_nonneg (by norm_num) _)
    have hprod_t'_nonneg :
        0 ≤ Real.rpow (3 : ℝ) (-t' * (m : ℝ)) *
          Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ)) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.rpow_nonneg (by norm_num) _)
    have hc1_nonneg : 0 ≤ (25 * hP4.sLower⁻¹ * β⁻¹) ^ 2 := sq_nonneg _
    have hc2_nonneg : 0 ≤ (25 * hP4.sUpper⁻¹ * β⁻¹) ^ 2 := sq_nonneg _
    have hσl0_nonneg : 0 ≤ σ * l0 := mul_nonneg hσ_nonneg hl0_nonneg
    have hσL0_nonneg : 0 ≤ σ⁻¹ * L0 :=
      mul_nonneg (inv_nonneg.mpr hσ_nonneg) hL0_nonneg
    have hrpow_bound_nonneg :
        0 ≤ Real.rpow (3 : ℝ) (-β * ((m - N : ℕ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hterm1 :
        (25 * hP4.sLower⁻¹ * β⁻¹) ^ 2 * (σ * l0) *
            (Real.rpow (3 : ℝ) (-s' * (m : ℝ)) *
              Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ))) ≤
          (25 * hP4.sLower⁻¹ * β⁻¹) ^ 2 * (2 * T) *
            Real.rpow (3 : ℝ) (-β * ((m - N : ℕ) : ℝ)) := by
      have h1 :
          (25 * hP4.sLower⁻¹ * β⁻¹) ^ 2 * (σ * l0) *
              (Real.rpow (3 : ℝ) (-s' * (m : ℝ)) *
                Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ))) ≤
            (25 * hP4.sLower⁻¹ * β⁻¹) ^ 2 * (2 * T) *
              (Real.rpow (3 : ℝ) (-s' * (m : ℝ)) *
                Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ))) := by
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hσl0_le hc1_nonneg) hprod_s'_nonneg
        simpa [mul_assoc] using this
      refine h1.trans ?_
      refine mul_le_mul_of_nonneg_left hexp_s' ?_
      have h2T_nonneg : 0 ≤ 2 * T := by linarith
      exact mul_nonneg hc1_nonneg h2T_nonneg
    have hterm2 :
        (25 * hP4.sUpper⁻¹ * β⁻¹) ^ 2 * (σ⁻¹ * L0) *
            (Real.rpow (3 : ℝ) (-t' * (m : ℝ)) *
              Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ))) ≤
          (25 * hP4.sUpper⁻¹ * β⁻¹) ^ 2 * (2 * T) *
            Real.rpow (3 : ℝ) (-β * ((m - N : ℕ) : ℝ)) := by
      have h1 :
          (25 * hP4.sUpper⁻¹ * β⁻¹) ^ 2 * (σ⁻¹ * L0) *
              (Real.rpow (3 : ℝ) (-t' * (m : ℝ)) *
                Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ))) ≤
            (25 * hP4.sUpper⁻¹ * β⁻¹) ^ 2 * (2 * T) *
              (Real.rpow (3 : ℝ) (-t' * (m : ℝ)) *
                Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ))) := by
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hσL0_le hc2_nonneg) hprod_t'_nonneg
        simpa [mul_assoc] using this
      refine h1.trans ?_
      refine mul_le_mul_of_nonneg_left hexp_t' ?_
      have h2T_nonneg : 0 ≤ 2 * T := by linarith
      exact mul_nonneg hc2_nonneg h2T_nonneg
    have hsum_le :
        (5 * β⁻¹) ^ 2 *
            ((25 * hP4.sLower⁻¹ * β⁻¹) ^ 2 * (σ * l0) *
                (Real.rpow (3 : ℝ) (-s' * (m : ℝ)) *
                  Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ))) +
              (25 * hP4.sUpper⁻¹ * β⁻¹) ^ 2 * (σ⁻¹ * L0) *
                (Real.rpow (3 : ℝ) (-t' * (m : ℝ)) *
                  Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ)))) ≤
          (5 * β⁻¹) ^ 2 *
            (((25 * hP4.sLower⁻¹ * β⁻¹) ^ 2 +
                (25 * hP4.sUpper⁻¹ * β⁻¹) ^ 2) * (2 * T) *
              Real.rpow (3 : ℝ) (-β * ((m - N : ℕ) : ℝ))) := by
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      calc
        (25 * hP4.sLower⁻¹ * β⁻¹) ^ 2 * (σ * l0) *
              (Real.rpow (3 : ℝ) (-s' * (m : ℝ)) *
                Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ))) +
            (25 * hP4.sUpper⁻¹ * β⁻¹) ^ 2 * (σ⁻¹ * L0) *
              (Real.rpow (3 : ℝ) (-t' * (m : ℝ)) *
                Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (m : ℝ))) ≤
            (25 * hP4.sLower⁻¹ * β⁻¹) ^ 2 * (2 * T) *
                Real.rpow (3 : ℝ) (-β * ((m - N : ℕ) : ℝ)) +
              (25 * hP4.sUpper⁻¹ * β⁻¹) ^ 2 * (2 * T) *
                Real.rpow (3 : ℝ) (-β * ((m - N : ℕ) : ℝ)) :=
          add_le_add hterm1 hterm2
        _ = ((25 * hP4.sLower⁻¹ * β⁻¹) ^ 2 +
              (25 * hP4.sUpper⁻¹ * β⁻¹) ^ 2) * (2 * T) *
            Real.rpow (3 : ℝ) (-β * ((m - N : ℕ) : ℝ)) := by
          ring
    refine hsum_le.trans ?_
    have hfinal_eq :
        (5 * β⁻¹) ^ 2 *
            (((25 * hP4.sLower⁻¹ * β⁻¹) ^ 2 +
                (25 * hP4.sUpper⁻¹ * β⁻¹) ^ 2) * (2 * T) *
              Real.rpow (3 : ℝ) (-β * ((m - N : ℕ) : ℝ))) =
        ((5 * β⁻¹) ^ 2 *
            (2 * ((25 * hP4.sLower⁻¹ * β⁻¹) ^ 2 +
              (25 * hP4.sUpper⁻¹ * β⁻¹) ^ 2))) *
          (T * Real.rpow (3 : ℝ) (-β * ((m - N : ℕ) : ℝ))) := by
      ring
    rw [hfinal_eq]
    have hCp_match :
        (5 * β⁻¹) ^ 2 *
            (2 * ((25 * hP4.sLower⁻¹ * β⁻¹) ^ 2 +
              (25 * hP4.sUpper⁻¹ * β⁻¹) ^ 2)) = Cp := by
      dsimp [Cp]
      rw [hβ_eq, hsL_eq, hsU_eq]
    rw [hCp_match, hβ_eq]
    have hT_le : T * Real.rpow (3 : ℝ) (-βp * ((m - N : ℕ) : ℝ)) ≤
        (2 + T) * Real.rpow (3 : ℝ) (-βp * ((m - N : ℕ) : ℝ)) := by
      have hr : 0 ≤ Real.rpow (3 : ℝ) (-βp * ((m - N : ℕ) : ℝ)) :=
        Real.rpow_nonneg (by norm_num) _
      exact mul_le_mul_of_nonneg_right
        (by linarith only [] : T ≤ 2 + T) hr
    calc
      Cp * (T * Real.rpow (3 : ℝ) (-βp * ((m - N : ℕ) : ℝ))) ≤
          Cp * ((2 + T) * Real.rpow (3 : ℝ) (-βp * ((m - N : ℕ) : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ hCp_nonneg
        exact hT_le
      _ ≤ eta := henv'
  -- final assembly against the terminal pair
  have hP_nonneg : 0 ≤ terminalPAtScales hP hStruct k m :=
    terminalPAtScales_nonneg_of_P4 hP hStruct hP4 hkm
  have hRM_nonneg :
      0 ≤ coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e :=
    coarseFluctuationResponseMomentAtScale_nonneg hP hStruct hP4 k m e
  have hcoeff_ratio_le :
      (5 * β⁻¹) ^ 2 *
        (σ * ((25 * hP4.sLower⁻¹ * (s' - hP4.sLower)⁻¹ *
              Real.rpow (3 : ℝ) (-s' * (m : ℝ))) ^ 2 /
            Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m) *
          ((((Homogenization.descendantsAtScale
              (Homogenization.originCube d (m : ℤ)) 0).card : ℝ) ^
            (1 / (hP4.xi : ℝ))) * l0) +
          σ⁻¹ * ((25 * hP4.sUpper⁻¹ * (t' - hP4.sUpper)⁻¹ *
              Real.rpow (3 : ℝ) (-t' * (m : ℝ))) ^ 2 /
            Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m) *
          ((((Homogenization.descendantsAtScale
              (Homogenization.originCube d (m : ℤ)) 0).card : ℝ) ^
            (1 / (hP4.xi : ℝ))) * L0)) ≤ eta := by
    rw [hratio_s', hratio_t']
    exact hcoeff_le
  have hmain :=
    mul_le_mul_of_nonneg_right hcoeff_ratio_le
      (mul_nonneg hP_nonneg hRM_nonneg)
  have hbudget_eq :
      section52SmallTailTerminalResponseBudgetAtScales hP hStruct hP4 k m e =
        (5 * β⁻¹) ^ 2 *
          (σ * ((25 * hP4.sLower⁻¹ * (s' - hP4.sLower)⁻¹ *
                Real.rpow (3 : ℝ) (-s' * (m : ℝ))) ^ 2 /
              Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m) *
            ((((Homogenization.descendantsAtScale
                (Homogenization.originCube d (m : ℤ)) 0).card : ℝ) ^
              (1 / (hP4.xi : ℝ))) * l0) +
            σ⁻¹ * ((25 * hP4.sUpper⁻¹ * (t' - hP4.sUpper)⁻¹ *
                Real.rpow (3 : ℝ) (-t' * (m : ℝ))) ^ 2 /
              Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m) *
            ((((Homogenization.descendantsAtScale
                (Homogenization.originCube d (m : ℤ)) 0).card : ℝ) ^
              (1 / (hP4.xi : ℝ))) * L0)) *
          (terminalPAtScales hP hStruct k m *
            coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e) := by
    dsimp only [section52SmallTailTerminalResponseBudgetAtScales, β, s', t',
      σ, l0, L0]
  rw [hbudget_eq]
  exact hmain

end

end Homogenization.HighContrast.EntryScale
