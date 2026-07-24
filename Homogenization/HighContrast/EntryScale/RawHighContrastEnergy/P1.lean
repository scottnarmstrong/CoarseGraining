import Mathlib.Tactic.Linarith
import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations
import Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.CenteredResponses
import Homogenization.HighContrast.EntryScale.Inputs
import Homogenization.HighContrast.EntryScale.MaximalResponse
import Homogenization.HighContrast.EntryScale.ResponseFluctuation
import Homogenization.HighContrast.EntryScale.ResponseMoment
import Homogenization.HighContrast.EntryScale.RawHighContrastWeakNorm.P8
import Homogenization.HighContrast.EntryScale.LocalTailTransport.P2

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization.Book.Ch05.Section54.OneStepContraction
open scoped Matrix.Norms.Elementwise


/-!
# Raw high-contrast response energy

Concrete bridges for the raw high-contrast centered-response energy
inequalities.  This file deliberately works below the maximal-response
combiner and below the final Section 5.3 coarse-fluctuation shortcut.
-/


namespace Homogenization.HighContrast.EntryScale

noncomputable section

/--
Source labels `p.HC.CR` and `e.W.low.tail`: the normalized cutoff-oscillation
bridge is converted back to the unnormalized raw-energy remainder slot.  This
is the form needed when `specialWeakNormEnergyRemainderAtScale` is bounded
directly: the cutoff term contributes to the `C_norm * eps⁻¹ * weakNorm`
budget, not to the raw `eps * F_m` centering slot.
-/
theorem cutoffOscillation_special_expectedResponse_le_rawEnergy_tail
    {d : ℕ} [NeZero d] :
    ∃ C_osc : ℝ, 0 ≤ C_osc ∧
      ∀ {P : Homogenization.Book.Ch04.CoeffLaw d}
        (hP : Homogenization.Book.Ch04.LawCarrier P)
        (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
        {k m : ℕ}, k < m → ∀ e : Homogenization.Vec d,
        Homogenization.vecNormSq e = 1 →
        ∀ {eps C_norm : ℝ}, 0 < eps → eps ≤ 1 → 0 < C_norm →
        ∀ {T_edge decay : ℝ},
        (let β := section53CoarseFluctuationBeta hP4
         (C_osc * C_norm⁻¹) *
            ((β ^ 2)⁻¹ *
              Real.rpow (3 : ℝ)
                (-2 * β * (((m - k : ℕ) : ℝ))) *
              contrastExcessAtScale hP hStruct m) ≤ decay * T_edge) →
        let Q : Homogenization.TriadicCube d :=
          Homogenization.originCube d (m : ℤ)
        let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
        let p_e :=
          Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
        let q_e :=
          Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
        Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant
              Q *
            Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffScaleSep
              Q j *
            Homogenization.Book.Ch04.expectedResponseJCubeSet P Q p_e q_e
          ≤ C_norm * eps⁻¹ * decay * T_edge := by
  rcases normalized_cutoffOscillation_special_expectedResponse_le_decay_tail
      (d := d) with ⟨C_osc, hC_osc_nonneg, hnorm_all⟩
  refine ⟨C_osc, hC_osc_nonneg, ?_⟩
  intro P hP hStruct hP4 k m hkm e he eps C_norm heps_pos heps_le hC_norm_pos
    T_edge decay htail
  dsimp only at htail ⊢
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let cutoffTerm : ℝ :=
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant
        Q *
      Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffScaleSep
        Q j *
      Homogenization.Book.Ch04.expectedResponseJCubeSet P Q p_e q_e
  have hnorm :
      eps * C_norm⁻¹ * cutoffTerm ≤ decay * T_edge := by
    simpa [Q, j, p_e, q_e, cutoffTerm] using
      hnorm_all hP hStruct hP4 hkm e he heps_pos heps_le hC_norm_pos htail
  have hfactor_nonneg : 0 ≤ C_norm * eps⁻¹ :=
    mul_nonneg hC_norm_pos.le (inv_nonneg.mpr heps_pos.le)
  have hscaled :
      C_norm * eps⁻¹ * (eps * C_norm⁻¹ * cutoffTerm) ≤
        C_norm * eps⁻¹ * (decay * T_edge) :=
    mul_le_mul_of_nonneg_left hnorm hfactor_nonneg
  have hcancel :
      C_norm * eps⁻¹ * (eps * C_norm⁻¹ * cutoffTerm) = cutoffTerm := by
    calc
      C_norm * eps⁻¹ * (eps * C_norm⁻¹ * cutoffTerm)
          = (eps * eps⁻¹) * (C_norm * C_norm⁻¹) * cutoffTerm := by ring
      _ = cutoffTerm := by
          rw [mul_inv_cancel₀ (ne_of_gt heps_pos),
            mul_inv_cancel₀ (ne_of_gt hC_norm_pos)]
          ring
  calc
    cutoffTerm
        = C_norm * eps⁻¹ * (eps * C_norm⁻¹ * cutoffTerm) :=
          hcancel.symm
    _ ≤ C_norm * eps⁻¹ * (decay * T_edge) := hscaled
    _ = C_norm * eps⁻¹ * decay * T_edge := by ring


/--
Source labels `p.HC.CR`, `e.W.first.sum`, `e.W.low.tail`,
`e.J.moment.bound`, `a.HM`, and `e.raw.CR.energy`: remainder bridge for the
SHARP source-max child-response route.  The source budget hypothesis carries
the sharp summed-weight first-power split (`min(sourceMax,1)` plus
`badEventTruncation` against the response with the `2 * sqrt(theta_m)`
normalizer) instead of the mis-sized Holder package.
-/
theorem specialWeakNormEnergyRemainderAtScale_le_centering_add_components_with_sourceMax_minBad_childResponse_lowerTailBudget
    {d : ℕ} [NeZero d] :
    ∃ C_osc C_lin : ℝ,
      0 ≤ C_osc ∧ 0 ≤ C_lin ∧
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
        ∀ {eps C_norm T_edge decay lowerTailBudget
            smallBudget lowBudget sourceBudget childTailBudget : ℝ},
        0 < eps → eps ≤ 1 → 0 < C_norm →
        (let β := section53CoarseFluctuationBeta hP4
         (C_osc * C_norm⁻¹) *
            ((β ^ 2)⁻¹ *
              Real.rpow (3 : ℝ)
                (-2 * β * (((m - k : ℕ) : ℝ))) *
              contrastExcessAtScale hP hStruct m) ≤ decay * T_edge) →
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
        let p_e :=
          Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
        let q_e :=
          Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
        let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
        let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
        let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
        let K :=
          Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst
            d
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
        specialWeakNormEnergyRemainderAtScale hP hStruct hP4 k m e ≤
          C_lin * eps * contrastExcessAtScale hP hStruct m +
            C_norm * eps⁻¹ * decay * T_edge +
              C_lin * eps⁻¹ *
                (16 *
                  (highScaleAverage + K ^ 2 * localSlots +
                    K ^ 2 * lowerTailBudget)) := by
  classical
  rcases cutoffOscillation_special_expectedResponse_le_rawEnergy_tail
      (d := d) with ⟨C_osc, hC_osc_nonneg, hcutoff_all⟩
  rcases
      Homogenization.HighContrast.EntryScale.linearProductTerms_special_le_centering_add_componentIntegrals_with_sourceMax_minBad_childResponse_lowerTailBudget_localWindow
        (d := d) with ⟨C_lin, hC_lin_nonneg, hlin_all⟩
  refine ⟨C_osc, C_lin, hC_osc_nonneg, hC_lin_nonneg, ?_⟩
  intro P hP hstat hStruct hP4 hc hm hparams N k m hNk hkm hHM e he eps C_norm
    T_edge decay lowerTailBudget smallBudget lowBudget sourceBudget
    childTailBudget heps_pos heps_le hC_norm_pos hcutoff_geo hSmallInt
    hLowInt hSmallBound hLowBound hSourceBudget hChildTailBudget htailBudget
  dsimp only at hcutoff_geo hSmallInt hLowInt hSmallBound hLowBound
  dsimp only at hSourceBudget hChildTailBudget htailBudget ⊢
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let s' := hP4.sLower + β
  let t := hP4.sUpper + 2 * β
  let t' := hP4.sUpper + β
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let θ := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
  let K :=
    Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst
      d
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
  let cutoffTerm : ℝ :=
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant
        Q *
      Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffScaleSep
        Q j *
      Homogenization.Book.Ch04.expectedResponseJCubeSet P Q p_e q_e
  let linProd : ℝ :=
    (1 / 2 : ℝ) * ‖q0_e‖ * (gradCoeff * ∫ a, gradWeak a ∂P) +
      (1 / 2 : ℝ) * ‖p0_e‖ * (fluxCoeff * ∫ a, fluxWeak a ∂P) +
        productCoeff * (Real.sqrt G * Real.sqrt F)
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
  have hcutoff :
      cutoffTerm ≤ C_norm * eps⁻¹ * decay * T_edge := by
    simpa [β, Q, j, p_e, q_e, cutoffTerm] using
      hcutoff_all hP hStruct hP4 hkm e he heps_pos heps_le hC_norm_pos
        hcutoff_geo
  have hlin :
      linProd ≤
        C_lin * eps * (Real.sqrt θ - 1) ^ 2 +
          C_lin * eps⁻¹ *
            (16 *
              (highScaleAverage + K ^ 2 * localSlots +
                K ^ 2 * lowerTailBudget)) := by
    simpa [β, s, s', t, t', Q, p_e, q_e, p0_e, q0_e, σ, θ, K,
      gradWeak, fluxWeak, gradCoeff, fluxCoeff, productCoeff, G, F,
      highScaleAverage, localSlots, linProd] using
      hlin_all hP hstat hStruct hP4 hc hm hparams hNk hkm hHM e he heps_pos
        heps_le hSmallInt hLowInt hSmallBound hLowBound hSourceBudget
        hChildTailBudget htailBudget
  have hcenter :
      C_lin * eps * (Real.sqrt θ - 1) ^ 2 ≤
        C_lin * eps * contrastExcessAtScale hP hStruct m := by
    have hcenter_base :=
      sqrt_thetaAtScale_sub_one_sq_le_contrastExcessAtScale
        hP hStruct hP4 m
    exact mul_le_mul_of_nonneg_left hcenter_base
      (mul_nonneg hC_lin_nonneg heps_pos.le)
  have hlin' :
      linProd ≤
        C_lin * eps * contrastExcessAtScale hP hStruct m +
          C_lin * eps⁻¹ *
              (16 *
                (highScaleAverage + K ^ 2 * localSlots +
                  K ^ 2 * lowerTailBudget)) :=
    hlin.trans (add_le_add hcenter le_rfl)
  have hremainder :
      specialWeakNormEnergyRemainderAtScale hP hStruct hP4 k m e =
        cutoffTerm + linProd := by
    dsimp [specialWeakNormEnergyRemainderAtScale, β, s, t, Q, j, p_e, q_e,
      p0_e, q0_e, gradWeak, fluxWeak, G, F, cutoffTerm, linProd,
      gradCoeff, fluxCoeff, productCoeff]
  calc
    specialWeakNormEnergyRemainderAtScale hP hStruct hP4 k m e
        = cutoffTerm + linProd := hremainder
    _ ≤
        C_norm * eps⁻¹ * decay * T_edge +
          (C_lin * eps * contrastExcessAtScale hP hStruct m +
            C_lin * eps⁻¹ *
              (16 *
                (highScaleAverage + K ^ 2 * localSlots +
                  K ^ 2 * lowerTailBudget))) := by
          exact add_le_add hcutoff hlin'
    _ =
          C_lin * eps * contrastExcessAtScale hP hStruct m +
          C_norm * eps⁻¹ * decay * T_edge +
            C_lin * eps⁻¹ *
              (16 *
                (highScaleAverage + K ^ 2 * localSlots +
                  K ^ 2 * lowerTailBudget)) := by
          ring

/--
Source labels `l.Jtilde.energy.bound` and `l.weaknorms.moreproto`:
integrability of the special gradient weak-norm square needed by the raw
centered-response energy estimate.  LIH proves this for its internal
weak-norm maximizer abbreviation; this theorem exposes the unfolded canonical
square used by the raw-energy bridge.
-/
theorem integrable_specialGradientWeakNormSquare_atScales_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Homogenization.Vec d)
    (he : Homogenization.Book.Ch02.vecNorm e = 1) :
    let β := section53CoarseFluctuationBeta hP4
    let s := hP4.sLower + 2 * β
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
    MeasureTheory.Integrable
      (fun a : Homogenization.CoeffField d =>
        (Homogenization.Book.Ch04.canonicalScalarResponseGradientWeakNormCubeSet
            (Homogenization.originCube d (m : ℤ)) s p_e q_e p0_e a) ^ 2) P := by
  dsimp only
  have he_sq : Homogenization.vecNormSq e = 1 :=
    Homogenization.Book.Ch05.Section54.GoodScale.vecNormSq_eq_one_of_vecNorm_eq_one he
  have hbase :
      MeasureTheory.Integrable
        (Internal.specialGradientWeakNormSquare hP hStruct hP4 m e) P :=
    integrable_specialGradientWeakNormSquare_from_weakNormMaximizer
      hP hStruct.stationary hStruct hP4 hkm e he_sq
  exact hbase.congr <|
    Filter.Eventually.of_forall fun a =>
      Internal.specialGradientWeakNormSquare.eq_1 hP hStruct hP4 m e a

/--
Source labels `l.Jtilde.energy.bound` and `l.weaknorms.moreproto`:
integrability of the special flux weak-norm square needed by the raw
centered-response energy estimate, unfolded from LIH's internal abbreviation
to the canonical raw-energy hypothesis.
-/
theorem integrable_specialFluxWeakNormSquare_atScales_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Homogenization.Vec d)
    (he : Homogenization.Book.Ch02.vecNorm e = 1) :
    let β := section53CoarseFluctuationBeta hP4
    let t := hP4.sUpper + 2 * β
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
    MeasureTheory.Integrable
      (fun a : Homogenization.CoeffField d =>
        (Homogenization.Book.Ch04.canonicalScalarResponseFluxWeakNormCubeSet
            (Homogenization.originCube d (m : ℤ)) t p_e q_e q0_e a) ^ 2) P := by
  dsimp only
  have he_sq : Homogenization.vecNormSq e = 1 :=
    Homogenization.Book.Ch05.Section54.GoodScale.vecNormSq_eq_one_of_vecNorm_eq_one he
  have hbase :
      MeasureTheory.Integrable
        (Internal.specialFluxWeakNormSquare hP hStruct hP4 m e) P :=
    integrable_specialFluxWeakNormSquare_from_weakNormMaximizer
      hP hStruct.stationary hStruct hP4 hkm e he_sq
  exact hbase.congr <|
    Filter.Eventually.of_forall fun a =>
      Internal.specialFluxWeakNormSquare.eq_1 hP hStruct hP4 m e a

/-- Local tau nonnegativity needed by the raw high-contrast component
compression.  This duplicates the no-drop API under a raw-energy-specific name
to avoid changing the existing import graph. -/
theorem tauAtScale_special_nonneg_of_P4_rawHighContrastEnergy
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k ≤ m) (e : Homogenization.Vec d) :
    0 ≤
      Homogenization.Book.Ch05.tauAtScale P (m : ℤ) (k : ℤ)
        (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
        (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) := by
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hkm
  have hBlockM :
      MeasureTheory.Integrable
        (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube
          (Homogenization.originCube d (m : ℤ))) P :=
    Homogenization.Book.Ch05.Section52.originBlockIntegrableAtScale_from_P4
      hP hStruct hP4 m
  have hBlockK :
      MeasureTheory.Integrable
        (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube
          (Homogenization.originCube d (k : ℤ))) P :=
    Homogenization.Book.Ch05.Section52.originBlockIntegrableAtScale_from_P4
      hP hStruct hP4 k
  have hDescBlock :
      ∀ R,
        R ∈ Homogenization.descendantsAtScale
            (Homogenization.originCube d (m : ℤ)) (k : ℤ) →
          MeasureTheory.Integrable
            (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube R) P := by
    intro R hR
    exact
      hP.integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
        hStruct.stationary hk_nonneg hkm_int hR hBlockK
  exact
    Homogenization.Book.Ch05.Section52.tauAtScale_nonneg_of_integrable_coarseFullBlockMatrixAtCube
      hP hStruct.stationary hk_nonneg hkm_int
      (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
      (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e)
      hBlockM hDescBlock

/-- Canonical weak-norm contribution with an explicit lower-edge budget slot. -/
noncomputable def specialWeakNormEnergyContributionWithLowerEdgeBudgetAtScale
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Homogenization.Vec d) (lowerEdgeBudget : ℝ) : ℝ :=
  let P_km := terminalPAtScales hP hStruct k m
  weakNormContribution (1 + contrastExcessAtScale hP hStruct m)
    (coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m)
    (P_km * weightedTauSumAtScales hP hStruct hP4 k m e)
    lowerEdgeBudget 0

/-- Older deterministic source drift carried by the memory lower-edge excess. -/
def sourceMaxMemoryTermOfGrid
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hc : HighContrastExponents d) (N Nstar L i : ℕ) : ℝ :=
  let F_i : ℝ := contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)
  let Hprev : ℝ :=
    memory (memoryDecay hc L)
      (initialMemory hc.rhoM N Nstar
        (fun n => contrastExcessAtScale hP hStruct n))
      (memoryGridDrop
        (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
      (i - 1)
  Hprev ^ 2 / (1 + F_i)

/-- Canonical lower-tail response budget on a grid step. -/
def sourceMaxCanonicalLowerTailBudgetOfGrid
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (Nstar L i : ℕ) (e : Homogenization.Vec d) (decay : ℝ) : ℝ :=
  let m : ℕ := memoryGridScale Nstar L i
  let k : ℕ := memoryGridScale Nstar L (i - 1)
  let F_i : ℝ := contrastExcessAtScale hP hStruct m
  let T_edge : ℝ := (1 + F_i) ^ 2 / F_i
  let P_km : ℝ := terminalPAtScales hP hStruct k m
  let responseMoment : ℝ :=
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  decay * (T_edge + P_km * responseMoment)

/-- Nonnegativity of the source-max edge-loss scalar. -/
private theorem sourceMax_edgeLossBudget_nonneg
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) (hcparams : hP4.params = hc.params) :
    0 ≤
      (let β := section53CoarseFluctuationBeta hP4
       let s' := hP4.sLower + β
       let t' := hP4.sUpper + β
       Homogenization.geometricDiscount s' 1 /
           Homogenization.geometricDiscount (s' - hc.rhoM) 1 +
         Homogenization.geometricDiscount t' 1 /
           Homogenization.geometricDiscount (t' - hc.rhoM) 1) := by
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  have hs'_pos : 0 < s' := by
    have hgap := hc.sourceMaxLowerGap_of_params hP4 hcparams
    dsimp [s', β]
    linarith [hc.rhoM_pos, hgap]
  have ht'_pos : 0 < t' := by
    have hgap := hc.sourceMaxUpperGap_of_params hP4 hcparams
    dsimp [t', β]
    linarith [hc.rhoM_pos, hgap]
  have hLowerGap : 0 < s' - hc.rhoM := by
    dsimp [s', β]
    exact sub_pos.mpr (hc.sourceMaxLowerGap_of_params hP4 hcparams)
  have hUpperGap : 0 < t' - hc.rhoM := by
    dsimp [t', β]
    exact sub_pos.mpr (hc.sourceMaxUpperGap_of_params hP4 hcparams)
  have hs_num :
      0 ≤ Homogenization.geometricDiscount s' 1 :=
    (Homogenization.geometricDiscount_pos (by nlinarith [hs'_pos])).le
  have hs_den :
      0 ≤ Homogenization.geometricDiscount (s' - hc.rhoM) 1 :=
    (Homogenization.geometricDiscount_pos (by nlinarith [hLowerGap])).le
  have ht_num :
      0 ≤ Homogenization.geometricDiscount t' 1 :=
    (Homogenization.geometricDiscount_pos (by nlinarith [ht'_pos])).le
  have ht_den :
      0 ≤ Homogenization.geometricDiscount (t' - hc.rhoM) 1 :=
    (Homogenization.geometricDiscount_pos (by nlinarith [hUpperGap])).le
  exact add_nonneg (div_nonneg hs_num hs_den) (div_nonneg ht_num ht_den)

/--
Source labels `p.HC.CR` and `e.M.def`: scale-independent constant prefactor of
the resized source-max budget.  This is the exact product of the no-growth
geometric-discount edge-loss budget (the scalar payment of the summed
`edgeWeightLoss` coefficient) and the Section 5.3 window constant
`(5 * beta⁻¹)^2` multiplying the response moment in the sharp first-power
source split.
-/
def sourceMaxSharpConst
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) : ℝ :=
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  (Homogenization.geometricDiscount s' 1 /
      Homogenization.geometricDiscount (s' - hc.rhoM) 1 +
    Homogenization.geometricDiscount t' 1 /
      Homogenization.geometricDiscount (t' - hc.rhoM) 1) *
    (5 * β⁻¹) ^ 2

/-- The resized source-max constant prefactor is nonnegative. -/
theorem sourceMaxSharpConst_nonneg
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) (hcparams : hP4.params = hc.params) :
    0 ≤ sourceMaxSharpConst hP4 hc := by
  dsimp [sourceMaxSharpConst]
  exact mul_nonneg (sourceMax_edgeLossBudget_nonneg hP4 hc hcparams) (sq_nonneg _)

/-- Parameter-level form of `sourceMaxSharpConst`. -/
noncomputable def sourceMaxSharpConstParams
    {d : ℕ}
    (params : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    (hc : HighContrastExponents d) : ℝ :=
  let β := section53CoarseFluctuationBetaParams params
  let s' := params.sLower + β
  let t' := params.sUpper + β
  (Homogenization.geometricDiscount s' 1 /
      Homogenization.geometricDiscount (s' - hc.rhoM) 1 +
    Homogenization.geometricDiscount t' 1 /
      Homogenization.geometricDiscount (t' - hc.rhoM) 1) *
    (5 * β⁻¹) ^ 2

/-- Under `hP4.params = params` the sharp constant is parameter-determined. -/
theorem sourceMaxSharpConst_eq_params
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d}
    (hparams : hP4.params = params) (hc : HighContrastExponents d) :
    sourceMaxSharpConst hP4 hc = sourceMaxSharpConstParams params hc := by
  have hβ :
      section53CoarseFluctuationBeta hP4 =
        section53CoarseFluctuationBetaParams params := by
    simpa [hparams] using
      (section53CoarseFluctuationBetaParams_eq_of_P4 hP4).symm
  have hs : params.sLower = hP4.sLower := by
    rw [← hparams]
    simp
  have ht : params.sUpper = hP4.sUpper := by
    rw [← hparams]
    simp
  simp [sourceMaxSharpConst, sourceMaxSharpConstParams, hβ, hs, ht]

/--
Source labels `p.HC.CR`, `e.weaknorms.moreproto`, `e.M.def`, and
`e.det.memory`: resized source-max budget at scales `k <= m`, in the sharp
summed-weight first-power split shape.  The exact summed edge weight loss is
paid by the no-growth geometric-discount budget, the sharp normalization
`2 * sqrt(theta_m)` multiplies the response moment, and the two first-power
source integrals are paid by the free scalar roots `stochRoot`, `polyRoot`
plus twice the deterministic weighted drift supremum.
-/
def sourceMaxResizedBudgetAtScales
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) (N k m : ℕ) (hNm : N ≤ m)
    (e : Homogenization.Vec d) (stochRoot polyRoot : ℝ) : ℝ :=
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let responseMoment : ℝ :=
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  let edgeLossBudget : ℝ :=
    Homogenization.geometricDiscount s' 1 /
        Homogenization.geometricDiscount (s' - hc.rhoM) 1 +
      Homogenization.geometricDiscount t' 1 /
        Homogenization.geometricDiscount (t' - hc.rhoM) 1
  edgeLossBudget *
      (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
      ((5 * β⁻¹) ^ 2 * responseMoment) *
    (stochRoot + polyRoot + 2 * terminalBadMaximalDriftSup hP hStruct hc hNm)

/--
Grid form of the resized source-max budget on the memory grid step `i`, at
scales `k := m_{i-1}` and `m := m_i`.
-/
def sourceMaxResizedBudgetOfGrid
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) (N Nstar L i : ℕ) (hNNstar : N ≤ Nstar)
    (e : Homogenization.Vec d) (stochRoot polyRoot : ℝ) : ℝ :=
  sourceMaxResizedBudgetAtScales hP hStruct hP4 hc N
    (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i)
    (hNNstar.trans (Nat.le_add_right Nstar (i * L))) e stochRoot polyRoot

/--
Source labels `e.M.def`, `e.det.memory`, and `e.nodrop`: scalar payment of the
resized first-power source budget.  The sharp `2 * sqrt(theta_m) * rM` factor
is absorbed by the paired terminal-response budget `C_resp * (1 + F)`, the
drift supremum is folded through the no-drop memory recursion
`q⁻¹ H_i = Hprev + Delta <= Hprev + rho * F`, and the linear previous-memory
term is folded by AM-GM into the quadratic memory channel `Hprev^2 / (1 + F)`
plus a `c_fold` share of the terminal edge weight `1 + F <= (1 + F)^2 / F`.
-/
theorem resizedSourceBudget_scalar_le_decay_mul_edge_add_memory
    {E C_resp S rM D F Hprev q_invH Delta stochRoot polyRoot etaSrc
      polyRootBound rho c_fold decay P_km : ℝ}
    (hE_nonneg : 0 ≤ E)
    (hC_resp_nonneg : 0 ≤ C_resp)
    (hD_nonneg : 0 ≤ D)
    (hF_pos : 0 < F)
    (hstochRoot_nonneg : 0 ≤ stochRoot)
    (hpolyRoot_nonneg : 0 ≤ polyRoot)
    (hstochRoot_le : stochRoot ≤ etaSrc)
    (hpolyRoot_le : polyRoot ≤ polyRootBound)
    (hrho_nonneg : 0 ≤ rho)
    (hc_fold_pos : 0 < c_fold)
    (hP_km_rM_nonneg : 0 ≤ P_km * rM)
    (hsqrt : S * rM ≤ C_resp / 2 * (1 + F))
    (hdrift : D * (1 + F) ≤ q_invH)
    (hrec : q_invH = Hprev + Delta)
    (hDelta_le : Delta ≤ rho * F)
    (hdecay :
      E * C_resp * (etaSrc + polyRootBound + 2 * rho + c_fold) ≤ decay) :
    E * (2 * S) * rM * (stochRoot + polyRoot + 2 * D) ≤
      decay * ((1 + F) ^ 2 / F + P_km * rM) +
        E * C_resp / c_fold * (Hprev ^ 2 / (1 + F)) := by
  have hden_pos : 0 < 1 + F := by linarith
  have hK_nonneg : 0 ≤ E * C_resp := mul_nonneg hE_nonneg hC_resp_nonneg
  have hbracket_nonneg : 0 ≤ etaSrc + polyRootBound + 2 * rho + c_fold := by
    linarith
  have hdecay_nonneg : 0 ≤ decay :=
    le_trans (mul_nonneg hK_nonneg hbracket_nonneg) hdecay
  have hdrift' : D * (1 + F) ≤ Hprev + rho * F := by
    rw [hrec] at hdrift
    linarith
  have hfold :
      2 * (E * C_resp) * Hprev ≤
        E * C_resp / c_fold * (Hprev ^ 2 / (1 + F)) +
          E * C_resp * c_fold * (1 + F) := by
    have hcT_pos : 0 < c_fold * (1 + F) := mul_pos hc_fold_pos hden_pos
    have hcT_ne : c_fold * (1 + F) ≠ 0 := ne_of_gt hcT_pos
    have hc_ne : c_fold ≠ 0 := ne_of_gt hc_fold_pos
    have hden_ne : (1 + F) ≠ 0 := ne_of_gt hden_pos
    have hbase :
        2 * Hprev ≤ Hprev ^ 2 / (c_fold * (1 + F)) + c_fold * (1 + F) := by
      have hdiv_nonneg :
          0 ≤ (Hprev - c_fold * (1 + F)) ^ 2 / (c_fold * (1 + F)) :=
        div_nonneg (sq_nonneg _) hcT_pos.le
      have hexpand :
          (Hprev - c_fold * (1 + F)) ^ 2 / (c_fold * (1 + F)) =
            Hprev ^ 2 / (c_fold * (1 + F)) + c_fold * (1 + F) - 2 * Hprev := by
        field_simp
        ring
      rw [hexpand] at hdiv_nonneg
      linarith
    have hscaled :
        E * C_resp * (2 * Hprev) ≤
          E * C_resp * (Hprev ^ 2 / (c_fold * (1 + F)) + c_fold * (1 + F)) :=
      mul_le_mul_of_nonneg_left hbase hK_nonneg
    have hsplit :
        E * C_resp * (Hprev ^ 2 / (c_fold * (1 + F)) + c_fold * (1 + F)) =
          E * C_resp / c_fold * (Hprev ^ 2 / (1 + F)) +
            E * C_resp * c_fold * (1 + F) := by
      field_simp
    linarith [hscaled, hsplit]
  have hedge : 1 + F ≤ (1 + F) ^ 2 / F := by
    rw [le_div_iff₀ hF_pos]
    nlinarith
  calc
    E * (2 * S) * rM * (stochRoot + polyRoot + 2 * D) =
        S * rM * (2 * E * (stochRoot + polyRoot + 2 * D)) := by ring
    _ ≤ C_resp / 2 * (1 + F) * (2 * E * (stochRoot + polyRoot + 2 * D)) := by
        have hX_nonneg : 0 ≤ stochRoot + polyRoot + 2 * D := by linarith
        have hfac_nonneg :
            0 ≤ 2 * E * (stochRoot + polyRoot + 2 * D) :=
          mul_nonneg (by linarith) hX_nonneg
        exact mul_le_mul_of_nonneg_right hsqrt hfac_nonneg
    _ = E * C_resp * (1 + F) * (stochRoot + polyRoot) +
          2 * (E * C_resp) * (D * (1 + F)) := by ring
    _ ≤ E * C_resp * (1 + F) * (etaSrc + polyRootBound) +
          2 * (E * C_resp) * (Hprev + rho * F) := by
        have hfirst :
            E * C_resp * (1 + F) * (stochRoot + polyRoot) ≤
              E * C_resp * (1 + F) * (etaSrc + polyRootBound) :=
          mul_le_mul_of_nonneg_left (by linarith)
            (mul_nonneg hK_nonneg hden_pos.le)
        have hsecond :
            2 * (E * C_resp) * (D * (1 + F)) ≤
              2 * (E * C_resp) * (Hprev + rho * F) :=
          mul_le_mul_of_nonneg_left hdrift' (by linarith)
        exact add_le_add hfirst hsecond
    _ = E * C_resp * (1 + F) * (etaSrc + polyRootBound) +
          2 * (E * C_resp) * Hprev + 2 * (E * C_resp) * rho * F := by ring
    _ ≤ E * C_resp * (1 + F) * (etaSrc + polyRootBound) +
          (E * C_resp / c_fold * (Hprev ^ 2 / (1 + F)) +
            E * C_resp * c_fold * (1 + F)) +
          2 * (E * C_resp) * rho * (1 + F) := by
        have hrhoF :
            2 * (E * C_resp) * rho * F ≤
              2 * (E * C_resp) * rho * (1 + F) :=
          mul_le_mul_of_nonneg_left (by linarith)
            (mul_nonneg (by linarith) hrho_nonneg)
        linarith [hfold, hrhoF]
    _ = E * C_resp * (etaSrc + polyRootBound + 2 * rho + c_fold) * (1 + F) +
          E * C_resp / c_fold * (Hprev ^ 2 / (1 + F)) := by ring
    _ ≤ decay * (1 + F) +
          E * C_resp / c_fold * (Hprev ^ 2 / (1 + F)) := by
        have hpay := mul_le_mul_of_nonneg_right hdecay hden_pos.le
        linarith
    _ ≤ decay * ((1 + F) ^ 2 / F) +
          E * C_resp / c_fold * (Hprev ^ 2 / (1 + F)) := by
        have hpay := mul_le_mul_of_nonneg_left hedge hdecay_nonneg
        linarith
    _ ≤ decay * ((1 + F) ^ 2 / F + P_km * rM) +
          E * C_resp / c_fold * (Hprev ^ 2 / (1 + F)) := by
        have hsplit :
            decay * ((1 + F) ^ 2 / F + P_km * rM) =
              decay * ((1 + F) ^ 2 / F) + decay * (P_km * rM) := by ring
        have hpos : 0 ≤ decay * (P_km * rM) :=
          mul_nonneg hdecay_nonneg hP_km_rM_nonneg
        linarith

end

end Homogenization.HighContrast.EntryScale
