import Homogenization.HighContrast.EntryScale.BadMaximal
import Homogenization.HighContrast.EntryScale.TerminalLowerEdge
import Homogenization.HighContrast.EntryScale.ResponseFluctuation
import Homogenization.HighContrast.EntryScale.ResponseMoment
import Homogenization.HighContrast.EntryScale.Lyapunov.P2
import Homogenization.HighContrast.EntryScale.RawHighContrastEnergy.P2
import Homogenization.HighContrast.EntryScale.RawHighContrastEnergy.P3

/-!
# Main assembly for the high-moment entry-scale development

This file records the final assembly target.  The public theorem statement
should be added only after the source provenance has fixed the exact binder
order and the external inputs.
-/

namespace Homogenization.HighContrast.EntryScale

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization.Book.Ch05.Section54.OneStepContraction
open scoped ENNReal
open scoped Matrix.Norms.Elementwise

private theorem section53CoarseFluctuationBetaCoreParams_pos_of_params
    {d : ℕ}
    (params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d) :
    0 < section53CoarseFluctuationBetaCoreParams params := by
  have hgap : 0 < 1 - params.sUpper - params.sLower := by
    linarith [params.sum_lt_one]
  have hupper : 0 < params.sUpper := params.sUpper_pos
  have hlower : 0 < params.sLower := params.sLower_pos
  have hupper_gain :
      0 < params.sUpper - (d : ℝ) / (params.xi : ℝ) := by
    linarith [params.dim_div_xi_lt_sUpper]
  have hlower_gain :
      0 < params.sLower - (d : ℝ) / (params.xi : ℝ) := by
    linarith [params.dim_div_xi_lt_sLower]
  unfold section53CoarseFluctuationBetaCoreParams
  exact lt_min hgap
    (lt_min hupper (lt_min hlower (lt_min hupper_gain hlower_gain)))

private theorem section53CoarseFluctuationBetaParams_pos_of_params
    {d : ℕ}
    (params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d) :
    0 < section53CoarseFluctuationBetaParams params := by
  unfold section53CoarseFluctuationBetaParams
  nlinarith [section53CoarseFluctuationBetaCoreParams_pos_of_params params]


/--
Source labels `l.S.and.J`, `e.raw.CR.energy`, `p.HC.CR`, `a.HM`, `M_m^st`,
`l.union.bound`, and `e.nodrop`: no-bad lower-memory main bridge on the SHARP
resized source track.  The child-tail source budget is
`sourceMaxResizedBudgetOfGrid` (summed-weight first-power split with the
`2 * sqrt(theta_m)` normalizer and free stochastic/polynomial roots) instead
of the mis-sized Holder package.
-/
theorem exists_rawEnergyConstants_bufferExponent_lyapunov_step_of_main_buffer_and_lower_memory_no_bad_linear_resized_scalars
    {d : ℕ} [NeZero d] {hc : HighContrastExponents d}
    (params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    (hm : HighCenteredMomentParameters d hc)
    (hhmP4 : hm.p4Params = params) (hcp : hc.params = params) :
    ∃ C_osc C_lin C_high : ℝ,
      0 ≤ C_osc ∧ 0 ≤ C_lin ∧ 0 ≤ C_high ∧
      ∀ (L : ℕ) {etaS etaSt delta_sc decay : ℝ},
      0 < etaS → 0 < etaSt → 0 < delta_sc → 0 < L → 0 < decay →
    ∃ B : ℝ,
      1 ≤ B ∧
        ∀ {P : Homogenization.Book.Ch04.CoeffLaw d}
          (hP : Homogenization.Book.Ch04.LawCarrier P)
          (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
          (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P),
          hP4.params = params →
          ∀ {N Nstar i : ℕ} (e : Homogenization.Vec d)
          {A K lambda rho C C_delta C_memory C_edgeMem C_S C_fluct C_sqrt C_norm
            eps coeff memoryCoeff edgeMemoryCoeff lowerEdgeBudget smallBudget
            lowBudget childTailBudget : ℝ},
            Homogenization.Book.Ch02.vecNorm e = 1 →
            1 ≤ i →
            (hNNstar : N ≤ Nstar) →
            ∀ (M_sub : ℕ → Homogenization.CoeffField d → ℝ),
            AEMeasurable (M_sub (memoryGridScale Nstar L i)) P →
            ∀ {stochRoot polyRoot : ℝ},
            ((∫⁻ ω, ‖terminalCoarseBlockStochasticMax hP hStruct hc N
                (memoryGridScale Nstar L i)
                (Homogenization.originCube d ((memoryGridScale Nstar L i : ℕ) : ℤ))
                (fun x : Homogenization.CoeffField d => x) ω‖ₑ ^ (2 : ℝ) ∂P) +
              (∫⁻ ω, ‖M_sub (memoryGridScale Nstar L i) ω‖ₑ ^ (2 : ℝ) ∂P) ≠ ⊤) →
            (2 * (((∫⁻ ω, ‖terminalCoarseBlockStochasticMax hP hStruct hc N
                  (memoryGridScale Nstar L i)
                  (Homogenization.originCube d ((memoryGridScale Nstar L i : ℕ) : ℤ))
                  (fun x : Homogenization.CoeffField d => x) ω‖ₑ ^ (2 : ℝ) ∂P) +
                (∫⁻ ω, ‖M_sub (memoryGridScale Nstar L i) ω‖ₑ ^ (2 : ℝ) ∂P)).toReal ^
                (1 / (hP4.xi : ℝ))) ≤ stochRoot) →
            ((ENNReal.ofReal
                (((2 +
                  Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
                  (hm.C_Q * (((memoryGridScale Nstar L i - N + 1 : ℕ) : ℝ) *
                    (3 : ℝ) ^
                      (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                        ((memoryGridScale Nstar L i - N : ℕ) : ℝ))))) ^
                (1 / hm.Q)).toReal ≤ polyRoot) →
            0 ≤ lambda →
            0 ≤ A →
            0 ≤ K →
            0 ≤ edgeMemoryCoeff →
            0 ≤ C_edgeMem →
            4 * memoryCoeff ≤ K ^ 2 →
            (1 + rho)⁻¹ + A * memoryDecay hc L ≤ lambda →
            memoryDecay hc L ≤ lambda →
            (K + 16 * edgeMemoryCoeff) +
                A * (memoryDecay hc L *
                      (1 + rho * (K + 16 * edgeMemoryCoeff))) ≤ lambda * A →
            0 < C →
            0 ≤ C_delta →
            0 ≤ C_sqrt →
            0 < C_norm →
            0 < eps →
            eps ≤ 1 →
            0 ≤ rho → 0 < rho → rho ≤ 1 →
            C ≤ C_delta →
            C_S ≤ C_delta →
            delta_sc ≤ contrastExcessAtScale hP hStruct
              (memoryGridScale Nstar L i) →
            2 * (1 + (delta_sc / 2)⁻¹) ^ 2 ≤ C_fluct →
            2 * section53CoarseFluctuationWeightSumConstant hP4 ≤ C_fluct →
            C * C_fluct ≤ C_S →
            C * (2 * section53CoarseFluctuationWeightSumConstant hP4) ≤
              C_delta →
            C * C_sqrt * Real.sqrt (delta_sc / 2)⁻¹ ≤ C_delta →
            (2 : ℝ) ≤ C_sqrt ^ 2 →
            0 ≤ lowerEdgeBudget →
            0 ≤ childTailBudget →
            (noDropWindow rho
                (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1)))
                (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) →
             let m : ℕ := memoryGridScale Nstar L i
             let k : ℕ := memoryGridScale Nstar L (i - 1)
             let T_edge : ℝ :=
              (1 + contrastExcessAtScale hP hStruct m) ^ 2 /
                contrastExcessAtScale hP hStruct m
             let P_km : ℝ := terminalPAtScales hP hStruct k m
             let canonicalLowerTailBudget : ℝ :=
              decay *
                (T_edge +
                  P_km *
                    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e)
             canonicalLowerTailBudget ≤ lowerEdgeBudget) →
            specialWeakNormEnergyFirstCoeffAtScale d
              (memoryGridScale Nstar L i) ≤ C →
            C_lin ≤ C →
            (let β := section53CoarseFluctuationBeta hP4
             let K :=
              Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst
                d
             C_lin * 16 * (C_high * β⁻¹) + C_lin * 16 * K ^ 2 ≤ C) →
            (let β := section53CoarseFluctuationBeta hP4
             let K :=
              Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst
                d
             C_lin * 16 * K ^ 2 * (5 * β⁻¹) ≤ C) →
            (let K :=
              Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst
                d
             C_norm + C_lin * 16 * K ^ 2 + C_lin * 16 * K ^ 2 ≤ C) →
            (let m : ℕ := memoryGridScale Nstar L i
             let k : ℕ := memoryGridScale Nstar L (i - 1)
             let T_edge : ℝ :=
              (1 + contrastExcessAtScale hP hStruct m) ^ 2 /
                contrastExcessAtScale hP hStruct m
             let β := section53CoarseFluctuationBeta hP4
             (C_osc * C_norm⁻¹) *
                ((β ^ 2)⁻¹ *
                  Real.rpow (3 : ℝ)
                    (-2 * β * (((m - k : ℕ) : ℝ))) *
                  contrastExcessAtScale hP hStruct m) ≤ decay * T_edge) →
            (let m : ℕ := memoryGridScale Nstar L i
             let k : ℕ := memoryGridScale Nstar L (i - 1)
             let β := section53CoarseFluctuationBeta hP4
             let s' := hP4.sLower + β
             let t' := hP4.sUpper + β
             let Q : Homogenization.TriadicCube d :=
              Homogenization.originCube d (m : ℤ)
             let p_e :=
              Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
             let q_e :=
              Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
             let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
             let childAvg := fun a : Homogenization.CoeffField d =>
              Homogenization.descendantsAverage Q (m - k)
                (fun R =>
                  Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
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
            (let m : ℕ := memoryGridScale Nstar L i
             let k : ℕ := memoryGridScale Nstar L (i - 1)
             let β := section53CoarseFluctuationBeta hP4
             let s' := hP4.sLower + β
             let t' := hP4.sUpper + β
             let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
             let Q : Homogenization.TriadicCube d :=
              Homogenization.originCube d (m : ℤ)
             let p_e :=
              Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
             let q_e :=
              Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
             let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
             let childAvg := fun a : Homogenization.CoeffField d =>
              Homogenization.descendantsAverage Q (m - k)
                (fun R =>
                  Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
             let response := fun a : Homogenization.CoeffField d =>
              (5 * β⁻¹) ^ 2 * childAvg a
             let lowerSlot :
                Homogenization.CoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
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
             let upperSlot :
                Homogenization.CoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
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
            (let m : ℕ := memoryGridScale Nstar L i
             let k : ℕ := memoryGridScale Nstar L (i - 1)
             let sourceBudget : ℝ :=
              sourceMaxResizedBudgetOfGrid hP hStruct hP4 hc N Nstar L i
                hNNstar e stochRoot polyRoot
         let β := section53CoarseFluctuationBeta hP4
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
            (let m : ℕ := memoryGridScale Nstar L i
             let k : ℕ := memoryGridScale Nstar L (i - 1)
             let sourceBudget : ℝ :=
              sourceMaxResizedBudgetOfGrid hP hStruct hP4 hc N Nstar L i
                hNNstar e stochRoot polyRoot
         childTailBudget + smallBudget + lowBudget + sourceBudget ≤ lowerEdgeBudget) →
            (noDropWindow rho
                (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1)))
                (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) →
             let m : ℕ := memoryGridScale Nstar L i
             let F_i : ℝ := contrastExcessAtScale hP hStruct m
             let Hprev : ℝ :=
              memory (memoryDecay hc L)
                (initialMemory hc.rhoM N Nstar
                  (fun n => contrastExcessAtScale hP hStruct n))
                (memoryGridDrop
                  (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
                (i - 1)
             C * eps⁻¹ * lowerEdgeBudget ≤
              C_delta * eps⁻¹ * decay * F_i +
                C_memory * eps⁻¹ * (Hprev ^ 2 / (1 + F_i)) +
                C_edgeMem * eps⁻¹ *
                  ((Hprev /
                      (1 +
                        contrastExcessAtScale hP hStruct
                          (memoryGridScale Nstar L (i - 1)))) *
                    terminalPAtScales hP hStruct
                      (memoryGridScale Nstar L (i - 1))
                      (memoryGridScale Nstar L i))) →
            N + Nat.ceil
                (B * Real.logb 3
                  (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) ≤
              memoryGridScale Nstar L i →
            HighCenteredMomentEstimate hm P N
              (intermediateCoarseBlockDeviation hP hStruct
                (fun x : Homogenization.CoeffField d => x)) →
            C_delta *
              (Real.sqrt rho + eps + eps⁻¹ * (etaS + etaSt + rho + rho ^ 2) +
                eps⁻¹ * decay) ≤ coeff →
            C_memory * eps⁻¹ ≤ memoryCoeff →
            C_edgeMem * eps⁻¹ ≤ edgeMemoryCoeff →
            2 * coeff ≤ (1 / 2 : ℝ) →
            lyapunovValue A
                (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
                (memory (memoryDecay hc L)
                  (initialMemory hc.rhoM N Nstar
                    (fun n => contrastExcessAtScale hP hStruct n))
                  (memoryGridDrop
                    (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
                  i) ≤
              lambda *
                lyapunovValue A
                  (contrastExcessAtScale hP hStruct
                    (memoryGridScale Nstar L (i - 1)))
                  (memory (memoryDecay hc L)
                    (initialMemory hc.rhoM N Nstar
                      (fun n => contrastExcessAtScale hP hStruct n))
                    (memoryGridDrop
                      (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
                    (i - 1)) := by
  rcases
      rawHighContrastResponseEnergy_atScales_of_P4_with_weakNormContribution_lowerEdgeBudget_sourceMax_resized_childTailBudget_terms
        params with
    ⟨C_osc, C_lin, C_high, hC_osc_nonneg, hC_lin_nonneg,
      hC_high_nonneg, hraw_all⟩
  refine ⟨C_osc, C_lin, C_high, hC_osc_nonneg, hC_lin_nonneg,
    hC_high_nonneg, ?_⟩
  intro L etaS etaSt delta_sc decay hηS hηSt hdelta_sc_pos hL_pos hdecay_pos
  obtain ⟨B, hB_one, hB_fluct⟩ :=
    exists_bufferExponent_terminal_weight_mul_coarseFluctuationFullBlockSumAtScale_le_stochastic_add_drift_of_windowLength
      hm L hηS
  refine ⟨B, hB_one, ?_⟩
  intro P hP hStruct hP4 hparams N Nstar i e A K lambda rho C C_delta
    C_memory C_edgeMem C_S C_fluct C_sqrt C_norm eps coeff memoryCoeff
    edgeMemoryCoeff lowerEdgeBudget smallBudget lowBudget childTailBudget
    he hi hNNstar M_sub hMsub stochRoot polyRoot hfin hstochRoot hpolyRoot
    hlambda_nonneg
    hA_nonneg hK_nonneg hedgeMemoryCoeff_nonneg hedgeMem_nonneg hKmem_le
    hdrop_coeff hdrop_memory_coeff
    hmemory_coeff hC_pos hC_delta_nonneg hC_sqrt_nonneg hC_norm_pos
    heps_pos heps_le_one hrho_nonneg hrho_pos hrho_le_one hC_eps hC_S
    hdelta_sc_le_F hC_eta hC_rho hC_fluct_budget hbudget_tau
    hbudget_sqrt hC_response_le hLowerBudget_nonneg hChildTail_nonneg
    hcanonicalLowerBudget
    hfirst_le hcenter_le hS_coeff hTau_coeff hL_coeff
    hcutoff_geo hSmallBound hLowBound hChildTailBudget htailBudget
    hLowerMemoryBudget
    hNstar hHM hcoeff_bound hmemoryCoeff hedgeMemoryCoeff hsmall
  have hP4_hm : hP4.params = hm.p4Params := hparams.trans hhmP4.symm
  have hP4_hc : hP4.params = hc.params := hparams.trans hcp.symm
  have hC_nonneg : 0 ≤ C := le_of_lt hC_pos
  let F_i : ℝ := contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)
  let delta : ℝ := delta_sc / 2
  let r_m : ℝ := Real.sqrt (1 + F_i)
  let P_km : ℝ :=
    terminalPAtScales hP hStruct
      (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i)
  let s : Finset ℕ :=
    Finset.Icc (memoryGridScale Nstar L (i - 1) + 1)
      (memoryGridScale Nstar L i)
  let w : ℕ → ℝ :=
    section53CoarseFluctuationScaleWeight hP4 (memoryGridScale Nstar L i)
  let tau : ℕ → ℝ := fun j =>
    Homogenization.Book.Ch05.tauAtScale P
      ((memoryGridScale Nstar L i : ℕ) : ℤ) (j : ℤ)
      (Homogenization.Book.Ch05.specialPAtScale hP hStruct
        ((memoryGridScale Nstar L i : ℕ) : ℤ) e)
      (Homogenization.Book.Ch05.specialQAtScale hP hStruct
        ((memoryGridScale Nstar L i : ℕ) : ℤ) e)
  let drop : ℕ → ℝ := fun j =>
    contrastExcessAtScale hP hStruct j -
      contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)
  let Cw : ℝ := section53CoarseFluctuationWeightSumConstant hP4
  let T_weight : ℝ := (1 + F_i) ^ 2 / F_i
  let weakNormGood : ℝ :=
    specialWeakNormEnergyContributionWithLowerEdgeBudgetAtScale hP hStruct hP4
      (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i) e
      lowerEdgeBudget
  let weakNormGoodStar : ℝ := weakNormGood
  let lowerEdge : ℝ := lowerEdgeBudget
  let lowerEdgeStar : ℝ := lowerEdgeBudget
  let C_threshold : ℝ := (1 + delta⁻¹) ^ 2
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    linarith
  have hdelta_lt_delta_sc : delta < delta_sc := by
    dsimp [delta]
    linarith
  have hdelta_lt_F : delta < F_i :=
    hdelta_lt_delta_sc.trans_le (by simpa [F_i] using hdelta_sc_le_F)
  have hdelta_le_F : delta ≤ F_i := le_of_lt hdelta_lt_F
  have hF_pos : 0 < F_i :=
    hdelta_sc_pos.trans_le (by simpa [F_i] using hdelta_sc_le_F)
  have hdecay_nonneg : 0 ≤ decay := le_of_lt hdecay_pos
  have hT_weight_nonneg : 0 ≤ T_weight := by
    dsimp [T_weight]
    exact div_nonneg (sq_nonneg _) (le_of_lt hF_pos)
  have hkm_strict :
      memoryGridScale Nstar L (i - 1) < memoryGridScale Nstar L i :=
    memoryGridScale_lt_of_pos_L hi hL_pos
  have hkm_grid :
      memoryGridScale Nstar L (i - 1) ≤ memoryGridScale Nstar L i :=
    hkm_strict.le
  have hNk :
      N ≤ memoryGridScale Nstar L (i - 1) := by
    dsimp [memoryGridScale]
    exact hNNstar.trans (Nat.le_add_right Nstar ((i - 1) * L))
  have hNk_plus : N ≤ memoryGridScale Nstar L (i - 1) + 1 := by
    omega
  have hwindowLength :
      memoryGridScale Nstar L i - memoryGridScale Nstar L (i - 1) ≤ L := by
    have hscale_eq :
        memoryGridScale Nstar L i =
          memoryGridScale Nstar L (i - 1) + L := by
      dsimp [memoryGridScale]
      have hi_eq : i = (i - 1) + 1 := by omega
      have hmul_eq : i * L = (i - 1) * L + L := by
        calc
          i * L = ((i - 1) + 1) * L :=
            congrArg (fun n : ℕ => n * L) hi_eq
          _ = (i - 1) * L + 1 * L := by rw [Nat.add_mul]
          _ = (i - 1) * L + L := by rw [one_mul]
      rw [hmul_eq]
      omega
    rw [hscale_eq]
    exact le_of_eq (Nat.add_sub_cancel_left (memoryGridScale Nstar L (i - 1)) L)
  have hr_nonneg : 0 ≤ r_m := by
    dsimp [r_m]
    exact Real.sqrt_nonneg (1 + F_i)
  have hP_nonneg : 0 ≤ P_km := by
    dsimp [P_km]
    exact terminalPAtScales_nonneg_of_P4 hP hStruct hP4 hkm_grid
  have hP_le_of_noDrop :
      noDropWindow rho
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1)))
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) →
        P_km ≤ 4 * r_m := by
    intro hno
    have hP_le :=
      terminalPAtScales_le_four_mul_sqrt_contrastExcess_of_noDrop_of_P4
        hP hStruct hP4 hkm_grid hno hrho_pos hrho_le_one
    simpa [P_km, r_m, F_i] using hP_le
  have hC_threshold : (1 + delta⁻¹) ^ 2 ≤ C_threshold := by
    rfl
  have hC_eta' : 2 * C_threshold ≤ C_fluct := by
    simpa [C_threshold, delta] using hC_eta
  have hfluct :
      noDropWindow rho
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1)))
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) →
        T_weight *
            coarseFluctuationFullBlockSumAtScale hP hStruct hP4
              (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i) ≤
          C_fluct * (etaS + rho ^ 2) *
            contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) := by
    intro hno
    have hS_base :=
      hB_fluct hP hStruct hP4
        (N := N) (k := memoryGridScale Nstar L (i - 1))
        (m := memoryGridScale Nstar L i) (rho := rho)
        (T_m := T_weight) (delta := delta) (C_delta := C_threshold)
        hNk_plus hwindowLength hNstar hHM hdelta_pos hdelta_le_F
        (by dsimp [T_weight, F_i]) hC_threshold hrho_nonneg hno
    have hscalar :
        2 * C_threshold * etaS + 2 * Cw * rho ^ 2 ≤
          C_fluct * (etaS + rho ^ 2) := by
      have hρ2_nonneg : 0 ≤ rho ^ 2 := sq_nonneg rho
      have hleft : (2 * C_threshold) * etaS ≤ C_fluct * etaS :=
        mul_le_mul_of_nonneg_right hC_eta' (le_of_lt hηS)
      have hright : (2 * Cw) * rho ^ 2 ≤ C_fluct * rho ^ 2 :=
        mul_le_mul_of_nonneg_right (by simpa [Cw] using hC_rho) hρ2_nonneg
      calc
        2 * C_threshold * etaS + 2 * Cw * rho ^ 2 =
          (2 * C_threshold) * etaS + (2 * Cw) * rho ^ 2 := by ring
        _ ≤ C_fluct * etaS + C_fluct * rho ^ 2 :=
          add_le_add hleft hright
        _ = C_fluct * (etaS + rho ^ 2) := by ring
    exact hS_base.trans
      (mul_le_mul_of_nonneg_right hscalar (le_of_lt hF_pos))
  have hw_nonneg : ∀ x ∈ s, 0 ≤ w x := by
    intro x _hx
    exact section53CoarseFluctuationScaleWeight_nonneg hP4
      (memoryGridScale Nstar L i) x
  have htau_nonneg : ∀ x ∈ s, 0 ≤ tau x := by
    intro x hx
    have hxm : x ≤ memoryGridScale Nstar L i := (Finset.mem_Icc.mp hx).2
    simpa [tau] using tauAtScale_special_nonneg_of_P4 hP hStruct hP4 hxm e
  have hrt' : ∀ x ∈ s, r_m * tau x ≤ (1 / 2 : ℝ) * drop x := by
    intro x hx
    have hxm : x ≤ memoryGridScale Nstar L i := (Finset.mem_Icc.mp hx).2
    simpa [r_m, F_i, tau, drop] using
      sqrt_contrastExcess_mul_tauAtScale_special_le_half_contrastExcess_drop_of_P4
        hP hStruct hP4 hxm e he
  have hdrop' :
      noDropWindow rho
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1)))
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) →
        ∀ x ∈ s, drop x ≤
          rho * contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) := by
    intro hno x hx
    have hkx : memoryGridScale Nstar L (i - 1) ≤ x := by
      have hlow : memoryGridScale Nstar L (i - 1) + 1 ≤ x :=
        (Finset.mem_Icc.mp hx).1
      omega
    simpa [drop] using
      contrastExcess_drop_le_noDrop_of_P4 hP hStruct hP4 hno hkx
  have hCw : ∑ x ∈ s, w x ≤ Cw := by
    simpa [s, w, Cw] using
      section53CoarseFluctuationScaleWeight_sum_le_geometricConstant hP4
        (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i)
  have hbudget_sqrt' : C * C_sqrt * Real.sqrt delta⁻¹ ≤ C_delta := by
    simpa [delta] using hbudget_sqrt
  have hraw_pair_of_no :
      noDropWindow rho
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1)))
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) →
        Homogenization.Book.Ch05.expectedCenteredResponseJAtScale hP hStruct
            ((memoryGridScale Nstar L i : ℕ) : ℤ)
            (Homogenization.Book.Ch05.specialPAtScale hP hStruct
              ((memoryGridScale Nstar L i : ℕ) : ℤ) e)
            (Homogenization.Book.Ch05.specialQAtScale hP hStruct
              ((memoryGridScale Nstar L i : ℕ) : ℤ) e) ≤
          C * centeredResponseSqrtTermAtScale hP hStruct
              ((memoryGridScale Nstar L (i - 1) : ℕ) : ℤ)
              ((memoryGridScale Nstar L i : ℕ) : ℤ) e +
            C * eps *
              contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) +
              C * eps⁻¹ * weakNormGood ∧
        Homogenization.Book.Ch05.expectedCenteredResponseJStarAtScale hP hStruct
            ((memoryGridScale Nstar L i : ℕ) : ℤ)
            (Homogenization.Book.Ch05.specialPAtScale hP hStruct
              ((memoryGridScale Nstar L i : ℕ) : ℤ) e)
            (Homogenization.Book.Ch05.specialQAtScale hP hStruct
              ((memoryGridScale Nstar L i : ℕ) : ℤ) e) ≤
          C * centeredResponseStarSqrtTermAtScale hP hStruct
              ((memoryGridScale Nstar L (i - 1) : ℕ) : ℤ)
              ((memoryGridScale Nstar L i : ℕ) : ℤ) e +
            C * eps *
              contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) +
              C * eps⁻¹ * weakNormGood := by
    intro hno
    simpa [weakNormGood, F_i] using
      hraw_all hP hStruct hP4 hparams hc hP4_hc hm hP4_hm
        (N := N) (k := memoryGridScale Nstar L (i - 1))
        (m := memoryGridScale Nstar L i) hNk hkm_strict hHM M_sub hMsub
        hfin hstochRoot hpolyRoot e he
        (C := C) (C_norm := C_norm) (eps := eps)
        (T_edge := T_weight) (decay := decay)
        (lowerEdgeBudget := lowerEdgeBudget) (smallBudget := smallBudget)
        (lowBudget := lowBudget) (childTailBudget := childTailBudget)
        hC_pos hC_norm_pos heps_pos heps_le_one
        hT_weight_nonneg hdecay_nonneg hLowerBudget_nonneg hChildTail_nonneg
        (by simpa [P_km, T_weight, F_i] using hcanonicalLowerBudget hno)
        hfirst_le hcenter_le hS_coeff hTau_coeff hL_coeff
        hcutoff_geo hSmallBound hLowBound
        hChildTailBudget htailBudget
  have hraw :
      noDropWindow rho
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1)))
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) →
      let m : ℕ := memoryGridScale Nstar L i
      let k : ℕ := memoryGridScale Nstar L (i - 1)
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      Homogenization.Book.Ch05.expectedCenteredResponseJAtScale hP hStruct
          (m : ℤ)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) ≤
        C * centeredResponseSqrtTermAtScale hP hStruct (k : ℤ) (m : ℤ) e +
        C * eps * F_i + C * eps⁻¹ * weakNormGood := by
    intro hno
    simpa [F_i, weakNormGood] using (hraw_pair_of_no hno).1
  have hrawStar :
      noDropWindow rho
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1)))
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) →
      let m : ℕ := memoryGridScale Nstar L i
      let k : ℕ := memoryGridScale Nstar L (i - 1)
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      Homogenization.Book.Ch05.expectedCenteredResponseJStarAtScale hP hStruct
          (m : ℤ)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) ≤
        C * centeredResponseStarSqrtTermAtScale hP hStruct (k : ℤ) (m : ℤ) e +
        C * eps * F_i + C * eps⁻¹ * weakNormGoodStar := by
    intro hno
    simpa [F_i, weakNormGoodStar, weakNormGood] using (hraw_pair_of_no hno).2
  have hweak :
      let m : ℕ := memoryGridScale Nstar L i
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      weakNormGood ≤
        weakNormContribution (1 + F_i)
          (coarseFluctuationFullBlockSumAtScale hP hStruct hP4
            (memoryGridScale Nstar L (i - 1)) m)
          (P_km * (∑ x ∈ s, w x * tau x)) lowerEdge 0 := by
    dsimp [weakNormGood, specialWeakNormEnergyContributionWithLowerEdgeBudgetAtScale,
      P_km, lowerEdge, s, w, tau, weightedTauSumAtScales]
    rfl
  have hweakStar :
      let m : ℕ := memoryGridScale Nstar L i
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      weakNormGoodStar ≤
        weakNormContribution (1 + F_i)
          (coarseFluctuationFullBlockSumAtScale hP hStruct hP4
            (memoryGridScale Nstar L (i - 1)) m)
          (P_km * (∑ x ∈ s, w x * tau x)) lowerEdgeStar 0 := by
    dsimp [weakNormGoodStar, weakNormGood,
      specialWeakNormEnergyContributionWithLowerEdgeBudgetAtScale, P_km,
      lowerEdgeStar, s, w, tau, weightedTauSumAtScales]
    rfl
  have h_eps :
      let m : ℕ := memoryGridScale Nstar L i
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      C * eps * F_i ≤ C_delta * eps * F_i := by
    have hepsF_nonneg : 0 ≤ eps * F_i :=
      mul_nonneg (le_of_lt heps_pos) (le_of_lt hF_pos)
    calc
      C * eps * F_i = C * (eps * F_i) := by ring
      _ ≤ C_delta * (eps * F_i) :=
        mul_le_mul_of_nonneg_right hC_eps hepsF_nonneg
      _ = C_delta * eps * F_i := by ring
  have h_lower :
      noDropWindow rho
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1)))
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) →
      let m : ℕ := memoryGridScale Nstar L i
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      let Hprev : ℝ :=
        memory (memoryDecay hc L)
          (initialMemory hc.rhoM N Nstar
            (fun n => contrastExcessAtScale hP hStruct n))
          (memoryGridDrop
            (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
          (i - 1)
      C * eps⁻¹ * lowerEdge ≤
        C_delta * eps⁻¹ * decay * F_i +
          C_memory * eps⁻¹ * (Hprev ^ 2 / (1 + F_i)) +
          C_edgeMem * eps⁻¹ *
            ((Hprev /
                (1 +
                  contrastExcessAtScale hP hStruct
                    (memoryGridScale Nstar L (i - 1)))) *
              terminalPAtScales hP hStruct (memoryGridScale Nstar L (i - 1))
                (memoryGridScale Nstar L i)) := by
    intro hno
    simpa [lowerEdge, F_i] using hLowerMemoryBudget hno
  have h_lowerStar :
      noDropWindow rho
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1)))
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) →
      let m : ℕ := memoryGridScale Nstar L i
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      let Hprev : ℝ :=
        memory (memoryDecay hc L)
          (initialMemory hc.rhoM N Nstar
            (fun n => contrastExcessAtScale hP hStruct n))
          (memoryGridDrop
            (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
          (i - 1)
      C * eps⁻¹ * lowerEdgeStar ≤
        C_delta * eps⁻¹ * decay * F_i +
          C_memory * eps⁻¹ * (Hprev ^ 2 / (1 + F_i)) +
          C_edgeMem * eps⁻¹ *
            ((Hprev /
                (1 +
                  contrastExcessAtScale hP hStruct
                    (memoryGridScale Nstar L (i - 1)))) *
              terminalPAtScales hP hStruct (memoryGridScale Nstar L (i - 1))
                (memoryGridScale Nstar L i)) := by
    intro hno
    simpa [lowerEdgeStar, F_i] using hLowerMemoryBudget hno
  exact
    lyapunov_step_of_memoryGrid_noDropResponse_lower_memory_no_bad_packaged_fluctuation_tau_and_sqrt_linear
      (hc := hc) (s := s) (hP := hP) (hStruct := hStruct) (hP4 := hP4)
      (N := N) (Nstar := Nstar) (L := L) (i := i) (e := e)
      (A := A) (K := K) (lambda := lambda) (rho := rho) (C := C)
      (C_delta := C_delta) (C_memory := C_memory) (C_edgeMem := C_edgeMem)
      (C_S := C_S)
      (C_fluct := C_fluct) (C_sqrt := C_sqrt) (eps := eps)
      (edgeMemoryCoeff := edgeMemoryCoeff)
      (etaS := etaS) (etaSt := etaSt) (decay := decay)
      (weakNormGood := weakNormGood)
      (weakNormGoodStar := weakNormGoodStar)
      (lowerEdge := lowerEdge) (lowerEdgeStar := lowerEdgeStar)
      (T_weight := T_weight) (delta := delta) (r_m := r_m) (P_km := P_km)
      (Cw := Cw) (coeff := coeff) (memoryCoeff := memoryCoeff)
      (w := w) (tau := tau) (drop := drop)
      he hi hlambda_nonneg hA_nonneg hK_nonneg hedgeMemoryCoeff_nonneg
      hedgeMem_nonneg hKmem_le hdrop_coeff
      hdrop_memory_coeff hmemory_coeff hC_nonneg hC_sqrt_nonneg heps_pos
      hrho_nonneg hrho_pos hrho_le_one (le_of_lt hηS) (le_of_lt hηSt)
      hC_delta_nonneg hC_S hdelta_pos hdelta_le_F
      (by dsimp [T_weight, F_i]) hfluct hC_fluct_budget hP_le_of_noDrop
      hw_nonneg htau_nonneg hrt' hdrop' hCw (by simpa [Cw] using hbudget_tau)
      hC_response_le hbudget_sqrt' hraw hrawStar hweak hweakStar h_eps
      h_lower h_lowerStar hcoeff_bound hmemoryCoeff hedgeMemoryCoeff hsmall


/--
Source labels `l.S.and.J`, `e.raw.CR.energy`, `p.HC.CR`, `a.HM`, `M_m^st`,
`l.union.bound`, and `e.nodrop`: Layer C linear compact-source no-bad
lower-memory main bridge on the SHARP resized source track (src-free).  The
Section 5.2 small and low tails are discharged internally; the child-tail
source budget is `sourceMaxResizedBudgetOfGrid`, payable by the L-G
grid/channel payment plus the union-bound and envelope root feeders.
-/
theorem exists_rawEnergyConstants_bufferExponent_lyapunov_step_of_main_buffer_and_compact_source_lower_edge_linear_resized_scalars
    {d : ℕ} [NeZero d] {hc : HighContrastExponents d}
    (params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    (hm : HighCenteredMomentParameters d hc)
    (hhmP4 : hm.p4Params = params) (hcp : hc.params = params) :
    ∃ C_osc C_lin C_high : ℝ,
      0 ≤ C_osc ∧ 0 ≤ C_lin ∧ 0 ≤ C_high ∧
      ∀ (L : ℕ) {etaS etaSt delta_sc decay : ℝ},
      0 < etaS → 0 < etaSt → 0 < delta_sc → 0 < L → 0 < decay →
    ∃ B : ℝ,
      1 ≤ B ∧
        ∀ {P : Homogenization.Book.Ch04.CoeffLaw d}
          (hP : Homogenization.Book.Ch04.LawCarrier P)
          (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
          (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P),
          hP4.params = params →
          ∀ {N Nstar i : ℕ} (e : Homogenization.Vec d)
          {A K lambda rho C C_delta C_memory C_edgeMem C_S C_fluct C_sqrt C_norm
            eps coeff memoryCoeff edgeMemoryCoeff lowerEdgeBudget
            childTailBudget : ℝ},
            Homogenization.Book.Ch02.vecNorm e = 1 →
            1 ≤ i →
            (hNNstar : N ≤ Nstar) →
            ∀ (M_sub : ℕ → Homogenization.CoeffField d → ℝ),
            AEMeasurable (M_sub (memoryGridScale Nstar L i)) P →
            ∀ {stochRoot polyRoot : ℝ},
            ((∫⁻ ω, ‖terminalCoarseBlockStochasticMax hP hStruct hc N
                (memoryGridScale Nstar L i)
                (Homogenization.originCube d ((memoryGridScale Nstar L i : ℕ) : ℤ))
                (fun x : Homogenization.CoeffField d => x) ω‖ₑ ^ (2 : ℝ) ∂P) +
              (∫⁻ ω, ‖M_sub (memoryGridScale Nstar L i) ω‖ₑ ^ (2 : ℝ) ∂P) ≠ ⊤) →
            (2 * (((∫⁻ ω, ‖terminalCoarseBlockStochasticMax hP hStruct hc N
                  (memoryGridScale Nstar L i)
                  (Homogenization.originCube d ((memoryGridScale Nstar L i : ℕ) : ℤ))
                  (fun x : Homogenization.CoeffField d => x) ω‖ₑ ^ (2 : ℝ) ∂P) +
                (∫⁻ ω, ‖M_sub (memoryGridScale Nstar L i) ω‖ₑ ^ (2 : ℝ) ∂P)).toReal ^
                (1 / (hP4.xi : ℝ))) ≤ stochRoot) →
            ((ENNReal.ofReal
                (((2 +
                  Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
                  (hm.C_Q * (((memoryGridScale Nstar L i - N + 1 : ℕ) : ℝ) *
                    (3 : ℝ) ^
                      (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                        ((memoryGridScale Nstar L i - N : ℕ) : ℝ))))) ^
                (1 / hm.Q)).toReal ≤ polyRoot) →
            0 ≤ lambda →
            0 ≤ A →
            0 ≤ K →
            0 ≤ edgeMemoryCoeff →
            0 ≤ C_edgeMem →
            4 * memoryCoeff ≤ K ^ 2 →
            (1 + rho)⁻¹ + A * memoryDecay hc L ≤ lambda →
            memoryDecay hc L ≤ lambda →
            (K + 16 * edgeMemoryCoeff) +
                A * (memoryDecay hc L *
                      (1 + rho * (K + 16 * edgeMemoryCoeff))) ≤ lambda * A →
            0 < C →
            0 ≤ C_delta →
            0 ≤ C_sqrt →
            0 < C_norm →
            0 < eps →
            eps ≤ 1 →
            0 ≤ rho → 0 < rho → rho ≤ 1 →
            C ≤ C_delta →
            C_S ≤ C_delta →
            delta_sc ≤ contrastExcessAtScale hP hStruct
              (memoryGridScale Nstar L i) →
            2 * (1 + (delta_sc / 2)⁻¹) ^ 2 ≤ C_fluct →
            2 * section53CoarseFluctuationWeightSumConstant hP4 ≤ C_fluct →
            C * C_fluct ≤ C_S →
            C * (2 * section53CoarseFluctuationWeightSumConstant hP4) ≤
              C_delta →
            C * C_sqrt * Real.sqrt (delta_sc / 2)⁻¹ ≤ C_delta →
            (2 : ℝ) ≤ C_sqrt ^ 2 →
            0 ≤ lowerEdgeBudget →
            0 ≤ childTailBudget →
            (noDropWindow rho
                (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1)))
                (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) →
             let m : ℕ := memoryGridScale Nstar L i
             let k : ℕ := memoryGridScale Nstar L (i - 1)
             let T_edge : ℝ :=
              (1 + contrastExcessAtScale hP hStruct m) ^ 2 /
                contrastExcessAtScale hP hStruct m
             let P_km : ℝ := terminalPAtScales hP hStruct k m
             let canonicalLowerTailBudget : ℝ :=
              decay *
                (T_edge +
                  P_km *
                    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e)
             canonicalLowerTailBudget ≤ lowerEdgeBudget) →
            specialWeakNormEnergyFirstCoeffAtScale d
              (memoryGridScale Nstar L i) ≤ C →
            C_lin ≤ C →
            (let β := section53CoarseFluctuationBeta hP4
             let K :=
              Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst
                d
             C_lin * 16 * (C_high * β⁻¹) + C_lin * 16 * K ^ 2 ≤ C) →
            (let β := section53CoarseFluctuationBeta hP4
             let K :=
              Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst
                d
             C_lin * 16 * K ^ 2 * (5 * β⁻¹) ≤ C) →
            (let K :=
              Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst
                d
             C_norm + C_lin * 16 * K ^ 2 + C_lin * 16 * K ^ 2 ≤ C) →
            (let m : ℕ := memoryGridScale Nstar L i
             let k : ℕ := memoryGridScale Nstar L (i - 1)
             let T_edge : ℝ :=
              (1 + contrastExcessAtScale hP hStruct m) ^ 2 /
                contrastExcessAtScale hP hStruct m
             let β := section53CoarseFluctuationBeta hP4
             (C_osc * C_norm⁻¹) *
                ((β ^ 2)⁻¹ *
                  Real.rpow (3 : ℝ)
                    (-2 * β * (((m - k : ℕ) : ℝ))) *
                  contrastExcessAtScale hP hStruct m) ≤ decay * T_edge) →
            (let m : ℕ := memoryGridScale Nstar L i
             let k : ℕ := memoryGridScale Nstar L (i - 1)
             let smallBudget : ℝ :=
              section52SmallTailTerminalResponseBudgetAtScales hP hStruct hP4
                (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i) e
             let lowBudget : ℝ :=
              lowTailSharpBudgetAtScales hP hStruct hP4 hc N
                (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i)
                (hNNstar.trans (Nat.le_add_right Nstar (i * L))) e
                stochRoot polyRoot
             let sourceBudget : ℝ :=
              sourceMaxResizedBudgetOfGrid hP hStruct hP4 hc N Nstar L i
                hNNstar e stochRoot polyRoot
         let β := section53CoarseFluctuationBeta hP4
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
            (let m : ℕ := memoryGridScale Nstar L i
             let k : ℕ := memoryGridScale Nstar L (i - 1)
             let smallBudget : ℝ :=
              section52SmallTailTerminalResponseBudgetAtScales hP hStruct hP4
                (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i) e
             let lowBudget : ℝ :=
              lowTailSharpBudgetAtScales hP hStruct hP4 hc N
                (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i)
                (hNNstar.trans (Nat.le_add_right Nstar (i * L))) e
                stochRoot polyRoot
             let sourceBudget : ℝ :=
              sourceMaxResizedBudgetOfGrid hP hStruct hP4 hc N Nstar L i
                hNNstar e stochRoot polyRoot
         childTailBudget + smallBudget + lowBudget + sourceBudget ≤ lowerEdgeBudget) →
            (noDropWindow rho
                (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1)))
                (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) →
             let m : ℕ := memoryGridScale Nstar L i
             let F_i : ℝ := contrastExcessAtScale hP hStruct m
             let Hprev : ℝ :=
              memory (memoryDecay hc L)
                (initialMemory hc.rhoM N Nstar
                  (fun n => contrastExcessAtScale hP hStruct n))
                (memoryGridDrop
                  (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
                (i - 1)
             C * eps⁻¹ * lowerEdgeBudget ≤
              C_delta * eps⁻¹ * decay * F_i +
                C_memory * eps⁻¹ * (Hprev ^ 2 / (1 + F_i)) +
                C_edgeMem * eps⁻¹ *
                  ((Hprev /
                      (1 +
                        contrastExcessAtScale hP hStruct
                          (memoryGridScale Nstar L (i - 1)))) *
                    terminalPAtScales hP hStruct
                      (memoryGridScale Nstar L (i - 1))
                      (memoryGridScale Nstar L i))) →
            N + Nat.ceil
                (B * Real.logb 3
                  (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) ≤
              memoryGridScale Nstar L i →
            HighCenteredMomentEstimate hm P N
              (intermediateCoarseBlockDeviation hP hStruct
                (fun x : Homogenization.CoeffField d => x)) →
            C_delta *
              (Real.sqrt rho + eps + eps⁻¹ * (etaS + etaSt + rho + rho ^ 2) +
                eps⁻¹ * decay) ≤ coeff →
            C_memory * eps⁻¹ ≤ memoryCoeff →
            C_edgeMem * eps⁻¹ ≤ edgeMemoryCoeff →
            2 * coeff ≤ (1 / 2 : ℝ) →
            lyapunovValue A
                (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
                (memory (memoryDecay hc L)
                  (initialMemory hc.rhoM N Nstar
                    (fun n => contrastExcessAtScale hP hStruct n))
                  (memoryGridDrop
                    (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
                  i) ≤
              lambda *
                lyapunovValue A
                  (contrastExcessAtScale hP hStruct
                    (memoryGridScale Nstar L (i - 1)))
                  (memory (memoryDecay hc L)
                    (initialMemory hc.rhoM N Nstar
                      (fun n => contrastExcessAtScale hP hStruct n))
                    (memoryGridDrop
                      (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
                    (i - 1)) := by
  rcases
      exists_rawEnergyConstants_bufferExponent_lyapunov_step_of_main_buffer_and_lower_memory_no_bad_linear_resized_scalars
        params hm hhmP4 hcp with
    ⟨C_osc, C_lin, C_high, hC_osc_nonneg, hC_lin_nonneg,
      hC_high_nonneg, hlower_all⟩
  refine ⟨C_osc, C_lin, C_high, hC_osc_nonneg, hC_lin_nonneg,
    hC_high_nonneg, ?_⟩
  intro L etaS etaSt delta_sc decay hηS hηSt hdelta_sc_pos hL_pos hdecay_pos
  obtain ⟨B, hB_one, hmain⟩ :=
    hlower_all L hηS hηSt hdelta_sc_pos hL_pos hdecay_pos
  refine ⟨B, hB_one, ?_⟩
  intro P hP hStruct hP4 hparams N Nstar i e A K lambda rho C C_delta
    C_memory C_edgeMem C_S C_fluct C_sqrt C_norm eps coeff memoryCoeff
    edgeMemoryCoeff lowerEdgeBudget childTailBudget
    he hi hNNstar M_sub hMsub stochRoot polyRoot hfin hstochRoot hpolyRoot
    hlambda_nonneg hA_nonneg hK_nonneg hedgeMemoryCoeff_nonneg
    hedgeMem_nonneg hKmem_le
    hdrop_coeff hdrop_memory_coeff hmemory_coeff hC_pos hC_delta_nonneg
    hC_sqrt_nonneg hC_norm_pos heps_pos heps_le_one hrho_nonneg hrho_pos
    hrho_le_one hC_eps hC_S hdelta_sc_le_F hC_eta hC_rho
    hC_fluct_budget hbudget_tau hbudget_sqrt hC_response_le
    hLowerBudget_nonneg hChildTail_nonneg hcanonicalLowerBudget hfirst_le
    hcenter_le hS_coeff
    hTau_coeff hL_coeff hcutoff_geo hChildTailBudget htailBudget
    hLowerMemoryBudget hNstar hHM
    hcoeff_bound hmemoryCoeff hedgeMemoryCoeff hsmall
  have hP4_hm : hP4.params = hm.p4Params := hparams.trans hhmP4.symm
  have hP4_hc : hP4.params = hc.params := hparams.trans hcp.symm
  let smallBudget : ℝ :=
    section52SmallTailTerminalResponseBudgetAtScales hP hStruct hP4
      (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i) e
  let lowBudget : ℝ :=
    lowTailSharpBudgetAtScales hP hStruct hP4 hc N
      (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i)
      (hNNstar.trans (Nat.le_add_right Nstar (i * L))) e
      stochRoot polyRoot
  have hkm_strict :
      memoryGridScale Nstar L (i - 1) < memoryGridScale Nstar L i :=
    memoryGridScale_lt_of_pos_L hi hL_pos
  exact
    hmain hP hStruct hP4 hparams (N := N) (Nstar := Nstar) (i := i) e
      (A := A) (K := K) (lambda := lambda) (rho := rho) (C := C)
      (C_delta := C_delta) (C_memory := C_memory) (C_edgeMem := C_edgeMem)
      (C_S := C_S)
      (C_fluct := C_fluct) (C_sqrt := C_sqrt) (C_norm := C_norm)
      (eps := eps) (coeff := coeff) (memoryCoeff := memoryCoeff)
      (edgeMemoryCoeff := edgeMemoryCoeff)
      (lowerEdgeBudget := lowerEdgeBudget) (smallBudget := smallBudget)
      (lowBudget := lowBudget) (childTailBudget := childTailBudget)
      he hi hNNstar M_sub hMsub hfin hstochRoot hpolyRoot
      hlambda_nonneg hA_nonneg hK_nonneg hedgeMemoryCoeff_nonneg
      hedgeMem_nonneg hKmem_le
      hdrop_coeff hdrop_memory_coeff hmemory_coeff hC_pos hC_delta_nonneg
      hC_sqrt_nonneg hC_norm_pos heps_pos heps_le_one hrho_nonneg
      hrho_pos hrho_le_one hC_eps hC_S hdelta_sc_le_F hC_eta hC_rho
      hC_fluct_budget hbudget_tau hbudget_sqrt hC_response_le
      hLowerBudget_nonneg hChildTail_nonneg hcanonicalLowerBudget
      hfirst_le hcenter_le hS_coeff hTau_coeff hL_coeff hcutoff_geo
      (by
        simpa [smallBudget, section52SmallTailChildResponseIntegralAtScales,
          section52SmallTailTerminalResponseBudgetAtScales] using
          section52SmallTailChildResponseIntegral_le_terminalResponseBudgetAtScales
            hP hStruct.stationary hStruct hP4 hkm_strict e)
      (by
        have hNk_grid : N ≤ memoryGridScale Nstar L (i - 1) :=
          hNNstar.trans (Nat.le_add_right Nstar ((i - 1) * L))
        simpa [lowBudget] using
          integral_section52LowTail_childResponseAverage_special_le_lowTailSharpBudgetAtScales
            hP hStruct hP4 hc hP4_hc hm hP4_hm hNk_grid hkm_strict hHM M_sub hMsub
            hfin hstochRoot hpolyRoot e)
      hChildTailBudget htailBudget hLowerMemoryBudget hNstar hHM hcoeff_bound
      hmemoryCoeff hedgeMemoryCoeff hsmall
end Homogenization.HighContrast.EntryScale
