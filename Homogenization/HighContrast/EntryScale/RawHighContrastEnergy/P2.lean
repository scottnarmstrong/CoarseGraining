import Mathlib.Tactic.Linarith
import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations
import Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.CenteredResponses
import Homogenization.HighContrast.EntryScale.Inputs
import Homogenization.HighContrast.EntryScale.MaximalResponse
import Homogenization.HighContrast.EntryScale.ResponseFluctuation
import Homogenization.HighContrast.EntryScale.ResponseMoment
import Homogenization.HighContrast.EntryScale.RawHighContrastWeakNorm.P4
import Homogenization.HighContrast.EntryScale.RawHighContrastWeakNorm.P6
import Homogenization.HighContrast.EntryScale.RawHighContrastWeakNorm.P8
import Homogenization.HighContrast.EntryScale.LocalTailTransport
import Homogenization.HighContrast.EntryScale.RawHighContrastEnergy.P1

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization.Book.Ch05.Section54.OneStepContraction
open scoped Matrix.Norms.Elementwise

namespace Homogenization.HighContrast.EntryScale

noncomputable section

/--
Source labels `p.HC.CR`, `e.det.memory`, and `e.nodrop`: grid/channel payment
of the resized source-max budget on a no-drop memory grid step.  The sharp
`2 * sqrt(theta_m) * rM` normalization is paid by the paired terminal-response
budget `C_resp * (1 + F_i)`, the deterministic drift supremum is reconciled
with the memory endpoint estimate
`terminalAnnealedFullBlockDrift_weightedSup_le_memory_of_P4`, and the
remaining linear memory term is folded into the canonical lower-tail budget
plus the quadratic deterministic memory channel `Hprev^2 / (1 + F_i)`.
-/
theorem sourceMaxResizedBudgetOfGrid_le_canonicalLowerTailBudget_add_memory_of_grid_noDrop
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) (hcparams : hP4.params = hc.params) {N Nstar L i : ℕ}
    {rho stochRoot polyRoot etaSrc polyRootBound C_resp c_fold decay : ℝ}
    (hi : 1 ≤ i) (hNNstar : N ≤ Nstar) (e : Homogenization.Vec d)
    (hrho_nonneg : 0 ≤ rho)
    (hstochRoot_nonneg : 0 ≤ stochRoot)
    (hpolyRoot_nonneg : 0 ≤ polyRoot)
    (hstochRoot_le : stochRoot ≤ etaSrc)
    (hpolyRoot_le : polyRoot ≤ polyRootBound)
    (hC_resp_nonneg : 0 ≤ C_resp)
    (hc_fold_pos : 0 < c_fold)
    (hF_pos :
      0 < contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
    (hno :
      noDropWindow rho
        (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1)))
        (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)))
    (hresponse_pair :
      terminalPAtScales hP hStruct (memoryGridScale Nstar L (i - 1))
            (memoryGridScale Nstar L i) *
          coarseFluctuationResponseMomentAtScale hP hStruct hP4
            (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i) e +
        terminalPAtScales hP hStruct (memoryGridScale Nstar L (i - 1))
            (memoryGridScale Nstar L i) *
          coarseFluctuationResponseMomentStarAtScale hP hStruct hP4
            (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i) e ≤
      C_resp *
        (1 + contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)))
    (hdecay :
      sourceMaxSharpConst hP4 hc * C_resp *
          (etaSrc + polyRootBound + 2 * rho + c_fold) ≤ decay) :
    sourceMaxResizedBudgetOfGrid hP hStruct hP4 hc N Nstar L i hNNstar e
        stochRoot polyRoot ≤
      sourceMaxCanonicalLowerTailBudgetOfGrid hP hStruct hP4 Nstar L i e
          decay +
        sourceMaxSharpConst hP4 hc * C_resp / c_fold *
          sourceMaxMemoryTermOfGrid hP hStruct hc N Nstar L i := by
  classical
  have hNm : N ≤ memoryGridScale Nstar L i :=
    hNNstar.trans (Nat.le_add_right Nstar (i * L))
  have hkm :
      memoryGridScale Nstar L (i - 1) ≤ memoryGridScale Nstar L i :=
    memoryGridScale_le_of_le (Nat.sub_le i 1)
  have hden_pos :
      0 < 1 + contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) := by
    linarith
  have hsqrt :=
    sqrtTheta_mul_responseMoment_le_of_terminalP_pair
      hP hStruct hP4 hkm e hresponse_pair
  have hdrift_div :
      terminalBadMaximalDriftSup hP hStruct hc hNm ≤
        ((memoryDecay hc L)⁻¹ *
          memory (memoryDecay hc L)
            (initialMemory hc.rhoM N Nstar
              (fun n => contrastExcessAtScale hP hStruct n))
            (memoryGridDrop
              (fun n => contrastExcessAtScale hP hStruct n) Nstar L) i) /
          (1 + contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) := by
    dsimp [terminalBadMaximalDriftSup]
    exact
      terminalAnnealedFullBlockDrift_weightedSup_le_memory_of_P4
        hc hP hStruct hP4 hi hNNstar
  have hdrift_mul :
      terminalBadMaximalDriftSup hP hStruct hc hNm *
          (1 + contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) ≤
        (memoryDecay hc L)⁻¹ *
          memory (memoryDecay hc L)
            (initialMemory hc.rhoM N Nstar
              (fun n => contrastExcessAtScale hP hStruct n))
            (memoryGridDrop
              (fun n => contrastExcessAtScale hP hStruct n) Nstar L) i :=
    (le_div_iff₀ hden_pos).mp hdrift_div
  have hi_eq : i - 1 + 1 = i := by omega
  have hrec :
      (memoryDecay hc L)⁻¹ *
          memory (memoryDecay hc L)
            (initialMemory hc.rhoM N Nstar
              (fun n => contrastExcessAtScale hP hStruct n))
            (memoryGridDrop
              (fun n => contrastExcessAtScale hP hStruct n) Nstar L) i =
        memory (memoryDecay hc L)
            (initialMemory hc.rhoM N Nstar
              (fun n => contrastExcessAtScale hP hStruct n))
            (memoryGridDrop
              (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
            (i - 1) +
          memoryGridDrop
            (fun n => contrastExcessAtScale hP hStruct n) Nstar L i := by
    have h :=
      inv_mul_memory_succ (memoryDecay hc L)
        (initialMemory hc.rhoM N Nstar
          (fun n => contrastExcessAtScale hP hStruct n))
        (memoryGridDrop
          (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
        (i - 1) (ne_of_gt (memoryDecay_pos hc L))
    rw [hi_eq] at h
    exact h
  have hdelta_le :
      memoryGridDrop (fun n => contrastExcessAtScale hP hStruct n) Nstar L i ≤
        rho * contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) := by
    rw [memoryGridDrop_eq_contrast_sub
      (fun n => contrastExcessAtScale hP hStruct n) Nstar L i hi]
    simpa only [memoryGridContrast, noDropWindow] using hno
  have hP_km_rM_nonneg :
      0 ≤ terminalPAtScales hP hStruct (memoryGridScale Nstar L (i - 1))
            (memoryGridScale Nstar L i) *
          coarseFluctuationResponseMomentAtScale hP hStruct hP4
            (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i) e :=
    mul_nonneg
      (terminalPAtScales_nonneg_of_P4 hP hStruct hP4 hkm)
      (coarseFluctuationResponseMomentAtScale_nonneg hP hStruct hP4
        (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i) e)
  have hmain :=
    resizedSourceBudget_scalar_le_decay_mul_edge_add_memory
      (E := sourceMaxSharpConst hP4 hc) (C_resp := C_resp)
      (S := Real.sqrt
        (Homogenization.Book.Ch05.thetaAtScale hP hStruct
          ((memoryGridScale Nstar L i : ℕ) : ℤ)))
      (rM := coarseFluctuationResponseMomentAtScale hP hStruct hP4
        (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i) e)
      (D := terminalBadMaximalDriftSup hP hStruct hc hNm)
      (F := contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
      (Hprev := memory (memoryDecay hc L)
        (initialMemory hc.rhoM N Nstar
          (fun n => contrastExcessAtScale hP hStruct n))
        (memoryGridDrop
          (fun n => contrastExcessAtScale hP hStruct n) Nstar L) (i - 1))
      (q_invH := (memoryDecay hc L)⁻¹ *
        memory (memoryDecay hc L)
          (initialMemory hc.rhoM N Nstar
            (fun n => contrastExcessAtScale hP hStruct n))
          (memoryGridDrop
            (fun n => contrastExcessAtScale hP hStruct n) Nstar L) i)
      (Delta := memoryGridDrop
        (fun n => contrastExcessAtScale hP hStruct n) Nstar L i)
      (P_km := terminalPAtScales hP hStruct (memoryGridScale Nstar L (i - 1))
        (memoryGridScale Nstar L i))
      (sourceMaxSharpConst_nonneg hP4 hc hcparams) hC_resp_nonneg
      (terminalBadMaximalDriftSup_nonneg hP hStruct hc hNm) hF_pos
      hstochRoot_nonneg hpolyRoot_nonneg hstochRoot_le hpolyRoot_le
      hrho_nonneg hc_fold_pos hP_km_rM_nonneg hsqrt hdrift_mul hrec
      hdelta_le hdecay
  calc
    sourceMaxResizedBudgetOfGrid hP hStruct hP4 hc N Nstar L i hNNstar e
        stochRoot polyRoot =
        sourceMaxSharpConst hP4 hc *
            (2 * Real.sqrt
              (Homogenization.Book.Ch05.thetaAtScale hP hStruct
                ((memoryGridScale Nstar L i : ℕ) : ℤ))) *
            coarseFluctuationResponseMomentAtScale hP hStruct hP4
              (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i) e *
          (stochRoot + polyRoot +
            2 * terminalBadMaximalDriftSup hP hStruct hc hNm) := by
        dsimp [sourceMaxResizedBudgetOfGrid, sourceMaxResizedBudgetAtScales,
          sourceMaxSharpConst]
        ring
    _ ≤ decay *
          ((1 + contrastExcessAtScale hP hStruct
              (memoryGridScale Nstar L i)) ^ 2 /
              contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) +
            terminalPAtScales hP hStruct (memoryGridScale Nstar L (i - 1))
                (memoryGridScale Nstar L i) *
              coarseFluctuationResponseMomentAtScale hP hStruct hP4
                (memoryGridScale Nstar L (i - 1))
                (memoryGridScale Nstar L i) e) +
          sourceMaxSharpConst hP4 hc * C_resp / c_fold *
            (memory (memoryDecay hc L)
                (initialMemory hc.rhoM N Nstar
                  (fun n => contrastExcessAtScale hP hStruct n))
                (memoryGridDrop
                  (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
                (i - 1) ^ 2 /
              (1 + contrastExcessAtScale hP hStruct
                (memoryGridScale Nstar L i))) :=
        hmain
    _ = sourceMaxCanonicalLowerTailBudgetOfGrid hP hStruct hP4 Nstar L i e
          decay +
        sourceMaxSharpConst hP4 hc * C_resp / c_fold *
          sourceMaxMemoryTermOfGrid hP hStruct hc N Nstar L i := by
        dsimp [sourceMaxCanonicalLowerTailBudgetOfGrid,
          sourceMaxMemoryTermOfGrid]

/--
Pure component bookkeeping for the child-average route when both the terminal
lower-edge estimate and the child tail carry bad-maximal pieces.  The two bad
coefficients are combined first and only their sum is absorbed by the single
bad slot in `weakNormContribution`.
-/
theorem component_childTailBudget_le_const_mul_contribution_with_split_badCoeff_of_component_bounds
    {C C_norm C_lin highCoeff K2 tauCoeff terminalBadCoeff childBadCoeff
      badCoeff S Tau L B high localSlots childTail decayT : ℝ}
    (hC_norm_nonneg : 0 ≤ C_norm)
    (hC_lin_nonneg : 0 ≤ C_lin)
    (hS_nonneg : 0 ≤ S)
    (hTau_nonneg : 0 ≤ Tau)
    (hL_nonneg : 0 ≤ L)
    (hB_nonneg : 0 ≤ B)
    (hK2_nonneg : 0 ≤ K2)
    (hhigh : high ≤ highCoeff * S)
    (hlocal :
      localSlots ≤ S + tauCoeff * Tau + L + terminalBadCoeff * B)
    (hchild : childTail ≤ L + childBadCoeff * B)
    (hdecay : decayT ≤ L)
    (hS_coeff : C_lin * 16 * highCoeff + C_lin * 16 * K2 ≤ C)
    (hTau_coeff : C_lin * 16 * K2 * tauCoeff ≤ C)
    (hL_coeff : C_norm + C_lin * 16 * K2 + C_lin * 16 * K2 ≤ C)
    (hBad_coeff : C_lin * 16 * K2 * badCoeff ≤ C)
    (hbadCoeff_sum : terminalBadCoeff + childBadCoeff ≤ badCoeff) :
    C_norm * decayT +
        C_lin * (16 * (high + K2 * localSlots + K2 * childTail))
      ≤ C * (S + Tau + L + B) := by
  have hsixteen_nonneg : 0 ≤ (16 : ℝ) := by norm_num
  have hfactor_nonneg : 0 ≤ C_lin * 16 :=
    mul_nonneg hC_lin_nonneg hsixteen_nonneg
  have hfactorK_nonneg : 0 ≤ C_lin * 16 * K2 :=
    mul_nonneg hfactor_nonneg hK2_nonneg
  have hhigh_scaled :
      C_lin * 16 * high ≤ C_lin * 16 * (highCoeff * S) :=
    mul_le_mul_of_nonneg_left hhigh hfactor_nonneg
  have hlocal_scaled :
      (C_lin * 16 * K2) * localSlots ≤
        (C_lin * 16 * K2) *
          (S + tauCoeff * Tau + L + terminalBadCoeff * B) :=
    mul_le_mul_of_nonneg_left hlocal hfactorK_nonneg
  have hchild_scaled :
      (C_lin * 16 * K2) * childTail ≤
        (C_lin * 16 * K2) * (L + childBadCoeff * B) :=
    mul_le_mul_of_nonneg_left hchild hfactorK_nonneg
  have hdecay_scaled :
      C_norm * decayT ≤ C_norm * L :=
    mul_le_mul_of_nonneg_left hdecay hC_norm_nonneg
  have hS_scaled :
      (C_lin * 16 * highCoeff + C_lin * 16 * K2) * S ≤ C * S :=
    mul_le_mul_of_nonneg_right hS_coeff hS_nonneg
  have hTau_scaled :
      (C_lin * 16 * K2 * tauCoeff) * Tau ≤ C * Tau :=
    mul_le_mul_of_nonneg_right hTau_coeff hTau_nonneg
  have hL_scaled :
      (C_norm + C_lin * 16 * K2 + C_lin * 16 * K2) * L ≤ C * L :=
    mul_le_mul_of_nonneg_right hL_coeff hL_nonneg
  have hBad_coeff_sum :
      C_lin * 16 * K2 * (terminalBadCoeff + childBadCoeff) ≤ C := by
    calc
      C_lin * 16 * K2 * (terminalBadCoeff + childBadCoeff)
          = (C_lin * 16 * K2) * (terminalBadCoeff + childBadCoeff) := by
            ring
      _ ≤ (C_lin * 16 * K2) * badCoeff :=
            mul_le_mul_of_nonneg_left hbadCoeff_sum hfactorK_nonneg
      _ = C_lin * 16 * K2 * badCoeff := by ring
      _ ≤ C := hBad_coeff
  have hB_scaled :
      (C_lin * 16 * K2 * (terminalBadCoeff + childBadCoeff)) * B ≤ C * B :=
    mul_le_mul_of_nonneg_right hBad_coeff_sum hB_nonneg
  calc
    C_norm * decayT +
        C_lin * (16 * (high + K2 * localSlots + K2 * childTail))
        =
      C_norm * decayT + C_lin * 16 * high +
        (C_lin * 16 * K2) * localSlots +
          (C_lin * 16 * K2) * childTail := by
        ring
    _ ≤
      C_norm * L + C_lin * 16 * (highCoeff * S) +
        (C_lin * 16 * K2) *
            (S + tauCoeff * Tau + L + terminalBadCoeff * B) +
          (C_lin * 16 * K2) * (L + childBadCoeff * B) := by
        linarith
    _ =
      (C_lin * 16 * highCoeff + C_lin * 16 * K2) * S +
        (C_lin * 16 * K2 * tauCoeff) * Tau +
          (C_norm + C_lin * 16 * K2 + C_lin * 16 * K2) * L +
            (C_lin * 16 * K2 * (terminalBadCoeff + childBadCoeff)) * B := by
        ring
    _ ≤ C * S + C * Tau + C * L + C * B := by
        linarith
    _ = C * (S + Tau + L + B) := by ring

/--
Source labels `e.W.first.sum`, `e.M.def`, and `e.raw.CR.energy`: component
compression for the Section 5.2 child-average route with an explicit terminal
lower-edge budget.  This is the component bridge needed by the source-max
full-buffer route: both the terminal positive-excess edge and the child-tail
budget are paid by the same caller-supplied `lowerEdgeBudget`, so no local
window response-tail coefficient is exposed.
-/
theorem specialWeakNormEnergy_componentBudget_childTail_le_weakNormContribution_with_terminalLowerEdgeBudget_atScales
    {d : ℕ} [NeZero d] :
    ∃ C_high : ℝ, 0 ≤ C_high ∧
    ∀ {P : Homogenization.Book.Ch04.CoeffLaw d}
      (hP : Homogenization.Book.Ch04.LawCarrier P)
      (_hstat : Homogenization.Book.Ch04.StationaryLaw P)
      (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
      (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
      {k m : ℕ}, k < m → ∀ e : Homogenization.Vec d,
      Homogenization.Book.Ch02.vecNorm e = 1 →
      ∀ {C C_norm C_lin T_edge decay lowerEdgeBudget childTail : ℝ},
      0 ≤ C_norm → 0 ≤ C_lin → 0 ≤ T_edge → 0 ≤ decay →
      0 ≤ lowerEdgeBudget →
      (let P_km := terminalPAtScales hP hStruct k m
       let canonicalLowerTailBudget : ℝ :=
        decay *
          (T_edge +
            P_km * coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e)
       canonicalLowerTailBudget ≤ lowerEdgeBudget) →
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
      (let β := section53CoarseFluctuationBeta hP4
       let s' := hP4.sLower + β
       let t' := hP4.sUpper + β
       let Q : Homogenization.TriadicCube d :=
        Homogenization.originCube d (m : ℤ)
       let p_e :=
        Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
       let q_e :=
        Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
       let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
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
       let terminalLowerEdge : ℝ :=
        ∫ a, (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) *
          defectSum a ^ 2 ∂P
       terminalLowerEdge ≤ lowerEdgeBudget) →
      childTail ≤ lowerEdgeBudget →
      let β := section53CoarseFluctuationBeta hP4
      let s := hP4.sLower + 2 * β
      let s' := hP4.sLower + β
      let t := hP4.sUpper + 2 * β
      let t' := hP4.sUpper + β
      let Q : Homogenization.TriadicCube d :=
        Homogenization.originCube d (m : ℤ)
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
      let defectSum := fun a : Homogenization.CoeffField d =>
        ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
          Real.rpow (3 : ℝ)
              (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
            Real.sqrt
              (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
                (m : ℤ) n p_e q_e a)
      let lowerEdge : ℝ :=
        ∫ a, (σ * lowerExcess a + σ⁻¹ * upperExcess a) *
          defectSum a ^ 2 ∂P
      let localSlots : ℝ :=
        (1 + contrastExcessAtScale hP hStruct m) *
            coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m +
          (5 * localWeakNormScalarWeightAtScales hP hStruct k m * β⁻¹) *
            weightedTauSumAtScales hP hStruct hP4 k m e +
          lowerEdge +
          (1 + contrastExcessAtScale hP hStruct m) * 0
      C_norm * decay * T_edge +
          C_lin *
            (16 *
              (highScaleAverage + K ^ 2 * localSlots +
                K ^ 2 * childTail))
        ≤
          C *
            specialWeakNormEnergyContributionWithLowerEdgeBudgetAtScale
              hP hStruct hP4 k m e lowerEdgeBudget := by
  classical
  rcases
      integral_paired_highScaleAverageTerms_special_le_beta_inv_contrastExcess_fullBlockSumAtScale
        (d := d) with ⟨C_high, hC_high_nonneg, hhigh_all⟩
  refine ⟨C_high, hC_high_nonneg, ?_⟩
  intro P hP _hstat hStruct hP4 k m hkm e he C C_norm C_lin T_edge decay
    lowerEdgeBudget childTail hC_norm_nonneg hC_lin_nonneg hT_edge_nonneg
    hdecay_nonneg hLowerBudget_nonneg hcanonicalBudget hS_coeff hTau_coeff
    hL_coeff hTerminalEdge_bound hChildTail_bound
  dsimp only at hcanonicalBudget hS_coeff hTau_coeff hL_coeff hTerminalEdge_bound
  dsimp only at hChildTail_bound ⊢
  have he_sq : Homogenization.vecNormSq e = 1 :=
    Homogenization.Book.Ch05.Section54.GoodScale.vecNormSq_eq_one_of_vecNorm_eq_one
      he
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
  let lowerLocal := fun a : Homogenization.CoeffField d =>
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹)
      0
  let upperLocal := fun a : Homogenization.CoeffField d =>
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
    ∫ a, (σ * lowerLocal a + σ⁻¹ * upperLocal a) * defectSum a ^ 2 ∂P
  let terminalLowerEdge : ℝ :=
    ∫ a, (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) *
      defectSum a ^ 2 ∂P
  let S_slot :=
    (1 + contrastExcessAtScale hP hStruct m) *
      coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m
  let tauSum : ℝ := weightedTauSumAtScales hP hStruct hP4 k m e
  let P_km : ℝ := terminalPAtScales hP hStruct k m
  let Tau_slot : ℝ := P_km * tauSum
  let localSlots : ℝ :=
    S_slot +
      (5 * localWeakNormScalarWeightAtScales hP hStruct k m * β⁻¹) * tauSum +
      lowerEdge + (1 + contrastExcessAtScale hP hStruct m) * 0
  let canonicalLowerTailBudget : ℝ :=
    decay *
      (T_edge +
        P_km * coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e)
  have hTerminalEdge_int :
      MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d =>
          (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) *
            defectSum a ^ 2) P := by
    simpa only [β, s', t', Q, p_e, q_e, σ, lowerTerminal, upperTerminal, defectSum]
      using
        integrable_terminalPositiveExcess_defectSum_sq_special_of_P4
          hP hStruct.stationary hStruct hP4 hkm e
  have hhigh :
      highScaleAverage ≤ (C_high * β⁻¹) * S_slot := by
    simpa only [β, s, t, p_e, q_e, p0_e, q0_e, σ, highScaleAverage, S_slot,
      mul_assoc] using
      hhigh_all hP hStruct.stationary hStruct hP4 hkm e he_sq
  have hlower_to_terminal : lowerEdge ≤ terminalLowerEdge := by
    simpa only [β, s', t', Q, p_e, q_e, σ, lowerLocal, upperLocal,
      lowerTerminal, upperTerminal, defectSum, lowerEdge, terminalLowerEdge] using
      integral_localPositiveExcess_defectSum_sq_special_le_terminalPositiveExcess
        hP hStruct hP4 hkm.le e hTerminalEdge_int
  have hterminal_budget :
      terminalLowerEdge ≤ lowerEdgeBudget := by
    simpa only [β, s', t', Q, p_e, q_e, σ, lowerTerminal, upperTerminal,
      defectSum, terminalLowerEdge] using hTerminalEdge_bound
  have hlocalWeight :
      localWeakNormScalarWeightAtScales hP hStruct k m = P_km := by
    simpa only [P_km] using
      localWeakNormScalarWeightAtScales_eq_terminalPAtScales_of_P4
        hP hStruct hP4 k m
  have hlocal :
      localSlots ≤ S_slot + (5 * β⁻¹) * Tau_slot + lowerEdgeBudget := by
    have hlower_budget : lowerEdge ≤ lowerEdgeBudget :=
      hlower_to_terminal.trans hterminal_budget
    dsimp [localSlots, Tau_slot]
    rw [hlocalWeight]
    ring_nf
    linarith
  have hF_nonneg : 0 ≤ contrastExcessAtScale hP hStruct m :=
    contrastExcessAtScale_nonneg_of_P4 hP hStruct hP4 m
  have hS_base_nonneg :
      0 ≤ coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m :=
    coarseFluctuationFullBlockSumAtScale_nonneg hP hStruct hP4 k m
  have hS_nonneg : 0 ≤ S_slot := by
    dsimp [S_slot]
    exact mul_nonneg (by linarith) hS_base_nonneg
  have hP_nonneg : 0 ≤ P_km := by
    dsimp [P_km]
    exact terminalPAtScales_nonneg_of_P4 hP hStruct hP4 hkm.le
  have htau_nonneg : 0 ≤ tauSum := by
    dsimp [tauSum, weightedTauSumAtScales]
    refine Finset.sum_nonneg ?_
    intro j hj
    have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
    exact mul_nonneg
      (section53CoarseFluctuationScaleWeight_nonneg hP4 m j)
      (by
        simpa only [one_div, sub_nonneg, Homogenization.Book.Ch05.specialPAtScale_eq, Homogenization.Book.Ch05.sigmaHatAtScale_eq, Real.rpow_eq_pow, Homogenization.Book.Ch05.specialQAtScale_eq, Homogenization.Book.Ch05.tauAtScale_eq] using
          tauAtScale_special_nonneg_of_P4_rawHighContrastEnergy hP hStruct hP4 hjm e)
  have hTau_nonneg : 0 ≤ Tau_slot := by
    dsimp [Tau_slot]
    exact mul_nonneg hP_nonneg htau_nonneg
  have hresponse_nonneg :
      0 ≤ coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e :=
    coarseFluctuationResponseMomentAtScale_nonneg hP hStruct hP4 k m e
  have hP_response_nonneg :
      0 ≤ P_km * coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e :=
    mul_nonneg hP_nonneg hresponse_nonneg
  have hcanonical_le : canonicalLowerTailBudget ≤ lowerEdgeBudget := by
    simpa only [canonicalLowerTailBudget, P_km] using hcanonicalBudget
  have hdecay_to_canonical :
      decay * T_edge ≤ canonicalLowerTailBudget := by
    dsimp [canonicalLowerTailBudget]
    exact mul_le_mul_of_nonneg_left (by linarith) hdecay_nonneg
  have hdecay_to_lower : decay * T_edge ≤ lowerEdgeBudget :=
    hdecay_to_canonical.trans hcanonical_le
  have hβ_pos : 0 < β := by
    simpa only [β] using
      Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta_pos
        hP4
  have hβ_inv_nonneg : 0 ≤ β⁻¹ := inv_nonneg.mpr hβ_pos.le
  have hS_lhs_nonneg :
      0 ≤ C_lin * 16 * (C_high * β⁻¹) + C_lin * 16 * K ^ 2 := by
    have hfactor_nonneg : 0 ≤ C_lin * 16 :=
      mul_nonneg hC_lin_nonneg (by norm_num)
    exact add_nonneg
      (mul_nonneg hfactor_nonneg (mul_nonneg hC_high_nonneg hβ_inv_nonneg))
      (mul_nonneg hfactor_nonneg (sq_nonneg K))
  have hC_nonneg : 0 ≤ C := hS_lhs_nonneg.trans hS_coeff
  have hcomponent :=
    component_childTailBudget_le_const_mul_contribution_with_split_badCoeff_of_component_bounds
      (C := C) (C_norm := C_norm) (C_lin := C_lin)
      (highCoeff := C_high * β⁻¹) (K2 := K ^ 2)
      (tauCoeff := 5 * β⁻¹) (terminalBadCoeff := 0)
      (childBadCoeff := 0) (badCoeff := 0) (S := S_slot)
      (Tau := Tau_slot) (L := lowerEdgeBudget) (B := 0)
      (high := highScaleAverage) (localSlots := localSlots)
      (childTail := childTail) (decayT := decay * T_edge)
      hC_norm_nonneg hC_lin_nonneg hS_nonneg hTau_nonneg
      hLowerBudget_nonneg (by norm_num) (sq_nonneg K) hhigh
      (by simpa only [zero_mul, add_zero] using hlocal)
      (by simpa only [zero_mul, add_zero] using hChildTail_bound)
      hdecay_to_lower
      (by simpa only [β, K] using hS_coeff)
      (by simpa only [β, K] using hTau_coeff)
      (by simpa only [K] using hL_coeff)
      (by simpa only [mul_zero] using hC_nonneg)
      (by norm_num)
  change
    C_norm * decay * T_edge +
        C_lin *
          (16 *
            (highScaleAverage + K ^ 2 * localSlots + K ^ 2 * childTail))
      ≤
        C *
          weakNormContribution (1 + contrastExcessAtScale hP hStruct m)
            (coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m)
            (P_km * tauSum) lowerEdgeBudget 0
  simpa [S_slot, Tau_slot, weakNormContribution, add_assoc, add_comm,
    add_left_comm, mul_assoc, mul_left_comm, mul_comm] using hcomponent

/--
Source labels `l.Jtilde.energy.bound`, `p.HC.CR`, `e.W.first.sum`,
`e.W.low.tail`, `e.J.moment.bound`, `a.HM`, `M_m^st`, `l.union.bound`, and
`e.raw.CR.energy`: source-max raw response estimate with an explicit
lower-edge budget and a child-tail budget, on the SHARP resized source track.
The source budget in the child-tail hypotheses is
`sourceMaxResizedBudgetAtScales` (summed-weight first-power split with the
`2 * sqrt(theta_m)` normalizer and free stochastic/polynomial roots); the
actual source content is discharged internally from the capped/bad-event
first-power pairings, so no Holder package and no uniform source axiom is consumed.
-/
theorem rawHighContrastResponseEnergy_atScales_of_P4_with_weakNormContribution_lowerEdgeBudget_sourceMax_resized_childTailBudget_terms
    {d : ℕ} [NeZero d]
    (params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C_osc C_lin C_high : ℝ,
      0 ≤ C_osc ∧ 0 ≤ C_lin ∧ 0 ≤ C_high ∧
      ∀ {P : Homogenization.Book.Ch04.CoeffLaw d}
        (hP : Homogenization.Book.Ch04.LawCarrier P)
        (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P),
        hP4.params = params →
        (hc : HighContrastExponents d) →
        (hcparams : hP4.params = hc.params) →
        (hm : HighCenteredMomentParameters d hc) →
        (hparams : hP4.params = hm.p4Params) →
        ∀ {N k m : ℕ}, (hNk : N ≤ k) → (hkm : k < m) →
        (hHM :
          HighCenteredMomentEstimate hm P N
            (intermediateCoarseBlockDeviation hP hStruct
              (fun x : Homogenization.CoeffField d => x))) →
        ∀ (M_sub : ℕ → Homogenization.CoeffField d → ℝ),
        AEMeasurable (M_sub m) P →
        ∀ {stochRoot polyRoot : ℝ},
        ((∫⁻ ω, ‖terminalCoarseBlockStochasticMax hP hStruct hc N m
            (Homogenization.originCube d (m : ℤ))
            (fun x : Homogenization.CoeffField d => x) ω‖ₑ ^ (2 : ℝ) ∂P) +
          (∫⁻ ω, ‖M_sub m ω‖ₑ ^ (2 : ℝ) ∂P) ≠ ⊤) →
        (2 * (((∫⁻ ω, ‖terminalCoarseBlockStochasticMax hP hStruct hc N m
              (Homogenization.originCube d (m : ℤ))
              (fun x : Homogenization.CoeffField d => x) ω‖ₑ ^ (2 : ℝ) ∂P) +
            (∫⁻ ω, ‖M_sub m ω‖ₑ ^ (2 : ℝ) ∂P)).toReal ^ (1 / (hP4.xi : ℝ))) ≤
          stochRoot) →
        ((ENNReal.ofReal
            (((2 +
              Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
              (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
                (3 : ℝ) ^
                  (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                    ((m - N : ℕ) : ℝ))))) ^ (1 / hm.Q)).toReal ≤ polyRoot) →
        ∀ e : Homogenization.Vec d,
        Homogenization.Book.Ch02.vecNorm e = 1 →
        ∀ {C C_norm eps T_edge decay lowerEdgeBudget
            smallBudget lowBudget childTailBudget : ℝ},
        0 < C → 0 < C_norm → 0 < eps → eps ≤ 1 →
        0 ≤ T_edge → 0 ≤ decay → 0 ≤ lowerEdgeBudget →
        0 ≤ childTailBudget →
        (let P_km := terminalPAtScales hP hStruct k m
         let canonicalLowerTailBudget : ℝ :=
          decay *
            (T_edge +
              P_km * coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e)
         canonicalLowerTailBudget ≤ lowerEdgeBudget) →
        specialWeakNormEnergyFirstCoeffAtScale d m ≤ C →
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
              (by simpa only [Q, Homogenization.originCube] using
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
              (by simpa only [Q, Homogenization.originCube] using
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
        (let sourceBudget : ℝ :=
          sourceMaxResizedBudgetAtScales hP hStruct hP4 hc N k m
            (hNk.trans hkm.le) e stochRoot polyRoot
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
        (let sourceBudget : ℝ :=
          sourceMaxResizedBudgetAtScales hP hStruct hP4 hc N k m
            (hNk.trans hkm.le) e stochRoot polyRoot
         childTailBudget + smallBudget + lowBudget + sourceBudget ≤ lowerEdgeBudget) →
        let weakNorm :=
          specialWeakNormEnergyContributionWithLowerEdgeBudgetAtScale hP
            hStruct hP4 k m e lowerEdgeBudget
        Homogenization.Book.Ch05.expectedCenteredResponseJAtScale hP hStruct
            (m : ℤ)
            (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
            (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) ≤
          C * centeredResponseSqrtTermAtScale hP hStruct (k : ℤ) (m : ℤ) e +
            C * eps * contrastExcessAtScale hP hStruct m +
              C * eps⁻¹ * weakNorm ∧
        Homogenization.Book.Ch05.expectedCenteredResponseJStarAtScale hP hStruct
            (m : ℤ)
            (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
            (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) ≤
          C * centeredResponseStarSqrtTermAtScale hP hStruct (k : ℤ) (m : ℤ) e +
            C * eps * contrastExcessAtScale hP hStruct m +
              C * eps⁻¹ * weakNorm := by
  classical
  rcases
      specialWeakNormEnergyRemainderAtScale_le_centering_add_components_with_sourceMax_minBad_childResponse_lowerTailBudget
        (d := d) with
    ⟨C_osc, C_lin, hC_osc_nonneg, hC_lin_nonneg, hremainder_all⟩
  rcases
      specialWeakNormEnergy_componentBudget_childTail_le_weakNormContribution_with_terminalLowerEdgeBudget_atScales
        (d := d) with
    ⟨C_high, hC_high_nonneg, hcomponent_all⟩
  refine
    ⟨C_osc, C_lin, C_high, hC_osc_nonneg, hC_lin_nonneg,
      hC_high_nonneg, ?_⟩
  intro P hP hStruct hP4 _hP4params hc hcparams hm hparams N k m hNk hkm hHM M_sub hMsub
    stochRoot polyRoot hfin hstochRoot hpolyRoot e he
    C C_norm eps T_edge decay lowerEdgeBudget smallBudget lowBudget
    childTailBudget hC_pos hC_norm_pos heps_pos heps_le hT_edge_nonneg
    hdecay_nonneg hLowerBudget_nonneg hChildTail_nonneg hcanonicalBudget
    hfirst_le hcenter_le hS_coeff hTau_coeff hL_coeff hcutoff_geo
    hSmallBound hLowBound hChildTailBudget htailBudget
  dsimp only at hcanonicalBudget hS_coeff hTau_coeff hL_coeff hcutoff_geo
  dsimp only at hSmallBound hLowBound hChildTailBudget htailBudget ⊢
  have he_sq : Homogenization.vecNormSq e = 1 :=
    Homogenization.Book.Ch05.Section54.GoodScale.vecNormSq_eq_one_of_vecNorm_eq_one
      he
  let weakNorm :=
    specialWeakNormEnergyContributionWithLowerEdgeBudgetAtScale hP hStruct hP4
      k m e lowerEdgeBudget
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
  let localSlotsLinear : ℝ :=
    (1 + contrastExcessAtScale hP hStruct m) *
        coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m +
      (5 * localWeakNormScalarWeightAtScales hP hStruct k m * β⁻¹) *
        weightedTauSumAtScales hP hStruct hP4 k m e +
      (1 + contrastExcessAtScale hP hStruct m) * 0
  let localSlotsComponent : ℝ :=
    (1 + contrastExcessAtScale hP hStruct m) *
        coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m +
      (5 * localWeakNormScalarWeightAtScales hP hStruct k m * β⁻¹) *
        weightedTauSumAtScales hP hStruct hP4 k m e +
      lowerEdge +
      (1 + contrastExcessAtScale hP hStruct m) * 0
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
  let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
  let lowerSlot : Homogenization.CoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa only [Q, Homogenization.originCube] using
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
        (by simpa only [Q, Homogenization.originCube] using
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
  let responseMoment : ℝ :=
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  let edgeLossBudget : ℝ :=
    Homogenization.geometricDiscount s' 1 /
        Homogenization.geometricDiscount (s' - hc.rhoM) 1 +
      Homogenization.geometricDiscount t' 1 /
        Homogenization.geometricDiscount (t' - hc.rhoM) 1
  let weightLossSup : {n : ℤ // n ∈ S} → ℝ := fun n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa only [Q, Homogenization.originCube] using
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
  let sourceBudget : ℝ :=
    sourceMaxResizedBudgetAtScales hP hStruct hP4 hc N k m
      (hNk.trans hkm.le) e stochRoot polyRoot
  let sourceMinTerm : ℝ :=
    edgeWeightLoss *
        (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
      (∫ a, min (sourceMax a) 1 * response a ∂P)
  let sourceBadTerm : ℝ :=
    edgeWeightLoss *
        (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
      (∫ a, badEventTruncation sourceMax a * response a ∂P)
  have hchild_nonneg_pb : ∀ a, 0 ≤ childAvg a := by
    intro a
    dsimp [childAvg]
    exact Homogenization.descendantsAverage_nonneg Q (m - k)
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
      (fun R _hR =>
        Homogenization.Book.Ch04.responseJObservableCubeSet_nonneg R p_e q_e a)
  have hsrc_nonneg_pb : ∀ a, 0 ≤ sourceMax a :=
    terminalSpectralPositivePartSourceMax_nonneg hP hStruct hc k m Q
      (fun x : Homogenization.CoeffField d => x)
  have hMinChildInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d =>
          min (sourceMax a) 1 * childAvg a) P := by
    simpa only [β, Q, p_e, q_e, childAvg, sourceMax] using
      integrable_min_terminalSourceMax_one_mul_childResponseAverage_special
        hP hStruct.stationary hStruct hP4 hc hkm e
  have hBadChildPair :=
    integral_badEventTruncation_terminalSourceMax_mul_childResponseAverage_le_responseMoment_mul_global_polynomialRoot_add_drift_of_start_le
      hP hStruct.stationary hStruct hP4 hc hm hparams hNk hkm hHM e
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
  have hdrift_nonneg_pb : 0 ≤ terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le) :=
    terminalBadMaximalDriftSup_nonneg hP hStruct hc (hNk.trans hkm.le)
  have hRM_nonneg_pb : 0 ≤ responseMoment := by
    simpa only [responseMoment] using
      coarseFluctuationResponseMomentAtScale_nonneg hP hStruct hP4 k m e
  have hstochRoot_nonneg : 0 ≤ stochRoot := by
    refine le_trans ?_ hstochRoot
    positivity
  have hpolyRoot_nonneg : 0 ≤ polyRoot :=
    le_trans ENNReal.toReal_nonneg hpolyRoot
  have hMinChild :
      ∫ a, min (sourceMax a) 1 * childAvg a ∂P ≤
        (stochRoot + min (terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) 1) * responseMoment := by
    simpa only [Q, p_e, q_e, childAvg, sourceMax, responseMoment] using
      integral_min_terminalSourceMax_one_mul_childResponseAverage_le_stochasticRoot_add_min_drift_one_mul_responseMoment
        hP hStruct.stationary hStruct hP4 hc hNk hkm M_sub hMsub e hfin hstochRoot
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
    simpa only [Q, p_e, q_e, childAvg, sourceMax, responseMoment] using hBadChildPair.2
  have hBadChild :
      ∫ a, badEventTruncation sourceMax a * childAvg a ∂P ≤
        responseMoment * (polyRoot + terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) := by
    refine hBadChildRaw.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hRM_nonneg_pb
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
  have hLowerGapPB : 0 < hP4.sLower + section53CoarseFluctuationBeta hP4 - hc.rhoM :=
    sub_pos.mpr (hc.sourceMaxLowerGap_of_params hP4 hcparams)
  have hUpperGapPB : 0 < hP4.sUpper + section53CoarseFluctuationBeta hP4 - hc.rhoM :=
    sub_pos.mpr (hc.sourceMaxUpperGap_of_params hP4 hcparams)
  have hedgePB : edgeWeightLoss ≤ edgeLossBudget := by
    have hraw :=
      section52LargeScale_terminalPositiveExcess_edgeWeightLoss_le_discountRatio_of_P4_beta
        (d := d) (P := P) hP4 hc (N := k) (m := m)
        (by simpa only [β, s'] using hLowerGapPB)
        (by simpa only [β, t'] using hUpperGapPB)
    simpa only [β, s', t', S, Q, weightLossSup, edgeWeightLoss, edgeLossBudget] using hraw
  have hEWL_nonneg : 0 ≤ edgeWeightLoss := by
    simpa only [β, s', t', S, Q, weightLossSup, edgeWeightLoss] using
      section52LargeScale_terminalPositiveExcess_edgeWeightLoss_nonneg_of_P4_beta
        (d := d) (P := P) hP4 hc (N := k) (m := m)
  have hImin_nonneg : 0 ≤ ∫ a, min (sourceMax a) 1 * childAvg a ∂P :=
    MeasureTheory.integral_nonneg fun a =>
      mul_nonneg (le_min (hsrc_nonneg_pb a) zero_le_one) (hchild_nonneg_pb a)
  have hIbad_nonneg : 0 ≤ ∫ a, badEventTruncation sourceMax a * childAvg a ∂P :=
    MeasureTheory.integral_nonneg fun a =>
      mul_nonneg (badEventTruncation_nonneg (hsrc_nonneg_pb a)) (hchild_nonneg_pb a)
  have hsqrtθ_nonneg :
      0 ≤ 2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) := by
    positivity
  have hr_sq_nonneg : 0 ≤ (5 * β⁻¹) ^ 2 := sq_nonneg _
  have hIsum :
      (∫ a, min (sourceMax a) 1 * childAvg a ∂P) +
          (∫ a, badEventTruncation sourceMax a * childAvg a ∂P) ≤
        responseMoment *
          (stochRoot + polyRoot + 2 * terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) := by
    have hmin_le : min (terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) 1 ≤ terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le) := min_le_left _ _
    have hsum0 := add_le_add hMinChild hBadChild
    have hstep :
        (stochRoot + min (terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) 1) *
            responseMoment +
          responseMoment *
            (polyRoot + terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) ≤
        responseMoment *
          (stochRoot + polyRoot +
            2 * terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) := by
      have h1 :
          (stochRoot + min (terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) 1) *
              responseMoment +
            responseMoment *
              (polyRoot + terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) =
          responseMoment *
            (stochRoot + polyRoot +
              terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le) +
              min (terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) 1) := by
        ring
      rw [h1]
      refine mul_le_mul_of_nonneg_left ?_ hRM_nonneg_pb
      linarith
    exact hsum0.trans hstep
  have hSourceBudget : sourceMinTerm + sourceBadTerm ≤ sourceBudget := by
    have hbracket_nonneg :
        0 ≤ stochRoot + polyRoot + 2 * terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le) := by
      linarith
    have hX_nonneg :
        0 ≤ (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
          ((5 * β⁻¹) ^ 2 *
            (responseMoment *
              (stochRoot + polyRoot + 2 * terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)))) :=
      mul_nonneg hsqrtθ_nonneg
        (mul_nonneg hr_sq_nonneg (mul_nonneg hRM_nonneg_pb hbracket_nonneg))
    calc
      sourceMinTerm + sourceBadTerm =
          edgeWeightLoss *
              (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
            ((5 * β⁻¹) ^ 2 *
              ((∫ a, min (sourceMax a) 1 * childAvg a ∂P) +
                (∫ a, badEventTruncation sourceMax a * childAvg a ∂P))) := by
          dsimp [sourceMinTerm, sourceBadTerm]
          rw [hMinRespEq, hBadRespEq]
          ring
      _ ≤ edgeWeightLoss *
              (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
            ((5 * β⁻¹) ^ 2 *
              (responseMoment *
                (stochRoot + polyRoot + 2 * terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)))) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg hEWL_nonneg hsqrtθ_nonneg)
          exact mul_le_mul_of_nonneg_left hIsum hr_sq_nonneg
      _ = edgeWeightLoss *
            ((2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
              ((5 * β⁻¹) ^ 2 *
                (responseMoment *
                  (stochRoot + polyRoot + 2 * terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le))))) := by
          ring
      _ ≤ edgeLossBudget *
            ((2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
              ((5 * β⁻¹) ^ 2 *
                (responseMoment *
                  (stochRoot + polyRoot + 2 * terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le))))) :=
          mul_le_mul_of_nonneg_right hedgePB hX_nonneg
      _ = sourceBudget := by
          dsimp [sourceBudget, sourceMaxResizedBudgetAtScales, edgeLossBudget,
            responseMoment, β, s', t']
          ring
  have hSmallInt_term :
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
          (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a) P := by
    simpa only [Homogenization.Book.Ch05.sigmaHatAtScale_eq, Homogenization.Book.Ch05.specialPAtScale_eq, one_div, Real.rpow_eq_pow, Homogenization.Book.Ch05.specialQAtScale_eq, Homogenization.Book.Ch04.responseJObservableCubeSet_apply] using
      (integrable_section52SmallTail_childResponseAverage_special_and_integral_le_responseMoment
        hP hStruct.stationary hStruct hP4 hkm e).1
  have hLowInt_term :
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
            (by simpa only [Q, Homogenization.originCube] using
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
            (by simpa only [Q, Homogenization.originCube] using
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
      MeasureTheory.Integrable lowSum P := by
    simpa only [Homogenization.Book.Ch05.sigmaHatAtScale_eq, Homogenization.Book.Ch05.specialPAtScale_eq, one_div, Real.rpow_eq_pow, Homogenization.Book.Ch05.specialQAtScale_eq, Homogenization.Book.Ch04.responseJObservableCubeSet_apply] using
      (integrable_section52LowTail_childResponseAverage_special_and_integral_le_responseMoment
        hP hStruct.stationary hStruct hP4 hkm e).1
  have htailBudget_terminal :
      smallBudget + lowBudget + sourceBudget ≤ lowerEdgeBudget := by
    linarith
  have hTerminalEdge_bound :
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
      let terminalLowerEdge : ℝ :=
        ∫ a, (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) *
          defectSum a ^ 2 ∂P
      terminalLowerEdge ≤ lowerEdgeBudget := by
    simpa only [sourceBudget] using
      integral_terminalPositiveExcess_defectSum_sq_le_lowerTailBudget_of_sourceMax_min_one_add_badEventTruncation_childResponseAverage
        (P := P) hP hStruct.stationary hStruct hP4 hc
        (k := k) (m := m) hkm e
        (smallBudget := smallBudget) (lowBudget := lowBudget)
        (sourceMinBudget := sourceMinTerm) (sourceBadBudget := sourceBadTerm)
        (lowerTailBudget := lowerEdgeBudget)
        hSmallInt_term hLowInt_term hMinRespInt hBadRespInt
        hSmallBound hLowBound le_rfl le_rfl
        (by
          have hglue :
              smallBudget + lowBudget + sourceMinTerm + sourceBadTerm ≤
                lowerEdgeBudget := by
            have hsb := hSourceBudget
            have htb := htailBudget_terminal
            linarith
          exact hglue)
  have hcomponent_explicit :
      C_norm * decay * T_edge +
          C_lin *
            (16 *
              (highScaleAverage + K ^ 2 * localSlotsComponent +
                K ^ 2 * lowerEdgeBudget)) ≤
        C * weakNorm := by
    simpa only [weakNorm, β, s, s', t, t', Q, p_e, q_e, p0_e, q0_e, σ, K,
      highScaleAverage, lowerExcess, upperExcess, defectSum, lowerEdge,
      localSlotsComponent] using
      hcomponent_all hP hStruct.stationary hStruct hP4 hkm e he
        (C := C) (C_norm := C_norm) (C_lin := C_lin)
        (T_edge := T_edge) (decay := decay)
        (lowerEdgeBudget := lowerEdgeBudget) (childTail := lowerEdgeBudget)
        hC_norm_pos.le hC_lin_nonneg hT_edge_nonneg hdecay_nonneg
        hLowerBudget_nonneg hcanonicalBudget hS_coeff hTau_coeff hL_coeff
        hTerminalEdge_bound le_rfl
  have hσ_nonneg : 0 ≤ σ := by
    exact
      (Homogenization.Book.Ch05.Section54.GoodScale.sigmaHatAtScale_pos_of_P4
        hP hStruct hP4 m).le
  have hlowerEdge_nonneg : 0 ≤ lowerEdge := by
    dsimp [lowerEdge]
    refine MeasureTheory.integral_nonneg fun a => ?_
    exact mul_nonneg
      (add_nonneg
        (mul_nonneg hσ_nonneg (le_max_right _ _))
        (mul_nonneg (inv_nonneg.mpr hσ_nonneg) (le_max_right _ _)))
      (sq_nonneg _)
  have hslots_le :
      highScaleAverage + K ^ 2 * localSlotsLinear + K ^ 2 * lowerEdgeBudget ≤
        highScaleAverage + K ^ 2 * localSlotsComponent + K ^ 2 * lowerEdgeBudget := by
    have hlocal_le : localSlotsLinear ≤ localSlotsComponent := by
      dsimp [localSlotsLinear, localSlotsComponent]
      linarith
    have hmul :
        K ^ 2 * localSlotsLinear ≤ K ^ 2 * localSlotsComponent :=
      mul_le_mul_of_nonneg_left hlocal_le (sq_nonneg K)
    linarith
  have hcomponent_for_remainder :
      C_norm * decay * T_edge +
          C_lin *
            (16 *
              (highScaleAverage + K ^ 2 * localSlotsLinear +
                K ^ 2 * lowerEdgeBudget)) ≤
        C * weakNorm := by
    have hscaled_slots :
        C_lin *
            (16 *
              (highScaleAverage + K ^ 2 * localSlotsLinear +
                K ^ 2 * lowerEdgeBudget)) ≤
          C_lin *
            (16 *
              (highScaleAverage + K ^ 2 * localSlotsComponent +
                K ^ 2 * lowerEdgeBudget)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hslots_le (by norm_num : 0 ≤ (16 : ℝ)))
        hC_lin_nonneg
    exact (add_le_add le_rfl hscaled_slots).trans hcomponent_explicit
  have hremainder_components :
      specialWeakNormEnergyRemainderAtScale hP hStruct hP4 k m e ≤
        C_lin * eps * contrastExcessAtScale hP hStruct m +
          C_norm * eps⁻¹ * decay * T_edge +
            C_lin * eps⁻¹ *
              (16 *
                (highScaleAverage + K ^ 2 * localSlotsLinear +
                  K ^ 2 * lowerEdgeBudget)) := by
    simpa only [β, s, t, Q, p_e, q_e, p0_e, q0_e, σ, K, highScaleAverage,
      localSlotsLinear, sourceBudget] using
      hremainder_all hP hStruct.stationary hStruct hP4 hc hm hparams hNk hkm hHM e
        he_sq heps_pos heps_le hC_norm_pos
        (T_edge := T_edge) (decay := decay)
        (lowerTailBudget := lowerEdgeBudget) (smallBudget := smallBudget)
        (lowBudget := lowBudget) (sourceBudget := sourceBudget)
        (childTailBudget := childTailBudget) hcutoff_geo
        hSmallInt_term hLowInt_term hSmallBound hLowBound
        (by
          simpa only [sourceMinTerm, sourceBadTerm, sourceBudget, edgeWeightLoss,
            weightLossSup, sourceMax, childAvg, response, β, s', t', S, Q,
            p_e, q_e] using hSourceBudget)
        (by
          simpa only [sourceBudget] using hChildTailBudget)
        (by
          simpa only [sourceBudget] using htailBudget)
  have hF_nonneg : 0 ≤ contrastExcessAtScale hP hStruct m :=
    contrastExcessAtScale_nonneg_of_P4 hP hStruct hP4 m
  have hcenter_scaled :
      C_lin * eps * contrastExcessAtScale hP hStruct m ≤
        C * eps * contrastExcessAtScale hP hStruct m := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcenter_le heps_pos.le) hF_nonneg
  have hcomponent_scaled :
      C_norm * eps⁻¹ * decay * T_edge +
          C_lin * eps⁻¹ *
            (16 *
              (highScaleAverage + K ^ 2 * localSlotsLinear +
                K ^ 2 * lowerEdgeBudget)) ≤
        C * eps⁻¹ * weakNorm := by
    have hscaled :
        eps⁻¹ *
            (C_norm * decay * T_edge +
              C_lin *
                (16 *
                  (highScaleAverage + K ^ 2 * localSlotsLinear +
                    K ^ 2 * lowerEdgeBudget))) ≤
          eps⁻¹ * (C * weakNorm) :=
      mul_le_mul_of_nonneg_left hcomponent_for_remainder
        (inv_nonneg.mpr heps_pos.le)
    calc
      C_norm * eps⁻¹ * decay * T_edge +
          C_lin * eps⁻¹ *
            (16 *
              (highScaleAverage + K ^ 2 * localSlotsLinear +
                K ^ 2 * lowerEdgeBudget))
          =
            eps⁻¹ *
              (C_norm * decay * T_edge +
                C_lin *
                  (16 *
                    (highScaleAverage + K ^ 2 * localSlotsLinear +
                      K ^ 2 * lowerEdgeBudget))) := by
            ring
      _ ≤ eps⁻¹ * (C * weakNorm) := hscaled
      _ = C * eps⁻¹ * weakNorm := by ring
  have hremainder :
      specialWeakNormEnergyRemainderAtScale hP hStruct hP4 k m e ≤
        C * eps * contrastExcessAtScale hP hStruct m +
          C * eps⁻¹ * weakNorm := by
    calc
      specialWeakNormEnergyRemainderAtScale hP hStruct hP4 k m e
          ≤
            C_lin * eps * contrastExcessAtScale hP hStruct m +
              (C_norm * eps⁻¹ * decay * T_edge +
                C_lin * eps⁻¹ *
                  (16 *
                    (highScaleAverage + K ^ 2 * localSlotsLinear +
                      K ^ 2 * lowerEdgeBudget))) := by
              simpa only [add_assoc] using hremainder_components
      _ ≤
            C * eps * contrastExcessAtScale hP hStruct m +
              C * eps⁻¹ * weakNorm := by
              exact add_le_add hcenter_scaled hcomponent_scaled
  have hGradSq :=
    integrable_specialGradientWeakNormSquare_atScales_of_P4
      hP hStruct hP4 hkm e he
  have hFluxSq :=
    integrable_specialFluxWeakNormSquare_atScales_of_P4
      hP hStruct hP4 hkm e he
  exact
    ⟨expectedCenteredResponseJAtScale_le_rawEnergyRHS_of_remainder_bound_atScales_of_P4
        hP hStruct.stationary hStruct hP4 hkm e hfirst_le hremainder
        hGradSq hFluxSq,
      expectedCenteredResponseJStarAtScale_le_rawEnergyRHS_of_remainder_bound_atScales_of_P4
        hP hStruct.stationary hStruct hP4 hkm e hfirst_le hremainder
        hGradSq hFluxSq⟩

end

end Homogenization.HighContrast.EntryScale
