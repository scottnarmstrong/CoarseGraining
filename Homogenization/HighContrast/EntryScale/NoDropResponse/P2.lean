import Mathlib.Tactic.Linarith
import Homogenization.HighContrast.EntryScale.MaximalResponse
import Homogenization.HighContrast.EntryScale.Memory
import Homogenization.HighContrast.EntryScale.ResponseFluctuation
import Homogenization.HighContrast.EntryScale.ResponseMoment
import Homogenization.HighContrast.EntryScale.NoDropResponse.P1

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open scoped Matrix.Norms.Elementwise

namespace Homogenization.HighContrast.EntryScale

/-- **Layer B linear channel: packaged no-bad memory-grid response with the
edge-memory residual slot.**

Linear analog of
`expectedCenteredResponsesAtMemoryGrid_le_noDropResponseRHS_of_split_raw_highContrast_lower_memory_no_bad_with_packaged_fluctuation_tau_and_sqrt`:
`h_lower`/`h_lowerStar` carry the additional `H`-linear edge-memory residual
`C_edgeMem·eps⁻¹·linTerm`, and the produced value is `noDropResponseRHSLinear`. -/
theorem expectedCenteredResponsesAtMemoryGrid_le_noDropResponseRHSLinear_of_split_raw_highContrast_lower_memory_no_bad_with_packaged_fluctuation_tau_and_sqrt_linear
    {ι : Type*} (s : Finset ι)
    {d : ℕ} [NeZero d] (hc : HighContrastExponents d)
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {N Nstar L i : ℕ} (e : Homogenization.Vec d)
    {rho C C_delta C_memory C_edgeMem C_S C_fluct C_sqrt eps etaS etaSt decay
      weakNormGood weakNormGoodStar lowerEdge lowerEdgeStar T_weight delta
      r_m P_km Cw linTerm : ℝ}
    {w tau drop : ι → ℝ}
    (hC_nonneg : 0 ≤ C)
    (hC_sqrt_nonneg : 0 ≤ C_sqrt)
    (heps_pos : 0 < eps)
    (hrho_nonneg : 0 ≤ rho)
    (hetaS_nonneg : 0 ≤ etaS)
    (hetaSt_nonneg : 0 ≤ etaSt)
    (hlin_nonneg : 0 ≤ linTerm)
    (hedgeMem_nonneg : 0 ≤ C_edgeMem)
    (hC_delta_nonneg : 0 ≤ C_delta)
    (hC_S : C_S ≤ C_delta)
    (hdelta_pos : 0 < delta)
    (hdelta_le_F :
      delta ≤ contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
    (hT_weight :
      T_weight =
        (1 + contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) ^ 2 /
          contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
    (hfluct :
      T_weight *
          coarseFluctuationFullBlockSumAtScale hP hStruct hP4
            (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i) ≤
        C_fluct * (etaS + rho ^ 2) *
          contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
    (hC_fluct_budget : C * C_fluct ≤ C_S)
    (hP_le : P_km ≤ 4 * r_m)
    (hw_nonneg : ∀ x ∈ s, 0 ≤ w x)
    (htau_nonneg : ∀ x ∈ s, 0 ≤ tau x)
    (hrt : ∀ x ∈ s, r_m * tau x ≤ (1 / 2 : ℝ) * drop x)
    (hdrop :
      ∀ x ∈ s, drop x ≤
        rho * contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
    (hCw : ∑ x ∈ s, w x ≤ Cw)
    (hbudget_tau : C * (2 * Cw) ≤ C_delta)
    (hsqrt_prod :
      let m : ℕ := memoryGridScale Nstar L i
      let k : ℕ := memoryGridScale Nstar L (i - 1)
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      Homogenization.Book.Ch05.tauAtScale P (m : ℤ) (k : ℤ)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) *
        Homogenization.Book.Ch04.expectedResponseJCubeSet P
          (Homogenization.originCube d (k : ℤ))
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) ≤
        (C_sqrt * Real.sqrt rho * Real.sqrt delta⁻¹ * F_i) ^ 2)
    (hbudget_sqrt : C * C_sqrt * Real.sqrt delta⁻¹ ≤ C_delta)
    (hraw :
      let m : ℕ := memoryGridScale Nstar L i
      let k : ℕ := memoryGridScale Nstar L (i - 1)
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      Homogenization.Book.Ch05.expectedCenteredResponseJAtScale hP hStruct
          (m : ℤ)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) ≤
        C * centeredResponseSqrtTermAtScale hP hStruct (k : ℤ) (m : ℤ) e +
        C * eps * F_i + C * eps⁻¹ * weakNormGood)
    (hrawStar :
      let m : ℕ := memoryGridScale Nstar L i
      let k : ℕ := memoryGridScale Nstar L (i - 1)
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      Homogenization.Book.Ch05.expectedCenteredResponseJStarAtScale hP hStruct
          (m : ℤ)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) ≤
        C * centeredResponseStarSqrtTermAtScale hP hStruct (k : ℤ) (m : ℤ) e +
        C * eps * F_i + C * eps⁻¹ * weakNormGoodStar)
    (hweak :
      let m : ℕ := memoryGridScale Nstar L i
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      weakNormGood ≤
        weakNormContribution (1 + F_i)
          (coarseFluctuationFullBlockSumAtScale hP hStruct hP4
            (memoryGridScale Nstar L (i - 1)) m)
          (P_km * (∑ x ∈ s, w x * tau x)) lowerEdge 0)
    (hweakStar :
      let m : ℕ := memoryGridScale Nstar L i
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      weakNormGoodStar ≤
        weakNormContribution (1 + F_i)
          (coarseFluctuationFullBlockSumAtScale hP hStruct hP4
            (memoryGridScale Nstar L (i - 1)) m)
          (P_km * (∑ x ∈ s, w x * tau x)) lowerEdgeStar 0)
    (h_eps :
      let m : ℕ := memoryGridScale Nstar L i
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      C * eps * F_i ≤ C_delta * eps * F_i)
    (h_lower :
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
          C_edgeMem * eps⁻¹ * linTerm)
    (h_lowerStar :
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
          C_edgeMem * eps⁻¹ * linTerm) :
    let m : ℕ := memoryGridScale Nstar L i
    let F_i : ℝ := contrastExcessAtScale hP hStruct m
    let Hprev : ℝ :=
      memory (memoryDecay hc L)
        (initialMemory hc.rhoM N Nstar
          (fun n => contrastExcessAtScale hP hStruct n))
        (memoryGridDrop
          (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
        (i - 1)
    let rhs : ℝ :=
      noDropResponseRHSLinear C_delta C_memory C_edgeMem eps (Real.sqrt rho) rho
        etaS etaSt (rho ^ 2) decay F_i (Hprev ^ 2 / (1 + F_i)) linTerm
    Homogenization.Book.Ch05.expectedCenteredResponseJAtScale hP hStruct
        (m : ℤ)
        (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
        (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) ≤
      rhs ∧
    Homogenization.Book.Ch05.expectedCenteredResponseJStarAtScale hP hStruct
        (m : ℤ)
        (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
        (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) ≤
      rhs := by
  dsimp only
  have hF_nonneg :
      0 ≤ contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) :=
    contrastExcessAtScale_nonneg_of_P4 hP hStruct hP4
      (memoryGridScale Nstar L i)
  have hF_pos :
      0 < contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) :=
    hdelta_pos.trans_le hdelta_le_F
  have hterminal :
      C * eps⁻¹ * T_weight *
          coarseFluctuationFullBlockSumAtScale hP hStruct hP4
            (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i) ≤
        C_S * eps⁻¹ * etaS *
            contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) +
          C_S * eps⁻¹ * rho ^ 2 *
            contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) :=
    terminalFluctuation_prefactor_le_eta_add_rhoSq_budget
      (C := C) (C_budget := C_S) (C_S := C_fluct) (eps := eps)
      (T_m := T_weight)
      (S_term :=
        coarseFluctuationFullBlockSumAtScale hP hStruct hP4
          (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i))
      (etaS := etaS) (rhoSq := rho ^ 2)
      (F_i := contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
      (inv_nonneg.mpr (le_of_lt heps_pos)) hC_nonneg hetaS_nonneg
      (sq_nonneg rho) (le_of_lt hF_pos) hfluct hC_fluct_budget
  have htheta_le :
      1 + contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) ≤
        T_weight :=
    one_add_contrast_le_terminal_weight hF_pos hT_weight
  have hsum_nonneg :
      0 ≤ coarseFluctuationFullBlockSumAtScale hP hStruct hP4
        (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i) :=
    coarseFluctuationFullBlockSumAtScale_nonneg hP hStruct hP4
      (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i)
  have hweighted :
      (1 + contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) *
          coarseFluctuationFullBlockSumAtScale hP hStruct hP4
            (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i) ≤
        T_weight *
          coarseFluctuationFullBlockSumAtScale hP hStruct hP4
            (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i) :=
    mul_le_mul_of_nonneg_right htheta_le hsum_nonneg
  have hfactor_nonneg : 0 ≤ C * eps⁻¹ :=
    mul_nonneg hC_nonneg (inv_nonneg.mpr (le_of_lt heps_pos))
  have hsource_le :
      C * eps⁻¹ *
          (1 + contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) *
          coarseFluctuationFullBlockSumAtScale hP hStruct hP4
            (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i) ≤
        C * eps⁻¹ * T_weight *
          coarseFluctuationFullBlockSumAtScale hP hStruct hP4
            (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i) := by
    calc
      C * eps⁻¹ *
          (1 + contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) *
          coarseFluctuationFullBlockSumAtScale hP hStruct hP4
            (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i)
          =
        (C * eps⁻¹) *
          ((1 + contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) *
            coarseFluctuationFullBlockSumAtScale hP hStruct hP4
              (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i)) := by
          ring
      _ ≤
        (C * eps⁻¹) *
          (T_weight *
            coarseFluctuationFullBlockSumAtScale hP hStruct hP4
              (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i)) :=
          mul_le_mul_of_nonneg_left hweighted hfactor_nonneg
      _ =
        C * eps⁻¹ * T_weight *
          coarseFluctuationFullBlockSumAtScale hP hStruct hP4
            (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i) := by
          ring
  have h_S :
      C * eps⁻¹ *
          (1 + contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) *
          coarseFluctuationFullBlockSumAtScale hP hStruct hP4
            (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i) ≤
        C_S * eps⁻¹ * etaS *
            contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) +
          C_S * eps⁻¹ * rho ^ 2 *
            contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) :=
    hsource_le.trans hterminal
  have hscale_le :
      memoryGridScale Nstar L (i - 1) ≤ memoryGridScale Nstar L i :=
    memoryGridScale_le_of_le (Nat.sub_le i 1)
  have htau_mk_nonneg :
      0 ≤
        Homogenization.Book.Ch05.tauAtScale P
          ((memoryGridScale Nstar L i : ℕ) : ℤ)
          ((memoryGridScale Nstar L (i - 1) : ℕ) : ℤ)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct
            ((memoryGridScale Nstar L i : ℕ) : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct
            ((memoryGridScale Nstar L i : ℕ) : ℤ) e) :=
    tauAtScale_special_nonneg_of_P4 hP hStruct hP4 hscale_le e
  have hresponse_nonneg :
      0 ≤
        Homogenization.Book.Ch04.expectedResponseJCubeSet P
          (Homogenization.originCube d
            ((memoryGridScale Nstar L (i - 1) : ℕ) : ℤ))
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct
            ((memoryGridScale Nstar L i : ℕ) : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct
            ((memoryGridScale Nstar L i : ℕ) : ℤ) e) :=
    expectedResponseJCubeSet_nonneg
      (Homogenization.originCube d
        ((memoryGridScale Nstar L (i - 1) : ℕ) : ℤ))
      (Homogenization.Book.Ch05.specialPAtScale hP hStruct
        ((memoryGridScale Nstar L i : ℕ) : ℤ) e)
      (Homogenization.Book.Ch05.specialQAtScale hP hStruct
        ((memoryGridScale Nstar L i : ℕ) : ℤ) e)
  have h_sqrt :
      C *
          centeredResponseSqrtTermAtScale hP hStruct
            ((memoryGridScale Nstar L (i - 1) : ℕ) : ℤ)
            ((memoryGridScale Nstar L i : ℕ) : ℤ) e ≤
        C_delta * Real.sqrt rho *
          contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) :=
    centeredResponseSqrtTermAtScale_prefactor_le_noDrop_rhoSqrt_budget
      hP hStruct ((memoryGridScale Nstar L (i - 1) : ℕ) : ℤ)
      ((memoryGridScale Nstar L i : ℕ) : ℤ) e
      (C := C) (C_delta := C_delta) (C_sqrt := C_sqrt)
      (rho := rho) (delta := delta)
      (F_i := contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
      hC_nonneg hC_sqrt_nonneg hdelta_pos hF_nonneg htau_mk_nonneg
      hresponse_nonneg hsqrt_prod hbudget_sqrt
  have h_sqrtStar :
      C *
          centeredResponseStarSqrtTermAtScale hP hStruct
            ((memoryGridScale Nstar L (i - 1) : ℕ) : ℤ)
            ((memoryGridScale Nstar L i : ℕ) : ℤ) e ≤
        C_delta * Real.sqrt rho *
          contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) :=
    centeredResponseStarSqrtTermAtScale_prefactor_le_noDrop_rhoSqrt_budget
      hP hStruct ((memoryGridScale Nstar L (i - 1) : ℕ) : ℤ)
      ((memoryGridScale Nstar L i : ℕ) : ℤ) e
      (C := C) (C_delta := C_delta) (C_sqrt := C_sqrt)
      (rho := rho) (delta := delta)
      (F_i := contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
      hC_nonneg hC_sqrt_nonneg hdelta_pos hF_nonneg htau_mk_nonneg
      hresponse_nonneg hsqrt_prod hbudget_sqrt
  have hrhoF_nonneg :
      0 ≤ rho *
        contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) :=
    mul_nonneg hrho_nonneg hF_nonneg
  have h_tau :
      C * eps⁻¹ * (P_km * (∑ x ∈ s, w x * tau x)) ≤
        C_delta * eps⁻¹ * rho *
          contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) :=
    weightedTauSum_prefactor_le_noDrop_rho_budget
      s (C := C) (C_delta := C_delta) (eps := eps) (r_m := r_m)
      (P_km := P_km) (rho := rho)
      (F_i := contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
      (Cw := Cw)
      heps_pos hC_nonneg hP_le hw_nonneg htau_nonneg hrt hdrop hCw
      hrhoF_nonneg hbudget_tau
  exact
    expectedCenteredResponsesAtMemoryGrid_le_noDropResponseRHSLinear_of_split_raw_highContrast_lower_memory_no_bad_linear
      (hc := hc) hP hStruct hP4 (N := N) (Nstar := Nstar) (L := L)
      (i := i) e
      (C_S := C_S) (C_edgeMem := C_edgeMem) (linTerm := linTerm)
      (S_term :=
        coarseFluctuationFullBlockSumAtScale hP hStruct hP4
          (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i))
      (starSqrtTerm :=
        centeredResponseStarSqrtTermAtScale hP hStruct
          ((memoryGridScale Nstar L (i - 1) : ℕ) : ℤ)
          ((memoryGridScale Nstar L i : ℕ) : ℤ) e)
      (P_tau_sum := P_km * (∑ x ∈ s, w x * tau x))
      (lowerEdge := lowerEdge) (lowerEdgeStar := lowerEdgeStar)
      hC_nonneg heps_pos hetaS_nonneg hetaSt_nonneg hlin_nonneg hedgeMem_nonneg
      hC_delta_nonneg hC_S
      hraw hrawStar hweak hweakStar h_sqrt h_sqrtStar h_eps h_S h_tau
      h_lower h_lowerStar

end Homogenization.HighContrast.EntryScale
