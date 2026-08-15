import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Homogenization.HighContrast.EntryScale.NoDropResponse
import Homogenization.HighContrast.EntryScale.Lyapunov.P1

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open scoped Matrix.Norms.Elementwise

namespace Homogenization.HighContrast.EntryScale

/--
Sharp variant of the linear scalar setup: identical to
`exists_noDrop_lyapunov_scalar_setup_linear`, with three additional positive
scalars `etaSrc`, `polyRootBound`, `c_fold` and the reserved source payment
`C_src * (etaSrc + polyRootBound + 2*rho + c_fold) ≤ decay` needed by the
resized source budget's L-G grid/channel payment.
-/
theorem exists_noDrop_lyapunov_scalar_setup_linear_sharp
    {d : ℕ} (hc : HighContrastExponents d) {C_delta C_memory C_edgeMem C_src : ℝ}
    (hC_delta_nonneg : 0 ≤ C_delta)
    (hC_memory_nonneg : 0 ≤ C_memory)
    (hC_edgeMem_nonneg : 0 ≤ C_edgeMem)
    (hC_src_nonneg : 0 ≤ C_src) :
    ∃ eps rho etaS etaSt decay etaSrc polyRootBound c_fold coeff memoryCoeff
      edgeMemoryCoeff K A lambda : ℝ,
      ∃ L : ℕ,
      0 < eps ∧ eps ≤ 1 ∧
      0 < rho ∧ rho ≤ 1 ∧
      0 < etaS ∧ 0 < etaSt ∧ 0 < decay ∧
      0 < L ∧
      noDropResponseDecay hc L ≤ decay ∧
      0 ≤ K ∧
      0 ≤ edgeMemoryCoeff ∧
      0 ≤ C_edgeMem ∧
      4 * memoryCoeff ≤ K ^ 2 ∧
      C_delta *
          (Real.sqrt rho + eps + eps⁻¹ * (etaS + etaSt + rho + rho ^ 2) +
            eps⁻¹ * decay) ≤ coeff ∧
      C_memory * eps⁻¹ ≤ memoryCoeff ∧
      C_edgeMem * eps⁻¹ ≤ edgeMemoryCoeff ∧
      2 * coeff ≤ (1 / 2 : ℝ) ∧
      0 ≤ A ∧ 0 < lambda ∧ lambda < 1 ∧
      (1 + rho)⁻¹ + A * memoryDecay hc L ≤ lambda ∧
      memoryDecay hc L ≤ lambda ∧
      (K + 16 * edgeMemoryCoeff) +
          A * (memoryDecay hc L *
                (1 + rho * (K + 16 * edgeMemoryCoeff))) ≤ lambda * A ∧
      0 < etaSrc ∧ 0 < polyRootBound ∧ 0 < c_fold ∧
      ((112 * (max C_delta 1 * (1 + 5 * C_src)))⁻¹) ^ 4 ≤ c_fold ∧
      C_src * (etaSrc + polyRootBound + 2 * rho + c_fold) ≤ decay := by
  obtain ⟨eps, rho, etaS, etaSt, decay, etaSrc, polyRootBound, c_fold,
      heps_pos, heps_le_one, hrho_pos, hrho_le_one, hetaS_pos, hetaSt_pos,
      hdecay_pos, hetaSrc_pos, hpolyRootBound_pos, hc_fold_pos, hc_fold_ge,
      hsrc_pay, hsmall_error⟩ :=
    exists_noDrop_response_error_parameters_sharp
      hC_delta_nonneg hC_src_nonneg
  set coeff : ℝ := (1 / 4 : ℝ) with hcoeff_def
  set memoryCoeff : ℝ := C_memory * eps⁻¹ with hmemoryCoeff_def
  set edgeMemoryCoeff : ℝ := C_edgeMem * eps⁻¹ with hedgeMemoryCoeff_def
  set K : ℝ := 2 * Real.sqrt memoryCoeff with hK_def
  have heps_inv_nonneg : 0 ≤ eps⁻¹ := inv_nonneg.mpr (le_of_lt heps_pos)
  have hmemoryCoeff_nonneg : 0 ≤ memoryCoeff := by
    rw [hmemoryCoeff_def]
    exact mul_nonneg hC_memory_nonneg heps_inv_nonneg
  have hedgeMemoryCoeff_nonneg : 0 ≤ edgeMemoryCoeff := by
    rw [hedgeMemoryCoeff_def]
    exact mul_nonneg hC_edgeMem_nonneg heps_inv_nonneg
  have hK_nonneg : 0 ≤ K := by
    rw [hK_def]; positivity
  have hKmem_le : 4 * memoryCoeff ≤ K ^ 2 := by
    rw [hK_def, mul_pow, Real.sq_sqrt hmemoryCoeff_nonneg]
    ring_nf
    exact le_rfl
  set Klin : ℝ := K + 16 * edgeMemoryCoeff with hKlin_def
  have hKlin_nonneg : 0 ≤ Klin := by
    rw [hKlin_def]
    have : 0 ≤ 16 * edgeMemoryCoeff :=
      mul_nonneg (by norm_num) hedgeMemoryCoeff_nonneg
    linarith
  obtain ⟨A, lambda, qMax, hA_nonneg, hlambda_pos, hlambda_lt_one,
      hqMax_pos, hcoeffs⟩ :=
    exists_lyapunov_coefficients_of_rho_pos hrho_pos hKlin_nonneg
  obtain ⟨L, hL_pos, hqL, hresponseDecay⟩ :=
    exists_memoryDecay_and_noDropResponseDecay_le_of_pos hc hqMax_pos hdecay_pos
  have hq_nonneg : 0 ≤ memoryDecay hc L :=
    le_of_lt (memoryDecay_pos hc L)
  obtain ⟨hdrop, hdecay_lambda, hmemory⟩ := hcoeffs hq_nonneg hqL
  refine
    ⟨eps, rho, etaS, etaSt, decay, etaSrc, polyRootBound, c_fold, coeff,
      memoryCoeff, edgeMemoryCoeff, K, A, lambda, L, heps_pos, heps_le_one,
      hrho_pos, hrho_le_one, hetaS_pos, hetaSt_pos, hdecay_pos, hL_pos,
      hresponseDecay, hK_nonneg, hedgeMemoryCoeff_nonneg, hC_edgeMem_nonneg,
      hKmem_le, ?_, le_rfl, le_rfl, ?_, hA_nonneg, hlambda_pos,
      hlambda_lt_one, hdrop, hdecay_lambda, ?_, hetaSrc_pos,
      hpolyRootBound_pos, hc_fold_pos, hc_fold_ge, hsrc_pay⟩
  · rw [hcoeff_def]; exact hsmall_error
  · rw [hcoeff_def]; norm_num
  · rw [← hKlin_def]; exact hmemory

/--
Source labels `p.nodrop.CR` and `e.sqrt.tau.absorb`: on a memory-grid
no-drop branch, the deterministic tau-drop estimate and the library's lower-scale
response bound give the square-root product feed used by the no-drop response
assembly.
-/
theorem tauAtMemoryGrid_mul_expectedResponseJCubeSet_special_le_sqrt_budget_sq_of_noDrop_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {Nstar L i : ℕ} (e : Homogenization.Vec d)
    {rho delta C_sqrt : ℝ}
    (he : Homogenization.Book.Ch02.vecNorm e = 1)
    (hrho_pos : 0 < rho)
    (hrho_le_one : rho ≤ 1)
    (hdelta_pos : 0 < delta)
    (hdelta_le_F :
      delta ≤ contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
    (hC_response_le : (2 : ℝ) ≤ C_sqrt ^ 2)
    (hno :
      noDropWindow rho
        (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1)))
        (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))) :
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
      (C_sqrt * Real.sqrt rho * Real.sqrt delta⁻¹ * F_i) ^ 2 := by
  let m : ℕ := memoryGridScale Nstar L i
  let k : ℕ := memoryGridScale Nstar L (i - 1)
  let F_i : ℝ := contrastExcessAtScale hP hStruct m
  have hsqrt_tau_drop :
      Real.sqrt (1 + F_i) *
        Homogenization.Book.Ch05.tauAtScale P (m : ℤ) (k : ℤ)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) ≤
        (1 / 2 : ℝ) * (rho * F_i) := by
    have hkm : k ≤ m := by
      dsimp [k, m]
      exact memoryGridScale_le_of_le (Nat.sub_le i 1)
    have hdet :
        Real.sqrt (1 + contrastExcessAtScale hP hStruct m) *
            Homogenization.Book.Ch05.tauAtScale P (m : ℤ) (k : ℤ)
              (Homogenization.Book.Ch05.specialPAtScale hP hStruct
                (m : ℤ) e)
              (Homogenization.Book.Ch05.specialQAtScale hP hStruct
                (m : ℤ) e) ≤
          (1 / 2 : ℝ) *
            (contrastExcessAtScale hP hStruct k -
              contrastExcessAtScale hP hStruct m) :=
      sqrt_contrastExcess_mul_tauAtScale_special_le_half_contrastExcess_drop_of_P4
        hP hStruct hP4 hkm e he
    have hdrop_branch :
        contrastExcessAtScale hP hStruct k -
            contrastExcessAtScale hP hStruct m ≤
          rho * F_i := by
      simpa [m, k, F_i, noDropWindow] using hno
    have hhalf :
        (1 / 2 : ℝ) *
            (contrastExcessAtScale hP hStruct k -
              contrastExcessAtScale hP hStruct m) ≤
          (1 / 2 : ℝ) * (rho * F_i) := by
      exact mul_le_mul_of_nonneg_left hdrop_branch
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
    exact hdet.trans hhalf
  let r_m : ℝ := Real.sqrt (1 + F_i)
  have hr_pos : 0 < r_m := by
    dsimp [r_m]
    exact Real.sqrt_pos.2 (by linarith : 0 < 1 + F_i)
  have hresponse_nonneg :
      0 ≤
        Homogenization.Book.Ch04.expectedResponseJCubeSet P
          (Homogenization.originCube d (k : ℤ))
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct
            (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct
            (m : ℤ) e) :=
    expectedResponseJCubeSet_nonneg
      (Homogenization.originCube d (k : ℤ))
      (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
      (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e)
  have hsqrt_tau_drop' :
      r_m *
        Homogenization.Book.Ch05.tauAtScale P (m : ℤ) (k : ℤ)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct
            (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct
            (m : ℤ) e) ≤
        (1 / 2 : ℝ) * (rho * F_i) := by
    simpa [r_m] using hsqrt_tau_drop
  have hresponse_le :
      Homogenization.Book.Ch04.expectedResponseJCubeSet P
          (Homogenization.originCube d (k : ℤ))
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct
            (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct
            (m : ℤ) e) ≤
        (2 : ℝ) * r_m := by
    have hkm : k ≤ m := by
      dsimp [k, m]
      exact memoryGridScale_le_of_le (Nat.sub_le i 1)
    have hresp :=
      expectedResponseJCubeSet_special_le_two_mul_sqrt_contrastExcess_of_noDrop_of_P4
        hP hStruct hP4 hkm hno hrho_pos hrho_le_one e he
    simpa [m, k, F_i, r_m] using hresp
  simpa [m, k, F_i, r_m] using
    tau_mul_response_le_sqrt_budget_sq_of_rtau_response_bounds
      (tau :=
        Homogenization.Book.Ch05.tauAtScale P (m : ℤ) (k : ℤ)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct
            (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct
            (m : ℤ) e))
      (response :=
        Homogenization.Book.Ch04.expectedResponseJCubeSet P
          (Homogenization.originCube d (k : ℤ))
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct
            (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct
            (m : ℤ) e))
      (r_m := r_m) (C_response := 2) (C_sqrt := C_sqrt)
      (rho := rho) (delta := delta) (F_m := F_i)
      hr_pos hresponse_nonneg (le_of_lt hrho_pos) hdelta_pos
      (by simpa [m, F_i] using hdelta_le_F)
      hsqrt_tau_drop' hresponse_le (by norm_num) hC_response_le

/-- **Layer B linear channel: top-level packaged no-bad Lyapunov step with the
edge-memory residual slot.**

Linear analog of
`lyapunov_step_of_memoryGrid_noDropResponse_lower_memory_no_bad_packaged_fluctuation_tau_and_sqrt`:
`h_lower`/`h_lowerStar` carry the additional `H`-linear edge-memory residual
`C_edgeMem·eps⁻¹·((Hprev/(1+F_prev))·terminalP k m)`, and the derivation routes
through the linear no-drop RHS and the linear Lyapunov capstone
`lyapunov_step_of_memoryGrid_noDropResponse_lower_memory_linear`. -/
theorem lyapunov_step_of_memoryGrid_noDropResponse_lower_memory_no_bad_packaged_fluctuation_tau_and_sqrt_linear
    {ι : Type*} (s : Finset ι)
    {d : ℕ} [NeZero d] (hc : HighContrastExponents d)
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {N Nstar L i : ℕ} (e : Homogenization.Vec d)
    {A K lambda rho C C_delta C_memory C_edgeMem C_S C_fluct C_sqrt eps etaS
      etaSt decay weakNormGood weakNormGoodStar lowerEdge lowerEdgeStar T_weight
      delta r_m P_km Cw coeff memoryCoeff edgeMemoryCoeff : ℝ}
    {w tau drop : ι → ℝ}
    (he : Homogenization.Book.Ch02.vecNorm e = 1)
    (hi : 1 ≤ i)
    (hlambda_nonneg : 0 ≤ lambda)
    (hA_nonneg : 0 ≤ A)
    (hK_nonneg : 0 ≤ K)
    (hedgeMemoryCoeff_nonneg : 0 ≤ edgeMemoryCoeff)
    (hedgeMem_nonneg : 0 ≤ C_edgeMem)
    (hKmem_le : 4 * memoryCoeff ≤ K ^ 2)
    (hdrop_coeff : (1 + rho)⁻¹ + A * memoryDecay hc L ≤ lambda)
    (hdrop_memory_coeff : memoryDecay hc L ≤ lambda)
    (hmemory_coeff :
      (K + 16 * edgeMemoryCoeff) +
          A * (memoryDecay hc L *
                (1 + rho * (K + 16 * edgeMemoryCoeff))) ≤ lambda * A)
    (hC_nonneg : 0 ≤ C)
    (hC_sqrt_nonneg : 0 ≤ C_sqrt)
    (heps_pos : 0 < eps)
    (hrho_nonneg : 0 ≤ rho)
    (hrho_pos : 0 < rho)
    (hrho_le_one : rho ≤ 1)
    (hetaS_nonneg : 0 ≤ etaS)
    (hetaSt_nonneg : 0 ≤ etaSt)
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
      noDropWindow rho
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1)))
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) →
        T_weight *
            coarseFluctuationFullBlockSumAtScale hP hStruct hP4
              (memoryGridScale Nstar L (i - 1)) (memoryGridScale Nstar L i) ≤
          C_fluct * (etaS + rho ^ 2) *
            contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
    (hC_fluct_budget : C * C_fluct ≤ C_S)
    (hP_le_of_noDrop :
      noDropWindow rho
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1)))
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) →
        P_km ≤ 4 * r_m)
    (hw_nonneg : ∀ x ∈ s, 0 ≤ w x)
    (htau_nonneg : ∀ x ∈ s, 0 ≤ tau x)
    (hrt : ∀ x ∈ s, r_m * tau x ≤ (1 / 2 : ℝ) * drop x)
    (hdrop :
      noDropWindow rho
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1)))
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) →
        ∀ x ∈ s, drop x ≤
          rho * contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
    (hCw : ∑ x ∈ s, w x ≤ Cw)
    (hbudget_tau : C * (2 * Cw) ≤ C_delta)
    (hC_response_le : (2 : ℝ) ≤ C_sqrt ^ 2)
    (hbudget_sqrt : C * C_sqrt * Real.sqrt delta⁻¹ ≤ C_delta)
    (hraw :
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
        C * eps * F_i + C * eps⁻¹ * weakNormGood)
    (hrawStar :
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
                (memoryGridScale Nstar L i)))
    (h_lowerStar :
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
                (memoryGridScale Nstar L i)))
    (hcoeff_bound :
      C_delta *
        (Real.sqrt rho + eps + eps⁻¹ * (etaS + etaSt + rho + rho ^ 2) +
          eps⁻¹ * decay) ≤ coeff)
    (hmemoryCoeff : C_memory * eps⁻¹ ≤ memoryCoeff)
    (hedgeMemoryCoeff : C_edgeMem * eps⁻¹ ≤ edgeMemoryCoeff)
    (hsmall : 2 * coeff ≤ (1 / 2 : ℝ)) :
    let Fgrid : ℕ → ℝ := fun n => contrastExcessAtScale hP hStruct n
    let q : ℝ := memoryDecay hc L
    let H0 : ℝ := initialMemory hc.rhoM N Nstar Fgrid
    let Delta : ℕ → ℝ := memoryGridDrop Fgrid Nstar L
    let F_prev : ℝ :=
      contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1))
    let F_i : ℝ :=
      contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)
    let H_prev : ℝ := memory q H0 Delta (i - 1)
    let H_i : ℝ := memory q H0 Delta i
    lyapunovValue A F_i H_i ≤ lambda * lyapunovValue A F_prev H_prev := by
  exact
    lyapunov_step_of_memoryGrid_noDropResponse_lower_memory_linear
      (hc := hc) (hP := hP) (hStruct := hStruct) (hP4 := hP4)
      (N := N) (Nstar := Nstar) (L := L) (i := i)
      (A := A) (K := K) (lambda := lambda) (rho := rho)
      (edgeMemoryCoeff := edgeMemoryCoeff) (memoryCoeff := memoryCoeff)
      hi hlambda_nonneg hA_nonneg hK_nonneg hedgeMemoryCoeff_nonneg
      hKmem_le hdrop_coeff hdrop_memory_coeff hmemory_coeff hrho_nonneg
      hrho_pos hrho_le_one
      (by
        intro hno
        let m : ℕ := memoryGridScale Nstar L i
        let k : ℕ := memoryGridScale Nstar L (i - 1)
        let F_i : ℝ := contrastExcessAtScale hP hStruct m
        have hP_le : P_km ≤ 4 * r_m := hP_le_of_noDrop hno
        have hsqrt_prod :
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
              (C_sqrt * Real.sqrt rho * Real.sqrt delta⁻¹ * F_i) ^ 2 := by
          exact
            tauAtMemoryGrid_mul_expectedResponseJCubeSet_special_le_sqrt_budget_sq_of_noDrop_of_P4
              (hP := hP) (hStruct := hStruct) (hP4 := hP4)
              (Nstar := Nstar) (L := L) (i := i) (e := e)
              (rho := rho) (delta := delta) (C_sqrt := C_sqrt)
              he hrho_pos hrho_le_one hdelta_pos hdelta_le_F
              hC_response_le hno
        have hkm :
            memoryGridScale Nstar L (i - 1) ≤ memoryGridScale Nstar L i :=
          memoryGridScale_le_of_le (Nat.sub_le i 1)
        have hF_antitone :
            Antitone (fun n => contrastExcessAtScale hP hStruct n) :=
          contrastExcessAtScale_antitone_of_P4 hP hStruct hP4
        have hHprev_nonneg :
            0 ≤ memory (memoryDecay hc L)
              (initialMemory hc.rhoM N Nstar
                (fun n => contrastExcessAtScale hP hStruct n))
              (memoryGridDrop
                (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
              (i - 1) :=
          memory_nonneg (le_of_lt (memoryDecay_pos hc L))
            (initialMemory_nonneg_of_antitone hF_antitone)
            (fun j => by
              cases j with
              | zero => simp
              | succ j =>
                  exact memoryGridDrop_succ_nonneg_of_antitone hF_antitone
                    Nstar L j)
            (i - 1)
        have hFprev_nonneg :
            0 ≤ contrastExcessAtScale hP hStruct
              (memoryGridScale Nstar L (i - 1)) :=
          contrastExcessAtScale_nonneg_of_P4 hP hStruct hP4
            (memoryGridScale Nstar L (i - 1))
        have hP_nonneg :
            0 ≤ terminalPAtScales hP hStruct (memoryGridScale Nstar L (i - 1))
              (memoryGridScale Nstar L i) :=
          terminalPAtScales_nonneg_of_P4 hP hStruct hP4 hkm
        have hlin_nonneg :
            0 ≤
              (memory (memoryDecay hc L)
                    (initialMemory hc.rhoM N Nstar
                      (fun n => contrastExcessAtScale hP hStruct n))
                    (memoryGridDrop
                      (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
                    (i - 1) /
                  (1 +
                    contrastExcessAtScale hP hStruct
                      (memoryGridScale Nstar L (i - 1)))) *
                terminalPAtScales hP hStruct (memoryGridScale Nstar L (i - 1))
                  (memoryGridScale Nstar L i) :=
          mul_nonneg
            (div_nonneg hHprev_nonneg (by linarith [hFprev_nonneg]))
            hP_nonneg
        have hresponses :=
          expectedCenteredResponsesAtMemoryGrid_le_noDropResponseRHSLinear_of_split_raw_highContrast_lower_memory_no_bad_with_packaged_fluctuation_tau_and_sqrt_linear
            (hc := hc) (s := s) (hP := hP) (hStruct := hStruct)
            (hP4 := hP4) (N := N) (Nstar := Nstar) (L := L)
            (i := i) (e := e) (rho := rho) (C := C)
            (C_delta := C_delta) (C_memory := C_memory)
            (C_edgeMem := C_edgeMem) (C_S := C_S)
            (C_fluct := C_fluct) (C_sqrt := C_sqrt) (eps := eps)
            (etaS := etaS) (etaSt := etaSt) (decay := decay)
            (weakNormGood := weakNormGood)
            (weakNormGoodStar := weakNormGoodStar)
            (lowerEdge := lowerEdge) (lowerEdgeStar := lowerEdgeStar)
            (T_weight := T_weight) (delta := delta) (r_m := r_m)
            (P_km := P_km) (Cw := Cw) (w := w) (tau := tau)
            (drop := drop)
            (linTerm :=
              (memory (memoryDecay hc L)
                    (initialMemory hc.rhoM N Nstar
                      (fun n => contrastExcessAtScale hP hStruct n))
                    (memoryGridDrop
                      (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
                    (i - 1) /
                  (1 +
                    contrastExcessAtScale hP hStruct
                      (memoryGridScale Nstar L (i - 1)))) *
                terminalPAtScales hP hStruct (memoryGridScale Nstar L (i - 1))
                  (memoryGridScale Nstar L i))
            hC_nonneg hC_sqrt_nonneg heps_pos hrho_nonneg
            hetaS_nonneg hetaSt_nonneg hlin_nonneg hedgeMem_nonneg
            hC_delta_nonneg hC_S hdelta_pos
            hdelta_le_F hT_weight (hfluct hno) hC_fluct_budget hP_le
            hw_nonneg htau_nonneg hrt (hdrop hno) hCw hbudget_tau
            hsqrt_prod hbudget_sqrt (hraw hno) (hrawStar hno) hweak
            hweakStar h_eps (h_lower hno) (h_lowerStar hno)
        have halt :=
          memory_alt_linear_of_memoryGrid_noDropResponseRHSLinear hP hStruct hP4
            (memoryGridScale Nstar L i) e
            (C_edgeMem := C_edgeMem) (edgeMemoryCoeff := edgeMemoryCoeff)
            (linTerm :=
              (memory (memoryDecay hc L)
                    (initialMemory hc.rhoM N Nstar
                      (fun n => contrastExcessAtScale hP hStruct n))
                    (memoryGridDrop
                      (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
                    (i - 1) /
                  (1 +
                    contrastExcessAtScale hP hStruct
                      (memoryGridScale Nstar L (i - 1)))) *
                terminalPAtScales hP hStruct (memoryGridScale Nstar L (i - 1))
                  (memoryGridScale Nstar L i))
            (Hprev :=
              memory (memoryDecay hc L)
                (initialMemory hc.rhoM N Nstar
                  (fun n => contrastExcessAtScale hP hStruct n))
                (memoryGridDrop
                  (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
                (i - 1))
            he hlin_nonneg hresponses.1 hresponses.2 hcoeff_bound hmemoryCoeff
            hedgeMemoryCoeff hsmall
        simpa [mul_assoc] using halt)

end Homogenization.HighContrast.EntryScale
