import Homogenization.CoarseGraining.AdjointSymmetry.BasicAdjoint
import Homogenization.Book.Ch04.Theorems.CoarseObservables
import Homogenization.Book.Ch04.Theorems.DilationResponse
import Homogenization.HighContrast.EntryScale.ResponseFluctuation
import Homogenization.HighContrast.EntryScale.ResponseMoment.P1
import Homogenization.HighContrast.EntryScale.ResponseMoment.P2

open MeasureTheory
open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization.Book.Ch05.Section54.OneStepContraction
open scoped Matrix.Norms.Elementwise

namespace Homogenization.HighContrast.EntryScale

/--
Source label `e.J.moment.bound`: primal and adjoint/star response moments are
controlled by the manuscript scale `r_m` times the fixed-window stochastic
maximum contribution.  This is the response half after the pointwise `J/J^*`
bound, the `ζ <= 2` Lyapunov step, the no-drop normalization, and the
conversion `sqrt(theta_m) = r_m`.
-/
theorem coarseFluctuationResponseMoment_add_star_le_four_r_m_mul_window_stochasticMax_add_two
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {rho r_m : ℝ} {N k m L : ℕ}
    (e : Homogenization.Vec d)
    (he : Homogenization.Book.Ch02.vecNorm e = 1)
    (hrho_nonneg : 0 ≤ rho) (hrho_le_one : rho ≤ 1)
    (hNk : N ≤ k) (hkm : k ≤ m) (hWindow : m - k ≤ L)
    (hno :
      noDropWindow rho
        (contrastExcessAtScale hP hStruct k)
        (contrastExcessAtScale hP hStruct m))
    (hr_nonneg : 0 ≤ r_m)
    (hr_sq : r_m ^ 2 = 1 + contrastExcessAtScale hP hStruct m)
    (hM_mem :
      MeasureTheory.MemLp
        (terminalCoarseBlockStochasticMax hP hStruct hc N m
          (Homogenization.originCube d (m : ℤ))
          (fun x : Homogenization.RegCoeffField d => x))
        (2 : ENNReal) P) :
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e +
        coarseFluctuationResponseMomentStarAtScale hP hStruct hP4 k m e ≤
      4 * r_m *
        ((3 : ℝ) ^ (hc.rhoM * (L : ℝ)) *
            Homogenization.Book.Ch04.annealedMomentRoot P 2
              (terminalCoarseBlockStochasticMax hP hStruct hc N m
                (Homogenization.originCube d (m : ℤ))
                (fun x : Homogenization.RegCoeffField d => x)) + 2) := by
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  let θ := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
  let Troot : ℝ :=
    Homogenization.Book.Ch04.annealedMomentRoot P 2
      (fun a : Homogenization.RegCoeffField d =>
        terminalUncenteredCoarseBlockNorm hP hStruct m
          (Homogenization.originCube d (k : ℤ)) a)
  let Mroot : ℝ :=
    Homogenization.Book.Ch04.annealedMomentRoot P 2
      (terminalCoarseBlockStochasticMax hP hStruct hc N m
        (Homogenization.originCube d (m : ℤ))
        (fun x : Homogenization.RegCoeffField d => x))
  let B : ℝ := (3 : ℝ) ^ (hc.rhoM * (L : ℝ)) * Mroot + 2
  have hT_mem :
      MeasureTheory.MemLp
        (fun a : Homogenization.RegCoeffField d =>
          terminalUncenteredCoarseBlockNorm hP hStruct m
            (Homogenization.originCube d (k : ℤ)) a)
        (2 : ENNReal) P :=
    terminalUncenteredCoarseBlockNorm_origin_memLp_two_of_stochasticMax
      hP hStruct hP4 hc hNk hkm hno hM_mem
  have hJ :
      coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e ≤
        2 * Real.sqrt θ * Troot := by
    simpa [Troot, θ] using
      coarseFluctuationResponseMomentAtScale_le_two_sqrtTheta_terminalUncenteredMomentRoot_two
        hP hStruct hP4 k m e he hT_mem
  have hJstar_eq :
      coarseFluctuationResponseMomentStarAtScale hP hStruct hP4 k m e =
        coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e :=
    coarseFluctuationResponseMomentStarAtScale_eq_responseMomentAtScale
      hP hStruct hP4 k m e
  have hTroot_le : Troot ≤ B := by
    simpa [Troot, Mroot, B] using
      terminalUncenteredCoarseBlockNorm_origin_annealedMomentRoot_two_le_window_stochasticMax_add_two
        hP hStruct hP4 hc hrho_nonneg hrho_le_one hNk hkm hWindow hno hM_mem
  have hsqrt : Real.sqrt θ = r_m := by
    simpa [θ] using
      sqrt_thetaAtScale_eq_r_m_of_sq_contrastExcess hP hStruct m hr_nonneg hr_sq
  have hcoef_nonneg : 0 ≤ 4 * r_m := by
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hr_nonneg
  calc
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e +
        coarseFluctuationResponseMomentStarAtScale hP hStruct hP4 k m e
        = coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e +
            coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
          rw [hJstar_eq]
    _ ≤ 2 * Real.sqrt θ * Troot + 2 * Real.sqrt θ * Troot :=
          add_le_add hJ hJ
    _ = 4 * Real.sqrt θ * Troot := by ring
    _ = 4 * r_m * Troot := by rw [hsqrt]
    _ ≤ 4 * r_m * B := by
          exact mul_le_mul_of_nonneg_left hTroot_le hcoef_nonneg
    _ =
        4 * r_m *
          ((3 : ℝ) ^ (hc.rhoM * (L : ℝ)) *
              Homogenization.Book.Ch04.annealedMomentRoot P 2
                (terminalCoarseBlockStochasticMax hP hStruct hc N m
                  (Homogenization.originCube d (m : ℤ))
                  (fun x : Homogenization.RegCoeffField d => x)) + 2) := by
          rfl

/--
Source label `e.J.moment.bound`: after the logarithmic high-moment buffer,
the paired response moments are bounded by `r_m` times an explicit fixed-window
constant and the chosen stochastic tolerance.
-/
theorem exists_bufferExponent_responseMoment_add_star_le_four_r_m_mul_window_eta_add_two_of_Nstar
    {d : ℕ} [NeZero d] {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) (L : ℕ)
    {η_M : ℝ} (hη_M : 0 < η_M) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {P : Homogenization.Book.Ch04.CoeffLaw d}
        (hP : Homogenization.Book.Ch04.LawCarrier P)
        (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
        {rho r_m : ℝ} {N k m : ℕ}
        (e : Homogenization.Vec d),
          Homogenization.Book.Ch02.vecNorm e = 1 →
          0 ≤ rho → rho ≤ 1 →
          N ≤ k → k ≤ m → m - k ≤ L →
          noDropWindow rho
            (contrastExcessAtScale hP hStruct k)
            (contrastExcessAtScale hP hStruct m) →
          0 ≤ r_m →
          r_m ^ 2 = 1 + contrastExcessAtScale hP hStruct m →
          N + Nat.ceil
              (B * Real.logb 3
                (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) ≤
            m →
          HighCenteredMomentEstimate hm P N
            (intermediateCoarseBlockDeviation hP hStruct
              (fun x : Homogenization.RegCoeffField d => x)) →
          coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e +
              coarseFluctuationResponseMomentStarAtScale hP hStruct hP4 k m e ≤
            4 * r_m * ((3 : ℝ) ^ (hc.rhoM * (L : ℝ)) * η_M + 2) := by
  obtain ⟨B, hB_one, hB⟩ :=
    exists_bufferExponent_terminalCoarseBlockStochasticMax_annealedMomentRoot_two_le_of_Nstar
      hm hη_M
  refine ⟨B, hB_one, ?_⟩
  intro P hP hStruct hP4 rho r_m N k m e he hrho_nonneg hrho_le_one hNk hkm
    hWindow hno hr_nonneg hr_sq hNstar hHM
  let Mroot : ℝ :=
    Homogenization.Book.Ch04.annealedMomentRoot P 2
      (terminalCoarseBlockStochasticMax hP hStruct hc N m
        (Homogenization.originCube d (m : ℤ))
        (fun x : Homogenization.RegCoeffField d => x))
  let Cw : ℝ := (3 : ℝ) ^ (hc.rhoM * (L : ℝ))
  obtain ⟨hM_mem, hMroot_le⟩ :=
    hB hP hStruct hP4 hNstar hHM
  have hresponse :=
    coarseFluctuationResponseMoment_add_star_le_four_r_m_mul_window_stochasticMax_add_two
      hP hStruct hP4 hc e he hrho_nonneg hrho_le_one hNk hkm hWindow hno
      hr_nonneg hr_sq hM_mem
  have hCw_nonneg : 0 ≤ Cw := by
    dsimp [Cw]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hinner :
      Cw * Mroot + 2 ≤ Cw * η_M + 2 := by
    have hmul := mul_le_mul_of_nonneg_left hMroot_le hCw_nonneg
    linarith
  have hcoef_nonneg : 0 ≤ 4 * r_m :=
    mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hr_nonneg
  calc
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e +
        coarseFluctuationResponseMomentStarAtScale hP hStruct hP4 k m e
        ≤ 4 * r_m * (Cw * Mroot + 2) := by
          simpa [Cw, Mroot] using hresponse
    _ ≤ 4 * r_m * (Cw * η_M + 2) :=
          mul_le_mul_of_nonneg_left hinner hcoef_nonneg
    _ = 4 * r_m * ((3 : ℝ) ^ (hc.rhoM * (L : ℝ)) * η_M + 2) := by
          rfl

/--
Source labels `e.J.moment.bound` and `e.P.bound`: sharp `sqrt(theta_m)`
absorption of the primal response moment by the paired terminal-prefactor
response budget.  From the paired bound
`P_km * rM + P_km * rM* <= C_resp * (1 + F_m)` and the sharp pricing
`2 * sqrt(theta_m) <= P_km`, the single weighted moment `sqrt(theta_m) * rM`
costs at most half of the paired budget.
-/
theorem sqrtTheta_mul_responseMoment_le_of_terminalP_pair
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k ≤ m) (e : Homogenization.Vec d)
    {C_resp : ℝ}
    (hresponse_pair :
      terminalPAtScales hP hStruct k m *
          coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e +
        terminalPAtScales hP hStruct k m *
          coarseFluctuationResponseMomentStarAtScale hP hStruct hP4 k m e ≤
      C_resp * (1 + contrastExcessAtScale hP hStruct m)) :
    Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
        coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e ≤
      C_resp / 2 * (1 + contrastExcessAtScale hP hStruct m) := by
  let rM : ℝ := coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  let rMstar : ℝ :=
    coarseFluctuationResponseMomentStarAtScale hP hStruct hP4 k m e
  let P_km : ℝ := terminalPAtScales hP hStruct k m
  have hrM_nonneg : 0 ≤ rM := by
    simpa [rM] using
      coarseFluctuationResponseMomentAtScale_nonneg hP hStruct hP4 k m e
  have hrMstar_nonneg : 0 ≤ rMstar := by
    simpa [rMstar] using
      coarseFluctuationResponseMomentStarAtScale_nonneg hP hStruct hP4 k m e
  have hP_nonneg : 0 ≤ P_km := by
    simpa [P_km] using terminalPAtScales_nonneg_of_P4 hP hStruct hP4 hkm
  have htwo_sqrt :
      2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) ≤
        P_km := by
    simpa [P_km] using two_mul_sqrtTheta_le_terminalPAtScales_of_P4
      hP hStruct hP4 hkm
  have hstar_term_nonneg : 0 ≤ P_km * rMstar :=
    mul_nonneg hP_nonneg hrMstar_nonneg
  have hprimal :
      2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
          rM ≤
        P_km * rM :=
    mul_le_mul_of_nonneg_right htwo_sqrt hrM_nonneg
  have hpair : P_km * rM + P_km * rMstar ≤
      C_resp * (1 + contrastExcessAtScale hP hStruct m) := by
    simpa [P_km, rM, rMstar] using hresponse_pair
  have hmain :
      2 * (Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
          rM) ≤
        C_resp * (1 + contrastExcessAtScale hP hStruct m) := by
    nlinarith [hprimal, hpair, hstar_term_nonneg]
  have hgoal :
      Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
          rM ≤
        C_resp / 2 * (1 + contrastExcessAtScale hP hStruct m) := by
    linarith
  simpa [rM] using hgoal

end Homogenization.HighContrast.EntryScale
