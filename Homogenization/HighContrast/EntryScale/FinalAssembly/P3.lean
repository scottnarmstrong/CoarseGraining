import Mathlib.Tactic.Positivity
import Homogenization.HighContrast.EntryScale.ResponseMoment.P3

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization.Book.Ch05.Section54.OneStepContraction
open scoped Matrix.Norms.Elementwise

namespace Homogenization.HighContrast.EntryScale

/--
Source labels `e.J.moment.bound` and `e.P.bound`: paired terminal-prefactor
response bound with the `(1 + F_m)` target needed by the resized-budget L-G
payment.  On a no-drop window `P_{k,m} ≤ 4·r_m` and the paired response
moments are at most `4·r_m·(3^{ρM·L}·η_M + 2)` by the `a.HM` window bound,
so the pair costs at most `C_resp·r_m² = C_resp·(1+F_m)`.
-/
theorem exists_bufferExponent_terminal_p_mul_responseMoment_add_star_le_const_one_add_contrast_of_Nstar
    {d : ℕ} [NeZero d] {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) (L : ℕ)
    {η_M C_resp : ℝ} (hη_M : 0 < η_M)
    (hC_resp :
      4 * (4 * ((3 : ℝ) ^ (hc.rhoM * (L : ℝ)) * η_M + 2)) ≤ C_resp) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {P : Homogenization.Book.Ch04.CoeffLaw d}
        (hP : Homogenization.Book.Ch04.LawCarrier P)
        (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
        {rho : ℝ} {N k m : ℕ}
        (e : Homogenization.Vec d),
          Homogenization.Book.Ch02.vecNorm e = 1 →
          0 < rho → rho ≤ 1 →
          N ≤ k → k ≤ m → m - k ≤ L →
          noDropWindow rho
            (contrastExcessAtScale hP hStruct k)
            (contrastExcessAtScale hP hStruct m) →
          N + Nat.ceil
              (B * Real.logb 3
                (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) ≤
            m →
          HighCenteredMomentEstimate hm P N
            (intermediateCoarseBlockDeviation hP hStruct
              (fun x : Homogenization.RegCoeffField d => x)) →
          terminalPAtScales hP hStruct k m *
              coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e +
            terminalPAtScales hP hStruct k m *
              coarseFluctuationResponseMomentStarAtScale hP hStruct hP4 k m e ≤
            C_resp * (1 + contrastExcessAtScale hP hStruct m) := by
  obtain ⟨B, hB_one, hB⟩ :=
    exists_bufferExponent_responseMoment_add_star_le_four_r_m_mul_window_eta_add_two_of_Nstar
      hm L hη_M
  refine ⟨B, hB_one, ?_⟩
  intro P hP hStruct hP4 rho N k m e he hrho_pos hrho_le_one hNk hkm
    hWindow hno hNstar hHM
  set F_m : ℝ := contrastExcessAtScale hP hStruct m with hF_def
  have hF_nonneg : 0 ≤ F_m := by
    simpa [hF_def] using contrastExcessAtScale_nonneg_of_P4 hP hStruct hP4 m
  set r_m : ℝ := Real.sqrt (1 + F_m) with hr_def
  have hr_nonneg : 0 ≤ r_m := Real.sqrt_nonneg _
  have hr_sq : r_m ^ 2 = 1 + F_m := by
    rw [hr_def]
    exact Real.sq_sqrt (by linarith)
  have hpair :=
    hB hP hStruct hP4 (rho := rho) (r_m := r_m) e he (le_of_lt hrho_pos)
      hrho_le_one hNk hkm hWindow hno hr_nonneg (by simpa [hF_def] using hr_sq)
      hNstar hHM
  have hP_le : terminalPAtScales hP hStruct k m ≤ 4 * r_m := by
    simpa [hr_def, hF_def] using
      terminalPAtScales_le_four_mul_sqrt_contrastExcess_of_noDrop_of_P4
        hP hStruct hP4 hkm hno hrho_pos hrho_le_one
  have hP_nonneg : 0 ≤ terminalPAtScales hP hStruct k m :=
    terminalPAtScales_nonneg_of_P4 hP hStruct hP4 hkm
  have hRM_nonneg :
      0 ≤ coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e :=
    coarseFluctuationResponseMomentAtScale_nonneg hP hStruct hP4 k m e
  have hRMstar_nonneg :
      0 ≤ coarseFluctuationResponseMomentStarAtScale hP hStruct hP4 k m e :=
    coarseFluctuationResponseMomentStarAtScale_nonneg hP hStruct hP4 k m e
  have hsum_nonneg :
      0 ≤ coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e +
        coarseFluctuationResponseMomentStarAtScale hP hStruct hP4 k m e := by
    linarith
  have hCw_nonneg : 0 ≤ (3 : ℝ) ^ (hc.rhoM * (L : ℝ)) * η_M + 2 := by
    have h1 : 0 ≤ (3 : ℝ) ^ (hc.rhoM * (L : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    nlinarith
  calc
    terminalPAtScales hP hStruct k m *
        coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e +
      terminalPAtScales hP hStruct k m *
        coarseFluctuationResponseMomentStarAtScale hP hStruct hP4 k m e =
      terminalPAtScales hP hStruct k m *
        (coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e +
          coarseFluctuationResponseMomentStarAtScale hP hStruct hP4 k m e) := by
      ring
    _ ≤ (4 * r_m) *
        (coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e +
          coarseFluctuationResponseMomentStarAtScale hP hStruct hP4 k m e) :=
      mul_le_mul_of_nonneg_right hP_le hsum_nonneg
    _ ≤ (4 * r_m) * (4 * r_m * ((3 : ℝ) ^ (hc.rhoM * (L : ℝ)) * η_M + 2)) := by
      refine mul_le_mul_of_nonneg_left hpair ?_
      linarith
    _ = (4 * (4 * ((3 : ℝ) ^ (hc.rhoM * (L : ℝ)) * η_M + 2))) * r_m ^ 2 := by
      ring
    _ ≤ C_resp * r_m ^ 2 := by
      refine mul_le_mul_of_nonneg_right hC_resp ?_
      exact sq_nonneg _
    _ = C_resp * (1 + F_m) := by
      rw [hr_sq]


/--
Scalar payment of the sharp lower-edge budget on a no-drop window: the
canonical budget plus the (clamped) tail sum is absorbed by the
`C_delta`-decay and `C_memory`-memory channels.  All inputs are scalars; the
geometric/probabilistic content is consumed upstream.
-/
theorem sharp_lowerEdge_budget_payment
    {Fv Pv RMv RMSv TFv WNv SBv LBv SRCv MTv decay eps delta_sc C_resp
      C_step C_delta C_memory crudeC sharpC c_fold KFS CR1 KCv : ℝ}
    (hF_pos : 0 < Fv)
    (hδ_pos : 0 < delta_sc)
    (hdecay_pos : 0 < decay)
    (hdecay_le : decay ≤ (1 / 4 : ℝ))
    (heps_pos : 0 < eps)
    (hC_resp_nonneg : 0 ≤ C_resp)
    (hc_fold_pos : 0 < c_fold)
    (hpair : Pv * RMv + Pv * RMSv ≤ C_resp * (1 + Fv))
    (hone_le_P : (1 : ℝ) ≤ Pv)
    (hP_nonneg : 0 ≤ Pv)
    (hRM_nonneg : 0 ≤ RMv)
    (hRMS_nonneg : 0 ≤ RMSv)
    (hWN_eq : WNv = Pv)
    (htf_le : TFv ≤ decay / 2)
    (htf_nonneg : 0 ≤ TFv)
    (hδF : delta_sc ≤ Fv)
    (hsmall_le : SBv ≤ decay * (Pv * RMv))
    (hcrude : crudeC ≤ decay)
    (hlow_split : LBv = crudeC * RMv + SRCv)
    (hsrc_le :
      SRCv ≤ decay * ((1 + Fv) ^ 2 / Fv + Pv * RMv) + sharpC / c_fold * MTv)
    (hMT_nonneg : 0 ≤ MTv)
    (hKfold_le : sharpC / c_fold ≤ KFS)
    (hKFS_nonneg : 0 ≤ KFS)
    (hCR1_def : CR1 = C_resp * (1 + delta_sc⁻¹))
    (hKCv_def : KCv = (1 + delta_sc⁻¹) ^ 2 + CR1)
    (hCstep_nonneg : 0 ≤ C_step)
    (hsize_delta : C_step * (KCv + (1 + 8 * (CR1 + KCv))) ≤ C_delta)
    (hsize_mem : C_step * (8 * KFS) ≤ C_memory) :
    C_step * eps⁻¹ *
        (decay * ((1 + Fv) ^ 2 / Fv + Pv * RMv) +
          max 0
            (max 0
                (TFv * WNv * RMv + 2 * (TFv * Fv) +
                  TFv * (SBv + LBv + SRCv)) +
              SBv + LBv + SRCv)) ≤
      C_delta * eps⁻¹ * (decay * Fv) + C_memory * eps⁻¹ * MTv := by
  have hF_nonneg : 0 ≤ Fv := le_of_lt hF_pos
  have hδinv_nonneg : 0 ≤ delta_sc⁻¹ := inv_nonneg.mpr (le_of_lt hδ_pos)
  have hone_add_le : 1 + Fv ≤ (1 + delta_sc⁻¹) * Fv := by
    have hδF' : 1 ≤ delta_sc⁻¹ * Fv := by
      have h1 := mul_le_mul_of_nonneg_left hδF hδinv_nonneg
      rwa [inv_mul_cancel₀ (ne_of_gt hδ_pos)] at h1
    nlinarith only [hδF', hF_nonneg, hδinv_nonneg]
  have hPRM_le : Pv * RMv ≤ C_resp * (1 + Fv) := by
    nlinarith only [hpair, mul_nonneg hP_nonneg hRMS_nonneg]
  have hRM_le : RMv ≤ C_resp * (1 + Fv) := by
    nlinarith only [hPRM_le, mul_nonneg (sub_nonneg.mpr hone_le_P) hRM_nonneg]
  have hT_edge_le : (1 + Fv) ^ 2 / Fv ≤ (1 + delta_sc⁻¹) ^ 2 * Fv := by
    rw [div_le_iff₀ hF_pos]
    nlinarith only [mul_le_mul hone_add_le hone_add_le
      (by linarith only [hF_nonneg]) (by positivity)]
  have hCR1_nonneg : 0 ≤ CR1 := by
    rw [hCR1_def]
    exact mul_nonneg hC_resp_nonneg (by linarith only [hδinv_nonneg])
  have hKCv_nonneg : 0 ≤ KCv := by
    rw [hKCv_def]
    have h1 : 0 ≤ (1 + delta_sc⁻¹) ^ 2 := sq_nonneg _
    linarith only [h1, hCR1_nonneg]
  set DFv : ℝ := decay * Fv with hDFv_def
  have hDFv_nonneg : 0 ≤ DFv := by
    rw [hDFv_def]
    exact mul_nonneg (le_of_lt hdecay_pos) hF_nonneg
  have hPRMv_le : Pv * RMv ≤ CR1 * Fv := by
    rw [hCR1_def]
    calc
      Pv * RMv ≤ C_resp * (1 + Fv) := hPRM_le
      _ ≤ C_resp * ((1 + delta_sc⁻¹) * Fv) :=
        mul_le_mul_of_nonneg_left hone_add_le hC_resp_nonneg
      _ = C_resp * (1 + delta_sc⁻¹) * Fv := by ring
  have hRMv_le : RMv ≤ CR1 * Fv := by
    rw [hCR1_def]
    calc
      RMv ≤ C_resp * (1 + Fv) := hRM_le
      _ ≤ C_resp * ((1 + delta_sc⁻¹) * Fv) :=
        mul_le_mul_of_nonneg_left hone_add_le hC_resp_nonneg
      _ = C_resp * (1 + delta_sc⁻¹) * Fv := by ring
  have hcanon_le : decay * ((1 + Fv) ^ 2 / Fv + Pv * RMv) ≤ KCv * DFv := by
    have h1 :
        (1 + Fv) ^ 2 / Fv + Pv * RMv ≤
          (1 + delta_sc⁻¹) ^ 2 * Fv + CR1 * Fv :=
      add_le_add hT_edge_le hPRMv_le
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hdecay_pos)
    rw [hKCv_def, hDFv_def]
    nlinarith only [h2]
  have hKFM_nonneg : 0 ≤ KFS * MTv := mul_nonneg hKFS_nonneg hMT_nonneg
  have hsrc_bound : SRCv ≤ KCv * DFv + KFS * MTv := by
    have h2 : sharpC / c_fold * MTv ≤ KFS * MTv :=
      mul_le_mul_of_nonneg_right hKfold_le hMT_nonneg
    linarith only [hsrc_le, h2, hcanon_le]
  have hsmall_bound : SBv ≤ CR1 * DFv := by
    have h2 : decay * (Pv * RMv) ≤ decay * (CR1 * Fv) :=
      mul_le_mul_of_nonneg_left hPRMv_le (le_of_lt hdecay_pos)
    rw [hDFv_def]
    nlinarith only [hsmall_le, h2]
  have hcrude_bound : crudeC * RMv ≤ CR1 * DFv := by
    have h1 : crudeC * RMv ≤ decay * RMv :=
      mul_le_mul_of_nonneg_right hcrude hRM_nonneg
    have h2 : decay * RMv ≤ decay * (CR1 * Fv) :=
      mul_le_mul_of_nonneg_left hRMv_le (le_of_lt hdecay_pos)
    rw [hDFv_def]
    nlinarith only [h1, h2]
  have hlow_bound : LBv ≤ CR1 * DFv + (KCv * DFv + KFS * MTv) := by
    rw [hlow_split]
    exact add_le_add hcrude_bound hsrc_bound
  have hsum3_bound :
      SBv + LBv + SRCv ≤
        CR1 * DFv + (CR1 * DFv + (KCv * DFv + KFS * MTv)) +
          (KCv * DFv + KFS * MTv) := by
    linarith only [hsmall_bound, hlow_bound, hsrc_bound]
  have hCRDF_nonneg : 0 ≤ CR1 * DFv := mul_nonneg hCR1_nonneg hDFv_nonneg
  have hKCDF_nonneg : 0 ≤ KCv * DFv := mul_nonneg hKCv_nonneg hDFv_nonneg
  have hsum3_nonneg :
      0 ≤ CR1 * DFv + (CR1 * DFv + (KCv * DFv + KFS * MTv)) +
        (KCv * DFv + KFS * MTv) := by
    linarith only [hCRDF_nonneg, hKCDF_nonneg, hKFM_nonneg]
  have htf_le_one : TFv ≤ 1 := by
    linarith only [htf_le, hdecay_le]
  have hterm1 : TFv * WNv * RMv ≤ CR1 * DFv := by
    rw [hWN_eq]
    have h1 : TFv * (Pv * RMv) ≤ (decay / 2) * (CR1 * Fv) := by
      refine mul_le_mul htf_le hPRMv_le ?_ ?_
      · exact mul_nonneg hP_nonneg hRM_nonneg
      · linarith only [hdecay_le, hdecay_pos]
    rw [hDFv_def]
    nlinarith only [h1, hCR1_nonneg,
      mul_nonneg hCR1_nonneg
        (mul_nonneg (le_of_lt hdecay_pos) hF_nonneg)]
  have hterm2 : 2 * (TFv * Fv) ≤ DFv := by
    have h1 : TFv * Fv ≤ (decay / 2) * Fv :=
      mul_le_mul_of_nonneg_right htf_le hF_nonneg
    rw [hDFv_def]
    linarith only [h1]
  have hterm3 :
      TFv * (SBv + LBv + SRCv) ≤
        CR1 * DFv + (CR1 * DFv + (KCv * DFv + KFS * MTv)) +
          (KCv * DFv + KFS * MTv) := by
    calc
      TFv * (SBv + LBv + SRCv) ≤
          TFv *
            (CR1 * DFv + (CR1 * DFv + (KCv * DFv + KFS * MTv)) +
              (KCv * DFv + KFS * MTv)) :=
        mul_le_mul_of_nonneg_left hsum3_bound htf_nonneg
      _ ≤ 1 *
            (CR1 * DFv + (CR1 * DFv + (KCv * DFv + KFS * MTv)) +
              (KCv * DFv + KFS * MTv)) :=
        mul_le_mul_of_nonneg_right htf_le_one hsum3_nonneg
      _ = CR1 * DFv + (CR1 * DFv + (KCv * DFv + KFS * MTv)) +
            (KCv * DFv + KFS * MTv) := by ring
  have hchild_bound :
      TFv * WNv * RMv + 2 * (TFv * Fv) + TFv * (SBv + LBv + SRCv) ≤
        CR1 * DFv + DFv +
          (CR1 * DFv + (CR1 * DFv + (KCv * DFv + KFS * MTv)) +
            (KCv * DFv + KFS * MTv)) := by
    linarith only [hterm1, hterm2, hterm3]
  have hchildB_rhs_nonneg :
      0 ≤ CR1 * DFv + DFv +
          (CR1 * DFv + (CR1 * DFv + (KCv * DFv + KFS * MTv)) +
            (KCv * DFv + KFS * MTv)) := by
    linarith only [hCRDF_nonneg, hKCDF_nonneg, hKFM_nonneg, hDFv_nonneg]
  have hchild_max :
      max 0 (TFv * WNv * RMv + 2 * (TFv * Fv) + TFv * (SBv + LBv + SRCv)) ≤
        CR1 * DFv + DFv +
          (CR1 * DFv + (CR1 * DFv + (KCv * DFv + KFS * MTv)) +
            (KCv * DFv + KFS * MTv)) :=
    max_le hchildB_rhs_nonneg hchild_bound
  have htailX_bound :
      max 0 (TFv * WNv * RMv + 2 * (TFv * Fv) + TFv * (SBv + LBv + SRCv)) +
          SBv + LBv + SRCv ≤
        (1 + 8 * (CR1 + KCv)) * DFv + 8 * (KFS * MTv) := by
    nlinarith only [hchild_max, hsmall_bound, hlow_bound, hsrc_bound,
      hCRDF_nonneg, hKCDF_nonneg, hKFM_nonneg, hDFv_nonneg]
  have htailX_rhs_nonneg :
      0 ≤ (1 + 8 * (CR1 + KCv)) * DFv + 8 * (KFS * MTv) := by
    have h1 : 0 ≤ (1 + 8 * (CR1 + KCv)) * DFv := by
      refine mul_nonneg ?_ hDFv_nonneg
      linarith only [hCR1_nonneg, hKCv_nonneg]
    linarith only [h1, hKFM_nonneg]
  have hbudget_total :
      decay * ((1 + Fv) ^ 2 / Fv + Pv * RMv) +
          max 0
            (max 0
                (TFv * WNv * RMv + 2 * (TFv * Fv) +
                  TFv * (SBv + LBv + SRCv)) +
              SBv + LBv + SRCv) ≤
        (KCv + (1 + 8 * (CR1 + KCv))) * DFv + 8 * (KFS * MTv) := by
    have hmaxX :
        max 0
            (max 0
                (TFv * WNv * RMv + 2 * (TFv * Fv) +
                  TFv * (SBv + LBv + SRCv)) +
              SBv + LBv + SRCv) ≤
          (1 + 8 * (CR1 + KCv)) * DFv + 8 * (KFS * MTv) :=
      max_le htailX_rhs_nonneg htailX_bound
    nlinarith only [hcanon_le, hmaxX]
  have hepsinv_nonneg : 0 ≤ eps⁻¹ := le_of_lt (inv_pos.mpr heps_pos)
  calc
    C_step * eps⁻¹ *
        (decay * ((1 + Fv) ^ 2 / Fv + Pv * RMv) +
          max 0
            (max 0
                (TFv * WNv * RMv + 2 * (TFv * Fv) +
                  TFv * (SBv + LBv + SRCv)) +
              SBv + LBv + SRCv)) ≤
        C_step * eps⁻¹ *
          ((KCv + (1 + 8 * (CR1 + KCv))) * DFv + 8 * (KFS * MTv)) := by
      refine mul_le_mul_of_nonneg_left hbudget_total ?_
      exact mul_nonneg hCstep_nonneg hepsinv_nonneg
    _ = (C_step * (KCv + (1 + 8 * (CR1 + KCv)))) * (eps⁻¹ * DFv) +
          (C_step * (8 * KFS)) * (eps⁻¹ * MTv) := by
      ring
    _ ≤ C_delta * (eps⁻¹ * DFv) + C_memory * (eps⁻¹ * MTv) := by
      refine add_le_add ?_ ?_
      · exact mul_le_mul_of_nonneg_right hsize_delta
          (mul_nonneg hepsinv_nonneg hDFv_nonneg)
      · exact mul_le_mul_of_nonneg_right hsize_mem
          (mul_nonneg hepsinv_nonneg hMT_nonneg)
    _ = C_delta * eps⁻¹ * (decay * Fv) + C_memory * eps⁻¹ * MTv := by
      rw [hDFv_def]
      ring

end Homogenization.HighContrast.EntryScale
