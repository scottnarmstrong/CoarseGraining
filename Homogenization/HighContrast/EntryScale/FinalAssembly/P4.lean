import Mathlib.Tactic.Positivity
import Homogenization.HighContrast.EntryScale.LowerEdgeKernel
import Homogenization.HighContrast.EntryScale.Main
import Homogenization.HighContrast.EntryScale.FinalAssembly.P1
import Homogenization.HighContrast.EntryScale.FinalAssembly.P2
import Homogenization.HighContrast.EntryScale.FinalAssembly.P3
import Homogenization.HighContrast.EntryScale.EntryScale.P2

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization.Book.Ch05.Section54.OneStepContraction
open scoped Matrix.Norms.Elementwise

namespace Homogenization.HighContrast.EntryScale

/--
Source labels `t.main`, `l.lyapunov`, `e.Nentry`, `e.final.decay`, and
`e.final.scale`: final assembly from the Main raw-energy scalar one-step theorem.

The theorem fixes the quantitative coarse-grained ellipticity parameters before
choosing constants, then chooses the scalar no-drop/Lyapunov setup and obtains
the high-moment buffer exponent after the block length `L` is fixed.  The
raw cutoff geometric absorption is proved internally by enlarging `L`; the
corrected lower-edge source theorem supplies the remaining coarse-fluctuation
edge coefficient, so the final theorem does not expose a per-step source
callback.

**Subthreshold observable (2026-07-23).**  This theorem no longer quantifies a
subthreshold observable `M_sub` nor takes a `SubthresholdPolynomialMomentEstimate`
hypothesis.  That parameter was vacuous: `M_sub` entered the proof only through
the union bound and a measurability side condition, never the conclusion, so the
hypothesis was dischargeable at the zero observable (whose estimate holds
trivially, `∫⁻ ‖0‖ₑ^2 = 0 ≤ envelope`).  The proof now instantiates the internal
observable at `0`.  The subthreshold *parameters* `sub` are retained (they still
shape the union-bound envelope).
-/
theorem exists_final_scale_decay_of_main_buffer_and_rawEnergy_scalars
    {d : ℕ} [NeZero d] {hc : HighContrastExponents d}
    (params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    (loc : LocalizationSmallContrastInput hc)
    (hm : HighCenteredMomentParameters d hc)
    (hhmP4 : hm.p4Params = params) (hcp : hc.params = params)
    (sub : SubthresholdPolynomialMomentParameters) :
    ∃ delta_sc eps rho etaS etaM etaSt decay coeff memoryCoeff K A lambda C_A
      C_delta C_memory : ℝ,
    ∃ L : ℕ,
    ∃ B C_resp C_final alpha C_osc C_lin C_high : ℝ,
      0 < delta_sc ∧ delta_sc ≤ loc.delta0 / 2 ∧
      0 < eps ∧ eps ≤ 1 ∧
      0 < rho ∧ rho ≤ 1 ∧
      0 < etaS ∧ 0 < etaM ∧ 0 < etaSt ∧ 0 < decay ∧
      0 < L ∧
      0 ≤ C_delta ∧ 0 ≤ C_memory ∧
      noDropResponseDecay hc L ≤ decay ∧
      0 ≤ K ∧
      4 * memoryCoeff ≤ K ^ 2 ∧
      C_delta *
          (Real.sqrt rho + eps + eps⁻¹ * (etaS + etaSt + rho + rho ^ 2) +
            eps⁻¹ * decay) ≤ coeff ∧
      C_memory * eps⁻¹ ≤ memoryCoeff ∧
      2 * coeff ≤ (1 / 2 : ℝ) ∧
      0 ≤ A ∧ 0 < lambda ∧ lambda < 1 ∧
      (1 + rho)⁻¹ + A * memoryDecay hc L ≤ lambda ∧
      memoryDecay hc L ≤ lambda ∧
      K + A * (memoryDecay hc L * (1 + rho * K)) ≤ lambda * A ∧
      0 < C_A ∧ 1 + A ≤ C_A ∧
      1 ≤ B ∧
      4 * (4 * ((3 : ℝ) ^ (hc.rhoM * (L : ℝ)) * etaM + 2)) ≤ C_resp ∧
      0 ≤ C_osc ∧ 0 ≤ C_lin ∧
      0 ≤ C_high ∧
      0 < C_final ∧ 0 < alpha ∧
      ∀ {P : Homogenization.Book.Ch04.CoeffLaw d}
        (hP : Homogenization.Book.Ch04.LawCarrier P)
        (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
        {N Nstar I : ℕ},
          hP4.params = params →
          N =
            Nat.ceil
              (hm.p_hm * Real.logb 3
                (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) →
          Nstar =
            N + Nat.ceil
              (B * Real.logb 3
                (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) →
          I =
            Nat.ceil
              (Real.log
                  (C_A *
                    (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) /
                    delta_sc) /
                |Real.log lambda|) →
          (hNNstar : N ≤ Nstar) →
          HighCenteredMomentEstimate hm P N
            (intermediateCoarseBlockDeviation hP hStruct
              (fun x : Homogenization.CoeffField d => x)) →
            ∃ N0 : ℕ,
              (∀ n : ℕ,
                Homogenization.Book.Ch05.thetaAtScale hP hStruct
                    ((N0 + n : ℕ) : ℤ) ≤
                  1 + (3 : ℝ) ^ (-(alpha * (n : ℝ)))) ∧
              (N0 : ℝ) ≤
                C_final * Real.logb 3
                  (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ∧
              (3 : ℝ) ^ N0 ≤
                Real.rpow
                  (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)
                  C_final := by
  let delta_sc : ℝ := loc.delta0 / 2
  have hdelta_sc_pos : 0 < delta_sc := by
    dsimp [delta_sc]
    linarith only [loc.delta0_pos]
  have hdelta_sc_le : delta_sc ≤ loc.delta0 / 2 := by
    rfl
  rcases
      exists_rawEnergyConstants_bufferExponent_lyapunov_step_of_main_buffer_and_compact_source_lower_edge_linear_resized_scalars
        params hm hhmP4 hcp with
    ⟨C_osc, C_lin, C_high, hC_osc_nonneg, hC_lin_nonneg, hC_high_nonneg,
      hhead⟩
  -- `C_tail` is retained as a proof-local (used in the cutoff `max` budgets below);
  -- it is no longer an exposed output constant. The edge/tail currents are carried
  -- by the non-zero `lowerEdgeBudget`/`childTailBudget` and the memory channel.
  let C_tail : ℝ := 0
  let C_resp : ℝ := 64
  have hC_resp_nonneg : 0 ≤ C_resp := by
    dsimp [C_resp]
    norm_num
  -- sharp source constants: C_src reserves two L-G copies, c_foldStar is the
  -- explicit setup fold scalar, and C_delta/C_memory are enlarged to hold the
  -- on-window tail shares
  obtain ⟨sharpP, hsharpP_def⟩ :
      ∃ x : ℝ, x = max 0 (sourceMaxSharpConstParams params hc) := ⟨_, rfl⟩
  have hsharpP_nonneg : 0 ≤ sharpP := by
    rw [hsharpP_def]
    exact le_max_left 0 _
  obtain ⟨C_src, hC_src_def⟩ : ∃ x : ℝ, x = 2 * sharpP * C_resp := ⟨_, rfl⟩
  have hC_src_nonneg : 0 ≤ C_src := by
    rw [hC_src_def]
    exact mul_nonneg (mul_nonneg (by norm_num) hsharpP_nonneg) hC_resp_nonneg
  obtain ⟨C_stepP, hC_stepP_def⟩ :
      ∃ x : ℝ, x = finalAssemblySourceStepBoundParams params C_lin C_high :=
    ⟨_, rfl⟩
  have hC_stepP_nonneg : 0 ≤ C_stepP := by
    rw [hC_stepP_def]
    dsimp [finalAssemblySourceStepBoundParams]
    exact le_trans zero_le_one (le_max_left 1 _)
  obtain ⟨Kcan, hKcan_def⟩ :
      ∃ x : ℝ, x = (1 + delta_sc⁻¹) ^ 2 + C_resp * (1 + delta_sc⁻¹) :=
    ⟨_, rfl⟩
  have hKcan_nonneg : 0 ≤ Kcan := by
    rw [hKcan_def]
    have hδ : 0 ≤ delta_sc⁻¹ := inv_nonneg.mpr (le_of_lt hdelta_sc_pos)
    positivity
  obtain ⟨Ktot, hKtot_def⟩ :
      ∃ x : ℝ, x = 1 + 8 * (C_resp * (1 + delta_sc⁻¹) + Kcan) := ⟨_, rfl⟩
  have hKtot_nonneg : 0 ≤ Ktot := by
    rw [hKtot_def]
    have hδ : 0 ≤ delta_sc⁻¹ := inv_nonneg.mpr (le_of_lt hdelta_sc_pos)
    positivity
  obtain ⟨C_delta, hC_delta_def⟩ :
      ∃ x : ℝ, x =
        max 1
          (finalAssemblyDeltaBudgetBoundParams params delta_sc C_resp C_lin
              C_high +
            C_stepP * (Kcan + Ktot)) := ⟨_, rfl⟩
  have hC_delta_nonneg : 0 ≤ C_delta := by
    rw [hC_delta_def]
    exact le_trans zero_le_one (le_max_left 1 _)
  have hC_delta_one : (1 : ℝ) ≤ C_delta := by
    rw [hC_delta_def]
    exact le_max_left 1 _
  obtain ⟨c_foldStar, hc_foldStar_def⟩ :
      ∃ x : ℝ, x = ((112 * (max C_delta 1 * (1 + 5 * C_src)))⁻¹) ^ 4 :=
    ⟨_, rfl⟩
  have hc_foldStar_pos : 0 < c_foldStar := by
    rw [hc_foldStar_def]
    have h1 : (0 : ℝ) < max C_delta 1 :=
      lt_of_lt_of_le zero_lt_one (le_max_right C_delta 1)
    have h2 : (0 : ℝ) < 1 + 5 * C_src := by
      linarith only [hC_src_nonneg]
    have h3 : (0 : ℝ) < 112 * (max C_delta 1 * (1 + 5 * C_src)) := by
      have h4 : (0 : ℝ) < max C_delta 1 * (1 + 5 * C_src) := mul_pos h1 h2
      linarith only [h4]
    exact pow_pos (inv_pos.mpr h3) 4
  obtain ⟨C_memory, hC_memory_def⟩ :
      ∃ x : ℝ, x =
        finalAssemblyMemoryBudgetBoundParams params C_lin C_high +
          C_stepP * (8 * (sharpP * C_resp / c_foldStar)) := ⟨_, rfl⟩
  have hC_memory_nonneg : 0 ≤ C_memory := by
    rw [hC_memory_def]
    have h1 : 0 ≤ finalAssemblyMemoryBudgetBoundParams params C_lin C_high :=
      le_max_left _ _
    have h2 : 0 ≤ sharpP * C_resp / c_foldStar :=
      div_nonneg (mul_nonneg hsharpP_nonneg hC_resp_nonneg)
        (le_of_lt hc_foldStar_pos)
    have h3 : 0 ≤ C_stepP * (8 * (sharpP * C_resp / c_foldStar)) :=
      mul_nonneg hC_stepP_nonneg (by linarith only [h2])
    exact add_nonneg h1 h3
  obtain ⟨eps, rho, etaS, etaSt, decay, etaSrc, polyRootBound, c_fold, coeff,
      memoryCoeff, edgeMemoryCoeff, K, A, lambda, L_old,
      heps_pos, heps_le_one, hrho_pos, hrho_le_one, hetaS_pos, hetaSt_pos,
      hdecay_pos, hL_old_pos, hresponseDecay_old, hK_nonneg,
      hedgeMemoryCoeff_nonneg, hC_edgeMem_nonneg', hKmem_le, hcoeff_bound,
      hmemoryCoeff, hedgeMemCoeff_le, hsmall, hA_nonneg, hlambda_pos,
      hlambda_lt_one, hdrop_coeff_old, hdrop_memory_coeff_old,
      hmemory_coeff_old, hetaSrc_pos, hpolyRootBound_pos, hc_fold_pos,
      hc_fold_ge, hsrc_pay⟩ :=
    exists_noDrop_lyapunov_scalar_setup_linear_sharp
      hc hC_delta_nonneg hC_memory_nonneg (le_refl (0 : ℝ)) hC_src_nonneg
  let betaBudget : ℝ :=
    (section53CoarseFluctuationBetaParams params ^ (2 : ℕ))⁻¹
  let cutoffBudget : ℝ :=
    max 1
      (max (C_osc * betaBudget)
        (max (2 * C_tail * betaBudget) (2 * betaBudget)))
  have hcutoffBudget_pos : 0 < cutoffBudget := by
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 _)
  let cutoffScale : ℝ := decay / cutoffBudget
  have hcutoffScale_pos : 0 < cutoffScale := by
    exact div_pos hdecay_pos hcutoffBudget_pos
  obtain ⟨L_geo, hL_geo_pos, hL_geo⟩ :=
    exists_section53CoarseFluctuationBeta_twoBlockDecay_le_of_params
      (d := d) params hcutoffScale_pos
  let L : ℕ := max L_old L_geo
  have hL_old_le : L_old ≤ L := Nat.le_max_left L_old L_geo
  have hL_geo_le : L_geo ≤ L := Nat.le_max_right L_old L_geo
  have hL_pos : 0 < L := by
    exact lt_of_lt_of_le hL_old_pos hL_old_le
  have hresponseDecay : noDropResponseDecay hc L ≤ decay := by
    exact ((noDropResponseDecay_antitone hc) hL_old_le).trans hresponseDecay_old
  have hmemoryDecay_le_old : memoryDecay hc L ≤ memoryDecay hc L_old := by
    exact (memoryDecay_antitone hc) hL_old_le
  have hdrop_coeff :
      (1 + rho)⁻¹ + A * memoryDecay hc L ≤ lambda := by
    calc
      (1 + rho)⁻¹ + A * memoryDecay hc L ≤
          (1 + rho)⁻¹ + A * memoryDecay hc L_old := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left
                (mul_le_mul_of_nonneg_left hmemoryDecay_le_old hA_nonneg)
                (1 + rho)⁻¹
      _ ≤ lambda := hdrop_coeff_old
  have hdrop_memory_coeff : memoryDecay hc L ≤ lambda := by
    exact hmemoryDecay_le_old.trans hdrop_memory_coeff_old
  have hmemory_coeff :
      (K + 16 * edgeMemoryCoeff) +
          A * (memoryDecay hc L *
                (1 + rho * (K + 16 * edgeMemoryCoeff))) ≤ lambda * A := by
    have hfactor_nonneg : 0 ≤ 1 + rho * (K + 16 * edgeMemoryCoeff) := by
      have h1 : 0 ≤ rho * (K + 16 * edgeMemoryCoeff) :=
        mul_nonneg (le_of_lt hrho_pos)
          (by linarith only [hK_nonneg, hedgeMemoryCoeff_nonneg])
      linarith only [h1]
    calc
      (K + 16 * edgeMemoryCoeff) +
          A * (memoryDecay hc L *
                (1 + rho * (K + 16 * edgeMemoryCoeff))) ≤
          (K + 16 * edgeMemoryCoeff) +
            A * (memoryDecay hc L_old *
                  (1 + rho * (K + 16 * edgeMemoryCoeff))) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left
                (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hmemoryDecay_le_old hfactor_nonneg)
                  hA_nonneg) (K + 16 * edgeMemoryCoeff)
      _ ≤ lambda * A := hmemory_coeff_old
  have hmemory_coeff_plain :
      K + A * (memoryDecay hc L * (1 + rho * K)) ≤ lambda * A := by
    have h16 : 0 ≤ 16 * edgeMemoryCoeff := by
      linarith only [hedgeMemoryCoeff_nonneg]
    have hmD_nonneg : 0 ≤ memoryDecay hc L :=
      le_of_lt (memoryDecay_pos hc L)
    have hinner : 1 + rho * K ≤ 1 + rho * (K + 16 * edgeMemoryCoeff) := by
      have h1 : rho * K ≤ rho * (K + 16 * edgeMemoryCoeff) :=
        mul_le_mul_of_nonneg_left (by linarith only [h16])
          (le_of_lt hrho_pos)
      linarith only [h1]
    have hterm :
        A * (memoryDecay hc L * (1 + rho * K)) ≤
          A * (memoryDecay hc L *
            (1 + rho * (K + 16 * edgeMemoryCoeff))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hinner hmD_nonneg) hA_nonneg
    have hmono :
        K + A * (memoryDecay hc L * (1 + rho * K)) ≤
          (K + 16 * edgeMemoryCoeff) +
            A * (memoryDecay hc L *
              (1 + rho * (K + 16 * edgeMemoryCoeff))) := by
      linarith only [hterm, h16]
    exact hmono.trans hmemory_coeff
  let C_A : ℝ := 1 + A
  have hC_A_pos : 0 < C_A := by
    dsimp [C_A]
    linarith only [hA_nonneg]
  have hC_A : 1 + A ≤ C_A := by
    rfl
  let etaM : ℝ := ((3 : ℝ) ^ (hc.rhoM * (L : ℝ)))⁻¹
  have hetaM_pos : 0 < etaM := by
    dsimp [etaM]
    exact inv_pos.mpr
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3)
        (hc.rhoM * (L : ℝ)))
  have hC_resp_main :
      4 * (4 * ((3 : ℝ) ^ (hc.rhoM * (L : ℝ)) * etaM + 2)) ≤ C_resp := by
    let growth : ℝ := (3 : ℝ) ^ (hc.rhoM * (L : ℝ))
    have hgrowth_pos : 0 < growth := by
      dsimp [growth]
      exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3)
        (hc.rhoM * (L : ℝ))
    have hprod : growth * growth⁻¹ = 1 :=
      mul_inv_cancel₀ (ne_of_gt hgrowth_pos)
    calc
      4 * (4 * ((3 : ℝ) ^ (hc.rhoM * (L : ℝ)) * etaM + 2)) =
          4 * (4 * (growth * growth⁻¹ + 2)) := by
            simp [growth, etaM]
      _ = 48 := by
            rw [hprod]
            norm_num
      _ ≤ C_resp := by
            norm_num [C_resp]
  obtain ⟨B_main, hB_main_one, hstep_main⟩ :=
    hhead L hetaS_pos hetaSt_pos hdelta_sc_pos hL_pos hdecay_pos
  obtain ⟨B_union, hB_union_one, hunion⟩ :=
    exists_bufferExponent_lintegral_terminalCoarseBlockStochasticMax_add_subthresholdMax_le_memoryGrid_of_Nstar
      hm sub
      (etaSt := (etaSrc / 2) ^ ((params.xi : ℕ) : ℝ))
      (by
        have h1 : (0 : ℝ) < etaSrc / 2 := by linarith only [hetaSrc_pos]
        exact Real.rpow_pos_of_pos h1 _)
  obtain ⟨B_env, hB_env_one, henvroot⟩ :=
    exists_bufferExponent_sourceEnvelopeRoot_le_of_Nstar hm hpolyRootBound_pos
  obtain ⟨B_s3, hB_s3_one, hs3⟩ :=
    exists_bufferExponent_section52SmallTailTerminalResponseBudget_le_eta_mul_terminal_of_Nstar
      params (eta := decay) hdecay_pos
  obtain ⟨B_low, hB_low_one, hlow⟩ :=
    exists_bufferExponent_lowTailBelowStartCoeff_le_eta_of_Nstar
      params (eta := decay) hdecay_pos
  obtain ⟨B_pair, hB_pair_one, hpair⟩ :=
    exists_bufferExponent_terminal_p_mul_responseMoment_add_star_le_const_one_add_contrast_of_Nstar
      hm L hetaM_pos hC_resp_main
  let B : ℝ :=
    max (max (max B_main B_union) (max B_env B_s3)) (max B_low B_pair)
  have hB_main_le : B_main ≤ B :=
    ((le_max_left B_main B_union).trans
      (le_max_left (max B_main B_union) (max B_env B_s3))).trans
      (le_max_left _ (max B_low B_pair))
  have hB_union_le : B_union ≤ B :=
    ((le_max_right B_main B_union).trans
      (le_max_left (max B_main B_union) (max B_env B_s3))).trans
      (le_max_left _ (max B_low B_pair))
  have hB_env_le : B_env ≤ B :=
    ((le_max_left B_env B_s3).trans
      (le_max_right (max B_main B_union) (max B_env B_s3))).trans
      (le_max_left _ (max B_low B_pair))
  have hB_s3_le : B_s3 ≤ B :=
    ((le_max_right B_env B_s3).trans
      (le_max_right (max B_main B_union) (max B_env B_s3))).trans
      (le_max_left _ (max B_low B_pair))
  have hB_low_le : B_low ≤ B :=
    (le_max_left B_low B_pair).trans (le_max_right _ (max B_low B_pair))
  have hB_pair_le : B_pair ≤ B :=
    (le_max_right B_low B_pair).trans (le_max_right _ (max B_low B_pair))
  have hB_one : 1 ≤ B := by
    exact hB_main_one.trans hB_main_le
  obtain ⟨Centry, hCentry_nonneg, hentry⟩ :=
    exists_entryScaleConstant_theta_entry_and_memoryGridScale_le_logb_of_choices_initial
      (hc := hc) (d := d) (p_hm := hm.p_hm) (B := B)
      (C_A := C_A) (delta_sc := delta_sc) (lambda := lambda) (L := L)
      hm.p_hm_nonneg hB_one hC_A_pos hdelta_sc_pos hlambda_pos
      hlambda_lt_one
  obtain ⟨C_final, alpha, hC_final_pos, halpha_pos, hfinal_entry⟩ :=
    exists_uniform_final_scale_decay_and_physical_scale_of_entry
      hc loc hdelta_sc_le hCentry_nonneg
  refine
    ⟨delta_sc, eps, rho, etaS, etaM, etaSt, decay, coeff, memoryCoeff, K, A,
      lambda, C_A, C_delta, C_memory, L, B, C_resp, C_final, alpha, C_osc,
      C_lin, C_high,
      hdelta_sc_pos, hdelta_sc_le,
      heps_pos, heps_le_one, hrho_pos, hrho_le_one, hetaS_pos, hetaM_pos,
      hetaSt_pos, hdecay_pos, hL_pos, hC_delta_nonneg, hC_memory_nonneg,
      hresponseDecay, hK_nonneg, hKmem_le,
      hcoeff_bound, hmemoryCoeff, hsmall, hA_nonneg, hlambda_pos,
      hlambda_lt_one, hdrop_coeff, hdrop_memory_coeff, hmemory_coeff_plain,
      hC_A_pos, hC_A, hB_one, hC_resp_main, hC_osc_nonneg, hC_lin_nonneg,
      hC_high_nonneg, hC_final_pos,
      halpha_pos, ?_⟩
  intro P hP hStruct hP4 N Nstar I _hparams hN_eq hNstar_eq hI_eq hNNstar
    hHM
  have hP4_hc : hP4.params = hc.params := _hparams.trans hcp.symm
  -- The subthreshold observable is discharged internally at the **zero**
  -- observable: it enters the assembly only through the union bound and a
  -- measurability side condition (never the conclusion), so any choice works
  -- and the zero observable satisfies `SubthresholdPolynomialMomentEstimate`
  -- trivially (`∫⁻ ‖0‖ₑ^2 = 0 ≤ envelope`).  See the docstring note.
  let M_sub : ℕ → Homogenization.CoeffField d → ℝ := fun _ _ => (0 : ℝ)
  have hsub :
      SubthresholdPolynomialMomentEstimate hc sub P
        (Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) N M_sub :=
    { aestronglyMeasurable := fun {m} _ => MeasureTheory.aestronglyMeasurable_const
      moment_le := by
        intro m _
        have hpt :
            (fun ω : Homogenization.CoeffField d => ‖M_sub m ω‖ₑ ^ (2 : ℝ))
              = fun _ => (0 : ENNReal) := by
          funext ω
          show ‖(0 : ℝ)‖ₑ ^ (2 : ℝ) = (0 : ENNReal)
          rw [enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
        rw [hpt, MeasureTheory.lintegral_zero]
        exact zero_le _ }
  have hstep_one_based :
      ∀ j, 1 ≤ j →
        delta_sc ≤
          contrastExcessAtScale hP hStruct (memoryGridScale Nstar L j) →
        lyapunovValue A
            (contrastExcessAtScale hP hStruct
              (memoryGridScale Nstar L j))
            (memory (memoryDecay hc L)
              (initialMemory hc.rhoM N Nstar
                (fun n => contrastExcessAtScale hP hStruct n))
              (memoryGridDrop
                (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
              j) ≤
          lambda *
            lyapunovValue A
              (contrastExcessAtScale hP hStruct
                (memoryGridScale Nstar L (j - 1)))
              (memory (memoryDecay hc L)
                (initialMemory hc.rhoM N Nstar
                  (fun n => contrastExcessAtScale hP hStruct n))
                (memoryGridDrop
                  (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
                (j - 1)) := by
        intro j hj hdelta
        let C_step : ℝ := finalAssemblySourceStepBound hP4 C_lin C_high
        let C_norm : ℝ := 1
        let C_S : ℝ := C_delta / 2
        let C_bad : ℝ := C_delta / 2
        let C_fluct : ℝ := finalAssemblyFluctuationBound hP4 delta_sc
        let C_sqrt : ℝ := 2
        have hKcanKtot_nonneg : 0 ≤ Kcan + Ktot := by
          linarith only [hKcan_nonneg, hKtot_nonneg]
        have hextra_delta_nonneg : 0 ≤ C_stepP * (Kcan + Ktot) :=
          mul_nonneg hC_stepP_nonneg hKcanKtot_nonneg
        have hdeltaParams_nonneg :
            0 ≤ finalAssemblyDeltaBudgetBoundParams params delta_sc C_resp
              C_lin C_high :=
          le_max_left _ _
        have hdelta_lift :
            finalAssemblyDeltaBudgetBoundParams params delta_sc C_resp C_lin
                C_high ≤ C_delta := by
          rw [hC_delta_def]
          refine le_trans ?_ (le_max_right 1 _)
          linarith only [hextra_delta_nonneg]
        have hextra_mem_nonneg :
            0 ≤ C_stepP * (8 * (sharpP * C_resp / c_foldStar)) := by
          have h2 : 0 ≤ sharpP * C_resp / c_foldStar :=
            div_nonneg (mul_nonneg hsharpP_nonneg hC_resp_nonneg)
              (le_of_lt hc_foldStar_pos)
          exact mul_nonneg hC_stepP_nonneg (by linarith only [h2])
        have hmemory_lift :
            finalAssemblyMemoryBudgetBoundParams params C_lin C_high ≤
              C_memory := by
          rw [hC_memory_def]
          linarith only [hextra_mem_nonneg]
        have hmemory_budget :
            6 * finalAssemblySourceStepBound hP4 C_lin C_high ≤ C_memory := by
          rw [finalAssemblySourceStepBound_eq_params hP4 _hparams C_lin C_high]
          refine le_trans ?_ hmemory_lift
          exact le_max_right _ _
        have hfluct_budget :
            2 *
                (finalAssemblySourceStepBound hP4 C_lin C_high *
                  finalAssemblyFluctuationBound hP4 delta_sc) ≤
              C_delta := by
          rw [finalAssemblySourceStepBound_eq_params hP4 _hparams C_lin C_high,
            finalAssemblyFluctuationBound_eq_params hP4 _hparams delta_sc]
          refine le_trans ?_ hdelta_lift
          exact le_max_of_le_right (le_max_left _ _)
        have hresponse_budget :
            finalAssemblySourceStepBound hP4 C_lin C_high *
                (1 + C_resp) * ((1 + (delta_sc / 2)⁻¹) ^ 2) ≤
              C_delta := by
          rw [finalAssemblySourceStepBound_eq_params hP4 _hparams C_lin C_high]
          refine le_trans ?_ hdelta_lift
          exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
        have hbad_budget :
            12 * finalAssemblySourceStepBound hP4 C_lin C_high ≤
              C_delta := by
          rw [finalAssemblySourceStepBound_eq_params hP4 _hparams C_lin C_high]
          refine le_trans ?_ hdelta_lift
          exact le_max_of_le_right
            (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
        have hbad_threshold_budget :
            6 * finalAssemblySourceStepBound hP4 C_lin C_high *
                (1 + (delta_sc / 2)⁻¹) ≤ C_delta := by
          rw [finalAssemblySourceStepBound_eq_params hP4 _hparams C_lin C_high]
          refine le_trans ?_ hdelta_lift
          exact le_max_of_le_right
            (le_max_of_le_right
              (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))
        have hsqrt_budget :
            finalAssemblySourceStepBound hP4 C_lin C_high *
                2 * Real.sqrt (delta_sc / 2)⁻¹ ≤ C_delta := by
          rw [finalAssemblySourceStepBound_eq_params hP4 _hparams C_lin C_high]
          refine le_trans ?_ hdelta_lift
          exact le_max_of_le_right
            (le_max_of_le_right
              (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))))
        have hscalars :=
          final_assembly_source_step_scalars (hP4 := hP4)
            (delta_sc := delta_sc) (C_delta := C_delta)
            (C_memory := C_memory) (C_resp := C_resp) (C_lin := C_lin)
            (C_high := C_high) hmemory_budget hfluct_budget
            hresponse_budget hbad_budget hbad_threshold_budget hsqrt_budget
        dsimp only at hscalars
        rcases hscalars with
          ⟨hC_pos, hC_norm_pos, hC_sqrt_nonneg, hC_S,
            hC_bad, hC_rhoSq, hC_bad_absorb, hC_memory,
            hC_eta, hC_rho, hC_fluct_budget, hbudget_lower,
            hbad_scale_threshold, hbudget_tau, hbudget_sqrt,
            hC_response_le, hfirst_uniform, hC_lin_step, hhigh_avg,
            htau_coeff, hlocal_slots⟩
        let e : Homogenization.Vec d := unitCoordinateVector
        have he : Homogenization.Book.Ch02.vecNorm e = 1 := by
          simpa [e] using (unitCoordinateVector_vecNorm (d := d))
        have hT_initial :
            1 ≤ Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 :=
          one_le_initialWidetildeTheta_of_P4 hP hStruct hP4
        have hNstar_buffer :
            N + Nat.ceil
                (B * Real.logb 3
                  (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) ≤
              memoryGridScale Nstar L j :=
          buffer_bound_le_memoryGridScale_of_nstar_eq (L := L) (i := j) hNstar_eq
        have hNstar_buffer_main :
            N + Nat.ceil
                (B_main * Real.logb 3
                  (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) ≤
              memoryGridScale Nstar L j :=
          nstar_le_of_bufferExponent_le hB_main_le hT_initial hNstar_buffer
        have hcutoff_geo :
            (let β := section53CoarseFluctuationBeta hP4
             (C_osc * C_norm⁻¹) *
                  ((β ^ 2)⁻¹ *
                    Real.rpow (3 : ℝ)
                      (-2 * β * ((((memoryGridScale Nstar L j) -
                        memoryGridScale Nstar L (j - 1) : ℕ) : ℝ))) *
                    contrastExcessAtScale hP hStruct
                      (memoryGridScale Nstar L j)) ≤
                decay *
                  ((1 +
                    contrastExcessAtScale hP hStruct
                      (memoryGridScale Nstar L j)) ^ 2 /
                    contrastExcessAtScale hP hStruct
                      (memoryGridScale Nstar L j))) := by
          let β := section53CoarseFluctuationBeta hP4
          let F_j : ℝ :=
            contrastExcessAtScale hP hStruct (memoryGridScale Nstar L j)
          let T_edge : ℝ := (1 + F_j) ^ 2 / F_j
          let geo : ℝ := Real.rpow (3 : ℝ) (-2 * β * (L : ℝ))
          have hβ_eq :
              β = section53CoarseFluctuationBetaParams params := by
            simpa [β, _hparams] using
              (section53CoarseFluctuationBetaParams_eq_of_P4 hP4).symm
          have hgeo_mk :
              Real.rpow (3 : ℝ)
                  (-2 * β *
                    ((((memoryGridScale Nstar L j) -
                      memoryGridScale Nstar L (j - 1) : ℕ) : ℝ))) =
                geo := by
            have hmk :
                memoryGridScale Nstar L j -
                    memoryGridScale Nstar L (j - 1) = L := by
              exact memoryGridScale_sub_prev_eq (Nstar := Nstar) (L := L)
                (i := j) hj
            simp [geo, hmk]
          have hgeo_le_geo_old :
              geo ≤
                Real.rpow (3 : ℝ)
                  (-2 * β * (L_geo : ℝ)) := by
            have hβ_nonneg : 0 ≤ β := by
              simpa [β] using section53CoarseFluctuationBeta_nonneg hP4
            simpa [geo] using
              section53CoarseFluctuationBeta_twoBlockDecay_le_of_le
                (β := β) (L0 := L_geo) (L := L) hβ_nonneg hL_geo_le
          have hgeo_le_cutoff : geo ≤ cutoffScale := by
            have hgeo_old_le :
                Real.rpow (3 : ℝ) (-2 * β * (L_geo : ℝ)) ≤
                  cutoffScale := by
              simpa [β] using hL_geo hP4 _hparams
            exact hgeo_le_geo_old.trans hgeo_old_le
          have hgeo_nonneg : 0 ≤ geo := by
            change 0 ≤ Real.rpow (3 : ℝ) (-2 * β * (L : ℝ))
            exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
          have hcoef_le_budget :
              (C_osc * C_norm⁻¹) * (β ^ 2)⁻¹ ≤ cutoffBudget := by
            calc
              (C_osc * C_norm⁻¹) * (β ^ 2)⁻¹ =
                  C_osc * betaBudget := by
                    simp [C_norm, hβ_eq, betaBudget]
              _ ≤ cutoffBudget := by
                    dsimp [cutoffBudget]
                    exact (le_max_left _ _).trans (le_max_right _ _)
          have hcoef_nonneg : 0 ≤ (C_osc * C_norm⁻¹) * (β ^ 2)⁻¹ := by
            have hC_norm_inv_nonneg : 0 ≤ C_norm⁻¹ := by
              simp [C_norm]
            exact mul_nonneg
              (mul_nonneg hC_osc_nonneg hC_norm_inv_nonneg)
              (inv_nonneg.mpr (sq_nonneg β))
          have hcoef_geo_le :
              ((C_osc * C_norm⁻¹) * (β ^ 2)⁻¹) * geo ≤ decay := by
            calc
              ((C_osc * C_norm⁻¹) * (β ^ 2)⁻¹) * geo ≤
                  cutoffBudget * cutoffScale := by
                    exact mul_le_mul hcoef_le_budget hgeo_le_cutoff
                      hgeo_nonneg (le_of_lt hcutoffBudget_pos)
              _ = decay := by
                    simp [cutoffScale, div_eq_mul_inv,
                      mul_left_comm, ne_of_gt hcutoffBudget_pos]
          have hF_pos : 0 < F_j := by
            exact lt_of_lt_of_le hdelta_sc_pos (by simpa [F_j] using hdelta)
          have hcutoff_absorb :
              ((C_osc * C_norm⁻¹) * (β ^ 2)⁻¹) * (geo * F_j) ≤
                decay * T_edge :=
            cutoff_contrast_geo_le_decay_terminal_weight hcoef_nonneg
              hcoef_geo_le hgeo_nonneg hF_pos rfl
          calc
            (C_osc * C_norm⁻¹) *
                ((β ^ 2)⁻¹ *
                  Real.rpow (3 : ℝ)
                    (-2 * β *
                      ((((memoryGridScale Nstar L j) -
                        memoryGridScale Nstar L (j - 1) : ℕ) : ℝ))) *
                  contrastExcessAtScale hP hStruct
                    (memoryGridScale Nstar L j)) =
                ((C_osc * C_norm⁻¹) * (β ^ 2)⁻¹) * (geo * F_j) := by
                  rw [hgeo_mk]
                  ring
            _ ≤ decay * T_edge := hcutoff_absorb
        -- grid indices, buffers, roots and budgets for the sharp head
        have hkm : memoryGridScale Nstar L (j - 1) ≤ memoryGridScale Nstar L j :=
          memoryGridScale_le_of_le (Nat.sub_le j 1)
        have hmk_eq :
            memoryGridScale Nstar L j - memoryGridScale Nstar L (j - 1) = L :=
          memoryGridScale_sub_prev_eq (Nstar := Nstar) (L := L) (i := j) hj
        have hmkL :
            memoryGridScale Nstar L j - memoryGridScale Nstar L (j - 1) ≤ L :=
          le_of_eq hmk_eq
        have hNk_grid : N ≤ memoryGridScale Nstar L (j - 1) :=
          hNNstar.trans (Nat.le_add_right Nstar ((j - 1) * L))
        have hNm_grid : N ≤ memoryGridScale Nstar L j := hNk_grid.trans hkm
        have hNstar_union :
            N + Nat.ceil
                (B_union * Real.logb 3
                  (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) ≤
              memoryGridScale Nstar L j :=
          nstar_le_of_bufferExponent_le hB_union_le hT_initial hNstar_buffer
        have hNstar_env :
            N + Nat.ceil
                (B_env * Real.logb 3
                  (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) ≤
              memoryGridScale Nstar L j :=
          nstar_le_of_bufferExponent_le hB_env_le hT_initial hNstar_buffer
        have hNstar_s3 :
            N + Nat.ceil
                (B_s3 * Real.logb 3
                  (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) ≤
              memoryGridScale Nstar L j :=
          nstar_le_of_bufferExponent_le hB_s3_le hT_initial hNstar_buffer
        have hNstar_low :
            N + Nat.ceil
                (B_low * Real.logb 3
                  (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) ≤
              memoryGridScale Nstar L j :=
          nstar_le_of_bufferExponent_le hB_low_le hT_initial hNstar_buffer
        have hNstar_pair :
            N + Nat.ceil
                (B_pair * Real.logb 3
                  (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) ≤
              memoryGridScale Nstar L j :=
          nstar_le_of_bufferExponent_le hB_pair_le hT_initial hNstar_buffer
        have hMsub_meas : AEMeasurable (M_sub (memoryGridScale Nstar L j)) P :=
          (hsub.aestronglyMeasurable hNm_grid).aemeasurable
        have hxi_cast : (hP4.xi : ℝ) = ((params.xi : ℕ) : ℝ) := by
          rw [← _hparams]
          simp
        have hxi_one : (1 : ℝ) ≤ (hP4.xi : ℝ) := by
          have := hP4.two_le_xi
          exact_mod_cast le_trans (by norm_num) this
        have hunion_j := hunion hP hStruct hP4 hNstar_union M_sub hHM hsub
        have hunion_j' :
            (∫⁻ ω, ‖terminalCoarseBlockStochasticMax hP hStruct hc N
                (memoryGridScale Nstar L j)
                (Homogenization.originCube d ((memoryGridScale Nstar L j : ℕ) : ℤ))
                (fun x : Homogenization.CoeffField d => x) ω‖ₑ ^ (2 : ℝ) ∂P) +
              (∫⁻ ω, ‖M_sub (memoryGridScale Nstar L j) ω‖ₑ ^ (2 : ℝ) ∂P) ≤
            ENNReal.ofReal ((etaSrc / 2) ^ (hP4.xi : ℝ)) := by
          rw [hxi_cast]
          exact hunion_j
        obtain ⟨hfin_j, hstochRoot_j⟩ :=
          stochRoot_of_lintegral_le_ofReal_pow hxi_one hetaSrc_pos hunion_j'
        have hpolyRoot_j := henvroot hP hStruct hP4 hNstar_env
        have heps_inv_one : (1 : ℝ) ≤ eps⁻¹ :=
          (one_le_inv₀ heps_pos).mpr heps_le_one
        have hdecay_le : decay ≤ (1 / 4 : ℝ) := by
          have hcoeff_le : coeff ≤ (1 / 4 : ℝ) := by
            linarith only [hsmall]
          have hsum_ge :
              eps⁻¹ * decay ≤
                Real.sqrt rho + eps + eps⁻¹ * (etaS + etaSt + rho + rho ^ 2) +
                  eps⁻¹ * decay := by
            have h1 : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg _
            have h2 : 0 ≤ eps⁻¹ * (etaS + etaSt + rho + rho ^ 2) := by
              have h2a : 0 ≤ eps⁻¹ := le_of_lt (inv_pos.mpr heps_pos)
              have h2b : 0 ≤ etaS + etaSt + rho + rho ^ 2 := by
                linarith only [le_of_lt hetaS_pos, le_of_lt hetaSt_pos,
                  le_of_lt hrho_pos, sq_nonneg rho]
              exact mul_nonneg h2a h2b
            linarith only [h1, h2, le_of_lt heps_pos]
          have hchain :
              C_delta * (eps⁻¹ * decay) ≤ coeff :=
            (mul_le_mul_of_nonneg_left hsum_ge hC_delta_nonneg).trans
              hcoeff_bound
          have hstep1 : decay ≤ eps⁻¹ * decay :=
            le_mul_of_one_le_left (le_of_lt hdecay_pos) heps_inv_one
          have hstep2 : eps⁻¹ * decay ≤ C_delta * (eps⁻¹ * decay) := by
            have hnn : 0 ≤ eps⁻¹ * decay :=
              mul_nonneg (le_of_lt (inv_pos.mpr heps_pos))
                (le_of_lt hdecay_pos)
            exact le_mul_of_one_le_left hnn hC_delta_one
          linarith only [hstep1, hstep2, hchain, hcoeff_le]
        have hF_pos :
            0 < contrastExcessAtScale hP hStruct (memoryGridScale Nstar L j) :=
          lt_of_lt_of_le hdelta_sc_pos hdelta
        have hF_nonneg :
            0 ≤ contrastExcessAtScale hP hStruct (memoryGridScale Nstar L j) :=
          le_of_lt hF_pos
        have hP_km_nonneg :
            0 ≤ terminalPAtScales hP hStruct (memoryGridScale Nstar L (j - 1))
              (memoryGridScale Nstar L j) :=
          terminalPAtScales_nonneg_of_P4 hP hStruct hP4 hkm
        have hRM_nonneg :
            0 ≤ coarseFluctuationResponseMomentAtScale hP hStruct hP4
              (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) e :=
          coarseFluctuationResponseMomentAtScale_nonneg hP hStruct hP4
            (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) e
        have hβ_eq2 :
            section53CoarseFluctuationBeta hP4 =
              section53CoarseFluctuationBetaParams params := by
          simpa [_hparams] using
            (section53CoarseFluctuationBetaParams_eq_of_P4 hP4).symm
        have hgeo_le_cutoff2 :
            Real.rpow (3 : ℝ)
                (-2 * section53CoarseFluctuationBeta hP4 * (L : ℝ)) ≤
              cutoffScale := by
          have hβ_nonneg : 0 ≤ section53CoarseFluctuationBeta hP4 :=
            section53CoarseFluctuationBeta_nonneg hP4
          have h1 :
              Real.rpow (3 : ℝ)
                  (-2 * section53CoarseFluctuationBeta hP4 * (L : ℝ)) ≤
                Real.rpow (3 : ℝ)
                  (-2 * section53CoarseFluctuationBeta hP4 * (L_geo : ℝ)) :=
            section53CoarseFluctuationBeta_twoBlockDecay_le_of_le
              (β := section53CoarseFluctuationBeta hP4) (L0 := L_geo)
              (L := L) hβ_nonneg hL_geo_le
          have h2 :
              Real.rpow (3 : ℝ)
                  (-2 * section53CoarseFluctuationBeta hP4 * (L_geo : ℝ)) ≤
                cutoffScale := by
            simpa [hβ_eq2] using hL_geo hP4 _hparams
          exact h1.trans h2
        have htailFactor_le :
            ((section53CoarseFluctuationBeta hP4) ^ 2)⁻¹ *
                Real.rpow (3 : ℝ)
                  (-2 * section53CoarseFluctuationBeta hP4 *
                    (((memoryGridScale Nstar L j -
                      memoryGridScale Nstar L (j - 1) : ℕ) : ℝ))) ≤
              decay / 2 := by
          rw [hmk_eq]
          have harm : 2 * ((section53CoarseFluctuationBeta hP4) ^ 2)⁻¹ ≤
              cutoffBudget := by
            calc
              2 * ((section53CoarseFluctuationBeta hP4) ^ 2)⁻¹ =
                  2 * betaBudget := by
                    simp [hβ_eq2, betaBudget]
              _ ≤ cutoffBudget := by
                    dsimp [cutoffBudget]
                    exact
                      (le_max_right (2 * C_tail * betaBudget)
                          (2 * betaBudget)).trans
                        ((le_max_right (C_osc * betaBudget)
                            (max (2 * C_tail * betaBudget)
                              (2 * betaBudget))).trans
                          (le_max_right 1
                            (max (C_osc * betaBudget)
                              (max (2 * C_tail * betaBudget)
                                (2 * betaBudget)))))
          have hgeo_nonneg :
              0 ≤ Real.rpow (3 : ℝ)
                (-2 * section53CoarseFluctuationBeta hP4 * (L : ℝ)) :=
            Real.rpow_nonneg (by norm_num) _
          have hstep :
              ((section53CoarseFluctuationBeta hP4) ^ 2)⁻¹ *
                  Real.rpow (3 : ℝ)
                    (-2 * section53CoarseFluctuationBeta hP4 * (L : ℝ)) ≤
                (cutoffBudget / 2) * cutoffScale := by
            have h1 :
                ((section53CoarseFluctuationBeta hP4) ^ 2)⁻¹ ≤
                  cutoffBudget / 2 := by
              linarith only [harm]
            exact mul_le_mul h1 hgeo_le_cutoff2 hgeo_nonneg (by positivity)
          refine hstep.trans (le_of_eq ?_)
          dsimp [cutoffScale]
          field_simp
        have htailFactor_nonneg :
            0 ≤ ((section53CoarseFluctuationBeta hP4) ^ 2)⁻¹ *
                Real.rpow (3 : ℝ)
                  (-2 * section53CoarseFluctuationBeta hP4 *
                    (((memoryGridScale Nstar L j -
                      memoryGridScale Nstar L (j - 1) : ℕ) : ℝ))) :=
          mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
            (Real.rpow_nonneg (by norm_num) _)
        have htailFactor_le_one :
            ((section53CoarseFluctuationBeta hP4) ^ 2)⁻¹ *
                Real.rpow (3 : ℝ)
                  (-2 * section53CoarseFluctuationBeta hP4 *
                    (((memoryGridScale Nstar L j -
                      memoryGridScale Nstar L (j - 1) : ℕ) : ℝ))) ≤ 1 := by
          refine htailFactor_le.trans ?_
          linarith only [hdecay_le]
        -- scalar slot facts
        have hC_eps : C_step ≤ C_delta := by
          have h1 : (1 : ℝ) ≤ 1 + C_resp := by
            dsimp [C_resp]
            norm_num
          have h2 : (1 : ℝ) ≤ (1 + (delta_sc / 2)⁻¹) ^ 2 := by
            have h2a : 0 ≤ (delta_sc / 2)⁻¹ := by
              have h2b : 0 < delta_sc / 2 := by
                linarith only [hdelta_sc_pos]
              exact inv_nonneg.mpr (le_of_lt h2b)
            have ht : (1 : ℝ) ≤ 1 + (delta_sc / 2)⁻¹ := by linarith only [h2a]
            exact one_le_pow₀ ht
          have h3 : 0 ≤ C_step := by
            dsimp [C_step]
            rw [finalAssemblySourceStepBound_eq_params hP4 _hparams C_lin
              C_high, ← hC_stepP_def]
            exact hC_stepP_nonneg
          have hle1 : C_step ≤ C_step * (1 + C_resp) :=
            le_mul_of_one_le_right h3 h1
          have hle2 :
              C_step * (1 + C_resp) ≤
                C_step * (1 + C_resp) * ((1 + (delta_sc / 2)⁻¹) ^ 2) :=
            le_mul_of_one_le_right (mul_nonneg h3 (by linarith only [h1])) h2
          exact (hle1.trans hle2).trans hresponse_budget
        have hC_S_le : C_S ≤ C_delta := by
          dsimp [C_S]
          linarith only [hC_delta_nonneg]
        have hfirst_at_scale :
            specialWeakNormEnergyFirstCoeffAtScale d
                (memoryGridScale Nstar L j) ≤ C_step :=
          (specialWeakNormEnergyFirstCoeffAtScale_le_dimensional
              d (memoryGridScale Nstar L j)).trans hfirst_uniform
        have hRMstar_nonneg : 0 ≤ coarseFluctuationResponseMomentStarAtScale hP hStruct hP4 (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) e :=
          coarseFluctuationResponseMomentStarAtScale_nonneg hP hStruct hP4
            (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) e
        have hWN_eq : localWeakNormScalarWeightAtScales hP hStruct (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) = terminalPAtScales hP hStruct (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) :=
          localWeakNormScalarWeightAtScales_eq_terminalPAtScales_of_P4
            hP hStruct hP4 (memoryGridScale Nstar L (j - 1))
            (memoryGridScale Nstar L j)
        have hδinv_nonneg : 0 ≤ delta_sc⁻¹ :=
          inv_nonneg.mpr (le_of_lt hdelta_sc_pos)
        have hone_add_le :
            1 + contrastExcessAtScale hP hStruct (memoryGridScale Nstar L j) ≤ (1 + delta_sc⁻¹) * contrastExcessAtScale hP hStruct (memoryGridScale Nstar L j) := by
          have hδF : 1 ≤ delta_sc⁻¹ * contrastExcessAtScale hP hStruct (memoryGridScale Nstar L j) := by
            have h1 := mul_le_mul_of_nonneg_left hdelta hδinv_nonneg
            rwa [inv_mul_cancel₀ (ne_of_gt hdelta_sc_pos)] at h1
          have hexp :
              (1 + delta_sc⁻¹) *
                  contrastExcessAtScale hP hStruct (memoryGridScale Nstar L j) =
                contrastExcessAtScale hP hStruct (memoryGridScale Nstar L j) +
                  delta_sc⁻¹ *
                    contrastExcessAtScale hP hStruct
                      (memoryGridScale Nstar L j) := by ring
          linarith only [hδF, hexp]
        have hsmall_le :
            section52SmallTailTerminalResponseBudgetAtScales hP hStruct hP4 (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) e ≤ decay * (terminalPAtScales hP hStruct (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) * coarseFluctuationResponseMomentAtScale hP hStruct hP4 (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) e) := by
          simpa using hs3 hP hStruct hP4 _hparams hNstar_s3 hkm e
        have hcrude := hlow hP hStruct hP4 _hparams hNstar_low
        have hlow_split :
            lowTailSharpBudgetAtScales hP hStruct hP4 hc N (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) (hNNstar.trans (Nat.le_add_right Nstar (j * L))) e etaSrc polyRootBound =
              (5 * (section53CoarseFluctuationBeta hP4)⁻¹) ^ 2 *
                  section52LowTailBelowStartCoeff hP hStruct hP4 N
                    (memoryGridScale Nstar L j) *
                  coarseFluctuationResponseMomentAtScale hP hStruct hP4 (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) e +
                sourceMaxResizedBudgetOfGrid hP hStruct hP4 hc N Nstar L j hNNstar e etaSrc polyRootBound := rfl
        have hcanon_nonneg0 : 0 ≤ decay * ((1 + contrastExcessAtScale hP hStruct (memoryGridScale Nstar L j)) ^ 2 / contrastExcessAtScale hP hStruct (memoryGridScale Nstar L j) + terminalPAtScales hP hStruct (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) * coarseFluctuationResponseMomentAtScale hP hStruct hP4 (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) e) := by
          have h1 : 0 ≤ (1 + contrastExcessAtScale hP hStruct (memoryGridScale Nstar L j)) ^ 2 / contrastExcessAtScale hP hStruct (memoryGridScale Nstar L j) :=
            div_nonneg (sq_nonneg _) hF_nonneg
          have h2 : 0 ≤ terminalPAtScales hP hStruct (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) * coarseFluctuationResponseMomentAtScale hP hStruct hP4 (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) e :=
            mul_nonneg hP_km_nonneg hRM_nonneg
          exact mul_nonneg (le_of_lt hdecay_pos) (by linarith only [h1, h2])
        set childTailB : ℝ := max 0 (((section53CoarseFluctuationBeta hP4) ^ 2)⁻¹ * Real.rpow (3 : ℝ) (-2 * section53CoarseFluctuationBeta hP4 * (((memoryGridScale Nstar L j - memoryGridScale Nstar L (j - 1) : ℕ) : ℝ))) * localWeakNormScalarWeightAtScales hP hStruct (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) * coarseFluctuationResponseMomentAtScale hP hStruct hP4 (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) e + 2 * (((section53CoarseFluctuationBeta hP4) ^ 2)⁻¹ * Real.rpow (3 : ℝ) (-2 * section53CoarseFluctuationBeta hP4 * (((memoryGridScale Nstar L j - memoryGridScale Nstar L (j - 1) : ℕ) : ℝ))) * contrastExcessAtScale hP hStruct (memoryGridScale Nstar L j)) + ((section53CoarseFluctuationBeta hP4) ^ 2)⁻¹ * Real.rpow (3 : ℝ) (-2 * section53CoarseFluctuationBeta hP4 * (((memoryGridScale Nstar L j - memoryGridScale Nstar L (j - 1) : ℕ) : ℝ))) * (section52SmallTailTerminalResponseBudgetAtScales hP hStruct hP4 (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) e + lowTailSharpBudgetAtScales hP hStruct hP4 hc N (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) (hNNstar.trans (Nat.le_add_right Nstar (j * L))) e etaSrc polyRootBound + sourceMaxResizedBudgetOfGrid hP hStruct hP4 hc N Nstar L j hNNstar e etaSrc polyRootBound)) with hchildTB_def
        set tailXB : ℝ := childTailB + section52SmallTailTerminalResponseBudgetAtScales hP hStruct hP4 (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) e + lowTailSharpBudgetAtScales hP hStruct hP4 hc N (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) (hNNstar.trans (Nat.le_add_right Nstar (j * L))) e etaSrc polyRootBound + sourceMaxResizedBudgetOfGrid hP hStruct hP4 hc N Nstar L j hNNstar e etaSrc polyRootBound with htailXB_def
        set lowerEdgeB : ℝ := decay * ((1 + contrastExcessAtScale hP hStruct (memoryGridScale Nstar L j)) ^ 2 / contrastExcessAtScale hP hStruct (memoryGridScale Nstar L j) + terminalPAtScales hP hStruct (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) * coarseFluctuationResponseMomentAtScale hP hStruct hP4 (memoryGridScale Nstar L (j - 1)) (memoryGridScale Nstar L j) e) + max 0 tailXB with hlowerEB_def
        exact
          hstep_main hP hStruct hP4 _hparams (N := N) (Nstar := Nstar) (i := j)
            e (A := A) (K := K) (lambda := lambda) (rho := rho)
            (C := C_step) (C_delta := C_delta) (C_memory := C_memory)
            (C_edgeMem := 0) (C_S := C_S) (C_fluct := C_fluct)
            (C_sqrt := C_sqrt) (C_norm := C_norm) (eps := eps)
            (coeff := coeff) (memoryCoeff := memoryCoeff)
            (edgeMemoryCoeff := edgeMemoryCoeff)
            (lowerEdgeBudget := lowerEdgeB)
            (childTailBudget := childTailB)
            he hj hNNstar M_sub hMsub_meas (stochRoot := etaSrc)
            (polyRoot := polyRootBound) hfin_j hstochRoot_j hpolyRoot_j
            (le_of_lt hlambda_pos) hA_nonneg hK_nonneg hedgeMemoryCoeff_nonneg
            (le_refl 0) hKmem_le hdrop_coeff hdrop_memory_coeff hmemory_coeff
            hC_pos hC_delta_nonneg hC_sqrt_nonneg hC_norm_pos heps_pos
            heps_le_one (le_of_lt hrho_pos) hrho_pos hrho_le_one
            hC_eps hC_S_le hdelta hC_eta hC_rho hC_fluct_budget hbudget_tau
            hbudget_sqrt hC_response_le
            (by
              rw [hlowerEB_def]
              exact add_nonneg hcanon_nonneg0 (le_max_left 0 _))
            (by
              rw [hchildTB_def]
              exact le_max_left 0 _)
            (by
              intro _hno
              dsimp only
              rw [hlowerEB_def]
              exact le_add_of_nonneg_right (le_max_left 0 _))
            hfirst_at_scale hC_lin_step hhigh_avg htau_coeff hlocal_slots
            hcutoff_geo
            (by
              dsimp only
              rw [hchildTB_def]
              exact le_max_right 0 _)
            (by
              dsimp only
              rw [← htailXB_def, hlowerEB_def]
              exact (le_max_right 0 tailXB).trans
                (le_add_of_nonneg_left hcanon_nonneg0))
            (by
              intro hno
              dsimp only
              have hpair_j :=
                hpair hP hStruct hP4 e he hrho_pos hrho_le_one hNk_grid hkm
                  hmkL hno hNstar_pair hHM
              have hone_le_P :
                  (1 : ℝ) ≤ terminalPAtScales hP hStruct
                    (memoryGridScale Nstar L (j - 1))
                    (memoryGridScale Nstar L j) := by
                have hs :=
                  sqrt_one_add_contrastExcessAtScale_le_terminalPAtScales_of_P4
                    hP hStruct hP4 hkm
                calc
                  (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
                  _ ≤ Real.sqrt (1 + contrastExcessAtScale hP hStruct (memoryGridScale Nstar L j)) :=
                    Real.sqrt_le_sqrt (by linarith only [hF_nonneg])
                  _ ≤ terminalPAtScales hP hStruct
                      (memoryGridScale Nstar L (j - 1))
                      (memoryGridScale Nstar L j) := hs
              have hsharp_eq :
                  sourceMaxSharpConst hP4 hc =
                    sourceMaxSharpConstParams params hc :=
                sourceMaxSharpConst_eq_params hP4 _hparams hc
              have hdecay_LG :
                  sourceMaxSharpConst hP4 hc * C_resp *
                      (etaSrc + polyRootBound + 2 * rho + c_fold) ≤ decay := by
                rw [hsharp_eq]
                have hX_nonneg :
                    0 ≤ etaSrc + polyRootBound + 2 * rho + c_fold := by
                  linarith only [le_of_lt hetaSrc_pos,
                    le_of_lt hpolyRootBound_pos, le_of_lt hrho_pos,
                    le_of_lt hc_fold_pos]
                have hCsrc : C_src = 2 * sharpP * C_resp := hC_src_def
                have hle_sharpP :
                    sourceMaxSharpConstParams params hc ≤ sharpP := by
                  rw [hsharpP_def]
                  exact le_max_right 0 _
                have hchain1 :
                    sourceMaxSharpConstParams params hc * C_resp *
                        (etaSrc + polyRootBound + 2 * rho + c_fold) ≤
                      sharpP * C_resp *
                        (etaSrc + polyRootBound + 2 * rho + c_fold) :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hle_sharpP hC_resp_nonneg)
                    hX_nonneg
                have htwice :
                    2 * (sharpP * C_resp *
                        (etaSrc + polyRootBound + 2 * rho + c_fold)) =
                      C_src * (etaSrc + polyRootBound + 2 * rho + c_fold) := by
                  rw [hCsrc]
                  ring
                have hhalf_nonneg :
                    0 ≤ sharpP * C_resp *
                      (etaSrc + polyRootBound + 2 * rho + c_fold) :=
                  mul_nonneg (mul_nonneg hsharpP_nonneg hC_resp_nonneg)
                    hX_nonneg
                have hchain2 :
                    sharpP * C_resp *
                        (etaSrc + polyRootBound + 2 * rho + c_fold) ≤ decay := by
                  linarith only [hsrc_pay, htwice, hhalf_nonneg]
                exact hchain1.trans hchain2
              have hsrc_le :=
                sourceMaxResizedBudgetOfGrid_le_canonicalLowerTailBudget_add_memory_of_grid_noDrop
                  hP hStruct hP4 hc hP4_hc (N := N) (Nstar := Nstar) (L := L) (i := j)
                  hj hNNstar e (le_of_lt hrho_pos) (le_of_lt hetaSrc_pos)
                  (le_of_lt hpolyRootBound_pos) le_rfl le_rfl hC_resp_nonneg
                  hc_fold_pos hF_pos hno hpair_j hdecay_LG
              have hsrcCanon_eq :
                  sourceMaxCanonicalLowerTailBudgetOfGrid hP hStruct hP4
                      Nstar L j e decay =
                    decay * ((1 + contrastExcessAtScale hP hStruct (memoryGridScale Nstar L j)) ^ 2 / contrastExcessAtScale hP hStruct (memoryGridScale Nstar L j) +
                      terminalPAtScales hP hStruct
                          (memoryGridScale Nstar L (j - 1))
                          (memoryGridScale Nstar L j) *
                        coarseFluctuationResponseMomentAtScale hP hStruct hP4
                          (memoryGridScale Nstar L (j - 1))
                          (memoryGridScale Nstar L j) e) := rfl
              rw [hsrcCanon_eq] at hsrc_le
              have hMT_nonneg :
                  0 ≤ sourceMaxMemoryTermOfGrid hP hStruct hc N Nstar L j := by
                dsimp [sourceMaxMemoryTermOfGrid]
                exact div_nonneg (sq_nonneg _) (by linarith only [hF_nonneg])
              have hKfold_le :
                  sourceMaxSharpConst hP4 hc * C_resp / c_fold ≤
                    sharpP * C_resp / c_foldStar := by
                rw [hsharp_eq]
                have hnum_le :
                    sourceMaxSharpConstParams params hc * C_resp ≤
                      sharpP * C_resp := by
                  refine mul_le_mul_of_nonneg_right ?_ hC_resp_nonneg
                  rw [hsharpP_def]
                  exact le_max_right 0 _
                have hnum_nonneg : 0 ≤ sharpP * C_resp :=
                  mul_nonneg hsharpP_nonneg hC_resp_nonneg
                have hfold_ge : c_foldStar ≤ c_fold := by
                  rw [hc_foldStar_def]
                  exact hc_fold_ge
                rw [div_le_div_iff₀ hc_fold_pos hc_foldStar_pos]
                exact mul_le_mul hnum_le hfold_ge
                  (le_of_lt hc_foldStar_pos) hnum_nonneg
              have hKFS_nonneg : 0 ≤ sharpP * C_resp / c_foldStar :=
                div_nonneg (mul_nonneg hsharpP_nonneg hC_resp_nonneg)
                  (le_of_lt hc_foldStar_pos)
              have hCstep_nonneg : 0 ≤ C_step := by
                dsimp [C_step]
                rw [finalAssemblySourceStepBound_eq_params hP4 _hparams
                  C_lin C_high, ← hC_stepP_def]
                exact hC_stepP_nonneg
              have hsize_delta :
                  C_step *
                      ((1 + delta_sc⁻¹) ^ 2 + C_resp * (1 + delta_sc⁻¹) +
                        (1 + 8 * (C_resp * (1 + delta_sc⁻¹) +
                          ((1 + delta_sc⁻¹) ^ 2 +
                            C_resp * (1 + delta_sc⁻¹))))) ≤ C_delta := by
                dsimp [C_step]
                rw [finalAssemblySourceStepBound_eq_params hP4 _hparams
                  C_lin C_high]
                rw [← hC_stepP_def, hC_delta_def]
                refine le_trans ?_ (le_max_right 1 _)
                have hKK :
                    (1 + delta_sc⁻¹) ^ 2 + C_resp * (1 + delta_sc⁻¹) +
                        (1 + 8 * (C_resp * (1 + delta_sc⁻¹) +
                          ((1 + delta_sc⁻¹) ^ 2 +
                            C_resp * (1 + delta_sc⁻¹)))) = Kcan + Ktot := by
                  rw [hKtot_def, hKcan_def]
                rw [hKK]
                linarith only [hdeltaParams_nonneg]
              have hsize_mem :
                  C_step * (8 * (sharpP * C_resp / c_foldStar)) ≤ C_memory := by
                dsimp [C_step]
                rw [finalAssemblySourceStepBound_eq_params hP4 _hparams
                  C_lin C_high]
                rw [← hC_stepP_def, hC_memory_def]
                have hparamsMem_nonneg :
                    0 ≤ finalAssemblyMemoryBudgetBoundParams params C_lin
                      C_high :=
                  le_max_left _ _
                linarith only [hparamsMem_nonneg]
              rw [hlowerEB_def, htailXB_def, hchildTB_def]
              refine le_trans
                (sharp_lowerEdge_budget_payment hF_pos hdelta_sc_pos
                  hdecay_pos hdecay_le heps_pos hC_resp_nonneg hc_fold_pos
                  hpair_j hone_le_P hP_km_nonneg hRM_nonneg hRMstar_nonneg
                  hWN_eq htailFactor_le htailFactor_nonneg hdelta hsmall_le
                  hcrude hlow_split hsrc_le hMT_nonneg hKfold_le hKFS_nonneg
                  rfl rfl hCstep_nonneg hsize_delta hsize_mem)
                (le_of_eq ?_)
              dsimp [sourceMaxMemoryTermOfGrid]
              ring)
            hNstar_buffer_main hHM
            hcoeff_bound hmemoryCoeff hedgeMemCoeff_le hsmall
  let F : ℕ → ℝ := fun j =>
    contrastExcessAtScale hP hStruct (memoryGridScale Nstar L j)
  let H : ℕ → ℝ := fun j =>
    memory (memoryDecay hc L)
      (initialMemory hc.rhoM N Nstar
        (fun n => contrastExcessAtScale hP hStruct n))
      (memoryGridDrop
        (fun n => contrastExcessAtScale hP hStruct n) Nstar L) j
  have hstep_one_based' :
      ∀ j, 1 ≤ j →
        delta_sc ≤ F j →
        lyapunovValue A (F j) (H j) ≤
          lambda * lyapunovValue A (F (j - 1)) (H (j - 1)) := by
    intro j hj hdelta
    simpa [F, H] using hstep_one_based j hj hdelta
  have hstep_if_above :
      ∀ i < I,
        delta_sc < F (i + 1) →
        lyapunovValue A (F (i + 1)) (H (i + 1)) ≤
          lambda * lyapunovValue A (F i) (H i) :=
    lyapunov_step_if_above_of_one_based_step
      (F := F) (H := H) (A := A) (lambda := lambda)
      (delta_sc := delta_sc) (I := I) hstep_one_based'
  obtain ⟨hentry_theta, hentry_log⟩ :=
    hentry hP hStruct hP4 hN_eq hNstar_eq hI_eq hNNstar hA_nonneg hC_A
      (by
        intro i hi hdelta
        simpa [F, H] using hstep_if_above i hi hdelta)
  exact hfinal_entry hP hStruct hP4 hP4_hc hentry_theta hentry_log

end Homogenization.HighContrast.EntryScale
