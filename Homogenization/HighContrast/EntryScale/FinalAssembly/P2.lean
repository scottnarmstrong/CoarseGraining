import Mathlib.Tactic.Positivity
import Homogenization.HighContrast.EntryScale.LowerEdgeKernel
import Homogenization.HighContrast.EntryScale.RawHighContrastEnergy.P3

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization.Book.Ch05.Section54.OneStepContraction
open scoped Matrix.Norms.Elementwise

namespace Homogenization.HighContrast.EntryScale

/--
Source labels `e.W.low.tail` and `a.HM` (buffer): the below-start crude
low-tail coefficient is buffer-small.  Every summand at a scale `n < N` is
collapsed onto the weight `3^{-β(m-n)}`: the descendant-card roots contribute
at most `3^{(d/ξ)(m-n)}` (the scale-`n` card factors cancel), the paired
`σ`-moment factors are bounded by `2·θ̃₀`, and the scale-zero gaps by `θ̃₀²`;
since `d/ξ + β ≤ s' ≤ t'`, the restricted sum decays like
`θ̃₀²·3^{-β(m-N)}`, which the `Nstar` buffer drives below any target.
-/
theorem exists_bufferExponent_lowTailBelowStartCoeff_le_eta_of_Nstar
    {d : ℕ} [NeZero d]
    (params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
        (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
        (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P),
        hP4.params = params →
        ∀ {N m : ℕ},
          N + Nat.ceil
              (B * Real.logb 3
                (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) ≤
            m →
          (5 * (section53CoarseFluctuationBeta hP4)⁻¹) ^ 2 *
              section52LowTailBelowStartCoeff hP hStruct hP4 N m ≤ eta := by
  classical
  let βp : ℝ := section53CoarseFluctuationBetaParams params
  have hβp_pos : 0 < βp := by
    dsimp [βp]
    exact
      Homogenization.Book.Ch05.Section51.section53CoarseFluctuationBetaParams_pos
        params
  let CRp : ℝ :=
    Homogenization.Book.Ch04.rosenthalDescendantsAtScaleLpConst d 0 params.xi +
      Homogenization.Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 params.xi
  have hCRp_nonneg : 0 ≤ CRp := by
    dsimp [CRp]
    unfold Homogenization.Book.Ch04.rosenthalDescendantsAtScaleLpConst
      Homogenization.Book.Ch04.rosenthalDescendantsAtScaleSqrtConst
      Homogenization.Book.Ch04.rosenthalBennettIntegralConst
      Homogenization.IndependentSums.rosenthalBennettIntegralConst
    positivity
  let discp : ℝ := Homogenization.geometricDiscount βp 1
  have hdiscp_pos : 0 < discp := by
    dsimp [discp]
    exact Homogenization.geometricDiscount_pos
      (by linarith only [hβp_pos] : (0 : ℝ) < βp * 1)
  let dim2p : ℝ := (Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)
  have hdim2p_nonneg : 0 ≤ dim2p := by
    dsimp [dim2p]
    positivity
  let Cp : ℝ := (5 * βp⁻¹) ^ 2 * ((8 * dim2p * CRp + 2) * discp⁻¹)
  have hCp_nonneg : 0 ≤ Cp := by
    dsimp [Cp]
    have h1 : 0 ≤ discp⁻¹ := inv_nonneg.mpr (le_of_lt hdiscp_pos)
    positivity
  obtain ⟨B, hB_one, hB⟩ :=
    exists_bufferExponent_for_polynomial_geometric_envelope_no_linear_le
      (C := Cp) (A := 2) (c := βp) (η := eta) hCp_nonneg hβp_pos heta
  refine ⟨B, hB_one, ?_⟩
  intro P hP hStruct hP4 hparams N m hNstar
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let T : ℝ := Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4
  let L0 : ℝ :=
    Homogenization.Book.Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi
  let l0 : ℝ :=
    Homogenization.Book.Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi
  let CR : ℝ := Homogenization.Book.Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi + Homogenization.Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi
  let disc : ℝ := Homogenization.geometricDiscount β 1
  let dim2 : ℝ := (Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)
  have hβ_eq : β = βp := by
    dsimp [β, βp]
    simpa only [hparams] using
      (section53CoarseFluctuationBetaParams_eq_of_P4 hP4).symm
  have hβ_pos : 0 < β := by
    rw [hβ_eq]; exact hβp_pos
  have hξ_eq : hP4.xi = params.xi := by
    rw [← hparams]
    simp only [Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity.params_xi]
  have hCR_eq : CR = CRp := by
    dsimp [CR, CRp]
    rw [hξ_eq]
  have hdisc_eq : disc = discp := by
    dsimp [disc, discp]
    rw [hβ_eq]
  have hdisc_pos : 0 < disc := by
    rw [hdisc_eq]; exact hdiscp_pos
  have hCR_nonneg : 0 ≤ CR := by
    rw [hCR_eq]; exact hCRp_nonneg
  have hdim2_eq : dim2 = dim2p := rfl
  have hdim2_nonneg : 0 ≤ dim2 := by
    dsimp [dim2]
    positivity
  have hT_one : 1 ≤ T := by
    simpa only [T] using one_le_initialWidetildeTheta_of_P4 hP hStruct hP4
  have hT_nonneg : 0 ≤ T := by linarith only [hT_one]
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, Homogenization.Book.Ch05.sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hL0_nonneg : 0 ≤ L0 := by
    simpa only [L0] using
      Homogenization.Book.Ch04.LambdaMomentAtScale_nonneg P 0 hP4.xi
        hP4.sUpper_pos
  have hl0_nonneg : 0 ≤ l0 := by
    simpa only [l0] using
      Homogenization.Book.Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi
        hP4.sLower_pos
  have hpair :=
    coarseFluctuationUnitMomentWeightAtScale_le_two_widetildeTheta_zero
      hP hStruct hP4 m
  have hpair' : σ * l0 + σ⁻¹ * L0 ≤ 2 * T := by
    simpa only [coarseFluctuationUnitMomentWeightAtScale, σ, l0, L0, T] using hpair
  have hσl0_le : σ * l0 ≤ 2 * T := by
    have h2 : 0 ≤ σ⁻¹ * L0 :=
      mul_nonneg (inv_nonneg.mpr hσ_nonneg) hL0_nonneg
    linarith only [hpair', h2]
  have hσL0_le : σ⁻¹ * L0 ≤ 2 * T := by
    have h1 : 0 ≤ σ * l0 := mul_nonneg hσ_nonneg hl0_nonneg
    linarith only [hpair', h1]
  have hbm_pos : 0 < hP.barSigmaAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 m
  have hcm_pos : 0 < hP.barSigmaStarAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 m
  have hb0_pos : 0 < hP.barSigmaAtScale hStruct (0 : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 0
  have hc0_pos : 0 < hP.barSigmaStarAtScale hStruct (0 : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 0
  have hσ_eq : σ = Real.sqrt (hP.barSigmaAtScale hStruct (m : ℤ) * hP.barSigmaStarAtScale hStruct (m : ℤ)) := rfl
  have hθ_eq :
      Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ) =
        hP.barSigmaAtScale hStruct (m : ℤ) * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ := rfl
  have hσ_star :
      σ * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ =
        Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) :=
    Homogenization.Book.Ch05.Section54.GoodScale.sigma_mul_inv_star_eq_sqrt_theta
      hbm_pos hcm_pos hσ_eq hθ_eq
  have hσ_bar :
      hP.barSigmaAtScale hStruct (m : ℤ) * σ⁻¹ =
        Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) :=
    Homogenization.Book.Ch05.Section54.GoodScale.barSigma_mul_inv_sigma_eq_sqrt_theta
      hbm_pos hcm_pos hσ_eq hθ_eq
  have hθ_le_T :
      Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ) ≤ T := by
    simpa only [T] using thetaAtScale_le_initialWidetildeTheta_of_P4 hP hStruct hP4 m
  have hsqrtθ_le_T :
      Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) ≤
        T := by
    calc
      Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) ≤
          Real.sqrt T := Real.sqrt_le_sqrt hθ_le_T
      _ ≤ Real.sqrt (T ^ 2) :=
        Real.sqrt_le_sqrt
          (by linarith only [sq_nonneg (T - 1), hT_one] : T ≤ T ^ 2)
      _ = T := Real.sqrt_sq (by linarith only [hT_one])
  have hratio_star : (hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ / (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ ≤ T := by
    simpa only [T] using
      terminalInvStarScalarRatio_le_initialWidetildeTheta_of_P4
        hP hStruct hP4 (Nat.zero_le m)
  have hratio_bar : hP.barSigmaAtScale hStruct (0 : ℤ) / hP.barSigmaAtScale hStruct (m : ℤ) ≤ T := by
    simpa only [T] using
      terminalUpperScalarRatio_le_initialWidetildeTheta_of_P4
        hP hStruct hP4 (Nat.zero_le m)
  have hgap_lower : σ * ((hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ - (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) ≤ T * T := by
    have hgap_le : (hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ - (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ ≤ (hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ := by
      have : 0 ≤ (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ := inv_nonneg.mpr (le_of_lt hcm_pos)
      linarith only [this]
    have hchain : σ * (hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ ≤ T * T := by
      have hdecomp :
          σ * (hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ =
            ((hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ / (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) * (σ * (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) := by
        have hcm_inv_ne : (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ ≠ 0 := ne_of_gt (inv_pos.mpr hcm_pos)
        field_simp
      rw [hdecomp, hσ_star]
      have hsq_nonneg :
          0 ≤ Real.sqrt
            (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) :=
        Real.sqrt_nonneg _
      calc
        ((hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ / (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) *
          Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) ≤
            T * Real.sqrt
              (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) :=
          mul_le_mul_of_nonneg_right hratio_star hsq_nonneg
        _ ≤ T * T := mul_le_mul_of_nonneg_left hsqrtθ_le_T hT_nonneg
    calc
      σ * ((hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ - (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) ≤ σ * (hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ :=
        mul_le_mul_of_nonneg_left hgap_le hσ_nonneg
      _ ≤ T * T := hchain
  have hgap_upper : σ⁻¹ * (hP.barSigmaAtScale hStruct (0 : ℤ) - hP.barSigmaAtScale hStruct (m : ℤ)) ≤ T * T := by
    have hgap_le : hP.barSigmaAtScale hStruct (0 : ℤ) - hP.barSigmaAtScale hStruct (m : ℤ) ≤ hP.barSigmaAtScale hStruct (0 : ℤ) := by
      linarith only [hbm_pos]
    have hchain : σ⁻¹ * hP.barSigmaAtScale hStruct (0 : ℤ) ≤ T * T := by
      have hdecomp :
          σ⁻¹ * hP.barSigmaAtScale hStruct (0 : ℤ) = (hP.barSigmaAtScale hStruct (0 : ℤ) / hP.barSigmaAtScale hStruct (m : ℤ)) * (hP.barSigmaAtScale hStruct (m : ℤ) * σ⁻¹) := by
        field_simp
      rw [hdecomp, hσ_bar]
      have hsq_nonneg :
          0 ≤ Real.sqrt
            (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) :=
        Real.sqrt_nonneg _
      calc
        (hP.barSigmaAtScale hStruct (0 : ℤ) / hP.barSigmaAtScale hStruct (m : ℤ)) *
          Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) ≤
            T * Real.sqrt
              (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) :=
          mul_le_mul_of_nonneg_right hratio_bar hsq_nonneg
        _ ≤ T * T := mul_le_mul_of_nonneg_left hsqrtθ_le_T hT_nonneg
    calc
      σ⁻¹ * (hP.barSigmaAtScale hStruct (0 : ℤ) - hP.barSigmaAtScale hStruct (m : ℤ)) ≤ σ⁻¹ * hP.barSigmaAtScale hStruct (0 : ℤ) :=
        mul_le_mul_of_nonneg_left hgap_le (inv_nonneg.mpr hσ_nonneg)
      _ ≤ T * T := hchain
  have hs'_pos : 0 < s' := by
    have := hP4.sLower_nonneg
    dsimp [s']
    linarith only [this, hβ_pos]
  have ht'_pos : 0 < t' := by
    have := hP4.sUpper_nonneg
    dsimp [t']
    linarith only [this, hβ_pos]
  have hd_div_lt_sL : (d : ℝ) / (hP4.xi : ℝ) < hP4.sLower :=
    hP4.dim_div_xi_lt_sLower
  have hd_div_lt_sU : (d : ℝ) / (hP4.xi : ℝ) < hP4.sUpper :=
    hP4.dim_div_xi_lt_sUpper
  have hgap_s' : β + (d : ℝ) / (hP4.xi : ℝ) ≤ s' := by
    dsimp [s']
    linarith only [hd_div_lt_sL]
  have hgap_t' : β + (d : ℝ) / (hP4.xi : ℝ) ≤ t' := by
    dsimp [t']
    linarith only [hd_div_lt_sU]
  -- collapse of any weight (exponent ≥ β + d/ξ) times the card-root growth
  have hweight_collapse :
      ∀ (sx : ℝ), 0 ≤ sx → β + (d : ℝ) / (hP4.xi : ℝ) ≤ sx →
      ∀ n : {n : ℤ // n ∈ S},
        Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sx m n.1 * Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (Int.toNat ((m : ℤ) - n.1) : ℝ)) ≤ disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1 := by
    intro sx hsx_nonneg hgap n
    set j : ℕ := Int.toNat ((m : ℤ) - n.1) with hj_def
    have hweight_val :
        Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sx m n.1 =
          Homogenization.geometricDiscount sx 1 *
            Real.rpow (3 : ℝ) (-(sx * 1) * (j : ℝ)) := by
      simp only [Homogenization.Book.Ch05.Section52.section52LargeScaleWeight,
        Homogenization.geometricWeight, Homogenization.geometricDiscount_one_eq,
        Real.rpow_eq_pow, mul_one, neg_mul, hj_def]
    have hweightβ_val :
        Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1 =
          Homogenization.geometricDiscount β 1 *
            Real.rpow (3 : ℝ) (-(β * 1) * (j : ℝ)) := by
      simp only [Homogenization.Book.Ch05.Section52.section52LargeScaleWeight,
        Homogenization.geometricWeight, Homogenization.geometricDiscount_one_eq,
        Real.rpow_eq_pow, mul_one, neg_mul, hj_def]
    have hdisc_le_one : Homogenization.geometricDiscount sx 1 ≤ 1 := by
      unfold Homogenization.geometricDiscount
      have : 0 ≤ Real.rpow (3 : ℝ) (-sx * 1) :=
        Real.rpow_nonneg (by norm_num) _
      linarith only [this]
    have hexp_col :
        Real.rpow (3 : ℝ) (-(sx * 1) * (j : ℝ)) *
          Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (j : ℝ)) ≤
        Real.rpow (3 : ℝ) (-(β * 1) * (j : ℝ)) := by
      have hadd :
          Real.rpow (3 : ℝ) (-(sx * 1) * (j : ℝ)) *
              Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (j : ℝ)) =
            Real.rpow (3 : ℝ)
              (-(sx * 1) * (j : ℝ) + ((d : ℝ) / (hP4.xi : ℝ)) * (j : ℝ)) :=
        (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
      rw [hadd]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hj_nonneg : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have hgap' : (0 : ℝ) ≤ sx - β - (d : ℝ) / (hP4.xi : ℝ) := by
        linarith only [hgap]
      linarith only [mul_nonneg hgap' hj_nonneg]
    have hrpowβ_eq :
        Real.rpow (3 : ℝ) (-(β * 1) * (j : ℝ)) =
          disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1 := by
      rw [hweightβ_val]
      dsimp [disc]
      field_simp [ne_of_gt hdisc_pos]
      exact (div_self (ne_of_gt hdisc_pos)).symm
    calc
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sx m n.1 * Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (Int.toNat ((m : ℤ) - n.1) : ℝ)) =
        Homogenization.geometricDiscount sx 1 *
          (Real.rpow (3 : ℝ) (-(sx * 1) * (j : ℝ)) *
            Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (j : ℝ))) := by
        rw [hweight_val, hj_def]
        ring
      _ ≤ 1 * (Real.rpow (3 : ℝ) (-(sx * 1) * (j : ℝ)) *
          Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (j : ℝ))) := by
        refine mul_le_mul_of_nonneg_right hdisc_le_one ?_
        exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg (by norm_num) _)
      _ = Real.rpow (3 : ℝ) (-(sx * 1) * (j : ℝ)) *
          Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (j : ℝ)) := by
        ring
      _ ≤ Real.rpow (3 : ℝ) (-(β * 1) * (j : ℝ)) := hexp_col
      _ = disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1 := hrpowβ_eq
  -- plain weight domination (no growth factor)
  have hweight_dom :
      ∀ (sx : ℝ), 0 ≤ sx → β ≤ sx →
      ∀ n : {n : ℤ // n ∈ S},
        Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sx m n.1 ≤ disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1 := by
    intro sx hsx_nonneg hβsx n
    set j : ℕ := Int.toNat ((m : ℤ) - n.1) with hj_def
    have hweight_val :
        Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sx m n.1 =
          Homogenization.geometricDiscount sx 1 *
            Real.rpow (3 : ℝ) (-(sx * 1) * (j : ℝ)) := by
      simp only [Homogenization.Book.Ch05.Section52.section52LargeScaleWeight,
        Homogenization.geometricWeight, Homogenization.geometricDiscount_one_eq,
        Real.rpow_eq_pow, mul_one, neg_mul, hj_def]
    have hweightβ_val :
        Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1 =
          Homogenization.geometricDiscount β 1 *
            Real.rpow (3 : ℝ) (-(β * 1) * (j : ℝ)) := by
      simp only [Homogenization.Book.Ch05.Section52.section52LargeScaleWeight,
        Homogenization.geometricWeight, Homogenization.geometricDiscount_one_eq,
        Real.rpow_eq_pow, mul_one, neg_mul, hj_def]
    have hdisc_le_one : Homogenization.geometricDiscount sx 1 ≤ 1 := by
      unfold Homogenization.geometricDiscount
      have : 0 ≤ Real.rpow (3 : ℝ) (-sx * 1) :=
        Real.rpow_nonneg (by norm_num) _
      linarith only [this]
    have hexp_col :
        Real.rpow (3 : ℝ) (-(sx * 1) * (j : ℝ)) ≤
          Real.rpow (3 : ℝ) (-(β * 1) * (j : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hj_nonneg : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have hβsx' : (0 : ℝ) ≤ sx - β := by
        linarith only [hβsx]
      linarith only [mul_nonneg hβsx' hj_nonneg]
    have hrpowβ_eq :
        Real.rpow (3 : ℝ) (-(β * 1) * (j : ℝ)) =
          disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1 := by
      rw [hweightβ_val]
      dsimp [disc]
      field_simp [ne_of_gt hdisc_pos]
      exact (div_self (ne_of_gt hdisc_pos)).symm
    calc
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sx m n.1 =
        Homogenization.geometricDiscount sx 1 *
          Real.rpow (3 : ℝ) (-(sx * 1) * (j : ℝ)) := hweight_val
      _ ≤ 1 * Real.rpow (3 : ℝ) (-(sx * 1) * (j : ℝ)) :=
        mul_le_mul_of_nonneg_right hdisc_le_one
          (Real.rpow_nonneg (by norm_num) _)
      _ = Real.rpow (3 : ℝ) (-(sx * 1) * (j : ℝ)) := by ring
      _ ≤ Real.rpow (3 : ℝ) (-(β * 1) * (j : ℝ)) := hexp_col
      _ = disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1 := hrpowβ_eq
  -- per-scale root-coefficient collapse
  have hrootC :
      ∀ (sx : ℝ), 0 ≤ sx → β + (d : ℝ) / (hP4.xi : ℝ) ≤ sx →
      ∀ n : {n : ℤ // n ∈ S},
        Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi sx m n.1 ≤
          2 * CR * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1) := by
    intro sx hsx_nonneg hgap n
    have hn_nonneg : 0 ≤ n.1 :=
      Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_nonneg n.2
    have hn_le : n.1 ≤ (m : ℤ) :=
      Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2
    have hcardM :
        (((Homogenization.descendantsAtScale (Homogenization.originCube d (m : ℤ)) n.1).card : ℝ) ^ (1 / (hP4.xi : ℝ))) = Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (Int.toNat ((m : ℤ) - n.1) : ℝ)) := by
      simpa only [one_div, Real.rpow_eq_pow] using
        Homogenization.Book.Ch05.Section52.section52_descendantsAtScale_originCube_large_card_rpow
          d hP4.xi m hn_le
    have hcardN_one_le : (1 : ℝ) ≤ ((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) := by
      have hne :
          (Homogenization.descendantsAtScale
            (Homogenization.originCube d n.1) 0).Nonempty := by
        refine Homogenization.descendantsAtScale_nonempty _ ?_
        simpa only [Homogenization.originCube] using hn_nonneg
      have hpos := Finset.card_pos.mpr hne
      exact_mod_cast hpos
    have hcardN_pos : (0 : ℝ) < ((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) := by linarith only [hcardN_one_le]
    have hxi_one_le : (1 : ℝ) ≤ (hP4.xi : ℝ) := by
      have := hP4.two_le_xi
      exact_mod_cast le_trans (by norm_num) this
    have hxi_pos : (0 : ℝ) < (hP4.xi : ℝ) := by linarith only [hxi_one_le]
    have hLp_ratio :
        (((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ))⁻¹ * (((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) ^ (1 / (hP4.xi : ℝ))) ≤ 1 := by
      have hx_ne : ((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) ≠ 0 := ne_of_gt hcardN_pos
      have hpow_le : ((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) ^ (1 / (hP4.xi : ℝ)) ≤ ((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) := by
        calc
          ((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) ^ (1 / (hP4.xi : ℝ)) ≤ ((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) ^ (1 : ℝ) := by
            refine Real.rpow_le_rpow_of_exponent_le hcardN_one_le ?_
            rw [div_le_one hxi_pos]
            exact hxi_one_le
          _ = ((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) := Real.rpow_one _
      calc
        (((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ))⁻¹ * (((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) ^ (1 / (hP4.xi : ℝ))) ≤
            (((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ))⁻¹ * ((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) :=
          mul_le_mul_of_nonneg_left hpow_le
            (inv_nonneg.mpr (le_of_lt hcardN_pos))
        _ = 1 := inv_mul_cancel₀ hx_ne
    have hSqrt_ratio :
        (((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ))⁻¹ * Real.sqrt ((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) ≤ 1 := by
      have hx_ne : ((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) ≠ 0 := ne_of_gt hcardN_pos
      have hsqrt_le : Real.sqrt ((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) ≤ ((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) := by
        calc
          Real.sqrt ((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) ≤
              Real.sqrt (((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) ^ 2) :=
            Real.sqrt_le_sqrt
              (by
                linarith only
                  [sq_nonneg
                    (((Homogenization.descendantsAtScale
                      (Homogenization.originCube d n.1) 0).card : ℝ) - 1),
                  hcardN_one_le])
          _ = ((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) :=
            Real.sqrt_sq (by linarith only [hcardN_one_le])
      calc
        (((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ))⁻¹ * Real.sqrt ((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) ≤ (((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ))⁻¹ * ((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) :=
          mul_le_mul_of_nonneg_left hsqrt_le
            (inv_nonneg.mpr (le_of_lt hcardN_pos))
        _ = 1 := inv_mul_cancel₀ hx_ne
    have hCLp_nonneg : 0 ≤ Homogenization.Book.Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi := by
      unfold Homogenization.Book.Ch04.rosenthalDescendantsAtScaleLpConst
      positivity
    have hCSqrt_nonneg : 0 ≤ Homogenization.Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi := by
      unfold Homogenization.Book.Ch04.rosenthalDescendantsAtScaleSqrtConst
        Homogenization.Book.Ch04.rosenthalBennettIntegralConst
        Homogenization.IndependentSums.rosenthalBennettIntegralConst
      positivity
    have hweight_nonneg : 0 ≤ Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sx m n.1 :=
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight_nonneg
        m hsx_nonneg n.1
    have hcollapse := hweight_collapse sx hsx_nonneg hgap n
    have hwr_nonneg : 0 ≤ Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sx m n.1 * Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (Int.toNat ((m : ℤ) - n.1) : ℝ)) :=
      mul_nonneg hweight_nonneg (Real.rpow_nonneg (by norm_num) _)
    have hexpand :
        Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi sx m n.1 =
          (Homogenization.Book.Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi * 2) *
            (((((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ))⁻¹ * (((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) ^ (1 / (hP4.xi : ℝ)))) *
            (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sx m n.1 * (((Homogenization.descendantsAtScale (Homogenization.originCube d (m : ℤ)) n.1).card : ℝ) ^ (1 / (hP4.xi : ℝ))))) +
          (Homogenization.Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi * 2) *
            (((((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ))⁻¹ * Real.sqrt ((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ)) *
            (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sx m n.1 * (((Homogenization.descendantsAtScale (Homogenization.originCube d (m : ℤ)) n.1).card : ℝ) ^ (1 / (hP4.xi : ℝ))))) := by
      simp only [Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff,
        Homogenization.Book.Ch05.Section52.section52LargeScaleLpRootCoeff,
        Homogenization.Book.Ch05.Section52.section52LargeScaleSqrtRootCoeff]
      ring
    rw [hexpand, hcardM]
    have hLp_part :
        (Homogenization.Book.Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi * 2) *
            (((((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ))⁻¹ * (((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) ^ (1 / (hP4.xi : ℝ)))) *
            (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sx m n.1 * Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (Int.toNat ((m : ℤ) - n.1) : ℝ)))) ≤
          (Homogenization.Book.Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi * 2) * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1) := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith only [hCLp_nonneg])
      calc
        ((((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ))⁻¹ * (((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) ^ (1 / (hP4.xi : ℝ)))) *
          (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sx m n.1 * Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (Int.toNat ((m : ℤ) - n.1) : ℝ))) ≤
            1 * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1) := by
          refine mul_le_mul hLp_ratio hcollapse hwr_nonneg ?_
          norm_num
        _ = disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1 := by ring
    have hSqrt_part :
        (Homogenization.Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi * 2) *
            (((((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ))⁻¹ * Real.sqrt ((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ)) *
            (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sx m n.1 * Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (Int.toNat ((m : ℤ) - n.1) : ℝ)))) ≤
          (Homogenization.Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi * 2) * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1) := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith only [hCSqrt_nonneg])
      calc
        ((((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ))⁻¹ * Real.sqrt ((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ)) *
          (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sx m n.1 * Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (Int.toNat ((m : ℤ) - n.1) : ℝ))) ≤
            1 * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1) := by
          refine mul_le_mul hSqrt_ratio hcollapse hwr_nonneg ?_
          norm_num
        _ = disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1 := by ring
    calc
      (Homogenization.Book.Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi * 2) *
          (((((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ))⁻¹ * (((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ) ^ (1 / (hP4.xi : ℝ)))) *
          (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sx m n.1 * Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (Int.toNat ((m : ℤ) - n.1) : ℝ)))) +
        (Homogenization.Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi * 2) *
          (((((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ))⁻¹ * Real.sqrt ((Homogenization.descendantsAtScale (Homogenization.originCube d n.1) 0).card : ℝ)) *
          (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sx m n.1 * Real.rpow (3 : ℝ) (((d : ℝ) / (hP4.xi : ℝ)) * (Int.toNat ((m : ℤ) - n.1) : ℝ)))) ≤
          (Homogenization.Book.Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi * 2) * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1) +
            (Homogenization.Book.Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi * 2) * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1) :=
        add_le_add hLp_part hSqrt_part
      _ = 2 * CR * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1) := by
        dsimp [CR]
        ring
  have hβ_le_s' : β ≤ s' := by
    have := hP4.sLower_nonneg
    dsimp [s']
    linarith only [this]
  have hβ_le_t' : β ≤ t' := by
    have := hP4.sUpper_nonneg
    dsimp [t']
    linarith only [this]
  -- per-term bound and summation
  let K : ℝ := (8 * dim2 * CR + 2 * T) * T
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    have h1 : 0 ≤ 8 * dim2 * CR := by positivity
    have h2 : 0 ≤ 8 * dim2 * CR + 2 * T := by
      linarith only [h1, hT_nonneg]
    exact mul_nonneg h2 hT_nonneg
  have hterm :
      ∀ n ∈ S.attach,
        (if N ≤ Int.toNat n.1 then 0 else
          σ * (dim2 * Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi s' m n.1 * l0) +
            σ⁻¹ * (dim2 * Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi t' m n.1 * L0) +
            (σ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 * ((hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ - (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) +
              σ⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 * (hP.barSigmaAtScale hStruct (0 : ℤ) - hP.barSigmaAtScale hStruct (m : ℤ)))) ≤
        (if N ≤ Int.toNat n.1 then 0 else
          K * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1)) := by
    intro n _hn
    by_cases hN : N ≤ Int.toNat n.1
    · simp only [if_pos hN]
      exact le_refl 0
    · simp only [if_neg hN]
      have hroot_s' := hrootC s' (le_of_lt hs'_pos) hgap_s' n
      have hroot_t' := hrootC t' (le_of_lt ht'_pos) hgap_t' n
      have hw_s'_nonneg : 0 ≤ Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 :=
        Homogenization.Book.Ch05.Section52.section52LargeScaleWeight_nonneg
          m (le_of_lt hs'_pos) n.1
      have hw_t'_nonneg : 0 ≤ Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 :=
        Homogenization.Book.Ch05.Section52.section52LargeScaleWeight_nonneg
          m (le_of_lt ht'_pos) n.1
      have hwβ_nonneg : 0 ≤ disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1 := by
        refine mul_nonneg (inv_nonneg.mpr (le_of_lt hdisc_pos)) ?_
        exact Homogenization.Book.Ch05.Section52.section52LargeScaleWeight_nonneg
          m (le_of_lt hβ_pos) n.1
      have hroot_s'_nonneg : 0 ≤ Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi s' m n.1 := by
        have h1 :=
          Homogenization.Book.Ch05.Section52.section52LargeScaleLpRootCoeff_nonneg
            (d := d) (ξ := hP4.xi) (s := s') m n.1 (le_of_lt hs'_pos)
        have h2 :=
          Homogenization.Book.Ch05.Section52.section52LargeScaleSqrtRootCoeff_nonneg
            (d := d) (ξ := hP4.xi) (s := t') m n.1 (le_of_lt ht'_pos)
        have h3 :=
          Homogenization.Book.Ch05.Section52.section52LargeScaleSqrtRootCoeff_nonneg
            (d := d) (ξ := hP4.xi) (s := s') m n.1 (le_of_lt hs'_pos)
        dsimp [Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff]
        linarith only [h1, h3]
      have hroot_t'_nonneg : 0 ≤ Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi t' m n.1 := by
        have h1 :=
          Homogenization.Book.Ch05.Section52.section52LargeScaleLpRootCoeff_nonneg
            (d := d) (ξ := hP4.xi) (s := t') m n.1 (le_of_lt ht'_pos)
        have h2 :=
          Homogenization.Book.Ch05.Section52.section52LargeScaleSqrtRootCoeff_nonneg
            (d := d) (ξ := hP4.xi) (s := t') m n.1 (le_of_lt ht'_pos)
        dsimp [Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff]
        linarith only [h1, h2]
      have hterm1 :
          σ * (dim2 * Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi s' m n.1 * l0) ≤
            (2 * T) * dim2 * (2 * CR * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1)) := by
        have hstep :
            σ * (dim2 * Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi s' m n.1 * l0) =
              (σ * l0) * dim2 * Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi s' m n.1 := by
          ring
        rw [hstep]
        calc
          (σ * l0) * dim2 * Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi s' m n.1 ≤
              (2 * T) * dim2 * Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi s' m n.1 := by
            refine mul_le_mul_of_nonneg_right ?_ hroot_s'_nonneg
            exact mul_le_mul_of_nonneg_right hσl0_le hdim2_nonneg
          _ ≤ (2 * T) * dim2 * (2 * CR * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1)) := by
            refine mul_le_mul_of_nonneg_left hroot_s' ?_
            have h2T : 0 ≤ 2 * T := by linarith only [hT_nonneg]
            exact mul_nonneg h2T hdim2_nonneg
      have hterm2 :
          σ⁻¹ * (dim2 * Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi t' m n.1 * L0) ≤
            (2 * T) * dim2 * (2 * CR * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1)) := by
        have hstep :
            σ⁻¹ * (dim2 * Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi t' m n.1 * L0) =
              (σ⁻¹ * L0) * dim2 * Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi t' m n.1 := by
          ring
        rw [hstep]
        calc
          (σ⁻¹ * L0) * dim2 * Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi t' m n.1 ≤
              (2 * T) * dim2 * Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi t' m n.1 := by
            refine mul_le_mul_of_nonneg_right ?_ hroot_t'_nonneg
            exact mul_le_mul_of_nonneg_right hσL0_le hdim2_nonneg
          _ ≤ (2 * T) * dim2 * (2 * CR * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1)) := by
            refine mul_le_mul_of_nonneg_left hroot_t' ?_
            have h2T : 0 ≤ 2 * T := by linarith only [hT_nonneg]
            exact mul_nonneg h2T hdim2_nonneg
      have hterm3 :
          σ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 * ((hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ - (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) +
            σ⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 * (hP.barSigmaAtScale hStruct (0 : ℤ) - hP.barSigmaAtScale hStruct (m : ℤ)) ≤
          (T * T) * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1) +
            (T * T) * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1) := by
        have h3a :
            σ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 * ((hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ - (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) =
              Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 * (σ * ((hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ - (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)) := by
          ring
        have h3b :
            σ⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 * (hP.barSigmaAtScale hStruct (0 : ℤ) - hP.barSigmaAtScale hStruct (m : ℤ)) =
              Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 * (σ⁻¹ * (hP.barSigmaAtScale hStruct (0 : ℤ) - hP.barSigmaAtScale hStruct (m : ℤ))) := by
          ring
        rw [h3a, h3b]
        have hTT_nonneg : 0 ≤ T * T := mul_nonneg hT_nonneg hT_nonneg
        have hga :
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 * (σ * ((hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ - (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)) ≤
              Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 * (T * T) :=
          mul_le_mul_of_nonneg_left hgap_lower hw_s'_nonneg
        have hgb :
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 * (σ⁻¹ * (hP.barSigmaAtScale hStruct (0 : ℤ) - hP.barSigmaAtScale hStruct (m : ℤ))) ≤
              Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 * (T * T) :=
          mul_le_mul_of_nonneg_left hgap_upper hw_t'_nonneg
        have hwa := hweight_dom s' (le_of_lt hs'_pos) hβ_le_s' n
        have hwb := hweight_dom t' (le_of_lt ht'_pos) hβ_le_t' n
        calc
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 * (σ * ((hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ - (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)) +
              Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 * (σ⁻¹ * (hP.barSigmaAtScale hStruct (0 : ℤ) - hP.barSigmaAtScale hStruct (m : ℤ))) ≤
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 * (T * T) + Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 * (T * T) :=
              add_le_add hga hgb
          _ ≤ (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1) * (T * T) +
              (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1) * (T * T) := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul_of_nonneg_right hwa hTT_nonneg
            · exact mul_le_mul_of_nonneg_right hwb hTT_nonneg
          _ = (T * T) * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1) +
              (T * T) * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1) := by
            ring
      have hβ_le_t'2 : β ≤ t' := hβ_le_t'
      calc
        σ * (dim2 * Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi s' m n.1 * l0) +
            σ⁻¹ * (dim2 * Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi t' m n.1 * L0) +
            (σ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 * ((hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ - (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) +
              σ⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 * (hP.barSigmaAtScale hStruct (0 : ℤ) - hP.barSigmaAtScale hStruct (m : ℤ))) ≤
          (2 * T) * dim2 * (2 * CR * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1)) +
            (2 * T) * dim2 * (2 * CR * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1)) +
            ((T * T) * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1) +
              (T * T) * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1)) := by
          have := add_le_add (add_le_add hterm1 hterm2) hterm3
          linarith only [this]
        _ = K * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1) := by
          dsimp [K]
          ring
  have hsum_le :
      (∑ n ∈ S.attach,
        if N ≤ Int.toNat n.1 then 0 else
          σ * (dim2 * Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi s' m n.1 * l0) +
            σ⁻¹ * (dim2 * Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi t' m n.1 * L0) +
            (σ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 * ((hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ - (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) +
              σ⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 * (hP.barSigmaAtScale hStruct (0 : ℤ) - hP.barSigmaAtScale hStruct (m : ℤ)))) ≤
      ∑ n ∈ S.attach,
        (if N ≤ Int.toNat n.1 then 0 else K * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1)) :=
    Finset.sum_le_sum hterm
  have hfactor :
      (∑ n ∈ S.attach,
        (if N ≤ Int.toNat n.1 then 0 else K * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1))) =
      K * disc⁻¹ *
        (∑ n ∈ S.attach, if N ≤ Int.toNat n.1 then 0 else Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro n _hn
    by_cases hN : N ≤ Int.toNat n.1
    · simp only [if_pos hN, mul_zero]
    · simp only [if_neg hN]
      ring
  have hattach :
      (∑ n ∈ S.attach, if N ≤ Int.toNat n.1 then 0 else Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1) =
      (∑ n ∈ S, if N ≤ Int.toNat n then 0 else Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n) := by
    exact Finset.sum_attach S
      (fun n => if N ≤ Int.toNat n then 0 else Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n)
  have htailβ :
      (∑ n ∈ S, if N ≤ Int.toNat n then 0 else Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n) ≤
      Real.rpow (3 : ℝ) (-β * ((m - N : ℕ) : ℝ)) := by
    simpa only [S] using
      section52LargeScaleSet_low_weight_sum_le_uniform_tail_rpow
        (c := β) (s := β) hβ_pos le_rfl N m
  -- envelope discharge
  have hceil_gap : Nat.ceil (B * Real.logb 3 (2 + T)) ≤ m - N := by
    have hNstarT :
        N + Nat.ceil (B * Real.logb 3 (2 + T)) ≤ m := by
      simpa only [T] using hNstar
    omega
  have hbuf : B * Real.logb 3 (2 + T) ≤ ((m - N : ℕ) : ℝ) :=
    (Nat.ceil_le).mp hceil_gap
  have henv := hB (T := T) (n := m - N) hT_one hbuf
  have hfinal :
      (5 * β⁻¹) ^ 2 *
          (K * disc⁻¹ * Real.rpow (3 : ℝ) (-β * ((m - N : ℕ) : ℝ))) ≤ eta := by
    have hKp_le : K ≤ (8 * dim2p * CRp + 2) * ((2 + T) ^ (2 : ℝ)) := by
      dsimp [K]
      rw [← hdim2_eq, ← hCR_eq]
      have hpow2 : (2 + T) ^ (2 : ℝ) = (2 + T) * (2 + T) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        ring
      rw [hpow2]
      have hT_le : T ≤ (2 + T) * (2 + T) := by
        linarith only [hT_nonneg, sq_nonneg T]
      have hTT_le : T * T ≤ (2 + T) * (2 + T) := by
        linarith only [hT_nonneg, sq_nonneg T]
      have h8 : 0 ≤ 8 * dim2 * CR := by positivity
      have hA :
          8 * dim2 * CR * T ≤ 8 * dim2 * CR * ((2 + T) * (2 + T)) :=
        mul_le_mul_of_nonneg_left hT_le h8
      have hB : 2 * (T * T) ≤ 2 * ((2 + T) * (2 + T)) := by
        linarith only [hTT_le]
      linarith only [hA, hB]
    have hrpow_nonneg :
        0 ≤ Real.rpow (3 : ℝ) (-β * ((m - N : ℕ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hdiscinv_nonneg : 0 ≤ disc⁻¹ := inv_nonneg.mpr (le_of_lt hdisc_pos)
    calc
      (5 * β⁻¹) ^ 2 *
          (K * disc⁻¹ * Real.rpow (3 : ℝ) (-β * ((m - N : ℕ) : ℝ))) ≤
        (5 * β⁻¹) ^ 2 *
          (((8 * dim2p * CRp + 2) * ((2 + T) ^ (2 : ℝ))) * disc⁻¹ *
            Real.rpow (3 : ℝ) (-β * ((m - N : ℕ) : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        refine mul_le_mul_of_nonneg_right ?_ hrpow_nonneg
        exact mul_le_mul_of_nonneg_right hKp_le hdiscinv_nonneg
      _ = Cp * ((2 + T) ^ (2 : ℝ) *
            Real.rpow (3 : ℝ) (-βp * ((m - N : ℕ) : ℝ))) := by
        dsimp [Cp]
        rw [← hβ_eq, ← hdisc_eq]
        ring
      _ ≤ eta := henv
  have hstart :
      section52LowTailBelowStartCoeff hP hStruct hP4 N m =
        (∑ n ∈ S.attach,
          if N ≤ Int.toNat n.1 then 0 else
            σ * (dim2 * Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi s' m n.1 * l0) +
              σ⁻¹ * (dim2 * Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi t' m n.1 * L0) +
              (σ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 * ((hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ - (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) +
                σ⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 * (hP.barSigmaAtScale hStruct (0 : ℤ) - hP.barSigmaAtScale hStruct (m : ℤ)))) := by
    simp only [section52LowTailBelowStartCoeff]
    refine Finset.sum_congr rfl ?_
    intro n _hn
    by_cases hN : N ≤ Int.toNat n.1
    · simp only [if_pos hN]
    · simp only [if_neg hN, σ, dim2, l0, L0, β, s', t']
  have hcoeff_le :
      section52LowTailBelowStartCoeff hP hStruct hP4 N m ≤
        K * disc⁻¹ *
          (∑ n ∈ S, if N ≤ Int.toNat n then 0 else Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n) := by
    rw [hstart]
    calc
      (∑ n ∈ S.attach,
        if N ≤ Int.toNat n.1 then 0 else
          σ * (dim2 * Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi s' m n.1 * l0) +
            σ⁻¹ * (dim2 * Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff d hP4.xi t' m n.1 * L0) +
            (σ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 * ((hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ - (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) +
              σ⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 * (hP.barSigmaAtScale hStruct (0 : ℤ) - hP.barSigmaAtScale hStruct (m : ℤ)))) ≤
        ∑ n ∈ S.attach,
          (if N ≤ Int.toNat n.1 then 0 else
            K * (disc⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1)) := hsum_le
      _ = K * disc⁻¹ *
          (∑ n ∈ S.attach, if N ≤ Int.toNat n.1 then 0 else Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n.1) :=
        hfactor
      _ = K * disc⁻¹ *
          (∑ n ∈ S, if N ≤ Int.toNat n then 0 else Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n) := by
        rw [hattach]
  have hKdisc_nonneg : 0 ≤ K * disc⁻¹ :=
    mul_nonneg hK_nonneg (inv_nonneg.mpr (le_of_lt hdisc_pos))
  have htail_step :
      K * disc⁻¹ *
          (∑ n ∈ S, if N ≤ Int.toNat n then 0 else Homogenization.Book.Ch05.Section52.section52LargeScaleWeight β m n) ≤
        K * disc⁻¹ * Real.rpow (3 : ℝ) (-β * ((m - N : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left htailβ hKdisc_nonneg
  have hcoeff_total :
      (5 * β⁻¹) ^ 2 * section52LowTailBelowStartCoeff hP hStruct hP4 N m ≤
        (5 * β⁻¹) ^ 2 *
          (K * disc⁻¹ * Real.rpow (3 : ℝ) (-β * ((m - N : ℕ) : ℝ))) :=
    mul_le_mul_of_nonneg_left (hcoeff_le.trans htail_step) (sq_nonneg _)
  exact hcoeff_total.trans hfinal

/--
Glue for the stochastic root: if the union-bound producer's `L²` sum is at
most `ofReal ((etaSrc/2)^ξ)`, then the sum is finite and its `1/ξ` root
(doubled) is at most `etaSrc`.
-/
theorem stochRoot_of_lintegral_le_ofReal_pow
    {X : ENNReal} {etaSrc ξr : ℝ}
    (hξ : 1 ≤ ξr) (hetaSrc : 0 < etaSrc)
    (hX : X ≤ ENNReal.ofReal ((etaSrc / 2) ^ ξr)) :
    X ≠ ⊤ ∧ 2 * (X.toReal ^ (1 / ξr)) ≤ etaSrc := by
  have hfin : X ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hX
  refine ⟨hfin, ?_⟩
  have hhalf_nonneg : (0 : ℝ) ≤ etaSrc / 2 := by linarith only [hetaSrc]
  have hbase_nonneg : (0 : ℝ) ≤ (etaSrc / 2) ^ ξr :=
    Real.rpow_nonneg hhalf_nonneg _
  have htoReal : X.toReal ≤ (etaSrc / 2) ^ ξr := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hX
    rwa [ENNReal.toReal_ofReal hbase_nonneg] at h
  have hexp_nonneg : (0 : ℝ) ≤ 1 / ξr := by positivity
  have hroot : X.toReal ^ (1 / ξr) ≤ ((etaSrc / 2) ^ ξr) ^ (1 / ξr) :=
    Real.rpow_le_rpow ENNReal.toReal_nonneg htoReal hexp_nonneg
  have hξ_ne : ξr ≠ 0 := by linarith only [hξ]
  have hcollapse : ((etaSrc / 2) ^ ξr) ^ (1 / ξr) = etaSrc / 2 := by
    rw [← Real.rpow_mul hhalf_nonneg, mul_one_div, div_self hξ_ne,
      Real.rpow_one]
  rw [hcollapse] at hroot
  linarith only [hroot]

/--
Glue for the polynomial root: the `a.HM` source envelope root at the buffered
scale is at most any positive target.  Uses the linear-prefactor envelope
buffer at `A := Q`, `c := min(Q·ρM − d, Q·γ) > 0`.
-/
theorem exists_bufferExponent_sourceEnvelopeRoot_le_of_Nstar
    {d : ℕ} [NeZero d] {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    {polyRootBound : ℝ} (hpos : 0 < polyRootBound) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P),
        1 ≤ Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 →
        ∀ {N m : ℕ},
          N + Nat.ceil
              (B * Real.logb 3
                (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) ≤
            m →
          ((ENNReal.ofReal
              (((2 +
                Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
                (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
                  (3 : ℝ) ^
                    (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                      ((m - N : ℕ) : ℝ))))) ^ (1 / hm.Q)).toReal ≤
            polyRootBound) := by
  classical
  have hQ_pos : 0 < hm.Q := highCenteredMoment_Q_pos hm
  have hc_min_pos : 0 < min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma) := by
    have h1 : 0 < hm.Q * hc.rhoM - (d : ℝ) := by
      have := hm.Q_mul_rhoM_gt
      linarith only [this]
    have h2 : 0 < hm.Q * hm.gamma :=
      mul_pos hQ_pos hm.gamma_pos
    exact lt_min h1 h2
  have htarget_pos : 0 < polyRootBound ^ hm.Q :=
    Real.rpow_pos_of_pos hpos _
  obtain ⟨B, hB_one, hB⟩ :=
    exists_bufferExponent_for_polynomial_geometric_envelope_le
      (C := hm.C_Q) (A := hm.Q)
      (c := min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma))
      (η := polyRootBound ^ hm.Q) hm.C_Q_nonneg hc_min_pos htarget_pos
  refine ⟨B, hB_one, ?_⟩
  intro P hP4 hTheta N m hNstar
  set T : ℝ := Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4
    with hT_def
  have hT_one : 1 ≤ T := by
    simpa only [hT_def] using hTheta
  have hT_nonneg : 0 ≤ T := by linarith only [hT_one]
  have hceil_gap : Nat.ceil (B * Real.logb 3 (2 + T)) ≤ m - N := by
    have hNstarT :
        N + Nat.ceil (B * Real.logb 3 (2 + T)) ≤ m := by
      simpa only [hT_def] using hNstar
    omega
  have hbuf : B * Real.logb 3 (2 + T) ≤ ((m - N : ℕ) : ℝ) :=
    (Nat.ceil_le).mp hceil_gap
  have henv := hB (T := T) (n := m - N) hT_one hbuf
  -- the envelope's linear form matches the source envelope up to reassociation
  have hE_nonneg :
      0 ≤ ((2 + T) ^ hm.Q) *
        (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
          (3 : ℝ) ^
            (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
              ((m - N : ℕ) : ℝ)))) := by
    have h2T : (0 : ℝ) ≤ 2 + T := by linarith only [hT_nonneg]
    have hpow : 0 ≤ (2 + T) ^ hm.Q := Real.rpow_nonneg h2T _
    have hlin : (0 : ℝ) ≤ ((m - N + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hrpow : (0 : ℝ) ≤ (3 : ℝ) ^
        (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
          ((m - N : ℕ) : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have := hm.C_Q_nonneg
    positivity
  have hE_le :
      ((2 + T) ^ hm.Q) *
        (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
          (3 : ℝ) ^
            (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
              ((m - N : ℕ) : ℝ)))) ≤ polyRootBound ^ hm.Q := by
    have hcast : ((m - N + 1 : ℕ) : ℝ) = ((m - N : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    calc
      ((2 + T) ^ hm.Q) *
          (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - N : ℕ) : ℝ)))) =
        hm.C_Q * (((2 + T) ^ hm.Q) *
          ((((m - N : ℕ) : ℝ) + 1) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - N : ℕ) : ℝ)))) := by
        rw [hcast]
        ring
      _ ≤ polyRootBound ^ hm.Q := henv
  have hroot_le :
      (((2 + T) ^ hm.Q) *
        (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
          (3 : ℝ) ^
            (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
              ((m - N : ℕ) : ℝ))))) ^ (1 / hm.Q) ≤ polyRootBound := by
    have hexp_nonneg : (0 : ℝ) ≤ 1 / hm.Q := by positivity
    have h := Real.rpow_le_rpow hE_nonneg hE_le hexp_nonneg
    have hQ_ne : hm.Q ≠ 0 := ne_of_gt hQ_pos
    have hcollapse : (polyRootBound ^ hm.Q) ^ (1 / hm.Q) = polyRootBound := by
      rw [← Real.rpow_mul (le_of_lt hpos), mul_one_div, div_self hQ_ne,
        Real.rpow_one]
    rwa [hcollapse] at h
  have hofReal :
      ((ENNReal.ofReal
          (((2 + T) ^ hm.Q) *
            (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
              (3 : ℝ) ^
                (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                  ((m - N : ℕ) : ℝ)))))) ^ (1 / hm.Q)).toReal =
        (((2 + T) ^ hm.Q) *
          (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - N : ℕ) : ℝ))))) ^ (1 / hm.Q) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hE_nonneg (by positivity : (0:ℝ) ≤ 1 / hm.Q)]
    exact ENNReal.toReal_ofReal (Real.rpow_nonneg hE_nonneg _)
  calc
    ((ENNReal.ofReal
        (((2 + T) ^ hm.Q) *
          (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - N : ℕ) : ℝ)))))) ^ (1 / hm.Q)).toReal =
      (((2 + T) ^ hm.Q) *
        (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
          (3 : ℝ) ^
            (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
              ((m - N : ℕ) : ℝ))))) ^ (1 / hm.Q) := hofReal
    _ ≤ polyRootBound := hroot_le

end Homogenization.HighContrast.EntryScale
