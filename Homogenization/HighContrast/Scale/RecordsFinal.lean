import Homogenization.Book.Ch05.Theorems.Section51.AnnealedConvergence
import Homogenization.Book.Ch05.Theorems.Section55.ShiftedWidetildeTheta
import Homogenization.HighContrast.Scale.WidetildeTheta
import Homogenization.HighContrast.EntryScale.Inputs

/-!
# Unconditional records for the homogenization-scale capstone

This file constructs concrete inhabitants of the entry-scale assembly's
external-input records at *canonical* quantitative coarse-grained ellipticity
parameters,
discharging them against the Chapter 5 formalization in `Homogenization`:

* `canonicalParams d` — the explicit `(P4)` parameter record `s₁ = s₂ = 1/3`,
  `ξ = 3d + 1`;
* `hcOfParams params` — the high-contrast exponent record with
  `β = ρ_M = section53CoarseFluctuationBetaParams params`, whose source-max gaps
  are the numeric inequalities `0 < s`;
* `locOfParams params` — the localization / small-contrast input, whose
  `localization` field is discharged from Section 5.5
  (`shiftedWidetildeThetaBound_homogenizationScale`) and whose `small_contrast`
  field is discharged from the Section 5.1 annealed-convergence restart
  mechanism (Section 5.6 algebraic decay transported to the shifted anchor).
-/

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch04 (RestrictionCoeffLaw RestrictionLawCarrier RestrictionStructuralLaw)
open Homogenization.Book.Ch05
open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization.Book.Ch05.Section51

namespace Homogenization

open Homogenization.HighContrast.EntryScale

/-- Positivity of the parameter-level Section 5.3 coarse-fluctuation exponent,
proved directly from the `(P4)` parameter inequalities. -/
theorem section53CoarseFluctuationBetaParams_pos_of_params {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    0 < section53CoarseFluctuationBetaParams params := by
  unfold section53CoarseFluctuationBetaParams section53CoarseFluctuationBetaCoreParams
  have h1 : 0 < 1 - params.sUpper - params.sLower := by
    have := params.sum_lt_one; linarith
  have h2 : 0 < params.sUpper := params.sUpper_pos
  have h3 : 0 < params.sLower := params.sLower_pos
  have h4 : 0 < params.sUpper - (d : ℝ) / (params.xi : ℝ) := by
    have := params.dim_div_xi_lt_sUpper; linarith
  have h5 : 0 < params.sLower - (d : ℝ) / (params.xi : ℝ) := by
    have := params.dim_div_xi_lt_sLower; linarith
  have hcore : 0 < min (1 - params.sUpper - params.sLower)
      (min params.sUpper
        (min params.sLower
          (min (params.sUpper - (d : ℝ) / (params.xi : ℝ))
            (params.sLower - (d : ℝ) / (params.xi : ℝ))))) :=
    lt_min h1 (lt_min h2 (lt_min h3 (lt_min h4 h5)))
  positivity

/-- The canonical `(P4)` parameter record: `s₁ = s₂ = 1/3`, `ξ = 3d + 1`. -/
noncomputable def canonicalParams (d : ℕ) (hd : 2 ≤ d) :
    QuantitativeCoarseGrainedEllipticityParams d where
  sUpper := 1 / 3
  sLower := 1 / 3
  xi := 3 * d + 1
  two_le_dim := hd
  sUpper_nonneg := by norm_num
  sUpper_lt_one := by norm_num
  sLower_nonneg := by norm_num
  sLower_lt_one := by norm_num
  xi_gt_two_mul_dim := by
    have : (0 : ℝ) ≤ (d : ℝ) := by positivity
    push_cast; linarith
  sum_lt_one := by norm_num
  dim_div_xi_lt_min := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
    have hxi_pos : (0 : ℝ) < (3 * (d : ℝ) + 1) := by linarith
    rw [lt_min_iff]
    constructor <;>
      · rw [div_lt_iff₀ (by push_cast; linarith)]
        push_cast; linarith

/-- The high-contrast exponent record at parameters `params`.  All exponents are
tied to the Section 5.3 coarse-fluctuation exponent `β = section53CoarseFluctuationBetaParams params`. -/
noncomputable def hcOfParams {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    HighContrastExponents d where
  params := params
  rhoM := section53CoarseFluctuationBetaParams params
  beta := section53CoarseFluctuationBetaParams params
  zeta := 3 / 2
  rhoM_pos := section53CoarseFluctuationBetaParams_pos_of_params params
  beta_pos := section53CoarseFluctuationBetaParams_pos_of_params params
  one_lt_zeta := by norm_num
  zeta_lt_two := by norm_num
  kappaH := section53CoarseFluctuationBetaParams params / 2
  kappaH_pos := by
    have := section53CoarseFluctuationBetaParams_pos_of_params params; linarith
  kappaH_le_rhoM := by
    have := section53CoarseFluctuationBetaParams_pos_of_params params; linarith
  kappaH_le_beta := by
    have := section53CoarseFluctuationBetaParams_pos_of_params params; linarith
  sourceMaxLowerGap := by
    have := params.sLower_pos; linarith
  sourceMaxUpperGap := by
    have := params.sUpper_pos; linarith

@[simp] theorem hcOfParams_params {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    (hcOfParams params).params = params := rfl

@[simp] theorem hcOfParams_beta {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    (hcOfParams params).beta = section53CoarseFluctuationBetaParams params := rfl

/-- A fixed unit coordinate vector, used as the test direction for the
small-contrast `J`-bound. -/
private def unitVec (d : ℕ) [NeZero d] : Vec d := Pi.single (0 : Fin d) 1

private theorem unitVec_normSq (d : ℕ) [NeZero d] : vecNormSq (unitVec d) = 1 := by
  rw [unitVec, vecNormSq, vecDot, Finset.sum_eq_single (0 : Fin d)]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

/-- The localization / small-contrast input at parameters `params`.

The `localization` field is the Section 5.5 shifted-localization bound; the
`small_contrast` field is the Section 5.1 annealed-convergence restart applied
at the given anchor `N` (Section 5.6 algebraic decay transported through the
scale-normalized law). -/
noncomputable def locOfParams {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    LocalizationSmallContrastInput (hcOfParams params) := by
  classical
  let S55 := Section55.shiftedWidetildeThetaBound_homogenizationScale (d := d) params.xi
      (section53CoarseFluctuationBetaParams params)
      (section53CoarseFluctuationBetaParams_pos_of_params params)
  have hCloc_spec := S55.choose_spec
  let S56 := Section56.SmallContrastAlgebraicDecay.smallContrastAlgebraicDecay_homogenizationScale
      (twoBetaShiftedParams params)
  let αsc : ℝ := S56.choose
  let δ0s : ℝ := S56.choose_spec.choose
  let K : ℝ := S56.choose_spec.choose_spec.choose
  have h56 := S56.choose_spec.choose_spec.choose_spec
  have hαsc_pos : 0 < αsc := h56.1
  have hδ0s_pos : 0 < δ0s := h56.2.1
  have hK_pos : 0 < K := h56.2.2.1
  set R : ℕ :=
    Nat.ceil (Real.log (max (4 * K) 1) / ((αsc / 2) * Real.log 3)) with hRdef
  set α : ℝ := min (αsc / 2) (((R + 1 : ℕ) : ℝ)⁻¹) with hαdef
  have hα_pos : 0 < α := by rw [hαdef]; exact lt_min (by positivity) (by positivity)
  refine
    { C_loc := S55.choose
      beta_loc := section53CoarseFluctuationBetaParams params
      delta0 := min δ0s (1 / 4)
      C_sc := 1
      alpha0 := α
      C_loc_nonneg := hCloc_spec.1
      beta_loc_pos := section53CoarseFluctuationBetaParams_pos_of_params params
      delta0_pos := lt_min hδ0s_pos (by norm_num)
      delta0_le_one := (min_le_right _ _).trans (by norm_num)
      C_sc_pos := one_pos
      alpha0_pos := hα_pos
      localization := ?_
      small_contrast := ?_ }
  · -- localization: direct from Section 5.5
    intro P hP hStruct hP4 hpe k n hkn
    have hpe' : hP4.params = params := hpe
    have hxi : hP4.xi = params.xi := by
      rw [← QuantitativeCoarseGrainedEllipticity.params_xi hP4, hpe']
    have hβ : section53CoarseFluctuationBeta hP4 =
        section53CoarseFluctuationBetaParams params := by
      rw [← section53CoarseFluctuationBetaParams_eq_of_P4 hP4, hpe']
    have h := hCloc_spec.2 hP hStruct hP4 hxi hβ hkn
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [neg_mul] at h2
    exact h2
  · -- small_contrast: the annealed-convergence restart at anchor `N`
    intro P hP hStruct hP4 hpe N hsmallN n
    have hpe' : hP4.params = params := hpe
    set δ : ℝ := min δ0s (1 / 4) with hδdef
    have hδ_le_δ0 : δ ≤ δ0s := min_le_left _ _
    have hδ_le_quarter : δ ≤ 1 / 4 := min_le_right _ _
    have hβ : section53CoarseFluctuationBetaParams params =
        section53CoarseFluctuationBeta hP4 := by
      rw [← section53CoarseFluctuationBetaParams_eq_of_P4 hP4, hpe']
    have hshiftN :
        Section55.shiftedWidetildeThetaAtScale P (N : ℤ) hP4
            (2 * section53CoarseFluctuationBeta hP4) - 1 ≤ δ := by
      have := hsmallN
      rw [hcOfParams_beta, hβ] at this
      exact this
    -- transport to the scale-normalized law at anchor `N`
    set PN : RestrictionCoeffLaw d := Homogenization.Book.Ch04.restrictionScaleNormalizedLaw N P with hPNdef
    set hPN : RestrictionLawCarrier PN := hP.scaleNormalized N with hPNcarr
    set hStructN : RestrictionStructuralLaw PN := hStruct.scaleNormalized N with hStructNdef
    set hP4N : QuantitativeCoarseGrainedEllipticity PN :=
      hP4.scaleNormalized hP hStruct N with hP4Ndef
    set hP4S : QuantitativeCoarseGrainedEllipticity PN :=
      twoBetaShiftedP4 hPN hStructN hP4N with hP4Sdef
    have hwide_eq :
        widetildeThetaAtScale PN (0 : ℤ) hP4S =
          Section55.shiftedWidetildeThetaAtScale P (N : ℤ) hP4
            (2 * section53CoarseFluctuationBeta hP4) := by
      simpa [hPNdef, hPNcarr, hStructNdef, hP4Ndef, hP4Sdef] using
        widetildeThetaAtScale_zero_scaleNormalized_twoBetaShiftedP4 hP hStruct hP4 N
    have hsmall0_delta : widetildeThetaAtScale PN (0 : ℤ) hP4S - 1 ≤ δ := by
      rw [hwide_eq]; exact hshiftN
    have hsmall0_δ0 : widetildeThetaAtScale PN (0 : ℤ) hP4S - 1 ≤ δ0s :=
      hsmall0_delta.trans hδ_le_δ0
    have hsmall0_quarter : widetildeThetaAtScale PN (0 : ℤ) hP4S - 1 ≤ 1 / 4 :=
      hsmall0_delta.trans hδ_le_quarter
    have hP4N_params : hP4N.params = params := by
      have h0 : hP4N.params = hP4.params := rfl
      rw [h0, hpe']
    have hparamsS : hP4S.params = twoBetaShiftedParams params := by
      rw [hP4Sdef, twoBetaShiftedP4_params, hP4N_params]
    have htheta_sub_quarter :
        thetaAtScale hPN hStructN (n : ℤ) - 1 ≤ 1 / 4 :=
      (Section56.SmallContrastAlgebraicDecay.thetaAtScale_sub_one_le_delta_of_widetildeThetaAtScale_zero_sub_one_le_delta
          hPN hStructN hP4S hsmall0_delta n).trans hδ_le_quarter
    have hwide_two : widetildeThetaAtScale PN (0 : ℤ) hP4S ≤ 2 := by
      linarith [hsmall0_quarter]
    set e : Vec d := unitVec d with hedef
    have he : vecNormSq e = 1 := by rw [hedef]; exact unitVec_normSq d
    have hJ_upper := h56.2.2.2 hPN hStructN hP4S hparamsS hsmall0_δ0 n e he
    have hJ_lower :=
      Section56.expectedResponseJCubeSet_special_ge_quarter_theta_sub_one
        hPN hStructN hP4S hwide_two n e he
    have htheta_sub_decay :
        thetaAtScale hPN hStructN (n : ℤ) - 1 ≤
          4 * K * Real.rpow (3 : ℝ) (-αsc * (n : ℝ)) := by
      dsimp only at hJ_upper hJ_lower
      nlinarith
    have htheta_sub_unit_decay :
        thetaAtScale hPN hStructN (n : ℤ) - 1 ≤
          Real.rpow (3 : ℝ) (-α * (n : ℝ)) := by
      by_cases hnR : n ≤ R
      · have hα_le_inv : α ≤ (((R + 1 : ℕ) : ℝ)⁻¹) := by
          rw [hαdef]; exact min_le_right _ _
        have hαn : α * (n : ℝ) ≤ 1 :=
          mul_nat_le_one_of_le_inverse_succ hα_le_inv hnR
        exact htheta_sub_quarter.trans
          (quarter_le_rpow_three_neg_mul_of_mul_nat_le_one hαn)
      · have hR_lt_n : R < n := Nat.lt_of_not_ge hnR
        have hlarge :
            Real.log (max (4 * K) 1) / ((αsc / 2) * Real.log 3) ≤ (n : ℝ) := by
          have hceil :
              Real.log (max (4 * K) 1) / ((αsc / 2) * Real.log 3) ≤ (R : ℝ) := by
            rw [hRdef]
            exact Nat.le_ceil _
          exact hceil.trans (by exact_mod_cast (Nat.le_of_lt hR_lt_n))
        have hpref :
            4 * K * Real.rpow (3 : ℝ) (-αsc * (n : ℝ)) ≤
              Real.rpow (3 : ℝ) (-(αsc / 2) * (n : ℝ)) :=
          prefactor_decay_le_half_exponent_decay_of_large
            (α₀ := αsc) (K := K) hαsc_pos hlarge
        have hhalf_to_alpha :
            Real.rpow (3 : ℝ) (-(αsc / 2) * (n : ℝ)) ≤
              Real.rpow (3 : ℝ) (-α * (n : ℝ)) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ?_
          have hα_le_half : α ≤ αsc / 2 := by rw [hαdef]; exact min_le_left _ _
          have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
          nlinarith
        exact htheta_sub_decay.trans (hpref.trans hhalf_to_alpha)
    have hscale :
        thetaAtScale hPN hStructN (n : ℤ) =
          thetaAtScale hP hStruct ((N + n : ℕ) : ℤ) := by
      simp only [thetaAtScale]
      exact hP.thetaAtScale_restrictionScaleNormalizedLaw hStruct N n
    rw [← hscale]
    simpa only [one_mul, neg_mul] using htheta_sub_unit_decay

/-- Integrability of a bounded nonnegative power on a probability measure. -/
private theorem integrable_pow_of_ae_bound {d : ℕ}
    {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {f : RegCoeffField d → ℝ} {C : ℝ} (hf : AEMeasurable f P)
    (hnonneg : ∀ᵐ a ∂P, 0 ≤ f a) (hbound : ∀ᵐ a ∂P, f a ≤ C) (ξ : ℕ) :
    Integrable (fun a => f a ^ ξ) P := by
  refine (integrable_const (C ^ ξ)).mono' (hf.pow_const ξ).aestronglyMeasurable ?_
  filter_upwards [hnonneg, hbound] with a hn hb
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hn ξ)]
  exact pow_le_pow_left₀ hn hb ξ

/-- The Chapter 5 quantitative coarse-grained ellipticity record `(P4)` at the
canonical parameters, constructed from a `Θ`-elliptic law.  Its integrability
fields are discharged from the a.e. multiscale ellipticity bounds
(`≤ 2Θ`, inverse `≤ 2`) on the probability measure. -/
noncomputable def qcgeOfThetaEllipticLaw {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {Θ : ℝ} (hΘ : 1 ≤ Θ) {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    (hP : RestrictionLawCarrier P) (hLaw : ThetaEllipticLaw Θ P) :
    QuantitativeCoarseGrainedEllipticity P where
  sUpper := 1 / 3
  sLower := 1 / 3
  xi := 3 * d + 1
  two_le_dim := hd
  sUpper_nonneg := by norm_num
  sUpper_lt_one := by norm_num
  sLower_nonneg := by norm_num
  sLower_lt_one := by norm_num
  xi_gt_two_mul_dim := by
    have : (0 : ℝ) ≤ (d : ℝ) := by positivity
    push_cast; linarith
  sum_lt_one := by norm_num
  dim_div_xi_lt_min := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
    rw [lt_min_iff]
    constructor <;>
      · rw [div_lt_iff₀ (by push_cast; linarith)]
        push_cast; linarith
  upper_moment_integrable := by
    refine integrable_pow_of_ae_bound (C := 2 * Θ)
      (hP.aemeasurable_LambdaSqCoeffField_finite_one (originCube d 0) (by norm_num))
      ?_ ?_ _
    · filter_upwards with a
      exact Homogenization.Book.Ch04.LambdaSqCoeffField_finite_nonneg (originCube d 0) a (by norm_num) le_rfl
    · filter_upwards [hLaw] with a ha
      exact LambdaSqCoeffField_originCube_zero_le_of_ae hΘ (by norm_num) ha
  lower_inv_moment_integrable := by
    refine integrable_pow_of_ae_bound (C := 2)
      (hP.aemeasurable_lambdaSqCoeffField_finite_one_inv (originCube d 0) (by norm_num))
      ?_ ?_ _
    · filter_upwards with a
      exact inv_nonneg.mpr
        (Homogenization.Book.Ch04.lambdaSqCoeffField_finite_nonneg (originCube d 0) a (by norm_num) le_rfl)
    · filter_upwards [hLaw] with a ha
      exact lambdaSqCoeffField_originCube_zero_inv_le_of_ae hΘ (by norm_num) ha

@[simp] theorem qcgeOfThetaEllipticLaw_params {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {Θ : ℝ} (hΘ : 1 ≤ Θ) {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    (hP : RestrictionLawCarrier P) (hLaw : ThetaEllipticLaw Θ P) :
    (qcgeOfThetaEllipticLaw hd hΘ hP hLaw).params = canonicalParams d hd := rfl

end Homogenization
