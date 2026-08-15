import Homogenization.HighContrast.Variance.BlockVarianceBound
import Homogenization.HighContrast.EntryScale.VarianceUpgrade.P1

/-!
# Parameter records for the homogenization-scale capstone

This file constructs, from the dimension `d` (`3 ≤ d`), the parameter-only
`(P4)` data `params`, an ellipticity level `Θ ≥ 1`, and the fixed
high-contrast exponents `hc`, the parameter records consumed by the
entry-scale final assembly
`Homogenization.HighContrast.EntryScale.exists_final_scale_decay_of_main_buffer_and_variance_scalars`
(`VarianceUpgrade/P2.lean`):

* `vpParams` — the two-channel variance input `VarianceMomentParameters`, with
  the *dimensional* decay slope `δ = (d-2)/(2(d-1))` (so the interpolation
  exponent `2δ = (d-2)/(d-1)` matches the landed second-moment envelope) and
  the *per-law* amplitudes `C₂ = Cd · Θ⁶` (Cd the dimension constant of the
  landed bound `integral_fullBlockNormalizedFluctuation_le`) and
  `C₀ = 48·|BlockCoord d|³ · Θ`, `b = 0` (uniformly elliptic pathwise bound).
* `hmParams` — the high centered-moment parameter pack
  `HighCenteredMomentParameters`, with a moment exponent `Q` chosen large
  enough for every downstream numeric side condition (`Q·ρ_M > d+4`,
  `2·ξ ≤ Q`, `holderExponentFloor < Q`) and `p4Params = params`.
* `subParams` — the polynomial subthreshold parameter record
  `SubthresholdPolynomialMomentParameters` (the *estimate* for these
  parameters is built by the sibling `Subthreshold*` package, not here).

together with the entry-scale definitions `scaleN2`, `scaleN` exposed as
functions of `T` so the capstone can instantiate the ceiling equations
`N₂ = ⌈p₂·log₃(2+T)⌉` and `N = ⌈p_Q·log₃(2+T)⌉`.

All numeric field conditions are discharged.  The analytic (theorem-valued)
fields of `LocalizationSmallContrastInput` are *external inputs* and are
supplied at the capstone, not reconstructed here.
-/

open Homogenization
open Homogenization.Book.Ch05 (QuantitativeCoarseGrainedEllipticityParams)

namespace Homogenization

open Homogenization.HighContrast.EntryScale

/-! ## The landed dimension constant and the pathwise-budget constant -/

/-- The dimension-only constant `Cd` from the landed variance bridge
`integral_fullBlockNormalizedFluctuation_le`, extracted as a concrete real so
it can anchor the variance amplitude `C₂`. -/
noncomputable def landedVarianceConstant (d : ℕ) [NeZero d] (hd : 3 ≤ d) : ℝ :=
  Classical.choose (Homogenization.integral_fullBlockNormalizedFluctuation_le hd)

theorem landedVarianceConstant_nonneg (d : ℕ) [NeZero d] (hd : 3 ≤ d) :
    0 ≤ landedVarianceConstant d hd :=
  (Classical.choose_spec
    (Homogenization.integral_fullBlockNormalizedFluctuation_le hd)).1

/-- The full landed variance bound for the extracted constant.  This is the
`choose_spec` of `landedVarianceConstant`, used by `VarianceEstimate.lean`. -/
theorem landedVarianceConstant_spec (d : ℕ) [NeZero d] (hd : 3 ≤ d) :
    ∀ {Θ : ℝ} (_hΘ : 1 ≤ Θ) {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
      [MeasureTheory.IsProbabilityMeasure P]
      (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
      (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
      (_hLaw : Homogenization.ThetaEllipticLaw Θ P)
      {m : ℤ} (_hm : 0 ≤ m),
      ∫ a, Homogenization.Book.Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct m (originCube d m) a ∂P
        ≤ landedVarianceConstant d hd * Θ ^ 6 *
            ((3 : ℝ) ^ m) ^ (-((d : ℝ) - 2) / ((d : ℝ) - 1)) :=
  (Classical.choose_spec
    (Homogenization.integral_fullBlockNormalizedFluctuation_le hd)).2

/-- The pathwise operator-norm budget constant `48·|BlockCoord d|³`.  This is
the deterministic constant behind the a.e. bound
`‖D·(A−Ā)·D‖ ≤ 48·|BlockCoord d|³·Θ` (`b = 0` uniformly elliptic case). -/
noncomputable def pathwiseBudgetConstant (d : ℕ) : ℝ :=
  48 * (Fintype.card (Homogenization.BlockCoord d) : ℝ) ^ 3

theorem pathwiseBudgetConstant_nonneg (d : ℕ) : 0 ≤ pathwiseBudgetConstant d := by
  unfold pathwiseBudgetConstant; positivity

/-! ## The variance parameter record -/

/-- The dimensional decay slope `δ = (d-2)/(2(d-1))`, so that `2δ = (d-2)/(d-1)`
is exactly the exponent of the landed second-moment envelope. -/
noncomputable def varianceDelta (d : ℕ) : ℝ := ((d : ℝ) - 2) / (2 * ((d : ℝ) - 1))

theorem varianceDelta_pos {d : ℕ} (hd : 3 ≤ d) : 0 < varianceDelta d := by
  have hd3 : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  unfold varianceDelta
  apply div_pos <;> linarith

/-- `2δ = (d-2)/(d-1)`: the interpolation exponent equals the landed envelope
exponent. -/
theorem two_mul_varianceDelta {d : ℕ} (hd : 3 ≤ d) :
    2 * varianceDelta d = ((d : ℝ) - 2) / ((d : ℝ) - 1) := by
  have hd3 : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1 : ((d : ℝ) - 1) ≠ 0 := by
    have : (0 : ℝ) < (d : ℝ) - 1 := by linarith
    exact ne_of_gt this
  unfold varianceDelta
  field_simp

/-- **The variance record.**  `VarianceMomentParameters` with
dimensional slope `δ` and per-law amplitudes `C₂ = Cd·Θ⁶`,
`C₀ = 48·|BlockCoord d|³·Θ`, `b = 0`, `p₂ = 1`. -/
noncomputable def vpParams (d : ℕ) [NeZero d] (hd : 3 ≤ d) (Θ : ℝ) :
    VarianceMomentParameters where
  p2 := 1
  delta := varianceDelta d
  C2 := landedVarianceConstant d hd * Θ ^ 6
  C0 := pathwiseBudgetConstant d * Θ ^ 6
  b := 0
  p2_nonneg := by norm_num
  delta_pos := varianceDelta_pos hd
  C2_nonneg :=
    mul_nonneg (landedVarianceConstant_nonneg d hd) (by positivity)
  C0_nonneg :=
    mul_nonneg (pathwiseBudgetConstant_nonneg d) (by positivity)
  b_nonneg := le_refl 0

@[simp] theorem vpParams_p2 (d : ℕ) [NeZero d] (hd : 3 ≤ d) (Θ : ℝ) :
    (vpParams d hd Θ).p2 = 1 := rfl

@[simp] theorem vpParams_delta (d : ℕ) [NeZero d] (hd : 3 ≤ d) (Θ : ℝ) :
    (vpParams d hd Θ).delta = varianceDelta d := rfl

@[simp] theorem vpParams_C2 (d : ℕ) [NeZero d] (hd : 3 ≤ d) (Θ : ℝ) :
    (vpParams d hd Θ).C2 = landedVarianceConstant d hd * Θ ^ 6 := rfl

@[simp] theorem vpParams_C0 (d : ℕ) [NeZero d] (hd : 3 ≤ d) (Θ : ℝ) :
    (vpParams d hd Θ).C0 = pathwiseBudgetConstant d * Θ ^ 6 := rfl

@[simp] theorem vpParams_b (d : ℕ) [NeZero d] (hd : 3 ≤ d) (Θ : ℝ) :
    (vpParams d hd Θ).b = 0 := rfl

/-! ## The high centered-moment parameter record -/

/-- The moment exponent, chosen large enough for every downstream numeric side
condition: `Q·ρ_M > d+4`, `2·ξ ≤ Q`, `2 ≤ Q`. -/
noncomputable def momentQ (d : ℕ) (hc : HighContrastExponents d)
    (params : QuantitativeCoarseGrainedEllipticityParams d) : ℝ :=
  2 + 2 * (params.xi : ℝ) + ((d : ℝ) + 5) / hc.rhoM

theorem two_le_momentQ (d : ℕ) (hc : HighContrastExponents d)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    2 ≤ momentQ d hc params := by
  unfold momentQ
  have h1 : (0 : ℝ) ≤ 2 * (params.xi : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ ((d : ℝ) + 5) / hc.rhoM :=
    div_nonneg (by positivity) (le_of_lt hc.rhoM_pos)
  linarith

/-- **The high centered-moment record.**  The fields `p_hm`,
`gamma`, `C_Q` are placeholders (the final assembly uses
`hm.varianceUpgrade vp`, which overrides all three); the structural fields
`Q`, `holderExponentFloor`, `p4Params` carry the genuine content. -/
noncomputable def hmParams (d : ℕ) (hc : HighContrastExponents d)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    HighCenteredMomentParameters d hc where
  p_hm := 0
  Q := momentQ d hc params
  gamma := 1
  C_Q := 0
  holderExponentFloor := 0
  p4Params := params
  p_hm_nonneg := le_refl 0
  two_le_Q := two_le_momentQ d hc params
  gamma_pos := by norm_num
  C_Q_nonneg := le_refl 0
  Q_mul_rhoM_gt := by
    unfold momentQ
    have hrho := hc.rhoM_pos
    have hxi : (0 : ℝ) ≤ (params.xi : ℝ) := by positivity
    have hkey :
        (2 + 2 * (params.xi : ℝ) + ((d : ℝ) + 5) / hc.rhoM) * hc.rhoM =
          2 * hc.rhoM + 2 * (params.xi : ℝ) * hc.rhoM + ((d : ℝ) + 5) := by
      field_simp
    rw [hkey]
    nlinarith [mul_nonneg hxi (le_of_lt hrho)]
  holderExponentFloor_nonneg := le_refl 0
  holderExponentFloor_lt_Q :=
    lt_of_lt_of_le (by norm_num) (two_le_momentQ d hc params)
  two_mul_p4_xi_le_Q := by
    show 2 * (params.xi : ℝ) ≤ momentQ d hc params
    unfold momentQ
    have h2 : (0 : ℝ) ≤ ((d : ℝ) + 5) / hc.rhoM :=
      div_nonneg (by positivity) (le_of_lt hc.rhoM_pos)
    linarith

@[simp] theorem hmParams_Q (d : ℕ) (hc : HighContrastExponents d)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    (hmParams d hc params).Q = momentQ d hc params := rfl

@[simp] theorem hmParams_p4Params (d : ℕ) (hc : HighContrastExponents d)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    (hmParams d hc params).p4Params = params := rfl

/-! ## The subthreshold polynomial parameter record

The *estimate* `SubthresholdPolynomialMomentEstimate` for these parameters is
built by the sibling `Subthreshold*` package; QA supplies only the parameter
record.  Any `0 ≤ C_sub` witness satisfies the record's single field
condition; the actual numeric values must be reconciled with the sibling's
estimate at the capstone. -/

/-- **The subthreshold parameter record.** -/
def subParams : SubthresholdPolynomialMomentParameters where
  C_sub := 1
  A_sub := 1
  C_sub_nonneg := by norm_num

/-! ## Entry-scale definitions parameterized by `T`

These mirror the ceiling equations of `P2.lean`.  Since `b = 0`, the
interpolated entry coefficient `p_Q = p₂ + b·(Q-2)/(2δ)` equals `p₂`, so
`scaleN = scaleN2` (recorded in `scaleN_eq_scaleN2`).  The remaining assembly
scales `Nstar = N + ⌈B·log₃(2+T)⌉` and `I = ⌈log(C_A·(2+T)/δ_sc)/|log λ|⌉`
depend on the *outputs* `B, C_A, δ_sc, λ` of the final-assembly constructor
`exists_final_scale_decay_of_main_buffer_and_rawEnergy_scalars`, not on QA
data, so they are instantiated at the capstone. -/

/-- The variance entry scale `N₂ = ⌈p₂·log₃(2+T)⌉`. -/
noncomputable def scaleN2 (d : ℕ) [NeZero d] (hd : 3 ≤ d) (Θ T : ℝ) : ℕ :=
  Nat.ceil ((vpParams d hd Θ).p2 * Real.logb 3 (2 + T))

/-- The interpolated (high-moment) entry scale `N = ⌈p_Q·log₃(2+T)⌉`. -/
noncomputable def scaleN (d : ℕ) [NeZero d] (hd : 3 ≤ d)
    (hc : HighContrastExponents d)
    (params : QuantitativeCoarseGrainedEllipticityParams d) (Θ T : ℝ) : ℕ :=
  Nat.ceil (((hmParams d hc params).varianceUpgrade (vpParams d hd Θ)).p_hm *
    Real.logb 3 (2 + T))

/-- With `b = 0` the interpolated entry coefficient equals `p₂`, so the two
entry scales coincide. -/
theorem scaleN_eq_scaleN2 (d : ℕ) [NeZero d] (hd : 3 ≤ d)
    (hc : HighContrastExponents d)
    (params : QuantitativeCoarseGrainedEllipticityParams d) (Θ T : ℝ) :
    scaleN d hd hc params Θ T = scaleN2 d hd Θ T := by
  unfold scaleN scaleN2
  congr 2
  rw [varianceUpgrade_p_hm]
  simp

end Homogenization
