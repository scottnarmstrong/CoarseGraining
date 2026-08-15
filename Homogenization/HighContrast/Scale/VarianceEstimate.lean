import Homogenization.HighContrast.Scale.Records
import Homogenization.HighContrast.EntryScale.DeterministicAlgebra.P3
import Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.NormalizedBlocks

/-!
# The variance block estimate from a `ThetaEllipticLaw`

This file assembles a `VarianceBlockEstimate` for the intermediate centered
coarse-block deviation `intermediateCoarseBlockDeviation hP hStruct id` out of
the variance bridge `integral_fullBlockNormalizedFluctuation_le`.

## The three fields

* `aemeasurable` — the deviation is `ENNReal.ofReal ∘ √` of the integrable
  observable `fullBlockNormalizedFluctuationOperatorNormSqAtScale`, hence
  a.e.-measurable.
* `second_moment_le` — the central bridge.  The observable identity
  `fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq_terminal_norm_sq`
  makes `deviation² = ofReal(observable)`; a real Bochner ↔ `∫⁻` conversion
  (nonnegativity + `(P4)` integrability) turns the `∫⁻` into `ofReal (∫ …)`;
  stationarity (`…_eq_originCube_from_P4`) reduces to the origin cube; the
  landed bound closes it at `Cd·Θ⁶·(3^j)^{-β}`; and the entry-scale envelope
  absorption `Cd·Θ⁶·3^{-βj} ≤ C₂·3^{-β(j-N₂)}` (with `C₂ = Cd·Θ⁶`,
  `2δ = β`, and the favorable factor `3^{β·N₂} ≥ 1`) finishes.

* `pathwise_le` — the deterministic C1′-type ellipticity bound
  `‖D·(A(Q)−Ā)·D‖ ≤ 48·|BlockCoord d|³·Θ⁶` a.e., i.e.
  `√(observable) ≤ pathwiseBudgetConstant d · Θ⁶` a.e.  The landed machinery
  provides a *good-scale* normalized annealed-quadratic bound
  (`normalizedAnnealedQuadratic_le_one_add_delta_mul_dotProduct_of_good`), but
  **no scale-uniform a.e. operator-norm bound** exists yet (the annealed
  `c₀`-quadratic bound requires good-scale hypotheses).  We therefore expose
  exactly this a.e. bound as the single hypothesis `hPathwise`; it is discharged
  from the coarse-ellipticity machinery in `Pathwise.lean`.
-/

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch04 (RestrictionCoeffLaw RestrictionLawCarrier RestrictionStructuralLaw)
open Homogenization.Book.Ch05 (QuantitativeCoarseGrainedEllipticity)
open Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale
  (integrable_fullBlockNormalizedFluctuationOperatorNormSqAtScale_from_P4_of_nonneg_scale
    integral_fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq_originCube_from_P4
    fullBlockNormalizedFluctuationOperatorNormSqAtScale_nonneg)

namespace Homogenization

open Homogenization.HighContrast.EntryScale

variable {d : ℕ}

/-- Shorthand: the manuscript normalized full-block fluctuation observable at
centre scale `j` on the cube `Q`. -/
private noncomputable def obs [NeZero d] {P : RestrictionCoeffLaw d}
    (hP : RestrictionLawCarrier P) (hStruct : RestrictionStructuralLaw P) (j : ℕ) (Q : TriadicCube d) :
    RegCoeffField d → ℝ :=
  fun a => Homogenization.Book.Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
    hP hStruct (j : ℤ) Q a

/-- The intermediate centered coarse-block deviation of the identity process is
`ENNReal.ofReal` of the square root of the manuscript observable. -/
theorem intermediateCoarseBlockDeviation_id_eq_ofReal_sqrt [NeZero d]
    {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P) (hStruct : RestrictionStructuralLaw P)
    (j : ℕ) (Q : TriadicCube d) (a : RegCoeffField d) :
    intermediateCoarseBlockDeviation hP hStruct (fun x : RegCoeffField d => x) j Q a =
      ENNReal.ofReal (Real.sqrt (obs hP hStruct j Q a)) := by
  have hid :=
    fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq_terminal_norm_sq
      hP hStruct j Q a
  unfold intermediateCoarseBlockDeviation intermediateCenteredFullBlockDeviation
    coarseFullBlockMatrixAtCubeProcess obs
  dsimp only
  congr 1
  rw [hid, Real.sqrt_sq (fullBlockOperatorNorm_nonneg _)]

/-- The `ℝ`-square of the deviation is `ENNReal.ofReal` of the observable. -/
theorem intermediateCoarseBlockDeviation_id_rpow_two [NeZero d]
    {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P) (hStruct : RestrictionStructuralLaw P)
    (j : ℕ) (Q : TriadicCube d) (a : RegCoeffField d) :
    intermediateCoarseBlockDeviation hP hStruct (fun x : RegCoeffField d => x) j Q a
        ^ (2 : ℝ) =
      ENNReal.ofReal (obs hP hStruct j Q a) := by
  rw [intermediateCoarseBlockDeviation_id_eq_ofReal_sqrt hP hStruct j Q a]
  have hnn : 0 ≤ obs hP hStruct j Q a :=
    fullBlockNormalizedFluctuationOperatorNormSqAtScale_nonneg hP hStruct (j : ℤ) Q a
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    Real.sq_sqrt hnn]

/-! ## The real-arithmetic envelope absorption -/

/-- The landed absolute bound `Cd·Θ⁶·(3^j)^{-β}` is dominated by the variance
envelope value `C₂·3^{-2δ(j-N₂)}` entered at `N₂`, with `C₂ = Cd·Θ⁶` and
`2δ = β = (d-2)/(d-1)`.  The favorable factor is `3^{β·N₂} ≥ 1`. -/
theorem landed_le_varianceEnvelope_real [NeZero d] (hd : 3 ≤ d) (Θ : ℝ) {N2 j : ℕ}
    (hj : N2 ≤ j) :
    landedVarianceConstant d hd * Θ ^ 6 *
        ((3 : ℝ) ^ (j : ℤ)) ^ (-((d : ℝ) - 2) / ((d : ℝ) - 1)) ≤
      (vpParams d hd Θ).C2 *
        (3 : ℝ) ^ (-(2 * (vpParams d hd Θ).delta) * ((j - N2 : ℕ) : ℝ)) := by
  have hd3 : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  set β : ℝ := ((d : ℝ) - 2) / ((d : ℝ) - 1) with hβdef
  have hβ_eq : 2 * (vpParams d hd Θ).delta = β := by
    rw [vpParams_delta]; exact two_mul_varianceDelta hd
  have hβ_nonneg : 0 ≤ β := by
    rw [hβdef]; apply div_nonneg <;> linarith
  have hC2_nonneg : 0 ≤ landedVarianceConstant d hd * Θ ^ 6 :=
    mul_nonneg (landedVarianceConstant_nonneg d hd) (by positivity)
  -- rewrite the left base as a `3`-rpow
  have hLbase : ((3 : ℝ) ^ (j : ℤ)) ^ (-((d : ℝ) - 2) / ((d : ℝ) - 1)) =
      (3 : ℝ) ^ ((j : ℝ) * (-β)) := by
    rw [← Real.rpow_intCast (3 : ℝ) (j : ℤ)]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    rw [hβdef]; ring
  -- rewrite the right exponent
  have hRexp : -(2 * (vpParams d hd Θ).delta) * ((j - N2 : ℕ) : ℝ) =
      -β * ((j : ℝ) - (N2 : ℝ)) := by
    rw [hβ_eq, Nat.cast_sub hj]
  rw [hLbase, vpParams_C2, hRexp]
  -- exponent comparison: -β·j ≤ -β·(j - N2)  ⇔  0 ≤ β·N2
  have hexp : (j : ℝ) * (-β) ≤ -β * ((j : ℝ) - (N2 : ℝ)) := by
    have hN2 : 0 ≤ β * (N2 : ℝ) := mul_nonneg hβ_nonneg (Nat.cast_nonneg _)
    nlinarith [hN2]
  have hpow :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
  exact mul_le_mul_of_nonneg_left hpow hC2_nonneg

/-! ## The variance block estimate -/

/-- **The variance block estimate.**  Under a
`ThetaEllipticLaw Θ P` and the structural + quantitative-ellipticity laws, the
intermediate centered coarse-block deviation of the identity process satisfies
the `VarianceBlockEstimate` at the QA variance parameters `vpParams d hd Θ`,
entered at any scale `N2`, with `T = widetildeThetaAtScale P 0 hP4`.

The pathwise (C1′) a.e. operator-norm bound is supplied as the hypothesis
`hPathwise`; every other field is discharged from landed machinery. -/
theorem varianceBlockEstimate_of_thetaEllipticLaw [NeZero d] (hd : 3 ≤ d)
    {Θ : ℝ} (hΘ : 1 ≤ Θ) {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    (hP : RestrictionLawCarrier P) (hStruct : RestrictionStructuralLaw P)
    (hLaw : Homogenization.ThetaEllipticLaw Θ P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (N2 : ℕ)
    (hPathwise : ∀ {j : ℕ}, N2 ≤ j → ∀ {Q : TriadicCube d}, Q.scale = (j : ℤ) →
      ∀ᵐ a ∂P, Real.sqrt (obs hP hStruct j Q a) ≤ pathwiseBudgetConstant d * Θ ^ 6) :
    VarianceBlockEstimate (vpParams d hd Θ) P
      (Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) N2
      (intermediateCoarseBlockDeviation hP hStruct
        (fun x : RegCoeffField d => x)) where
  aemeasurable := by
    intro j hj Q hQscale
    have hQ_nonneg : 0 ≤ Q.scale := by rw [hQscale]; exact_mod_cast Nat.zero_le j
    have hobs_int : Integrable (obs hP hStruct j Q) P :=
      integrable_fullBlockNormalizedFluctuationOperatorNormSqAtScale_from_P4_of_nonneg_scale
        hP hStruct hP4 (j : ℤ) Q hQ_nonneg
    have hobs_aem : AEMeasurable (obs hP hStruct j Q) P :=
      hobs_int.aestronglyMeasurable.aemeasurable
    have hsqrt_aem : AEMeasurable (fun a => Real.sqrt (obs hP hStruct j Q a)) P :=
      Real.continuous_sqrt.measurable.comp_aemeasurable hobs_aem
    refine (ENNReal.measurable_ofReal.comp_aemeasurable hsqrt_aem).congr ?_
    filter_upwards with a
    exact (intermediateCoarseBlockDeviation_id_eq_ofReal_sqrt hP hStruct j Q a).symm
  pathwise_le := by
    intro j hj Q hQscale
    filter_upwards [hPathwise hj hQscale] with a ha
    rw [intermediateCoarseBlockDeviation_id_eq_ofReal_sqrt hP hStruct j Q a]
    unfold variancePathwiseBound
    rw [vpParams_b, vpParams_C0]
    rw [Real.rpow_zero, mul_one]
    exact ENNReal.ofReal_le_ofReal ha
  second_moment_le := by
    intro j hj Q hQscale
    have hQ_nonneg : 0 ≤ Q.scale := by rw [hQscale]; exact_mod_cast Nat.zero_le j
    have hj_int_nonneg : (0 : ℤ) ≤ (j : ℤ) := by exact_mod_cast Nat.zero_le j
    have hobs_int : Integrable (obs hP hStruct j Q) P :=
      integrable_fullBlockNormalizedFluctuationOperatorNormSqAtScale_from_P4_of_nonneg_scale
        hP hStruct hP4 (j : ℤ) Q hQ_nonneg
    have hobs_nonneg_ae : (0 : RegCoeffField d → ℝ) ≤ᵐ[P] obs hP hStruct j Q :=
      Filter.Eventually.of_forall fun a =>
        fullBlockNormalizedFluctuationOperatorNormSqAtScale_nonneg hP hStruct (j : ℤ) Q a
    -- rewrite the squared integrand
    have hint_eq :
        ∫⁻ a, intermediateCoarseBlockDeviation hP hStruct
            (fun x : RegCoeffField d => x) j Q a ^ (2 : ℝ) ∂P =
          ENNReal.ofReal (∫ a, obs hP hStruct j Q a ∂P) := by
      rw [ofReal_integral_eq_lintegral_ofReal hobs_int hobs_nonneg_ae]
      exact lintegral_congr fun a =>
        intermediateCoarseBlockDeviation_id_rpow_two hP hStruct j Q a
    rw [hint_eq]
    -- stationarity to the origin cube
    have hstat :
        ∫ a, obs hP hStruct j Q a ∂P =
          ∫ a, obs hP hStruct j (originCube d Q.scale) a ∂P :=
      integral_fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq_originCube_from_P4
        hP hStruct hP4 (j : ℤ) Q hQ_nonneg
    -- the origin cube at scale `j`
    have horigin : originCube d Q.scale = originCube d (j : ℤ) := by rw [hQscale]
    -- landed bound at the origin cube
    have hlanded :
        ∫ a, obs hP hStruct j (originCube d (j : ℤ)) a ∂P ≤
          landedVarianceConstant d hd * Θ ^ 6 *
            ((3 : ℝ) ^ (j : ℤ)) ^ (-((d : ℝ) - 2) / ((d : ℝ) - 1)) :=
      landedVarianceConstant_spec d hd hΘ hP hStruct hLaw (m := (j : ℤ)) hj_int_nonneg
    -- assemble the real bound on the integral
    have hInt_le :
        ∫ a, obs hP hStruct j Q a ∂P ≤
          landedVarianceConstant d hd * Θ ^ 6 *
            ((3 : ℝ) ^ (j : ℤ)) ^ (-((d : ℝ) - 2) / ((d : ℝ) - 1)) := by
      rw [hstat, horigin]
      exact hlanded
    -- push through `ofReal` and finish by envelope absorption
    refine le_trans (ENNReal.ofReal_le_ofReal hInt_le) ?_
    unfold varianceMomentEnvelope
    exact ENNReal.ofReal_le_ofReal (landed_le_varianceEnvelope_real hd Θ hj)

end Homogenization
