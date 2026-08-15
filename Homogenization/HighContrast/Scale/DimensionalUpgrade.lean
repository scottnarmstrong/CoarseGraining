import Homogenization.HighContrast.Scale.VarianceEstimate
import Homogenization.HighContrast.EntryScale.EntryScale.P1

/-!
# the dimensional high-moment record (paper §9 log-shift)

The landed variance-to-high-moment upgrade `HighCenteredMomentParameters.varianceUpgrade`
carries the `Θ`-polynomial amplitude in the record's `C_Q` field:
`C_Q = 3^{2δ}·C₂·C₀^{Q-2}` with `C₂ = Cd·Θ⁶`, `C₀ = pathwise·Θ⁶`, so
`C_Q = C_Q^{dim}·Θ^{6(Q-1)}`.  That `Θ`-power is absorbed logarithmically by the
final-assembly buffer, making the scale constant `Θ`-dependent — the defect.

This file re-parametrizes the record along the manuscript's §9 log-shift: it
keeps a **dimensional** `C_Q^{dim}` and pushes the entire `Θ`-power into the
entry-scale **slope** `p_hm`, so that the buffer amplitude is dimensional while
`p_hm · log₃(2+T)` collapses to `O(log(2+Θ))`.  Concretely, for the entry
`N ≥ N_Q + 3(Q-1)·log₃Θ/δ`,
`(varianceUpgrade vp).C_Q = C_Q^{dim}·Θ^{6(Q-1)} ≤ C_Q^{dim}·3^{2δ(N-N_Q)}`,
so the moment estimate re-anchors from `(varianceUpgrade vp, N_Q)` to the
dimensional record `hmDimParams` at the shifted entry `N`.

## Contents

* `HighCenteredMomentEstimate.reanchor` — a general re-anchoring lemma: a
  high-moment estimate transfers to a record with the same `Q`, `Q·γ` and a
  smaller amplitude `C_Q`, entered later, provided the amplitude gap is covered
  by the geometric decay over the entry-scale shift.
* `dimensionalCQ`, `absScale`, `pHmDim` — the dimensional amplitude, the
  `Θ`-absorption scale, and the shifted entry slope.
* `varianceUpgrade_C_Q_le_dimensional` — the amplitude absorption identity.
* `hmDimParams` — the dimensional record (a field update of `varianceUpgrade`).
* `highCenteredMomentEstimate_dimensional_of_varianceBlockEstimate` — the
  dimensional high-moment estimate from a `VarianceBlockEstimate`.
-/

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch04 (RestrictionCoeffLaw RestrictionLawCarrier RestrictionStructuralLaw)
open Homogenization.Book.Ch05 (QuantitativeCoarseGrainedEllipticity)

namespace Homogenization.HighContrast.EntryScale

/-- **Re-anchoring.**  A high centered-moment estimate for `hm1` entered at `N1`
transfers to any record `hm2` with the same moment exponent `Q` and the same
decay `Q·γ`, entered at a later scale `N2 ≥ N1`, provided the (possibly smaller)
amplitude `hm2.C_Q` covers `hm1.C_Q` after the geometric decay across the shift
`N2 - N1`. -/
theorem HighCenteredMomentEstimate.reanchor
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {hc : HighContrastExponents d}
    {hm1 hm2 : HighCenteredMomentParameters d hc} {μ : MeasureTheory.Measure Ω}
    {N1 N2 : ℕ}
    {dev : ℕ → Homogenization.TriadicCube d → Ω → ENNReal}
    (hQ : hm2.Q = hm1.Q)
    (hQg : hm2.Q * hm2.gamma = hm1.Q * hm1.gamma)
    (hN : N1 ≤ N2)
    (hamp :
      hm1.C_Q ≤
        hm2.C_Q * (3 : ℝ) ^ ((hm2.Q * hm2.gamma) * ((N2 - N1 : ℕ) : ℝ)))
    (hHM : HighCenteredMomentEstimate hm1 μ N1 dev) :
    HighCenteredMomentEstimate hm2 μ N2 dev where
  measurable := by
    intro j hj Q hQscale
    have hN1j : N1 ≤ j := hN.trans hj
    have h := hHM.measurable hN1j hQscale
    rw [hQ]
    exact h
  moment_le := by
    intro j hj Q hQscale
    have hN1j : N1 ≤ j := hN.trans hj
    have hmom := hHM.moment_le hN1j hQscale
    rw [hQ]
    refine hmom.trans ?_
    -- envelope comparison
    set g : ℝ := hm2.Q * hm2.gamma with hg_def
    have hg1 : hm1.Q * hm1.gamma = g := hQg.symm
    have hC1_nonneg : 0 ≤ hm1.C_Q := hm1.C_Q_nonneg
    have hC2_nonneg : 0 ≤ hm2.C_Q := hm2.C_Q_nonneg
    -- natural-subtraction split `(j - N1) = (j - N2) + (N2 - N1)`
    have hsplit : ((j - N1 : ℕ) : ℝ) = ((j - N2 : ℕ) : ℝ) + ((N2 - N1 : ℕ) : ℝ) := by
      have : j - N1 = (j - N2) + (N2 - N1) := by omega
      rw [this]; push_cast; ring
    have hbc : (3 : ℝ) ^ (g * ((N2 - N1 : ℕ) : ℝ)) *
        (3 : ℝ) ^ (-g * ((N2 - N1 : ℕ) : ℝ)) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      simp
    have ha_nonneg : 0 ≤ (3 : ℝ) ^ (-g * ((j - N2 : ℕ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hc_nonneg : 0 ≤ (3 : ℝ) ^ (-g * ((N2 - N1 : ℕ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hreal :
        hm1.C_Q * (3 : ℝ) ^ (-(hm1.Q * hm1.gamma) * ((j - N1 : ℕ) : ℝ)) ≤
          hm2.C_Q * (3 : ℝ) ^ (-(hm2.Q * hm2.gamma) * ((j - N2 : ℕ) : ℝ)) := by
      rw [hg1, ← hg_def]
      have hexp :
          (3 : ℝ) ^ (-g * ((j - N1 : ℕ) : ℝ)) =
            (3 : ℝ) ^ (-g * ((j - N2 : ℕ) : ℝ)) *
              (3 : ℝ) ^ (-g * ((N2 - N1 : ℕ) : ℝ)) := by
        rw [hsplit, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 1; ring
      rw [hexp]
      calc
        hm1.C_Q *
            ((3 : ℝ) ^ (-g * ((j - N2 : ℕ) : ℝ)) *
              (3 : ℝ) ^ (-g * ((N2 - N1 : ℕ) : ℝ)))
            ≤ (hm2.C_Q * (3 : ℝ) ^ (g * ((N2 - N1 : ℕ) : ℝ))) *
                ((3 : ℝ) ^ (-g * ((j - N2 : ℕ) : ℝ)) *
                  (3 : ℝ) ^ (-g * ((N2 - N1 : ℕ) : ℝ))) := by
              apply mul_le_mul_of_nonneg_right hamp
              exact mul_nonneg ha_nonneg hc_nonneg
        _ = hm2.C_Q * (3 : ℝ) ^ (-g * ((j - N2 : ℕ) : ℝ)) *
              ((3 : ℝ) ^ (g * ((N2 - N1 : ℕ) : ℝ)) *
                (3 : ℝ) ^ (-g * ((N2 - N1 : ℕ) : ℝ))) := by ring
        _ = hm2.C_Q * (3 : ℝ) ^ (-g * ((j - N2 : ℕ) : ℝ)) := by
              rw [hbc]; ring
    rw [highCenteredMomentEnvelope_eq hm1 N1 j, highCenteredMomentEnvelope_eq hm2 N2 j]
    exact ENNReal.ofReal_le_ofReal hreal

end Homogenization.HighContrast.EntryScale

namespace Homogenization

open Homogenization.HighContrast.EntryScale

variable {d : ℕ}

/-- The **dimensional** high-moment amplitude
`C_Q^{dim} = 3^{2δ}·Cd·pathwise^{Q-2}`, i.e. `(varianceUpgrade vp).C_Q` with the
`Θ`-powers of `C₂ = Cd·Θ⁶` and `C₀ = pathwise·Θ⁶` stripped out. -/
noncomputable def dimensionalCQ [NeZero d] (hd : 3 ≤ d)
    (hc : HighContrastExponents d)
    (params : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d) :
    ℝ :=
  (3 : ℝ) ^ (2 * varianceDelta d) * landedVarianceConstant d hd *
    pathwiseBudgetConstant d ^ (momentQ d hc params - 2)

theorem dimensionalCQ_nonneg [NeZero d] (hd : 3 ≤ d)
    (hc : HighContrastExponents d)
    (params : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d) :
    0 ≤ dimensionalCQ hd hc params := by
  unfold dimensionalCQ
  have h1 : 0 ≤ (3 : ℝ) ^ (2 * varianceDelta d) := Real.rpow_nonneg (by norm_num) _
  have h2 : 0 ≤ landedVarianceConstant d hd := landedVarianceConstant_nonneg d hd
  have h3 : 0 ≤ pathwiseBudgetConstant d ^ (momentQ d hc params - 2) :=
    Real.rpow_nonneg (pathwiseBudgetConstant_nonneg d) _
  positivity

/-- The `Θ`-absorption scale `3(Q-1)·log₃Θ/δ`: the entry-scale shift needed for
`Θ^{6(Q-1)} ≤ 3^{2δ·shift}`. -/
noncomputable def absScale (hc : HighContrastExponents d)
    (params : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    (Θ : ℝ) : ℝ :=
  3 * (momentQ d hc params - 1) * Real.logb 3 Θ / varianceDelta d

theorem absScale_nonneg [NeZero d] (hd : 3 ≤ d) (hc : HighContrastExponents d)
    (params : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    {Θ : ℝ} (hΘ : 1 ≤ Θ) :
    0 ≤ absScale hc params Θ := by
  unfold absScale
  have hQ : (2 : ℝ) ≤ momentQ d hc params := two_le_momentQ d hc params
  have hlog : 0 ≤ Real.logb 3 Θ :=
    Real.logb_nonneg (by norm_num) hΘ
  have hδ : 0 < varianceDelta d := varianceDelta_pos hd
  have hnum : 0 ≤ 3 * (momentQ d hc params - 1) * Real.logb 3 Θ := by
    have : 0 ≤ momentQ d hc params - 1 := by linarith
    positivity
  positivity

/-- The shifted entry slope `p_hm' = 1 + (absScale + 2)/log₃(2+T)`.  Chosen so
that `p_hm' · log₃(2+T) = log₃(2+T) + absScale + 2`, which both dominates the
absorption scale (making the amplitude dimensional) and stays `O(log(2+Θ))`. -/
noncomputable def pHmDim [NeZero d] (hc : HighContrastExponents d)
    (params : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    (Θ T : ℝ) : ℝ :=
  1 + (absScale hc params Θ + 2) / Real.logb 3 (2 + T)

theorem pHmDim_nonneg [NeZero d] (hd : 3 ≤ d) (hc : HighContrastExponents d)
    (params : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    {Θ T : ℝ} (hΘ : 1 ≤ Θ) (hT : 1 ≤ T) :
    0 ≤ pHmDim hc params Θ T := by
  unfold pHmDim
  have habs : 0 ≤ absScale hc params Θ := absScale_nonneg hd hc params hΘ
  have hlogT : (1 : ℝ) ≤ Real.logb 3 (2 + T) := one_le_logb_three_two_add hT
  have hdiv : 0 ≤ (absScale hc params Θ + 2) / Real.logb 3 (2 + T) :=
    div_nonneg (by linarith) (by linarith)
  linarith

/-- `pHmDim · log₃(2+T) = log₃(2+T) + absScale + 2`. -/
theorem pHmDim_mul_logb [NeZero d] (hc : HighContrastExponents d)
    (params : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    {Θ T : ℝ} (hT : 1 ≤ T) :
    pHmDim hc params Θ T * Real.logb 3 (2 + T) =
      Real.logb 3 (2 + T) + absScale hc params Θ + 2 := by
  have hlogT : (1 : ℝ) ≤ Real.logb 3 (2 + T) := one_le_logb_three_two_add hT
  have hne : Real.logb 3 (2 + T) ≠ 0 := ne_of_gt (by linarith)
  unfold pHmDim
  field_simp
  ring

/-- **Amplitude absorption (§9 log-shift).**  The `Θ`-polynomial amplitude of the
landed upgraded record is dominated by the dimensional amplitude times the
geometric decay across the entry-scale shift, once the shift covers the
absorption scale:
`(varianceUpgrade vp).C_Q = C_Q^{dim}·Θ^{6(Q-1)} ≤ C_Q^{dim}·3^{2δ(N-N_Q)}`. -/
theorem varianceUpgrade_C_Q_le_dimensional [NeZero d] (hd : 3 ≤ d)
    (hc : HighContrastExponents d)
    (params : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    {Θ : ℝ} (hΘ : 1 ≤ Θ) {NQ N : ℕ}
    (hshift : absScale hc params Θ ≤ ((N - NQ : ℕ) : ℝ)) :
    ((hmParams d hc params).varianceUpgrade (vpParams d hd Θ)).C_Q ≤
      dimensionalCQ hd hc params *
        (3 : ℝ) ^ ((2 * varianceDelta d) * ((N - NQ : ℕ) : ℝ)) := by
  have hΘpos : (0 : ℝ) < Θ := by linarith
  have hM_pos : (0 : ℝ) < Θ ^ 6 := by positivity
  have hδpos : 0 < varianceDelta d := varianceDelta_pos hd
  have hδne : varianceDelta d ≠ 0 := ne_of_gt hδpos
  have hCd_nonneg : 0 ≤ landedVarianceConstant d hd := landedVarianceConstant_nonneg d hd
  have hpw_nonneg : 0 ≤ pathwiseBudgetConstant d := pathwiseBudgetConstant_nonneg d
  -- `varianceUpgrade C_Q = dimensionalCQ · (Θ⁶)^{Q-1}`
  have hcomb :
      (Θ ^ 6) ^ (momentQ d hc params - 1) =
        (Θ ^ 6) * (Θ ^ 6) ^ (momentQ d hc params - 2) := by
    have h1 : momentQ d hc params - 1 = 1 + (momentQ d hc params - 2) := by ring
    rw [h1, Real.rpow_add hM_pos, Real.rpow_one]
  have hCQ_eq :
      ((hmParams d hc params).varianceUpgrade (vpParams d hd Θ)).C_Q =
        dimensionalCQ hd hc params * (Θ ^ 6) ^ (momentQ d hc params - 1) := by
    rw [varianceUpgrade_C_Q, vpParams_delta, vpParams_C2, vpParams_C0, hmParams_Q]
    unfold dimensionalCQ
    rw [Real.mul_rpow hpw_nonneg (le_of_lt hM_pos), hcomb]
    ring
  -- `(Θ⁶)^{Q-1} = 3^{2δ·absScale}`
  have hlogb6 : Real.logb 3 (Θ ^ 6) = 6 * Real.logb 3 Θ := by
    rw [Real.logb_pow]; norm_num
  have hpow_eq :
      (Θ ^ 6) ^ (momentQ d hc params - 1) =
        (3 : ℝ) ^ ((2 * varianceDelta d) * absScale hc params Θ) := by
    have step1 :
        (Θ ^ 6) ^ (momentQ d hc params - 1) =
          (3 : ℝ) ^ (Real.logb 3 (Θ ^ 6) * (momentQ d hc params - 1)) := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
        Real.rpow_logb (by norm_num) (by norm_num) hM_pos]
    rw [step1, hlogb6]
    congr 1
    unfold absScale
    field_simp
    ring
  rw [hCQ_eq, hpow_eq]
  apply mul_le_mul_of_nonneg_left _ (dimensionalCQ_nonneg hd hc params)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
  exact mul_le_mul_of_nonneg_left hshift (by positivity)

/-- **The `Θ`-free dimensional high-moment record** (§9 log-shift): the field
update of the landed `varianceUpgrade` record (instantiated at the fixed
`Θ = 1`, since `Q`, `γ`, `p4Params` are `Θ`-independent) with the `Θ`-polynomial
amplitude `C_Q` replaced by the dimensional `dimensionalCQ` and a placeholder
entry slope `p_hm := 0` (the entry slope is supplied separately as the free
parameter `q` of `…_rawEnergy_scalars_uniform`).  This record is genuinely free
of `Θ`, so the final assembly returns a dimensional `Cdim` before `∀Θ`. -/
noncomputable def hmDimFree [NeZero d] (hd : 3 ≤ d) (hc : HighContrastExponents d)
    (params : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d) :
    HighCenteredMomentParameters d hc :=
  { (hmParams d hc params).varianceUpgrade (vpParams d hd 1) with
    p_hm := 0
    C_Q := dimensionalCQ hd hc params
    p_hm_nonneg := le_refl 0
    C_Q_nonneg := dimensionalCQ_nonneg hd hc params }

@[simp] theorem hmDimFree_C_Q [NeZero d] (hd : 3 ≤ d) (hc : HighContrastExponents d)
    (params : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d) :
    (hmDimFree hd hc params).C_Q = dimensionalCQ hd hc params := rfl

theorem hmDimFree_p4Params [NeZero d] (hd : 3 ≤ d) (hc : HighContrastExponents d)
    (params : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d) :
    (hmDimFree hd hc params).p4Params = params := by
  show ((hmParams d hc params).varianceUpgrade (vpParams d hd 1)).p4Params = params
  rw [varianceUpgrade_p4Params, hmParams_p4Params]

/-- The record decay `Q·γ = 2δ` of the dimensional record. -/
theorem hmDimFree_Q_mul_gamma [NeZero d] (hd : 3 ≤ d) (hc : HighContrastExponents d)
    (params : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d) :
    (hmDimFree hd hc params).Q * (hmDimFree hd hc params).gamma =
      2 * varianceDelta d := by
  show ((hmParams d hc params).varianceUpgrade (vpParams d hd 1)).Q *
      ((hmParams d hc params).varianceUpgrade (vpParams d hd 1)).gamma =
    2 * varianceDelta d
  rw [varianceUpgrade_Q, varianceUpgrade_gamma, hmParams_Q, vpParams_delta]
  have hmQ_ne : momentQ d hc params ≠ 0 :=
    ne_of_gt (by linarith [two_le_momentQ d hc params])
  field_simp

/-- **The dimensional high-moment estimate** from a `VarianceBlockEstimate`.
Runs the landed variance-to-moment interpolation at the QA records (entry
`N_Q = ⌈p₂·log₃(2+T)⌉`), then re-anchors to the `Θ`-free dimensional record at
the shifted entry `N = ⌈pHmDim·log₃(2+T)⌉`, absorbing the `Θ`-polynomial
amplitude into the entry-scale shift. -/
theorem highCenteredMomentEstimate_dimensional_of_varianceBlockEstimate
    [NeZero d] (hd : 3 ≤ d) (hc : HighContrastExponents d)
    (params : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {Θ T : ℝ} (hΘ : 1 ≤ Θ) (hT : 1 ≤ T) {N2 N : ℕ}
    {dev : ℕ → Homogenization.TriadicCube d → Ω → ENNReal}
    (hN2 : N2 = Nat.ceil ((vpParams d hd Θ).p2 * Real.logb 3 (2 + T)))
    (hN : N = Nat.ceil (pHmDim hc params Θ T * Real.logb 3 (2 + T)))
    (hVar : VarianceBlockEstimate (vpParams d hd Θ) μ T N2 dev) :
    HighCenteredMomentEstimate (hmDimFree hd hc params) μ N dev := by
  set NQ := Nat.ceil
    (((hmParams d hc params).varianceUpgrade (vpParams d hd Θ)).p_hm *
      Real.logb 3 (2 + T)) with hNQdef
  have hUp :=
    HighCenteredMomentEstimate.of_varianceBlockEstimate
      (hmParams d hc params) (vpParams d hd Θ) hT hN2 hNQdef hVar
  have hlogT : (1 : ℝ) ≤ Real.logb 3 (2 + T) := one_le_logb_three_two_add hT
  have habs : 0 ≤ absScale hc params Θ := absScale_nonneg hd hc params hΘ
  have hp_hm_up :
      ((hmParams d hc params).varianceUpgrade (vpParams d hd Θ)).p_hm = 1 := by
    rw [varianceUpgrade_p_hm, vpParams_p2, vpParams_b]; ring
  -- `NQ ≤ N`
  have hNQ_le_N : NQ ≤ N := by
    rw [hNQdef, hN]
    apply Nat.ceil_le_ceil
    rw [hp_hm_up, one_mul, pHmDim_mul_logb hc params hT]
    linarith
  -- absorption shift `absScale ≤ N - NQ`
  have hshift : absScale hc params Θ ≤ ((N - NQ : ℕ) : ℝ) := by
    have hNlb : pHmDim hc params Θ T * Real.logb 3 (2 + T) ≤ (N : ℝ) := by
      rw [hN]; exact Nat.le_ceil _
    rw [pHmDim_mul_logb hc params hT] at hNlb
    have hNQub : (NQ : ℝ) ≤ Real.logb 3 (2 + T) + 1 := by
      rw [hNQdef, hp_hm_up, one_mul]
      have hlt := Nat.ceil_lt_add_one
        (show (0 : ℝ) ≤ Real.logb 3 (2 + T) by linarith)
      linarith
    have hcast : ((N - NQ : ℕ) : ℝ) = (N : ℝ) - (NQ : ℝ) := Nat.cast_sub hNQ_le_N
    rw [hcast]; linarith
  -- amplitude covered
  have hamp :
      ((hmParams d hc params).varianceUpgrade (vpParams d hd Θ)).C_Q ≤
        (hmDimFree hd hc params).C_Q *
          (3 : ℝ) ^ (((hmDimFree hd hc params).Q *
            (hmDimFree hd hc params).gamma) * ((N - NQ : ℕ) : ℝ)) := by
    rw [hmDimFree_C_Q, hmDimFree_Q_mul_gamma]
    exact varianceUpgrade_C_Q_le_dimensional hd hc params hΘ hshift
  exact HighCenteredMomentEstimate.reanchor
    (hm1 := (hmParams d hc params).varianceUpgrade (vpParams d hd Θ))
    (hm2 := hmDimFree hd hc params)
    rfl rfl hNQ_le_N hamp hUp

end Homogenization
