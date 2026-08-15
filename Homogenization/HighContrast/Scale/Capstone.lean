import Homogenization.HighContrast.Scale.VarianceEstimate
import Homogenization.HighContrast.Scale.WidetildeTheta
import Homogenization.HighContrast.EntryScale.VarianceUpgrade.P2

/-!
# The homogenization-scale capstone

This file assembles the final homogenization-scale decay theorem from the
entry-scale variance final assembly
`Homogenization.HighContrast.EntryScale.exists_final_scale_decay_of_main_buffer_and_variance_scalars`
(`VarianceUpgrade/P2.lean`) and the parameter records / variance bridge of
this directory (`Records.lean`, `VarianceEstimate.lean`).

## What is closed here

* **Subthreshold (`T3`).**  As of 2026-07-23 `P2` no longer exposes a
  subthreshold observable `M_sub` or a `SubthresholdPolynomialMomentEstimate`
  hypothesis: that slot was vacuous (the observable never reached the
  conclusion) and is now discharged internally at the zero observable inside
  `P2`/`t.main`.  The capstone therefore no longer supplies any subthreshold
  plumbing; the subthreshold *parameters* `subParams` are still passed.
* **Assembly (`T4`).**  The full instantiation of the `P2` constructor at the
  QA records, together with the entry-scale ceiling equations, the `N ≤ Nstar`
  side condition, and the variance/subthreshold estimates.
* **Contrast conversion.**  The `P2` conclusion is stated in the moment-enhanced
  contrast `T = widetildeThetaAtScale P 0 hP4`.  Using `T ≤ 4Θ`
  (`widetildeThetaAtScale_le_of_quantitativeCoarseGrainedEllipticity`) and the
  elementary bounds `2+T ≤ 4(2+Θ)`, `log 3 ≤ log(2+Θ)`, the capstone rephrases
  the entry-scale and physical-scale bounds in `Θ`.

## Isolated inputs (hypotheses, not `sorry`)

Three inputs are genuinely external / open and are exposed as hypotheses rather
than fabricated:

* `hc : HighContrastExponents d` — the high-contrast weak-norm exponents.  These
  are external data throughout the development; there is no constructor from
  `params`.
* `loc : LocalizationSmallContrastInput hc` — the localization / small-contrast
  handoff.  Its analytic fields are external inputs; the Section 5.5 dependency
  source `shiftedWidetildeThetaBound_homogenizationScale` bounds the
  *`hP4`-dependent* shifted contrast at `2·section53CoarseFluctuationBeta hP4`,
  which cannot be packaged uniformly against the record's *fixed* `2·hc.beta`
  over all laws.
* `hpath` — the scale-uniform pathwise (C1′) operator-norm budget
  `√(observable) ≤ pathwiseBudgetConstant d · Θ⁶` a.e.  This is exactly the
  `hPathwise` hypothesis of `varianceBlockEstimate_of_thetaEllipticLaw`; it is
  discharged in `Pathwise.lean`.

## Constant dependence

`P2`'s output constants are produced by
`exists_uniform_final_scale_decay_and_physical_scale_of_entry`, whose decay
exponent is `alpha = loc.alpha0` (`Θ`-free) but whose scale constant is
`C_final = Centry + 2·B + Rsc + 1`, where `Centry` carries the per-law buffer
built from the `Θ`-dependent record `hm.varianceUpgrade (vpParams d hd Θ)`.
`C_final` is therefore obtained per-`Θ`; accordingly the capstone quantifies the
scale constants **after** `Θ` (`∀ Θ, ∃ Cscale Ctriadic alpha, …`).
-/

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch04 (RestrictionCoeffLaw RestrictionLawCarrier RestrictionStructuralLaw)
open Homogenization.Book.Ch05 (QuantitativeCoarseGrainedEllipticity)

namespace Homogenization

open Homogenization.HighContrast.EntryScale

/-! ## Elementary contrast-conversion arithmetic -/

/-- The `Θ`-conversion factor `k = 1 + log 4 / log 3 ≥ 1`. -/
noncomputable def contrastLogFactor : ℝ := 1 + Real.log 4 / Real.log 3

theorem contrastLogFactor_pos : 0 < contrastLogFactor := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold contrastLogFactor
  positivity

/-- `log(2+T) ≤ k · log(2+Θ)` whenever `1 ≤ Θ`, `1 ≤ T`, `T ≤ 4Θ`. -/
theorem log_two_add_le (Θ T : ℝ) (hΘ : 1 ≤ Θ) (hT1 : 1 ≤ T) (hT : T ≤ 4 * Θ) :
    Real.log (2 + T) ≤ contrastLogFactor * Real.log (2 + Θ) := by
  have hbase : (0 : ℝ) < 2 + T := by linarith
  have h3le : (3 : ℝ) ≤ 2 + Θ := by linarith
  have hle4 : 2 + T ≤ 4 * (2 + Θ) := by linarith
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlogΘ : Real.log 3 ≤ Real.log (2 + Θ) := Real.log_le_log (by norm_num) h3le
  have h1 : Real.log (2 + T) ≤ Real.log (4 * (2 + Θ)) := Real.log_le_log hbase hle4
  have h2 : Real.log (4 * (2 + Θ)) = Real.log 4 + Real.log (2 + Θ) :=
    Real.log_mul (by norm_num) (by linarith)
  have h3 : Real.log 4 ≤ (Real.log 4 / Real.log 3) * Real.log (2 + Θ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog3]
    exact mul_le_mul_of_nonneg_left hlogΘ hlog4
  calc Real.log (2 + T) ≤ Real.log 4 + Real.log (2 + Θ) := by rw [← h2]; exact h1
    _ ≤ (Real.log 4 / Real.log 3) * Real.log (2 + Θ) + Real.log (2 + Θ) := by linarith
    _ = contrastLogFactor * Real.log (2 + Θ) := by unfold contrastLogFactor; ring

/-- `(2+T)^C ≤ (2+Θ)^(k·C)` (as `rpow`) whenever `1 ≤ Θ`, `1 ≤ T`, `T ≤ 4Θ`,
`0 ≤ C`. -/
theorem rpow_two_add_le (Θ T C : ℝ) (hΘ : 1 ≤ Θ) (hT1 : 1 ≤ T) (hT : T ≤ 4 * Θ)
    (hC : 0 ≤ C) :
    (2 + T) ^ C ≤ (2 + Θ) ^ (contrastLogFactor * C) := by
  have hbaseΘ : (0 : ℝ) < 2 + Θ := by linarith
  have h3le : (3 : ℝ) ≤ 2 + Θ := by linarith
  have hle4 : 2 + T ≤ 4 * (2 + Θ) := by linarith
  -- `4 ≤ (2+Θ)^(logb 3 4)`
  have h4le : (4 : ℝ) ≤ (2 + Θ) ^ (Real.logb 3 4) := by
    have e1 : (3 : ℝ) ^ (Real.logb 3 4) = 4 :=
      Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)
    calc (4 : ℝ) = (3 : ℝ) ^ (Real.logb 3 4) := e1.symm
      _ ≤ (2 + Θ) ^ (Real.logb 3 4) :=
          Real.rpow_le_rpow (by norm_num) h3le
            (Real.logb_nonneg (by norm_num) (by norm_num))
  calc (2 + T) ^ C
      ≤ (4 * (2 + Θ)) ^ C := Real.rpow_le_rpow (by linarith) hle4 hC
    _ = (4 : ℝ) ^ C * (2 + Θ) ^ C := Real.mul_rpow (by norm_num) (le_of_lt hbaseΘ)
    _ ≤ ((2 + Θ) ^ Real.logb 3 4) ^ C * (2 + Θ) ^ C :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by norm_num) h4le hC)
          (Real.rpow_nonneg (le_of_lt hbaseΘ) _)
    _ = (2 + Θ) ^ (Real.logb 3 4 * C) * (2 + Θ) ^ C := by
        rw [← Real.rpow_mul (le_of_lt hbaseΘ)]
    _ = (2 + Θ) ^ (Real.logb 3 4 * C + C) := (Real.rpow_add hbaseΘ _ _).symm
    _ = (2 + Θ) ^ (contrastLogFactor * C) := by
        congr 1; unfold contrastLogFactor Real.logb; ring

/-! ## The capstone theorem (`T4`) -/

/-- **The homogenization-scale capstone.**

Under a `ThetaEllipticLaw Θ P` (with the structural, carrier and quantitative
coarse-grained ellipticity laws at the fixed parameters `params`), the
scale-uniform pathwise budget `hpath`, and the external localization /
small-contrast handoff `loc` at the high-contrast exponents `hc`, the
moment-enhanced ellipticity contrast contracts to `1` at a scale `N0` that is
`O(log(2+Θ))`, with the physical scale `3^{N0}` polynomial in `2+Θ`.

The scale constants are quantified after `Θ` because the entry-scale assembly's
scale constant `C_final` carries the per-law entry buffer (the decay exponent
`alpha = loc.alpha0` is itself `Θ`-free); see the module header.

**Superseded (2026-07-23).**  `CapstoneUniform.lean` proves
`thetaEllipticLaw_implies_homogenizationScale_uniform`, which quantifies
`Cscale, Ctriadic, alpha` **before** `Θ` (depending only on `d, params, hc,
loc`) via the §9 log-shift — the genuine `Θ`-growth statement.  This per-`Θ`
form is retained as the source-faithful shape; prefer the uniform one. -/
-- Intermediate: superseded by the unconditional `homogenizationScale_polynomial_of_unitRange`
-- (`Final.lean`), which discharges `hc, params, loc, hP4, hpath`.
theorem thetaEllipticLaw_implies_homogenizationScale
    {d : ℕ} [NeZero d] (hd : 3 ≤ d) (hc : HighContrastExponents d)
    (params : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    (loc : LocalizationSmallContrastInput hc) (hcp : hc.params = params)
    {Θ : ℝ} (hΘ : 1 ≤ Θ) {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    (hP : RestrictionLawCarrier P) (hStruct : RestrictionStructuralLaw P)
    (hLaw : Homogenization.ThetaEllipticLaw Θ P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hparams : hP4.params = params)
    (hpath : ∀ {j : ℕ} {Q : TriadicCube d}, Q.scale = (j : ℤ) →
      ∀ᵐ a ∂P, Real.sqrt
          (Homogenization.Book.Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
            hP hStruct (j : ℤ) Q a)
        ≤ pathwiseBudgetConstant d * Θ ^ 6) :
    ∃ Cscale Ctriadic alpha : ℝ, 0 < Cscale ∧ 0 < Ctriadic ∧ 0 < alpha ∧
      ∃ N0 : ℕ,
        (∀ n : ℕ,
          Homogenization.Book.Ch05.thetaAtScale hP hStruct ((N0 + n : ℕ) : ℤ) - 1 ≤
            (3 : ℝ) ^ (-alpha * (n : ℝ))) ∧
        (N0 : ℝ) ≤ Cscale * Real.log (2 + Θ) ∧
        (3 : ℝ) ^ (N0 : ℝ) ≤ (2 + Θ) ^ Ctriadic := by
  classical
  set T : ℝ := Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 with hTdef
  -- basic contrast bounds
  have hT1 : 1 ≤ T := one_le_initialWidetildeTheta_of_P4 hP hStruct hP4
  have hT4 : T ≤ 4 * Θ := by
    have h :=
      Homogenization.widetildeThetaAtScale_le_of_quantitativeCoarseGrainedEllipticity
        hLaw hP4
    simpa [hTdef, Homogenization.Book.Ch05.widetildeThetaAtScale_eq] using h
  -- the QA records
  set hm := hmParams d hc params with hmdef
  set vp := vpParams d hd Θ with hvpdef
  have hhmP4 : hm.p4Params = params := hmParams_p4Params d hc params
  -- the entry-scale variance final assembly at the parameter records
  obtain ⟨delta_sc, eps, rho, etaS, etaM, etaSt, decay, coeff, memoryCoeff, K,
      A, lambda, C_A, C_delta, C_memory, L, B, C_resp, C_final, alpha, C_osc,
      C_lin, C_high, _h1, _h2, _h3, _h4, _h5, _h6, _h7, _h8, _h9, _h10, _h11,
      _h12, _h13, _h14, _h15, _h16, _h17, _h18, _h19, _h20, _h21, _h22, _h23,
      _h24, _h25, _h26, _h27, _h28, _h29, _h30, _h31, _h32, hC_final_pos,
      halpha_pos, hmain⟩ :=
    exists_final_scale_decay_of_main_buffer_and_variance_scalars
      params loc hm vp hhmP4 hcp subParams
  -- entry scales, per the ceiling equations of `P2`
  set N2 : ℕ := Nat.ceil (vp.p2 * Real.logb 3 (2 + T)) with hN2def
  set N : ℕ := Nat.ceil ((hm.varianceUpgrade vp).p_hm * Real.logb 3 (2 + T)) with hNdef
  set Nstar : ℕ := N + Nat.ceil (B * Real.logb 3 (2 + T)) with hNstardef
  set I : ℕ :=
    Nat.ceil (Real.log (C_A * (2 + T) / delta_sc) / |Real.log lambda|) with hIdef
  have hNNstar : N ≤ Nstar := by rw [hNstardef]; exact Nat.le_add_right _ _
  -- the variance block estimate from the pathwise budget (`T1` input) + landed bridge
  have hVar :
      VarianceBlockEstimate vp P T N2
        (intermediateCoarseBlockDeviation hP hStruct (fun x : RegCoeffField d => x)) :=
    varianceBlockEstimate_of_thetaEllipticLaw hd hΘ hP hStruct hLaw hP4 N2
      (fun {j} _ {Q} hQ => hpath (j := j) (Q := Q) hQ)
  -- run the assembly (the subthreshold observable is discharged inside `P2`)
  obtain ⟨N0, hdecay, hN0_log, hN0_phys⟩ :=
    hmain hP hStruct hP4 hparams hN2def
      hNdef hNstardef hIdef hNNstar hVar
  -- convert the two scale bounds from `T` to `Θ`
  refine ⟨C_final * contrastLogFactor / Real.log 3, contrastLogFactor * C_final,
    alpha, ?_, ?_, halpha_pos, N0, ?_, ?_, ?_⟩
  · -- 0 < Cscale
    have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have := contrastLogFactor_pos
    positivity
  · -- 0 < Ctriadic
    have := contrastLogFactor_pos
    positivity
  · -- θ-decay: subtract 1 and match the exponent shape
    intro n
    have h := hdecay n
    have he : (3 : ℝ) ^ (-alpha * (n : ℝ)) = (3 : ℝ) ^ (-(alpha * (n : ℝ))) := by
      rw [neg_mul]
    rw [he]
    linarith
  · -- N0 ≤ Cscale · log(2+Θ)
    have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hlogb : Real.logb 3 (2 + T) = Real.log (2 + T) / Real.log 3 := rfl
    have hlogle : Real.log (2 + T) ≤ contrastLogFactor * Real.log (2 + Θ) :=
      log_two_add_le Θ T hΘ hT1 hT4
    have hCfnn : 0 ≤ C_final := le_of_lt hC_final_pos
    calc (N0 : ℝ) ≤ C_final * Real.logb 3 (2 + T) := hN0_log
      _ = C_final * (Real.log (2 + T) / Real.log 3) := by rw [hlogb]
      _ = C_final / Real.log 3 * Real.log (2 + T) := by ring
      _ ≤ C_final / Real.log 3 * (contrastLogFactor * Real.log (2 + Θ)) :=
          mul_le_mul_of_nonneg_left hlogle (by positivity)
      _ = C_final * contrastLogFactor / Real.log 3 * Real.log (2 + Θ) := by ring
  · -- 3^N0 ≤ (2+Θ)^Ctriadic
    have hCfnn : 0 ≤ C_final := le_of_lt hC_final_pos
    have hconv : (2 + T) ^ C_final ≤ (2 + Θ) ^ (contrastLogFactor * C_final) :=
      rpow_two_add_le Θ T C_final hΘ hT1 hT4 hCfnn
    have hcast : (3 : ℝ) ^ (N0 : ℝ) = (3 : ℝ) ^ N0 := Real.rpow_natCast 3 N0
    rw [hcast]
    exact le_trans hN0_phys hconv

end Homogenization
