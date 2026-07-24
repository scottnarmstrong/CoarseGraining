import Homogenization.HighContrast.Scale.Capstone
import Homogenization.HighContrast.Scale.DimensionalUpgrade
import Homogenization.HighContrast.EntryScale.FinalAssembly.P4Uniform

/-!
# the **uniform** homogenization-scale capstone (constants before `Θ`)

The landed `thetaEllipticLaw_implies_homogenizationScale` (`Capstone.lean`)
quantifies its scale constants *after* `Θ`, so `N0 ≤ Cscale·log(2+Θ)` is vacuous
as a growth statement.  This file proves the uniform version with the
constants `Cscale, Ctriadic, alpha` quantified **before** `Θ`, depending only on
the dimensional data `(d, params, hc, loc)`.

The mechanism is the manuscript's §9 log-shift (`DimensionalUpgrade.lean`): the
`Θ`-polynomial amplitude of the high-moment envelope is absorbed into a
`Θ,T`-dependent entry slope `pHmDim`, leaving a dimensional amplitude
`dimensionalCQ`.  The final assembly is therefore run **once**, before `Θ`, at
the `Θ`-free record `hmDimFree` with a free entry slope
(`…_rawEnergy_scalars_uniform`), yielding a dimensional `Cdim`.  Per law, the
entry slope `q := pHmDim` is supplied together with the shifted-anchor moment
estimate, and the affine bound `N0 ≤ (pHmDim + Cdim)·log₃(2+T)` converts to
`N0 ≤ Cscale·log(2+Θ)` because `pHmDim·log₃(2+T) = log₃(2+T) + absScale + 2` and
`absScale ≤ (3(Q-1)/δ)·log₃(2+Θ)`.
-/

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch04 (CoeffLaw LawCarrier StructuralLaw)
open Homogenization.Book.Ch05 (QuantitativeCoarseGrainedEllipticity)

namespace Homogenization

open Homogenization.HighContrast.EntryScale

/-- **the uniform homogenization-scale capstone.**

Identical conclusion to `thetaEllipticLaw_implies_homogenizationScale`, except the
scale/triadic constants and the decay exponent are chosen **before** `Θ`,
depending only on `(d, params, hc, loc)`.  This supersedes the per-`Θ` capstone
as a genuine `Θ`-growth statement (`N0 = O(log(2+Θ))` uniformly).

**Intermediate.** This still takes the records `hc, params, loc` and the
witness `hP4` as hypotheses; the unconditional public headline that discharges
all of them is `homogenizationScale_polynomial_of_unitRange` (`Final.lean`). -/
theorem thetaEllipticLaw_implies_homogenizationScale_uniform
    {d : ℕ} [NeZero d] (hd : 3 ≤ d) (hc : HighContrastExponents d)
    (params : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    (loc : LocalizationSmallContrastInput hc) (hcp : hc.params = params) :
    ∃ Cscale Ctriadic alpha : ℝ, 0 < Cscale ∧ 0 < Ctriadic ∧ 0 < alpha ∧
      ∀ {Θ : ℝ} (_hΘ : 1 ≤ Θ) {P : CoeffLaw d} [IsProbabilityMeasure P]
        (hP : LawCarrier P) (hStruct : StructuralLaw P)
        (hLaw : Homogenization.ThetaEllipticLaw Θ P)
        (hP4 : QuantitativeCoarseGrainedEllipticity P)
        (_hparams : hP4.params = params)
        (_hpath : ∀ {j : ℕ} {Q : TriadicCube d}, Q.scale = (j : ℤ) →
          ∀ᵐ a ∂P, Real.sqrt
              (Homogenization.Book.Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
                hP hStruct (j : ℤ) Q a)
            ≤ pathwiseBudgetConstant d * Θ ^ 6),
      ∃ N0 : ℕ,
        (∀ n : ℕ,
          Homogenization.Book.Ch05.thetaAtScale hP hStruct ((N0 + n : ℕ) : ℤ) - 1 ≤
            (3 : ℝ) ^ (-alpha * (n : ℝ))) ∧
        (N0 : ℝ) ≤ Cscale * Real.log (2 + Θ) ∧
        (3 : ℝ) ^ (N0 : ℝ) ≤ (2 + Θ) ^ Ctriadic := by
  classical
  -- the final assembly, run once at the `Θ`-free dimensional record with a free
  -- entry slope
  obtain ⟨delta_sc, C_A, lambda, B, alpha, Cdim,
      hdelta_sc_pos, hdelta_sc_le, hC_A_pos, hlambda_pos, hlambda_lt_one,
      hB_one, halpha_pos, hCdim_nonneg, hP4main⟩ :=
    exists_final_scale_decay_of_main_buffer_and_rawEnergy_scalars_uniform
      params loc (hmDimFree hd hc params) (hmDimFree_p4Params hd hc params) hcp subParams
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hk_pos : 0 < contrastLogFactor := contrastLogFactor_pos
  have hδ_pos : 0 < varianceDelta d := varianceDelta_pos hd
  have hQ2 : (2 : ℝ) ≤ momentQ d hc params := two_le_momentQ d hc params
  have hcoef_nonneg : 0 ≤ 3 * (momentQ d hc params - 1) / varianceDelta d := by
    have : 0 ≤ momentQ d hc params - 1 := by linarith
    positivity
  set Ctriadic : ℝ :=
    contrastLogFactor + 3 * (momentQ d hc params - 1) / varianceDelta d + 2 +
      Cdim * contrastLogFactor with hCt_def
  set Cscale : ℝ := Ctriadic / Real.log 3 with hCs_def
  have hCtriadic_pos : 0 < Ctriadic := by
    rw [hCt_def]
    have hCk : 0 ≤ Cdim * contrastLogFactor := mul_nonneg hCdim_nonneg (le_of_lt hk_pos)
    linarith
  have hCscale_pos : 0 < Cscale := by rw [hCs_def]; positivity
  refine ⟨Cscale, Ctriadic, alpha, hCscale_pos, hCtriadic_pos, halpha_pos, ?_⟩
  intro Θ hΘ P _ hP hStruct hLaw hP4 hparams hpath
  -- the moment-enhanced contrast and its two-sided comparison with `Θ`
  set T : ℝ := Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 with hTdef
  have hT1 : 1 ≤ T := one_le_initialWidetildeTheta_of_P4 hP hStruct hP4
  have hT4 : T ≤ 4 * Θ := by
    have h :=
      Homogenization.widetildeThetaAtScale_le_of_quantitativeCoarseGrainedEllipticity
        hLaw hP4
    simpa [hTdef, Homogenization.Book.Ch05.widetildeThetaAtScale_eq] using h
  have hlogbT_ge1 : (1 : ℝ) ≤ Real.logb 3 (2 + T) := one_le_logb_three_two_add hT1
  have hlogbΘ_ge1 : (1 : ℝ) ≤ Real.logb 3 (2 + Θ) := one_le_logb_three_two_add hΘ
  -- entry scales
  set N2 : ℕ := Nat.ceil ((vpParams d hd Θ).p2 * Real.logb 3 (2 + T)) with hN2def
  set N : ℕ := Nat.ceil (pHmDim hc params Θ T * Real.logb 3 (2 + T)) with hNdef
  set Nstar : ℕ := N + Nat.ceil (B * Real.logb 3 (2 + T)) with hNstardef
  set I : ℕ :=
    Nat.ceil (Real.log (C_A * (2 + T) / delta_sc) / |Real.log lambda|) with hIdef
  have hNNstar : N ≤ Nstar := by rw [hNstardef]; exact Nat.le_add_right _ _
  -- the shifted-anchor variance estimate + dimensional moment estimate
  have hVar :
      VarianceBlockEstimate (vpParams d hd Θ) P T N2
        (intermediateCoarseBlockDeviation hP hStruct (fun x : CoeffField d => x)) :=
    varianceBlockEstimate_of_thetaEllipticLaw hd hΘ hP hStruct hLaw hP4 N2
      (fun {j} _ {Q} hQ => hpath (j := j) (Q := Q) hQ)
  have hMom :
      HighCenteredMomentEstimate (hmDimFree hd hc params) P N
        (intermediateCoarseBlockDeviation hP hStruct (fun x : CoeffField d => x)) :=
    highCenteredMomentEstimate_dimensional_of_varianceBlockEstimate
      hd hc params hΘ hT1 hN2def hNdef hVar
  -- run the (uniform) assembly at the per-law entry slope `q := pHmDim`
  obtain ⟨N0, hdecay, hN0_log, hN0_phys⟩ :=
    hP4main hP hStruct hP4 hparams (pHmDim_nonneg hd hc params hΘ hT1)
      hNdef hNstardef hIdef hNNstar hMom
  -- convert `N0 ≤ (pHmDim + Cdim)·log₃(2+T)` to `N0 ≤ Ctriadic·log₃(2+Θ)`
  have hbT : Real.logb 3 (2 + T) = Real.log (2 + T) / Real.log 3 := rfl
  have hbΘ : Real.logb 3 (2 + Θ) = Real.log (2 + Θ) / Real.log 3 := rfl
  have hbΘ0 : Real.logb 3 Θ = Real.log Θ / Real.log 3 := rfl
  have hLTΘ :
      Real.logb 3 (2 + T) ≤ contrastLogFactor * Real.logb 3 (2 + Θ) := by
    have h := log_two_add_le Θ T hΘ hT1 hT4
    have e : contrastLogFactor * Real.logb 3 (2 + Θ) =
        (contrastLogFactor * Real.log (2 + Θ)) / Real.log 3 := by rw [hbΘ]; ring
    rw [hbT, e]
    exact div_le_div_of_nonneg_right h (le_of_lt hlog3)
  have hlogbΘ_mono : Real.logb 3 Θ ≤ Real.logb 3 (2 + Θ) := by
    have hlogΘ_le : Real.log Θ ≤ Real.log (2 + Θ) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [hbΘ0, hbΘ]
    exact div_le_div_of_nonneg_right hlogΘ_le (le_of_lt hlog3)
  have habsΘ :
      absScale hc params Θ ≤
        (3 * (momentQ d hc params - 1) / varianceDelta d) * Real.logb 3 (2 + Θ) := by
    have heq : absScale hc params Θ =
        (3 * (momentQ d hc params - 1) / varianceDelta d) * Real.logb 3 Θ := by
      unfold absScale; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hlogbΘ_mono hcoef_nonneg
  have hN0_logbΘ : (N0 : ℝ) ≤ Ctriadic * Real.logb 3 (2 + Θ) := by
    have hstep :
        (pHmDim hc params Θ T + Cdim) * Real.logb 3 (2 + T) =
          (Real.logb 3 (2 + T) + absScale hc params Θ + 2) +
            Cdim * Real.logb 3 (2 + T) := by
      rw [add_mul, pHmDim_mul_logb hc params hT1]
    have hCdimL :
        Cdim * Real.logb 3 (2 + T) ≤
          Cdim * (contrastLogFactor * Real.logb 3 (2 + Θ)) :=
      mul_le_mul_of_nonneg_left hLTΘ hCdim_nonneg
    have hCt_expand :
        Ctriadic * Real.logb 3 (2 + Θ) =
          contrastLogFactor * Real.logb 3 (2 + Θ) +
            (3 * (momentQ d hc params - 1) / varianceDelta d) * Real.logb 3 (2 + Θ) +
            2 * Real.logb 3 (2 + Θ) +
            Cdim * (contrastLogFactor * Real.logb 3 (2 + Θ)) := by
      rw [hCt_def]; ring
    have h2Θ : (2 : ℝ) ≤ 2 * Real.logb 3 (2 + Θ) := by linarith
    calc (N0 : ℝ)
        ≤ (pHmDim hc params Θ T + Cdim) * Real.logb 3 (2 + T) := hN0_log
      _ = (Real.logb 3 (2 + T) + absScale hc params Θ + 2) +
            Cdim * Real.logb 3 (2 + T) := hstep
      _ ≤ Ctriadic * Real.logb 3 (2 + Θ) := by
          rw [hCt_expand]; linarith [hLTΘ, habsΘ, h2Θ, hCdimL]
  refine ⟨N0, ?_, ?_, ?_⟩
  · -- θ-decay
    intro n
    have h := hdecay n
    have he : (3 : ℝ) ^ (-alpha * (n : ℝ)) = (3 : ℝ) ^ (-(alpha * (n : ℝ))) := by
      rw [neg_mul]
    rw [he]; linarith
  · -- `N0 ≤ Cscale · log(2+Θ)`
    calc (N0 : ℝ) ≤ Ctriadic * Real.logb 3 (2 + Θ) := hN0_logbΘ
      _ = Cscale * Real.log (2 + Θ) := by rw [hCs_def, hbΘ]; ring
  · -- `3^{N0} ≤ (2+Θ)^Ctriadic`
    have hbaseΘ : (0 : ℝ) < 2 + Θ := by linarith
    have hphys := physical_scale_le_of_logb_bound
      (N := N0) (C := Ctriadic) (T := Θ) hbaseΘ hN0_logbΘ
    rw [Real.rpow_natCast]
    exact hphys

end Homogenization
