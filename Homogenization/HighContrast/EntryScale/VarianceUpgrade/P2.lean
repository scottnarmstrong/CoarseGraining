import Homogenization.HighContrast.EntryScale.FinalAssembly.P4
import Homogenization.HighContrast.EntryScale.VarianceUpgrade.P1

/-!
# Final assembly from the variance input

The final scale-decay theorem with the high centered-moment hypothesis
replaced by the two-channel variance input of `l.moment.variance.upgrade`:
a second-moment envelope entered at `N_2 = ceil(p_2 log_3 (2+T))` together
with the pathwise ellipticity bound `C_0 (2+T)^b`.  The statement is that of
`exists_final_scale_decay_of_main_buffer_and_rawEnergy_scalars` (source label
`t.main`) at the interpolated parameters `hm.varianceUpgrade vp`; the proof
is the interpolation constructor followed by `t.main`.
-/

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization.Book.Ch05.Section54.OneStepContraction
open scoped Matrix.Norms.Elementwise

namespace Homogenization.HighContrast.EntryScale

/--
Source labels `t.main` and `l.moment.variance.upgrade`: the final scale-decay
theorem from a variance (second-moment) input instead of a high
centered-moment input.

In the uniformly elliptic case the centered coarse block deviation is
bounded pathwise, so the `Q`-th centered moment required by `t.main` follows
from the variance envelope by interpolation, at the price of dividing the
decay exponent by `Q` and shifting the entry scale to
`N = ceil(p_Q log_3 (2+T))` — both still of the form required by the final
assembly.  The entry scale `N2` of the variance input and the entry scale `N`
of the conclusion are passed with their defining ceiling equations.

**Subthreshold observable (2026-07-23).**  Following `t.main`, this theorem no
longer quantifies a subthreshold observable `M_sub` nor takes a
`SubthresholdPolynomialMomentEstimate` hypothesis; that parameter was vacuous
(it never reached the conclusion and was dischargeable at the zero observable).
The subthreshold *parameters* `sub` are retained.
-/
theorem exists_final_scale_decay_of_main_buffer_and_variance_scalars
    {d : ℕ} [NeZero d] {hc : HighContrastExponents d}
    (params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    (loc : LocalizationSmallContrastInput hc)
    (hm : HighCenteredMomentParameters d hc)
    (vp : VarianceMomentParameters)
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
        {N2 N Nstar I : ℕ},
          hP4.params = params →
          N2 =
            Nat.ceil
              (vp.p2 * Real.logb 3
                (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) →
          N =
            Nat.ceil
              ((hm.varianceUpgrade vp).p_hm * Real.logb 3
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
          VarianceBlockEstimate vp P
            (Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) N2
            (intermediateCoarseBlockDeviation hP hStruct
              (fun x : Homogenization.RegCoeffField d => x)) →
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
  have hhmP4' : (hm.varianceUpgrade vp).p4Params = params := by
    rw [varianceUpgrade_p4Params]
    exact hhmP4
  obtain ⟨delta_sc, eps, rho, etaS, etaM, etaSt, decay, coeff, memoryCoeff, K,
      A, lambda, C_A, C_delta, C_memory, L, B, C_resp, C_final, alpha, C_osc,
      C_lin, C_high, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
      h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27,
      h28, h29, h30, h31, h32, h33, h34, hmain⟩ :=
    exists_final_scale_decay_of_main_buffer_and_rawEnergy_scalars
      params loc (hm.varianceUpgrade vp) hhmP4' hcp sub
  refine ⟨delta_sc, eps, rho, etaS, etaM, etaSt, decay, coeff, memoryCoeff, K,
      A, lambda, C_A, C_delta, C_memory, L, B, C_resp, C_final, alpha, C_osc,
      C_lin, C_high, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
      h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27,
      h28, h29, h30, h31, h32, h33, h34, ?_⟩
  intro P hP hStruct hP4 N2 N Nstar I hparams hN2_eq hN_eq hNstar_eq
    hI_eq hNNstar hVar
  have hT :
      1 ≤ Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 :=
    one_le_initialWidetildeTheta_of_P4 hP hStruct hP4
  exact hmain hP hStruct hP4 hparams hN_eq hNstar_eq hI_eq hNNstar
    (HighCenteredMomentEstimate.of_varianceBlockEstimate hm vp hT hN2_eq
      hN_eq hVar)

end Homogenization.HighContrast.EntryScale
