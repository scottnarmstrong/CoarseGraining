import Mathlib.Algebra.Order.Field.GeomSum
import Homogenization.Book.Ch05.Theorems.Section52.P4Integrability
import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations
import Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.ResponseMoment
import Homogenization.HighContrast.EntryScale.DeterministicAlgebra
import Homogenization.HighContrast.EntryScale.MomentConsequences
import Homogenization.HighContrast.EntryScale.ResponseFluctuation.P1
import Homogenization.HighContrast.EntryScale.ResponseFluctuation.P2

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization.Book.Ch05.Section54.OneStepContraction

namespace Homogenization.HighContrast.EntryScale

private theorem ofReal_windowConstant_mul_budget_le {C η : ℝ}
    (hC : 0 ≤ C) (hη : 0 < η) :
    ENNReal.ofReal C * ENNReal.ofReal (η / (1 + C)) ≤ ENNReal.ofReal η := by
  have hden_pos : 0 < 1 + C := by linarith
  have hreal : C * (η / (1 + C)) ≤ η := by
    field_simp [ne_of_gt hden_pos]
    nlinarith [mul_nonneg hC (le_of_lt hη)]
  rw [← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal hreal

private theorem section53_windowConstant_eq_ofReal {d : ℕ} {hc : HighContrastExponents d}
    (L : ℕ) :
    (L : ENNReal) * ENNReal.ofReal ((3 : ℝ) ^ (2 * hc.rhoM * (L : ℝ))) =
      ENNReal.ofReal ((L : ℝ) * (3 : ℝ) ^ (2 * hc.rhoM * (L : ℝ))) := by
  have hL_nonneg : 0 ≤ (L : ℝ) := by exact_mod_cast Nat.zero_le L
  rw [ENNReal.ofReal_mul hL_nonneg]
  simp only [ENNReal.ofReal_natCast]

private theorem ofReal_highCenteredMomentBudget_rpow_eq
    {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) {η : ℝ} (hη : 0 < η) :
    (ENNReal.ofReal (η ^ (hm.Q / 2))) ^ ((2 : ℝ) / hm.Q) =
      ENNReal.ofReal η := by
  have hQ_pos : 0 < hm.Q := highCenteredMoment_Q_pos hm
  have hη_nonneg : 0 ≤ η := le_of_lt hη
  have hQhalf_nonneg : 0 ≤ hm.Q / 2 := by linarith
  have hbase :
      ENNReal.ofReal (η ^ (hm.Q / 2)) =
        (ENNReal.ofReal η) ^ (hm.Q / 2) :=
    (ENNReal.ofReal_rpow_of_nonneg hη_nonneg hQhalf_nonneg).symm
  have hprod : hm.Q / 2 * ((2 : ℝ) / hm.Q) = 1 := by
    field_simp [(ne_of_gt hQ_pos)]
  calc
    (ENNReal.ofReal (η ^ (hm.Q / 2))) ^ ((2 : ℝ) / hm.Q)
        = ((ENNReal.ofReal η) ^ (hm.Q / 2)) ^ ((2 : ℝ) / hm.Q) := by
          rw [hbase]
    _ = (ENNReal.ofReal η) ^ (hm.Q / 2 * ((2 : ℝ) / hm.Q)) := by
          rw [← ENNReal.rpow_mul]
    _ = ENNReal.ofReal η := by
          rw [hprod, ENNReal.rpow_one]

/--
Source labels `a.HM`, `M_m^st`, and `l.S.and.J`: the finite-window stochastic
centered-square contribution is bounded by the explicit window loss times the
polynomial high-moment convolution envelope.  This is the stochastic analytic
part of the Section 5.3 fluctuation sum, up to the remaining measurability
surface for the real terminal stochastic maximum.
-/
theorem lintegral_ofReal_terminalCenteredFullBlockFluctuationSqAtScale_sum_le_windowConstant_mul_polynomial_convolution_of_highMoment
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    {N k m L : ℕ} (hNk : N ≤ k + 1) (hNm : N ≤ m)
    (hWindow : m - k ≤ L)
    (hHM :
      HighCenteredMomentEstimate hm P N
        (intermediateCoarseBlockDeviation hP hStruct
          (fun x : Homogenization.RegCoeffField d => x)))
    (hM :
      MeasureTheory.AEStronglyMeasurable
        (terminalCoarseBlockStochasticMax hP hStruct hc N m
          (Homogenization.originCube d (m : ℤ))
          (fun x : Homogenization.RegCoeffField d => x)) P) :
    ∑ j ∈ Finset.Icc (k + 1) m,
        ENNReal.ofReal (section53CoarseFluctuationScaleWeight hP4 m j) *
          ∫⁻ a,
            ENNReal.ofReal
              (terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
                (Homogenization.originCube d (j : ℤ)) a) ∂P ≤
      ((L : ENNReal) * ENNReal.ofReal ((3 : ℝ) ^ (2 * hc.rhoM * (L : ℝ)))) *
        (ENNReal.ofReal
          (((2 +
            Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
            (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
              (3 : ℝ) ^
                (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                  ((m - N : ℕ) : ℝ)))))) ^ ((2 : ℝ) / hm.Q) := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  let Qm := Homogenization.originCube d (m : ℤ)
  let envIntegral : ENNReal :=
    ∫⁻ a,
      (terminalCoarseBlockStochasticEnvelope hP hStruct N m Qm
        (terminalStochasticWeakWeight (d := d) hc m)
        (fun x : Homogenization.RegCoeffField d => x) a) ^ 2 ∂P
  let weightLoss : ENNReal :=
    ∑ j ∈ Finset.Icc (k + 1) m,
      ENNReal.ofReal (section53CoarseFluctuationScaleWeight hP4 m j) *
        (terminalStochasticWeakWeight (d := d) hc m j
            (Homogenization.originCube d (j : ℤ)))⁻¹ ^ 2
  have hinsert :
      ∑ j ∈ Finset.Icc (k + 1) m,
          ENNReal.ofReal (section53CoarseFluctuationScaleWeight hP4 m j) *
            ∫⁻ a,
              ENNReal.ofReal
                (terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
                  (Homogenization.originCube d (j : ℤ)) a) ∂P ≤
        weightLoss * envIntegral := by
    simpa [weightLoss, envIntegral, Qm] using
      lintegral_ofReal_terminalCenteredFullBlockFluctuationSqAtScale_sum_le_weighted_inv_weight_sq_mul_lintegral_terminalCoarseBlockStochasticEnvelope_sq
        hP hStruct hP4 hc hNk
  have hweight :
      weightLoss ≤
        (L : ENNReal) * ENNReal.ofReal ((3 : ℝ) ^ (2 * hc.rhoM * (L : ℝ))) := by
    simpa [weightLoss] using
      section53CoarseFluctuationScaleWeight_mul_terminalStochasticWeakWeight_inv_sq_sum_le_windowConstant
        hP4 hc hWindow
  have hQm_scale : Qm.scale = (m : ℤ) := by
    rfl
  have henv :
      envIntegral ≤
        (ENNReal.ofReal
          (((2 +
            Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
            (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
              (3 : ℝ) ^
                (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                  ((m - N : ℕ) : ℝ)))))) ^ ((2 : ℝ) / hm.Q) := by
    simpa [envIntegral, Qm] using
      lintegral_terminalCoarseBlockStochasticEnvelope_sq_terminalWeak_le_polynomial_convolution_of_highMoment
        hP hStruct hP4 hm P Qm hNm hQm_scale
        (fun x : Homogenization.RegCoeffField d => x) hHM hM
  calc
    ∑ j ∈ Finset.Icc (k + 1) m,
        ENNReal.ofReal (section53CoarseFluctuationScaleWeight hP4 m j) *
          ∫⁻ a,
            ENNReal.ofReal
              (terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
                (Homogenization.originCube d (j : ℤ)) a) ∂P
        ≤ weightLoss * envIntegral := hinsert
    _ ≤ ((L : ENNReal) *
          ENNReal.ofReal ((3 : ℝ) ^ (2 * hc.rhoM * (L : ℝ)))) *
        (ENNReal.ofReal
          (((2 +
            Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
            (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
              (3 : ℝ) ^
                (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                  ((m - N : ℕ) : ℝ)))))) ^ ((2 : ℝ) / hm.Q) := by
          exact mul_le_mul' hweight henv

/--
Source labels `a.HM`, `e.Nstar`, and `l.S.and.J`: for a fixed Section 5.3
window length, the stochastic centered-square contribution is made smaller
than `eta_S` by increasing the same logarithmic buffer.  The fixed window loss
`L * 3^{2 rho_M L}` is absorbed into the tolerance before applying the
high-moment convolution buffer.
-/
theorem exists_bufferExponent_lintegral_ofReal_terminalCenteredFullBlockFluctuationSqAtScale_sum_le_of_windowLength
    {d : ℕ} [NeZero d] {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) (L : ℕ) {η_S : ℝ} (hη_S : 0 < η_S) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
        (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
        (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
        {N k m : ℕ},
          N ≤ k + 1 →
          m - k ≤ L →
          N + Nat.ceil
              (B * Real.logb 3
                (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) ≤
            m →
          HighCenteredMomentEstimate hm P N
            (intermediateCoarseBlockDeviation hP hStruct
              (fun x : Homogenization.RegCoeffField d => x)) →
          ∑ j ∈ Finset.Icc (k + 1) m,
              ENNReal.ofReal (section53CoarseFluctuationScaleWeight hP4 m j) *
                ∫⁻ a,
                  ENNReal.ofReal
                    (terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
                      (Homogenization.originCube d (j : ℤ)) a) ∂P ≤
            ENNReal.ofReal η_S := by
  let Cwin : ℝ := (L : ℝ) * (3 : ℝ) ^ (2 * hc.rhoM * (L : ℝ))
  have hCwin_nonneg : 0 ≤ Cwin := by
    dsimp [Cwin]
    exact mul_nonneg (by exact_mod_cast Nat.zero_le L)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3)
        (2 * hc.rhoM * (L : ℝ)))
  let η_window : ℝ := η_S / (1 + Cwin)
  have hden_pos : 0 < 1 + Cwin := by linarith
  have hη_window_pos : 0 < η_window := by
    exact div_pos hη_S hden_pos
  let η_high : ℝ := η_window ^ (hm.Q / 2)
  have hη_high_pos : 0 < η_high := by
    dsimp [η_high]
    exact Real.rpow_pos_of_pos hη_window_pos (hm.Q / 2)
  obtain ⟨B, hB_one, hB⟩ :=
    exists_bufferExponent_highCenteredMoment_convolutionEnvelope_le hm hη_high_pos
  refine ⟨B, hB_one, ?_⟩
  intro P hP hStruct hP4 N k m hNk hWindow hNstar hHM
  let T : ℝ := Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4
  let n : ℕ := m - N
  let poly : ℝ :=
    ((2 + T : ℝ) ^ hm.Q) *
      (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
        (3 : ℝ) ^
          (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
            ((m - N : ℕ) : ℝ))))
  have hNm : N ≤ m := by omega
  have hT : 1 ≤ T := by
    simpa [T] using one_le_initialWidetildeTheta_of_P4 hP hStruct hP4
  have hceil_gap :
      Nat.ceil (B * Real.logb 3 (2 + T)) ≤ m - N := by
    have hNstarT : N + Nat.ceil (B * Real.logb 3 (2 + T)) ≤ m := by
      simpa [T] using hNstar
    omega
  have hbuf : B * Real.logb 3 (2 + T) ≤ ((m - N : ℕ) : ℝ) := by
    exact (Nat.ceil_le).mp hceil_gap
  have hpoly_le : poly ≤ η_high := by
    have henv :
        hm.C_Q * (((2 + T : ℝ) ^ hm.Q) *
          (((n : ℝ) + 1) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                (n : ℝ)))) ≤ η_high :=
      hB (T := T) (n := n) hT (by simpa [T, n] using hbuf)
    simpa [poly, T, n, Nat.cast_add, Nat.cast_one, mul_assoc, mul_comm, mul_left_comm]
      using henv
  have hmain :=
    lintegral_ofReal_terminalCenteredFullBlockFluctuationSqAtScale_sum_le_windowConstant_mul_polynomial_convolution_of_highMoment
      hP hStruct hP4 hm hNk hNm hWindow hHM
      (aestronglyMeasurable_terminalCoarseBlockStochasticMax_origin hP hStruct hP4 hc N m)
  have hp_nonneg : 0 ≤ (2 : ℝ) / hm.Q := by
    exact div_nonneg (by norm_num) (le_of_lt (highCenteredMoment_Q_pos hm))
  have hpoly_small :
      (ENNReal.ofReal poly) ^ ((2 : ℝ) / hm.Q) ≤ ENNReal.ofReal η_window := by
    calc
      (ENNReal.ofReal poly) ^ ((2 : ℝ) / hm.Q)
          ≤ (ENNReal.ofReal η_high) ^ ((2 : ℝ) / hm.Q) :=
            ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hpoly_le) hp_nonneg
      _ = ENNReal.ofReal η_window := by
            simpa [η_high] using
              ofReal_highCenteredMomentBudget_rpow_eq hm hη_window_pos
  have hwindow_eq :
      (L : ENNReal) * ENNReal.ofReal ((3 : ℝ) ^ (2 * hc.rhoM * (L : ℝ))) =
        ENNReal.ofReal Cwin := by
    rw [section53_windowConstant_eq_ofReal (hc := hc) L]
  calc
    ∑ j ∈ Finset.Icc (k + 1) m,
        ENNReal.ofReal (section53CoarseFluctuationScaleWeight hP4 m j) *
          ∫⁻ a,
            ENNReal.ofReal
              (terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
                (Homogenization.originCube d (j : ℤ)) a) ∂P
        ≤ ((L : ENNReal) * ENNReal.ofReal ((3 : ℝ) ^ (2 * hc.rhoM * (L : ℝ)))) *
            (ENNReal.ofReal poly) ^ ((2 : ℝ) / hm.Q) := by
          simpa [poly, T] using hmain
    _ = ENNReal.ofReal Cwin * (ENNReal.ofReal poly) ^ ((2 : ℝ) / hm.Q) := by
          rw [hwindow_eq]
    _ ≤ ENNReal.ofReal Cwin * ENNReal.ofReal η_window := by
          exact mul_le_mul' le_rfl hpoly_small
    _ ≤ ENNReal.ofReal η_S := by
          simpa [η_window] using
            ofReal_windowConstant_mul_budget_le hCwin_nonneg hη_S

/--
Source labels `a.HM`, `e.Nstar`, and `l.S.and.J`: real-valued form of the
stochastic centered-square smallness statement used in the Section 5.3 split.
It is obtained from the `ENNReal` buffer theorem by the nonnegative integral
conversion above.
-/
theorem exists_bufferExponent_terminalCenteredFullBlockFluctuationSqAtScale_integral_sum_le_of_windowLength
    {d : ℕ} [NeZero d] {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) (L : ℕ) {η_S : ℝ} (hη_S : 0 < η_S) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
        (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
        (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
        {N k m : ℕ},
          N ≤ k + 1 →
          m - k ≤ L →
          N + Nat.ceil
              (B * Real.logb 3
                (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) ≤
            m →
          HighCenteredMomentEstimate hm P N
            (intermediateCoarseBlockDeviation hP hStruct
              (fun x : Homogenization.RegCoeffField d => x)) →
          ∑ j ∈ Finset.Icc (k + 1) m,
              section53CoarseFluctuationScaleWeight hP4 m j *
                ∫ a,
                  terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
                    (Homogenization.originCube d (j : ℤ)) a ∂P ≤
            η_S := by
  obtain ⟨B, hB_one, hB⟩ :=
    exists_bufferExponent_lintegral_ofReal_terminalCenteredFullBlockFluctuationSqAtScale_sum_le_of_windowLength
      hm L hη_S
  refine ⟨B, hB_one, ?_⟩
  intro P hP hStruct hP4 N k m hNk hWindow hNstar hHM
  have hlintegral :=
    hB hP hStruct hP4 hNk hWindow hNstar hHM
  exact
    terminalCenteredFullBlockFluctuationSqAtScale_integral_sum_le_of_lintegral_sum_le
      hP hStruct hP4 (le_of_lt hη_S) hlintegral

/--
Source label `l.S.and.J`: squared deterministic annealed-drift contribution
appearing after `|X+Y|^2 <= 2|X|^2 + 2|Y|^2`.
-/
noncomputable def terminalAnnealedFullBlockDriftSqAtScales
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (j m : ℕ) : ℝ :=
  terminalAnnealedFullBlockDriftAtScales hP hStruct j m ^ 2

/--
Source label `l.S.and.J`: named form of the pointwise deterministic split of
the library's terminal fluctuation into the stochastic centered-at-`j` part and the
annealed drift.
-/
theorem fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_two_terminalCentered_add_two_terminalAnnealedDrift
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (j m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.RegCoeffField d) :
    Homogenization.Book.Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
        hP hStruct (m : ℤ) Q a ≤
      2 * terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m Q a +
        2 * terminalAnnealedFullBlockDriftSqAtScales hP hStruct j m := by
  exact
    fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_two_stochastic_add_two_drift
      hP hStruct j m Q a

/--
Source label `l.S.and.J`: after the library's Section 5.3 natural reindex, the
coarse full-block fluctuation sum is bounded by the terminal stochastic
centered-at-`j` sum plus the deterministic annealed-drift sum.  The only
integrability needed for the stochastic centered square is supplied by `(P4)`.
-/
theorem coarseFluctuationFullBlockSumAtScale_le_two_terminalCentered_integral_sum_add_two_terminalAnnealedDrift_sum
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) :
    coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m ≤
      2 * ∑ j ∈ Finset.Icc (k + 1) m,
        section53CoarseFluctuationScaleWeight hP4 m j *
          ∫ a,
            terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
              (Homogenization.originCube d (j : ℤ)) a ∂P +
      2 * ∑ j ∈ Finset.Icc (k + 1) m,
        section53CoarseFluctuationScaleWeight hP4 m j *
          terminalAnnealedFullBlockDriftSqAtScales hP hStruct j m := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  let S := Finset.Icc (k + 1) m
  let w : ℕ → ℝ := section53CoarseFluctuationScaleWeight hP4 m
  let fluct : ℕ → Homogenization.RegCoeffField d → ℝ :=
    fun j a =>
      Homogenization.Book.Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
        hP hStruct (m : ℤ) (Homogenization.originCube d (j : ℤ)) a
  let centered : ℕ → Homogenization.RegCoeffField d → ℝ :=
    fun j a =>
      terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
        (Homogenization.originCube d (j : ℤ)) a
  let drift : ℕ → ℝ :=
    fun j => terminalAnnealedFullBlockDriftSqAtScales hP hStruct j m
  have hw_nonneg : ∀ j, 0 ≤ w j := by
    intro j
    dsimp [w, section53CoarseFluctuationScaleWeight]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hIntegralBound :
      ∀ j ∈ S,
        (∫ a, fluct j a ∂P) ≤ 2 * (∫ a, centered j a ∂P) + 2 * drift j := by
    intro j hj
    have hfluct_nonneg : 0 ≤ᵐ[P] fluct j := by
      refine Filter.Eventually.of_forall ?_
      intro a
      simp [fluct, Homogenization.Book.Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale,
        Homogenization.Book.Ch04.fullBlockNormalizedFluctuationOperatorNormSq]
    have hcentered_int : MeasureTheory.Integrable (centered j) P := by
      simpa [centered] using
        integrable_terminalCenteredFullBlockFluctuationSqAtScale_origin_of_P4
          hP hStruct hP4 j m
    have hrhs_int :
        MeasureTheory.Integrable
          (fun a : Homogenization.RegCoeffField d =>
            2 * centered j a + 2 * drift j) P :=
      (hcentered_int.const_mul 2).add (MeasureTheory.integrable_const (2 * drift j))
    have hpoint :
        fluct j ≤ᵐ[P]
          fun a : Homogenization.RegCoeffField d => 2 * centered j a + 2 * drift j := by
      refine Filter.Eventually.of_forall ?_
      intro a
      exact
        fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_two_terminalCentered_add_two_terminalAnnealedDrift
          hP hStruct j m (Homogenization.originCube d (j : ℤ)) a
    calc
      (∫ a, fluct j a ∂P) ≤
          ∫ a, 2 * centered j a + 2 * drift j ∂P :=
        MeasureTheory.integral_mono_of_nonneg hfluct_nonneg hrhs_int hpoint
      _ = ∫ a, 2 * centered j a ∂P +
          ∫ _ : Homogenization.RegCoeffField d, 2 * drift j ∂P := by
        rw [MeasureTheory.integral_add
          (hcentered_int.const_mul 2) (MeasureTheory.integrable_const (2 * drift j))]
      _ = 2 * (∫ a, centered j a ∂P) + 2 * drift j := by
        rw [MeasureTheory.integral_const_mul]
        rw [MeasureTheory.integral_eq_const
          (μ := P) (Filter.Eventually.of_forall (fun _ : Homogenization.RegCoeffField d => rfl))]
  have hsum :
      ∑ j ∈ S, w j * (∫ a, fluct j a ∂P) ≤
        ∑ j ∈ S, w j *
          (2 * (∫ a, centered j a ∂P) + 2 * drift j) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact mul_le_mul_of_nonneg_left (hIntegralBound j hj) (hw_nonneg j)
  have hrewrite :
      ∑ j ∈ S, w j *
          (2 * (∫ a, centered j a ∂P) + 2 * drift j) =
        2 * ∑ j ∈ S, w j * (∫ a, centered j a ∂P) +
          2 * ∑ j ∈ S, w j * drift j := by
    calc
      ∑ j ∈ S, w j *
          (2 * (∫ a, centered j a ∂P) + 2 * drift j) =
          ∑ j ∈ S,
            (2 * (w j * (∫ a, centered j a ∂P)) + 2 * (w j * drift j)) := by
        refine Finset.sum_congr rfl ?_
        intro j _hj
        ring
      _ = ∑ j ∈ S, 2 * (w j * (∫ a, centered j a ∂P)) +
          ∑ j ∈ S, 2 * (w j * drift j) := by
        rw [Finset.sum_add_distrib]
      _ = 2 * ∑ j ∈ S, w j * (∫ a, centered j a ∂P) +
          2 * ∑ j ∈ S, w j * drift j := by
        rw [Finset.mul_sum, Finset.mul_sum]
  calc
    coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m =
        ∑ j ∈ S, w j * (∫ a, fluct j a ∂P) := by
      rw [coarseFluctuationFullBlockSumAtScale_eq_nat_Icc hP hStruct hP4 k m]
    _ ≤ ∑ j ∈ S, w j *
          (2 * (∫ a, centered j a ∂P) + 2 * drift j) := hsum
    _ = 2 * ∑ j ∈ S, w j * (∫ a, centered j a ∂P) +
          2 * ∑ j ∈ S, w j * drift j := hrewrite
    _ = 2 * ∑ j ∈ Finset.Icc (k + 1) m,
          section53CoarseFluctuationScaleWeight hP4 m j *
            ∫ a,
              terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
                (Homogenization.originCube d (j : ℤ)) a ∂P +
        2 * ∑ j ∈ Finset.Icc (k + 1) m,
          section53CoarseFluctuationScaleWeight hP4 m j *
            terminalAnnealedFullBlockDriftSqAtScales hP hStruct j m := by
      rfl

/--
Source labels `e.drift.general`, `e.drift.nodrop`, and `l.S.and.J`: insert a
pointwise no-drop drift bound for `D_{j,m}` into the deterministic part of the
Section 5.3 weighted fluctuation sum.

The hypothesis `hDrift` is the remaining pointwise content of
`e.drift.general` after the no-drop estimate has bounded `F_j - F_m` by
`rho * F_m`; this theorem performs only the squaring, weighting, and terminal
`T_m` scaling.
-/
theorem terminal_weight_mul_terminalAnnealedFullBlockDriftSq_sum_le_of_drift_bound
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) {C Cw rho F_m T_m : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hrho_nonneg : 0 ≤ rho)
    (hF_pos : 0 < F_m)
    (hT : T_m = (1 + F_m) ^ 2 / F_m)
    (hDrift :
      ∀ j ∈ Finset.Icc (k + 1) m,
        terminalAnnealedFullBlockDriftAtScales hP hStruct j m ≤
          C * (rho * F_m) / (1 + F_m))
    (hWeightSum :
      ∑ j ∈ Finset.Icc (k + 1) m,
        section53CoarseFluctuationScaleWeight hP4 m j ≤ Cw) :
    T_m *
        (∑ j ∈ Finset.Icc (k + 1) m,
          section53CoarseFluctuationScaleWeight hP4 m j *
            terminalAnnealedFullBlockDriftSqAtScales hP hStruct j m) ≤
      C ^ 2 * Cw * rho ^ 2 * F_m := by
  classical
  let S := Finset.Icc (k + 1) m
  let w : ℕ → ℝ := section53CoarseFluctuationScaleWeight hP4 m
  let D : ℕ → ℝ := fun j => terminalAnnealedFullBlockDriftAtScales hP hStruct j m
  have hT_pos : 0 < T_m := by
    rw [hT]
    positivity
  have hw_nonneg : ∀ j ∈ S, 0 ≤ w j := by
    intro j _hj
    dsimp [w, section53CoarseFluctuationScaleWeight]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hDsq :
      ∀ j ∈ S, D j ^ 2 ≤ C ^ 2 * rho ^ 2 * F_m / T_m := by
    intro j hj
    exact
      drift_general_square_bound
        (terminalAnnealedFullBlockDriftAtScales_nonneg hP hStruct j m)
        hC_nonneg hrho_nonneg hF_pos hT
        (by simpa [D, S] using hDrift j hj)
  have hC_sq_nonneg : 0 ≤ C ^ 2 := sq_nonneg C
  have hF_nonneg : 0 ≤ F_m := le_of_lt hF_pos
  have hweighted :=
    weighted_drift_square_bound
      (s := S) (w := w) (D := D) (T_m := T_m) (C := C ^ 2)
      (Cw := Cw) (rho := rho) (F_m := F_m)
      hT_pos hC_sq_nonneg hF_nonneg hw_nonneg hDsq
      (by simpa [S, w] using hWeightSum)
  simpa [S, w, D, terminalAnnealedFullBlockDriftSqAtScales] using hweighted

/--
Source labels `e.drift.general`, `e.drift.nodrop`, and `l.S.and.J`: concrete
no-drop insertion for the deterministic annealed-drift sum, with the geometric
Section 5.3 weight constant from the library instead of the temporary window-length
bound.
-/
theorem terminal_weight_mul_terminalAnnealedFullBlockDriftSq_sum_le_noDrop_contrastExcess
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) {rho T_m : ℝ}
    (hrho_nonneg : 0 ≤ rho)
    (hno :
      noDropWindow rho
        (contrastExcessAtScale hP hStruct k)
        (contrastExcessAtScale hP hStruct m))
    (hF_pos : 0 < contrastExcessAtScale hP hStruct m)
    (hT :
      T_m =
        (1 + contrastExcessAtScale hP hStruct m) ^ 2 /
          contrastExcessAtScale hP hStruct m) :
    T_m *
        (∑ j ∈ Finset.Icc (k + 1) m,
          section53CoarseFluctuationScaleWeight hP4 m j *
            terminalAnnealedFullBlockDriftSqAtScales hP hStruct j m) ≤
      section53CoarseFluctuationWeightSumConstant hP4 * rho ^ 2 *
        contrastExcessAtScale hP hStruct m := by
  refine
    (terminal_weight_mul_terminalAnnealedFullBlockDriftSq_sum_le_of_drift_bound
      hP hStruct hP4 k m (by norm_num : (0 : ℝ) ≤ 1)
      hrho_nonneg hF_pos hT ?_
      (section53CoarseFluctuationScaleWeight_sum_le_geometricConstant hP4 k m)).trans_eq ?_
  · intro j hj
    have hj_bounds := Finset.mem_Icc.mp hj
    have hkj : k ≤ j := by omega
    have hjm : j ≤ m := hj_bounds.2
    have hD :=
      terminalAnnealedFullBlockDriftAtScales_le_noDrop_contrastExcess_of_P4
        hP hStruct hP4 hno hkj hjm
    simpa [one_mul] using hD
  · ring

/--
Source label `l.S.and.J`, equation `e.S.term.bound`: full Section 5.3
terminal fluctuation estimate before scalar constant packaging.  The first
input is the proved stochastic centered-square sum estimate; the second
contribution is the deterministic no-drop annealed-drift estimate.  This is
the analytic bridge from the stochastic buffer to the source-form
`T_m S_{k,m} <= C (eta_S + rho^2) F_m`.
-/
theorem terminal_weight_mul_coarseFluctuationFullBlockSumAtScale_le_stochastic_add_drift
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) {rho T_m delta C_delta etaS : ℝ}
    (hdelta_pos : 0 < delta)
    (hdelta_le_F : delta ≤ contrastExcessAtScale hP hStruct m)
    (hT :
      T_m =
        (1 + contrastExcessAtScale hP hStruct m) ^ 2 /
          contrastExcessAtScale hP hStruct m)
    (hC_delta : (1 + delta⁻¹) ^ 2 ≤ C_delta)
    (hrho_nonneg : 0 ≤ rho)
    (hno :
      noDropWindow rho
        (contrastExcessAtScale hP hStruct k)
        (contrastExcessAtScale hP hStruct m))
    (hstoch :
      ∑ j ∈ Finset.Icc (k + 1) m,
          section53CoarseFluctuationScaleWeight hP4 m j *
            ∫ a,
              terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
                (Homogenization.originCube d (j : ℤ)) a ∂P ≤ etaS) :
    T_m * coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m ≤
      (2 * C_delta * etaS +
          2 * section53CoarseFluctuationWeightSumConstant hP4 * rho ^ 2) *
        contrastExcessAtScale hP hStruct m := by
  classical
  let stoch : ℝ :=
    ∑ j ∈ Finset.Icc (k + 1) m,
      section53CoarseFluctuationScaleWeight hP4 m j *
        ∫ a,
          terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
            (Homogenization.originCube d (j : ℤ)) a ∂P
  let drift : ℝ :=
    ∑ j ∈ Finset.Icc (k + 1) m,
      section53CoarseFluctuationScaleWeight hP4 m j *
        terminalAnnealedFullBlockDriftSqAtScales hP hStruct j m
  let Fm : ℝ := contrastExcessAtScale hP hStruct m
  let Cw : ℝ := section53CoarseFluctuationWeightSumConstant hP4
  have hF_pos : 0 < Fm := hdelta_pos.trans_le hdelta_le_F
  have hT_pos : 0 < T_m := by
    rw [hT]
    positivity
  have hS_split :
      coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m ≤
        2 * stoch + 2 * drift := by
    simpa [stoch, drift] using
      coarseFluctuationFullBlockSumAtScale_le_two_terminalCentered_integral_sum_add_two_terminalAnnealedDrift_sum
        hP hStruct hP4 k m
  have hstoch_nonneg : 0 ≤ stoch := by
    dsimp [stoch]
    refine Finset.sum_nonneg ?_
    intro j _hj
    exact mul_nonneg
      (by
        dsimp [section53CoarseFluctuationScaleWeight]
        exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
      (MeasureTheory.integral_nonneg fun a => by
        unfold terminalCenteredFullBlockFluctuationSqAtScale
        positivity)
  have hstoch_weight :
      T_m * stoch ≤ C_delta * etaS * Fm := by
    exact
      terminal_weight_mul_term_le_const_mul_contrast_of_le
        hdelta_pos hdelta_le_F hT hC_delta hstoch_nonneg
        (by simpa [stoch] using hstoch)
  have hdrift_weight :
      T_m * drift ≤ Cw * rho ^ 2 * Fm := by
    simpa [drift, Cw, Fm] using
      terminal_weight_mul_terminalAnnealedFullBlockDriftSq_sum_le_noDrop_contrastExcess
        hP hStruct hP4 k m hrho_nonneg hno hF_pos hT
  have hweighted_split :
      T_m * coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m ≤
        2 * (T_m * stoch) + 2 * (T_m * drift) := by
    calc
      T_m * coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m
          ≤ T_m * (2 * stoch + 2 * drift) :=
            mul_le_mul_of_nonneg_left hS_split (le_of_lt hT_pos)
      _ = 2 * (T_m * stoch) + 2 * (T_m * drift) := by ring
  calc
    T_m * coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m
        ≤ 2 * (T_m * stoch) + 2 * (T_m * drift) := hweighted_split
    _ ≤ 2 * (C_delta * etaS * Fm) + 2 * (Cw * rho ^ 2 * Fm) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hstoch_weight (by norm_num : (0 : ℝ) ≤ 2))
            (mul_le_mul_of_nonneg_left hdrift_weight (by norm_num : (0 : ℝ) ≤ 2))
    _ = (2 * C_delta * etaS + 2 * Cw * rho ^ 2) * Fm := by ring

/--
Source label `l.S.and.J`, equation `e.S.term.bound`: fixed-window
source-facing buffer form of the Section 5.3 terminal fluctuation estimate.
The logarithmic buffer is inherited from the real stochastic centered-square
buffer, while the no-drop drift term remains explicit.
-/
theorem exists_bufferExponent_terminal_weight_mul_coarseFluctuationFullBlockSumAtScale_le_stochastic_add_drift_of_windowLength
    {d : ℕ} [NeZero d] {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) (L : ℕ) {etaS : ℝ} (hηS : 0 < etaS) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
        (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
        (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
        {N k m : ℕ} {rho T_m delta C_delta : ℝ},
          N ≤ k + 1 →
          m - k ≤ L →
          N + Nat.ceil
              (B * Real.logb 3
                (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) ≤
            m →
          HighCenteredMomentEstimate hm P N
            (intermediateCoarseBlockDeviation hP hStruct
              (fun x : Homogenization.RegCoeffField d => x)) →
          0 < delta →
          delta ≤ contrastExcessAtScale hP hStruct m →
          T_m =
            (1 + contrastExcessAtScale hP hStruct m) ^ 2 /
              contrastExcessAtScale hP hStruct m →
          (1 + delta⁻¹) ^ 2 ≤ C_delta →
          0 ≤ rho →
          noDropWindow rho
            (contrastExcessAtScale hP hStruct k)
            (contrastExcessAtScale hP hStruct m) →
          T_m * coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m ≤
            (2 * C_delta * etaS +
                2 * section53CoarseFluctuationWeightSumConstant hP4 * rho ^ 2) *
              contrastExcessAtScale hP hStruct m := by
  obtain ⟨B, hB_one, hB⟩ :=
    exists_bufferExponent_terminalCenteredFullBlockFluctuationSqAtScale_integral_sum_le_of_windowLength
      hm L hηS
  refine ⟨B, hB_one, ?_⟩
  intro P hP hStruct hP4 N k m rho T_m delta C_delta
    hNk hWindow hNstar hHM hdelta_pos hdelta_le_F hT hC_delta hrho_nonneg hno
  have hstoch := hB hP hStruct hP4 hNk hWindow hNstar hHM
  exact
    terminal_weight_mul_coarseFluctuationFullBlockSumAtScale_le_stochastic_add_drift
      hP hStruct hP4 k m hdelta_pos hdelta_le_F hT hC_delta
      hrho_nonneg hno hstoch

end Homogenization.HighContrast.EntryScale
