import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Homogenization.HighContrast.EntryScale.BadMaximal.P3

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open MeasureTheory


/-!
# Bad-event response term

This file isolates the terminal lower-edge bad-event child-response integral.
The analytic input kept visible is the Hölder partner needed for the bad-event
square: an `L^xi` bound on `(badEventTruncation M)^2`.
-/


namespace Homogenization.HighContrast.EntryScale

noncomputable section

/--
Source labels: `a.HM`, `l.union.bound`, `e.M.def`, and `p.HC.CR`.

Quantitative high-moment bound for the source-max bad-event Hölder partner.
The bound keeps the deterministic annealed-drift source term visible; the
manuscript source maximum is controlled by the centered stochastic `Q`-envelope
plus this drift, not by the centered stochastic envelope alone.
-/
theorem lintegral_enorm_rpow_two_mul_xi_badEventTruncation_terminalSourceMax_le_polynomial_add_drift
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d)
    (hm : HighCenteredMomentParameters d hc)
    (hparams : hP4.params = hm.p4Params) {k m : ℕ} (hkm : k ≤ m)
    (hHM :
      HighCenteredMomentEstimate hm P k
        (intermediateCoarseBlockDeviation hP hStruct
          (fun x : Homogenization.RegCoeffField d => x))) :
    let Qm : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let sourceMax :=
      terminalSpectralPositivePartSourceMax hP hStruct hc k m Qm
        (fun x : Homogenization.RegCoeffField d => x)
    let drift := terminalBadMaximalDriftSup hP hStruct hc hkm
    let polynomialBound : ENNReal :=
      ENNReal.ofReal
        (((2 +
          Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
          (hm.C_Q * (((m - k + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - k : ℕ) : ℝ)))))
    ∫⁻ a, ‖badEventTruncation sourceMax a‖ₑ ^
        (2 * (hP4.xi : ℝ)) ∂P ≤
      (polynomialBound ^ (1 / hm.Q) + ENNReal.ofReal drift) ^
        (2 * (hP4.xi : ℝ)) := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  dsimp only
  let Qm : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let sourceMax : Homogenization.RegCoeffField d → ℝ :=
    terminalSpectralPositivePartSourceMax hP hStruct hc k m Qm
      (fun x : Homogenization.RegCoeffField d => x)
  let stochastic : Homogenization.RegCoeffField d → ℝ :=
    terminalCoarseBlockStochasticMax hP hStruct hc k m Qm
      (fun x : Homogenization.RegCoeffField d => x)
  let drift : ℝ := terminalBadMaximalDriftSup hP hStruct hc hkm
  let polynomialBound : ENNReal :=
    ENNReal.ofReal
      (((2 +
        Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
        (hm.C_Q * (((m - k + 1 : ℕ) : ℝ) *
          (3 : ℝ) ^
            (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
              ((m - k : ℕ) : ℝ)))))
  let p : ℝ := 2 * (hP4.xi : ℝ)
  have hxi_pos : 0 < (hP4.xi : ℝ) := by
    exact_mod_cast hP4.xi_pos
  have hp_pos : 0 < p := by
    dsimp [p]
    nlinarith
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hp_le_Q : p ≤ hm.Q := by
    simpa [p] using highCenteredMoment_two_mul_p4_xi_le_Q hm hP4 hparams
  have hQ_pos : 0 < hm.Q := highCenteredMoment_Q_pos hm
  have hQ_nonneg : 0 ≤ hm.Q := le_of_lt hQ_pos
  have hQ_ne_zero : hm.Q ≠ 0 := ne_of_gt hQ_pos
  have hpenn_ne_zero : ENNReal.ofReal p ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le_of_gt hp_pos]
  have hpenn_ne_top : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hQenn_ne_zero : ENNReal.ofReal hm.Q ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le_of_gt hQ_pos]
  have hQenn_ne_top : ENNReal.ofReal hm.Q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hQscale : Qm.scale = (m : ℤ) := by
    simp [Qm, Homogenization.originCube]
  have hsource_meas :
      MeasureTheory.AEStronglyMeasurable sourceMax P := by
    simpa [sourceMax, Qm] using
      aestronglyMeasurable_terminalSpectralPositivePartSourceMax_origin
        hP hStruct hc k m
  have hbad_meas :
      MeasureTheory.AEStronglyMeasurable (badEventTruncation sourceMax) P :=
    aestronglyMeasurable_badEventTruncation hsource_meas
  have hstochastic_meas :
      MeasureTheory.AEStronglyMeasurable stochastic P := by
    simpa [stochastic, Qm] using
      aestronglyMeasurable_terminalCoarseBlockStochasticMax_origin
        hP hStruct hP4 hc k m
  have hdrift_nonneg : 0 ≤ drift := by
    simpa [drift] using terminalBadMaximalDriftSup_nonneg hP hStruct hc hkm
  have hbad_to_source :
      MeasureTheory.eLpNorm (badEventTruncation sourceMax)
          (ENNReal.ofReal hm.Q) P ≤
        MeasureTheory.eLpNorm sourceMax (ENNReal.ofReal hm.Q) P := by
    refine MeasureTheory.eLpNorm_mono ?_
    intro a
    have hsource_nonneg : 0 ≤ sourceMax a := by
      simpa [sourceMax, Qm] using
        terminalSpectralPositivePartSourceMax_nonneg hP hStruct hc k m Qm
          (fun x : Homogenization.RegCoeffField d => x) a
    have hbad_nonneg : 0 ≤ badEventTruncation sourceMax a :=
      badEventTruncation_nonneg hsource_nonneg
    have hbad_le : badEventTruncation sourceMax a ≤ sourceMax a :=
      badEventTruncation_le_self_of_nonneg hsource_nonneg
    simpa [Real.norm_eq_abs, abs_of_nonneg hbad_nonneg,
      abs_of_nonneg hsource_nonneg] using hbad_le
  have hsource_to_sum :
      MeasureTheory.eLpNorm sourceMax (ENNReal.ofReal hm.Q) P ≤
        MeasureTheory.eLpNorm
          (fun a : Homogenization.RegCoeffField d => stochastic a + drift)
          (ENNReal.ofReal hm.Q) P := by
    refine MeasureTheory.eLpNorm_mono ?_
    intro a
    have hsource_nonneg : 0 ≤ sourceMax a := by
      simpa [sourceMax, Qm] using
        terminalSpectralPositivePartSourceMax_nonneg hP hStruct hc k m Qm
          (fun x : Homogenization.RegCoeffField d => x) a
    have hstochastic_nonneg : 0 ≤ stochastic a := by
      simpa [stochastic, Qm] using
        terminalCoarseBlockStochasticMax_nonneg hP hStruct hc k m Qm
          (fun x : Homogenization.RegCoeffField d => x) a
    have hsum_nonneg : 0 ≤ stochastic a + drift :=
      add_nonneg hstochastic_nonneg hdrift_nonneg
    have hsource_le : sourceMax a ≤ stochastic a + drift := by
      have hle :=
        terminalSpectralPositivePartSourceMax_le_terminalBadMaximalSplitEnvelope
          hP hStruct hc hkm Qm (fun x : Homogenization.RegCoeffField d => x)
          (fun _ _ => (0 : ℝ)) a
      simpa [sourceMax, stochastic, drift, Qm, terminalBadMaximalSplitEnvelope]
        using hle
    simpa [Real.norm_eq_abs, abs_of_nonneg hsource_nonneg,
      abs_of_nonneg hsum_nonneg] using hsource_le
  have hQ_one : (1 : ENNReal) ≤ ENNReal.ofReal hm.Q := by
    calc
      (1 : ENNReal) ≤ (2 : ENNReal) := by norm_num
      _ = ENNReal.ofReal (2 : ℝ) := by norm_num
      _ ≤ ENNReal.ofReal hm.Q := ENNReal.ofReal_le_ofReal hm.two_le_Q
  have htriangle :
      MeasureTheory.eLpNorm
          (fun a : Homogenization.RegCoeffField d => stochastic a + drift)
          (ENNReal.ofReal hm.Q) P ≤
        MeasureTheory.eLpNorm stochastic (ENNReal.ofReal hm.Q) P +
          MeasureTheory.eLpNorm
            (fun _a : Homogenization.RegCoeffField d => drift)
            (ENNReal.ofReal hm.Q) P := by
    simpa [Pi.add_apply] using
      MeasureTheory.eLpNorm_add_le
        (f := stochastic)
        (g := fun _a : Homogenization.RegCoeffField d => drift)
        hstochastic_meas MeasureTheory.aestronglyMeasurable_const hQ_one
  have hweak : ∀ j ∈ Finset.Icc k m,
      ∀ R ∈ Homogenization.descendantsAtDepth Qm (m - j),
        terminalStochasticWeakWeight hc m j R ≤
          ENNReal.ofReal ((3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ))) := by
    intro j _hj R _hR
    rfl
  have hstochastic_Q :
      ∫⁻ a, ‖stochastic a‖ₑ ^ hm.Q ∂P ≤ polynomialBound := by
    have hpoint : ∀ a : Homogenization.RegCoeffField d,
        ‖stochastic a‖ₑ ^ hm.Q ≤
          terminalCoarseBlockStochasticQEnvelope hP hStruct hm k m Qm
            (terminalStochasticWeakWeight hc m)
            (fun x : Homogenization.RegCoeffField d => x) a := by
      intro a
      simpa [stochastic, Qm] using
        terminalCoarseBlockStochasticMax_rpow_le_QEnvelope
          hP hStruct hm k m Qm
          (fun x : Homogenization.RegCoeffField d => x) a
    exact
      (MeasureTheory.lintegral_mono hpoint).trans
        (by
          simpa [polynomialBound, Qm] using
            lintegral_terminalCoarseBlockStochasticQEnvelope_le_polynomial_convolution_of_highMoment
              hP hStruct hP4 hm P Qm hkm hQscale
              (terminalStochasticWeakWeight hc m)
              (fun x : Homogenization.RegCoeffField d => x) hHM hweak)
  have hstochastic_eLp :
      MeasureTheory.eLpNorm stochastic (ENNReal.ofReal hm.Q) P ≤
        polynomialBound ^ (1 / hm.Q) := by
    have hrewrite :
        MeasureTheory.eLpNorm stochastic (ENNReal.ofReal hm.Q) P =
          (∫⁻ a, ‖stochastic a‖ₑ ^ hm.Q ∂P) ^ (1 / hm.Q) := by
      rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm
        hQenn_ne_zero hQenn_ne_top]
      simp [ENNReal.toReal_ofReal hQ_nonneg]
    calc
      MeasureTheory.eLpNorm stochastic (ENNReal.ofReal hm.Q) P =
          (∫⁻ a, ‖stochastic a‖ₑ ^ hm.Q ∂P) ^ (1 / hm.Q) := hrewrite
      _ ≤ polynomialBound ^ (1 / hm.Q) :=
          ENNReal.rpow_le_rpow hstochastic_Q
            (one_div_nonneg.mpr hQ_nonneg)
  have hdrift_eLp :
      MeasureTheory.eLpNorm
          (fun _a : Homogenization.RegCoeffField d => drift)
          (ENNReal.ofReal hm.Q) P =
        ENNReal.ofReal drift := by
    rw [MeasureTheory.eLpNorm_const drift hQenn_ne_zero (NeZero.ne P)]
    rw [Real.enorm_eq_ofReal hdrift_nonneg]
    simp [ENNReal.toReal_ofReal hQ_nonneg]
  have hbad_p_to_Q :
      MeasureTheory.eLpNorm (badEventTruncation sourceMax)
          (ENNReal.ofReal p) P ≤
        MeasureTheory.eLpNorm (badEventTruncation sourceMax)
          (ENNReal.ofReal hm.Q) P :=
    MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le
      (ENNReal.ofReal_le_ofReal hp_le_Q) hbad_meas
  have hbad_eLp :
      MeasureTheory.eLpNorm (badEventTruncation sourceMax)
          (ENNReal.ofReal p) P ≤
        polynomialBound ^ (1 / hm.Q) + ENNReal.ofReal drift := by
    calc
      MeasureTheory.eLpNorm (badEventTruncation sourceMax)
          (ENNReal.ofReal p) P
          ≤ MeasureTheory.eLpNorm (badEventTruncation sourceMax)
              (ENNReal.ofReal hm.Q) P := hbad_p_to_Q
      _ ≤ MeasureTheory.eLpNorm sourceMax (ENNReal.ofReal hm.Q) P :=
            hbad_to_source
      _ ≤ MeasureTheory.eLpNorm
            (fun a : Homogenization.RegCoeffField d => stochastic a + drift)
            (ENNReal.ofReal hm.Q) P := hsource_to_sum
      _ ≤ MeasureTheory.eLpNorm stochastic (ENNReal.ofReal hm.Q) P +
            MeasureTheory.eLpNorm
              (fun _a : Homogenization.RegCoeffField d => drift)
              (ENNReal.ofReal hm.Q) P := htriangle
      _ ≤ polynomialBound ^ (1 / hm.Q) + ENNReal.ofReal drift := by
            exact add_le_add hstochastic_eLp (le_of_eq hdrift_eLp)
  have hbad_lintegral_root :
      (∫⁻ a, ‖badEventTruncation sourceMax a‖ₑ ^ p ∂P) ^ (1 / p) ≤
        polynomialBound ^ (1 / hm.Q) + ENNReal.ofReal drift := by
    have hrewrite :
        MeasureTheory.eLpNorm (badEventTruncation sourceMax)
            (ENNReal.ofReal p) P =
          (∫⁻ a, ‖badEventTruncation sourceMax a‖ₑ ^ p ∂P) ^ (1 / p) := by
      rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm
        hpenn_ne_zero hpenn_ne_top]
      simp [ENNReal.toReal_ofReal hp_nonneg]
    simpa [hrewrite] using hbad_eLp
  have hpow := ENNReal.rpow_le_rpow hbad_lintegral_root hp_nonneg
  have hleft :
      ((∫⁻ a, ‖badEventTruncation sourceMax a‖ₑ ^ p ∂P) ^ (1 / p)) ^ p =
        ∫⁻ a, ‖badEventTruncation sourceMax a‖ₑ ^ p ∂P := by
    rw [← ENNReal.rpow_mul]
    field_simp [ne_of_gt hp_pos]
    rw [ENNReal.rpow_one]
  calc
    ∫⁻ a, ‖badEventTruncation sourceMax a‖ₑ ^
        (2 * (hP4.xi : ℝ)) ∂P
        = ∫⁻ a, ‖badEventTruncation sourceMax a‖ₑ ^ p ∂P := by
            rfl
    _ = ((∫⁻ a, ‖badEventTruncation sourceMax a‖ₑ ^ p ∂P) ^ (1 / p)) ^ p :=
            hleft.symm
    _ ≤ (polynomialBound ^ (1 / hm.Q) + ENNReal.ofReal drift) ^ p := hpow
    _ = (polynomialBound ^ (1 / hm.Q) + ENNReal.ofReal drift) ^
        (2 * (hP4.xi : ℝ)) := by
          rfl

/--
`eLpNorm` form of
`lintegral_enorm_rpow_two_mul_xi_badEventTruncation_terminalSourceMax_le_polynomial_add_drift`.
-/
theorem eLpNorm_badEventTruncation_terminalSourceMax_le_polynomial_add_drift
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d)
    (hm : HighCenteredMomentParameters d hc)
    (hparams : hP4.params = hm.p4Params) {k m : ℕ} (hkm : k ≤ m)
    (hHM :
      HighCenteredMomentEstimate hm P k
        (intermediateCoarseBlockDeviation hP hStruct
          (fun x : Homogenization.RegCoeffField d => x))) :
    let Qm : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let sourceMax :=
      terminalSpectralPositivePartSourceMax hP hStruct hc k m Qm
        (fun x : Homogenization.RegCoeffField d => x)
    let drift := terminalBadMaximalDriftSup hP hStruct hc hkm
    let polynomialBound : ENNReal :=
      ENNReal.ofReal
        (((2 +
          Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
          (hm.C_Q * (((m - k + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - k : ℕ) : ℝ)))))
    MeasureTheory.eLpNorm (badEventTruncation sourceMax)
        (ENNReal.ofReal (2 * (hP4.xi : ℝ))) P ≤
      polynomialBound ^ (1 / hm.Q) + ENNReal.ofReal drift := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  dsimp only
  let Qm : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let sourceMax : Homogenization.RegCoeffField d → ℝ :=
    terminalSpectralPositivePartSourceMax hP hStruct hc k m Qm
      (fun x : Homogenization.RegCoeffField d => x)
  let drift : ℝ := terminalBadMaximalDriftSup hP hStruct hc hkm
  let polynomialBound : ENNReal :=
    ENNReal.ofReal
      (((2 +
        Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
        (hm.C_Q * (((m - k + 1 : ℕ) : ℝ) *
          (3 : ℝ) ^
            (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
              ((m - k : ℕ) : ℝ)))))
  let p : ℝ := 2 * (hP4.xi : ℝ)
  let sourceBound : ENNReal :=
    polynomialBound ^ (1 / hm.Q) + ENNReal.ofReal drift
  have hxi_pos : 0 < (hP4.xi : ℝ) := by
    exact_mod_cast hP4.xi_pos
  have hp_pos : 0 < p := by
    dsimp [p]
    nlinarith
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hpenn_ne_zero : ENNReal.ofReal p ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le_of_gt hp_pos]
  have hpenn_ne_top : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hlin :
      ∫⁻ a, ‖badEventTruncation sourceMax a‖ₑ ^ p ∂P ≤
        sourceBound ^ p := by
    simpa [sourceBound, polynomialBound, sourceMax, Qm, drift, p] using
      lintegral_enorm_rpow_two_mul_xi_badEventTruncation_terminalSourceMax_le_polynomial_add_drift
        hP hStruct hP4 hc hm hparams hkm hHM
  have hroot :
      (∫⁻ a, ‖badEventTruncation sourceMax a‖ₑ ^ p ∂P) ^ (1 / p) ≤
        sourceBound := by
    have hpow := ENNReal.rpow_le_rpow hlin (one_div_nonneg.mpr hp_nonneg)
    calc
      (∫⁻ a, ‖badEventTruncation sourceMax a‖ₑ ^ p ∂P) ^ (1 / p)
          ≤ (sourceBound ^ p) ^ (1 / p) := hpow
      _ = sourceBound := by
          rw [← ENNReal.rpow_mul]
          field_simp [ne_of_gt hp_pos]
          rw [ENNReal.rpow_one]
  have hrewrite :
      MeasureTheory.eLpNorm (badEventTruncation sourceMax)
          (ENNReal.ofReal p) P =
        (∫⁻ a, ‖badEventTruncation sourceMax a‖ₑ ^ p ∂P) ^ (1 / p) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm
      hpenn_ne_zero hpenn_ne_top]
    simp [ENNReal.toReal_ofReal hp_nonneg]
  simpa [sourceBound, polynomialBound, sourceMax, Qm, drift, p] using
    hrewrite.le.trans hroot

/-! ## Source-budget resize moment bounds (design items L-C and L-D)

Both lemmas below repackage existing sorry-free feeders: the first-power
Hölder pairing of the bad-event truncation against the child response average
(L-D), and the capped first-power pairing of the raw source maximum against
the child response average (L-C).  No new probabilistic input is introduced.
-/

/-- Capped subadditivity: `min (x + y) 1 ≤ min x 1 + min y 1` for
nonnegative `x`, `y`. -/
theorem min_add_one_le_add_min_one {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    min (x + y) 1 ≤ min x 1 + min y 1 := by
  rcases le_total 1 x with hx1 | hx1
  · have hminx : min x 1 = 1 := min_eq_right hx1
    have hminy : 0 ≤ min y 1 := le_min hy zero_le_one
    calc
      min (x + y) 1 ≤ 1 := min_le_right _ _
      _ ≤ min x 1 + min y 1 := by rw [hminx]; linarith
  · rcases le_total 1 y with hy1 | hy1
    · have hminy : min y 1 = 1 := min_eq_right hy1
      have hminx : 0 ≤ min x 1 := le_min hx zero_le_one
      calc
        min (x + y) 1 ≤ 1 := min_le_right _ _
        _ ≤ min x 1 + min y 1 := by rw [hminy]; linarith
    · have hminx : min x 1 = x := min_eq_left hx1
      have hminy : min y 1 = y := min_eq_left hy1
      calc
        min (x + y) 1 ≤ x + y := min_le_left _ _
        _ = min x 1 + min y 1 := by rw [hminx, hminy]

/-- For nonnegative reals the squared extended norm is the `ofReal` square. -/
private theorem enorm_rpow_two_eq_ofReal_sq' {x : ℝ} (hx : 0 ≤ x) :
    ‖x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (x ^ 2) := by
  rw [Real.enorm_eq_ofReal hx, ENNReal.ofReal_rpow_of_nonneg hx (by norm_num)]
  congr 1
  rw [Real.rpow_two]

/-- Private copy of the stationary child-response zeta-root comparison
(the canonical copy lives downstream in `RawHighContrastWeakNorm.lean`, which
imports this file, so it cannot be used here). -/
theorem childResponseAverage_zetaRoot_le_responseMoment_of_stationary
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hstat : Homogenization.Book.Ch04.RestrictionStationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Homogenization.Vec d) :
    let ζ := section53CoarseFluctuationZeta hP4
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let childAvg := fun a : Homogenization.RegCoeffField d =>
      Homogenization.descendantsAverage Q (m - k)
        (fun R => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
    (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) ≤
      coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
  classical
  dsimp only
  let ζ := section53CoarseFluctuationZeta hP4
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let childAvg : Homogenization.RegCoeffField d → ℝ := fun a =>
    Homogenization.descendantsAverage Q (m - k)
      (fun R => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by
    exact_mod_cast Nat.zero_le k
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by
    exact_mod_cast hkm.le
  have hchild_nonneg_all : ∀ a, 0 ≤ childAvg a := by
    intro a
    dsimp [childAvg]
    exact Homogenization.descendantsAverage_nonneg Q (m - k)
      (fun R => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
      (fun R _hR =>
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet_nonneg R p_e q_e a)
  have hIntLe :=
    integral_rpow_descendantsAverage_restrictionResponseJObservableCubeSet_originCube_le_originCube_of_stationary
      hP hstat hStruct hP4 hk_nonneg hkm_int p_e q_e
  have hChildPow_nonneg :
      0 ≤ ∫ a, childAvg a ^ ζ ∂P := by
    refine MeasureTheory.integral_nonneg fun a => ?_
    exact Real.rpow_nonneg (hchild_nonneg_all a) _
  have hζ_nonneg : 0 ≤ ζ := by
    simpa [ζ] using (section53CoarseFluctuationZeta_pos hP4).le
  have hroot_nonneg : 0 ≤ 1 / ζ := by
    exact div_nonneg zero_le_one hζ_nonneg
  have hroot :=
    Real.rpow_le_rpow hChildPow_nonneg
      (by simpa [childAvg, Q, ζ, p_e, q_e, Real.rpow_eq_pow] using hIntLe)
      hroot_nonneg
  simpa [coarseFluctuationResponseMomentAtScale, childAvg, Q, ζ, p_e, q_e,
    one_div] using hroot

/-- A capped nonnegative observable lies in every `L^p` on a finite measure
space. -/
theorem memLp_min_one_of_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ]
    {F : Ω → ℝ} (hF : MeasureTheory.AEStronglyMeasurable F μ)
    (hF_nonneg : ∀ ω, 0 ≤ F ω) (p : ENNReal) :
    MeasureTheory.MemLp (fun ω => min (F ω) 1) p μ := by
  refine MeasureTheory.MemLp.of_bound
    ((hF.aemeasurable.min aemeasurable_const).aestronglyMeasurable) 1 ?_
  filter_upwards with ω
  have h0 : 0 ≤ min (F ω) 1 := le_min (hF_nonneg ω) zero_le_one
  have h1 : min (F ω) 1 ≤ 1 := min_le_right _ _
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

/-- Workhorse for the L-C stochastic pieces: the `xi`-th moment of a capped
nonnegative observable is dominated by any finite bound on its `L^2`
lintegral, because the cap pushes the exponent `xi >= 2` down to `2`. -/
theorem integral_min_one_rpow_le_lintegral_enorm_sq_toReal
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ]
    {F : Ω → ℝ} (hF : MeasureTheory.AEStronglyMeasurable F μ)
    (hF_nonneg : ∀ ω, 0 ≤ F ω)
    {ξ : ℝ} (hξ_two : (2 : ℝ) ≤ ξ)
    {L : ENNReal} (hL : (∫⁻ ω, ‖F ω‖ₑ ^ (2 : ℝ) ∂μ) ≤ L) (hL_ne_top : L ≠ ⊤) :
    ∫ ω, min (F ω) 1 ^ ξ ∂μ ≤ L.toReal := by
  classical
  have hξ_pos : (0 : ℝ) < ξ := lt_of_lt_of_le two_pos hξ_two
  have hmin_nonneg : ∀ ω, 0 ≤ min (F ω) 1 := fun ω =>
    le_min (hF_nonneg ω) zero_le_one
  have hpow_nonneg : ∀ ω, 0 ≤ min (F ω) 1 ^ ξ := fun ω =>
    Real.rpow_nonneg (hmin_nonneg ω) _
  have hmin_asm :
      MeasureTheory.AEStronglyMeasurable (fun ω => min (F ω) 1) μ :=
    (hF.aemeasurable.min aemeasurable_const).aestronglyMeasurable
  have hpow_asm :
      MeasureTheory.AEStronglyMeasurable (fun ω => min (F ω) 1 ^ ξ) μ :=
    ((Real.continuous_rpow_const hξ_pos.le).measurable.comp_aemeasurable
      hmin_asm.aemeasurable).aestronglyMeasurable
  have hpow_le_one : ∀ ω, min (F ω) 1 ^ ξ ≤ 1 := fun ω =>
    Real.rpow_le_one (hmin_nonneg ω) (min_le_right _ _) hξ_pos.le
  have hInt :
      MeasureTheory.Integrable (fun ω => min (F ω) 1 ^ ξ) μ := by
    refine MeasureTheory.memLp_one_iff_integrable.mp ?_
    refine MeasureTheory.MemLp.of_bound hpow_asm 1 ?_
    filter_upwards with ω
    simpa [Real.norm_eq_abs, abs_of_nonneg (hpow_nonneg ω)] using
      hpow_le_one ω
  have hpoint :
      ∀ ω, ENNReal.ofReal (min (F ω) 1 ^ ξ) ≤ ‖F ω‖ₑ ^ (2 : ℝ) := by
    intro ω
    have h1 : min (F ω) 1 ^ ξ ≤ min (F ω) 1 ^ (2 : ℝ) := by
      rcases eq_or_lt_of_le (hmin_nonneg ω) with h0 | h0
      · rw [← h0, Real.zero_rpow (ne_of_gt hξ_pos),
          Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0)]
      · exact Real.rpow_le_rpow_of_exponent_ge h0 (min_le_right _ _) hξ_two
    have h2 : min (F ω) 1 ^ (2 : ℝ) ≤ F ω ^ 2 := by
      rw [Real.rpow_two]
      simpa [pow_two] using
        mul_self_le_mul_self (hmin_nonneg ω) (min_le_left (F ω) 1)
    calc
      ENNReal.ofReal (min (F ω) 1 ^ ξ)
          ≤ ENNReal.ofReal (F ω ^ 2) :=
            ENNReal.ofReal_le_ofReal (h1.trans h2)
      _ = ‖F ω‖ₑ ^ (2 : ℝ) := (enorm_rpow_two_eq_ofReal_sq' (hF_nonneg ω)).symm
  have hofReal_int :
      ENNReal.ofReal (∫ ω, min (F ω) 1 ^ ξ ∂μ) =
        ∫⁻ ω, ENNReal.ofReal (min (F ω) 1 ^ ξ) ∂μ :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall hpow_nonneg)
  have hlin :
      (∫⁻ ω, ENNReal.ofReal (min (F ω) 1 ^ ξ) ∂μ) ≤ L :=
    le_trans (MeasureTheory.lintegral_mono fun ω => hpoint ω) hL
  have hint_nonneg : 0 ≤ ∫ ω, min (F ω) 1 ^ ξ ∂μ :=
    MeasureTheory.integral_nonneg hpow_nonneg
  calc
    ∫ ω, min (F ω) 1 ^ ξ ∂μ
        = (ENNReal.ofReal (∫ ω, min (F ω) 1 ^ ξ ∂μ)).toReal :=
          (ENNReal.toReal_ofReal hint_nonneg).symm
    _ ≤ L.toReal := by
          refine ENNReal.toReal_mono hL_ne_top ?_
          rw [hofReal_int]
          exact hlin

/--
Source labels `p.HC.CR`, `a.HM`, `l.union.bound`, and `e.M.def`: full-buffer
form of the un-squared source-max bad-event `L^{2 xi}` estimate.  The local
window `k..m` bad-event factor is dominated by the enlarged `N..m` source
maximum, so the polynomial envelope decays over the manuscript buffer length
`m - N`.
-/
theorem eLpNorm_badEventTruncation_terminalSourceMax_le_global_polynomial_add_drift_of_start_le
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d)
    (hm : HighCenteredMomentParameters d hc)
    (hparams : hP4.params = hm.p4Params) {N k m : ℕ}
    (hNk : N ≤ k) (hkm : k ≤ m)
    (hHM :
      HighCenteredMomentEstimate hm P N
        (intermediateCoarseBlockDeviation hP hStruct
          (fun x : Homogenization.RegCoeffField d => x))) :
    let Qm : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let sourceMax :=
      terminalSpectralPositivePartSourceMax hP hStruct hc k m Qm
        (fun x : Homogenization.RegCoeffField d => x)
    let globalDrift := terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm)
    let polynomialBound : ENNReal :=
      ENNReal.ofReal
        (((2 +
          Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
          (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - N : ℕ) : ℝ)))))
    MeasureTheory.eLpNorm (badEventTruncation sourceMax)
        (ENNReal.ofReal (2 * (hP4.xi : ℝ))) P ≤
      polynomialBound ^ (1 / hm.Q) + ENNReal.ofReal globalDrift := by
  classical
  dsimp only
  let Qm : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let sourceMax : Homogenization.RegCoeffField d → ℝ :=
    terminalSpectralPositivePartSourceMax hP hStruct hc k m Qm
      (fun x : Homogenization.RegCoeffField d => x)
  let globalSourceMax : Homogenization.RegCoeffField d → ℝ :=
    terminalSpectralPositivePartSourceMax hP hStruct hc N m Qm
      (fun x : Homogenization.RegCoeffField d => x)
  have hlocal_le_global :
      MeasureTheory.eLpNorm (badEventTruncation sourceMax)
          (ENNReal.ofReal (2 * (hP4.xi : ℝ))) P ≤
        MeasureTheory.eLpNorm (badEventTruncation globalSourceMax)
          (ENNReal.ofReal (2 * (hP4.xi : ℝ))) P := by
    refine MeasureTheory.eLpNorm_mono ?_
    intro a
    have hbad_le :
        badEventTruncation sourceMax a ≤
          badEventTruncation globalSourceMax a := by
      simpa [sourceMax, globalSourceMax, Qm] using
        badEventTruncation_terminalSpectralPositivePartSourceMax_le_of_start_le
          hP hStruct hc hNk Qm (fun x : Homogenization.RegCoeffField d => x) a
    have hbad_nonneg : 0 ≤ badEventTruncation sourceMax a :=
      badEventTruncation_nonneg
        (terminalSpectralPositivePartSourceMax_nonneg hP hStruct hc k m Qm
          (fun x : Homogenization.RegCoeffField d => x) a)
    have hbad_global_nonneg : 0 ≤ badEventTruncation globalSourceMax a :=
      badEventTruncation_nonneg
        (terminalSpectralPositivePartSourceMax_nonneg hP hStruct hc N m Qm
          (fun x : Homogenization.RegCoeffField d => x) a)
    simpa [Real.norm_eq_abs, abs_of_nonneg hbad_nonneg,
      abs_of_nonneg hbad_global_nonneg] using hbad_le
  refine hlocal_le_global.trans ?_
  simpa [globalSourceMax, Qm] using
    eLpNorm_badEventTruncation_terminalSourceMax_le_polynomial_add_drift
      hP hStruct hP4 hc hm hparams (hNk.trans hkm) hHM

/--
Design item L-D.  Source labels `p.HC.CR`, `a.HM`, `l.union.bound`,
`e.M.def`, and `e.J.moment.bound`: first-power source-budget pairing.  The
bad-event truncation of the terminal source maximum is paired against the
child response average by Hölder with the conjugate pair `(xi, zeta)`
(`zeta = xi / (xi - 1)`); on the probability space the `L^xi` norm of the
truncation is dominated by its `L^{2 xi}` norm, which the full-buffer
high-moment feeder bounds by the polynomial root plus the deterministic drift
supremum.
-/
theorem integral_badEventTruncation_terminalSourceMax_mul_childResponseAverage_le_responseMoment_mul_global_polynomialRoot_add_drift_of_start_le
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hstat : Homogenization.Book.Ch04.RestrictionStationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d)
    (hm : HighCenteredMomentParameters d hc)
    (hparams : hP4.params = hm.p4Params) {N k m : ℕ}
    (hNk : N ≤ k) (hkm : k < m)
    (hHM :
      HighCenteredMomentEstimate hm P N
        (intermediateCoarseBlockDeviation hP hStruct
          (fun x : Homogenization.RegCoeffField d => x)))
    (e : Homogenization.Vec d) :
    let Qm : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let childAvg := fun a : Homogenization.RegCoeffField d =>
      Homogenization.descendantsAverage Qm (m - k)
        (fun R => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
    let sourceMax :=
      terminalSpectralPositivePartSourceMax hP hStruct hc k m Qm
        (fun x : Homogenization.RegCoeffField d => x)
    let globalDrift := terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)
    let polynomialBound : ENNReal :=
      ENNReal.ofReal
        (((2 +
          Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
          (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - N : ℕ) : ℝ)))))
    MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          badEventTruncation sourceMax a * childAvg a) P ∧
      ∫ a, badEventTruncation sourceMax a * childAvg a ∂P ≤
        coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e *
          ((polynomialBound ^ (1 / hm.Q)).toReal + globalDrift) := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  dsimp only
  let ζ := section53CoarseFluctuationZeta hP4
  let Qm : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let childAvg : Homogenization.RegCoeffField d → ℝ := fun a =>
    Homogenization.descendantsAverage Qm (m - k)
      (fun R => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
  let sourceMax : Homogenization.RegCoeffField d → ℝ :=
    terminalSpectralPositivePartSourceMax hP hStruct hc k m Qm
      (fun x : Homogenization.RegCoeffField d => x)
  let badTrunc : Homogenization.RegCoeffField d → ℝ := badEventTruncation sourceMax
  let globalDrift : ℝ := terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)
  let polynomialBound : ENNReal :=
    ENNReal.ofReal
      (((2 +
        Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
        (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
          (3 : ℝ) ^
            (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
              ((m - N : ℕ) : ℝ)))))
  let sourceBound : ENNReal :=
    polynomialBound ^ (1 / hm.Q) + ENNReal.ofReal globalDrift
  let responseMoment : ℝ :=
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  have hxi_pos : (0 : ℝ) < (hP4.xi : ℝ) := by
    exact_mod_cast hP4.xi_pos
  have hxi_one : 1 ≤ hP4.xi := Nat.succ_le_of_lt hP4.xi_pos
  have hsource_nonneg : ∀ a, 0 ≤ sourceMax a :=
    terminalSpectralPositivePartSourceMax_nonneg hP hStruct hc k m Qm
      (fun x : Homogenization.RegCoeffField d => x)
  have hbad_nonneg : ∀ a, 0 ≤ badTrunc a := fun a =>
    badEventTruncation_nonneg (hsource_nonneg a)
  have hchild_nonneg : ∀ a, 0 ≤ childAvg a := by
    intro a
    dsimp [childAvg]
    exact Homogenization.descendantsAverage_nonneg Qm (m - k)
      (fun R => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
      (fun R _hR =>
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet_nonneg R p_e q_e a)
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by
    exact_mod_cast Nat.zero_le k
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by
    exact_mod_cast hkm.le
  have hdepth : Int.toNat ((m : ℤ) - (k : ℤ)) = m - k := by
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hkm_int)]
    exact (Nat.cast_sub hkm.le).symm
  have hChildMem :
      MeasureTheory.MemLp childAvg (ENNReal.ofReal ζ) P := by
    simpa [childAvg, Qm, p_e, q_e, ζ, hdepth] using
      memLp_zeta_descendantsAverage_restrictionResponseJObservableCubeSet_originCube_from_P4_of_stationary
        hP hstat hStruct hP4 hk_nonneg hkm_int p_e q_e
  have hSourceMem :
      MeasureTheory.MemLp sourceMax (ENNReal.ofReal hm.Q) P := by
    simpa [sourceMax, Qm] using
      memLp_terminalSpectralPositivePartSourceMax_origin_highMoment
        hP hStruct hP4 hm hkm.le
        (HighCenteredMomentEstimate.of_start_le hNk hHM)
  have hxi_le_Q : (hP4.xi : ℝ) ≤ hm.Q := by
    have h2 := highCenteredMoment_two_mul_p4_xi_le_Q hm hP4 hparams
    linarith
  have hBadMem :
      MeasureTheory.MemLp badTrunc (ENNReal.ofReal (hP4.xi : ℝ)) P := by
    refine
      (hSourceMem.mono_exponent (ENNReal.ofReal_le_ofReal hxi_le_Q)).of_le
        (aestronglyMeasurable_badEventTruncation hSourceMem.1) ?_
    filter_upwards with a
    have hle : badTrunc a ≤ sourceMax a :=
      badEventTruncation_le_self_of_nonneg (hsource_nonneg a)
    simpa [Real.norm_eq_abs, abs_of_nonneg (hbad_nonneg a),
      abs_of_nonneg (hsource_nonneg a)] using hle
  have hHolderXiZeta : (hP4.xi : ℝ).HolderConjugate ζ :=
    holderConjugate_xi_section53CoarseFluctuationZeta hP4
  letI : ENNReal.HolderTriple
      (ENNReal.ofReal (hP4.xi : ℝ)) (ENNReal.ofReal ζ) 1 := by
    simpa using Real.HolderTriple.ennrealOfReal hHolderXiZeta
  have hInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d => badTrunc a * childAvg a) P := by
    simpa using hBadMem.integrable_mul hChildMem
  have hHolder :
      ∫ a, badTrunc a * childAvg a ∂P ≤
        (∫ a, badTrunc a ^ (hP4.xi : ℝ) ∂P) ^ (1 / (hP4.xi : ℝ)) *
          (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) :=
    MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hHolderXiZeta
      (Filter.Eventually.of_forall hbad_nonneg)
      (Filter.Eventually.of_forall hchild_nonneg) hBadMem hChildMem
  have hchildRoot_le :
      (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) ≤ responseMoment := by
    simpa [childAvg, Qm, ζ, p_e, q_e, responseMoment] using
      childResponseAverage_zetaRoot_le_responseMoment_of_stationary
        hP hstat hStruct hP4 hkm e
  have hchildRoot_nonneg :
      0 ≤ (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) :=
    Real.rpow_nonneg
      (MeasureTheory.integral_nonneg fun a =>
        Real.rpow_nonneg (hchild_nonneg a) _) _
  have hresponse_nonneg : 0 ≤ responseMoment := by
    simpa [responseMoment] using
      coarseFluctuationResponseMomentAtScale_nonneg hP hStruct hP4 k m e
  have hBadMemNat :
      MeasureTheory.MemLp badTrunc ((hP4.xi : ℕ) : ENNReal) P := by
    simpa [ENNReal.ofReal_natCast] using hBadMem
  have hbadRoot_eq :
      (∫ a, badTrunc a ^ (hP4.xi : ℝ) ∂P) ^ (1 / (hP4.xi : ℝ)) =
        (MeasureTheory.eLpNorm badTrunc ((hP4.xi : ℕ) : ENNReal) P).toReal := by
    have htoReal :=
      Homogenization.Book.Ch04.toReal_eLpNorm_eq_integral_norm_pow_rpow_inv
        (μ := P) (f := badTrunc) (p := hP4.xi) hxi_one hBadMemNat
    calc
      (∫ a, badTrunc a ^ (hP4.xi : ℝ) ∂P) ^ (1 / (hP4.xi : ℝ))
          = (∫ a, ‖badTrunc a‖ ^ hP4.xi ∂P) ^ (1 / (hP4.xi : ℝ)) := by
            congr 1
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with a
            rw [Real.norm_of_nonneg (hbad_nonneg a), Real.rpow_natCast]
      _ = (MeasureTheory.eLpNorm badTrunc ((hP4.xi : ℕ) : ENNReal) P).toReal :=
            htoReal.symm
  have hmono_eLp :
      MeasureTheory.eLpNorm badTrunc ((hP4.xi : ℕ) : ENNReal) P ≤
        MeasureTheory.eLpNorm badTrunc
          (ENNReal.ofReal (2 * (hP4.xi : ℝ))) P := by
    have hle : ((hP4.xi : ℕ) : ENNReal) ≤ ENNReal.ofReal (2 * (hP4.xi : ℝ)) := by
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    exact MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le hle hBadMem.1
  have hglobal_eLp :
      MeasureTheory.eLpNorm badTrunc
          (ENNReal.ofReal (2 * (hP4.xi : ℝ))) P ≤ sourceBound := by
    simpa [badTrunc, sourceBound, polynomialBound, sourceMax, Qm,
      globalDrift] using
      eLpNorm_badEventTruncation_terminalSourceMax_le_global_polynomial_add_drift_of_start_le
        hP hStruct hP4 hc hm hparams hNk hkm.le hHM
  have hQ_pos : 0 < hm.Q := highCenteredMoment_Q_pos hm
  have hpolyRoot_ne_top : polynomialBound ^ (1 / hm.Q) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg
      (one_div_nonneg.mpr hQ_pos.le) ENNReal.ofReal_ne_top
  have hsourceBound_ne_top : sourceBound ≠ ⊤ := by
    dsimp [sourceBound]
    exact ENNReal.add_ne_top.2 ⟨hpolyRoot_ne_top, ENNReal.ofReal_ne_top⟩
  have hdrift_nonneg : 0 ≤ globalDrift :=
    terminalBadMaximalDriftSup_nonneg hP hStruct hc (hNk.trans hkm.le)
  have hsourceBound_toReal :
      sourceBound.toReal = (polynomialBound ^ (1 / hm.Q)).toReal + globalDrift := by
    dsimp [sourceBound]
    rw [ENNReal.toReal_add hpolyRoot_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hdrift_nonneg]
  have hbadRoot_le :
      (∫ a, badTrunc a ^ (hP4.xi : ℝ) ∂P) ^ (1 / (hP4.xi : ℝ)) ≤
        (polynomialBound ^ (1 / hm.Q)).toReal + globalDrift := by
    rw [hbadRoot_eq, ← hsourceBound_toReal]
    exact ENNReal.toReal_mono hsourceBound_ne_top
      (hmono_eLp.trans hglobal_eLp)
  have hbound_nonneg :
      0 ≤ (polynomialBound ^ (1 / hm.Q)).toReal + globalDrift :=
    add_nonneg ENNReal.toReal_nonneg hdrift_nonneg
  constructor
  · simpa [badTrunc, sourceMax, childAvg, Qm, p_e, q_e] using hInt
  · calc
      ∫ a, badEventTruncation sourceMax a * childAvg a ∂P
          = ∫ a, badTrunc a * childAvg a ∂P := by rfl
      _ ≤ (∫ a, badTrunc a ^ (hP4.xi : ℝ) ∂P) ^ (1 / (hP4.xi : ℝ)) *
            (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) := hHolder
      _ ≤ ((polynomialBound ^ (1 / hm.Q)).toReal + globalDrift) *
            responseMoment :=
          mul_le_mul hbadRoot_le hchildRoot_le hchildRoot_nonneg hbound_nonneg
      _ = responseMoment *
            ((polynomialBound ^ (1 / hm.Q)).toReal + globalDrift) := by ring

/--
Design item L-C.  Source labels `p.HC.CR`, `e.M.def`, `M_m^st`,
`l.union.bound`, and `e.J.moment.bound`: capped first-power source pairing.
The capped source maximum is split through the stochastic/subthreshold/drift
envelope; the drift piece pays first power against the child response
expectation, while the stochastic and subthreshold pieces pay by Hölder with
the conjugate pair `(xi, zeta)` after the cap pushes the exponent `xi >= 2`
down to the `L^2` control supplied by `hstochRoot`.

The free scalar `stochRoot` is fed by the union-bound producer
`exists_bufferExponent_lintegral_terminalCoarseBlockStochasticMax_add_subthresholdMax_le_memoryGrid_of_Nstar`:
its output bounds exactly the ENNReal sum appearing in `hfin`/`hstochRoot`.
The exponent in `hstochRoot` is `1 / xi`; the prefactor `2` accounts for the
two capped Hölder pieces (stochastic and subthreshold) sharing one `L^2` sum.
-/
theorem integral_min_terminalSourceMax_one_mul_childResponseAverage_le_stochasticRoot_add_min_drift_one_mul_responseMoment
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hstat : Homogenization.Book.Ch04.RestrictionStationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {N k m : ℕ}
    (hNk : N ≤ k) (hkm : k < m)
    (M_sub : ℕ → Homogenization.RegCoeffField d → ℝ)
    (hMsub : AEMeasurable (M_sub m) P)
    (e : Homogenization.Vec d)
    {stochRoot : ℝ}
    (hfin :
      (∫⁻ ω, ‖terminalCoarseBlockStochasticMax hP hStruct hc N m
          (Homogenization.originCube d (m : ℤ))
          (fun x : Homogenization.RegCoeffField d => x) ω‖ₑ ^ (2 : ℝ) ∂P) +
        (∫⁻ ω, ‖M_sub m ω‖ₑ ^ (2 : ℝ) ∂P) ≠ ⊤)
    (hstochRoot :
      2 * (((∫⁻ ω, ‖terminalCoarseBlockStochasticMax hP hStruct hc N m
            (Homogenization.originCube d (m : ℤ))
            (fun x : Homogenization.RegCoeffField d => x) ω‖ₑ ^ (2 : ℝ) ∂P) +
          (∫⁻ ω, ‖M_sub m ω‖ₑ ^ (2 : ℝ) ∂P)).toReal ^ (1 / (hP4.xi : ℝ))) ≤
        stochRoot) :
    let Qm : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let childAvg := fun a : Homogenization.RegCoeffField d =>
      Homogenization.descendantsAverage Qm (m - k)
        (fun R => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
    let sourceMax :=
      terminalSpectralPositivePartSourceMax hP hStruct hc k m Qm
        (fun x : Homogenization.RegCoeffField d => x)
    ∫ a, min (sourceMax a) 1 * childAvg a ∂P ≤
      (stochRoot +
          min (terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) 1) *
        coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  dsimp only
  let ζ := section53CoarseFluctuationZeta hP4
  let ξr : ℝ := (hP4.xi : ℝ)
  let Qm : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let childAvg : Homogenization.RegCoeffField d → ℝ := fun a =>
    Homogenization.descendantsAverage Qm (m - k)
      (fun R => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
  let sourceMax : Homogenization.RegCoeffField d → ℝ :=
    terminalSpectralPositivePartSourceMax hP hStruct hc k m Qm
      (fun x : Homogenization.RegCoeffField d => x)
  let S : Homogenization.RegCoeffField d → ℝ :=
    terminalCoarseBlockStochasticMax hP hStruct hc N m Qm
      (fun x : Homogenization.RegCoeffField d => x)
  let T : Homogenization.RegCoeffField d → ℝ := fun a => |M_sub m a|
  let D : ℝ := terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)
  let lintSum : ENNReal :=
    (∫⁻ ω, ‖S ω‖ₑ ^ (2 : ℝ) ∂P) + (∫⁻ ω, ‖M_sub m ω‖ₑ ^ (2 : ℝ) ∂P)
  let sumRoot : ℝ := lintSum.toReal ^ (1 / ξr)
  let responseMoment : ℝ :=
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  have hxi_two : (2 : ℝ) ≤ ξr := by
    show (2 : ℝ) ≤ (hP4.xi : ℝ)
    exact_mod_cast hP4.two_le_xi
  have hxi_pos : (0 : ℝ) < ξr := lt_of_lt_of_le two_pos hxi_two
  have hζ_one : 1 ≤ ζ := (one_lt_section53CoarseFluctuationZeta hP4).le
  have hS_nonneg : ∀ a, 0 ≤ S a :=
    terminalCoarseBlockStochasticMax_nonneg hP hStruct hc N m Qm
      (fun x : Homogenization.RegCoeffField d => x)
  have hT_nonneg : ∀ a, 0 ≤ T a := fun a => abs_nonneg _
  have hD_nonneg : 0 ≤ D :=
    terminalBadMaximalDriftSup_nonneg hP hStruct hc (hNk.trans hkm.le)
  have hsrc_nonneg : ∀ a, 0 ≤ sourceMax a :=
    terminalSpectralPositivePartSourceMax_nonneg hP hStruct hc k m Qm
      (fun x : Homogenization.RegCoeffField d => x)
  have hchild_nonneg : ∀ a, 0 ≤ childAvg a := by
    intro a
    dsimp [childAvg]
    exact Homogenization.descendantsAverage_nonneg Qm (m - k)
      (fun R => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
      (fun R _hR =>
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet_nonneg R p_e q_e a)
  have hS_asm : MeasureTheory.AEStronglyMeasurable S P := by
    simpa [S, Qm] using
      aestronglyMeasurable_terminalCoarseBlockStochasticMax_origin
        hP hStruct hP4 hc N m
  have hT_asm : MeasureTheory.AEStronglyMeasurable T P := by
    simpa [T, Real.norm_eq_abs] using hMsub.aestronglyMeasurable.norm
  have hsrc_asm : MeasureTheory.AEStronglyMeasurable sourceMax P := by
    simpa [sourceMax, Qm] using
      aestronglyMeasurable_terminalSpectralPositivePartSourceMax_origin
        hP hStruct hc k m
  -- membership of the child average and the capped observables
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by
    exact_mod_cast Nat.zero_le k
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by
    exact_mod_cast hkm.le
  have hdepth : Int.toNat ((m : ℤ) - (k : ℤ)) = m - k := by
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hkm_int)]
    exact (Nat.cast_sub hkm.le).symm
  have hChildMem :
      MeasureTheory.MemLp childAvg (ENNReal.ofReal ζ) P := by
    simpa [childAvg, Qm, p_e, q_e, ζ, hdepth] using
      memLp_zeta_descendantsAverage_restrictionResponseJObservableCubeSet_originCube_from_P4_of_stationary
        hP hstat hStruct hP4 hk_nonneg hkm_int p_e q_e
  have hminS_mem :
      MeasureTheory.MemLp (fun a => min (S a) 1) (ENNReal.ofReal ξr) P :=
    memLp_min_one_of_aestronglyMeasurable hS_asm hS_nonneg _
  have hminT_mem :
      MeasureTheory.MemLp (fun a => min (T a) 1) (ENNReal.ofReal ξr) P :=
    memLp_min_one_of_aestronglyMeasurable hT_asm hT_nonneg _
  have hminSrc_mem :
      MeasureTheory.MemLp (fun a => min (sourceMax a) 1)
        (ENNReal.ofReal ξr) P :=
    memLp_min_one_of_aestronglyMeasurable hsrc_asm hsrc_nonneg _
  have hHolderXiZeta : ξr.HolderConjugate ζ :=
    holderConjugate_xi_section53CoarseFluctuationZeta hP4
  letI : ENNReal.HolderTriple (ENNReal.ofReal ξr) (ENNReal.ofReal ζ) 1 := by
    simpa using Real.HolderTriple.ennrealOfReal hHolderXiZeta
  have hChildInt : MeasureTheory.Integrable childAvg P :=
    hChildMem.integrable (ENNReal.one_le_ofReal.mpr hζ_one)
  have hIS :
      MeasureTheory.Integrable
        (fun a => min (S a) 1 * childAvg a) P := by
    simpa using hminS_mem.integrable_mul hChildMem
  have hIT :
      MeasureTheory.Integrable
        (fun a => min (T a) 1 * childAvg a) P := by
    simpa using hminT_mem.integrable_mul hChildMem
  have hID :
      MeasureTheory.Integrable
        (fun a => min D 1 * childAvg a) P :=
    hChildInt.const_mul (min D 1)
  have hILHS :
      MeasureTheory.Integrable
        (fun a => min (sourceMax a) 1 * childAvg a) P := by
    simpa using hminSrc_mem.integrable_mul hChildMem
  have hIST :
      MeasureTheory.Integrable
        (fun a => min (S a) 1 * childAvg a + min (T a) 1 * childAvg a) P := by
    simpa using hIS.add hIT
  -- pointwise envelope split
  have hsplit : ∀ a,
      min (sourceMax a) 1 ≤ min (S a) 1 + min (T a) 1 + min D 1 := by
    intro a
    have hstart :
        sourceMax a ≤
          terminalSpectralPositivePartSourceMax hP hStruct hc N m Qm
            (fun x : Homogenization.RegCoeffField d => x) a := by
      simpa [sourceMax, Qm] using
        terminalSpectralPositivePartSourceMax_le_of_start_le
          hP hStruct hc hNk Qm (fun x : Homogenization.RegCoeffField d => x) a
    have henv :
        terminalSpectralPositivePartSourceMax hP hStruct hc N m Qm
            (fun x : Homogenization.RegCoeffField d => x) a ≤
          S a + T a + D := by
      simpa [terminalBadMaximalSplitEnvelope, S, T, D, Qm] using
        terminalSpectralPositivePartSourceMax_le_terminalBadMaximalSplitEnvelope
          hP hStruct hc (hNk.trans hkm.le) Qm
          (fun x : Homogenization.RegCoeffField d => x) M_sub a
    have h1 : min (sourceMax a) 1 ≤ min (S a + T a + D) 1 :=
      min_le_min (hstart.trans henv) le_rfl
    have h2 : min (S a + T a + D) 1 ≤ min (S a + T a) 1 + min D 1 :=
      min_add_one_le_add_min_one
        (add_nonneg (hS_nonneg a) (hT_nonneg a)) hD_nonneg
    have h3 : min (S a + T a) 1 ≤ min (S a) 1 + min (T a) 1 :=
      min_add_one_le_add_min_one (hS_nonneg a) (hT_nonneg a)
    linarith
  have hpt :
      (fun a => min (sourceMax a) 1 * childAvg a) ≤
        fun a =>
          (min (S a) 1 * childAvg a + min (T a) 1 * childAvg a) +
            min D 1 * childAvg a := by
    intro a
    have := mul_le_mul_of_nonneg_right (hsplit a) (hchild_nonneg a)
    calc
      min (sourceMax a) 1 * childAvg a
          ≤ (min (S a) 1 + min (T a) 1 + min D 1) * childAvg a := this
      _ = (min (S a) 1 * childAvg a + min (T a) 1 * childAvg a) +
            min D 1 * childAvg a := by ring
  -- the three pieces
  have hzetaRoot_le :
      (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) ≤ responseMoment := by
    simpa [childAvg, Qm, ζ, p_e, q_e, responseMoment] using
      childResponseAverage_zetaRoot_le_responseMoment_of_stationary
        hP hstat hStruct hP4 hkm e
  have hzetaRoot_nonneg :
      0 ≤ (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) :=
    Real.rpow_nonneg
      (MeasureTheory.integral_nonneg fun a =>
        Real.rpow_nonneg (hchild_nonneg a) _) _
  have hresponse_nonneg : 0 ≤ responseMoment := by
    simpa [responseMoment] using
      coarseFluctuationResponseMomentAtScale_nonneg hP hStruct hP4 k m e
  have hsumRoot_nonneg : 0 ≤ sumRoot :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  -- stochastic piece
  have hS_pow_le : ∫ a, min (S a) 1 ^ ξr ∂P ≤ lintSum.toReal :=
    integral_min_one_rpow_le_lintegral_enorm_sq_toReal hS_asm hS_nonneg
      hxi_two le_self_add hfin
  have hS_root_le :
      (∫ a, min (S a) 1 ^ ξr ∂P) ^ (1 / ξr) ≤ sumRoot :=
    Real.rpow_le_rpow
      (MeasureTheory.integral_nonneg fun a =>
        Real.rpow_nonneg (le_min (hS_nonneg a) zero_le_one) _)
      hS_pow_le (one_div_nonneg.mpr hxi_pos.le)
  have hS_holder :
      ∫ a, min (S a) 1 * childAvg a ∂P ≤
        (∫ a, min (S a) 1 ^ ξr ∂P) ^ (1 / ξr) *
          (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) :=
    MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hHolderXiZeta
      (Filter.Eventually.of_forall fun a => le_min (hS_nonneg a) zero_le_one)
      (Filter.Eventually.of_forall hchild_nonneg) hminS_mem hChildMem
  have hS_piece :
      ∫ a, min (S a) 1 * childAvg a ∂P ≤ sumRoot * responseMoment :=
    hS_holder.trans
      (mul_le_mul hS_root_le hzetaRoot_le hzetaRoot_nonneg hsumRoot_nonneg)
  -- subthreshold piece
  have hT_lint :
      (∫⁻ ω, ‖T ω‖ₑ ^ (2 : ℝ) ∂P) ≤ lintSum := by
    have heq :
        (∫⁻ ω, ‖T ω‖ₑ ^ (2 : ℝ) ∂P) =
          ∫⁻ ω, ‖M_sub m ω‖ₑ ^ (2 : ℝ) ∂P := by
      refine MeasureTheory.lintegral_congr fun ω => ?_
      congr 1
      simp [T, Real.enorm_eq_ofReal_abs, abs_abs]
    rw [heq]
    exact le_add_self
  have hT_pow_le : ∫ a, min (T a) 1 ^ ξr ∂P ≤ lintSum.toReal :=
    integral_min_one_rpow_le_lintegral_enorm_sq_toReal hT_asm hT_nonneg
      hxi_two hT_lint hfin
  have hT_root_le :
      (∫ a, min (T a) 1 ^ ξr ∂P) ^ (1 / ξr) ≤ sumRoot :=
    Real.rpow_le_rpow
      (MeasureTheory.integral_nonneg fun a =>
        Real.rpow_nonneg (le_min (hT_nonneg a) zero_le_one) _)
      hT_pow_le (one_div_nonneg.mpr hxi_pos.le)
  have hT_holder :
      ∫ a, min (T a) 1 * childAvg a ∂P ≤
        (∫ a, min (T a) 1 ^ ξr ∂P) ^ (1 / ξr) *
          (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) :=
    MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hHolderXiZeta
      (Filter.Eventually.of_forall fun a => le_min (hT_nonneg a) zero_le_one)
      (Filter.Eventually.of_forall hchild_nonneg) hminT_mem hChildMem
  have hT_piece :
      ∫ a, min (T a) 1 * childAvg a ∂P ≤ sumRoot * responseMoment :=
    hT_holder.trans
      (mul_le_mul hT_root_le hzetaRoot_le hzetaRoot_nonneg hsumRoot_nonneg)
  -- drift piece
  have hchild_int_le : ∫ a, childAvg a ∂P ≤ responseMoment := by
    have hOneMem :
        MeasureTheory.MemLp (fun _ : Homogenization.RegCoeffField d => (1 : ℝ))
          (ENNReal.ofReal ξr) P :=
      MeasureTheory.memLp_const 1
    have hH1 :=
      MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hHolderXiZeta.symm
        (Filter.Eventually.of_forall hchild_nonneg)
        (Filter.Eventually.of_forall fun _ => zero_le_one) hChildMem hOneMem
    have hone_pow :
        (∫ _a, (1 : ℝ) ^ ξr ∂P) ^ (1 / ξr) = 1 := by
      simp [Real.one_rpow]
    rw [hone_pow, mul_one] at hH1
    simpa [mul_one] using hH1.trans hzetaRoot_le
  have hminD_nonneg : 0 ≤ min D 1 := le_min hD_nonneg zero_le_one
  have hD_piece :
      ∫ a, min D 1 * childAvg a ∂P ≤ min D 1 * responseMoment := by
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hchild_int_le hminD_nonneg
  -- assembly
  have hstochRoot' : 2 * sumRoot ≤ stochRoot := by
    simpa [sumRoot, lintSum, S, Qm] using hstochRoot
  calc
    ∫ a, min (sourceMax a) 1 * childAvg a ∂P
        ≤ ∫ a,
            (min (S a) 1 * childAvg a + min (T a) 1 * childAvg a) +
              min D 1 * childAvg a ∂P :=
          MeasureTheory.integral_mono hILHS (hIST.add hID) hpt
    _ = (∫ a, min (S a) 1 * childAvg a ∂P +
          ∫ a, min (T a) 1 * childAvg a ∂P) +
          ∫ a, min D 1 * childAvg a ∂P := by
        rw [MeasureTheory.integral_add hIST hID,
          MeasureTheory.integral_add hIS hIT]
    _ ≤ (sumRoot * responseMoment + sumRoot * responseMoment) +
          min D 1 * responseMoment :=
        add_le_add (add_le_add hS_piece hT_piece) hD_piece
    _ = (2 * sumRoot + min D 1) * responseMoment := by ring
    _ ≤ (stochRoot + min D 1) * responseMoment :=
        mul_le_mul_of_nonneg_right
          (add_le_add hstochRoot' le_rfl) hresponse_nonneg

end

end Homogenization.HighContrast.EntryScale
