import Homogenization.HighContrast.EntryScale.ResponseFluctuation
import Homogenization.HighContrast.EntryScale.ResponseMoment
import Homogenization.HighContrast.EntryScale.TerminalLowerEdge
import Homogenization.HighContrast.EntryScale.BadEventResponse
import Homogenization.HighContrast.EntryScale.RawHighContrastWeakNorm.P2

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization
open scoped Matrix.Norms.Elementwise

namespace Homogenization.HighContrast.EntryScale

noncomputable section

/--
Source label `p.HC.CR`: unscaled child-average integrability for the terminal
positive-excess weight.  This is the form used by the raw low-tail library branch;
the existing scaled theorem is for the weak-norm defect-square route.
-/
theorem integrable_terminalPositiveExcess_childAverage_special_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hstat : Homogenization.Book.Ch04.RestrictionStationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Homogenization.Vec d) :
    let β := section53CoarseFluctuationBeta hP4
    let s' := hP4.sLower + β
    let t' := hP4.sUpper + β
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let childAvg := fun a : Homogenization.RegCoeffField d =>
      Homogenization.descendantsAverage Q (m - k)
        (fun R => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
    let lowerTerminal := fun a : Homogenization.RegCoeffField d =>
      max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0
    let upperTerminal := fun a : Homogenization.RegCoeffField d =>
      max
        (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0
    MeasureTheory.Integrable
      (fun a : Homogenization.RegCoeffField d =>
        (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) * childAvg a) P := by
  classical
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let childAvg : Homogenization.RegCoeffField d → ℝ := fun a =>
    Homogenization.descendantsAverage Q (m - k)
      (fun R => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
  let response : Homogenization.RegCoeffField d → ℝ := fun a =>
    (5 * β⁻¹) ^ 2 * childAvg a
  let lowerTerminal : Homogenization.RegCoeffField d → ℝ := fun a =>
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
      0
  let upperTerminal : Homogenization.RegCoeffField d → ℝ := fun a =>
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
        hP.barSigmaAtScale hStruct (m : ℤ))
      0
  let coeff : ℝ := (5 * β⁻¹) ^ 2
  have hscaled :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) * response a) P := by
    simpa [β, s', t', Q, p_e, q_e, σ, childAvg, response, lowerTerminal,
      upperTerminal] using
      integrable_terminalPositiveExcess_childResponseAverage_special_of_P4
        hP hstat hStruct hP4 hkm e
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hcoeff_ne : coeff ≠ 0 := by
    dsimp [coeff]
    exact pow_ne_zero 2
      (mul_ne_zero (by norm_num) (inv_ne_zero (ne_of_gt hβ_pos)))
  have hscaled' :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          coeff⁻¹ *
            ((σ * lowerTerminal a + σ⁻¹ * upperTerminal a) * response a)) P :=
    hscaled.const_mul coeff⁻¹
  refine hscaled'.congr ?_
  filter_upwards with a
  change coeff⁻¹ *
        ((σ * lowerTerminal a + σ⁻¹ * upperTerminal a) *
          (coeff * childAvg a)) =
      (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) * childAvg a
  calc
    coeff⁻¹ *
        ((σ * lowerTerminal a + σ⁻¹ * upperTerminal a) *
          (coeff * childAvg a)) =
        (coeff⁻¹ * coeff) *
          ((σ * lowerTerminal a + σ⁻¹ * upperTerminal a) * childAvg a) := by
          ring
    _ = (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) * childAvg a := by
          rw [inv_mul_cancel₀ hcoeff_ne, one_mul]

/--
Source label `p.HC.CR`: integral normal form for the scale-zero
positive-excess child-average branch.  The library presents this branch as
`sigma * int lower + sigma^{-1} * int upper`; terminal Section 5.2 estimates
use the integral of the combined weighted positive-excess observable.
-/
theorem integral_zeroBaselinePositiveExcess_childAverage_split_special_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hstat : Homogenization.Book.Ch04.RestrictionStationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Homogenization.Vec d) :
    let β := section53CoarseFluctuationBeta hP4
    let s' := hP4.sLower + β
    let t' := hP4.sUpper + β
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let childAvg := fun a : Homogenization.RegCoeffField d =>
      Homogenization.descendantsAverage Q (m - k)
        (fun R => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
    let lowerZero := fun a : Homogenization.RegCoeffField d =>
      max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct 0)⁻¹)
        0
    let upperZero := fun a : Homogenization.RegCoeffField d =>
      max
        (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
          hP.barSigmaAtScale hStruct 0)
        0
    ∫ a, (σ * lowerZero a + σ⁻¹ * upperZero a) * childAvg a ∂P =
      σ * (∫ a, lowerZero a * childAvg a ∂P) +
        σ⁻¹ * (∫ a, upperZero a * childAvg a ∂P) := by
  classical
  dsimp only
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let childAvg : Homogenization.RegCoeffField d → ℝ := fun a =>
    Homogenization.descendantsAverage Q (m - k)
      (fun R => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
  let lowerZero : Homogenization.RegCoeffField d → ℝ := fun a =>
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct 0)⁻¹)
      0
  let upperZero : Homogenization.RegCoeffField d → ℝ := fun a =>
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
        hP.barSigmaAtScale hStruct 0)
      0
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hs'_pos : 0 < s' := by
    dsimp [s', β]
    linarith [hP4.sLower_pos, hβ_pos]
  have ht'_pos : 0 < t' := by
    dsimp [t', β]
    linarith [hP4.sUpper_pos, hβ_pos]
  have hs'_gt : hP4.sLower < s' := by
    dsimp [s', β]
    linarith
  have ht'_gt : hP4.sUpper < t' := by
    dsimp [t', β]
    linarith
  have hs'_lt_one : s' < 1 := by
    have hsum := sUpper_add_sLower_add_two_beta_le_one hP4
    dsimp [s', β]
    nlinarith [hP4.sUpper_pos, hβ_pos]
  have ht'_lt_one : t' < 1 := by
    have hsum := sUpper_add_sLower_add_two_beta_le_one hP4
    dsimp [t', β]
    nlinarith [hP4.sLower_pos, hβ_pos]
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hkm.le
  have hChildMem :
      MeasureTheory.MemLp childAvg
        (ENNReal.ofReal (section53CoarseFluctuationZeta hP4)) P := by
    simpa [childAvg, Q, p_e, q_e] using
      memLp_zeta_descendantsAverage_restrictionResponseJObservableCubeSet_originCube_from_P4_of_stationary
        hP hstat hStruct hP4 hk_nonneg hkm_int p_e q_e
  have hLowerAE : AEMeasurable lowerZero P := by
    simpa [lowerZero, Q] using
      ((hP.aemeasurable_lambdaSqCoeffField_finite_one_inv Q hs'_pos).sub
        aemeasurable_const).max aemeasurable_const
  have hUpperAE : AEMeasurable upperZero P := by
    simpa [upperZero, Q] using
      ((hP.aemeasurable_LambdaSqCoeffField_finite_one Q ht'_pos).sub
        aemeasurable_const).max aemeasurable_const
  have hLowerPowInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d => lowerZero a ^ hP4.xi) P := by
    simpa [lowerZero, Q, s', β] using
      Homogenization.Book.Ch05.Section52.lowerPositiveExcessPowIntegrableAtScale_from_P4_twoExponent
        hP hStruct hP4 hs'_gt hs'_lt_one m
  have hUpperPowInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d => upperZero a ^ hP4.xi) P := by
    simpa [upperZero, Q, t', β] using
      Homogenization.Book.Ch05.Section52.upperPositiveExcessPowIntegrableAtScale_from_P4_twoExponent
        hP hStruct hP4 ht'_gt ht'_lt_one m
  have hLower_nonneg : ∀ᵐ a ∂P, 0 ≤ lowerZero a := by
    filter_upwards with a
    exact le_max_right _ _
  have hUpper_nonneg : ∀ᵐ a ∂P, 0 ≤ upperZero a := by
    filter_upwards with a
    exact le_max_right _ _
  have hLowerMem :
      MeasureTheory.MemLp lowerZero (ENNReal.ofReal (hP4.xi : ℝ)) P :=
    memLp_of_integrable_nonneg_nat_pow hP4.xi_pos hLowerAE
      hLower_nonneg hLowerPowInt
  have hUpperMem :
      MeasureTheory.MemLp upperZero (ENNReal.ofReal (hP4.xi : ℝ)) P :=
    memLp_of_integrable_nonneg_nat_pow hP4.xi_pos hUpperAE
      hUpper_nonneg hUpperPowInt
  have hHolderReal :
      (section53CoarseFluctuationZeta hP4).HolderConjugate (hP4.xi : ℝ) := by
    simpa using
      (holderConjugate_xi_section53CoarseFluctuationZeta hP4).symm
  letI : ENNReal.HolderTriple
      (ENNReal.ofReal (section53CoarseFluctuationZeta hP4))
      (ENNReal.ofReal (hP4.xi : ℝ)) 1 := by
    simpa using Real.HolderTriple.ennrealOfReal hHolderReal
  have hLowerChildInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d => lowerZero a * childAvg a) P := by
    simpa [mul_comm] using hChildMem.integrable_mul hLowerMem
  have hUpperChildInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d => upperZero a * childAvg a) P := by
    simpa [mul_comm] using hChildMem.integrable_mul hUpperMem
  calc
    ∫ a, (σ * lowerZero a + σ⁻¹ * upperZero a) * childAvg a ∂P
        =
      ∫ a, σ * (lowerZero a * childAvg a) +
        σ⁻¹ * (upperZero a * childAvg a) ∂P := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with a
        ring
    _ =
      ∫ a, σ * (lowerZero a * childAvg a) ∂P +
        ∫ a, σ⁻¹ * (upperZero a * childAvg a) ∂P := by
        rw [MeasureTheory.integral_add
          (hLowerChildInt.const_mul σ) (hUpperChildInt.const_mul σ⁻¹)]
    _ =
      σ * (∫ a, lowerZero a * childAvg a ∂P) +
        σ⁻¹ * (∫ a, upperZero a * childAvg a ∂P) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/--
Source label `p.HC.CR`: monotone comparison from the scale-zero positive
excess weight to the terminal positive-excess weight, after multiplying by an
arbitrary nonnegative response factor.  This is the raw low-tail bridge before
the Section 5.2 terminal split is applied.
-/
theorem integral_zeroBaselinePositiveExcessWeight_mul_le_terminalPositiveExcessWeight_mul
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {m : ℕ} (rLower rUpper : ℝ)
    (J : Homogenization.RegCoeffField d → ℝ)
    (hJ_nonneg : 0 ≤ᵐ[P] J)
    (hTerminalInt :
      let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
      let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
      let lowerTerminal := fun a : Homogenization.RegCoeffField d =>
        max
          ((Homogenization.Book.Ch04.lambdaSqCoeffField Q rLower (.finite 1) a)⁻¹ -
            (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
          0
      let upperTerminal := fun a : Homogenization.RegCoeffField d =>
        max
          (Homogenization.Book.Ch04.LambdaSqCoeffField Q rUpper (.finite 1) a -
            hP.barSigmaAtScale hStruct (m : ℤ))
          0
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) * J a) P) :
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let lowerZero := fun a : Homogenization.RegCoeffField d =>
      max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField Q rLower (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct 0)⁻¹)
        0
    let upperZero := fun a : Homogenization.RegCoeffField d =>
      max
        (Homogenization.Book.Ch04.LambdaSqCoeffField Q rUpper (.finite 1) a -
          hP.barSigmaAtScale hStruct 0)
        0
    let lowerTerminal := fun a : Homogenization.RegCoeffField d =>
      max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField Q rLower (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0
    let upperTerminal := fun a : Homogenization.RegCoeffField d =>
      max
        (Homogenization.Book.Ch04.LambdaSqCoeffField Q rUpper (.finite 1) a -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0
    ∫ a, (σ * lowerZero a + σ⁻¹ * upperZero a) * J a ∂P
      ≤
        ∫ a, (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) * J a ∂P := by
  classical
  dsimp only at hTerminalInt ⊢
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let lowerZero : Homogenization.RegCoeffField d → ℝ := fun a =>
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q rLower (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct 0)⁻¹)
      0
  let upperZero : Homogenization.RegCoeffField d → ℝ := fun a =>
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q rUpper (.finite 1) a -
        hP.barSigmaAtScale hStruct 0)
      0
  let lowerTerminal : Homogenization.RegCoeffField d → ℝ := fun a =>
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q rLower (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
      0
  let upperTerminal : Homogenization.RegCoeffField d → ℝ := fun a =>
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q rUpper (.finite 1) a -
        hP.barSigmaAtScale hStruct (m : ℤ))
      0
  let zeroEdge : Homogenization.RegCoeffField d → ℝ := fun a =>
    (σ * lowerZero a + σ⁻¹ * upperZero a) * J a
  let terminalEdge : Homogenization.RegCoeffField d → ℝ := fun a =>
    (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) * J a
  have hTerminalInt' : MeasureTheory.Integrable terminalEdge P := by
    simpa [terminalEdge, Q, σ, lowerTerminal, upperTerminal] using hTerminalInt
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, Homogenization.Book.Ch05.sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hzero_nonneg : 0 ≤ᵐ[P] zeroEdge := by
    filter_upwards [hJ_nonneg] with a hJ_a
    dsimp [zeroEdge]
    exact mul_nonneg
      (add_nonneg
        (mul_nonneg hσ_nonneg (le_max_right _ _))
        (mul_nonneg hσ_inv_nonneg (le_max_right _ _)))
      hJ_a
  have hpoint : zeroEdge ≤ᵐ[P] terminalEdge := by
    filter_upwards [hJ_nonneg] with a hJ_a
    have hweight :
        σ * lowerZero a + σ⁻¹ * upperZero a ≤
          σ * lowerTerminal a + σ⁻¹ * upperTerminal a := by
      simpa [Q, σ, lowerZero, lowerTerminal, upperZero, upperTerminal] using
        localPositiveExcessWeight_le_terminalBaseline_of_P4
          hP hStruct hP4 (Nat.zero_le m) rLower rUpper a
    exact mul_le_mul_of_nonneg_right hweight hJ_a
  have hmono :
      ∫ a, zeroEdge a ∂P ≤ ∫ a, terminalEdge a ∂P :=
    MeasureTheory.integral_mono_of_nonneg hzero_nonneg hTerminalInt' hpoint
  simpa [zeroEdge, terminalEdge, Q, σ, lowerZero, upperZero, lowerTerminal,
    upperTerminal] using hmono

/--
Source labels `p.HC.CR` and `e.M.def`: pointwise scalar lower-edge split of
the terminal finite-one positive-excess weight into the library's Section 5.2
small-tail terms plus large-scale descendant matrix positive-excess terms.
This is the scalar multiscale extraction step before the downstream
source-max good/bad split.
-/
theorem terminalPositiveExcessWeight_le_section52SmallTail_add_largeScalePositiveExcess
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (a : Homogenization.RegCoeffField d) :
    let β := section53CoarseFluctuationBeta hP4
    let s' := hP4.sLower + β
    let t' := hP4.sUpper + β
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let lowerTerminal : ℝ :=
      max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0
    let upperTerminal : ℝ :=
      max
        (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0
    let lowerSmall : ℝ :=
      Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
          (d := d) m s' a ^ 2 /
        Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
    let upperSmall : ℝ :=
      Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
          (d := d) m t' a ^ 2 /
        Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
    let lowerLarge : ℝ :=
      ((Homogenization.Book.Ch05.Section52.section52LargeScaleSet m).attach.sum fun n =>
        Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
          (let parents := Homogenization.descendantsAtScale Q n.1
           let hparents : parents.Nonempty :=
            Homogenization.descendantsAtScale_nonempty Q
              (by simpa [Q, Homogenization.originCube] using
                Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
           parents.sup' hparents
            (fun R =>
              max
                (Homogenization.Book.Ch02.matrixNorm
                    (Homogenization.coarseBlockMatrix
                      (Homogenization.cubeSet R) a).lowerRight -
                  (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
                0)))
    let upperLarge : ℝ :=
      ((Homogenization.Book.Ch05.Section52.section52LargeScaleSet m).attach.sum fun n =>
        Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
          (let parents := Homogenization.descendantsAtScale Q n.1
           let hparents : parents.Nonempty :=
            Homogenization.descendantsAtScale_nonempty Q
              (by simpa [Q, Homogenization.originCube] using
                Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
           parents.sup' hparents
            (fun R =>
              max
                (Homogenization.Book.Ch02.matrixNorm
                    (Homogenization.coarseBlockMatrix
                      (Homogenization.cubeSet R) a).upperLeft -
                  hP.barSigmaAtScale hStruct (m : ℤ))
                0)))
    σ * lowerTerminal + σ⁻¹ * upperTerminal ≤
      σ * (lowerSmall + lowerLarge) + σ⁻¹ * (upperSmall + upperLarge) := by
  classical
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let lowerTerminal : ℝ :=
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
      0
  let upperTerminal : ℝ :=
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
        hP.barSigmaAtScale hStruct (m : ℤ))
      0
  let lowerSmall : ℝ :=
    Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
        (d := d) m s' a ^ 2 /
      Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
  let upperSmall : ℝ :=
    Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
        (d := d) m t' a ^ 2 /
      Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
  let lowerLarge : ℝ :=
    ((Homogenization.Book.Ch05.Section52.section52LargeScaleSet m).attach.sum fun n =>
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
        (let parents := Homogenization.descendantsAtScale Q n.1
         let hparents : parents.Nonempty :=
          Homogenization.descendantsAtScale_nonempty Q
            (by simpa [Q, Homogenization.originCube] using
              Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
         parents.sup' hparents
          (fun R =>
            max
                (Homogenization.Book.Ch02.matrixNorm
                    (Homogenization.coarseBlockMatrix
                      (Homogenization.cubeSet R) a).lowerRight -
                  (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
                0)))
  let upperLarge : ℝ :=
    ((Homogenization.Book.Ch05.Section52.section52LargeScaleSet m).attach.sum fun n =>
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
        (let parents := Homogenization.descendantsAtScale Q n.1
         let hparents : parents.Nonempty :=
          Homogenization.descendantsAtScale_nonempty Q
            (by simpa [Q, Homogenization.originCube] using
              Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
         parents.sup' hparents
          (fun R =>
            max
              (Homogenization.Book.Ch02.matrixNorm
                  (Homogenization.coarseBlockMatrix
                    (Homogenization.cubeSet R) a).upperLeft -
                hP.barSigmaAtScale hStruct (m : ℤ))
              0)))
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hs'_pos : 0 < s' := by
    dsimp [s', β]
    linarith [hP4.sLower_pos, hβ_pos]
  have ht'_pos : 0 < t' := by
    dsimp [t', β]
    linarith [hP4.sUpper_pos, hβ_pos]
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, Homogenization.Book.Ch05.sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hbar_pos :
      0 < hP.barSigmaAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 m
  have hbar_nonneg : 0 ≤ hP.barSigmaAtScale hStruct (m : ℤ) :=
    hbar_pos.le
  have hstar_inv_pos :
      0 < (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_inv_pos_of_P4
      hP hStruct hP4 m
  have hstar_inv_nonneg :
      0 ≤ (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ :=
    hstar_inv_pos.le
  have hbar_matrix :
      Homogenization.Book.Ch02.matrixNorm
          (hP.barSigmaAtScale hStruct (m : ℤ) • (1 : Homogenization.Mat d)) =
        hP.barSigmaAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section52.matrixNorm_smul_one_eq_of_nonneg
      hbar_nonneg
  have hstar_matrix :
      Homogenization.Book.Ch02.matrixNorm
          ((hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ •
            (1 : Homogenization.Mat d)) =
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ :=
    Homogenization.Book.Ch05.Section52.matrixNorm_smul_one_eq_of_nonneg
      hstar_inv_nonneg
  have hlower :
      lowerTerminal ≤ lowerSmall + lowerLarge := by
    simpa [lowerTerminal, lowerSmall, lowerLarge, Q, s', hstar_matrix] using
      Homogenization.Book.Ch05.Section52.lowerPositiveExcess_pointwise_le_smallTail_add_largeScalePositiveExcess
        (d := d) m (s := s')
        (base := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        hs'_pos hstar_inv_nonneg a
  have hupper :
      upperTerminal ≤ upperSmall + upperLarge := by
    simpa [upperTerminal, upperSmall, upperLarge, Q, t', hbar_matrix] using
      Homogenization.Book.Ch05.Section52.upperPositiveExcess_pointwise_le_smallTail_add_largeScalePositiveExcess
        (d := d) m (s := t')
        (base := hP.barSigmaAtScale hStruct (m : ℤ))
        ht'_pos hbar_nonneg a
  exact add_le_add
    (mul_le_mul_of_nonneg_left hlower hσ_nonneg)
    (mul_le_mul_of_nonneg_left hupper hσ_inv_nonneg)

/--
Source labels `p.HC.CR`, `e.weaknorms.moreproto`, and `e.M.def`:
sqrt-theta first-power source-max variant of the terminal finite-one
positive-excess split which keeps the exact Section 5.2 `edgeWeightLoss`
coefficient.  This is the summed-weight sharp-normalization hybrid: the source
factor is split as `min(sourceMax, 1) + badEventTruncation(sourceMax)` at
first power, priced by `2 * sqrt(theta_m)` instead of the crude
`2 * (1 + F_m)`.
-/
theorem terminalPositiveExcessWeight_mul_le_section52SmallTail_mul_add_lowSum_add_edgeWeightLoss_mul_sqrtThetaAtScale_sourceMax_min_one_add_badEventTruncation_mul_response
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {N m : ℕ}
    (a : Ω → Homogenization.RegCoeffField d) (ω : Ω)
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField (a ω))
    {J : ℝ} (hJ_nonneg : 0 ≤ J) :
    let β := section53CoarseFluctuationBeta hP4
    let s' := hP4.sLower + β
    let t' := hP4.sUpper + β
    let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let sourceMax := terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a
    let lowerTerminal : ℝ :=
      max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) (a ω))⁻¹ -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0
    let upperTerminal : ℝ :=
      max
        (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) (a ω) -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0
    let lowerSmall : ℝ :=
      Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
          (d := d) m s' (a ω) ^ 2 /
        Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
    let upperSmall : ℝ :=
      Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
          (d := d) m t' (a ω) ^ 2 /
        Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
    let B : ℝ :=
      2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
        (min (sourceMax ω) 1 * J +
          badEventTruncation sourceMax ω * J)
    let lowerSlot : {n : ℤ // n ∈ S} → ℝ := fun n =>
      let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa [Q, Homogenization.originCube] using
            Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
      let lowerExcess : Homogenization.TriadicCube d → ℝ := fun R =>
        max
          (Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix
                (Homogenization.cubeSet R) (a ω)).lowerRight -
            (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
          0
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
        (σ * parents.sup' hparents lowerExcess) * J
    let upperSlot : {n : ℤ // n ∈ S} → ℝ := fun n =>
      let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa [Q, Homogenization.originCube] using
            Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
      let upperExcess : Homogenization.TriadicCube d → ℝ := fun R =>
        max
          (Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix
                (Homogenization.cubeSet R) (a ω)).upperLeft -
            hP.barSigmaAtScale hStruct (m : ℤ))
          0
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
        (σ⁻¹ * parents.sup' hparents upperExcess) * J
    let lowSum : ℝ :=
      S.attach.sum fun n =>
        if N ≤ Int.toNat n.1 then 0 else lowerSlot n + upperSlot n
    let weightLossSup : {n : ℤ // n ∈ S} → ℝ := fun n =>
      let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa [Q, Homogenization.originCube] using
            Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
      parents.sup' hparents
        (fun R =>
          ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n.1) R)⁻¹).toReal)
    let edgeWeightLoss : ℝ :=
      S.attach.sum fun n =>
        if N ≤ Int.toNat n.1 then
          (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 +
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1) *
            weightLossSup n
        else 0
    (σ * lowerTerminal + σ⁻¹ * upperTerminal) * J ≤
      (σ * lowerSmall + σ⁻¹ * upperSmall) * J +
        lowSum + edgeWeightLoss * B := by
  classical
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let source : Ω → ℝ := terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a
  let lowerTerminal : ℝ :=
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) (a ω))⁻¹ -
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
      0
  let upperTerminal : ℝ :=
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) (a ω) -
        hP.barSigmaAtScale hStruct (m : ℤ))
      0
  let lowerSmall : ℝ :=
    Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
        (d := d) m s' (a ω) ^ 2 /
      Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
  let upperSmall : ℝ :=
    Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
        (d := d) m t' (a ω) ^ 2 /
      Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
  let lowerLarge : ℝ :=
    S.attach.sum fun n =>
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
        (let parents := Homogenization.descendantsAtScale Q n.1
         let hparents : parents.Nonempty :=
          Homogenization.descendantsAtScale_nonempty Q
            (by simpa [Q, Homogenization.originCube] using
              Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
         parents.sup' hparents
          (fun R =>
            max
              (Homogenization.Book.Ch02.matrixNorm
                  (Homogenization.coarseBlockMatrix
                    (Homogenization.cubeSet R) (a ω)).lowerRight -
                (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
              0))
  let upperLarge : ℝ :=
    S.attach.sum fun n =>
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
        (let parents := Homogenization.descendantsAtScale Q n.1
         let hparents : parents.Nonempty :=
          Homogenization.descendantsAtScale_nonempty Q
            (by simpa [Q, Homogenization.originCube] using
              Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
         parents.sup' hparents
          (fun R =>
            max
              (Homogenization.Book.Ch02.matrixNorm
                  (Homogenization.coarseBlockMatrix
                    (Homogenization.cubeSet R) (a ω)).upperLeft -
                hP.barSigmaAtScale hStruct (m : ℤ))
              0))
  let B : ℝ :=
    2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
      (min (source ω) 1 * J + badEventTruncation source ω * J)
  let lowerSlot : {n : ℤ // n ∈ S} → ℝ := fun n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa [Q, Homogenization.originCube] using
          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
    let lowerExcess : Homogenization.TriadicCube d → ℝ := fun R =>
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix
              (Homogenization.cubeSet R) (a ω)).lowerRight -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
      (σ * parents.sup' hparents lowerExcess) * J
  let upperSlot : {n : ℤ // n ∈ S} → ℝ := fun n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa [Q, Homogenization.originCube] using
          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
    let upperExcess : Homogenization.TriadicCube d → ℝ := fun R =>
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix
              (Homogenization.cubeSet R) (a ω)).upperLeft -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
      (σ⁻¹ * parents.sup' hparents upperExcess) * J
  let largeSum : ℝ := S.attach.sum fun n => lowerSlot n + upperSlot n
  let lowSum : ℝ :=
    S.attach.sum fun n =>
      if N ≤ Int.toNat n.1 then 0 else lowerSlot n + upperSlot n
  let weightLossSup : {n : ℤ // n ∈ S} → ℝ := fun n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa [Q, Homogenization.originCube] using
          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
    parents.sup' hparents
      (fun R =>
        ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n.1) R)⁻¹).toReal)
  let edgeWeightLoss : ℝ :=
    S.attach.sum fun n =>
      if N ≤ Int.toNat n.1 then
        (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 +
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1) *
          weightLossSup n
      else 0
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hs'_pos : 0 < s' := by
    dsimp [s', β]
    linarith [hP4.sLower_pos, hβ_pos]
  have ht'_pos : 0 < t' := by
    dsimp [t', β]
    linarith [hP4.sUpper_pos, hβ_pos]
  have hsplit :
      σ * lowerTerminal + σ⁻¹ * upperTerminal ≤
        σ * (lowerSmall + lowerLarge) + σ⁻¹ * (upperSmall + upperLarge) := by
    simpa [β, s', t', S, Q, σ, lowerTerminal, upperTerminal,
      lowerSmall, upperSmall, lowerLarge, upperLarge] using
      terminalPositiveExcessWeight_le_section52SmallTail_add_largeScalePositiveExcess
        hP hStruct hP4 m (a ω)
  have hlarge :
      largeSum ≤ lowSum + edgeWeightLoss * B := by
    simpa [S, Q, σ, source, B, lowerSlot, upperSlot, largeSum, lowSum,
      weightLossSup, edgeWeightLoss, β, s', t'] using
      section52LargeScale_terminalPositiveExcess_allSum_mul_le_lowSum_add_edgeWeightLoss_mul_sqrt_thetaAtScale_sourceMax_min_one_add_badEventTruncation_mul_response
        (hP := hP) (hStruct := hStruct) (hP4 := hP4) (hc := hc)
        (N := N) (m := m)
        (sLower := s') (sUpper := t') hs'_pos ht'_pos
        a ω ha hJ_nonneg
  have hlowerLarge_mul :
      σ * lowerLarge * J = S.attach.sum fun n => lowerSlot n := by
    dsimp [lowerLarge, lowerSlot]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro n _hn
    ring
  have hupperLarge_mul :
      σ⁻¹ * upperLarge * J = S.attach.sum fun n => upperSlot n := by
    dsimp [upperLarge, upperSlot]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro n _hn
    ring
  have hlarge_eq :
      σ * lowerLarge * J + σ⁻¹ * upperLarge * J = largeSum := by
    rw [hlowerLarge_mul, hupperLarge_mul]
    dsimp [largeSum]
    rw [← Finset.sum_add_distrib]
  have hdecomp :
      (σ * (lowerSmall + lowerLarge) +
          σ⁻¹ * (upperSmall + upperLarge)) * J =
        (σ * lowerSmall + σ⁻¹ * upperSmall) * J + largeSum := by
    calc
      (σ * (lowerSmall + lowerLarge) +
          σ⁻¹ * (upperSmall + upperLarge)) * J =
          (σ * lowerSmall + σ⁻¹ * upperSmall) * J +
            (σ * lowerLarge * J + σ⁻¹ * upperLarge * J) := by
            ring
      _ = (σ * lowerSmall + σ⁻¹ * upperSmall) * J + largeSum := by
            rw [hlarge_eq]
  calc
    (σ * lowerTerminal + σ⁻¹ * upperTerminal) * J
        ≤ (σ * (lowerSmall + lowerLarge) +
            σ⁻¹ * (upperSmall + upperLarge)) * J :=
          mul_le_mul_of_nonneg_right hsplit hJ_nonneg
    _ = (σ * lowerSmall + σ⁻¹ * upperSmall) * J + largeSum := hdecomp
    _ ≤ (σ * lowerSmall + σ⁻¹ * upperSmall) * J +
          (lowSum + edgeWeightLoss * B) :=
          add_le_add_right hlarge ((σ * lowerSmall + σ⁻¹ * upperSmall) * J)
    _ = (σ * lowerSmall + σ⁻¹ * upperSmall) * J +
          lowSum + edgeWeightLoss * B := by
          ring

/--
Source labels `p.HC.CR`, `e.weaknorms.moreproto`, and `e.M.def`:
pointwise `defectSum ^ 2` specialization of the sqrt-theta first-power
source-max Section 5.2 edge-loss split, with every response slot converted to
the child response average.
-/
theorem terminalPositiveExcessWeight_mul_defectSum_sq_le_section52SmallTail_mul_childResponseAverage_add_lowSum_childResponseAverage_add_edgeWeightLoss_mul_sqrtThetaAtScale_sourceMax_min_one_add_badEventTruncation_mul_childResponseAverage
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {k m : ℕ}
    (hkm : k < m)
    (e : Homogenization.Vec d)
    (a : Ω → Homogenization.RegCoeffField d) (ω : Ω)
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField (a ω)) :
    let β := section53CoarseFluctuationBeta hP4
    let s' := hP4.sLower + β
    let t' := hP4.sUpper + β
    let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let sourceMax := terminalSpectralPositivePartSourceMax hP hStruct hc k m Q a
    let defectSum : ℝ :=
      ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
        Real.rpow (3 : ℝ)
            (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          Real.sqrt
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
              (m : ℤ) n p_e q_e (a ω))
    let childAvg : ℝ :=
      Homogenization.descendantsAverage Q (m - k)
        (fun R => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e (a ω))
    let response : ℝ := (5 * β⁻¹) ^ 2 * childAvg
    let lowerTerminal : ℝ :=
      max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) (a ω))⁻¹ -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0
    let upperTerminal : ℝ :=
      max
        (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) (a ω) -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0
    let lowerSmall : ℝ :=
      Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
          (d := d) m s' (a ω) ^ 2 /
        Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
    let upperSmall : ℝ :=
      Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
          (d := d) m t' (a ω) ^ 2 /
        Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
    let B : ℝ :=
      2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
        (min (sourceMax ω) 1 * response +
          badEventTruncation sourceMax ω * response)
    let lowerSlot : {n : ℤ // n ∈ S} → ℝ := fun n =>
      let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa [Q, Homogenization.originCube] using
            Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
      let lowerExcess : Homogenization.TriadicCube d → ℝ := fun R =>
        max
          (Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix
                (Homogenization.cubeSet R) (a ω)).lowerRight -
            (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
          0
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
        (σ * parents.sup' hparents lowerExcess) * response
    let upperSlot : {n : ℤ // n ∈ S} → ℝ := fun n =>
      let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa [Q, Homogenization.originCube] using
            Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
      let upperExcess : Homogenization.TriadicCube d → ℝ := fun R =>
        max
          (Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix
                (Homogenization.cubeSet R) (a ω)).upperLeft -
            hP.barSigmaAtScale hStruct (m : ℤ))
          0
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
        (σ⁻¹ * parents.sup' hparents upperExcess) * response
    let lowSum : ℝ :=
      S.attach.sum fun n =>
        if k ≤ Int.toNat n.1 then 0 else lowerSlot n + upperSlot n
    let weightLossSup : {n : ℤ // n ∈ S} → ℝ := fun n =>
      let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa [Q, Homogenization.originCube] using
            Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
      parents.sup' hparents
        (fun R =>
          ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n.1) R)⁻¹).toReal)
    let edgeWeightLoss : ℝ :=
      S.attach.sum fun n =>
        if k ≤ Int.toNat n.1 then
          (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 +
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1) *
            weightLossSup n
        else 0
    (σ * lowerTerminal + σ⁻¹ * upperTerminal) * defectSum ^ 2 ≤
      (σ * lowerSmall + σ⁻¹ * upperSmall) * response +
        lowSum + edgeWeightLoss * B := by
  classical
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let defectSum : ℝ :=
    ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
      Real.rpow (3 : ℝ)
          (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
        Real.sqrt
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
            (m : ℤ) n p_e q_e (a ω))
  let childAvg : ℝ :=
    Homogenization.descendantsAverage Q (m - k)
      (fun R => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e (a ω))
  let response : ℝ := (5 * β⁻¹) ^ 2 * childAvg
  let lowerTerminal : ℝ :=
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) (a ω))⁻¹ -
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
      0
  let upperTerminal : ℝ :=
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) (a ω) -
        hP.barSigmaAtScale hStruct (m : ℤ))
      0
  have hdef_le : defectSum ^ 2 ≤ response := by
    simpa [β, p_e, q_e, defectSum, childAvg, response, Q] using
      defectSum_sq_special_le_childResponseAverage
        hP hStruct hP4 hkm e ha
  have hchild_nonneg : 0 ≤ childAvg := by
    dsimp [childAvg]
    exact Homogenization.descendantsAverage_nonneg Q (m - k)
      (fun R => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e (a ω))
      (fun R _hR =>
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet_nonneg R p_e q_e (a ω))
  have hresponse_nonneg : 0 ≤ response := by
    dsimp [response]
    exact mul_nonneg (sq_nonneg _) hchild_nonneg
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, Homogenization.Book.Ch05.sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hweight_nonneg :
      0 ≤ σ * lowerTerminal + σ⁻¹ * upperTerminal := by
    exact add_nonneg
      (mul_nonneg hσ_nonneg (le_max_right _ _))
      (mul_nonneg hσ_inv_nonneg (le_max_right _ _))
  have hleft_le :
      (σ * lowerTerminal + σ⁻¹ * upperTerminal) * defectSum ^ 2 ≤
        (σ * lowerTerminal + σ⁻¹ * upperTerminal) * response :=
    mul_le_mul_of_nonneg_left hdef_le hweight_nonneg
  have hsplit :=
    terminalPositiveExcessWeight_mul_le_section52SmallTail_mul_add_lowSum_add_edgeWeightLoss_mul_sqrtThetaAtScale_sourceMax_min_one_add_badEventTruncation_mul_response
      (hP := hP) (hStruct := hStruct) (hP4 := hP4) (hc := hc)
      (N := k) (m := m) a ω ha
      (J := response) hresponse_nonneg
  exact hleft_le.trans
    (by
      simpa [β, s', t', S, Q, p_e, q_e, σ, childAvg, response,
        lowerTerminal, upperTerminal] using hsplit)

end

end Homogenization.HighContrast.EntryScale
