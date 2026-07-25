import Homogenization.HighContrast.EntryScale.ResponseFluctuation
import Homogenization.HighContrast.EntryScale.ResponseMoment
import Homogenization.HighContrast.EntryScale.TerminalLowerEdge
import Homogenization.HighContrast.EntryScale.BadEventResponse
import Homogenization.HighContrast.EntryScale.RawHighContrastWeakNorm.P1

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization
open scoped Matrix.Norms.Elementwise

namespace Homogenization.HighContrast.EntryScale

noncomputable section

/--
Source labels `p.HC.CR`, `e.J.moment.bound`, and `l.weaknorms.moreproto`:
the LIH scale-zero positive-excess lower-edge integral is bounded by the
response-moment term before any final Section 5.3 coarse-fluctuation
compression.  The only loss introduced here is the explicit
`(5 * β⁻¹)^2` conversion from the weighted response-defect square to the
child-response average.
-/
theorem integral_zeroBaselinePositiveExcess_defectSum_sq_special_le_responseMoment
    {d : ℕ} [NeZero d]
    (params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Homogenization.Book.Ch04.CoeffLaw d}
      (hP : Homogenization.Book.Ch04.LawCarrier P)
      (_hstat : Homogenization.Book.Ch04.StationaryLaw P)
      (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
      (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      ∀ {k m : ℕ}, k < m → ∀ e : Homogenization.Vec d,
        let β := section53CoarseFluctuationBeta hP4
        let s' := hP4.sLower + β
        let t' := hP4.sUpper + β
        let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
        let p_e :=
          Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
        let q_e :=
          Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
        let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
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
        let defectSum := fun a : Homogenization.RegCoeffField d =>
          ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
            Real.rpow (3 : ℝ)
                (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
              Real.sqrt
                (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
                  (m : ℤ) n p_e q_e a)
        MeasureTheory.Integrable
          (fun a : Homogenization.RegCoeffField d =>
            (σ * lowerZero a + σ⁻¹ * upperZero a) * defectSum a ^ 2) P ∧
          ∫ a, (σ * lowerZero a + σ⁻¹ * upperZero a) *
              defectSum a ^ 2 ∂P
            ≤
              (5 * β⁻¹) ^ 2 * C * (hP4.xi : ℝ) *
                Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
                coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                  coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
  classical
  rcases
      ellipticityPositiveExcess_childResponseAverage_expectation_le_uniform
        params with ⟨C, hC_nonneg, hC_all⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro P hP hstat hStruct hP4 hparams k m hkm e
  subst params
  dsimp only
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let S : Finset ℤ := Finset.Icc (((k : ℤ) + 1)) (m : ℤ)
  let w : ℤ → ℝ :=
    fun n => Real.rpow (3 : ℝ)
      (-β * (Int.toNat ((m : ℤ) - n) : ℝ))
  let defectSum : Homogenization.RegCoeffField d → ℝ :=
    fun a =>
      ∑ n ∈ S, w n *
        Real.sqrt
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
            (m : ℤ) n p_e q_e a)
  let childAvg : Homogenization.RegCoeffField d → ℝ :=
    fun a => Homogenization.descendantsAverage Q j
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
  let lowerZero : Homogenization.RegCoeffField d → ℝ :=
    fun a =>
      max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct 0)⁻¹)
        0
  let upperZero : Homogenization.RegCoeffField d → ℝ :=
    fun a =>
      max
        (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
          hP.barSigmaAtScale hStruct 0)
        0
  let coeff : ℝ := (5 * β⁻¹) ^ 2
  let positiveWeight : Homogenization.RegCoeffField d → ℝ :=
    fun a => σ * lowerZero a + σ⁻¹ * upperZero a
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hβ_le_one : β ≤ 1 := by
    have hle := sLower_add_beta_le_one hP4
    dsimp [β] at hle ⊢
    linarith [hP4.sLower_pos]
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
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, Homogenization.Book.Ch05.sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hcoeff_nonneg : 0 ≤ coeff := by
    dsimp [coeff]
    exact sq_nonneg _
  have hChildMem :
      MeasureTheory.MemLp childAvg
        (ENNReal.ofReal (section53CoarseFluctuationZeta hP4)) P := by
    simpa [childAvg, Q, j, p_e, q_e] using
      memLp_zeta_descendantsAverage_responseJObservableCubeSet_originCube_from_P4_of_stationary
        hP hstat hStruct hP4 hk_nonneg hkm_int p_e q_e
  have hLowerAE : AEMeasurable lowerZero P := by
    simpa [lowerZero, Q] using
      ((hP.aemeasurable_lambdaSqCoeffField_finite_one_inv Q hs'_pos).sub
        aemeasurable_const).max aemeasurable_const
  have hUpperAE : AEMeasurable upperZero P := by
    simpa [upperZero, Q] using
      ((hP.aemeasurable_LambdaSqCoeffField_finite_one Q ht'_pos).sub
        aemeasurable_const).max aemeasurable_const
  have hLower_nonneg : ∀ᵐ a ∂P, 0 ≤ lowerZero a := by
    filter_upwards with a
    exact le_max_right _ _
  have hUpper_nonneg : ∀ᵐ a ∂P, 0 ≤ upperZero a := by
    filter_upwards with a
    exact le_max_right _ _
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
  have hPositiveChildInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          positiveWeight a * childAvg a) P := by
    have hsum :
        MeasureTheory.Integrable
          (fun a : Homogenization.RegCoeffField d =>
            σ * (lowerZero a * childAvg a) +
              σ⁻¹ * (upperZero a * childAvg a)) P :=
      (hLowerChildInt.const_mul σ).add (hUpperChildInt.const_mul σ⁻¹)
    refine hsum.congr ?_
    filter_upwards with a
    dsimp [positiveWeight]
    ring
  have hDefectAE : AEMeasurable defectSum P := by
    refine S.aemeasurable_fun_sum (μ := P) ?_
    intro n _hn
    have hDefAE :
        AEMeasurable
          (fun a : Homogenization.RegCoeffField d =>
            Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
              (m : ℤ) n p_e q_e a) P := by
      simpa [Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale,
        Q] using
        (hP.aemeasurable_descendantsAverage_responseJObservableCubeSet
          Q (Int.toNat ((m : ℤ) - n)) p_e q_e).sub
          (hP.aemeasurable_responseJObservableCubeSet Q p_e q_e)
    exact aemeasurable_const.mul hDefAE.sqrt
  have hLeftAE :
      AEMeasurable
        (fun a : Homogenization.RegCoeffField d =>
          positiveWeight a * defectSum a ^ 2) P := by
    simpa [positiveWeight, pow_two] using
      ((aemeasurable_const.mul hLowerAE).add
        (aemeasurable_const.mul hUpperAE)).mul
        (hDefectAE.mul hDefectAE)
  have hChild_nonneg : ∀ a, 0 ≤ childAvg a := by
    intro a
    dsimp [childAvg]
    exact Homogenization.descendantsAverage_nonneg Q j
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
      (fun R _hR =>
        Homogenization.Book.Ch04.responseJObservableCubeSet_nonneg R p_e q_e a)
  have hPositiveWeight_nonneg : ∀ a, 0 ≤ positiveWeight a := by
    intro a
    dsimp [positiveWeight]
    exact add_nonneg
      (mul_nonneg hσ_nonneg (le_max_right _ _))
      (mul_nonneg hσ_inv_nonneg (le_max_right _ _))
  have hDefect_le :
      ∀ᵐ a ∂P, defectSum a ^ 2 ≤ coeff * childAvg a := by
    filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
    simpa [defectSum, childAvg, coeff, S, w, Q, j, β, p_e, q_e] using
      sq_beta_weighted_sqrt_responseDefectAverageAtScale_le_childResponseAverageAtScale
        ha hk_nonneg hkm_int hβ_pos hβ_le_one p_e q_e
  have hPoint :
      (fun a : Homogenization.RegCoeffField d =>
          positiveWeight a * defectSum a ^ 2)
        ≤ᵐ[P]
        (fun a : Homogenization.RegCoeffField d =>
          coeff * (positiveWeight a * childAvg a)) := by
    filter_upwards [hDefect_le] with a hdef
    calc
      positiveWeight a * defectSum a ^ 2
          ≤ positiveWeight a * (coeff * childAvg a) :=
            mul_le_mul_of_nonneg_left hdef (hPositiveWeight_nonneg a)
      _ = coeff * (positiveWeight a * childAvg a) := by ring
  have hRightInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          coeff * (positiveWeight a * childAvg a)) P :=
    hPositiveChildInt.const_mul coeff
  have hLeftInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          positiveWeight a * defectSum a ^ 2) P := by
    refine MeasureTheory.Integrable.mono' hRightInt
      hLeftAE.aestronglyMeasurable ?_
    filter_upwards [hPoint] with a hle
    have hleft_nonneg : 0 ≤ positiveWeight a * defectSum a ^ 2 :=
      mul_nonneg (hPositiveWeight_nonneg a) (sq_nonneg _)
    have hright_nonneg : 0 ≤ coeff * (positiveWeight a * childAvg a) :=
      mul_nonneg hcoeff_nonneg
        (mul_nonneg (hPositiveWeight_nonneg a) (hChild_nonneg a))
    simpa [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (hPositiveWeight_nonneg a),
      abs_of_nonneg (sq_nonneg (defectSum a)),
      abs_of_nonneg hcoeff_nonneg,
      abs_of_nonneg (hChild_nonneg a)] using hle
  have hmono :
      ∫ a, positiveWeight a * defectSum a ^ 2 ∂P
        ≤ ∫ a, coeff * (positiveWeight a * childAvg a) ∂P :=
    MeasureTheory.integral_mono_ae hLeftInt hRightInt hPoint
  have hRight_eq :
      ∫ a, coeff * (positiveWeight a * childAvg a) ∂P =
        coeff *
          (σ * (∫ a, lowerZero a * childAvg a ∂P) +
            σ⁻¹ * (∫ a, upperZero a * childAvg a ∂P)) := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    have hsplit :
        ∫ a, positiveWeight a * childAvg a ∂P =
          ∫ a, σ * (lowerZero a * childAvg a) +
            σ⁻¹ * (upperZero a * childAvg a) ∂P := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with a
      dsimp [positiveWeight]
      ring
    rw [hsplit]
    rw [MeasureTheory.integral_add (hLowerChildInt.const_mul σ)
      (hUpperChildInt.const_mul σ⁻¹)]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hPositiveChild :
      σ * (∫ a, lowerZero a * childAvg a ∂P) +
          σ⁻¹ * (∫ a, upperZero a * childAvg a ∂P)
        ≤
          C * (hP4.xi : ℝ) *
            Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
              coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
    have hCpos := hC_all hP hstat hStruct hP4 rfl hkm e
    simpa [β, s', t', Q, j, p_e, q_e, σ, childAvg, lowerZero, upperZero] using
      hCpos
  constructor
  · simpa [β, s', t', Q, p_e, q_e, σ, lowerZero, upperZero, defectSum,
      positiveWeight, S, w] using hLeftInt
  · calc
      ∫ a, (σ * lowerZero a + σ⁻¹ * upperZero a) *
          defectSum a ^ 2 ∂P
          =
        ∫ a, positiveWeight a * defectSum a ^ 2 ∂P := by
          simp [positiveWeight]
      _ ≤ ∫ a, coeff * (positiveWeight a * childAvg a) ∂P := hmono
      _ =
          coeff *
            (σ * (∫ a, lowerZero a * childAvg a ∂P) +
              σ⁻¹ * (∫ a, upperZero a * childAvg a ∂P)) := hRight_eq
      _ ≤
          coeff *
            (C * (hP4.xi : ℝ) *
              Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
                coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
                  coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e) :=
            mul_le_mul_of_nonneg_left hPositiveChild hcoeff_nonneg
      _ =
          (5 * β⁻¹) ^ 2 * C * (hP4.xi : ℝ) *
            Real.rpow (3 : ℝ) (-β * (m : ℝ)) *
            coarseFluctuationUnitMomentWeightAtScale hP hStruct hP4 m *
              coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
            dsimp [coeff]
            ring

/--
Source label `p.HC.CR`: integrability of the local positive-excess lower-edge
integrand.  This is the integrability companion to the checked local-to-zero
lower-edge decomposition: the local scale-`k` excess is dominated by LIH's
scale-zero excess plus the deterministic baseline-gap multiple of the
defect-square term.
-/
theorem integrable_localPositiveExcess_defectSum_sq_special_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hstat : Homogenization.Book.Ch04.StationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
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
    let lowerLocal := fun a : Homogenization.RegCoeffField d =>
      max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹)
        0
    let upperLocal := fun a : Homogenization.RegCoeffField d =>
      max
        (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
          hP.barSigmaAtScale hStruct (k : ℤ))
        0
    let defectSum := fun a : Homogenization.RegCoeffField d =>
      ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
        Real.rpow (3 : ℝ)
            (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          Real.sqrt
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
              (m : ℤ) n p_e q_e a)
    MeasureTheory.Integrable
      (fun a : Homogenization.RegCoeffField d =>
        (σ * lowerLocal a + σ⁻¹ * upperLocal a) * defectSum a ^ 2) P := by
  classical
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let lowerLocal := fun a : Homogenization.RegCoeffField d =>
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹)
      0
  let upperLocal := fun a : Homogenization.RegCoeffField d =>
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
        hP.barSigmaAtScale hStruct (k : ℤ))
      0
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
  let defectSum := fun a : Homogenization.RegCoeffField d =>
    ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
      Real.rpow (3 : ℝ)
          (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
        Real.sqrt
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
            (m : ℤ) n p_e q_e a)
  let localEdge := fun a : Homogenization.RegCoeffField d =>
    (σ * lowerLocal a + σ⁻¹ * upperLocal a) * defectSum a ^ 2
  let zeroEdge := fun a : Homogenization.RegCoeffField d =>
    (σ * lowerZero a + σ⁻¹ * upperZero a) * defectSum a ^ 2
  let gap := localPositiveExcessBaselineGapAtScales hP hStruct k m
  let rhs := fun a : Homogenization.RegCoeffField d =>
    zeroEdge a + gap * defectSum a ^ 2
  have hDsq_int :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d => defectSum a ^ 2) P := by
    simpa [defectSum, β, p_e, q_e] using
      integrable_defectSum_sq_special_of_P4 hP hstat hStruct hP4 hkm e
  rcases
      integral_zeroBaselinePositiveExcess_defectSum_sq_special_le_responseMoment
        hP4.params with ⟨C0, _hC0_nonneg, hzero_all⟩
  have hzero_pair := hzero_all hP hstat hStruct hP4 rfl hkm e
  have hZeroEdge_int : MeasureTheory.Integrable zeroEdge P := by
    simpa [zeroEdge, β, s', t', Q, p_e, q_e, σ, lowerZero, upperZero,
      defectSum] using hzero_pair.1
  have hGapD_int :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d => gap * defectSum a ^ 2) P :=
    hDsq_int.const_mul gap
  have hrhs_int : MeasureTheory.Integrable rhs P :=
    hZeroEdge_int.add hGapD_int
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hs'_pos : 0 < s' := by
    dsimp [s', β]
    linarith [hP4.sLower_pos, hβ_pos]
  have ht'_pos : 0 < t' := by
    dsimp [t', β]
    linarith [hP4.sUpper_pos, hβ_pos]
  have hLowerLocalAE : AEMeasurable lowerLocal P := by
    simpa [lowerLocal, Q] using
      ((hP.aemeasurable_lambdaSqCoeffField_finite_one_inv Q hs'_pos).sub
        aemeasurable_const).max aemeasurable_const
  have hUpperLocalAE : AEMeasurable upperLocal P := by
    simpa [upperLocal, Q] using
      ((hP.aemeasurable_LambdaSqCoeffField_finite_one Q ht'_pos).sub
        aemeasurable_const).max aemeasurable_const
  have hDsqAE :
      AEMeasurable (fun a : Homogenization.RegCoeffField d => defectSum a ^ 2) P :=
    hDsq_int.aestronglyMeasurable.aemeasurable
  have hLocalEdgeAE : AEMeasurable localEdge P := by
    simpa [localEdge] using
      ((aemeasurable_const.mul hLowerLocalAE).add
        (aemeasurable_const.mul hUpperLocalAE)).mul hDsqAE
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, Homogenization.Book.Ch05.sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hgap_nonneg : 0 ≤ gap := by
    simpa [gap] using
      localPositiveExcessBaselineGapAtScales_nonneg_of_P4
        hP hStruct hP4 k m
  have hlocal_nonneg : ∀ a, 0 ≤ localEdge a := by
    intro a
    dsimp [localEdge]
    exact mul_nonneg
      (add_nonneg
        (mul_nonneg hσ_nonneg (le_max_right _ _))
        (mul_nonneg hσ_inv_nonneg (le_max_right _ _)))
      (sq_nonneg _)
  have hzero_nonneg : ∀ a, 0 ≤ zeroEdge a := by
    intro a
    dsimp [zeroEdge]
    exact mul_nonneg
      (add_nonneg
        (mul_nonneg hσ_nonneg (le_max_right _ _))
        (mul_nonneg hσ_inv_nonneg (le_max_right _ _)))
      (sq_nonneg _)
  have hrhs_nonneg : ∀ a, 0 ≤ rhs a := by
    intro a
    dsimp [rhs]
    exact add_nonneg (hzero_nonneg a) (mul_nonneg hgap_nonneg (sq_nonneg _))
  have hpoint : ∀ a, localEdge a ≤ rhs a := by
    intro a
    have hweight :
        σ * lowerLocal a + σ⁻¹ * upperLocal a ≤
          σ * lowerZero a + σ⁻¹ * upperZero a + gap := by
      simpa [Q, σ, lowerLocal, lowerZero, upperLocal, upperZero, gap] using
        localPositiveExcessWeight_le_zeroBaseline_add_gap_of_P4
          hP hStruct hP4 k m s' t' a
    calc
      localEdge a
          ≤ (σ * lowerZero a + σ⁻¹ * upperZero a + gap) *
              defectSum a ^ 2 :=
            mul_le_mul_of_nonneg_right hweight (sq_nonneg _)
      _ = rhs a := by
          dsimp [localEdge, rhs, zeroEdge]
          ring
  refine MeasureTheory.Integrable.mono' hrhs_int
    hLocalEdgeAE.aestronglyMeasurable ?_
  filter_upwards with a
  have hnorm_eq : ‖localEdge a‖ = localEdge a := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hlocal_nonneg a)]
  simpa [localEdge, σ, lowerLocal, upperLocal, defectSum, β, s', t', Q,
    p_e, q_e, Homogenization.Book.Ch05.sigmaHatAtScale,
    Homogenization.Book.Ch05.specialPAtScale,
    Homogenization.Book.Ch05.specialQAtScale] using
      hnorm_eq.trans_le (hpoint a)

/--
Source label `p.HC.CR`: integrability of the terminal positive-excess
lower-edge integrand.  This discharges the integrability side-condition for
the terminal lower-edge route from `(P4)`, leaving only the genuine good/bad
terminal positive-excess bound to be proved downstream.
-/
theorem integrable_terminalPositiveExcess_defectSum_sq_special_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hstat : Homogenization.Book.Ch04.StationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
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
    let defectSum := fun a : Homogenization.RegCoeffField d =>
      ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
        Real.rpow (3 : ℝ)
            (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          Real.sqrt
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
              (m : ℤ) n p_e q_e a)
    MeasureTheory.Integrable
      (fun a : Homogenization.RegCoeffField d =>
        (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) * defectSum a ^ 2) P := by
  classical
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
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
  let defectSum := fun a : Homogenization.RegCoeffField d =>
    ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
      Real.rpow (3 : ℝ)
          (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
        Real.sqrt
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
            (m : ℤ) n p_e q_e a)
  let terminalEdge := fun a : Homogenization.RegCoeffField d =>
    (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) * defectSum a ^ 2
  let zeroEdge := fun a : Homogenization.RegCoeffField d =>
    (σ * lowerZero a + σ⁻¹ * upperZero a) * defectSum a ^ 2
  let gap := localPositiveExcessBaselineGapAtScales hP hStruct m m
  let rhs := fun a : Homogenization.RegCoeffField d =>
    zeroEdge a + gap * defectSum a ^ 2
  have hDsq_int :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d => defectSum a ^ 2) P := by
    simpa [defectSum, β, p_e, q_e] using
      integrable_defectSum_sq_special_of_P4 hP hstat hStruct hP4 hkm e
  rcases
      integral_zeroBaselinePositiveExcess_defectSum_sq_special_le_responseMoment
        hP4.params with ⟨C0, _hC0_nonneg, hzero_all⟩
  have hzero_pair := hzero_all hP hstat hStruct hP4 rfl hkm e
  have hZeroEdge_int : MeasureTheory.Integrable zeroEdge P := by
    simpa [zeroEdge, β, s', t', Q, p_e, q_e, σ, lowerZero, upperZero,
      defectSum] using hzero_pair.1
  have hGapD_int :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d => gap * defectSum a ^ 2) P :=
    hDsq_int.const_mul gap
  have hrhs_int : MeasureTheory.Integrable rhs P :=
    hZeroEdge_int.add hGapD_int
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hs'_pos : 0 < s' := by
    dsimp [s', β]
    linarith [hP4.sLower_pos, hβ_pos]
  have ht'_pos : 0 < t' := by
    dsimp [t', β]
    linarith [hP4.sUpper_pos, hβ_pos]
  have hLowerTerminalAE : AEMeasurable lowerTerminal P := by
    simpa [lowerTerminal, Q] using
      ((hP.aemeasurable_lambdaSqCoeffField_finite_one_inv Q hs'_pos).sub
        aemeasurable_const).max aemeasurable_const
  have hUpperTerminalAE : AEMeasurable upperTerminal P := by
    simpa [upperTerminal, Q] using
      ((hP.aemeasurable_LambdaSqCoeffField_finite_one Q ht'_pos).sub
        aemeasurable_const).max aemeasurable_const
  have hDsqAE :
      AEMeasurable (fun a : Homogenization.RegCoeffField d => defectSum a ^ 2) P :=
    hDsq_int.aestronglyMeasurable.aemeasurable
  have hTerminalEdgeAE : AEMeasurable terminalEdge P := by
    simpa [terminalEdge] using
      ((aemeasurable_const.mul hLowerTerminalAE).add
        (aemeasurable_const.mul hUpperTerminalAE)).mul hDsqAE
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, Homogenization.Book.Ch05.sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hgap_nonneg : 0 ≤ gap := by
    simpa [gap] using
      localPositiveExcessBaselineGapAtScales_nonneg_of_P4
        hP hStruct hP4 m m
  have hterminal_nonneg : ∀ a, 0 ≤ terminalEdge a := by
    intro a
    dsimp [terminalEdge]
    exact mul_nonneg
      (add_nonneg
        (mul_nonneg hσ_nonneg (le_max_right _ _))
        (mul_nonneg hσ_inv_nonneg (le_max_right _ _)))
      (sq_nonneg _)
  have hzero_nonneg : ∀ a, 0 ≤ zeroEdge a := by
    intro a
    dsimp [zeroEdge]
    exact mul_nonneg
      (add_nonneg
        (mul_nonneg hσ_nonneg (le_max_right _ _))
        (mul_nonneg hσ_inv_nonneg (le_max_right _ _)))
      (sq_nonneg _)
  have hpoint : ∀ a, terminalEdge a ≤ rhs a := by
    intro a
    have hweight :
        σ * lowerTerminal a + σ⁻¹ * upperTerminal a ≤
          σ * lowerZero a + σ⁻¹ * upperZero a + gap := by
      simpa [Q, σ, lowerTerminal, lowerZero, upperTerminal, upperZero, gap] using
        localPositiveExcessWeight_le_zeroBaseline_add_gap_of_P4
          hP hStruct hP4 m m s' t' a
    calc
      terminalEdge a
          ≤ (σ * lowerZero a + σ⁻¹ * upperZero a + gap) *
              defectSum a ^ 2 :=
            mul_le_mul_of_nonneg_right hweight (sq_nonneg _)
      _ = rhs a := by
          dsimp [terminalEdge, rhs, zeroEdge]
          ring
  refine MeasureTheory.Integrable.mono' hrhs_int
    hTerminalEdgeAE.aestronglyMeasurable ?_
  filter_upwards with a
  have hnorm_eq : ‖terminalEdge a‖ = terminalEdge a := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hterminal_nonneg a)]
  simpa [terminalEdge, σ, lowerTerminal, upperTerminal, defectSum, β, s', t', Q,
    p_e, q_e, Homogenization.Book.Ch05.sigmaHatAtScale,
    Homogenization.Book.Ch05.specialPAtScale,
    Homogenization.Book.Ch05.specialQAtScale] using
      hnorm_eq.trans_le (hpoint a)

/--
Source labels `p.HC.CR` and `e.J.moment.bound`: integrability of the
terminal positive-excess lower-edge integrand with the child-response average.
This is the side condition needed to route the low-tail response branch
through the Section 5.2 terminal split, without collapsing it to the stale
window-moment coefficient.
-/
theorem integrable_terminalPositiveExcess_childResponseAverage_special_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hstat : Homogenization.Book.Ch04.StationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
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
        (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
    let response := fun a : Homogenization.RegCoeffField d =>
      (5 * β⁻¹) ^ 2 * childAvg a
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
        (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) * response a) P := by
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
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
  let response : Homogenization.RegCoeffField d → ℝ := fun a =>
    (5 * β⁻¹) ^ 2 * childAvg a
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
  let terminalEdge := fun a : Homogenization.RegCoeffField d =>
    (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) * response a
  let zeroEdge := fun a : Homogenization.RegCoeffField d =>
    (σ * lowerZero a + σ⁻¹ * upperZero a) * response a
  let gap := localPositiveExcessBaselineGapAtScales hP hStruct m m
  let rhs := fun a : Homogenization.RegCoeffField d =>
    zeroEdge a + gap * response a
  let coeff : ℝ := (5 * β⁻¹) ^ 2
  let zeroWeight := fun a : Homogenization.RegCoeffField d =>
    σ * lowerZero a + σ⁻¹ * upperZero a
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
      memLp_zeta_descendantsAverage_responseJObservableCubeSet_originCube_from_P4_of_stationary
        hP hstat hStruct hP4 hk_nonneg hkm_int p_e q_e
  have hChildInt : MeasureTheory.Integrable childAvg P := by
    have hdesc :=
      integrable_terminalDescendantsAverage_responseJObservableCubeSet_and_integral_le
        hP hstat hStruct hP4 hkm.le e
    simpa [childAvg, Q, p_e, q_e] using hdesc.1
  have hResponseInt : MeasureTheory.Integrable response P := by
    simpa [response, coeff] using hChildInt.const_mul coeff
  have hLowerZeroAE : AEMeasurable lowerZero P := by
    simpa [lowerZero, Q] using
      ((hP.aemeasurable_lambdaSqCoeffField_finite_one_inv Q hs'_pos).sub
        aemeasurable_const).max aemeasurable_const
  have hUpperZeroAE : AEMeasurable upperZero P := by
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
    memLp_of_integrable_nonneg_nat_pow hP4.xi_pos hLowerZeroAE
      hLower_nonneg hLowerPowInt
  have hUpperMem :
      MeasureTheory.MemLp upperZero (ENNReal.ofReal (hP4.xi : ℝ)) P :=
    memLp_of_integrable_nonneg_nat_pow hP4.xi_pos hUpperZeroAE
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
  have hZeroWeightChildInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d => zeroWeight a * childAvg a) P := by
    have hsum :
        MeasureTheory.Integrable
          (fun a : Homogenization.RegCoeffField d =>
            σ * (lowerZero a * childAvg a) +
              σ⁻¹ * (upperZero a * childAvg a)) P :=
      (hLowerChildInt.const_mul σ).add (hUpperChildInt.const_mul σ⁻¹)
    refine hsum.congr ?_
    filter_upwards with a
    dsimp [zeroWeight]
    ring
  have hZeroEdgeInt : MeasureTheory.Integrable zeroEdge P := by
    have hscaled :
        MeasureTheory.Integrable
          (fun a : Homogenization.RegCoeffField d =>
            coeff * (zeroWeight a * childAvg a)) P :=
      hZeroWeightChildInt.const_mul coeff
    refine hscaled.congr ?_
    filter_upwards with a
    dsimp [zeroEdge, response, zeroWeight, coeff]
    ring
  have hGapResponseInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d => gap * response a) P :=
    hResponseInt.const_mul gap
  have hrhs_int : MeasureTheory.Integrable rhs P :=
    hZeroEdgeInt.add hGapResponseInt
  have hLowerTerminalAE : AEMeasurable lowerTerminal P := by
    simpa [lowerTerminal, Q] using
      ((hP.aemeasurable_lambdaSqCoeffField_finite_one_inv Q hs'_pos).sub
        aemeasurable_const).max aemeasurable_const
  have hUpperTerminalAE : AEMeasurable upperTerminal P := by
    simpa [upperTerminal, Q] using
      ((hP.aemeasurable_LambdaSqCoeffField_finite_one Q ht'_pos).sub
        aemeasurable_const).max aemeasurable_const
  have hResponseAE : AEMeasurable response P :=
    hResponseInt.aestronglyMeasurable.aemeasurable
  have hTerminalEdgeAE : AEMeasurable terminalEdge P := by
    simpa [terminalEdge] using
      ((aemeasurable_const.mul hLowerTerminalAE).add
        (aemeasurable_const.mul hUpperTerminalAE)).mul hResponseAE
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, Homogenization.Book.Ch05.sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hgap_nonneg : 0 ≤ gap := by
    simpa [gap] using
      localPositiveExcessBaselineGapAtScales_nonneg_of_P4
        hP hStruct hP4 m m
  have hchild_nonneg : ∀ a, 0 ≤ childAvg a := by
    intro a
    dsimp [childAvg]
    exact Homogenization.descendantsAverage_nonneg Q (m - k)
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
      (fun R _hR =>
        Homogenization.Book.Ch04.responseJObservableCubeSet_nonneg R p_e q_e a)
  have hresponse_nonneg : ∀ a, 0 ≤ response a := by
    intro a
    dsimp [response]
    exact mul_nonneg (sq_nonneg _) (hchild_nonneg a)
  have hterminal_nonneg : ∀ a, 0 ≤ terminalEdge a := by
    intro a
    dsimp [terminalEdge]
    exact mul_nonneg
      (add_nonneg
        (mul_nonneg hσ_nonneg (le_max_right _ _))
        (mul_nonneg hσ_inv_nonneg (le_max_right _ _)))
      (hresponse_nonneg a)
  have hpoint : ∀ a, terminalEdge a ≤ rhs a := by
    intro a
    have hweight :
        σ * lowerTerminal a + σ⁻¹ * upperTerminal a ≤
          σ * lowerZero a + σ⁻¹ * upperZero a + gap := by
      simpa [Q, σ, lowerTerminal, lowerZero, upperTerminal, upperZero, gap] using
        localPositiveExcessWeight_le_zeroBaseline_add_gap_of_P4
          hP hStruct hP4 m m s' t' a
    calc
      terminalEdge a
          ≤ (σ * lowerZero a + σ⁻¹ * upperZero a + gap) *
              response a :=
            mul_le_mul_of_nonneg_right hweight (hresponse_nonneg a)
      _ = rhs a := by
          dsimp [terminalEdge, rhs, zeroEdge]
          ring
  refine MeasureTheory.Integrable.mono' hrhs_int
    hTerminalEdgeAE.aestronglyMeasurable ?_
  filter_upwards with a
  have hnorm_eq : ‖terminalEdge a‖ = terminalEdge a := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hterminal_nonneg a)]
  simpa [terminalEdge, σ, lowerTerminal, upperTerminal, response, β, s', t', Q,
    p_e, q_e, childAvg, Homogenization.Book.Ch05.sigmaHatAtScale,
    Homogenization.Book.Ch05.specialPAtScale,
    Homogenization.Book.Ch05.specialQAtScale] using
      hnorm_eq.trans_le (hpoint a)

end

end Homogenization.HighContrast.EntryScale
