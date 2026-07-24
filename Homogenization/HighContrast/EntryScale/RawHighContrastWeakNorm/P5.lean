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
Source labels `p.HC.CR`, `e.weaknorms.moreproto`, and `e.J.moment.bound`:
the child-response average appearing in the source-max Holder core has
`L^zeta` root bounded by the canonical coarse-fluctuation response moment.
This is the shared response factor used by the small, low, and bad-event
pieces of the lower-edge decomposition.
-/
theorem childResponseAverage_zetaRoot_le_coarseFluctuationResponseMomentAtScale_of_stationary
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hstat : Homogenization.Book.Ch04.StationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Homogenization.Vec d) :
    let ζ := section53CoarseFluctuationZeta hP4
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let childAvg := fun a : Homogenization.CoeffField d =>
      Homogenization.descendantsAverage Q (m - k)
        (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
    (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) ≤
      coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
  classical
  dsimp only
  let ζ := section53CoarseFluctuationZeta hP4
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let childAvg : Homogenization.CoeffField d → ℝ := fun a =>
    Homogenization.descendantsAverage Q (m - k)
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by
    exact_mod_cast Nat.zero_le k
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by
    exact_mod_cast hkm.le
  have hchild_nonneg_all : ∀ a, 0 ≤ childAvg a := by
    intro a
    dsimp [childAvg]
    exact Homogenization.descendantsAverage_nonneg Q (m - k)
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
      (fun R _hR =>
        Homogenization.Book.Ch04.responseJObservableCubeSet_nonneg R p_e q_e a)
  have hIntLe :=
    integral_rpow_descendantsAverage_responseJObservableCubeSet_originCube_le_originCube_of_stationary
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

/--
Source labels `p.HC.CR`, `e.weaknorms.moreproto`, and `e.J.moment.bound`:
the Section 5.2 small-tail child-response term is bounded directly by the
response moment from the lower-edge Holder step.  The estimate keeps the
manuscript response factor
`coarseFluctuationResponseMomentAtScale`; it does not replace it by a
window/unit ellipticity moment.

This is the scalar-bound producer for the `hSmallBound` slot in the terminal
lower-edge assembly.  The bound is proved by comparing the nonnegative
small-tail integrand with the integrable Holder envelope, so the scalar
estimate no longer needs the separate small-tail integrability slot.
-/
theorem integrable_section52SmallTail_childResponseAverage_special_and_integral_le_responseMoment
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
    let D := Homogenization.descendantsAtScale Q 0
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let childAvg := fun a : Homogenization.CoeffField d =>
      Homogenization.descendantsAverage Q (m - k)
        (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
    let response := fun a : Homogenization.CoeffField d =>
      (5 * β⁻¹) ^ 2 * childAvg a
    let lowerSmall := fun a : Homogenization.CoeffField d =>
      Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
          (d := d) m s' a ^ 2 /
        Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
    let upperSmall := fun a : Homogenization.CoeffField d =>
      Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
          (d := d) m t' a ^ 2 /
        Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
    let lowerCoeff :=
      (25 * hP4.sLower⁻¹ * (s' - hP4.sLower)⁻¹ *
            Real.rpow (3 : ℝ) (-s' * (m : ℝ))) ^ 2 /
          Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
    let upperCoeff :=
      (25 * hP4.sUpper⁻¹ * (t' - hP4.sUpper)⁻¹ *
            Real.rpow (3 : ℝ) (-t' * (m : ℝ))) ^ 2 /
          Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
    MeasureTheory.Integrable
      (fun a : Homogenization.CoeffField d =>
        (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a) P ∧
    ∫ a, (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a ∂P ≤
      (5 * β⁻¹) ^ 2 *
        (σ * lowerCoeff *
            ((D.card : ℝ) ^ (1 / (hP4.xi : ℝ)) *
              Homogenization.Book.Ch04.lambdaInvMomentAtScale
                P 0 hP4.sLower hP4.xi *
              coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e) +
          σ⁻¹ * upperCoeff *
            ((D.card : ℝ) ^ (1 / (hP4.xi : ℝ)) *
              Homogenization.Book.Ch04.LambdaMomentAtScale
                P 0 hP4.sUpper hP4.xi *
              coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e)) := by
  classical
  dsimp only
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let ζ := section53CoarseFluctuationZeta hP4
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let D : Finset (Homogenization.TriadicCube d) :=
    Homogenization.descendantsAtScale Q 0
  let hD : D.Nonempty :=
    Homogenization.descendantsAtScale_nonempty Q (by simp [Q, Homogenization.originCube])
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let childAvg : Homogenization.CoeffField d → ℝ := fun a =>
    Homogenization.descendantsAverage Q (m - k)
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
  let response : Homogenization.CoeffField d → ℝ := fun a =>
    (5 * β⁻¹) ^ 2 * childAvg a
  let lowerSmall : Homogenization.CoeffField d → ℝ := fun a =>
    Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
        (d := d) m s' a ^ 2 /
      Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
  let upperSmall : Homogenization.CoeffField d → ℝ := fun a =>
    Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
        (d := d) m t' a ^ 2 /
      Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
  let lowerSup : Homogenization.CoeffField d → ℝ := fun a =>
    D.sup' hD
      (fun U =>
        (Homogenization.Book.Ch04.lambdaSqCoeffField U hP4.sLower (.finite 1) a)⁻¹)
  let upperSup : Homogenization.CoeffField d → ℝ := fun a =>
    D.sup' hD
      (fun U =>
        Homogenization.Book.Ch04.LambdaSqCoeffField U hP4.sUpper (.finite 1) a)
  let lowerCoeff : ℝ :=
    (25 * hP4.sLower⁻¹ * (s' - hP4.sLower)⁻¹ *
          Real.rpow (3 : ℝ) (-s' * (m : ℝ))) ^ 2 /
        Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
  let upperCoeff : ℝ :=
    (25 * hP4.sUpper⁻¹ * (t' - hP4.sUpper)⁻¹ *
          Real.rpow (3 : ℝ) (-t' * (m : ℝ))) ^ 2 /
        Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
  let responseMoment :=
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  let coeffResponse : ℝ := (5 * β⁻¹) ^ 2
  let envelope : Homogenization.CoeffField d → ℝ := fun a =>
    coeffResponse *
      (σ * lowerCoeff * (lowerSup a * childAvg a) +
        σ⁻¹ * upperCoeff * (upperSup a * childAvg a))
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
  have hζ_pos : 0 < ζ := by
    simpa [ζ] using section53CoarseFluctuationZeta_pos hP4
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hkm.le
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, Homogenization.Book.Ch05.sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hcoeffResponse_nonneg : 0 ≤ coeffResponse := by
    dsimp [coeffResponse]
    exact sq_nonneg _
  have hlowerCoeff_nonneg : 0 ≤ lowerCoeff := by
    dsimp [lowerCoeff]
    exact div_nonneg (sq_nonneg _)
      (Homogenization.Book.Ch05.Section52.section52SmallTailWeight_nonneg
        hs'_pos.le m)
  have hupperCoeff_nonneg : 0 ≤ upperCoeff := by
    dsimp [upperCoeff]
    exact div_nonneg (sq_nonneg _)
      (Homogenization.Book.Ch05.Section52.section52SmallTailWeight_nonneg
        ht'_pos.le m)
  have hchild_nonneg_all : ∀ a, 0 ≤ childAvg a := by
    intro a
    dsimp [childAvg]
    exact Homogenization.descendantsAverage_nonneg Q (m - k)
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
      (fun R _hR =>
        Homogenization.Book.Ch04.responseJObservableCubeSet_nonneg R p_e q_e a)
  have hchild_nonneg : 0 ≤ᵐ[P] childAvg :=
    Filter.Eventually.of_forall hchild_nonneg_all
  have hLowerSup_nonneg_all : ∀ a, 0 ≤ lowerSup a := by
    intro a
    simpa [lowerSup, D, Q] using
      Homogenization.Book.Ch05.Section52.lower_unitDescendantSup_nonneg
        (d := d) (s := hP4.sLower) (m := m) hP4.sLower_pos a
  have hUpperSup_nonneg_all : ∀ a, 0 ≤ upperSup a := by
    intro a
    simpa [upperSup, D, Q] using
      Homogenization.Book.Ch05.Section52.upper_unitDescendantSup_nonneg
        (d := d) (s := hP4.sUpper) (m := m) hP4.sUpper_pos a
  have hLowerSup_nonneg : 0 ≤ᵐ[P] lowerSup :=
    Filter.Eventually.of_forall hLowerSup_nonneg_all
  have hUpperSup_nonneg : 0 ≤ᵐ[P] upperSup :=
    Filter.Eventually.of_forall hUpperSup_nonneg_all
  have hChildMem :
      MeasureTheory.MemLp childAvg
        (ENNReal.ofReal (section53CoarseFluctuationZeta hP4)) P := by
    simpa [childAvg, Q, p_e, q_e] using
      memLp_zeta_descendantsAverage_responseJObservableCubeSet_originCube_from_P4_of_stationary
        hP hstat hStruct hP4 hk_nonneg hkm_int p_e q_e
  have hLowerSupAE : AEMeasurable lowerSup P := by
    simpa [lowerSup, D, Q] using
      Homogenization.Book.Ch05.Section52.lower_unitDescendantSup_aemeasurable
        (d := d) (P := P) hP (s := hP4.sLower) (m := m) hP4.sLower_pos
  have hUpperSupAE : AEMeasurable upperSup P := by
    simpa [upperSup, D, Q] using
      Homogenization.Book.Ch05.Section52.upper_unitDescendantSup_aemeasurable
        (d := d) (P := P) hP (s := hP4.sUpper) (m := m) hP4.sUpper_pos
  have hξ_one : 1 ≤ hP4.xi := by
    exact Nat.succ_le_of_lt hP4.xi_pos
  have hLowerSupAbsInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d => |lowerSup a| ^ hP4.xi) P := by
    simpa [lowerSup, D, Q] using
      Homogenization.Book.Ch05.Section52.lower_unitDescendantSup_integrable_abs_pow
        (d := d) (P := P) hP hStruct
        (s := hP4.sLower) (ξ := hP4.xi) (m := m)
        hP4.sLower_pos hξ_one hP4.lower_inv_moment_integrable
  have hUpperSupAbsInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d => |upperSup a| ^ hP4.xi) P := by
    simpa [upperSup, D, Q] using
      Homogenization.Book.Ch05.Section52.upper_unitDescendantSup_integrable_abs_pow
        (d := d) (P := P) hP hStruct
        (s := hP4.sUpper) (ξ := hP4.xi) (m := m)
        hP4.sUpper_pos hξ_one hP4.upper_moment_integrable
  have hLowerSupPowInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d => lowerSup a ^ hP4.xi) P := by
    refine hLowerSupAbsInt.congr ?_
    filter_upwards with a
    rw [abs_of_nonneg (hLowerSup_nonneg_all a)]
  have hUpperSupPowInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d => upperSup a ^ hP4.xi) P := by
    refine hUpperSupAbsInt.congr ?_
    filter_upwards with a
    rw [abs_of_nonneg (hUpperSup_nonneg_all a)]
  have hLowerSupMem :
      MeasureTheory.MemLp lowerSup (ENNReal.ofReal (hP4.xi : ℝ)) P :=
    memLp_of_integrable_nonneg_nat_pow hP4.xi_pos hLowerSupAE
      hLowerSup_nonneg hLowerSupPowInt
  have hUpperSupMem :
      MeasureTheory.MemLp upperSup (ENNReal.ofReal (hP4.xi : ℝ)) P :=
    memLp_of_integrable_nonneg_nat_pow hP4.xi_pos hUpperSupAE
      hUpperSup_nonneg hUpperSupPowInt
  have hHolderReal :
      (hP4.xi : ℝ).HolderConjugate (section53CoarseFluctuationZeta hP4) :=
    holderConjugate_xi_section53CoarseFluctuationZeta hP4
  letI : ENNReal.HolderTriple
      (ENNReal.ofReal (hP4.xi : ℝ))
      (ENNReal.ofReal (section53CoarseFluctuationZeta hP4)) 1 := by
    simpa using Real.HolderTriple.ennrealOfReal hHolderReal
  have hLowerProdInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d => lowerSup a * childAvg a) P :=
    hLowerSupMem.integrable_mul hChildMem
  have hUpperProdInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d => upperSup a * childAvg a) P :=
    hUpperSupMem.integrable_mul hChildMem
  have hChildMomentRoot_le :
      (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) ≤ responseMoment := by
    simpa [childAvg, Q, ζ, p_e, q_e, responseMoment] using
      childResponseAverage_zetaRoot_le_coarseFluctuationResponseMomentAtScale_of_stationary
        hP hstat hStruct hP4 hkm e
  have hChildMomentRoot_nonneg :
      0 ≤ (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) := by
    exact Real.rpow_nonneg
      (MeasureTheory.integral_nonneg fun a =>
        Real.rpow_nonneg (hchild_nonneg_all a) _) _
  have hResponseMoment_nonneg : 0 ≤ responseMoment := by
    simpa [responseMoment] using
      coarseFluctuationResponseMomentAtScale_nonneg hP hStruct hP4 k m e
  have hLowerRoot_le :
      Homogenization.Book.Ch04.annealedMomentRoot P hP4.xi lowerSup ≤
        (D.card : ℝ) ^ (1 / (hP4.xi : ℝ)) *
          Homogenization.Book.Ch04.lambdaInvMomentAtScale
            P 0 hP4.sLower hP4.xi := by
    simpa [lowerSup, D, Q] using
      Homogenization.Book.Ch05.Section52.lower_unitDescendantSup_momentRoot_le_card_mul_origin
        (d := d) (P := P) hP hStruct
        (s := hP4.sLower) (ξ := hP4.xi) (m := m)
        hP4.sLower_pos hξ_one hP4.lower_inv_moment_integrable
  have hUpperRoot_le :
      Homogenization.Book.Ch04.annealedMomentRoot P hP4.xi upperSup ≤
        (D.card : ℝ) ^ (1 / (hP4.xi : ℝ)) *
          Homogenization.Book.Ch04.LambdaMomentAtScale
            P 0 hP4.sUpper hP4.xi := by
    simpa [upperSup, D, Q] using
      Homogenization.Book.Ch05.Section52.upper_unitDescendantSup_momentRoot_le_card_mul_origin
        (d := d) (P := P) hP hStruct
        (s := hP4.sUpper) (ξ := hP4.xi) (m := m)
        hP4.sUpper_pos hξ_one hP4.upper_moment_integrable
  have hLowerRootTarget_nonneg :
      0 ≤ (D.card : ℝ) ^ (1 / (hP4.xi : ℝ)) *
        Homogenization.Book.Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi := by
    exact mul_nonneg
      (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le D.card) _)
      (Homogenization.Book.Ch04.lambdaInvMomentAtScale_nonneg
        P 0 hP4.xi hP4.sLower_pos)
  have hUpperRootTarget_nonneg :
      0 ≤ (D.card : ℝ) ^ (1 / (hP4.xi : ℝ)) *
        Homogenization.Book.Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi := by
    exact mul_nonneg
      (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le D.card) _)
      (Homogenization.Book.Ch04.LambdaMomentAtScale_nonneg
        P 0 hP4.xi hP4.sUpper_pos)
  have hLowerHolder :
      ∫ a, lowerSup a * childAvg a ∂P ≤
        ((D.card : ℝ) ^ (1 / (hP4.xi : ℝ)) *
          Homogenization.Book.Ch04.lambdaInvMomentAtScale
            P 0 hP4.sLower hP4.xi) *
          responseMoment := by
    have hHolderRaw :=
      MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
        (μ := P) hHolderReal hLowerSup_nonneg hchild_nonneg
        hLowerSupMem hChildMem
    have hHolder :
        ∫ a, lowerSup a * childAvg a ∂P ≤
          Homogenization.Book.Ch04.annealedMomentRoot P hP4.xi lowerSup *
            (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) := by
      simpa [lowerSup, Homogenization.Book.Ch04.annealedMomentRoot, ζ,
        one_div, Real.rpow_natCast] using hHolderRaw
    exact hHolder.trans
      (mul_le_mul hLowerRoot_le hChildMomentRoot_le
        hChildMomentRoot_nonneg hLowerRootTarget_nonneg)
  have hUpperHolder :
      ∫ a, upperSup a * childAvg a ∂P ≤
        ((D.card : ℝ) ^ (1 / (hP4.xi : ℝ)) *
          Homogenization.Book.Ch04.LambdaMomentAtScale
            P 0 hP4.sUpper hP4.xi) *
          responseMoment := by
    have hHolderRaw :=
      MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
        (μ := P) hHolderReal hUpperSup_nonneg hchild_nonneg
        hUpperSupMem hChildMem
    have hHolder :
        ∫ a, upperSup a * childAvg a ∂P ≤
          Homogenization.Book.Ch04.annealedMomentRoot P hP4.xi upperSup *
            (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) := by
      simpa [upperSup, Homogenization.Book.Ch04.annealedMomentRoot, ζ,
        one_div, Real.rpow_natCast] using hHolderRaw
    exact hHolder.trans
      (mul_le_mul hUpperRoot_le hChildMomentRoot_le
        hChildMomentRoot_nonneg hUpperRootTarget_nonneg)
  have hEnvelopeInt : MeasureTheory.Integrable envelope P := by
    have hsum :
        MeasureTheory.Integrable
          (fun a : Homogenization.CoeffField d =>
            σ * lowerCoeff * (lowerSup a * childAvg a) +
              σ⁻¹ * upperCoeff * (upperSup a * childAvg a)) P :=
      (hLowerProdInt.const_mul (σ * lowerCoeff)).add
        (hUpperProdInt.const_mul (σ⁻¹ * upperCoeff))
    simpa [envelope, mul_assoc] using hsum.const_mul coeffResponse
  have hEnvelopeIntegral :
      ∫ a, envelope a ∂P =
        coeffResponse *
          ((σ * lowerCoeff) * ∫ a, lowerSup a * childAvg a ∂P +
            (σ⁻¹ * upperCoeff) * ∫ a, upperSup a * childAvg a ∂P) := by
    dsimp [envelope]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_add
      (hLowerProdInt.const_mul (σ * lowerCoeff))
      (hUpperProdInt.const_mul (σ⁻¹ * upperCoeff))]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hEnvelopeBound :
      ∫ a, envelope a ∂P ≤
        coeffResponse *
          (σ * lowerCoeff *
              ((D.card : ℝ) ^ (1 / (hP4.xi : ℝ)) *
                Homogenization.Book.Ch04.lambdaInvMomentAtScale
                  P 0 hP4.sLower hP4.xi *
                responseMoment) +
            σ⁻¹ * upperCoeff *
              ((D.card : ℝ) ^ (1 / (hP4.xi : ℝ)) *
                Homogenization.Book.Ch04.LambdaMomentAtScale
                  P 0 hP4.sUpper hP4.xi *
                responseMoment)) := by
    have hinside :
        (σ * lowerCoeff) * ∫ a, lowerSup a * childAvg a ∂P +
            (σ⁻¹ * upperCoeff) * ∫ a, upperSup a * childAvg a ∂P
          ≤
        σ * lowerCoeff *
              ((D.card : ℝ) ^ (1 / (hP4.xi : ℝ)) *
                Homogenization.Book.Ch04.lambdaInvMomentAtScale
                  P 0 hP4.sLower hP4.xi *
                responseMoment) +
          σ⁻¹ * upperCoeff *
              ((D.card : ℝ) ^ (1 / (hP4.xi : ℝ)) *
                Homogenization.Book.Ch04.LambdaMomentAtScale
                  P 0 hP4.sUpper hP4.xi *
                responseMoment) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hLowerHolder
          (mul_nonneg hσ_nonneg hlowerCoeff_nonneg))
        (mul_le_mul_of_nonneg_left hUpperHolder
          (mul_nonneg hσ_inv_nonneg hupperCoeff_nonneg))
    calc
      ∫ a, envelope a ∂P =
          coeffResponse *
            ((σ * lowerCoeff) * ∫ a, lowerSup a * childAvg a ∂P +
              (σ⁻¹ * upperCoeff) * ∫ a, upperSup a * childAvg a ∂P) :=
          hEnvelopeIntegral
      _ ≤ coeffResponse *
          (σ * lowerCoeff *
              ((D.card : ℝ) ^ (1 / (hP4.xi : ℝ)) *
                Homogenization.Book.Ch04.lambdaInvMomentAtScale
                  P 0 hP4.sLower hP4.xi *
                responseMoment) +
            σ⁻¹ * upperCoeff *
              ((D.card : ℝ) ^ (1 / (hP4.xi : ℝ)) *
                Homogenization.Book.Ch04.LambdaMomentAtScale
                  P 0 hP4.sUpper hP4.xi *
                responseMoment)) :=
          mul_le_mul_of_nonneg_left hinside hcoeffResponse_nonneg
  have hPoint :
      (fun a : Homogenization.CoeffField d =>
        (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a)
        ≤ᵐ[P] envelope := by
    filter_upwards with a
    have hlowerPoint :
        lowerSmall a ≤ lowerCoeff * lowerSup a := by
      simpa [lowerSmall, lowerCoeff, lowerSup, D, Q, s'] using
        Homogenization.Book.Ch05.Section52.lowerSmallTailTerm_le_raw_unitDescendantSup
          (d := d) m (s := hP4.sLower) (r := s')
          hP4.sLower_pos hs'_gt hs'_lt_one a
    have hupperPoint :
        upperSmall a ≤ upperCoeff * upperSup a := by
      simpa [upperSmall, upperCoeff, upperSup, D, Q, t'] using
        Homogenization.Book.Ch05.Section52.upperSmallTailTerm_le_raw_unitDescendantSup
          (d := d) m (s := hP4.sUpper) (r := t')
          hP4.sUpper_pos ht'_gt ht'_lt_one a
    have hweight :
        σ * lowerSmall a + σ⁻¹ * upperSmall a ≤
          σ * (lowerCoeff * lowerSup a) +
            σ⁻¹ * (upperCoeff * upperSup a) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hlowerPoint hσ_nonneg)
        (mul_le_mul_of_nonneg_left hupperPoint hσ_inv_nonneg)
    calc
      (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a
          = coeffResponse *
              ((σ * lowerSmall a + σ⁻¹ * upperSmall a) * childAvg a) := by
            dsimp [response, coeffResponse]
            ring
      _ ≤ coeffResponse *
            ((σ * (lowerCoeff * lowerSup a) +
                σ⁻¹ * (upperCoeff * upperSup a)) * childAvg a) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hweight (hchild_nonneg_all a))
            hcoeffResponse_nonneg
      _ = envelope a := by
          dsimp [envelope]
          ring
  have hSmall_nonneg :
      0 ≤ᵐ[P] (fun a : Homogenization.CoeffField d =>
        (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a) := by
    filter_upwards with a
    have hlowerSmall_nonneg : 0 ≤ lowerSmall a := by
      dsimp [lowerSmall]
      exact div_nonneg (sq_nonneg _)
        (Homogenization.Book.Ch05.Section52.section52SmallTailWeight_nonneg
          hs'_pos.le m)
    have hupperSmall_nonneg : 0 ≤ upperSmall a := by
      dsimp [upperSmall]
      exact div_nonneg (sq_nonneg _)
        (Homogenization.Book.Ch05.Section52.section52SmallTailWeight_nonneg
          ht'_pos.le m)
    have hresponse_nonneg : 0 ≤ response a := by
      dsimp [response]
      exact mul_nonneg (sq_nonneg _) (hchild_nonneg_all a)
    exact mul_nonneg
      (add_nonneg
        (mul_nonneg hσ_nonneg hlowerSmall_nonneg)
        (mul_nonneg hσ_inv_nonneg hupperSmall_nonneg))
      hresponse_nonneg
  have hSmallIntegral_le :
      ∫ a, (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a ∂P
        ≤ ∫ a, envelope a ∂P :=
    MeasureTheory.integral_mono_of_nonneg hSmall_nonneg hEnvelopeInt hPoint
  have hLowerSmallAE : AEMeasurable lowerSmall P := by
    have htail :=
      aemeasurable_lowerSmallSqrtTailCoeffField hP m hs'_pos
    have hsq : AEMeasurable
        (fun a : Homogenization.CoeffField d =>
          Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
              (d := d) m s' a ^ 2) P := by
      simpa [pow_two] using (htail.mul htail)
    simpa [lowerSmall, div_eq_mul_inv] using
      hsq.mul_const
        (Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m)⁻¹
  have hUpperSmallAE : AEMeasurable upperSmall P := by
    have htail :=
      aemeasurable_upperSmallSqrtTailCoeffField hP m ht'_pos
    have hsq : AEMeasurable
        (fun a : Homogenization.CoeffField d =>
          Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
              (d := d) m t' a ^ 2) P := by
      simpa [pow_two] using (htail.mul htail)
    simpa [upperSmall, div_eq_mul_inv] using
      hsq.mul_const
        (Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m)⁻¹
  have hChildAE : AEMeasurable childAvg P :=
    hChildMem.aestronglyMeasurable.aemeasurable
  have hResponseAE : AEMeasurable response P := by
    simpa [response, coeffResponse] using hChildAE.const_mul coeffResponse
  have hSmallAE :
      AEMeasurable
        (fun a : Homogenization.CoeffField d =>
          (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a) P := by
    exact
      ((hLowerSmallAE.const_mul σ).add
        (hUpperSmallAE.const_mul σ⁻¹)).mul hResponseAE
  have hSmallInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d =>
          (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a) P := by
    refine MeasureTheory.Integrable.mono' hEnvelopeInt
      hSmallAE.aestronglyMeasurable ?_
    filter_upwards [hPoint, hSmall_nonneg] with a hle hnonneg
    change |(σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a| ≤ envelope a
    rw [abs_of_nonneg hnonneg]
    exact hle
  exact ⟨hSmallInt, hSmallIntegral_le.trans hEnvelopeBound⟩

/--
Source labels `p.HC.CR`, `e.weaknorms.moreproto`, `e.J.moment.bound`, and
`e.P.bound`: terminal-prefactor version of
`integrable_section52SmallTail_childResponseAverage_special_and_integral_le_responseMoment`.
The analytic estimate is unchanged; the response-moment factor is enlarged by
the corrected terminal prefactor `P_{k,m}`.
-/
theorem integrable_section52SmallTail_childResponseAverage_special_and_integral_le_terminalPAtScales_mul_responseMoment
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
    let D := Homogenization.descendantsAtScale Q 0
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let childAvg := fun a : Homogenization.CoeffField d =>
      Homogenization.descendantsAverage Q (m - k)
        (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
    let response := fun a : Homogenization.CoeffField d =>
      (5 * β⁻¹) ^ 2 * childAvg a
    let lowerSmall := fun a : Homogenization.CoeffField d =>
      Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
          (d := d) m s' a ^ 2 /
        Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
    let upperSmall := fun a : Homogenization.CoeffField d =>
      Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
          (d := d) m t' a ^ 2 /
        Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
    let lowerCoeff :=
      (25 * hP4.sLower⁻¹ * (s' - hP4.sLower)⁻¹ *
            Real.rpow (3 : ℝ) (-s' * (m : ℝ))) ^ 2 /
          Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
    let upperCoeff :=
      (25 * hP4.sUpper⁻¹ * (t' - hP4.sUpper)⁻¹ *
            Real.rpow (3 : ℝ) (-t' * (m : ℝ))) ^ 2 /
          Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
    let lowerMomentCoeff :=
      (D.card : ℝ) ^ (1 / (hP4.xi : ℝ)) *
        Homogenization.Book.Ch04.lambdaInvMomentAtScale
          P 0 hP4.sLower hP4.xi
    let upperMomentCoeff :=
      (D.card : ℝ) ^ (1 / (hP4.xi : ℝ)) *
        Homogenization.Book.Ch04.LambdaMomentAtScale
          P 0 hP4.sUpper hP4.xi
    let smallCoeff :=
      (5 * β⁻¹) ^ 2 *
        (σ * lowerCoeff * lowerMomentCoeff +
          σ⁻¹ * upperCoeff * upperMomentCoeff)
    MeasureTheory.Integrable
      (fun a : Homogenization.CoeffField d =>
        (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a) P ∧
    ∫ a, (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a ∂P ≤
      smallCoeff *
        (terminalPAtScales hP hStruct k m *
          coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e) := by
  classical
  obtain ⟨hSmallInt, hSmallBound⟩ :=
    integrable_section52SmallTail_childResponseAverage_special_and_integral_le_responseMoment
      hP hstat hStruct hP4 hkm e
  dsimp only at hSmallInt hSmallBound ⊢
  refine ⟨hSmallInt, ?_⟩
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let D : Finset (Homogenization.TriadicCube d) :=
    Homogenization.descendantsAtScale Q 0
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let childAvg : Homogenization.CoeffField d → ℝ := fun a =>
    Homogenization.descendantsAverage Q (m - k)
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
  let response : Homogenization.CoeffField d → ℝ := fun a =>
    (5 * β⁻¹) ^ 2 * childAvg a
  let lowerSmall : Homogenization.CoeffField d → ℝ := fun a =>
    Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
        (d := d) m s' a ^ 2 /
      Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
  let upperSmall : Homogenization.CoeffField d → ℝ := fun a =>
    Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
        (d := d) m t' a ^ 2 /
      Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
  let lowerCoeff : ℝ :=
    (25 * hP4.sLower⁻¹ * (s' - hP4.sLower)⁻¹ *
          Real.rpow (3 : ℝ) (-s' * (m : ℝ))) ^ 2 /
        Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
  let upperCoeff : ℝ :=
    (25 * hP4.sUpper⁻¹ * (t' - hP4.sUpper)⁻¹ *
          Real.rpow (3 : ℝ) (-t' * (m : ℝ))) ^ 2 /
        Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
  let lowerMomentCoeff : ℝ :=
    (D.card : ℝ) ^ (1 / (hP4.xi : ℝ)) *
      Homogenization.Book.Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi
  let upperMomentCoeff : ℝ :=
    (D.card : ℝ) ^ (1 / (hP4.xi : ℝ)) *
      Homogenization.Book.Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi
  let smallCoeff : ℝ :=
    (5 * β⁻¹) ^ 2 *
      (σ * lowerCoeff * lowerMomentCoeff +
        σ⁻¹ * upperCoeff * upperMomentCoeff)
  let responseMoment : ℝ :=
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  let P_km : ℝ := terminalPAtScales hP hStruct k m
  let smallIntegral : ℝ :=
    ∫ a, (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a ∂P
  have hraw :
      smallIntegral ≤ smallCoeff * responseMoment := by
    calc
      smallIntegral ≤
          (5 * β⁻¹) ^ 2 *
            (σ * lowerCoeff * (lowerMomentCoeff * responseMoment) +
              σ⁻¹ * upperCoeff * (upperMomentCoeff * responseMoment)) := by
            simpa [smallIntegral, β, s', t', Q, D, p_e, q_e, σ, childAvg,
              response, lowerSmall, upperSmall, lowerCoeff, upperCoeff,
              lowerMomentCoeff, upperMomentCoeff, responseMoment] using
              hSmallBound
      _ = smallCoeff * responseMoment := by
          dsimp [smallCoeff]
          ring
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
  have hlowerCoeff_nonneg : 0 ≤ lowerCoeff := by
    dsimp [lowerCoeff]
    exact div_nonneg (sq_nonneg _)
      (Homogenization.Book.Ch05.Section52.section52SmallTailWeight_nonneg
        hs'_pos.le m)
  have hupperCoeff_nonneg : 0 ≤ upperCoeff := by
    dsimp [upperCoeff]
    exact div_nonneg (sq_nonneg _)
      (Homogenization.Book.Ch05.Section52.section52SmallTailWeight_nonneg
        ht'_pos.le m)
  have hlowerMomentCoeff_nonneg : 0 ≤ lowerMomentCoeff := by
    dsimp [lowerMomentCoeff]
    exact mul_nonneg
      (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le D.card) _)
      (Homogenization.Book.Ch04.lambdaInvMomentAtScale_nonneg
        P 0 hP4.xi hP4.sLower_pos)
  have hupperMomentCoeff_nonneg : 0 ≤ upperMomentCoeff := by
    dsimp [upperMomentCoeff]
    exact mul_nonneg
      (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le D.card) _)
      (Homogenization.Book.Ch04.LambdaMomentAtScale_nonneg
        P 0 hP4.xi hP4.sUpper_pos)
  have hsmallCoeff_nonneg : 0 ≤ smallCoeff := by
    dsimp [smallCoeff]
    exact mul_nonneg (sq_nonneg _)
      (add_nonneg
        (mul_nonneg (mul_nonneg hσ_nonneg hlowerCoeff_nonneg)
          hlowerMomentCoeff_nonneg)
        (mul_nonneg (mul_nonneg hσ_inv_nonneg hupperCoeff_nonneg)
          hupperMomentCoeff_nonneg))
  have hresponse_nonneg : 0 ≤ responseMoment := by
    simpa [responseMoment] using
      coarseFluctuationResponseMomentAtScale_nonneg hP hStruct hP4 k m e
  have hterminal_one : 1 ≤ P_km := by
    have hF_nonneg : 0 ≤ contrastExcessAtScale hP hStruct m :=
      contrastExcessAtScale_nonneg_of_P4 hP hStruct hP4 m
    have hsqrt_one :
        1 ≤ Real.sqrt (1 + contrastExcessAtScale hP hStruct m) :=
      Real.one_le_sqrt.mpr (by linarith)
    exact hsqrt_one.trans
      (by
        simpa [P_km] using
          sqrt_one_add_contrastExcessAtScale_le_terminalPAtScales_of_P4
            hP hStruct hP4 hkm.le)
  have hresponse_terminal :
      responseMoment ≤ P_km * responseMoment := by
    calc
      responseMoment = 1 * responseMoment := by ring
      _ ≤ P_km * responseMoment :=
          mul_le_mul_of_nonneg_right hterminal_one hresponse_nonneg
  have hfinal : smallIntegral ≤ smallCoeff * (P_km * responseMoment) :=
    hraw.trans
      (mul_le_mul_of_nonneg_left hresponse_terminal hsmallCoeff_nonneg)
  simpa [smallIntegral, smallCoeff, P_km, responseMoment, β, s', t', Q, D,
    p_e, q_e, σ, childAvg, response, lowerSmall, upperSmall, lowerCoeff,
    upperCoeff, lowerMomentCoeff, upperMomentCoeff] using hfinal

end

end Homogenization.HighContrast.EntryScale
