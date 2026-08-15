import Homogenization.HighContrast.EntryScale.ResponseFluctuation
import Homogenization.HighContrast.EntryScale.ResponseMoment
import Homogenization.HighContrast.EntryScale.TerminalLowerEdge
import Homogenization.HighContrast.EntryScale.BadEventResponse
import Homogenization.HighContrast.EntryScale.RawHighContrastWeakNorm.P5

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization
open scoped Matrix.Norms.Elementwise

namespace Homogenization.HighContrast.EntryScale

noncomputable section

/--
Source labels `p.HC.CR`, `e.weaknorms.moreproto`, and `e.J.moment.bound`:
the Section 5.2 low-tail child-response term is bounded by a finite sum of
large-scale positive-excess root coefficients times the lower-edge response
moment.  The exact `lowSum` shape from the terminal lower-edge assembly is
used, including the manuscript response factor
`(5 * beta^{-1})^2 * childAvg`.

The terminal baseline in the slots is first compared with the scale-zero
large-scale positive-excess baseline, producing the explicit baseline-gap
remainder.  The stochastic part is then paid by Holder against the same
`coarseFluctuationResponseMomentAtScale` as the small-tail estimate.
-/
theorem integrable_section52LowTail_childResponseAverage_special_and_integral_le_responseMoment
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hstat : Homogenization.Book.Ch04.RestrictionStationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Homogenization.Vec d) :
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
    let childAvg := fun a : Homogenization.RegCoeffField d =>
      Homogenization.descendantsAverage Q (m - k)
        (fun R => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
    let response := fun a : Homogenization.RegCoeffField d =>
      (5 * β⁻¹) ^ 2 * childAvg a
    let lowerSlot : Homogenization.RegCoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
      let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa only [originCube, Q] using
            Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
      let lowerExcess : Homogenization.TriadicCube d → ℝ := fun R =>
        max
          (Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix
                (Homogenization.cubeSet R) a).lowerRight -
            (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
          0
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
        (σ * parents.sup' hparents lowerExcess) * response a
    let upperSlot : Homogenization.RegCoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
      let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa only [originCube, Q] using
            Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
      let upperExcess : Homogenization.TriadicCube d → ℝ := fun R =>
        max
          (Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix
                (Homogenization.cubeSet R) a).upperLeft -
            hP.barSigmaAtScale hStruct (m : ℤ))
          0
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
        (σ⁻¹ * parents.sup' hparents upperExcess) * response a
    let lowSum := fun a : Homogenization.RegCoeffField d =>
      S.attach.sum fun n =>
        if k ≤ Int.toNat n.1 then 0 else lowerSlot a n + upperSlot a n
    let dimCoeff : ℝ := (Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)
    let lowerGap : ℝ :=
      (hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ -
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹
    let upperGap : ℝ :=
      hP.barSigmaAtScale hStruct (0 : ℤ) -
        hP.barSigmaAtScale hStruct (m : ℤ)
    let lowerRootCoeff : {n : ℤ // n ∈ S} → ℝ := fun n =>
      dimCoeff *
        Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff
          d hP4.xi s' m n.1 *
        Homogenization.Book.Ch04.lambdaInvMomentAtScale
          P 0 hP4.sLower hP4.xi
    let upperRootCoeff : {n : ℤ // n ∈ S} → ℝ := fun n =>
      dimCoeff *
        Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff
          d hP4.xi t' m n.1 *
        Homogenization.Book.Ch04.LambdaMomentAtScale
          P 0 hP4.sUpper hP4.xi
    let gapCoeff : {n : ℤ // n ∈ S} → ℝ := fun n =>
      σ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
          lowerGap +
        σ⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
          upperGap
    let lowCoeff : ℝ :=
      S.attach.sum fun n =>
        if k ≤ Int.toNat n.1 then 0 else
          σ * lowerRootCoeff n + σ⁻¹ * upperRootCoeff n + gapCoeff n
    MeasureTheory.Integrable lowSum P ∧
    ∫ a, lowSum a ∂P ≤
      (5 * β⁻¹) ^ 2 * lowCoeff *
        coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
  classical
  dsimp only
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let ζ := section53CoarseFluctuationZeta hP4
  let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let childAvg : Homogenization.RegCoeffField d → ℝ := fun a =>
    Homogenization.descendantsAverage Q (m - k)
      (fun R => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
  let response : Homogenization.RegCoeffField d → ℝ := fun a =>
    (5 * β⁻¹) ^ 2 * childAvg a
  let coeffResponse : ℝ := (5 * β⁻¹) ^ 2
  let responseMoment :=
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  let lowerGap : ℝ :=
    (hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ -
      (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹
  let upperGap : ℝ :=
    hP.barSigmaAtScale hStruct (0 : ℤ) -
      hP.barSigmaAtScale hStruct (m : ℤ)
  let dimCoeff : ℝ := (Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)
  let lowerRootCoeff : {n : ℤ // n ∈ S} → ℝ := fun n =>
    dimCoeff *
      Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff
        d hP4.xi s' m n.1 *
      Homogenization.Book.Ch04.lambdaInvMomentAtScale
        P 0 hP4.sLower hP4.xi
  let upperRootCoeff : {n : ℤ // n ∈ S} → ℝ := fun n =>
    dimCoeff *
      Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff
        d hP4.xi t' m n.1 *
      Homogenization.Book.Ch04.LambdaMomentAtScale
        P 0 hP4.sUpper hP4.xi
  let gapCoeff : {n : ℤ // n ∈ S} → ℝ := fun n =>
    σ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
        lowerGap +
      σ⁻¹ * Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
        upperGap
  let coeffTerm : {n : ℤ // n ∈ S} → ℝ := fun n =>
    σ * lowerRootCoeff n + σ⁻¹ * upperRootCoeff n + gapCoeff n
  let lowCoeff : ℝ :=
    S.attach.sum fun n =>
      if k ≤ Int.toNat n.1 then 0 else coeffTerm n
  let lowerSlot : Homogenization.RegCoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa only [originCube, Q] using
          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
    let lowerExcess : Homogenization.TriadicCube d → ℝ := fun R =>
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix
              (Homogenization.cubeSet R) a).lowerRight -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
      (σ * parents.sup' hparents lowerExcess) * response a
  let upperSlot : Homogenization.RegCoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa only [originCube, Q] using
          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
    let upperExcess : Homogenization.TriadicCube d → ℝ := fun R =>
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix
              (Homogenization.cubeSet R) a).upperLeft -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
      (σ⁻¹ * parents.sup' hparents upperExcess) * response a
  let lowSum : Homogenization.RegCoeffField d → ℝ := fun a =>
    S.attach.sum fun n =>
      if k ≤ Int.toNat n.1 then 0 else lowerSlot a n + upperSlot a n
  let lowerZero : Homogenization.RegCoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa only [originCube, Q] using
          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
      parents.sup' hparents (fun R =>
        max
          (Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix
                (Homogenization.cubeSet R) a).lowerRight -
            Homogenization.Book.Ch02.matrixNorm
              ((hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ •
                (1 : Homogenization.Mat d)))
          0)
  let upperZero : Homogenization.RegCoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa only [originCube, Q] using
          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
      parents.sup' hparents (fun R =>
        max
          (Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix
                (Homogenization.cubeSet R) a).upperLeft -
            Homogenization.Book.Ch02.matrixNorm
              (hP.barSigmaAtScale hStruct (0 : ℤ) •
                (1 : Homogenization.Mat d)))
          0)
  let envelopeTerm : {n : ℤ // n ∈ S} → Homogenization.RegCoeffField d → ℝ := fun n a =>
    if k ≤ Int.toNat n.1 then 0 else
      coeffResponse *
        ((σ * lowerZero a n + σ⁻¹ * upperZero a n + gapCoeff n) *
          childAvg a)
  let envelope : Homogenization.RegCoeffField d → ℝ := fun a =>
    S.attach.sum fun n => envelopeTerm n a
  have hβ_pos : 0 < β := by
    simpa only using section53CoarseFluctuationBeta_pos hP4
  have hs'_pos : 0 < s' := by
    dsimp [s', β]
    linarith only [hP4.sLower_pos, hβ_pos]
  have ht'_pos : 0 < t' := by
    dsimp [t', β]
    linarith only [hP4.sUpper_pos, hβ_pos]
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, Homogenization.Book.Ch05.sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hcoeffResponse_nonneg : 0 ≤ coeffResponse := by
    dsimp [coeffResponse]
    exact sq_nonneg _
  have hξ_one : 1 ≤ hP4.xi :=
    le_trans (by norm_num : 1 ≤ 2) hP4.two_le_xi
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hkm.le
  have hζ_pos : 0 < ζ := by
    simpa only using section53CoarseFluctuationZeta_pos hP4
  have hchain :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.scalarChain_of_P4
      hP hStruct hP4 (Nat.zero_le m)
  have hlowerGap_nonneg : 0 ≤ lowerGap := by
    dsimp [lowerGap]
    exact sub_nonneg.mpr hchain.2.1
  have hupperGap_nonneg : 0 ≤ upperGap := by
    dsimp [upperGap]
    exact sub_nonneg.mpr hchain.2.2
  have hbar0_pos :
      0 < hP.barSigmaAtScale hStruct (0 : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 0
  have hbar0_nonneg : 0 ≤ hP.barSigmaAtScale hStruct (0 : ℤ) :=
    hbar0_pos.le
  have hstar0_inv_pos :
      0 < (hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_inv_pos_of_P4
      hP hStruct hP4 0
  have hstar0_inv_nonneg :
      0 ≤ (hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ :=
    hstar0_inv_pos.le
  have hbar0_matrix :
      Homogenization.Book.Ch02.matrixNorm
          (hP.barSigmaAtScale hStruct (0 : ℤ) • (1 : Homogenization.Mat d)) =
        hP.barSigmaAtScale hStruct (0 : ℤ) :=
    Homogenization.Book.Ch05.Section52.matrixNorm_smul_one_eq_of_nonneg
      hbar0_nonneg
  have hstar0_matrix :
      Homogenization.Book.Ch02.matrixNorm
          ((hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ •
            (1 : Homogenization.Mat d)) =
        (hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ :=
    Homogenization.Book.Ch05.Section52.matrixNorm_smul_one_eq_of_nonneg
      hstar0_inv_nonneg
  have hchild_nonneg_all : ∀ a, 0 ≤ childAvg a := by
    intro a
    dsimp [childAvg]
    exact Homogenization.descendantsAverage_nonneg Q (m - k)
      (fun R => Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e a)
      (fun R _hR =>
        Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet_nonneg R p_e q_e a)
  have hchild_nonneg : 0 ≤ᵐ[P] childAvg :=
    Filter.Eventually.of_forall hchild_nonneg_all
  have hdesc :=
    integrable_terminalDescendantsAverage_restrictionResponseJObservableCubeSet_and_integral_le
      hP hstat hStruct hP4 hkm.le e
  have hChildInt : MeasureTheory.Integrable childAvg P := by
    simpa only [childAvg, Q, p_e, q_e] using hdesc.1
  have hChildIntegral_le :
      ∫ a, childAvg a ∂P ≤ responseMoment := by
    simpa only [childAvg, Q, p_e, q_e, responseMoment] using hdesc.2
  have hChildMem :
      MeasureTheory.MemLp childAvg
        (ENNReal.ofReal (section53CoarseFluctuationZeta hP4)) P := by
    simpa only [Book.Ch05.specialPAtScale_eq, Book.Ch05.sigmaHatAtScale_eq, one_div, Real.rpow_eq_pow, Book.Ch05.specialQAtScale_eq, Book.Ch04.restrictionResponseJObservableCubeSet_apply, Int.toNat_sub', Int.toNat_natCast] using
      memLp_zeta_descendantsAverage_restrictionResponseJObservableCubeSet_originCube_from_P4_of_stationary
        hP hstat hStruct hP4 hk_nonneg hkm_int p_e q_e
  have hChildMomentRoot_le :
      (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) ≤ responseMoment := by
    simpa only [childAvg, Q, ζ, p_e, q_e, responseMoment] using
      childResponseAverage_zetaRoot_le_coarseFluctuationResponseMomentAtScale_of_stationary
        hP hstat hStruct hP4 hkm e
  have hChildMomentRoot_nonneg :
      0 ≤ (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) := by
    exact Real.rpow_nonneg
      (MeasureTheory.integral_nonneg fun a =>
        Real.rpow_nonneg (hchild_nonneg_all a) _) _
  have hHolderReal :
      (hP4.xi : ℝ).HolderConjugate (section53CoarseFluctuationZeta hP4) :=
    holderConjugate_xi_section53CoarseFluctuationZeta hP4
  letI : ENNReal.HolderTriple
      (ENNReal.ofReal (hP4.xi : ℝ))
      (ENNReal.ofReal (section53CoarseFluctuationZeta hP4)) 1 := by
    simpa only [ENNReal.ofReal_natCast, ENNReal.ofReal_one] using Real.HolderTriple.ennrealOfReal hHolderReal
  have hLowerZero_nonneg_all :
      ∀ n : {n : ℤ // n ∈ S}, ∀ a, 0 ≤ lowerZero a n := by
    intro n a
    simpa only using
      Homogenization.Book.Ch05.Section52.lowerLargeScalePositiveExcess_nonneg_source
        (d := d) (P := P) hP hStruct (r := s') hs'_pos.le n.2 a
  have hUpperZero_nonneg_all :
      ∀ n : {n : ℤ // n ∈ S}, ∀ a, 0 ≤ upperZero a n := by
    intro n a
    simpa only using
      Homogenization.Book.Ch05.Section52.upperLargeScalePositiveExcess_nonneg_source
        (d := d) (P := P) hP hStruct (r := t') ht'_pos.le n.2 a
  have hLowerZeroMem :
      ∀ n : {n : ℤ // n ∈ S},
        MeasureTheory.MemLp (fun a : Homogenization.RegCoeffField d => lowerZero a n)
          (ENNReal.ofReal (hP4.xi : ℝ)) P := by
    intro n
    have hAE : AEMeasurable
        (fun a : Homogenization.RegCoeffField d => lowerZero a n) P := by
      simpa only using
        Homogenization.Book.Ch05.Section52.lowerLargeScalePositiveExcess_aemeasurable_source
          (d := d) (P := P) hP hStruct (r := s') n.2
    have hAbsInt :
        MeasureTheory.Integrable
          (fun a : Homogenization.RegCoeffField d => |lowerZero a n| ^ hP4.xi) P := by
      simpa only [lowerZero, Q, Real.norm_eq_abs] using
        Homogenization.Book.Ch05.Section52.lowerLargeScalePositiveExcess_integrable_abs_pow_source
          (d := d) (P := P) hP hStruct
          (sSource := hP4.sLower) (r := s') (ξ := hP4.xi)
          hP4.sLower_pos hξ_one hP4.two_le_xi
          hP4.lower_inv_moment_integrable n.2
    have hPowInt :
        MeasureTheory.Integrable
          (fun a : Homogenization.RegCoeffField d => lowerZero a n ^ hP4.xi) P := by
      refine hAbsInt.congr ?_
      filter_upwards with a
      rw [abs_of_nonneg (hLowerZero_nonneg_all n a)]
    exact memLp_of_integrable_nonneg_nat_pow hP4.xi_pos hAE
      (Filter.Eventually.of_forall (hLowerZero_nonneg_all n)) hPowInt
  have hUpperZeroMem :
      ∀ n : {n : ℤ // n ∈ S},
        MeasureTheory.MemLp (fun a : Homogenization.RegCoeffField d => upperZero a n)
          (ENNReal.ofReal (hP4.xi : ℝ)) P := by
    intro n
    have hAE : AEMeasurable
        (fun a : Homogenization.RegCoeffField d => upperZero a n) P := by
      simpa only using
        Homogenization.Book.Ch05.Section52.upperLargeScalePositiveExcess_aemeasurable_source
          (d := d) (P := P) hP hStruct (r := t') n.2
    have hAbsInt :
        MeasureTheory.Integrable
          (fun a : Homogenization.RegCoeffField d => |upperZero a n| ^ hP4.xi) P := by
      simpa only [upperZero, Q, Real.norm_eq_abs] using
        Homogenization.Book.Ch05.Section52.upperLargeScalePositiveExcess_integrable_abs_pow_source
          (d := d) (P := P) hP hStruct
          (sSource := hP4.sUpper) (r := t') (ξ := hP4.xi)
          hP4.sUpper_pos hξ_one hP4.two_le_xi
          hP4.upper_moment_integrable n.2
    have hPowInt :
        MeasureTheory.Integrable
          (fun a : Homogenization.RegCoeffField d => upperZero a n ^ hP4.xi) P := by
      refine hAbsInt.congr ?_
      filter_upwards with a
      rw [abs_of_nonneg (hUpperZero_nonneg_all n a)]
    exact memLp_of_integrable_nonneg_nat_pow hP4.xi_pos hAE
      (Filter.Eventually.of_forall (hUpperZero_nonneg_all n)) hPowInt
  have hLowerProdInt :
      ∀ n : {n : ℤ // n ∈ S},
        MeasureTheory.Integrable
          (fun a : Homogenization.RegCoeffField d => lowerZero a n * childAvg a) P := by
    intro n
    exact (hLowerZeroMem n).integrable_mul hChildMem
  have hUpperProdInt :
      ∀ n : {n : ℤ // n ∈ S},
        MeasureTheory.Integrable
          (fun a : Homogenization.RegCoeffField d => upperZero a n * childAvg a) P := by
    intro n
    exact (hUpperZeroMem n).integrable_mul hChildMem
  have hLowerRoot_le :
      ∀ n : {n : ℤ // n ∈ S},
        Homogenization.Book.Ch04.annealedMomentRoot P hP4.xi
            (fun a : Homogenization.RegCoeffField d => lowerZero a n) ≤
          lowerRootCoeff n := by
    intro n
    simpa only [lowerZero, lowerRootCoeff, dimCoeff, Q] using
      Homogenization.Book.Ch05.Section52.lowerLargeScalePositiveExcessRoot_le_largeScaleRootCoeff_source
        (d := d) (P := P) hP hStruct
        (sSource := hP4.sLower) (r := s') (ξ := hP4.xi)
        hP4.sLower_pos hs'_pos.le hξ_one hP4.two_le_xi
        hP4.lower_inv_moment_integrable n.2
  have hUpperRoot_le :
      ∀ n : {n : ℤ // n ∈ S},
        Homogenization.Book.Ch04.annealedMomentRoot P hP4.xi
            (fun a : Homogenization.RegCoeffField d => upperZero a n) ≤
          upperRootCoeff n := by
    intro n
    simpa only [upperZero, upperRootCoeff, dimCoeff, Q] using
      Homogenization.Book.Ch05.Section52.upperLargeScalePositiveExcessRoot_le_largeScaleRootCoeff_source
        (d := d) (P := P) hP hStruct
        (sSource := hP4.sUpper) (r := t') (ξ := hP4.xi)
        hP4.sUpper_pos ht'_pos.le hξ_one hP4.two_le_xi
        hP4.upper_moment_integrable n.2
  have hLowerRootCoeff_nonneg :
      ∀ n : {n : ℤ // n ∈ S}, 0 ≤ lowerRootCoeff n := by
    intro n
    dsimp [lowerRootCoeff, dimCoeff]
    exact mul_nonneg
      (mul_nonneg
        (mul_self_nonneg _)
        (Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff_nonneg
          (d := d) (ξ := hP4.xi) (s := s') m n.1 hs'_pos.le))
      (Homogenization.Book.Ch04.lambdaInvMomentAtScale_nonneg
        P 0 hP4.xi hP4.sLower_pos)
  have hUpperRootCoeff_nonneg :
      ∀ n : {n : ℤ // n ∈ S}, 0 ≤ upperRootCoeff n := by
    intro n
    dsimp [upperRootCoeff, dimCoeff]
    exact mul_nonneg
      (mul_nonneg
        (mul_self_nonneg _)
        (Homogenization.Book.Ch05.Section52.section52LargeScaleRootCoeff_nonneg
          (d := d) (ξ := hP4.xi) (s := t') m n.1 ht'_pos.le))
      (Homogenization.Book.Ch04.LambdaMomentAtScale_nonneg
        P 0 hP4.xi hP4.sUpper_pos)
  have hGapCoeff_nonneg :
      ∀ n : {n : ℤ // n ∈ S}, 0 ≤ gapCoeff n := by
    intro n
    dsimp [gapCoeff]
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg hσ_nonneg
          (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight_nonneg
            m hs'_pos.le n.1))
        hlowerGap_nonneg)
      (mul_nonneg
        (mul_nonneg hσ_inv_nonneg
          (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight_nonneg
            m ht'_pos.le n.1))
        hupperGap_nonneg)
  have hLowerHolder :
      ∀ n : {n : ℤ // n ∈ S},
        ∫ a, lowerZero a n * childAvg a ∂P ≤ lowerRootCoeff n * responseMoment := by
    intro n
    have hHolderRaw :=
      MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
        (μ := P) hHolderReal
        (Filter.Eventually.of_forall (hLowerZero_nonneg_all n))
        hchild_nonneg (hLowerZeroMem n) hChildMem
    have hHolder :
        ∫ a, lowerZero a n * childAvg a ∂P ≤
          Homogenization.Book.Ch04.annealedMomentRoot P hP4.xi
              (fun a : Homogenization.RegCoeffField d => lowerZero a n) *
            (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) := by
      simpa only [Book.Ch04.annealedMomentRoot, one_div, Real.rpow_natCast] using hHolderRaw
    exact hHolder.trans
      (mul_le_mul (hLowerRoot_le n) hChildMomentRoot_le
        hChildMomentRoot_nonneg (hLowerRootCoeff_nonneg n))
  have hUpperHolder :
      ∀ n : {n : ℤ // n ∈ S},
        ∫ a, upperZero a n * childAvg a ∂P ≤ upperRootCoeff n * responseMoment := by
    intro n
    have hHolderRaw :=
      MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
        (μ := P) hHolderReal
        (Filter.Eventually.of_forall (hUpperZero_nonneg_all n))
        hchild_nonneg (hUpperZeroMem n) hChildMem
    have hHolder :
        ∫ a, upperZero a n * childAvg a ∂P ≤
          Homogenization.Book.Ch04.annealedMomentRoot P hP4.xi
              (fun a : Homogenization.RegCoeffField d => upperZero a n) *
            (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) := by
      simpa only [Book.Ch04.annealedMomentRoot, one_div, Real.rpow_natCast] using hHolderRaw
    exact hHolder.trans
      (mul_le_mul (hUpperRoot_le n) hChildMomentRoot_le
        hChildMomentRoot_nonneg (hUpperRootCoeff_nonneg n))
  have hEnvelopeTermInt :
      ∀ n ∈ S.attach, MeasureTheory.Integrable (envelopeTerm n) P := by
    intro n _hn
    by_cases hnlow : k ≤ Int.toNat n.1
    · simp only [hnlow, ↓reduceIte, enorm_zero, ne_eq, ENNReal.zero_ne_top, not_false_eq_true, MeasureTheory.integrable_const_enorm, envelopeTerm]
    · have hsumNested :
          MeasureTheory.Integrable
            ((fun a : Homogenization.RegCoeffField d =>
                σ * (lowerZero a n * childAvg a)) +
              ((fun a : Homogenization.RegCoeffField d =>
                  σ⁻¹ * (upperZero a n * childAvg a)) +
                fun a : Homogenization.RegCoeffField d =>
                  gapCoeff n * childAvg a)) P :=
        ((hLowerProdInt n).const_mul σ).add
          (((hUpperProdInt n).const_mul σ⁻¹).add
            (hChildInt.const_mul (gapCoeff n)))
      have hsum :
          MeasureTheory.Integrable
            (fun a : Homogenization.RegCoeffField d =>
              σ * (lowerZero a n * childAvg a) +
                σ⁻¹ * (upperZero a n * childAvg a) +
                gapCoeff n * childAvg a) P := by
        refine hsumNested.congr ?_
        filter_upwards with a
        ac_rfl
      have hscaled := hsum.const_mul coeffResponse
      refine hscaled.congr ?_
      filter_upwards with a
      simp only [hnlow, ↓reduceIte, mul_eq_mul_left_iff, envelopeTerm]
      ring_nf
      simp only [true_or]
  have hEnvelopeInt : MeasureTheory.Integrable envelope P := by
    simpa only using
      MeasureTheory.integrable_finset_sum S.attach hEnvelopeTermInt
  have hPoint : lowSum ≤ᵐ[P] envelope := by
    filter_upwards with a
    dsimp [lowSum, envelope]
    refine Finset.sum_le_sum ?_
    intro n _hn
    by_cases hnlow : k ≤ Int.toNat n.1
    · simp only [hnlow, ↓reduceIte, le_refl, envelopeTerm]
    · let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa only [originCube, Q] using
            Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
      let lowerTerminal : Homogenization.TriadicCube d → ℝ := fun R =>
        max
          (Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix
                (Homogenization.cubeSet R) a).lowerRight -
            (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
          0
      let upperTerminal : Homogenization.TriadicCube d → ℝ := fun R =>
        max
          (Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix
                (Homogenization.cubeSet R) a).upperLeft -
            hP.barSigmaAtScale hStruct (m : ℤ))
          0
      let lowerZeroRaw : Homogenization.TriadicCube d → ℝ := fun R =>
        max
          (Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix
                (Homogenization.cubeSet R) a).lowerRight -
            Homogenization.Book.Ch02.matrixNorm
              ((hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ •
                (1 : Homogenization.Mat d)))
          0
      let upperZeroRaw : Homogenization.TriadicCube d → ℝ := fun R =>
        max
          (Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix
                (Homogenization.cubeSet R) a).upperLeft -
            Homogenization.Book.Ch02.matrixNorm
              (hP.barSigmaAtScale hStruct (0 : ℤ) •
                (1 : Homogenization.Mat d)))
          0
      have hlower_sup :
          parents.sup' hparents lowerTerminal ≤
            parents.sup' hparents lowerZeroRaw + lowerGap := by
        rcases Finset.exists_mem_eq_sup' hparents lowerTerminal with
          ⟨R0, hR0, hR0_eq⟩
        have hR :
            lowerTerminal R0 ≤ lowerZeroRaw R0 + lowerGap := by
          simpa only [lowerTerminal, lowerZeroRaw, lowerGap, hstar0_matrix] using
            positivePart_sub_le_positivePart_sub_add_baseline_gap
              (x := Homogenization.Book.Ch02.matrixNorm
                (Homogenization.coarseBlockMatrix
                  (Homogenization.cubeSet R0) a).lowerRight)
              (baseLocal := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
              (baseGlobal := (hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹)
              hchain.2.1
        calc
          parents.sup' hparents lowerTerminal = lowerTerminal R0 := by
            simpa only [parents, lowerTerminal, hparents] using hR0_eq
          _ ≤ lowerZeroRaw R0 + lowerGap := hR
          _ ≤ parents.sup' hparents lowerZeroRaw + lowerGap :=
            by
              have hsup := Finset.le_sup' (s := parents) (f := lowerZeroRaw) hR0
              linarith only [hsup]
      have hupper_sup :
          parents.sup' hparents upperTerminal ≤
            parents.sup' hparents upperZeroRaw + upperGap := by
        rcases Finset.exists_mem_eq_sup' hparents upperTerminal with
          ⟨R0, hR0, hR0_eq⟩
        have hR :
            upperTerminal R0 ≤ upperZeroRaw R0 + upperGap := by
          simpa only [upperTerminal, upperZeroRaw, upperGap, hbar0_matrix] using
            positivePart_sub_le_positivePart_sub_add_baseline_gap
              (x := Homogenization.Book.Ch02.matrixNorm
                (Homogenization.coarseBlockMatrix
                  (Homogenization.cubeSet R0) a).upperLeft)
              (baseLocal := hP.barSigmaAtScale hStruct (m : ℤ))
              (baseGlobal := hP.barSigmaAtScale hStruct (0 : ℤ))
              hchain.2.2
        calc
          parents.sup' hparents upperTerminal = upperTerminal R0 := by
            simpa only [parents, upperTerminal, hparents] using hR0_eq
          _ ≤ upperZeroRaw R0 + upperGap := hR
          _ ≤ parents.sup' hparents upperZeroRaw + upperGap :=
            by
              have hsup := Finset.le_sup' (s := parents) (f := upperZeroRaw) hR0
              linarith only [hsup]
      have hlower_weighted :
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
              parents.sup' hparents lowerTerminal ≤
            lowerZero a n +
              Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
                lowerGap := by
        have hweight_nonneg :
            0 ≤ Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 :=
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight_nonneg
            m hs'_pos.le n.1
        calc
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
              parents.sup' hparents lowerTerminal
              ≤
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
              (parents.sup' hparents lowerZeroRaw + lowerGap) :=
              mul_le_mul_of_nonneg_left hlower_sup hweight_nonneg
          _ =
            lowerZero a n +
              Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
                lowerGap := by
              dsimp [lowerZero, lowerZeroRaw, parents, hparents]
              ring
      have hupper_weighted :
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
              parents.sup' hparents upperTerminal ≤
            upperZero a n +
              Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
                upperGap := by
        have hweight_nonneg :
            0 ≤ Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 :=
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight_nonneg
            m ht'_pos.le n.1
        calc
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
              parents.sup' hparents upperTerminal
              ≤
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
              (parents.sup' hparents upperZeroRaw + upperGap) :=
              mul_le_mul_of_nonneg_left hupper_sup hweight_nonneg
          _ =
            upperZero a n +
              Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
                upperGap := by
              dsimp [upperZero, upperZeroRaw, parents, hparents]
              ring
      have hlower_slot :
          lowerSlot a n ≤
            coeffResponse *
              (σ *
                (lowerZero a n +
                  Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
                    lowerGap) *
                childAvg a) := by
        calc
          lowerSlot a n =
            coeffResponse *
              (σ *
                (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
                  parents.sup' hparents lowerTerminal) *
                childAvg a) := by
                dsimp [lowerSlot, response, coeffResponse, lowerTerminal, parents, hparents]
                ring
          _ ≤
            coeffResponse *
              (σ *
                (lowerZero a n +
                  Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
                    lowerGap) *
                childAvg a) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hlower_weighted hσ_nonneg)
                    (hchild_nonneg_all a))
                  hcoeffResponse_nonneg
      have hupper_slot :
          upperSlot a n ≤
            coeffResponse *
              (σ⁻¹ *
                (upperZero a n +
                  Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
                    upperGap) *
                childAvg a) := by
        calc
          upperSlot a n =
            coeffResponse *
              (σ⁻¹ *
                (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
                  parents.sup' hparents upperTerminal) *
                childAvg a) := by
                dsimp [upperSlot, response, coeffResponse, upperTerminal, parents, hparents]
                ring
          _ ≤
            coeffResponse *
              (σ⁻¹ *
                (upperZero a n +
                  Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
                    upperGap) *
                childAvg a) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hupper_weighted hσ_inv_nonneg)
                    (hchild_nonneg_all a))
                  hcoeffResponse_nonneg
      calc
        (if k ≤ Int.toNat n.1 then 0 else lowerSlot a n + upperSlot a n)
            = lowerSlot a n + upperSlot a n := by simp only [hnlow, ↓reduceIte]
        _ ≤
          coeffResponse *
            (σ *
              (lowerZero a n +
                Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
                  lowerGap) *
              childAvg a) +
            coeffResponse *
            (σ⁻¹ *
              (upperZero a n +
                Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
                  upperGap) *
              childAvg a) :=
            add_le_add hlower_slot hupper_slot
        _ =
          envelopeTerm n a := by
            simp only [hnlow, ↓reduceIte, envelopeTerm, gapCoeff]
            ring
  have hresponse_nonneg_all : ∀ a, 0 ≤ response a := by
    intro a
    dsimp [response]
    exact mul_nonneg (sq_nonneg _) (hchild_nonneg_all a)
  have hLow_nonneg : 0 ≤ᵐ[P] lowSum := by
    filter_upwards with a
    dsimp [lowSum]
    refine Finset.sum_nonneg ?_
    intro n _hn
    by_cases hnlow : k ≤ Int.toNat n.1
    · simp only [hnlow, ↓reduceIte, le_refl]
    · let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa only [originCube, Q] using
            Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
      let lowerTerminal : Homogenization.TriadicCube d → ℝ := fun R =>
        max
          (Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix
                (Homogenization.cubeSet R) a).lowerRight -
            (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
          0
      let upperTerminal : Homogenization.TriadicCube d → ℝ := fun R =>
        max
          (Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix
                (Homogenization.cubeSet R) a).upperLeft -
            hP.barSigmaAtScale hStruct (m : ℤ))
          0
      have hlower_sup_nonneg :
          0 ≤ parents.sup' hparents lowerTerminal := by
        rcases hparents with ⟨R0, hR0⟩
        exact Finset.le_sup'_of_le lowerTerminal hR0 (le_max_right _ _)
      have hupper_sup_nonneg :
          0 ≤ parents.sup' hparents upperTerminal := by
        rcases hparents with ⟨R0, hR0⟩
        exact Finset.le_sup'_of_le upperTerminal hR0 (le_max_right _ _)
      have hlowerSlot_nonneg : 0 ≤ lowerSlot a n := by
        have hweight_nonneg :
            0 ≤ Homogenization.Book.Ch05.Section52.section52LargeScaleWeight
              s' m n.1 :=
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight_nonneg
            m hs'_pos.le n.1
        dsimp [lowerSlot, response, parents, hparents, lowerTerminal]
        exact mul_nonneg
          (mul_nonneg hweight_nonneg
            (mul_nonneg hσ_nonneg hlower_sup_nonneg))
          (hresponse_nonneg_all a)
      have hupperSlot_nonneg : 0 ≤ upperSlot a n := by
        have hweight_nonneg :
            0 ≤ Homogenization.Book.Ch05.Section52.section52LargeScaleWeight
              t' m n.1 :=
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight_nonneg
            m ht'_pos.le n.1
        dsimp [upperSlot, response, parents, hparents, upperTerminal]
        exact mul_nonneg
          (mul_nonneg hweight_nonneg
            (mul_nonneg hσ_inv_nonneg hupper_sup_nonneg))
          (hresponse_nonneg_all a)
      simpa only [hnlow, ↓reduceIte, ge_iff_le] using add_nonneg hlowerSlot_nonneg hupperSlot_nonneg
  have hResponseAE : AEMeasurable response P := by
    have hChildAE : AEMeasurable childAvg P :=
      hChildMem.aestronglyMeasurable.aemeasurable
    simpa only using hChildAE.const_mul coeffResponse
  have hbar_m_pos :
      0 < hP.barSigmaAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 m
  have hstar_m_inv_pos :
      0 < (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_inv_pos_of_P4
      hP hStruct hP4 m
  have hbar_m_matrix :
      Homogenization.Book.Ch02.matrixNorm
          (hP.barSigmaAtScale hStruct (m : ℤ) • (1 : Homogenization.Mat d)) =
        hP.barSigmaAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section52.matrixNorm_smul_one_eq_of_nonneg
      hbar_m_pos.le
  have hstar_m_matrix :
      Homogenization.Book.Ch02.matrixNorm
          ((hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ •
            (1 : Homogenization.Mat d)) =
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ :=
    Homogenization.Book.Ch05.Section52.matrixNorm_smul_one_eq_of_nonneg
      hstar_m_inv_pos.le
  have hLowerSlotAE :
      ∀ n : {n : ℤ // n ∈ S}, AEMeasurable (fun a => lowerSlot a n) P := by
    intro n
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa only [originCube, Q] using
          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
    let lowerTerminal : Homogenization.TriadicCube d →
        Homogenization.RegCoeffField d → ℝ := fun R a =>
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix
              (Homogenization.cubeSet R) a).lowerRight -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0
    have hsup_base :
        AEMeasurable
          (fun a : Homogenization.RegCoeffField d =>
            parents.sup' hparents
            (fun R =>
              max
                (Homogenization.Book.Ch02.matrixNorm
                    (Homogenization.coarseBlockMatrix
                      (Homogenization.cubeSet R) a).lowerRight -
                  Homogenization.Book.Ch02.matrixNorm
                    ((hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ •
                      (1 : Homogenization.Mat d)))
                0)) P :=
      Homogenization.Book.Ch04.RestrictionLawCarrier.aemeasurable_lowerRight_matrixNorm_positiveExcess_finsetSup
          hP hparents
          ((hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ •
            (1 : Homogenization.Mat d))
    have hsup :
        AEMeasurable
          (fun a : Homogenization.RegCoeffField d =>
            parents.sup' hparents (fun R => lowerTerminal R a)) P := by
      simpa only [hstar_m_matrix] using hsup_base
    have hslot :
        AEMeasurable
          (fun a : Homogenization.RegCoeffField d =>
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 *
              (σ * parents.sup' hparents (fun R => lowerTerminal R a)) * response a) P :=
      ((aemeasurable_const.mul (aemeasurable_const.mul hsup)).mul hResponseAE)
    simpa only using hslot
  have hUpperSlotAE :
      ∀ n : {n : ℤ // n ∈ S}, AEMeasurable (fun a => upperSlot a n) P := by
    intro n
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa only [originCube, Q] using
          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
    let upperTerminal : Homogenization.TriadicCube d →
        Homogenization.RegCoeffField d → ℝ := fun R a =>
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix
              (Homogenization.cubeSet R) a).upperLeft -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0
    have hsup_base :
        AEMeasurable
          (fun a : Homogenization.RegCoeffField d =>
            parents.sup' hparents
            (fun R =>
              max
                (Homogenization.Book.Ch02.matrixNorm
                    (Homogenization.coarseBlockMatrix
                      (Homogenization.cubeSet R) a).upperLeft -
                  Homogenization.Book.Ch02.matrixNorm
                    (hP.barSigmaAtScale hStruct (m : ℤ) •
                      (1 : Homogenization.Mat d)))
                0)) P :=
      Homogenization.Book.Ch04.RestrictionLawCarrier.aemeasurable_upperLeft_matrixNorm_positiveExcess_finsetSup
          hP hparents
          (hP.barSigmaAtScale hStruct (m : ℤ) •
            (1 : Homogenization.Mat d))
    have hsup :
        AEMeasurable
          (fun a : Homogenization.RegCoeffField d =>
            parents.sup' hparents (fun R => upperTerminal R a)) P := by
      simpa only [hbar_m_matrix] using hsup_base
    have hslot :
        AEMeasurable
          (fun a : Homogenization.RegCoeffField d =>
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1 *
              (σ⁻¹ * parents.sup' hparents (fun R => upperTerminal R a)) * response a) P :=
      ((aemeasurable_const.mul (aemeasurable_const.mul hsup)).mul hResponseAE)
    simpa only using hslot
  have hLowAE : AEMeasurable lowSum P := by
    have hterm :
        ∀ n ∈ S.attach,
          AEMeasurable
            (fun a : Homogenization.RegCoeffField d =>
              if k ≤ Int.toNat n.1 then 0 else lowerSlot a n + upperSlot a n) P := by
      intro n _hn
      by_cases hnlow : k ≤ Int.toNat n.1
      · simp only [hnlow, ↓reduceIte, aemeasurable_const]
      · simpa only [hnlow, ↓reduceIte] using (hLowerSlotAE n).add (hUpperSlotAE n)
    simpa only using Finset.aemeasurable_fun_sum (μ := P)
      (f := fun n (a : Homogenization.RegCoeffField d) =>
        if k ≤ Int.toNat n.1 then 0 else lowerSlot a n + upperSlot a n)
      S.attach hterm
  have hLowInt : MeasureTheory.Integrable lowSum P := by
    refine MeasureTheory.Integrable.mono' hEnvelopeInt
      hLowAE.aestronglyMeasurable ?_
    filter_upwards [hPoint, hLow_nonneg] with a hle hnonneg
    change |lowSum a| ≤ envelope a
    rw [abs_of_nonneg hnonneg]
    exact hle
  have hmono :
      ∫ a, lowSum a ∂P ≤ ∫ a, envelope a ∂P :=
    MeasureTheory.integral_mono_of_nonneg hLow_nonneg hEnvelopeInt hPoint
  have hEnvelopeIntegral :
      ∫ a, envelope a ∂P =
        S.attach.sum fun n => ∫ a, envelopeTerm n a ∂P := by
    simpa only using
      MeasureTheory.integral_finset_sum S.attach hEnvelopeTermInt
  have hEnvelopeTermBound :
      ∀ n ∈ S.attach,
        ∫ a, envelopeTerm n a ∂P ≤
          coeffResponse *
            ((if k ≤ Int.toNat n.1 then 0 else coeffTerm n) * responseMoment) := by
    intro n _hn
    by_cases hnlow : k ≤ Int.toNat n.1
    · simp only [hnlow, ↓reduceIte, MeasureTheory.integral_zero, zero_mul, mul_zero, le_refl, envelopeTerm, coeffTerm]
    · have hEnvelopeTerm_eq :
          ∫ a, envelopeTerm n a ∂P =
            coeffResponse *
              (σ * ∫ a, lowerZero a n * childAvg a ∂P +
                σ⁻¹ * ∫ a, upperZero a n * childAvg a ∂P +
                gapCoeff n * ∫ a, childAvg a ∂P) := by
        have hsplit :
            ∫ a, envelopeTerm n a ∂P =
              ∫ a, coeffResponse *
                (σ * (lowerZero a n * childAvg a) +
                  σ⁻¹ * (upperZero a n * childAvg a) +
                  gapCoeff n * childAvg a) ∂P := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with a
          simp only [hnlow, ↓reduceIte, mul_eq_mul_left_iff, envelopeTerm]
          ring_nf
          simp only [true_or]
        have hsplit_integral :
            ∫ a,
              σ * (lowerZero a n * childAvg a) +
                σ⁻¹ * (upperZero a n * childAvg a) +
                gapCoeff n * childAvg a ∂P =
              σ * ∫ a, lowerZero a n * childAvg a ∂P +
                σ⁻¹ * ∫ a, upperZero a n * childAvg a ∂P +
                gapCoeff n * ∫ a, childAvg a ∂P := by
          let lowerProd : Homogenization.RegCoeffField d → ℝ := fun a =>
            lowerZero a n * childAvg a
          let upperProd : Homogenization.RegCoeffField d → ℝ := fun a =>
            upperZero a n * childAvg a
          let gapProd : Homogenization.RegCoeffField d → ℝ := childAvg
          have hlowerInt : MeasureTheory.Integrable lowerProd P := by
            simpa only using hLowerProdInt n
          have hupperInt : MeasureTheory.Integrable upperProd P := by
            simpa only using hUpperProdInt n
          have hgapInt : MeasureTheory.Integrable gapProd P := by
            simpa only using hChildInt
          have hpairInt :
              MeasureTheory.Integrable
                (fun a : Homogenization.RegCoeffField d =>
                  σ * lowerProd a + σ⁻¹ * upperProd a) P :=
            (hlowerInt.const_mul σ).add (hupperInt.const_mul σ⁻¹)
          calc
            ∫ a,
                σ * (lowerZero a n * childAvg a) +
                  σ⁻¹ * (upperZero a n * childAvg a) +
                  gapCoeff n * childAvg a ∂P =
              ∫ a,
                (σ * lowerProd a + σ⁻¹ * upperProd a) +
                  gapCoeff n * gapProd a ∂P := by
                refine MeasureTheory.integral_congr_ae ?_
                filter_upwards with a
                dsimp [lowerProd, upperProd, gapProd]
            _ =
              ∫ a, σ * lowerProd a + σ⁻¹ * upperProd a ∂P +
                ∫ a, gapCoeff n * gapProd a ∂P := by
                rw [MeasureTheory.integral_add hpairInt
                  (hgapInt.const_mul (gapCoeff n))]
            _ =
              (∫ a, σ * lowerProd a ∂P +
                  ∫ a, σ⁻¹ * upperProd a ∂P) +
                ∫ a, gapCoeff n * gapProd a ∂P := by
                rw [MeasureTheory.integral_add
                  (hlowerInt.const_mul σ) (hupperInt.const_mul σ⁻¹)]
            _ =
              σ * ∫ a, lowerZero a n * childAvg a ∂P +
                σ⁻¹ * ∫ a, upperZero a n * childAvg a ∂P +
                gapCoeff n * ∫ a, childAvg a ∂P := by
                rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
                  MeasureTheory.integral_const_mul]
        rw [hsplit, MeasureTheory.integral_const_mul, hsplit_integral]
      have hinside :
          σ * ∫ a, lowerZero a n * childAvg a ∂P +
              σ⁻¹ * ∫ a, upperZero a n * childAvg a ∂P +
              gapCoeff n * ∫ a, childAvg a ∂P
            ≤
          σ * (lowerRootCoeff n * responseMoment) +
              σ⁻¹ * (upperRootCoeff n * responseMoment) +
              gapCoeff n * responseMoment := by
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left (hLowerHolder n) hσ_nonneg)
            (mul_le_mul_of_nonneg_left (hUpperHolder n) hσ_inv_nonneg))
          (mul_le_mul_of_nonneg_left hChildIntegral_le (hGapCoeff_nonneg n))
      calc
        ∫ a, envelopeTerm n a ∂P =
          coeffResponse *
            (σ * ∫ a, lowerZero a n * childAvg a ∂P +
              σ⁻¹ * ∫ a, upperZero a n * childAvg a ∂P +
              gapCoeff n * ∫ a, childAvg a ∂P) := hEnvelopeTerm_eq
        _ ≤
          coeffResponse *
            (σ * (lowerRootCoeff n * responseMoment) +
              σ⁻¹ * (upperRootCoeff n * responseMoment) +
              gapCoeff n * responseMoment) :=
            mul_le_mul_of_nonneg_left hinside hcoeffResponse_nonneg
        _ =
          coeffResponse *
            ((if k ≤ Int.toNat n.1 then 0 else coeffTerm n) * responseMoment) := by
            rw [if_neg hnlow]
            dsimp [coeffTerm]
            ring_nf
  have hEnvelopeBound :
      ∫ a, envelope a ∂P ≤ coeffResponse * lowCoeff * responseMoment := by
    calc
      ∫ a, envelope a ∂P =
          S.attach.sum fun n => ∫ a, envelopeTerm n a ∂P := hEnvelopeIntegral
      _ ≤
          S.attach.sum fun n =>
            coeffResponse *
              ((if k ≤ Int.toNat n.1 then 0 else coeffTerm n) * responseMoment) :=
          Finset.sum_le_sum hEnvelopeTermBound
      _ =
          coeffResponse * lowCoeff * responseMoment := by
          dsimp [lowCoeff]
          calc
            S.attach.sum (fun n =>
                coeffResponse *
                  ((if k ≤ Int.toNat n.1 then 0 else coeffTerm n) * responseMoment))
                =
              S.attach.sum (fun n =>
                (coeffResponse *
                  (if k ≤ Int.toNat n.1 then 0 else coeffTerm n)) * responseMoment) := by
                refine Finset.sum_congr rfl ?_
                intro n _hn
                ring
            _ =
              (S.attach.sum fun n =>
                coeffResponse * (if k ≤ Int.toNat n.1 then 0 else coeffTerm n)) *
                  responseMoment := by
                rw [Finset.sum_mul]
            _ =
              (coeffResponse *
                (S.attach.sum fun n =>
                  if k ≤ Int.toNat n.1 then 0 else coeffTerm n)) *
                  responseMoment := by
                rw [Finset.mul_sum]
            _ =
              coeffResponse *
                (S.attach.sum fun n =>
                  if k ≤ Int.toNat n.1 then 0 else coeffTerm n) *
                  responseMoment := by
                ring
  exact ⟨hLowInt, hmono.trans hEnvelopeBound⟩

end

end Homogenization.HighContrast.EntryScale
