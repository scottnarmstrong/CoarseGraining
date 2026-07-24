import Homogenization.HighContrast.EntryScale.RawHighContrastWeakNorm.P1
import Homogenization.HighContrast.EntryScale.RawHighContrastWeakNorm.P3
import Homogenization.HighContrast.EntryScale.ResponseMoment
import Homogenization.Book.Ch04.Theorems.DilationResponse

open Homogenization
open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization.Book.Ch05.Section54.OneStepContraction


/-!
# Local tail transport

Lemmas for transporting LIH scale-zero low-tail coefficients for the law
normalized at the left endpoint back to the original local window `(k,m)`.

The point of this file is to keep the transported coefficient tied to the
correct local scalar `localWeakNormScalarWeightAtScales`/`terminalPAtScales`,
rather than the coarse terminal scalar
`coarseFluctuationScalarWeightAtScale hP hStruct m`.
-/


namespace Homogenization.HighContrast.EntryScale

noncomputable section

/-- Descendant averages commute with triadic cube dilation. -/
theorem descendantsAverage_dilateCube {d : ℕ} (k : ℤ)
    (Q : Homogenization.TriadicCube d) (j : ℕ)
    (F : Homogenization.TriadicCube d → ℝ) :
    Homogenization.descendantsAverage
        (Homogenization.Book.Ch02.dilateCube k Q) j F =
      Homogenization.descendantsAverage Q j
        (fun R => F (Homogenization.Book.Ch02.dilateCube k R)) := by
  classical
  dsimp [Homogenization.descendantsAverage]
  rw [Homogenization.Book.Ch02.descendantsAtDepth_dilateCube]
  rw [Finset.card_image_of_injective
    _ (Homogenization.Book.Ch02.dilateCube_injective k)]
  rw [Finset.sum_image]
  intro R _hR S _hS hRS
  exact Homogenization.Book.Ch02.dilateCube_injective k hRS

/-- Origin-cube lower ellipticity coefficient transport from normalized window
coordinates back to the original terminal scale. -/
theorem lambdaSqCoeffField_originCube_dilateCoeffField_neg_nat_of_le
    {d : ℕ} [NeZero d] {a : Homogenization.CoeffField d}
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a)
    {k m : ℕ} (hkm : k ≤ m) (s : ℝ)
    (q : Homogenization.Book.Ch02.MultiscaleExponent) :
    Homogenization.Book.Ch04.lambdaSqCoeffField
        (Homogenization.originCube d ((m - k : ℕ) : ℤ)) s q
        (Homogenization.Book.Ch02.dilateCoeffField (-(k : ℤ)) a) =
      Homogenization.Book.Ch04.lambdaSqCoeffField
        (Homogenization.originCube d (m : ℤ)) s q a := by
  rw [← Homogenization.Book.Ch04.rescaleCoeffField_eq_dilateCoeffField_neg_nat k]
  have hshift :=
    Homogenization.Book.Ch04.lambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
      ha k (m - k) s q
  have hsum : k + (m - k) = m := Nat.add_sub_of_le hkm
  simpa only [hsum] using hshift

/-- Origin-cube upper ellipticity coefficient transport from normalized window
coordinates back to the original terminal scale. -/
theorem LambdaSqCoeffField_originCube_dilateCoeffField_neg_nat_of_le
    {d : ℕ} [NeZero d] {a : Homogenization.CoeffField d}
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a)
    {k m : ℕ} (hkm : k ≤ m) (s : ℝ)
    (q : Homogenization.Book.Ch02.MultiscaleExponent) :
    Homogenization.Book.Ch04.LambdaSqCoeffField
        (Homogenization.originCube d ((m - k : ℕ) : ℤ)) s q
        (Homogenization.Book.Ch02.dilateCoeffField (-(k : ℤ)) a) =
      Homogenization.Book.Ch04.LambdaSqCoeffField
        (Homogenization.originCube d (m : ℤ)) s q a := by
  rw [← Homogenization.Book.Ch04.rescaleCoeffField_eq_dilateCoeffField_neg_nat k]
  have hshift :=
    Homogenization.Book.Ch04.LambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
      ha k (m - k) s q
  have hsum : k + (m - k) = m := Nat.add_sub_of_le hkm
  simpa only [hsum] using hshift

/-- Origin-cube response observable transport from normalized window
coordinates back to the original terminal scale. -/
theorem responseJObservableCubeSet_originCube_dilateCoeffField_neg_nat_of_le
    {d : ℕ} [NeZero d] {a : Homogenization.CoeffField d}
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a)
    {k m : ℕ} (hkm : k ≤ m) (p q : Homogenization.Vec d) :
    Homogenization.Book.Ch04.responseJObservableCubeSet
        (Homogenization.originCube d ((m - k : ℕ) : ℤ)) p q
        (Homogenization.Book.Ch02.dilateCoeffField (-(k : ℤ)) a) =
      Homogenization.Book.Ch04.responseJObservableCubeSet
        (Homogenization.originCube d (m : ℤ)) p q a := by
  have hshift :=
    Homogenization.Book.Ch04.responseJObservableCubeSet_originCube_dilateCoeffField_neg_nat_of_aelocallyUniformlyElliptic
      ha k (m - k) p q
  have hsum : k + (m - k) = m := Nat.add_sub_of_le hkm
  simpa only [Book.Ch04.responseJObservableCubeSet_apply, hsum] using hshift

/-- LIH's gradient low-scale tail transports from normalized coordinates
`(0,m-k)` back to the original local window `(k,m)`. -/
theorem gradientLowScaleTailAtScale_dilateCoeffField_neg_nat_of_le
    {d : ℕ} [NeZero d] {a : Homogenization.CoeffField d}
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a)
    {k m : ℕ} (hkm : k ≤ m) (s s' : ℝ)
    (p q : Homogenization.Vec d) :
    Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientLowScaleTailAtScale
        ((m - k : ℕ) : ℤ) (0 : ℤ) s s' p q
        (Homogenization.Book.Ch02.dilateCoeffField (-(k : ℤ)) a) =
      Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientLowScaleTailAtScale
        (m : ℤ) (k : ℤ) s s' p q a := by
  have hdiff :
      Int.toNat (((m - k : ℕ) : ℤ) - (0 : ℤ)) =
        Int.toNat ((m : ℤ) - (k : ℤ)) := by
    omega
  have hlambda :=
    lambdaSqCoeffField_originCube_dilateCoeffField_neg_nat_of_le
      (d := d) ha hkm s' (.finite 1)
  have hresponse :=
    responseJObservableCubeSet_originCube_dilateCoeffField_neg_nat_of_le
      (d := d) ha hkm p q
  have hresponse' :
      Homogenization.ResponseJ
          (Homogenization.cubeSet
            (Homogenization.originCube d ((m - k : ℕ) : ℤ))) p q
          (Homogenization.Book.Ch02.dilateCoeffField (-(k : ℤ)) a) =
        Homogenization.ResponseJ
          (Homogenization.cubeSet
            (Homogenization.originCube d (m : ℤ))) p q a := by
    simpa only [Book.Ch04.responseJObservableCubeSet] using hresponse
  dsimp [Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientLowScaleTailAtScale]
  rw [hdiff, hlambda, hresponse']

/-- LIH's flux low-scale tail transports from normalized coordinates
`(0,m-k)` back to the original local window `(k,m)`. -/
theorem fluxLowScaleTailAtScale_dilateCoeffField_neg_nat_of_le
    {d : ℕ} [NeZero d] {a : Homogenization.CoeffField d}
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a)
    {k m : ℕ} (hkm : k ≤ m) (t t' : ℝ)
    (p q : Homogenization.Vec d) :
    Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxLowScaleTailAtScale
        ((m - k : ℕ) : ℤ) (0 : ℤ) t t' p q
        (Homogenization.Book.Ch02.dilateCoeffField (-(k : ℤ)) a) =
      Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxLowScaleTailAtScale
        (m : ℤ) (k : ℤ) t t' p q a := by
  have hdiff :
      Int.toNat (((m - k : ℕ) : ℤ) - (0 : ℤ)) =
        Int.toNat ((m : ℤ) - (k : ℤ)) := by
    omega
  have hLambda :=
    LambdaSqCoeffField_originCube_dilateCoeffField_neg_nat_of_le
      (d := d) ha hkm t' (.finite 1)
  have hresponse :=
    responseJObservableCubeSet_originCube_dilateCoeffField_neg_nat_of_le
      (d := d) ha hkm p q
  have hresponse' :
      Homogenization.ResponseJ
          (Homogenization.cubeSet
            (Homogenization.originCube d ((m - k : ℕ) : ℤ))) p q
          (Homogenization.Book.Ch02.dilateCoeffField (-(k : ℤ)) a) =
        Homogenization.ResponseJ
          (Homogenization.cubeSet
            (Homogenization.originCube d (m : ℤ))) p q a := by
    simpa only [Book.Ch04.responseJObservableCubeSet] using hresponse
  dsimp [Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxLowScaleTailAtScale]
  rw [hdiff, hLambda, hresponse']


private theorem childResponseScale_ge_one_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P) :
    1 ≤ (5 * (section53CoarseFluctuationBeta hP4)⁻¹) ^ 2 := by
  let β := section53CoarseFluctuationBeta hP4
  have hβ_pos : 0 < β := by
    simpa only using
      Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta_pos
        hP4
  have hβ_le_one : β ≤ 1 := by
    have hle := sLower_add_beta_le_one hP4
    dsimp [β] at hle ⊢
    linarith only [hle, hP4.sLower_pos]
  have hβ_inv_ge_one : 1 ≤ β⁻¹ := by
    have hmul := mul_le_mul_of_nonneg_right hβ_le_one
      (inv_nonneg.mpr hβ_pos.le)
    rw [mul_inv_cancel₀ hβ_pos.ne'] at hmul
    simpa only [ge_iff_le, one_mul] using hmul
  have hfive : 1 ≤ 5 * β⁻¹ := by linarith only [hβ_inv_ge_one]
  have hfive_nonneg : 0 ≤ 5 * β⁻¹ := le_trans zero_le_one hfive
  have hsq :
      (1 : ℝ) ^ 2 ≤ (5 * β⁻¹) ^ 2 :=
    (sq_le_sq₀ zero_le_one hfive_nonneg).2 hfive
  simpa only [one_le_sq_iff_one_le_abs, abs_mul, Nat.abs_ofNat, abs_inv, ge_iff_le, one_pow] using hsq


/--
Normalized raw low-tail bridge with the response-baseline scalar transported
to the local window.  The positive child-response branch is returned as the
original terminal positive-excess child average, so the existing source-max
lower-edge package can be used without transporting the source maximum.
-/
private theorem integral_paired_lowScaleTailSquares_special_le_localResponseBaseline_add_terminalPositiveExcess_childAverage
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hstat : Homogenization.Book.Ch04.StationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m)
    (e : Homogenization.Vec d) :
    let β := section53CoarseFluctuationBeta hP4
    let s := hP4.sLower + 2 * β
    let s' := hP4.sLower + β
    let t := hP4.sUpper + 2 * β
    let t' := hP4.sUpper + β
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let childAvg := fun a : Homogenization.CoeffField d =>
      Homogenization.descendantsAverage Q (m - k)
        (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
    let lowerTerminal := fun a : Homogenization.CoeffField d =>
      max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0
    let upperTerminal := fun a : Homogenization.CoeffField d =>
      max
        (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0
    let terminalChild : Homogenization.CoeffField d → ℝ := fun a =>
      (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) * childAvg a
    let tailFactor : ℝ :=
      (β ^ 2)⁻¹ *
        Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))
    let responseBaselineCoeff : ℝ :=
      tailFactor * localWeakNormScalarWeightAtScales hP hStruct k m
    let responseTerm : ℝ :=
      coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
    let lowScaleTail : ℝ :=
      ∫ a,
        (σ *
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientLowScaleTailAtScale
              (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
          σ⁻¹ *
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxLowScaleTailAtScale
              (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P
    lowScaleTail ≤
      responseBaselineCoeff * responseTerm + tailFactor * ∫ a, terminalChild a ∂P := by
  classical
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let s' := hP4.sLower + β
  let t := hP4.sUpper + 2 * β
  let t' := hP4.sUpper + β
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let childAvg : Homogenization.CoeffField d → ℝ := fun a =>
    Homogenization.descendantsAverage Q (m - k)
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
  let lowerTerminal : Homogenization.CoeffField d → ℝ := fun a =>
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
      0
  let upperTerminal : Homogenization.CoeffField d → ℝ := fun a =>
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
        hP.barSigmaAtScale hStruct (m : ℤ))
      0
  let terminalChild : Homogenization.CoeffField d → ℝ := fun a =>
    (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) * childAvg a
  let tailFactor : ℝ :=
    (β ^ 2)⁻¹ *
      Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))
  let responseBaselineCoeff : ℝ :=
    tailFactor * localWeakNormScalarWeightAtScales hP hStruct k m
  let responseTerm : ℝ :=
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  let lowScaleTail : ℝ :=
    ∫ a,
      (σ *
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientLowScaleTailAtScale
            (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
        σ⁻¹ *
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxLowScaleTailAtScale
            (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P
  let hP4k := hP4.scaleNormalized hP hStruct k
  let βk := section53CoarseFluctuationBeta hP4k
  let sk := hP4k.sLower + 2 * βk
  let sk' := hP4k.sLower + βk
  let tk := hP4k.sUpper + 2 * βk
  let tk' := hP4k.sUpper + βk
  let M : ℕ := m - k
  let Qk : Homogenization.TriadicCube d := Homogenization.originCube d (M : ℤ)
  let p_ek :=
    Homogenization.Book.Ch05.specialPAtScale
      (hP.scaleNormalized k) (hStruct.scaleNormalized k) (M : ℤ) e
  let q_ek :=
    Homogenization.Book.Ch05.specialQAtScale
      (hP.scaleNormalized k) (hStruct.scaleNormalized k) (M : ℤ) e
  let σk :=
    Homogenization.Book.Ch05.sigmaHatAtScale
      (hP.scaleNormalized k) (hStruct.scaleNormalized k) (M : ℤ)
  let childAvgK : Homogenization.CoeffField d → ℝ := fun a =>
    Homogenization.descendantsAverage Qk M
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_ek q_ek a)
  let lowerZeroK : Homogenization.CoeffField d → ℝ := fun a =>
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Qk sk' (.finite 1) a)⁻¹ -
        ((hP.scaleNormalized k).barSigmaStarAtScale
          (hStruct.scaleNormalized k) (0 : ℤ))⁻¹)
      0
  let upperZeroK : Homogenization.CoeffField d → ℝ := fun a =>
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Qk tk' (.finite 1) a -
        (hP.scaleNormalized k).barSigmaAtScale
          (hStruct.scaleNormalized k) (0 : ℤ))
      0
  let lowerTerminalK : Homogenization.CoeffField d → ℝ := fun a =>
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Qk sk' (.finite 1) a)⁻¹ -
        ((hP.scaleNormalized k).barSigmaStarAtScale
          (hStruct.scaleNormalized k) (M : ℤ))⁻¹)
      0
  let upperTerminalK : Homogenization.CoeffField d → ℝ := fun a =>
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Qk tk' (.finite 1) a -
        (hP.scaleNormalized k).barSigmaAtScale
          (hStruct.scaleNormalized k) (M : ℤ))
      0
  let terminalChildK : Homogenization.CoeffField d → ℝ := fun a =>
    (σk * lowerTerminalK a + σk⁻¹ * upperTerminalK a) * childAvgK a
  let X : Homogenization.CoeffField d → ℝ := fun a =>
    σk *
        (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientLowScaleTailAtScale
          (M : ℤ) (0 : ℤ) sk sk' p_ek q_ek a) ^ 2 +
      σk⁻¹ *
        (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxLowScaleTailAtScale
          (M : ℤ) (0 : ℤ) tk tk' p_ek q_ek a) ^ 2
  let tailFactorK : ℝ :=
    (βk ^ 2)⁻¹ * Real.rpow (3 : ℝ) (-2 * βk * (M : ℝ))
  let responseTermK : ℝ :=
    coarseFluctuationResponseMomentAtScale
      (hP.scaleNormalized k) (hStruct.scaleNormalized k) hP4k 0 M e
  let positiveK : ℝ :=
    σk * (∫ a, lowerZeroK a * childAvgK a
        ∂Homogenization.Book.Ch04.scaleNormalizedLaw k P) +
      σk⁻¹ * (∫ a, upperZeroK a * childAvgK a
        ∂Homogenization.Book.Ch04.scaleNormalizedLaw k P)
  have hM_pos : 0 < M := by
    simpa only [M] using Nat.sub_pos_of_lt hkm
  have hraw_norm :=
    integral_paired_lowScaleTailSquares_special_le_rawLowScaleTerms
      (hP.scaleNormalized k) (hstat.scaleNormalized k)
      (hStruct.scaleNormalized k) hP4k (k := 0) (m := M) hM_pos e
  have hβk : βk = β := by
    dsimp [βk, β, hP4k,
      section53CoarseFluctuationBeta, section53CoarseFluctuationBetaCore,
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity.scaleNormalized]
  have hsk : sk = s := by
    simp only [Book.Ch05.QuantitativeCoarseGrainedEllipticity.scaleNormalized, hβk, sk, hP4k, βk, β, s]
  have hsk' : sk' = s' := by
    simp only [Book.Ch05.QuantitativeCoarseGrainedEllipticity.scaleNormalized, hβk, sk', hP4k, βk, β, s']
  have htk : tk = t := by
    simp only [Book.Ch05.QuantitativeCoarseGrainedEllipticity.scaleNormalized, hβk, tk, hP4k, βk, β, t]
  have htk' : tk' = t' := by
    simp only [Book.Ch05.QuantitativeCoarseGrainedEllipticity.scaleNormalized, hβk, tk', hP4k, βk, β, t']
  have hp_ek : p_ek = p_e := by
    simpa only [p_ek, p_e, M] using specialPAtScale_scaleNormalizedLaw_of_le
      (hP := hP) (hStruct := hStruct) hkm.le e
  have hq_ek : q_ek = q_e := by
    simpa only [q_ek, q_e, M] using specialQAtScale_scaleNormalizedLaw_of_le
      (hP := hP) (hStruct := hStruct) hkm.le e
  have hσk : σk = σ := by
    simpa only [Book.Ch05.sigmaHatAtScale_eq] using sigmaHatAtScale_scaleNormalizedLaw_of_le
      (hP := hP) (hStruct := hStruct) hkm.le
  have hscalarK :
      coarseFluctuationScalarWeightAtScale
          (hP.scaleNormalized k) (hStruct.scaleNormalized k) M =
        localWeakNormScalarWeightAtScales hP hStruct k m := by
    simpa only using
      coarseFluctuationScalarWeightAtScale_scaleNormalizedLaw_of_le
        (hP := hP) (hStruct := hStruct) hkm.le
  have hresponseTermK :
      responseTermK = responseTerm := by
    simpa only using
      coarseFluctuationResponseMomentAtScale_scaleNormalizedLaw_of_le
        hP hStruct hP4 hkm.le e
  have htailFactorK : tailFactorK = tailFactor := by
    dsimp [tailFactorK, tailFactor, M]
    rw [hβk]
  have hX_meas :
      MeasureTheory.AEStronglyMeasurable X
        (Homogenization.Book.Ch04.scaleNormalizedLaw k P) := by
    simpa only [X, βk, sk, sk', tk, tk', M, Qk, p_ek, q_ek, σk] using
      hraw_norm.1.aestronglyMeasurable
  have hlow_integral :
      ∫ a, X a ∂Homogenization.Book.Ch04.scaleNormalizedLaw k P =
        lowScaleTail := by
    rw [Homogenization.Book.Ch04.integral_scaleNormalizedLaw k X hX_meas]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
    have hgrad :=
      gradientLowScaleTailAtScale_dilateCoeffField_neg_nat_of_le
        (d := d) ha hkm.le s s' p_e q_e
    have hflux :=
      fluxLowScaleTailAtScale_dilateCoeffField_neg_nat_of_le
        (d := d) ha hkm.le t t' p_e q_e
    simp only [hσk, hsk, hsk', hp_ek, hq_ek, htk, htk', hgrad, hflux, X, M]
  have hraw_bound :
      ∫ a, X a ∂Homogenization.Book.Ch04.scaleNormalizedLaw k P ≤
        tailFactorK *
          (coarseFluctuationScalarWeightAtScale
              (hP.scaleNormalized k) (hStruct.scaleNormalized k) M *
            Homogenization.Book.Ch04.expectedResponseJCubeSet
              (Homogenization.Book.Ch04.scaleNormalizedLaw k P) Qk p_ek q_ek +
            positiveK) := by
    simpa only [X, positiveK, tailFactorK, βk, sk, sk', tk, tk', M, Qk,
      p_ek, q_ek, σk, childAvgK, lowerZeroK, upperZeroK] using hraw_norm.2
  have htail_nonneg : 0 ≤ tailFactorK := by
    dsimp [tailFactorK]
    exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hscalar_nonneg :
      0 ≤
        coarseFluctuationScalarWeightAtScale
          (hP.scaleNormalized k) (hStruct.scaleNormalized k) M :=
    coarseFluctuationScalarWeightAtScale_nonneg
      (hP.scaleNormalized k) (hStruct.scaleNormalized k) hP4k M
  have hresponse_le :
      Homogenization.Book.Ch04.expectedResponseJCubeSet
          (Homogenization.Book.Ch04.scaleNormalizedLaw k P) Qk p_ek q_ek
        ≤ responseTermK := by
    simpa only [Qk, p_ek, q_ek, responseTermK, M] using
      expectedResponseJCubeSet_terminal_le_coarseFluctuationResponseMomentAtScale
        (hP.scaleNormalized k) (hstat.scaleNormalized k)
        (hStruct.scaleNormalized k) hP4k (Nat.zero_le M) e
  have hbaseline_le :
      tailFactorK *
          (coarseFluctuationScalarWeightAtScale
              (hP.scaleNormalized k) (hStruct.scaleNormalized k) M *
            Homogenization.Book.Ch04.expectedResponseJCubeSet
              (Homogenization.Book.Ch04.scaleNormalizedLaw k P) Qk p_ek q_ek)
        ≤ responseBaselineCoeff * responseTerm := by
    calc
      tailFactorK *
          (coarseFluctuationScalarWeightAtScale
              (hP.scaleNormalized k) (hStruct.scaleNormalized k) M *
            Homogenization.Book.Ch04.expectedResponseJCubeSet
              (Homogenization.Book.Ch04.scaleNormalizedLaw k P) Qk p_ek q_ek)
          ≤
        tailFactorK *
          (coarseFluctuationScalarWeightAtScale
              (hP.scaleNormalized k) (hStruct.scaleNormalized k) M *
            responseTermK) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hresponse_le hscalar_nonneg) htail_nonneg
      _ = responseBaselineCoeff * responseTerm := by
          dsimp [responseBaselineCoeff]
          rw [htailFactorK, hscalarK, hresponseTermK]
          ring
  have hchildK_nonneg :
      0 ≤ᵐ[Homogenization.Book.Ch04.scaleNormalizedLaw k P] childAvgK := by
    filter_upwards with a
    dsimp [childAvgK]
    exact Homogenization.descendantsAverage_nonneg Qk M
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_ek q_ek a)
      (fun R _hR =>
        Homogenization.Book.Ch04.responseJObservableCubeSet_nonneg R p_ek q_ek a)
  have hTerminalKInt : MeasureTheory.Integrable terminalChildK
      (Homogenization.Book.Ch04.scaleNormalizedLaw k P) := by
    simpa only [terminalChildK, βk, sk', tk', M, Qk, p_ek, q_ek, σk,
      childAvgK, lowerTerminalK, upperTerminalK] using
      integrable_terminalPositiveExcess_childAverage_special_of_P4
        (hP.scaleNormalized k) (hstat.scaleNormalized k)
        (hStruct.scaleNormalized k) hP4k (k := 0) (m := M) hM_pos e
  have hzero_to_terminalK :
      ∫ a,
          (σk * lowerZeroK a + σk⁻¹ * upperZeroK a) * childAvgK a
          ∂Homogenization.Book.Ch04.scaleNormalizedLaw k P
        ≤ ∫ a, terminalChildK a
          ∂Homogenization.Book.Ch04.scaleNormalizedLaw k P := by
    simpa only [Book.Ch05.sigmaHatAtScale_eq] using
      integral_zeroBaselinePositiveExcessWeight_mul_le_terminalPositiveExcessWeight_mul
        (hP.scaleNormalized k) (hStruct.scaleNormalized k) hP4k
        (m := M) sk' tk' childAvgK hchildK_nonneg
        (by simpa only [Book.Ch05.sigmaHatAtScale_eq, M, terminalChildK, σk, lowerTerminalK, Qk, upperTerminalK] using hTerminalKInt)
  have hsplitK :
      ∫ a,
          (σk * lowerZeroK a + σk⁻¹ * upperZeroK a) * childAvgK a
          ∂Homogenization.Book.Ch04.scaleNormalizedLaw k P
        = positiveK := by
    simpa only [positiveK, βk, sk', tk', M, Qk, p_ek, q_ek, σk,
      childAvgK, lowerZeroK, upperZeroK] using
      integral_zeroBaselinePositiveExcess_childAverage_split_special_of_P4
        (hP.scaleNormalized k) (hstat.scaleNormalized k)
        (hStruct.scaleNormalized k) hP4k (k := 0) (m := M) hM_pos e
  have hterminal_transport :
      ∫ a, terminalChildK a ∂Homogenization.Book.Ch04.scaleNormalizedLaw k P =
        ∫ a, terminalChild a ∂P := by
    rw [Homogenization.Book.Ch04.integral_scaleNormalizedLaw
      k terminalChildK hTerminalKInt.aestronglyMeasurable]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
    have hlowerBase :
        (hP.scaleNormalized k).barSigmaStarAtScale
            (hStruct.scaleNormalized k) (M : ℤ) =
          hP.barSigmaStarAtScale hStruct (m : ℤ) := by
      have h := hP.barSigmaStarAtScale_scaleNormalizedLaw hStruct k M
      have hsum : k + M = m := by simpa only using Nat.add_sub_of_le hkm.le
      simpa only [hsum] using h
    have hupperBase :
        (hP.scaleNormalized k).barSigmaAtScale
            (hStruct.scaleNormalized k) (M : ℤ) =
          hP.barSigmaAtScale hStruct (m : ℤ) := by
      have h := hP.barSigmaAtScale_scaleNormalizedLaw hStruct k M
      have hsum : k + M = m := by simpa only using Nat.add_sub_of_le hkm.le
      simpa only [hsum] using h
    have hlambda :
        Homogenization.Book.Ch04.lambdaSqCoeffField Qk sk' (.finite 1)
            (Homogenization.Book.Ch02.dilateCoeffField (-(k : ℤ)) a) =
          Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a := by
      have h :=
        lambdaSqCoeffField_originCube_dilateCoeffField_neg_nat_of_le
          (d := d) ha hkm.le sk' (.finite 1)
      simpa only [hsk'] using h
    have hLambda :
        Homogenization.Book.Ch04.LambdaSqCoeffField Qk tk' (.finite 1)
            (Homogenization.Book.Ch02.dilateCoeffField (-(k : ℤ)) a) =
          Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a := by
      have h :=
        LambdaSqCoeffField_originCube_dilateCoeffField_neg_nat_of_le
          (d := d) ha hkm.le tk' (.finite 1)
      simpa only [htk'] using h
    have hlower :
        lowerTerminalK (Homogenization.Book.Ch02.dilateCoeffField (-(k : ℤ)) a) =
          lowerTerminal a := by
      simp only [hlowerBase, hlambda, lowerTerminalK, lowerTerminal]
    have hupper :
        upperTerminalK (Homogenization.Book.Ch02.dilateCoeffField (-(k : ℤ)) a) =
          upperTerminal a := by
      simp only [hupperBase, hLambda, upperTerminalK, upperTerminal]
    have hchild :
        childAvgK (Homogenization.Book.Ch02.dilateCoeffField (-(k : ℤ)) a) =
          childAvg a := by
      have hfun :
          (fun R : Homogenization.TriadicCube d =>
              Homogenization.Book.Ch04.responseJObservableCubeSet R p_ek q_ek
                (Homogenization.Book.Ch02.dilateCoeffField (-(k : ℤ)) a))
            =
          (fun R : Homogenization.TriadicCube d =>
              Homogenization.Book.Ch04.responseJObservableCubeSet
                (Homogenization.Book.Ch02.dilateCube (k : ℤ) R) p_e q_e a) := by
        funext R
        have hresp :=
          Homogenization.Book.Ch04.responseJObservableCubeSet_dilateCoeffField_neg_nat_of_aelocallyUniformlyElliptic
            ha k R p_e q_e
        simpa only [hp_ek, hq_ek, Book.Ch04.responseJObservableCubeSet_apply] using hresp
      have hdesc :=
        descendantsAverage_dilateCube (d := d) (k := (k : ℤ)) Qk M
          (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
      have hcube :
          Homogenization.Book.Ch02.dilateCube (k : ℤ) Qk = Q := by
        have h := Homogenization.Book.Ch04.dilateCube_originCube_nat
          (d := d) k M
        have hsum : k + M = m := by simpa only using Nat.add_sub_of_le hkm.le
        simp only [Book.Ch04.dilateCube_originCube_nat, hsum, M, Qk, Q] at h ⊢
      calc
        childAvgK (Homogenization.Book.Ch02.dilateCoeffField (-(k : ℤ)) a)
            =
          Homogenization.descendantsAverage Qk M
            (fun R : Homogenization.TriadicCube d =>
              Homogenization.Book.Ch04.responseJObservableCubeSet
                (Homogenization.Book.Ch02.dilateCube (k : ℤ) R) p_e q_e a) := by
              simpa only [Book.Ch04.responseJObservableCubeSet_apply, childAvgK] using
                congrArg (Homogenization.descendantsAverage Qk M) hfun
        _ =
          Homogenization.descendantsAverage
            (Homogenization.Book.Ch02.dilateCube (k : ℤ) Qk) M
            (fun R : Homogenization.TriadicCube d =>
              Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a) := by
              simpa only [Book.Ch04.responseJObservableCubeSet_apply] using hdesc.symm
        _ = childAvg a := by
              simp only [hcube, Book.Ch04.responseJObservableCubeSet_apply, Q, M, childAvg]
    simp only [hσk, hlower, hupper, hchild, terminalChildK, terminalChild]
  have hpositive_le :
      positiveK ≤ ∫ a, terminalChild a ∂P := by
    calc
      positiveK =
          ∫ a, (σk * lowerZeroK a + σk⁻¹ * upperZeroK a) * childAvgK a
            ∂Homogenization.Book.Ch04.scaleNormalizedLaw k P := hsplitK.symm
      _ ≤ ∫ a, terminalChildK a
            ∂Homogenization.Book.Ch04.scaleNormalizedLaw k P := hzero_to_terminalK
      _ = ∫ a, terminalChild a ∂P := hterminal_transport
  have hpositive_tail_le :
      tailFactorK * positiveK ≤ tailFactor * ∫ a, terminalChild a ∂P := by
    have hmul := mul_le_mul_of_nonneg_left hpositive_le htail_nonneg
    simpa only [htailFactorK, ge_iff_le] using hmul
  have hmain :
      lowScaleTail ≤ responseBaselineCoeff * responseTerm +
          tailFactor * ∫ a, terminalChild a ∂P := by
    calc
      lowScaleTail =
          ∫ a, X a ∂Homogenization.Book.Ch04.scaleNormalizedLaw k P :=
            hlow_integral.symm
      _ ≤ tailFactorK *
          (coarseFluctuationScalarWeightAtScale
              (hP.scaleNormalized k) (hStruct.scaleNormalized k) M *
            Homogenization.Book.Ch04.expectedResponseJCubeSet
              (Homogenization.Book.Ch04.scaleNormalizedLaw k P) Qk p_ek q_ek +
            positiveK) := hraw_bound
      _ =
          tailFactorK *
            (coarseFluctuationScalarWeightAtScale
                (hP.scaleNormalized k) (hStruct.scaleNormalized k) M *
              Homogenization.Book.Ch04.expectedResponseJCubeSet
                (Homogenization.Book.Ch04.scaleNormalizedLaw k P) Qk p_ek q_ek) +
          tailFactorK * positiveK := by ring
      _ ≤ responseBaselineCoeff * responseTerm +
          tailFactor * ∫ a, terminalChild a ∂P :=
            add_le_add hbaseline_le hpositive_tail_le
  simpa only [β, s, s', t, t', Q, p_e, q_e, σ, childAvg, lowerTerminal,
    upperTerminal, terminalChild, tailFactor, responseBaselineCoeff,
    responseTerm, lowScaleTail] using hmain

/--
Source labels `p.HC.CR`, `e.W.first.sum`, `e.J.moment.bound`, and `a.HM`:
raw LIH low-tail expectation conversion with the zero-baseline child-response
branch routed through the SHARP summed-weight first-power source split
(`min(sourceMax,1) + badEventTruncation` against the response, with the
`2 * sqrt(theta_m)` normalizer), replacing the mis-sized Holder package.
-/
theorem integral_paired_lowScaleTailSquares_special_le_responseBaseline_add_sourceMax_minBad_childResponseAverage_terms
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hstat : Homogenization.Book.Ch04.StationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d)
    (hm : HighCenteredMomentParameters d hc)
    (hparams : hP4.params = hm.p4Params) {N k m : ℕ}
    (hNk : N ≤ k) (hkm : k < m)
    (hHM :
      HighCenteredMomentEstimate hm P N
        (intermediateCoarseBlockDeviation hP hStruct
          (fun x : Homogenization.CoeffField d => x)))
    (e : Homogenization.Vec d)
    (hSmallInt :
      let β := section53CoarseFluctuationBeta hP4
      let s' := hP4.sLower + β
      let t' := hP4.sUpper + β
      let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
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
      MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d =>
          (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a) P)
    (hLowInt :
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
      let childAvg := fun a : Homogenization.CoeffField d =>
        Homogenization.descendantsAverage Q (m - k)
          (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
      let response := fun a : Homogenization.CoeffField d =>
        (5 * β⁻¹) ^ 2 * childAvg a
      let lowerSlot : Homogenization.CoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
        let parents := Homogenization.descendantsAtScale Q n.1
        let hparents : parents.Nonempty :=
          Homogenization.descendantsAtScale_nonempty Q
            (by simpa [Q, Homogenization.originCube] using
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
      let upperSlot : Homogenization.CoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
        let parents := Homogenization.descendantsAtScale Q n.1
        let hparents : parents.Nonempty :=
          Homogenization.descendantsAtScale_nonempty Q
            (by simpa [Q, Homogenization.originCube] using
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
      let lowSum := fun a : Homogenization.CoeffField d =>
        S.attach.sum fun n =>
          if k ≤ Int.toNat n.1 then 0 else lowerSlot a n + upperSlot a n
      MeasureTheory.Integrable lowSum P) :
    let β := section53CoarseFluctuationBeta hP4
    let s := hP4.sLower + 2 * β
    let s' := hP4.sLower + β
    let t := hP4.sUpper + 2 * β
    let t' := hP4.sUpper + β
    let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
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
    let lowerSlot : Homogenization.CoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
      let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa [Q, Homogenization.originCube] using
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
    let upperSlot : Homogenization.CoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
      let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa [Q, Homogenization.originCube] using
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
    let lowSum := fun a : Homogenization.CoeffField d =>
      S.attach.sum fun n =>
        if k ≤ Int.toNat n.1 then 0 else lowerSlot a n + upperSlot a n
    let sourceMax :=
      terminalSpectralPositivePartSourceMax hP hStruct hc k m Q
        (fun x : Homogenization.CoeffField d => x)
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
    let responseTerm : ℝ :=
      coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
    let sourceTerm : ℝ :=
      edgeWeightLoss *
          (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
          (∫ a, min (sourceMax a) 1 * response a ∂P) +
        edgeWeightLoss *
          (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
          (∫ a, badEventTruncation sourceMax a * response a ∂P)
    let tailFactor : ℝ :=
      (β ^ 2)⁻¹ *
        Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))
    let responseBaselineCoeff : ℝ :=
      tailFactor * localWeakNormScalarWeightAtScales hP hStruct k m
    let lowScaleTail : ℝ :=
      ∫ a,
        (σ *
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientLowScaleTailAtScale
              (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
          σ⁻¹ *
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxLowScaleTailAtScale
              (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P
    lowScaleTail ≤
      responseBaselineCoeff * responseTerm +
        tailFactor *
          (∫ a, (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a ∂P +
            ∫ a, lowSum a ∂P +
            sourceTerm) := by
  classical
  dsimp only at hSmallInt hLowInt ⊢
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let s' := hP4.sLower + β
  let t := hP4.sUpper + 2 * β
  let t' := hP4.sUpper + β
  let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let childAvg : Homogenization.CoeffField d → ℝ := fun a =>
    Homogenization.descendantsAverage Q (m - k)
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
  let response : Homogenization.CoeffField d → ℝ := fun a =>
    (5 * β⁻¹) ^ 2 * childAvg a
  let lowerZero : Homogenization.CoeffField d → ℝ := fun a =>
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct 0)⁻¹)
      0
  let upperZero : Homogenization.CoeffField d → ℝ := fun a =>
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
        hP.barSigmaAtScale hStruct 0)
      0
  let lowerTerminal : Homogenization.CoeffField d → ℝ := fun a =>
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
      0
  let upperTerminal : Homogenization.CoeffField d → ℝ := fun a =>
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
        hP.barSigmaAtScale hStruct (m : ℤ))
      0
  let lowerSmall : Homogenization.CoeffField d → ℝ := fun a =>
    Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
        (d := d) m s' a ^ 2 /
      Homogenization.Book.Ch05.Section52.section52SmallTailWeight s' m
  let upperSmall : Homogenization.CoeffField d → ℝ := fun a =>
    Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
        (d := d) m t' a ^ 2 /
      Homogenization.Book.Ch05.Section52.section52SmallTailWeight t' m
  let lowerSlot : Homogenization.CoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa [Q, Homogenization.originCube] using
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
  let upperSlot : Homogenization.CoeffField d → {n : ℤ // n ∈ S} → ℝ := fun a n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa [Q, Homogenization.originCube] using
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
  let lowSum : Homogenization.CoeffField d → ℝ := fun a =>
    S.attach.sum fun n =>
      if k ≤ Int.toNat n.1 then 0 else lowerSlot a n + upperSlot a n
  let sourceMax : Homogenization.CoeffField d → ℝ :=
    terminalSpectralPositivePartSourceMax hP hStruct hc k m Q
      (fun x : Homogenization.CoeffField d => x)
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
  let responseTerm : ℝ :=
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  let sourceTerm : ℝ :=
    edgeWeightLoss *
        (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
        (∫ a, min (sourceMax a) 1 * response a ∂P) +
      edgeWeightLoss *
        (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
        (∫ a, badEventTruncation sourceMax a * response a ∂P)
  let tailFactor : ℝ :=
    (β ^ 2)⁻¹ *
      Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))
  let responseBaselineCoeff : ℝ :=
    tailFactor * localWeakNormScalarWeightAtScales hP hStruct k m
  let lowScaleTail : ℝ :=
    ∫ a,
      (σ *
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientLowScaleTailAtScale
            (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
        σ⁻¹ *
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxLowScaleTailAtScale
            (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P
  let terminalChild : Homogenization.CoeffField d → ℝ := fun a =>
    (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) * childAvg a
  let terminalResponse : Homogenization.CoeffField d → ℝ := fun a =>
    (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) * response a
  let smallTerm : Homogenization.CoeffField d → ℝ := fun a =>
    (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a
  let badTerm : Homogenization.CoeffField d → ℝ := fun a =>
    edgeWeightLoss *
      (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
        (min (sourceMax a) 1 * response a +
          badEventTruncation sourceMax a * response a))
  have hraw :=
    integral_paired_lowScaleTailSquares_special_le_rawLowScaleTerms
      hP hstat hStruct hP4 hkm e
  have htail_nonneg : 0 ≤ tailFactor := by
    dsimp [tailFactor]
    exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hscale_ge_one : 1 ≤ (5 * β⁻¹) ^ 2 := by
    simpa only [one_le_sq_iff_one_le_abs, abs_mul, Nat.abs_ofNat, abs_inv] using childResponseScale_ge_one_of_P4 hP4
  have hChild_nonneg : 0 ≤ᵐ[P] childAvg := by
    filter_upwards with a
    dsimp [childAvg]
    exact Homogenization.descendantsAverage_nonneg Q (m - k)
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
      (fun R _hR =>
        Homogenization.Book.Ch04.responseJObservableCubeSet_nonneg R p_e q_e a)
  have hTerminalChildInt : MeasureTheory.Integrable terminalChild P := by
    simpa only [terminalChild, β, s', t', Q, p_e, q_e, σ, childAvg,
      lowerTerminal, upperTerminal] using
      integrable_terminalPositiveExcess_childAverage_special_of_P4
        hP hstat hStruct hP4 hkm e
  have hTerminalResponseInt : MeasureTheory.Integrable terminalResponse P := by
    refine (hTerminalChildInt.const_mul ((5 * β⁻¹) ^ 2)).congr ?_
    filter_upwards with a
    dsimp [terminalChild, terminalResponse, response]
    ring
  have hSmallInt' : MeasureTheory.Integrable smallTerm P := by
    simpa only [smallTerm, β, s', t', Q, p_e, q_e, σ, childAvg, response,
      lowerSmall, upperSmall] using hSmallInt
  have hLowInt' : MeasureTheory.Integrable lowSum P := by
    simpa only [lowSum, β, s', t', S, Q, p_e, q_e, σ, childAvg, response,
      lowerSlot, upperSlot] using hLowInt
  have hMinChildInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d =>
          min (sourceMax a) 1 * childAvg a) P := by
    simpa only [β, Q, p_e, q_e, childAvg, sourceMax] using
      integrable_min_terminalSourceMax_one_mul_childResponseAverage_special
        hP hstat hStruct hP4 hc hkm e
  have hBadChildPair :=
    integral_badEventTruncation_terminalSourceMax_mul_childResponseAverage_le_responseMoment_mul_global_polynomialRoot_add_drift_of_start_le
      hP hstat hStruct hP4 hc hm hparams hNk hkm hHM e
  have hBadChildInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d =>
          badEventTruncation sourceMax a * childAvg a) P := by
    simpa only [β, Q, p_e, q_e, childAvg, sourceMax] using hBadChildPair.1
  have hMinRespInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d =>
          min (sourceMax a) 1 * response a) P := by
    refine (hMinChildInt.const_mul ((5 * β⁻¹) ^ 2)).congr ?_
    filter_upwards with a
    dsimp [response]
    ring
  have hBadRespInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d =>
          badEventTruncation sourceMax a * response a) P := by
    refine (hBadChildInt.const_mul ((5 * β⁻¹) ^ 2)).congr ?_
    filter_upwards with a
    dsimp [response]
    ring
  have hBadInt : MeasureTheory.Integrable badTerm P := by
    refine ((hMinRespInt.add hBadRespInt).const_mul
      (edgeWeightLoss *
        (2 * Real.sqrt
          (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))))).congr ?_
    filter_upwards with a
    dsimp [badTerm]
    ring
  have hBadBound : ∫ a, badTerm a ∂P ≤ sourceTerm := by
    have hint :
        ∫ a, badTerm a ∂P =
          edgeWeightLoss *
              (2 * Real.sqrt
                (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))) *
            ∫ a,
              (min (sourceMax a) 1 * response a +
                badEventTruncation sourceMax a * response a) ∂P := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with a
      dsimp [badTerm]
      ring
    rw [hint, MeasureTheory.integral_add hMinRespInt hBadRespInt]
    refine le_of_eq ?_
    dsimp [sourceTerm]
    ring
  have hzero_le_terminal :
      ∫ a, (σ * lowerZero a + σ⁻¹ * upperZero a) * childAvg a ∂P
        ≤ ∫ a, terminalChild a ∂P := by
    simpa only [Book.Ch05.sigmaHatAtScale_eq] using
      integral_zeroBaselinePositiveExcessWeight_mul_le_terminalPositiveExcessWeight_mul
        (hP := hP) (hStruct := hStruct) (hP4 := hP4) (m := m)
        s' t' childAvg hChild_nonneg
        (by simpa only [Book.Ch05.sigmaHatAtScale_eq, terminalChild, σ, lowerTerminal, Q, upperTerminal]
          using hTerminalChildInt)
  have hterminal_child_le_response :
      ∫ a, terminalChild a ∂P ≤ ∫ a, terminalResponse a ∂P := by
    have hpoint : terminalChild ≤ᵐ[P] terminalResponse := by
      filter_upwards [hChild_nonneg] with a ha
      have hchild_le_response : childAvg a ≤ response a := by
        have hscale_nonneg : 0 ≤ (5 * β⁻¹) ^ 2 - 1 := sub_nonneg.mpr hscale_ge_one
        have hprod : 0 ≤ ((5 * β⁻¹) ^ 2 - 1) * childAvg a :=
          mul_nonneg hscale_nonneg ha
        dsimp [response]
        have hexp : ((5 * β⁻¹) ^ 2 - 1) * childAvg a =
            (5 * β⁻¹) ^ 2 * childAvg a - childAvg a := by ring
        linarith only [hprod, hexp]
      have hσ_nonneg : 0 ≤ σ := by
        dsimp [σ, Homogenization.Book.Ch05.sigmaHatAtScale]
        exact Real.sqrt_nonneg _
      have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
      have hweight_nonneg :
          0 ≤ σ * lowerTerminal a + σ⁻¹ * upperTerminal a := by
        exact add_nonneg
          (mul_nonneg hσ_nonneg (le_max_right _ _))
          (mul_nonneg hσ_inv_nonneg (le_max_right _ _))
      simpa only [ge_iff_le] using
        mul_le_mul_of_nonneg_left hchild_le_response hweight_nonneg
    exact MeasureTheory.integral_mono_ae hTerminalChildInt hTerminalResponseInt hpoint
  have hterminal_response_bound :
      ∫ a, terminalResponse a ∂P
        ≤ ∫ a, smallTerm a ∂P + ∫ a, lowSum a ∂P + sourceTerm := by
    have hRightInt :
        MeasureTheory.Integrable
          (fun a : Homogenization.CoeffField d =>
            smallTerm a + lowSum a + badTerm a) P :=
      (hSmallInt'.add hLowInt').add hBadInt
    have hPoint :
        terminalResponse ≤ᵐ[P]
          (fun a : Homogenization.CoeffField d =>
            smallTerm a + lowSum a + badTerm a) := by
      filter_upwards [hP.ae_locallyUniformlyEllipticField, hChild_nonneg] with a ha hchild
      have hresponse_nonneg : 0 ≤ response a := by
        dsimp [response]
        exact mul_nonneg (sq_nonneg _) hchild
      simpa only [terminalResponse, smallTerm, lowSum, badTerm, β, s', t', S, Q,
        p_e, q_e, σ, childAvg, response, lowerTerminal, upperTerminal,
        lowerSmall, upperSmall, lowerSlot, upperSlot, sourceMax,
        weightLossSup, edgeWeightLoss] using
        terminalPositiveExcessWeight_mul_le_section52SmallTail_mul_add_lowSum_add_edgeWeightLoss_mul_sqrtThetaAtScale_sourceMax_min_one_add_badEventTruncation_mul_response
          (hP := hP) (hStruct := hStruct) (hP4 := hP4) (hc := hc)
          (N := k) (m := m)
          (a := fun x : Homogenization.CoeffField d => x) (ω := a) ha
          (J := response a) hresponse_nonneg
    have hmono :
        ∫ a, terminalResponse a ∂P ≤
          ∫ a, smallTerm a + lowSum a + badTerm a ∂P :=
      MeasureTheory.integral_mono_ae hTerminalResponseInt hRightInt hPoint
    calc
      ∫ a, terminalResponse a ∂P
          ≤ ∫ a, smallTerm a + lowSum a + badTerm a ∂P := hmono
      _ = ∫ a, (smallTerm + lowSum) a + badTerm a ∂P := by rfl
      _ = ∫ a, (smallTerm + lowSum) a ∂P +
            ∫ a, badTerm a ∂P := by
            rw [MeasureTheory.integral_add (hSmallInt'.add hLowInt') hBadInt]
      _ = ∫ a, smallTerm a + lowSum a ∂P +
            ∫ a, badTerm a ∂P := by rfl
      _ = (∫ a, smallTerm a ∂P + ∫ a, lowSum a ∂P) +
            ∫ a, badTerm a ∂P := by
            rw [MeasureTheory.integral_add hSmallInt' hLowInt']
      _ ≤ (∫ a, smallTerm a ∂P + ∫ a, lowSum a ∂P) + sourceTerm := by
            linarith only [hBadBound]
      _ = ∫ a, smallTerm a ∂P + ∫ a, lowSum a ∂P + sourceTerm := by ring
  have hpositive_split :
      σ * (∫ a, lowerZero a * childAvg a ∂P) +
          σ⁻¹ * (∫ a, upperZero a * childAvg a ∂P)
        ≤
          ∫ a, smallTerm a ∂P +
          ∫ a, lowSum a ∂P +
          sourceTerm := by
    have hzero_split :
        ∫ a, (σ * lowerZero a + σ⁻¹ * upperZero a) * childAvg a ∂P =
          σ * (∫ a, lowerZero a * childAvg a ∂P) +
            σ⁻¹ * (∫ a, upperZero a * childAvg a ∂P) := by
      simpa only [β, s', t', Q, p_e, q_e, σ, childAvg, lowerZero, upperZero] using
        integral_zeroBaselinePositiveExcess_childAverage_split_special_of_P4
          hP hstat hStruct hP4 hkm e
    calc
      σ * (∫ a, lowerZero a * childAvg a ∂P) +
          σ⁻¹ * (∫ a, upperZero a * childAvg a ∂P)
          =
        ∫ a, (σ * lowerZero a + σ⁻¹ * upperZero a) * childAvg a ∂P :=
          hzero_split.symm
      _ ≤ ∫ a, terminalChild a ∂P := hzero_le_terminal
      _ ≤ ∫ a, terminalResponse a ∂P := hterminal_child_le_response
      _ ≤ ∫ a, smallTerm a ∂P + ∫ a, lowSum a ∂P + sourceTerm :=
          hterminal_response_bound
  have hpositive_le :
      tailFactor *
          (σ * (∫ a, lowerZero a * childAvg a ∂P) +
            σ⁻¹ * (∫ a, upperZero a * childAvg a ∂P))
        ≤
          tailFactor *
            (∫ a, smallTerm a ∂P +
              ∫ a, lowSum a ∂P +
              sourceTerm) :=
    mul_le_mul_of_nonneg_left hpositive_split htail_nonneg
  have hlocal_raw :
      lowScaleTail ≤
        responseBaselineCoeff * responseTerm +
          tailFactor * ∫ a, terminalChild a ∂P := by
    simpa only [β, s, s', t, t', Q, p_e, q_e, σ, childAvg, lowerTerminal,
      upperTerminal, terminalChild, tailFactor, responseBaselineCoeff,
      responseTerm, lowScaleTail] using
      integral_paired_lowScaleTailSquares_special_le_localResponseBaseline_add_terminalPositiveExcess_childAverage
        hP hstat hStruct hP4 hkm e
  have hterminal_child_budget :
      ∫ a, terminalChild a ∂P ≤
        ∫ a, smallTerm a ∂P + ∫ a, lowSum a ∂P + sourceTerm :=
    hterminal_child_le_response.trans hterminal_response_bound
  have hmain :
      lowScaleTail ≤
        responseBaselineCoeff * responseTerm +
          tailFactor *
            (∫ a, smallTerm a ∂P +
              ∫ a, lowSum a ∂P +
              sourceTerm) := by
    calc
      lowScaleTail ≤
          responseBaselineCoeff * responseTerm +
            tailFactor * ∫ a, terminalChild a ∂P := hlocal_raw
      _ ≤ responseBaselineCoeff * responseTerm +
          tailFactor *
            (∫ a, smallTerm a ∂P +
              ∫ a, lowSum a ∂P +
              sourceTerm) := by
          exact add_le_add le_rfl
            (mul_le_mul_of_nonneg_left hterminal_child_budget htail_nonneg)
  simpa only [β, s, s', t, t', S, Q, p_e, q_e, σ, childAvg, response,
    lowScaleTail, tailFactor, responseBaselineCoeff, responseTerm, lowerSmall,
    upperSmall, lowerSlot, upperSlot, lowSum, sourceMax, weightLossSup,
    edgeWeightLoss, sourceTerm, smallTerm] using hmain

end

end Homogenization.HighContrast.EntryScale
