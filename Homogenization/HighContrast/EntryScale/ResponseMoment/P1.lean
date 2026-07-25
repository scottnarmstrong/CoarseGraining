import Homogenization.CoarseGraining.AdjointSymmetry.BasicAdjoint
import Homogenization.Book.Ch04.Theorems.CoarseObservables
import Homogenization.Book.Ch04.Theorems.DilationResponse
import Homogenization.HighContrast.EntryScale.ResponseFluctuation

open MeasureTheory
open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization.Book.Ch05.Section54.OneStepContraction
open scoped Matrix.Norms.Elementwise


/-!
# Response-moment bridges for the entry-scale window

Local LeanIntoHomogenization-facing response estimates needed for the
`e.J.moment.bound` half of `l.S.and.J` in the high-moment paper
(Armstrong–Kuusi–Loher, in preparation).
-/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace OneStepContraction

open MeasureTheory
open scoped BigOperators
open Section53.JUpperBoundCoarseFluctuations

private theorem responseMoment_blockPosDef_quadratic_nonneg
    {d : ℕ} {A : BlockMat d} (hA : Ch02.BlockPosDef A) (X : BlockVec d) :
    0 ≤ blockVecDot X (blockMatVecMul A X) := by
  by_cases hX : X = 0
  · subst X
    simp [blockVecDot, blockMatVecMul, vecDot, matVecMul]
  · exact (hA X hX).le

/-- Mixed response block terms are controlled by the two diagonal quadratics. -/
theorem responseMoment_block_cross_abs_le_half_quadratics
    {d : ℕ} {A : BlockMat d} (hSymm : IsSymmetricBlockMat A)
    (hPos : Ch02.BlockPosDef A) (p q : Vec d) :
    |vecDot q (matVecMul A.lowerLeft p)| ≤
      (1 / 2 : ℝ) *
        (vecDot p (matVecMul A.upperLeft p) +
          vecDot q (matVecMul A.lowerRight q)) := by
  let X : BlockVec d := (0, q)
  let Y : BlockVec d := (p, 0)
  have hcomm :
      blockVecDot Y (blockMatVecMul A X) =
        blockVecDot X (blockMatVecMul A Y) := by
    exact (blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat hSymm Y X)
  have hXX :
      blockVecDot X (blockMatVecMul A X) =
        vecDot q (matVecMul A.lowerRight q) := by
    simp [X, blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left]
  have hYY :
      blockVecDot Y (blockMatVecMul A Y) =
        vecDot p (matVecMul A.upperLeft p) := by
    simp [Y, blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left]
  have hXY :
      blockVecDot X (blockMatVecMul A Y) =
        vecDot q (matVecMul A.lowerLeft p) := by
    simp [X, Y, blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left]
  have hYX :
      blockVecDot Y (blockMatVecMul A X) =
        vecDot q (matVecMul A.lowerLeft p) := by
    rw [hcomm, hXY]
  let z := vecDot q (matVecMul A.lowerLeft p)
  let a := vecDot q (matVecMul A.lowerRight q)
  let b := vecDot p (matVecMul A.upperLeft p)
  have hplus :
      0 ≤ a + z + z + b := by
    have hnonneg := responseMoment_blockPosDef_quadratic_nonneg hPos (X + Y)
    have hraw :
        0 ≤ a + z + (z + b) := by
      simpa [z, a, b, blockMatVecMul_add, blockVecDot_add_left,
        blockVecDot_add_right, hXX, hYY, hXY, hYX] using hnonneg
    nlinarith
  have hminus :
      0 ≤ a - z - z + b := by
    have hnonneg := responseMoment_blockPosDef_quadratic_nonneg hPos (X - Y)
    have hnegMul : blockMatVecMul A (-Y) = -blockMatVecMul A Y := by
      simpa using blockMatVecMul_smul A (-1) Y
    have hnegDotL :
        blockVecDot (-Y) (blockMatVecMul A X) =
          -blockVecDot Y (blockMatVecMul A X) := by
      simpa using blockVecDot_smul_left (-1) Y (blockMatVecMul A X)
    have hnegDotR :
        blockVecDot X (-blockMatVecMul A Y) =
          -blockVecDot X (blockMatVecMul A Y) := by
      simpa using blockVecDot_smul_right X (blockMatVecMul A Y) (-1)
    have hnegYY :
        blockVecDot (-Y) (-blockMatVecMul A Y) =
          blockVecDot Y (blockMatVecMul A Y) := by
      calc
        blockVecDot (-Y) (-blockMatVecMul A Y) =
            -blockVecDot (-Y) (blockMatVecMul A Y) := by
              simpa using blockVecDot_smul_right (-Y) (blockMatVecMul A Y) (-1)
        _ = blockVecDot Y (blockMatVecMul A Y) := by
              rw [show blockVecDot (-Y) (blockMatVecMul A Y) =
                  -blockVecDot Y (blockMatVecMul A Y) by
                    simpa using blockVecDot_smul_left (-1) Y (blockMatVecMul A Y)]
              ring
    have hraw :
        0 ≤ a + -z + (-z + b) := by
      simpa [sub_eq_add_neg, z, a, b, blockMatVecMul_add, hnegMul,
        blockVecDot_add_left, blockVecDot_add_right, hXX, hYY, hXY, hYX,
        hnegDotL, hnegDotR, hnegYY] using hnonneg
    nlinarith
  have habs : 2 * |z| ≤ a + b := by
    have hz_abs : |z| ≤ (a + b) / 2 := by
      rw [abs_le]
      constructor <;> nlinarith
    nlinarith
  have htarget : |z| ≤ (1 / 2 : ℝ) * (b + a) := by
    nlinarith
  simpa [z, a, b, add_comm] using htarget

/--
Moment-root comparison used to turn an a.e. nonnegative bound at exponent
`zeta` into a natural-exponent annealed moment root bound.
-/
theorem responseMoment_realRpowMomentRoot_le_natAnnealedMomentRoot_of_ae_le
    {d : ℕ} {P : Ch04.CoeffLaw d} [IsProbabilityMeasure P]
    {ζ : ℝ} {ξ : ℕ} {X Y : RegCoeffField d → ℝ}
    (hζ_pos : 0 < ζ) (hζ_le_ξ : ζ ≤ (ξ : ℝ)) (hξ_one : 1 ≤ ξ)
    (hX_meas : AEMeasurable X P)
    (hX_nonneg : ∀ a, 0 ≤ X a) (hY_nonneg : ∀ a, 0 ≤ Y a)
    (hY_memξ : MemLp Y (ξ : ENNReal) P)
    (hXY : X ≤ᵐ[P] Y) :
    Real.rpow (∫ a, Real.rpow (X a) ζ ∂P) ζ⁻¹ ≤
      Ch04.annealedMomentRoot P ξ Y := by
  have hζ_ne_zero : ENNReal.ofReal ζ ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le.mpr hζ_pos]
  have hζ_ne_top : ENNReal.ofReal ζ ≠ ⊤ := by
    simp
  have hζ_le_enn : ENNReal.ofReal ζ ≤ (ξ : ENNReal) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hζ_le_ξ
  have hY_memζ : MemLp Y (ENNReal.ofReal ζ) P :=
    hY_memξ.mono_exponent hζ_le_enn
  have hX_memζ : MemLp X (ENNReal.ofReal ζ) P := by
    refine hY_memζ.mono hX_meas.aestronglyMeasurable ?_
    filter_upwards [hXY] with a hle
    rw [Real.norm_of_nonneg (hX_nonneg a),
      Real.norm_of_nonneg (hY_nonneg a)]
    exact hle
  have hcmp₁ :
      eLpNorm X (ENNReal.ofReal ζ) P ≤
        eLpNorm Y (ENNReal.ofReal ζ) P := by
    refine eLpNorm_mono_ae ?_
    filter_upwards [hXY] with a hle
    rw [Real.norm_of_nonneg (hX_nonneg a),
      Real.norm_of_nonneg (hY_nonneg a)]
    exact hle
  have hcmp₂ :
      eLpNorm Y (ENNReal.ofReal ζ) P ≤ eLpNorm Y (ξ : ENNReal) P :=
    eLpNorm_le_eLpNorm_of_exponent_le hζ_le_enn
      hY_memξ.aestronglyMeasurable
  have hcmp :
      eLpNorm X (ENNReal.ofReal ζ) P ≤ eLpNorm Y (ξ : ENNReal) P :=
    hcmp₁.trans hcmp₂
  have hcmp_toReal :
      (eLpNorm X (ENNReal.ofReal ζ) P).toReal ≤
        (eLpNorm Y (ξ : ENNReal) P).toReal :=
    ENNReal.toReal_mono hY_memξ.2.ne hcmp
  have hleft :
      (eLpNorm X (ENNReal.ofReal ζ) P).toReal =
        Real.rpow (∫ a, Real.rpow (X a) ζ ∂P) ζ⁻¹ := by
    rw [hX_memζ.eLpNorm_eq_integral_rpow_norm hζ_ne_zero hζ_ne_top]
    have hnonneg :
        0 ≤
          (∫ a, ‖X a‖ ^ (ENNReal.ofReal ζ).toReal ∂P) ^
            (ENNReal.ofReal ζ).toReal⁻¹ := by
      positivity
    rw [ENNReal.toReal_ofReal hnonneg]
    congr 1
    · exact integral_congr_ae (by
        filter_upwards with a
        rw [ENNReal.toReal_ofReal hζ_pos.le,
          Real.norm_of_nonneg (hX_nonneg a), Real.rpow_eq_pow])
    · rw [ENNReal.toReal_ofReal hζ_pos.le]
  have hright :
      (eLpNorm Y (ξ : ENNReal) P).toReal =
        Ch04.annealedMomentRoot P ξ Y := by
    calc
      (eLpNorm Y (ξ : ENNReal) P).toReal =
          (∫ a, ‖Y a‖ ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := by
            exact Ch04.toReal_eLpNorm_eq_integral_norm_pow_rpow_inv
              (μ := P) (f := Y) (p := ξ) hξ_one hY_memξ
      _ = (∫ a, Y a ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := by
            congr 1
            exact integral_congr_ae (by
              filter_upwards with a
              rw [Real.norm_of_nonneg (hY_nonneg a)])
      _ = Ch04.annealedMomentRoot P ξ Y := rfl
  calc
    Real.rpow (∫ a, Real.rpow (X a) ζ ∂P) ζ⁻¹ =
        (eLpNorm X (ENNReal.ofReal ζ) P).toReal := hleft.symm
    _ ≤ (eLpNorm Y (ξ : ENNReal) P).toReal := hcmp_toReal
    _ = Ch04.annealedMomentRoot P ξ Y := hright

/--
Source label `p.HC.CR`: the Section 5.3 response moment transports through
scale normalization at the left endpoint of the window.
-/
theorem coarseFluctuationResponseMomentAtScale_scaleNormalizedLaw_of_le
    {d : ℕ} [NeZero d] {P : Ch04.CoeffLaw d}
    (hP : Ch04.LawCarrier P) (hStruct : Ch04.StructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k ≤ m) (e : Vec d) :
    coarseFluctuationResponseMomentAtScale
        (hP.scaleNormalized k) (hStruct.scaleNormalized k)
        (hP4.scaleNormalized hP hStruct k) 0 (m - k) e =
      coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
  let M : ℕ := m - k
  let ζ := section53CoarseFluctuationZeta hP4
  let pN := specialPAtScale
    (hP.scaleNormalized k) (hStruct.scaleNormalized k) (M : ℤ) e
  let qN := specialQAtScale
    (hP.scaleNormalized k) (hStruct.scaleNormalized k) (M : ℤ) e
  let p := specialPAtScale hP hStruct (m : ℤ) e
  let q := specialQAtScale hP hStruct (m : ℤ) e
  have hζ_nonneg : 0 ≤ ζ := (section53CoarseFluctuationZeta_pos hP4).le
  have hsum : k + M = m := by
    dsimp [M]
    exact Nat.add_sub_of_le hkm
  have hsigma :
      sigmaHatAtScale
          (hP.scaleNormalized k) (hStruct.scaleNormalized k) (M : ℤ) =
        sigmaHatAtScale hP hStruct (m : ℤ) := by
    simp [sigmaHatAtScale,
      hP.barSigmaAtScale_scaleNormalizedLaw hStruct k M,
      hP.barSigmaStarAtScale_scaleNormalizedLaw hStruct k M,
      hsum]
  have hp : pN = p := by
    change
      Real.rpow
          (sigmaHatAtScale
            (hP.scaleNormalized k) (hStruct.scaleNormalized k) (M : ℤ))
          (-(1 / 2 : ℝ)) • e =
        Real.rpow (sigmaHatAtScale hP hStruct (m : ℤ)) (-(1 / 2 : ℝ)) • e
    rw [hsigma]
  have hq : qN = q := by
    change
      Real.rpow
          (sigmaHatAtScale
            (hP.scaleNormalized k) (hStruct.scaleNormalized k) (M : ℤ))
          (1 / 2 : ℝ) • e =
        Real.rpow (sigmaHatAtScale hP hStruct (m : ℤ)) (1 / 2 : ℝ) • e
    rw [hsigma]
  change
    Real.rpow
        (∫ a,
          Real.rpow
            (Ch04.responseJObservableCubeSet (originCube d (0 : ℤ)) pN qN a) ζ
          ∂Ch04.scaleNormalizedLaw k P)
        ζ⁻¹ =
      Real.rpow
        (∫ a,
          Real.rpow
            (Ch04.responseJObservableCubeSet (originCube d (k : ℤ)) p q a) ζ
          ∂P)
        ζ⁻¹
  rw [hp, hq]
  apply congrArg (fun x : ℝ => Real.rpow x ζ⁻¹)
  let X : RegCoeffField d → ℝ := fun a =>
    Real.rpow (Ch04.responseJObservableCubeSet (originCube d (0 : ℤ)) p q a) ζ
  have hX_meas : AEStronglyMeasurable X (Ch04.scaleNormalizedLaw k P) := by
    dsimp [X]
    exact ((Real.continuous_rpow_const hζ_nonneg).measurable.comp_aemeasurable
      ((hP.scaleNormalized k).aemeasurable_responseJObservableCubeSet
        (originCube d (0 : ℤ)) p q)).aestronglyMeasurable
  change ∫ a, X a ∂Ch04.scaleNormalizedLaw k P =
    ∫ a, Real.rpow
      (Ch04.responseJObservableCubeSet (originCube d (k : ℤ)) p q a) ζ ∂P
  rw [Ch04.integral_scaleNormalizedLaw k X hX_meas]
  apply integral_congr_ae
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  dsimp [X]
  have hresp :=
    Ch04.responseJObservableCubeSet_dilateCoeffField_neg_nat_of_aelocallyUniformlyElliptic
      ha k (originCube d (0 : ℤ)) p q
  have hcube :
      Ch02.dilateCube (k : ℤ) (originCube d (0 : ℤ)) =
        originCube d (k : ℤ) := by
    simpa using Ch04.dilateCube_originCube_nat (d := d) k 0
  have hinside :
      Ch04.responseJObservableCubeSet (originCube d (0 : ℤ)) p q
          (dilateReg (-(k : ℤ)) a) =
        Ch04.responseJObservableCubeSet (originCube d (k : ℤ)) p q a := by
    rw [hresp, hcube]
  simpa [Ch04.responseJObservableCubeSet] using
    congrArg (fun x : ℝ => Real.rpow x ζ) hinside
end OneStepContraction
end Section54
end Ch05
end Book
end Homogenization

namespace Homogenization.HighContrast.EntryScale

private theorem integral_le_real_rpow_momentRoot_of_ae_nonneg
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {p : ℝ} {X : α → ℝ}
    (hp : 1 ≤ p)
    (hX_meas : AEMeasurable X μ)
    (hX_nonneg : ∀ᵐ a ∂μ, 0 ≤ X a)
    (hXpow_int : MeasureTheory.Integrable (fun a => Real.rpow (X a) p) μ) :
    ∫ a, X a ∂μ ≤ Real.rpow (∫ a, Real.rpow (X a) p ∂μ) p⁻¹ := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp_ne_zero : ENNReal.ofReal p ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le.mpr hp_pos]
  have hp_ne_top : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hnormpow_int :
      MeasureTheory.Integrable
        (fun a => ‖X a‖ ^ (ENNReal.ofReal p).toReal) μ := by
    refine hXpow_int.congr ?_
    filter_upwards [hX_nonneg] with a ha
    simp [ENNReal.toReal_ofReal hp_pos.le, Real.norm_eq_abs,
      abs_of_nonneg ha]
  have hmem_p : MeasureTheory.MemLp X (ENNReal.ofReal p) μ := by
    rw [← MeasureTheory.integrable_norm_rpow_iff
      hX_meas.aestronglyMeasurable hp_ne_zero hp_ne_top]
    exact hnormpow_int
  have hp_enn : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    simpa [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hmem_one : MeasureTheory.MemLp X (1 : ENNReal) μ :=
    hmem_p.mono_exponent hp_enn
  have hX_int : MeasureTheory.Integrable X μ := by
    rwa [MeasureTheory.memLp_one_iff_integrable] at hmem_one
  have hX_norm_int : MeasureTheory.Integrable (fun a => ‖X a‖) μ := hX_int.norm
  have hint_le_norm : ∫ a, X a ∂μ ≤ ∫ a, ‖X a‖ ∂μ :=
    MeasureTheory.integral_mono_ae hX_int hX_norm_int
      (Filter.Eventually.of_forall fun a => by
        simpa [Real.norm_eq_abs] using le_abs_self (X a))
  have hcmp :
      MeasureTheory.eLpNorm X (1 : ENNReal) μ ≤
        MeasureTheory.eLpNorm X (ENNReal.ofReal p) μ :=
    MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le hp_enn
      hX_meas.aestronglyMeasurable
  have hcmp_toReal :
      (MeasureTheory.eLpNorm X (1 : ENNReal) μ).toReal ≤
        (MeasureTheory.eLpNorm X (ENNReal.ofReal p) μ).toReal :=
    ENNReal.toReal_mono hmem_p.2.ne hcmp
  have hL1 :
      (MeasureTheory.eLpNorm X (1 : ENNReal) μ).toReal =
        ∫ a, ‖X a‖ ∂μ := by
    rw [hmem_one.eLpNorm_eq_integral_rpow_norm one_ne_zero
      ENNReal.one_ne_top]
    have hroot_nonneg :
        0 ≤
          (∫ a, ‖X a‖ ^ (1 : ENNReal).toReal ∂μ) ^
            ((1 : ENNReal).toReal)⁻¹ := by
      positivity
    rw [ENNReal.toReal_ofReal hroot_nonneg]
    simp
  have hLp :
      (MeasureTheory.eLpNorm X (ENNReal.ofReal p) μ).toReal =
        Real.rpow (∫ a, Real.rpow (X a) p ∂μ) p⁻¹ := by
    rw [hmem_p.eLpNorm_eq_integral_rpow_norm hp_ne_zero hp_ne_top]
    have hroot_nonneg :
        0 ≤
          (∫ a, ‖X a‖ ^ (ENNReal.ofReal p).toReal ∂μ) ^
            ((ENNReal.ofReal p).toReal)⁻¹ := by
      positivity
    rw [ENNReal.toReal_ofReal hroot_nonneg]
    rw [ENNReal.toReal_ofReal hp_pos.le]
    congr 1
    exact MeasureTheory.integral_congr_ae (by
      filter_upwards [hX_nonneg] with a ha
      simp [Real.norm_eq_abs, abs_of_nonneg ha])
  calc
    ∫ a, X a ∂μ ≤ ∫ a, ‖X a‖ ∂μ := hint_le_norm
    _ = (MeasureTheory.eLpNorm X (1 : ENNReal) μ).toReal := hL1.symm
    _ ≤ (MeasureTheory.eLpNorm X (ENNReal.ofReal p) μ).toReal := hcmp_toReal
    _ = Real.rpow (∫ a, Real.rpow (X a) p ∂μ) p⁻¹ := hLp

/--
Source label `p.HC.CR`: the lower-edge response expectation is bounded by
the Section 5.3 response moment kept in the manuscript terminal slot.
-/
theorem expectedResponseJCubeSet_le_coarseFluctuationResponseMomentAtScale
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Homogenization.Vec d) :
    let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    Homogenization.Book.Ch04.expectedResponseJCubeSet P
        (Homogenization.originCube d (k : ℤ)) p_e q_e ≤
      coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  dsimp only
  let ζ := section53CoarseFluctuationZeta hP4
  let X : Homogenization.RegCoeffField d → ℝ := fun a =>
    Homogenization.Book.Ch04.responseJObservableCubeSet
      (Homogenization.originCube d (k : ℤ))
      (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
      (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) a
  have hζ_one : 1 ≤ ζ :=
    (one_lt_section53CoarseFluctuationZeta hP4).le
  have hX_meas : AEMeasurable X P := by
    simpa [X] using
      hP.aemeasurable_responseJObservableCubeSet
        (Homogenization.originCube d (k : ℤ))
        (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
        (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e)
  have hX_nonneg : ∀ᵐ a ∂P, 0 ≤ X a :=
    Filter.Eventually.of_forall fun a => by
      dsimp [X]
      exact
        Homogenization.Book.Ch04.responseJObservableCubeSet_nonneg
          (Homogenization.originCube d (k : ℤ))
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) a
  have hXpow_int :
      MeasureTheory.Integrable (fun a => Real.rpow (X a) ζ) P := by
    simpa [X, ζ] using
      Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.integrable_rpow_responseJObservableCubeSet_originCube_from_P4
        hP hStruct hP4 k
        (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
        (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e)
  have hroot :=
    integral_le_real_rpow_momentRoot_of_ae_nonneg
      (μ := P) (p := ζ) (X := X) hζ_one hX_meas hX_nonneg hXpow_int
  simpa [Homogenization.Book.Ch04.expectedResponseJCubeSet,
    coarseFluctuationResponseMomentAtScale, X, ζ] using hroot

/--
Source label `p.HC.CR`: the parent terminal response expectation can be kept
as a lower-edge response moment.  This is the primitive replacement for the
low-tail baseline conversion
`expectedResponseJCubeSet(origin m) <= theta_m - 1`.
-/
theorem expectedResponseJCubeSet_terminal_le_coarseFluctuationResponseMomentAtScale
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hstat : Homogenization.Book.Ch04.StationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k ≤ m) (e : Homogenization.Vec d) :
    let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    Homogenization.Book.Ch04.expectedResponseJCubeSet P
        (Homogenization.originCube d (m : ℤ)) p_e q_e ≤
      coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
  classical
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
  let Jm : Homogenization.RegCoeffField d → ℝ :=
    fun a =>
      Homogenization.Book.Ch04.responseJObservableCubeSet Q p_e q_e a
  let childAvg : Homogenization.RegCoeffField d → ℝ :=
    fun a =>
      Homogenization.descendantsAverage Q j
        (fun R =>
          Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by
    exact_mod_cast Nat.zero_le k
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by
    exact_mod_cast hkm
  have hOriginBlock :
      MeasureTheory.Integrable
        (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube
          (Homogenization.originCube d (k : ℤ))) P := by
    simpa using
      Homogenization.Book.Ch05.Section52.originBlockIntegrableAtScale_from_P4
        hP hStruct hP4 k
  have hChildJ :
      ∀ R, R ∈ Homogenization.descendantsAtScale
          (Homogenization.originCube d (m : ℤ)) (k : ℤ) →
        MeasureTheory.Integrable
          (Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e) P := by
    intro R hR
    have hBlockR :
        MeasureTheory.Integrable
          (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube R) P :=
      hP.integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
        hstat hk_nonneg hkm_int hR hOriginBlock
    exact
      hP.integrable_responseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
        R p_e q_e hBlockR
  have hChildJ_depth :
      ∀ R, R ∈ Homogenization.descendantsAtDepth Q j →
        MeasureTheory.Integrable
          (Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e) P := by
    intro R hR
    exact hChildJ R (by
      simpa [Q, j,
        Homogenization.descendantsAtScale_eq_descendantsAtDepth
          (Homogenization.originCube d (m : ℤ)) hkm_int] using hR)
  have hJmInt : MeasureTheory.Integrable Jm P := by
    have hBlock :
        MeasureTheory.Integrable
          (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube Q) P := by
      simpa [Q] using
        Homogenization.Book.Ch05.Section52.originBlockIntegrableAtScale_from_P4
          hP hStruct hP4 m
    simpa [Jm] using
      hP.integrable_responseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
        Q p_e q_e hBlock
  have hChildInt : MeasureTheory.Integrable childAvg P := by
    simpa [childAvg, Q, j] using
      Homogenization.Book.Ch04.integrable_descendantsAverage
        (Q := Q) (j := j)
        (F := fun R a =>
          Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
        hChildJ_depth
  have hParent_le_child : Jm ≤ᵐ[P] childAvg := by
    simpa [Jm, childAvg, Q, j] using
      hP.responseJObservableCubeSet_le_descendantsAverage_ae hkm_int p_e q_e
  have hparent_integral_le :
      ∫ a, Jm a ∂P ≤ ∫ a, childAvg a ∂P :=
    MeasureTheory.integral_mono_ae hJmInt hChildInt hParent_le_child
  have hchild_integral_eq :
      ∫ a, childAvg a ∂P =
        Homogenization.Book.Ch04.expectedResponseJCubeSet P
          (Homogenization.originCube d (k : ℤ)) p_e q_e := by
    simpa [childAvg, Q, j] using
      hP.integral_descendantsAverage_responseJObservableCubeSet_eq_originCube_of_stationary
        hstat hk_nonneg hkm_int p_e q_e hChildJ
  have hlower :
      Homogenization.Book.Ch04.expectedResponseJCubeSet P
          (Homogenization.originCube d (k : ℤ)) p_e q_e ≤
        coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
    simpa [p_e, q_e] using
      expectedResponseJCubeSet_le_coarseFluctuationResponseMomentAtScale
        hP hStruct hP4 k m e
  calc
    Homogenization.Book.Ch04.expectedResponseJCubeSet P
        (Homogenization.originCube d (m : ℤ)) p_e q_e
        = ∫ a, Jm a ∂P := by
          simp [Homogenization.Book.Ch04.expectedResponseJCubeSet, Jm, Q]
    _ ≤ ∫ a, childAvg a ∂P := hparent_integral_le
    _ =
        Homogenization.Book.Ch04.expectedResponseJCubeSet P
          (Homogenization.originCube d (k : ℤ)) p_e q_e :=
        hchild_integral_eq
    _ ≤ coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e :=
        hlower

/--
Source labels `p.HC.CR` and `e.J.moment.bound`: the descendant average of the
terminal response observable over the `k`-scale children is integrable, and its
expectation is bounded by the lower-edge response moment.  This is the
good-event response branch used in the terminal positive-excess proof.
-/
theorem integrable_terminalDescendantsAverage_responseJObservableCubeSet_and_integral_le
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hstat : Homogenization.Book.Ch04.StationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k ≤ m) (e : Homogenization.Vec d) :
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let childAvg := fun a : Homogenization.RegCoeffField d =>
      Homogenization.descendantsAverage Q (m - k)
        (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
    MeasureTheory.Integrable childAvg P ∧
      ∫ a, childAvg a ∂P ≤
        coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
  classical
  dsimp only
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
  let childAvg : Homogenization.RegCoeffField d → ℝ :=
    fun a =>
      Homogenization.descendantsAverage Q j
        (fun R =>
          Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by
    exact_mod_cast Nat.zero_le k
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by
    exact_mod_cast hkm
  have hOriginBlock :
      MeasureTheory.Integrable
        (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube
          (Homogenization.originCube d (k : ℤ))) P := by
    simpa using
      Homogenization.Book.Ch05.Section52.originBlockIntegrableAtScale_from_P4
        hP hStruct hP4 k
  have hChildJ :
      ∀ R, R ∈ Homogenization.descendantsAtScale
          (Homogenization.originCube d (m : ℤ)) (k : ℤ) →
        MeasureTheory.Integrable
          (Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e) P := by
    intro R hR
    have hBlockR :
        MeasureTheory.Integrable
          (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube R) P :=
      hP.integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
        hstat hk_nonneg hkm_int hR hOriginBlock
    exact
      hP.integrable_responseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
        R p_e q_e hBlockR
  have hChildJ_depth :
      ∀ R, R ∈ Homogenization.descendantsAtDepth Q j →
        MeasureTheory.Integrable
          (Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e) P := by
    intro R hR
    exact hChildJ R (by
      simpa [Q, j,
        Homogenization.descendantsAtScale_eq_descendantsAtDepth
          (Homogenization.originCube d (m : ℤ)) hkm_int] using hR)
  have hChildInt : MeasureTheory.Integrable childAvg P := by
    simpa [childAvg, Q, j] using
      Homogenization.Book.Ch04.integrable_descendantsAverage
        (Q := Q) (j := j)
        (F := fun R a =>
          Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
        hChildJ_depth
  have hchild_integral_eq :
      ∫ a, childAvg a ∂P =
        Homogenization.Book.Ch04.expectedResponseJCubeSet P
          (Homogenization.originCube d (k : ℤ)) p_e q_e := by
    simpa [childAvg, Q, j] using
      hP.integral_descendantsAverage_responseJObservableCubeSet_eq_originCube_of_stationary
        hstat hk_nonneg hkm_int p_e q_e hChildJ
  have hlower :
      Homogenization.Book.Ch04.expectedResponseJCubeSet P
          (Homogenization.originCube d (k : ℤ)) p_e q_e ≤
        coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
    simpa [p_e, q_e] using
      expectedResponseJCubeSet_le_coarseFluctuationResponseMomentAtScale
        hP hStruct hP4 k m e
  have hbound :
      ∫ a, childAvg a ∂P ≤
        coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
    calc
      ∫ a, childAvg a ∂P =
          Homogenization.Book.Ch04.expectedResponseJCubeSet P
            (Homogenization.originCube d (k : ℤ)) p_e q_e :=
          hchild_integral_eq
      _ ≤ coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e :=
          hlower
  exact
    ⟨by simpa [childAvg, Q, j, p_e, q_e] using hChildInt,
      by simpa [childAvg, Q, j, p_e, q_e] using hbound⟩

/--
Source label `e.J.moment.bound`: the adjoint/star response moment from the
manuscript's paired `J` and `J^*` estimate at the lower edge of a no-drop
window.  This is the Section 5.3 response moment with the coefficient field
composed with `adjointCoeffField`.
-/
noncomputable def coarseFluctuationResponseMomentStarAtScale
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Homogenization.Vec d) : ℝ :=
  let ζ := section53CoarseFluctuationZeta hP4
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  Real.rpow
    (∫ a,
      Real.rpow
        (Homogenization.Book.Ch04.responseJObservableCubeSet
          (Homogenization.originCube d (k : ℤ)) p_e q_e
          (Homogenization.adjointReg a)) ζ ∂P)
    ζ⁻¹

/-- Nonnegativity of the adjoint/star response moment term. -/
theorem coarseFluctuationResponseMomentStarAtScale_nonneg
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Homogenization.Vec d) :
    0 ≤ coarseFluctuationResponseMomentStarAtScale hP hStruct hP4 k m e := by
  dsimp [coarseFluctuationResponseMomentStarAtScale]
  let ζ := section53CoarseFluctuationZeta hP4
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  have hJpow_nonneg :
      ∀ a : Homogenization.RegCoeffField d,
        0 ≤ Real.rpow
          (Homogenization.Book.Ch04.responseJObservableCubeSet
            (Homogenization.originCube d (k : ℤ)) p_e q_e
            (Homogenization.adjointReg a)) ζ := by
    intro a
    exact Real.rpow_nonneg
        (Homogenization.Book.Ch04.responseJObservableCubeSet_nonneg
        (Homogenization.originCube d (k : ℤ)) p_e q_e
        (Homogenization.adjointReg a)) _
  exact Real.rpow_nonneg (integral_nonneg hJpow_nonneg) _

/--
In the adjoint-invariant structural setting, the star response moment is the
ordinary response moment.  This is the moment-level form of the
homogenization repo's centered `J = J^*` symmetry.
-/
theorem coarseFluctuationResponseMomentStarAtScale_eq_responseMomentAtScale
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Homogenization.Vec d) :
    coarseFluctuationResponseMomentStarAtScale hP hStruct hP4 k m e =
      coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
  let ζ := section53CoarseFluctuationZeta hP4
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (k : ℤ)
  let f : Homogenization.RegCoeffField d → ℝ := fun a =>
    Real.rpow (Homogenization.Book.Ch04.responseJObservableCubeSet Q p_e q_e a) ζ
  have hζ_nonneg : 0 ≤ ζ := by
    exact (section53CoarseFluctuationZeta_pos hP4).le
  have hf_aemeas : AEMeasurable f P := by
    dsimp [f]
    exact (Real.continuous_rpow_const hζ_nonneg).measurable.comp_aemeasurable
      (hP.aemeasurable_responseJObservableCubeSet Q p_e q_e)
  have hint :
      ∫ a, f (Homogenization.adjointReg a) ∂P = ∫ a, f a ∂P :=
    hStruct.adjoint_invariant.integral_comp_adjointReg f
      hf_aemeas.aestronglyMeasurable
  change
    Real.rpow (∫ a, f (Homogenization.adjointReg a) ∂P) ζ⁻¹ =
      Real.rpow (∫ a, f a ∂P) ζ⁻¹
  rw [hint]

private def responseMomentFullBlockQuadratic {d : ℕ}
    (M : Homogenization.FullBlockMat d) (x : Homogenization.FullBlockVec d) :
    ℝ :=
  dotProduct x (Matrix.mulVec M x)

private theorem responseMomentFullBlockQuadratic_abs_le_operatorNorm_mul_dotProduct
    {d : ℕ} (M : Homogenization.FullBlockMat d)
    (x : Homogenization.FullBlockVec d) :
    |responseMomentFullBlockQuadratic M x| ≤
      fullBlockOperatorNorm M * dotProduct x x := by
  let X : PiLp 2 (fun _ : Homogenization.BlockCoord d => ℝ) := WithLp.toLp 2 x
  let Y : PiLp 2 (fun _ : Homogenization.BlockCoord d => ℝ) :=
    WithLp.toLp 2 (Matrix.mulVec M x)
  have hY :
      (Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
          (𝕜 := ℝ) M) X = Y := by
    simp [X, Y, Matrix.toEuclideanCLM_toLp]
  have hinner :
      inner ℝ X Y = responseMomentFullBlockQuadratic M x := by
    simp [X, Y, responseMomentFullBlockQuadratic, PiLp.inner_apply,
      dotProduct, mul_comm]
  have hnormY :
      ‖Y‖ ≤ fullBlockOperatorNorm M * ‖X‖ := by
    simpa [hY, fullBlockOperatorNorm] using
      (Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
        (𝕜 := ℝ) M).le_opNorm X
  have hnormX_sq :
      ‖X‖ ^ 2 = dotProduct x x := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [X, dotProduct, sq]
  calc
    |responseMomentFullBlockQuadratic M x| = |inner ℝ X Y| := by rw [hinner]
    _ ≤ ‖X‖ * ‖Y‖ := abs_real_inner_le_norm X Y
    _ ≤ ‖X‖ * (fullBlockOperatorNorm M * ‖X‖) := by
          exact mul_le_mul_of_nonneg_left hnormY (norm_nonneg X)
    _ = fullBlockOperatorNorm M * dotProduct x x := by
          rw [← hnormX_sq]
          ring

private theorem responseMoment_dotProduct_diagonal_mulVec_left_eq_right
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r x y : ι → ℝ) :
    dotProduct (Matrix.mulVec (Matrix.diagonal r) x) y =
      dotProduct x (Matrix.mulVec (Matrix.diagonal r) y) := by
  simp [dotProduct, Matrix.mulVec, Matrix.diagonal, mul_left_comm, mul_comm]

private theorem responseMomentFullBlockQuadratic_diagonal_conj
    {d : ℕ} (r : Homogenization.BlockCoord d → ℝ)
    (M : Homogenization.FullBlockMat d) (q : Homogenization.FullBlockVec d) :
    responseMomentFullBlockQuadratic
        (Matrix.diagonal r * M * Matrix.diagonal r) q =
      responseMomentFullBlockQuadratic M
        (Matrix.mulVec (Matrix.diagonal r) q) := by
  let D : Homogenization.FullBlockMat d := Matrix.diagonal r
  let y : Homogenization.FullBlockVec d := Matrix.mulVec M (Matrix.mulVec D q)
  have hmul : Matrix.mulVec (D * M * D) q = Matrix.mulVec D y := by
    calc
      Matrix.mulVec (D * M * D) q =
          Matrix.mulVec (D * M) (Matrix.mulVec D q) := by
            exact (Matrix.mulVec_mulVec q (D * M) D).symm
      _ = Matrix.mulVec D y := by
            change
              Matrix.mulVec (D * M) (Matrix.mulVec D q) =
                Matrix.mulVec D (Matrix.mulVec M (Matrix.mulVec D q))
            exact (Matrix.mulVec_mulVec (Matrix.mulVec D q) D M).symm
  calc
    responseMomentFullBlockQuadratic (Matrix.diagonal r * M * Matrix.diagonal r) q
        = dotProduct q (Matrix.mulVec D y) := by
          simp [responseMomentFullBlockQuadratic, D, y, hmul]
    _ = dotProduct (Matrix.mulVec D q) y :=
          (responseMoment_dotProduct_diagonal_mulVec_left_eq_right r q y).symm
    _ = responseMomentFullBlockQuadratic M (Matrix.mulVec (Matrix.diagonal r) q) := by
          simp [responseMomentFullBlockQuadratic, D, y]

private theorem responseMomentFullBlockQuadratic_toFullBlockMat
    {d : ℕ} (A : Homogenization.BlockMat d)
    (X : Homogenization.BlockVec d) :
    responseMomentFullBlockQuadratic
        (Homogenization.toFullBlockMat A) (Homogenization.toFullBlockVec X) =
      Homogenization.blockVecDot X (Homogenization.blockMatVecMul A X) := by
  unfold responseMomentFullBlockQuadratic
  rw [← Homogenization.toFullBlockVec_blockMatVecMul,
    Homogenization.dotProduct_toFullBlockVec]

private theorem responseMoment_upper_special_quad_le_sqrtTheta_terminalNorm
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (e : Homogenization.Vec d)
    (he : Homogenization.Book.Ch02.vecNorm e = 1)
    (A : Homogenization.BlockMat d) :
    let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let θ := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
    Homogenization.vecDot p_e (Homogenization.matVecMul A.upperLeft p_e) ≤
      Real.sqrt θ *
        fullBlockOperatorNorm
          (scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
            Homogenization.toFullBlockMat A *
            scalarFullBlockNormalizerMatrixAtScale hP hStruct m) := by
  classical
  dsimp only
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let b := hP.barSigmaAtScale hStruct (m : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let θ := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
  let D : Homogenization.FullBlockMat d :=
    scalarFullBlockNormalizerMatrixAtScale hP hStruct m
  let M : Homogenization.FullBlockMat d :=
    D * Homogenization.toFullBlockMat A * D
  let xu : Homogenization.FullBlockVec d :=
    Homogenization.toFullBlockVec ((Real.sqrt b) • p_e, 0)
  have hb : 0 < b := by
    simpa [b] using
      Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
        hP hStruct hP4 m
  have hc : 0 < c := by
    simpa [c] using
      Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
        hP hStruct hP4 m
  have hσ_pos : 0 < σ := by
    simpa [σ] using
      Homogenization.Book.Ch05.Section54.GoodScale.sigmaHatAtScale_pos_of_P4
        hP hStruct hP4 m
  have he_sq :
      Homogenization.vecNormSq e = 1 :=
    Homogenization.Book.Ch05.Section54.GoodScale.vecNormSq_eq_one_of_vecNorm_eq_one he
  have hp_norm :
      Homogenization.vecNormSq p_e = σ⁻¹ := by
    change
      Homogenization.vecNormSq
        (((Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)) ^
          (-(1 / 2 : ℝ))) • e) = σ⁻¹
    rw [show Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ) = σ by rfl]
    rw [Homogenization.vecNormSq_smul]
    rw [Homogenization.Book.Ch05.Section54.GoodScale.rpow_neg_half_sq_eq_inv
      hσ_pos, he_sq, mul_one]
  have hsqrt_factor :
      b * σ⁻¹ = Real.sqrt θ := by
    exact
      Homogenization.Book.Ch05.Section54.GoodScale.barSigma_mul_inv_sigma_eq_sqrt_theta
        hb hc (by rfl : σ = Real.sqrt (b * c))
        (by rfl : θ = b * c⁻¹)
  have hDxu :
      Matrix.mulVec D xu = Homogenization.toFullBlockVec (p_e, 0) := by
    funext α
    cases α with
    | inl i =>
        simp [D, xu, scalarFullBlockNormalizerMatrixAtScale,
          Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag,
          Matrix.mulVec, Matrix.diagonal, dotProduct, Homogenization.toFullBlockVec,
          b]
        field_simp [ne_of_gt (Real.sqrt_pos.mpr (by simpa [b] using hb))]
    | inr i =>
        simp [D, xu, scalarFullBlockNormalizerMatrixAtScale,
          Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag,
          Matrix.mulVec, Matrix.diagonal, dotProduct, Homogenization.toFullBlockVec]
  have hquad_eq :
      responseMomentFullBlockQuadratic M xu =
        Homogenization.vecDot p_e
          (Homogenization.matVecMul A.upperLeft p_e) := by
    calc
      responseMomentFullBlockQuadratic M xu =
          responseMomentFullBlockQuadratic
            (Homogenization.toFullBlockMat A) (Matrix.mulVec D xu) := by
            simpa [M, D, scalarFullBlockNormalizerMatrixAtScale, b, c] using
              responseMomentFullBlockQuadratic_diagonal_conj
                (r := Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag b c)
                (M := Homogenization.toFullBlockMat A) (q := xu)
      _ = responseMomentFullBlockQuadratic
            (Homogenization.toFullBlockMat A)
            (Homogenization.toFullBlockVec (p_e, 0)) := by
            rw [hDxu]
      _ = Homogenization.blockVecDot (p_e, 0)
            (Homogenization.blockMatVecMul A (p_e, 0)) := by
            exact responseMomentFullBlockQuadratic_toFullBlockMat A (p_e, 0)
      _ = Homogenization.vecDot p_e
            (Homogenization.matVecMul A.upperLeft p_e) := by
            simp [Homogenization.blockVecDot, Homogenization.blockMatVecMul,
              Homogenization.matVecMul_zero, Homogenization.vecDot_zero_left]
  have hxu_dot :
      dotProduct xu xu = Real.sqrt θ := by
    calc
      dotProduct xu xu =
          Homogenization.blockVecDot ((Real.sqrt b) • p_e, 0)
            ((Real.sqrt b) • p_e, 0) := by
            exact Homogenization.dotProduct_toFullBlockVec _ _
      _ = Homogenization.vecNormSq ((Real.sqrt b) • p_e) := by
            simp [Homogenization.blockVecDot, Homogenization.vecNormSq,
              Homogenization.vecDot_zero_left]
      _ = b * Homogenization.vecNormSq p_e := by
            rw [Homogenization.vecNormSq_smul]
            rw [Real.sq_sqrt hb.le]
      _ = b * σ⁻¹ := by rw [hp_norm]
      _ = Real.sqrt θ := hsqrt_factor
  have hquad_abs :=
    responseMomentFullBlockQuadratic_abs_le_operatorNorm_mul_dotProduct M xu
  calc
    Homogenization.vecDot p_e (Homogenization.matVecMul A.upperLeft p_e)
        = responseMomentFullBlockQuadratic M xu := hquad_eq.symm
    _ ≤ |responseMomentFullBlockQuadratic M xu| := le_abs_self _
    _ ≤ fullBlockOperatorNorm M * dotProduct xu xu := hquad_abs
    _ = fullBlockOperatorNorm M * Real.sqrt θ := by rw [hxu_dot]
    _ = Real.sqrt θ * fullBlockOperatorNorm M := by ring

private theorem responseMoment_lower_special_quad_le_sqrtTheta_terminalNorm
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (e : Homogenization.Vec d)
    (he : Homogenization.Book.Ch02.vecNorm e = 1)
    (A : Homogenization.BlockMat d) :
    let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let θ := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
    Homogenization.vecDot q_e (Homogenization.matVecMul A.lowerRight q_e) ≤
      Real.sqrt θ *
        fullBlockOperatorNorm
          (scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
            Homogenization.toFullBlockMat A *
            scalarFullBlockNormalizerMatrixAtScale hP hStruct m) := by
  classical
  dsimp only
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let b := hP.barSigmaAtScale hStruct (m : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let θ := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
  let D : Homogenization.FullBlockMat d :=
    scalarFullBlockNormalizerMatrixAtScale hP hStruct m
  let M : Homogenization.FullBlockMat d :=
    D * Homogenization.toFullBlockMat A * D
  let xl : Homogenization.FullBlockVec d :=
    Homogenization.toFullBlockVec (0, (Real.sqrt c)⁻¹ • q_e)
  have hb : 0 < b := by
    simpa [b] using
      Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
        hP hStruct hP4 m
  have hc : 0 < c := by
    simpa [c] using
      Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
        hP hStruct hP4 m
  have hσ_pos : 0 < σ := by
    simpa [σ] using
      Homogenization.Book.Ch05.Section54.GoodScale.sigmaHatAtScale_pos_of_P4
        hP hStruct hP4 m
  have he_sq :
      Homogenization.vecNormSq e = 1 :=
    Homogenization.Book.Ch05.Section54.GoodScale.vecNormSq_eq_one_of_vecNorm_eq_one he
  have hq_norm :
      Homogenization.vecNormSq q_e = σ := by
    change
      Homogenization.vecNormSq
        (((Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)) ^
          (1 / 2 : ℝ)) • e) = σ
    rw [show Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ) = σ by rfl]
    rw [Homogenization.vecNormSq_smul]
    rw [Homogenization.Book.Ch05.Section54.GoodScale.rpow_half_sq_eq_self
      hσ_pos, he_sq, mul_one]
  have hsqrt_factor :
      σ * c⁻¹ = Real.sqrt θ := by
    exact
      Homogenization.Book.Ch05.Section54.GoodScale.sigma_mul_inv_star_eq_sqrt_theta
        hb hc (by rfl : σ = Real.sqrt (b * c))
        (by rfl : θ = b * c⁻¹)
  have hDxl :
      Matrix.mulVec D xl = Homogenization.toFullBlockVec (0, q_e) := by
    funext α
    cases α with
    | inl i =>
        simp [D, xl, scalarFullBlockNormalizerMatrixAtScale,
          Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag,
          Matrix.mulVec, Matrix.diagonal, dotProduct, Homogenization.toFullBlockVec]
    | inr i =>
        simp [D, xl, scalarFullBlockNormalizerMatrixAtScale,
          Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag,
          Matrix.mulVec, Matrix.diagonal, dotProduct, Homogenization.toFullBlockVec,
          c]
        field_simp [ne_of_gt (Real.sqrt_pos.mpr (by simpa [c] using hc))]
  have hquad_eq :
      responseMomentFullBlockQuadratic M xl =
        Homogenization.vecDot q_e
          (Homogenization.matVecMul A.lowerRight q_e) := by
    calc
      responseMomentFullBlockQuadratic M xl =
          responseMomentFullBlockQuadratic
            (Homogenization.toFullBlockMat A) (Matrix.mulVec D xl) := by
            simpa [M, D, scalarFullBlockNormalizerMatrixAtScale, b, c] using
              responseMomentFullBlockQuadratic_diagonal_conj
                (r := Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag b c)
                (M := Homogenization.toFullBlockMat A) (q := xl)
      _ = responseMomentFullBlockQuadratic
            (Homogenization.toFullBlockMat A)
            (Homogenization.toFullBlockVec (0, q_e)) := by
            rw [hDxl]
      _ = Homogenization.blockVecDot (0, q_e)
            (Homogenization.blockMatVecMul A (0, q_e)) := by
            exact responseMomentFullBlockQuadratic_toFullBlockMat A (0, q_e)
      _ = Homogenization.vecDot q_e
            (Homogenization.matVecMul A.lowerRight q_e) := by
            simp [Homogenization.blockVecDot, Homogenization.blockMatVecMul,
              Homogenization.matVecMul_zero, Homogenization.vecDot_zero_left]
  have hxl_dot :
      dotProduct xl xl = Real.sqrt θ := by
    calc
      dotProduct xl xl =
          Homogenization.blockVecDot (0, (Real.sqrt c)⁻¹ • q_e)
            (0, (Real.sqrt c)⁻¹ • q_e) := by
            exact Homogenization.dotProduct_toFullBlockVec _ _
      _ = Homogenization.vecNormSq ((Real.sqrt c)⁻¹ • q_e) := by
            simp [Homogenization.blockVecDot, Homogenization.vecNormSq,
              Homogenization.vecDot_zero_left]
      _ = c⁻¹ * Homogenization.vecNormSq q_e := by
            rw [Homogenization.vecNormSq_smul]
            have hsqrt_sq : (Real.sqrt c) ^ 2 = c :=
              Real.sq_sqrt hc.le
            rw [inv_pow, hsqrt_sq]
      _ = c⁻¹ * σ := by rw [hq_norm]
      _ = Real.sqrt θ := by
            rw [mul_comm]
            exact hsqrt_factor
  have hquad_abs :=
    responseMomentFullBlockQuadratic_abs_le_operatorNorm_mul_dotProduct M xl
  calc
    Homogenization.vecDot q_e (Homogenization.matVecMul A.lowerRight q_e)
        = responseMomentFullBlockQuadratic M xl := hquad_eq.symm
    _ ≤ |responseMomentFullBlockQuadratic M xl| := le_abs_self _
    _ ≤ fullBlockOperatorNorm M * dotProduct xl xl := hquad_abs
    _ = fullBlockOperatorNorm M * Real.sqrt θ := by rw [hxl_dot]
    _ = Real.sqrt θ * fullBlockOperatorNorm M := by ring

/--
Source label `e.J.moment.bound`: uncentered terminal-normalized full-block
norm appearing in the pointwise response estimate
`|Ahom_m^{-1/2} A(cu_k) Ahom_m^{-1/2}|`.
-/
noncomputable def terminalUncenteredCoarseBlockNorm
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.RegCoeffField d) : ℝ :=
  fullBlockOperatorNorm
    (scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
      Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube Q a *
      scalarFullBlockNormalizerMatrixAtScale hP hStruct m)

private theorem measurable_terminalUncenteredFunctional
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P) (m : ℕ) :
    Measurable fun Y : Homogenization.FullBlockMat d =>
      fullBlockOperatorNorm
        (scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
          Y *
          scalarFullBlockNormalizerMatrixAtScale hP hStruct m) := by
  let L : Homogenization.FullBlockMat d →ₗ[ℝ]
      (EuclideanSpace ℝ (Homogenization.BlockCoord d) →L[ℝ]
        EuclideanSpace ℝ (Homogenization.BlockCoord d)) := {
    toFun := fun M =>
      Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d) (𝕜 := ℝ) M
    map_add' := by
      intro A B
      exact map_add
        (Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d) (𝕜 := ℝ)) A B
    map_smul' := by
      intro r A
      exact map_smul
        (Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d) (𝕜 := ℝ)) r A
  }
  have hinner : Continuous fun Y : Homogenization.FullBlockMat d =>
      scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
        Y *
        scalarFullBlockNormalizerMatrixAtScale hP hStruct m := by
    fun_prop
  have hcont : Continuous fun Y : Homogenization.FullBlockMat d =>
      ‖L (scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
        Y *
        scalarFullBlockNormalizerMatrixAtScale hP hStruct m)‖ :=
    (L.continuous_of_finiteDimensional.comp hinner).norm
  simpa [fullBlockOperatorNorm, L] using hcont.measurable

/--
Source label `e.J.moment.bound`: measurability of the uncentered
terminal-normalized block norm used in the response moment estimate.
-/
theorem aemeasurable_terminalUncenteredCoarseBlockNorm
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (m : ℕ) (Q : Homogenization.TriadicCube d) :
    AEMeasurable
      (fun a : Homogenization.RegCoeffField d =>
        terminalUncenteredCoarseBlockNorm hP hStruct m Q a) P := by
  have hbase :
      AEMeasurable
        (fun a : Homogenization.RegCoeffField d =>
          Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube Q a) P := by
    simpa [Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube] using
      hP.aemeasurable_coarseFullBlockMatrix_cubeSet Q
  have hcomp :=
    (measurable_terminalUncenteredFunctional hP hStruct m).comp_aemeasurable hbase
  simpa [terminalUncenteredCoarseBlockNorm] using hcomp

/--
Source label `e.J.moment.bound`: the special-vector response observable at
the lower edge of the no-drop window is controlled, a.e. under the law, by
the terminal-normalized uncentered full-block norm.  This is the primal
pointwise analytic estimate before converting `sqrt(theta_m)` to the
manuscript's `r_m` normalization.
-/
theorem responseJ_special_ae_le_two_sqrtTheta_terminalUncentered
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Homogenization.Vec d)
    (he : Homogenization.Book.Ch02.vecNorm e = 1) :
    (fun a : Homogenization.RegCoeffField d =>
        Homogenization.Book.Ch04.responseJObservableCubeSet
          (Homogenization.originCube d (k : ℤ))
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) a)
      ≤ᵐ[P]
        fun a =>
          2 * Real.sqrt
              (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
            terminalUncenteredCoarseBlockNorm hP hStruct m
              (Homogenization.originCube d (k : ℤ)) a := by
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let θ := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  have hσ_pos : 0 < σ := by
    simpa [σ] using
      Homogenization.Book.Ch05.Section54.GoodScale.sigmaHatAtScale_pos_of_P4
        hP hStruct hP4 m
  have he_sq :
      Homogenization.vecNormSq e = 1 :=
    Homogenization.Book.Ch05.Section54.GoodScale.vecNormSq_eq_one_of_vecNorm_eq_one he
  have he_dot : Homogenization.vecDot e e = 1 := by
    simpa [Homogenization.vecNormSq] using he_sq
  have hdot_nonneg : 0 ≤ Homogenization.vecDot p_e q_e := by
    have hpq :
        Homogenization.vecDot p_e q_e = 1 := by
      change
        Homogenization.vecDot
          (((Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)) ^
            (-(1 / 2 : ℝ))) • e)
          (((Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)) ^
            (1 / 2 : ℝ)) • e) = 1
      rw [show Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ) = σ by rfl]
      simp [Homogenization.vecDot_smul_left, Homogenization.vecDot_smul_right]
      have hcross :
          σ ^ (1 / 2 : ℝ) * (σ ^ (-(1 / 2 : ℝ)) *
            Homogenization.vecDot e e) = 1 := by
        rw [← mul_assoc, mul_comm (σ ^ (1 / 2 : ℝ)) (σ ^ (-(1 / 2 : ℝ)))]
        rw [Homogenization.Book.Ch05.Section54.GoodScale.rpow_neg_half_mul_rpow_half_eq_one
          hσ_pos, one_mul, he_dot]
      have hcross2 :
          σ ^ (2⁻¹ : ℝ) * (σ ^ (-2⁻¹ : ℝ) *
            Homogenization.vecDot e e) = 1 := by
        convert hcross using 1
        norm_num
      simpa using hcross2
    rw [hpq]
    norm_num
  filter_upwards
    [Homogenization.Book.Ch04.responseJObservableCubeSet_ae_eq_quadratic_coarseBlockMatrix_of_lawCarrier
        hP (Homogenization.originCube d (k : ℤ)) p_e q_e,
     hP.ae_locallyUniformlyEllipticField] with a hJ ha
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (k : ℤ)
  let A : Homogenization.BlockMat d :=
    Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a
  let F : Homogenization.Book.Ch02.TriadicCoeffFamily d :=
    Homogenization.Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hEq :
      A =
        Homogenization.Book.Ch02.coarseBlockMatrix
          (Homogenization.Book.Ch02.cubeDomain Q) (F.coeffOn Q) := by
    simpa [A, F] using
      Homogenization.Book.Ch04.LawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  have hSymm : Homogenization.IsSymmetricBlockMat A := by
    rw [hEq]
    exact Homogenization.Book.Ch02.isSymmetricBlockMat_coarseBlockMatrix
      (Homogenization.Book.Ch02.cubeDomain Q) (F.coeffOn Q)
  have hPos : Homogenization.Book.Ch02.BlockPosDef A := by
    rw [hEq]
    exact
      (Homogenization.Book.Ch02.blockCoarseMatrixTheory
        (Homogenization.Book.Ch02.cubeDomain Q) (F.coeffOn Q)).block_matrix_posDef
  let upperQuad :=
    Homogenization.vecDot p_e (Homogenization.matVecMul A.upperLeft p_e)
  let lowerQuad :=
    Homogenization.vecDot q_e (Homogenization.matVecMul A.lowerRight q_e)
  have hcross :
      |Homogenization.vecDot q_e (Homogenization.matVecMul A.lowerLeft p_e)| ≤
        (1 / 2 : ℝ) * (upperQuad + lowerQuad) := by
    simpa [upperQuad, lowerQuad, add_comm] using
      Homogenization.Book.Ch05.Section54.OneStepContraction.responseMoment_block_cross_abs_le_half_quadratics
          hSymm hPos p_e q_e
  have hJ_le_quads :
      Homogenization.Book.Ch04.responseJObservableCubeSet Q p_e q_e a ≤
        upperQuad + lowerQuad := by
    calc
      Homogenization.Book.Ch04.responseJObservableCubeSet Q p_e q_e a =
          (1 / 2 : ℝ) * lowerQuad - Homogenization.vecDot p_e q_e -
            Homogenization.vecDot q_e (Homogenization.matVecMul A.lowerLeft p_e) +
            (1 / 2 : ℝ) * upperQuad := by
            simpa [Q, A, upperQuad, lowerQuad] using hJ
      _ ≤ (1 / 2 : ℝ) * lowerQuad +
            |Homogenization.vecDot q_e
              (Homogenization.matVecMul A.lowerLeft p_e)| +
            (1 / 2 : ℝ) * upperQuad := by
            nlinarith
              [hdot_nonneg,
               neg_le_abs
                (Homogenization.vecDot q_e
                  (Homogenization.matVecMul A.lowerLeft p_e))]
      _ ≤ (1 / 2 : ℝ) * lowerQuad +
            (1 / 2 : ℝ) * (upperQuad + lowerQuad) +
            (1 / 2 : ℝ) * upperQuad := by
            nlinarith
      _ = upperQuad + lowerQuad := by ring
  have hUpper :
      upperQuad ≤
        Real.sqrt θ *
          terminalUncenteredCoarseBlockNorm hP hStruct m Q a := by
    simpa [upperQuad, terminalUncenteredCoarseBlockNorm, Q, A, p_e,
      Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube,
      Homogenization.coarseFullBlockMatrixObservable, θ] using
      responseMoment_upper_special_quad_le_sqrtTheta_terminalNorm
        hP hStruct hP4 m e he A
  have hLower :
      lowerQuad ≤
        Real.sqrt θ *
          terminalUncenteredCoarseBlockNorm hP hStruct m Q a := by
    simpa [lowerQuad, terminalUncenteredCoarseBlockNorm, Q, A, q_e,
      Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube,
      Homogenization.coarseFullBlockMatrixObservable, θ] using
      responseMoment_lower_special_quad_le_sqrtTheta_terminalNorm
        hP hStruct hP4 m e he A
  calc
    Homogenization.Book.Ch04.responseJObservableCubeSet Q p_e q_e a
        ≤ upperQuad + lowerQuad := hJ_le_quads
    _ ≤ Real.sqrt θ * terminalUncenteredCoarseBlockNorm hP hStruct m Q a +
          Real.sqrt θ * terminalUncenteredCoarseBlockNorm hP hStruct m Q a :=
          add_le_add hUpper hLower
    _ = 2 * Real.sqrt θ *
          terminalUncenteredCoarseBlockNorm hP hStruct m Q a := by ring

end Homogenization.HighContrast.EntryScale
