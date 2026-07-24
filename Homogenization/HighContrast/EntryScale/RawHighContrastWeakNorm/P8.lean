import Homogenization.HighContrast.EntryScale.ResponseFluctuation
import Homogenization.HighContrast.EntryScale.ResponseMoment
import Homogenization.HighContrast.EntryScale.TerminalLowerEdge
import Homogenization.HighContrast.EntryScale.BadEventResponse
import Homogenization.HighContrast.EntryScale.RawHighContrastWeakNorm.P1
import Homogenization.HighContrast.EntryScale.RawHighContrastWeakNorm.P2
import Homogenization.HighContrast.EntryScale.RawHighContrastWeakNorm.P5

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization
open scoped Matrix.Norms.Elementwise

namespace Homogenization.HighContrast.EntryScale

noncomputable section

/-- Compact name for the Section 5.2 small-tail child-response integral. -/
def section52SmallTailChildResponseIntegralAtScales
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Homogenization.Vec d) : ℝ :=
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
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
  ∫ a, (σ * lowerSmall a + σ⁻¹ * upperSmall a) * response a ∂P

/-- Compact terminal-prefactor budget for the Section 5.2 small-tail term. -/
def section52SmallTailTerminalResponseBudgetAtScales
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Homogenization.Vec d) : ℝ :=
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let D := Homogenization.descendantsAtScale Q 0
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let responseMoment : ℝ :=
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
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
      Homogenization.Book.Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi
  let upperMomentCoeff :=
    (D.card : ℝ) ^ (1 / (hP4.xi : ℝ)) *
      Homogenization.Book.Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi
  let smallCoeff :=
    (5 * β⁻¹) ^ 2 *
      (σ * lowerCoeff * lowerMomentCoeff +
        σ⁻¹ * upperCoeff * upperMomentCoeff)
  smallCoeff * (terminalPAtScales hP hStruct k m * responseMoment)

/-- Terminal-prefactor small-tail estimate with compact budget names. -/
theorem section52SmallTailChildResponseIntegral_le_terminalResponseBudgetAtScales
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hstat : Homogenization.Book.Ch04.StationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Homogenization.Vec d) :
    section52SmallTailChildResponseIntegralAtScales hP hStruct hP4 k m e ≤
      section52SmallTailTerminalResponseBudgetAtScales hP hStruct hP4 k m e := by
  simpa [section52SmallTailChildResponseIntegralAtScales,
    section52SmallTailTerminalResponseBudgetAtScales] using
    (integrable_section52SmallTail_childResponseAverage_special_and_integral_le_terminalPAtScales_mul_responseMoment
      hP hstat hStruct hP4 hkm e).2

/--
Source labels `p.HC.CR` and `e.W.first.sum`: LIH's high-scale average
component has the manuscript terminal fluctuation shape, up to the explicit
Section 5.3 constant and `β⁻¹` loss.  This theorem only rewrites
`θ_m` as `1 + F_m`; it does not use the final coarse-fluctuation RHS.
-/
theorem integral_paired_highScaleAverageTerms_special_le_beta_inv_contrastExcess_fullBlockSumAtScale
    {d : ℕ} [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Homogenization.Book.Ch04.CoeffLaw d}
        (hP : Homogenization.Book.Ch04.LawCarrier P)
        (_hstat : Homogenization.Book.Ch04.StationaryLaw P)
        (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
        {k m : ℕ}, k < m → ∀ e : Homogenization.Vec d,
        Homogenization.vecNormSq e = 1 →
        let β := section53CoarseFluctuationBeta hP4
        let s := hP4.sLower + 2 * β
        let t := hP4.sUpper + 2 * β
        let p_e :=
          Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
        let q_e :=
          Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
        let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
        let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
        let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
        ∫ a,
            (σ *
                (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientAverageTermAtScale
                  (m : ℤ) (k : ℤ) s p_e q_e p0_e a) ^ 2 +
              σ⁻¹ *
                (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxAverageTermAtScale
                  (m : ℤ) (k : ℤ) t p_e q_e q0_e a) ^ 2) ∂P
          ≤
            C * β⁻¹ * (1 + contrastExcessAtScale hP hStruct m) *
              coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m := by
  rcases integral_paired_highScaleAverageTerms_special_le_beta_inv_fullBlockSumAtScale
      (d := d) with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro P hP hstat hStruct hP4 k m hkm e he
  have h := hC hP hstat hStruct hP4 hkm e he
  simpa [contrastExcessAtScale, mul_assoc] using h

private theorem constantTail_norm_sq_le_vecNormSq {d : ℕ} (v : Homogenization.Vec d) :
    ‖v‖ ^ 2 ≤ Homogenization.vecNormSq v := by
  have hnorm_le : ‖v‖ ≤ Real.sqrt (Homogenization.vecNormSq v) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 ?_
    intro i
    have hi : ‖v i‖ ^ 2 ≤ Homogenization.vecNormSq v := by
      calc
        ‖v i‖ ^ 2 = v i ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
        _ ≤ ∑ j, v j ^ 2 := by
          exact Finset.single_le_sum (fun j _hj => sq_nonneg (v j)) (Finset.mem_univ i)
        _ = Homogenization.vecNormSq v := by
          simp [Homogenization.vecNormSq, Homogenization.vecDot, pow_two]
    exact Real.le_sqrt_of_sq_le hi
  have hsqrt_sq :
      (Real.sqrt (Homogenization.vecNormSq v)) ^ 2 = Homogenization.vecNormSq v := by
    simpa [pow_two] using Real.sq_sqrt (Homogenization.vecNormSq_nonneg v)
  calc
    ‖v‖ ^ 2 ≤ (Real.sqrt (Homogenization.vecNormSq v)) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 hnorm_le
    _ = Homogenization.vecNormSq v := hsqrt_sq

private theorem constantTail_rpow_three_sq (x : ℝ) :
    Real.rpow (3 : ℝ) x ^ 2 = Real.rpow (3 : ℝ) (2 * x) := by
  calc
    Real.rpow (3 : ℝ) x ^ 2 =
        Real.rpow (3 : ℝ) x * Real.rpow (3 : ℝ) x := by ring
    _ = Real.rpow (3 : ℝ) (x + x) := by
        exact (Real.rpow_add (by norm_num : (0 : ℝ) < 3) x x).symm
    _ = Real.rpow (3 : ℝ) (2 * x) := by ring_nf

private theorem constantTail_inv_sq_rpow_tail_le
    {β r N : ℝ} (hβ : 0 < β) (hβr : β ≤ r) (hN : 0 ≤ N) :
    r⁻¹ ^ 2 * Real.rpow (3 : ℝ) (-2 * r * N) ≤
      (β ^ 2)⁻¹ * Real.rpow (3 : ℝ) (-2 * β * N) := by
  have hr : 0 < r := hβ.trans_le hβr
  have hinv : r⁻¹ ≤ β⁻¹ := (inv_le_inv₀ hr hβ).2 hβr
  have hinv_sq : r⁻¹ ^ 2 ≤ β⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hr.le) hinv 2
  have hβ_inv_sq : β⁻¹ ^ 2 = (β ^ 2)⁻¹ := by
    field_simp [hβ.ne']
  have hinv_sq' : r⁻¹ ^ 2 ≤ (β ^ 2)⁻¹ := by
    simpa [hβ_inv_sq] using hinv_sq
  have hpow :
      Real.rpow (3 : ℝ) (-2 * r * N) ≤
        Real.rpow (3 : ℝ) (-2 * β * N) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    nlinarith
  exact mul_le_mul hinv_sq' hpow
    (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    (inv_nonneg.mpr (sq_nonneg β))

private theorem constantTail_sqrt_sub_one_sq_le_sub_one {θ : ℝ} (hθ : 1 ≤ θ) :
    (Real.sqrt θ - 1) ^ 2 ≤ θ - 1 := by
  have hθ_nonneg : 0 ≤ θ := le_trans zero_le_one hθ
  have hs_nonneg : 0 ≤ Real.sqrt θ - 1 := by
    have hs : 1 ≤ Real.sqrt θ := Real.one_le_sqrt.mpr hθ
    linarith
  have hfactor :
      (Real.sqrt θ - 1) * (Real.sqrt θ + 1) = θ - 1 := by
    calc
      (Real.sqrt θ - 1) * (Real.sqrt θ + 1) =
          (Real.sqrt θ) ^ 2 - 1 := by ring
      _ = θ - 1 := by rw [Real.sq_sqrt hθ_nonneg]
  calc
    (Real.sqrt θ - 1) ^ 2 =
        (Real.sqrt θ - 1) * (Real.sqrt θ - 1) := by ring
    _ ≤ (Real.sqrt θ - 1) * (Real.sqrt θ + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hs_nonneg
    _ = θ - 1 := hfactor

/--
Source labels `p.HC.CR` and `e.W.first.sum`: the constant affine tails in
LIH's weak-norm maximizer are bounded by the unweighted local geometric
contrast tail.  This stops at the pre-Section 5.3 scalar-weight estimate in
LIH's proof and exposes the manuscript-facing `F_m` tail.
-/
theorem paired_constantTail_special_le_contrastExcess_lowScaleTail_unweighted
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (_hkm : k < m) (e : Homogenization.Vec d)
    (he : Homogenization.vecNormSq e = 1) :
    let β := section53CoarseFluctuationBeta hP4
    let s := hP4.sLower + 2 * β
    let t := hP4.sUpper + 2 * β
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
    let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    σ *
        (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientConstantTailAtScale
          (m : ℤ) (k : ℤ) s p0_e) ^ 2 +
      σ⁻¹ *
        (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxConstantTailAtScale
          (m : ℤ) (k : ℤ) t q0_e) ^ 2
      ≤
        2 * ((β ^ 2)⁻¹ *
          Real.rpow (3 : ℝ)
            (-2 * β * (((m - k : ℕ) : ℝ))) *
          contrastExcessAtScale hP hStruct m) := by
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let t := hP4.sUpper + 2 * β
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let θ := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
  let tail :=
    (β ^ 2)⁻¹ *
      Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hs_ge : β ≤ s := by
    dsimp [s, β]
    linarith [hP4.sLower_nonneg, hβ_pos.le]
  have ht_ge : β ≤ t := by
    dsimp [t, β]
    linarith [hP4.sUpper_nonneg, hβ_pos.le]
  have hN_nonneg : 0 ≤ (((m - k : ℕ) : ℝ)) := by positivity
  have hs_factor :
      s⁻¹ ^ 2 *
          Real.rpow (3 : ℝ)
            (-2 * s * (((m - k : ℕ) : ℝ))) ≤ tail := by
    simpa [tail] using constantTail_inv_sq_rpow_tail_le hβ_pos hs_ge hN_nonneg
  have ht_factor :
      t⁻¹ ^ 2 *
          Real.rpow (3 : ℝ)
            (-2 * t * (((m - k : ℕ) : ℝ))) ≤ tail := by
    simpa [tail] using constantTail_inv_sq_rpow_tail_le hβ_pos ht_ge hN_nonneg
  have htail_nonneg : 0 ≤ tail := by
    dsimp [tail]
    exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hσ_nonneg : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hθ_one : 1 ≤ θ := by
    simpa [θ] using one_le_thetaAtScale_of_P4 hP hStruct hP4 m
  have hcenter_le : (Real.sqrt θ - 1) ^ 2 ≤ θ - 1 :=
    constantTail_sqrt_sub_one_sq_le_sub_one hθ_one
  have hp_center :
      σ * ‖p0_e‖ ^ 2 ≤ (Real.sqrt θ - 1) ^ 2 := by
    have hnorm := constantTail_norm_sq_le_vecNormSq p0_e
    have hvec :=
      sigmaHatAtScale_mul_vecNormSq_specialPCentering_eq hP hStruct hP4 m e
    calc
      σ * ‖p0_e‖ ^ 2 ≤ σ * Homogenization.vecNormSq p0_e :=
        mul_le_mul_of_nonneg_left hnorm hσ_nonneg
      _ = (Real.sqrt θ - 1) ^ 2 := by
        simpa [σ, θ, p_e, q_e, p0_e, he] using hvec
  have hq_center :
      σ⁻¹ * ‖q0_e‖ ^ 2 ≤ (Real.sqrt θ - 1) ^ 2 := by
    have hnorm := constantTail_norm_sq_le_vecNormSq q0_e
    have hvec :=
      inv_sigmaHatAtScale_mul_vecNormSq_specialQCentering_eq hP hStruct hP4 m e
    calc
      σ⁻¹ * ‖q0_e‖ ^ 2 ≤ σ⁻¹ * Homogenization.vecNormSq q0_e :=
        mul_le_mul_of_nonneg_left hnorm hσ_inv_nonneg
      _ = (Real.sqrt θ - 1) ^ 2 := by
        simpa [σ, θ, p_e, q_e, q0_e, he] using hvec
  have hgrad_sq :
      (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientConstantTailAtScale
          (m : ℤ) (k : ℤ) s p0_e) ^ 2 =
        s⁻¹ ^ 2 *
          Real.rpow (3 : ℝ)
            (-2 * s * (((m - k : ℕ) : ℝ))) * ‖p0_e‖ ^ 2 := by
    dsimp [Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientConstantTailAtScale]
    have hmk :
        (Int.toNat ((m : ℤ) - (k : ℤ)) : ℝ) = ((m - k : ℕ) : ℝ) := by
      have hmk_nat : Int.toNat ((m : ℤ) - (k : ℤ)) = m - k := by omega
      exact_mod_cast hmk_nat
    rw [hmk]
    rw [mul_pow, mul_pow]
    change
      s⁻¹ ^ 2 *
          (Real.rpow (3 : ℝ) (-s * (((m - k : ℕ) : ℝ)))) ^ 2 *
            ‖p0_e‖ ^ 2 =
        s⁻¹ ^ 2 *
          Real.rpow (3 : ℝ) (-2 * s * (((m - k : ℕ) : ℝ))) *
            ‖p0_e‖ ^ 2
    rw [constantTail_rpow_three_sq]
    ring_nf
  have hflux_sq :
      (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxConstantTailAtScale
          (m : ℤ) (k : ℤ) t q0_e) ^ 2 =
        t⁻¹ ^ 2 *
          Real.rpow (3 : ℝ)
            (-2 * t * (((m - k : ℕ) : ℝ))) * ‖q0_e‖ ^ 2 := by
    dsimp [Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxConstantTailAtScale]
    have hmk :
        (Int.toNat ((m : ℤ) - (k : ℤ)) : ℝ) = ((m - k : ℕ) : ℝ) := by
      have hmk_nat : Int.toNat ((m : ℤ) - (k : ℤ)) = m - k := by omega
      exact_mod_cast hmk_nat
    rw [hmk]
    rw [mul_pow, mul_pow]
    change
      t⁻¹ ^ 2 *
          (Real.rpow (3 : ℝ) (-t * (((m - k : ℕ) : ℝ)))) ^ 2 *
            ‖q0_e‖ ^ 2 =
        t⁻¹ ^ 2 *
          Real.rpow (3 : ℝ) (-2 * t * (((m - k : ℕ) : ℝ))) *
            ‖q0_e‖ ^ 2
    rw [constantTail_rpow_three_sq]
    ring_nf
  have hgrad_le :
      σ *
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientConstantTailAtScale
            (m : ℤ) (k : ℤ) s p0_e) ^ 2
        ≤ tail * (θ - 1) := by
    calc
      σ *
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientConstantTailAtScale
            (m : ℤ) (k : ℤ) s p0_e) ^ 2
          =
        (s⁻¹ ^ 2 *
          Real.rpow (3 : ℝ)
            (-2 * s * (((m - k : ℕ) : ℝ)))) *
          (σ * ‖p0_e‖ ^ 2) := by
          rw [hgrad_sq]
          ring
      _ ≤ tail * (θ - 1) := by
          have hp_nonneg : 0 ≤ σ * ‖p0_e‖ ^ 2 :=
            mul_nonneg hσ_nonneg (sq_nonneg _)
          exact mul_le_mul hs_factor (hp_center.trans hcenter_le)
            hp_nonneg htail_nonneg
  have hflux_le :
      σ⁻¹ *
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxConstantTailAtScale
            (m : ℤ) (k : ℤ) t q0_e) ^ 2
        ≤ tail * (θ - 1) := by
    calc
      σ⁻¹ *
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxConstantTailAtScale
            (m : ℤ) (k : ℤ) t q0_e) ^ 2
          =
        (t⁻¹ ^ 2 *
          Real.rpow (3 : ℝ)
            (-2 * t * (((m - k : ℕ) : ℝ)))) *
          (σ⁻¹ * ‖q0_e‖ ^ 2) := by
          rw [hflux_sq]
          ring
      _ ≤ tail * (θ - 1) := by
          have hq_nonneg : 0 ≤ σ⁻¹ * ‖q0_e‖ ^ 2 :=
            mul_nonneg hσ_inv_nonneg (sq_nonneg _)
          exact mul_le_mul ht_factor (hq_center.trans hcenter_le)
            hq_nonneg htail_nonneg
  calc
    σ *
        (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientConstantTailAtScale
          (m : ℤ) (k : ℤ) s p0_e) ^ 2 +
      σ⁻¹ *
        (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxConstantTailAtScale
          (m : ℤ) (k : ℤ) t q0_e) ^ 2
        ≤ tail * (θ - 1) + tail * (θ - 1) :=
          add_le_add hgrad_le hflux_le
    _ = 2 * (tail * (θ - 1)) := by ring
    _ =
        2 * ((β ^ 2)⁻¹ *
          Real.rpow (3 : ℝ)
            (-2 * β * (((m - k : ℕ) : ℝ))) *
          contrastExcessAtScale hP hStruct m) := by
        simp [tail, θ, contrastExcessAtScale, mul_assoc]

/--
Source labels `p.HC.CR` and `e.W.low.tail`: LIH's cutoff-oscillation
remainder term is controlled by the same geometrically discounted contrast
coefficient, before the scale-zero Section 5.3 scalar weight is inserted.
This is the manuscript-facing local-tail form used in the high-moment paper
(Armstrong–Kuusi–Loher, in preparation).
-/
private theorem two_mul_section53CoarseFluctuationBeta_le_one
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P) :
    2 * section53CoarseFluctuationBeta hP4 ≤ 1 := by
  have hsum := sUpper_add_sLower_add_four_beta_le_one hP4
  have hupper := hP4.sUpper_nonneg
  have hlower := hP4.sLower_nonneg
  have hbeta := section53CoarseFluctuationBeta_nonneg hP4
  nlinarith

private theorem cutoff_decay_le_contrast_tail_decay
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (N : ℕ) :
    ((3 : ℝ) ^ N)⁻¹ ≤
      Real.rpow (3 : ℝ)
        (-2 * section53CoarseFluctuationBeta hP4 * (N : ℝ)) := by
  have htwo : 2 * section53CoarseFluctuationBeta hP4 ≤ 1 :=
    two_mul_section53CoarseFluctuationBeta_le_one hP4
  have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
  have hexp :
      -(N : ℝ) ≤
        -2 * section53CoarseFluctuationBeta hP4 * (N : ℝ) := by
    nlinarith
  have hrpow :
      Real.rpow (3 : ℝ) (-(N : ℝ)) ≤
        Real.rpow (3 : ℝ)
          (-2 * section53CoarseFluctuationBeta hP4 * (N : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
  have hpow_eq : ((3 : ℝ) ^ N)⁻¹ = Real.rpow (3 : ℝ) (-(N : ℝ)) := by
    calc
      ((3 : ℝ) ^ N)⁻¹ = (Real.rpow (3 : ℝ) (N : ℝ))⁻¹ := by
        simp [Real.rpow_natCast]
      _ = Real.rpow (3 : ℝ) (-(N : ℝ)) := by
        exact (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3) (N : ℝ)).symm
  rw [hpow_eq]
  exact hrpow

private theorem cutoffCoeff_le_uniform_contrast_tail_coeff
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (_hkm : k < m) {eps : ℝ} (heps : 0 < eps)
    (heps_le : eps ≤ 1) :
    let β := section53CoarseFluctuationBeta hP4
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant
        Q *
      Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffScaleSep
        Q j
      ≤
        (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
          eps⁻¹ * (β ^ 2)⁻¹ *
            Real.rpow (3 : ℝ)
              (-2 * β * (((m - k : ℕ) : ℝ))) := by
  intro β Q j
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have heps_inv_ge_one : 1 ≤ eps⁻¹ :=
    (one_le_inv₀ heps).mpr heps_le
  have hβ_sq_inv_ge_one : 1 ≤ (β ^ 2)⁻¹ := by
    have hβ_le_one : β ≤ 1 := by
      have htwo := two_mul_section53CoarseFluctuationBeta_le_one hP4
      nlinarith [hβ_pos.le, htwo]
    have hsquare_le_one : β ^ 2 ≤ 1 := by
      nlinarith [hβ_pos.le, hβ_le_one]
    exact (one_le_inv₀ (sq_pos_of_pos hβ_pos)).mpr hsquare_le_one
  have hosc :=
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant_mul_scaleSep_eq
      Q j
  have hbound :=
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound_le_two_pow_card
      Q
  have hgrad_nonneg := quantitativeCubeCutoffGradientConst_nonneg d
  have htwo_pow_nonneg : 0 ≤ (2 : ℝ) ^ d := pow_nonneg (by norm_num) d
  have hcut_base :
      Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant
          Q *
        Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffScaleSep
          Q j
        ≤
          (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
            ((3 : ℝ) ^ j)⁻¹ := by
    calc
      Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant
          Q *
        Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffScaleSep
          Q j
          =
        (8 * quantitativeCubeCutoffGradientConst d *
            Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound
              Q) *
          ((3 : ℝ) ^ j)⁻¹ := hosc
      _ ≤
        (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
          ((3 : ℝ) ^ j)⁻¹ := by
          exact mul_le_mul_of_nonneg_right
            (by
              nlinarith [mul_le_mul_of_nonneg_left hbound
                (mul_nonneg (by norm_num : 0 ≤ (8 : ℝ)) hgrad_nonneg)])
            (inv_nonneg.mpr (pow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) j))
  have hmk_nat : j = m - k := by
    dsimp [j]
    omega
  have hdecay :
      ((3 : ℝ) ^ j)⁻¹ ≤
        Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) := by
    simpa [β, hmk_nat, mul_assoc] using
      cutoff_decay_le_contrast_tail_decay hP4 (m - k)
  have hbase_nonneg :
      0 ≤ 8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d :=
    mul_nonneg (mul_nonneg (by norm_num) hgrad_nonneg) htwo_pow_nonneg
  have htail_nonneg :
      0 ≤ Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have htail_le :
      Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) ≤
        eps⁻¹ * (β ^ 2)⁻¹ *
          Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) := by
    have hfac : 1 ≤ eps⁻¹ * (β ^ 2)⁻¹ := by
      nlinarith [heps_inv_ge_one, hβ_sq_inv_ge_one]
    calc
      Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))
          = 1 * Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) := by
              ring
      _ ≤
        (eps⁻¹ * (β ^ 2)⁻¹) *
          Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right hfac htail_nonneg
  calc
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant
        Q *
      Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffScaleSep
        Q j
        ≤
          (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
            ((3 : ℝ) ^ j)⁻¹ := hcut_base
    _ ≤
          (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
            Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hdecay hbase_nonneg
    _ ≤
          (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
            eps⁻¹ * (β ^ 2)⁻¹ *
              Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) := by
          calc
            (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
                Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))
                ≤
                  (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
                    (eps⁻¹ * (β ^ 2)⁻¹ *
                      Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))) :=
                  mul_le_mul_of_nonneg_left htail_le hbase_nonneg
            _ =
                  (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
                    eps⁻¹ * (β ^ 2)⁻¹ *
                      Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) := by
                  ring

private theorem expectedResponseJCubeSet_nonneg_rawWeak
    {d : ℕ} (P : Homogenization.Book.Ch04.CoeffLaw d)
    (Q : Homogenization.TriadicCube d) (p q : Homogenization.Vec d) :
    0 ≤ Homogenization.Book.Ch04.expectedResponseJCubeSet P Q p q := by
  dsimp [Homogenization.Book.Ch04.expectedResponseJCubeSet]
  exact MeasureTheory.integral_nonneg fun a =>
    Homogenization.Book.Ch04.responseJObservableCubeSet_nonneg Q p q a

theorem cutoffOscillation_special_expectedResponse_le_contrastTail_uniform
    {d : ℕ} [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Homogenization.Book.Ch04.CoeffLaw d}
        (hP : Homogenization.Book.Ch04.LawCarrier P)
        (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
        {k m : ℕ}, k < m →
        ∀ e : Homogenization.Vec d, Homogenization.vecNormSq e = 1 →
        ∀ {eps : ℝ}, 0 < eps → eps ≤ 1 →
      let β := section53CoarseFluctuationBeta hP4
      let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
      let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
      let p_e :=
        Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
      let q_e :=
        Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
      Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant
          Q *
        Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffScaleSep
          Q j *
        Homogenization.Book.Ch04.expectedResponseJCubeSet P Q p_e q_e
        ≤
          C * eps⁻¹ * (β ^ 2)⁻¹ *
            Real.rpow (3 : ℝ)
              (-2 * β * (((m - k : ℕ) : ℝ))) *
            (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ) - 1) := by
  refine ⟨8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d,
    mul_nonneg
      (mul_nonneg (by norm_num) (quantitativeCubeCutoffGradientConst_nonneg d))
      (pow_nonneg (by norm_num) d), ?_⟩
  intro P hP hStruct hP4 k m hkm e he eps heps_pos heps_le
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
  let θ := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
  have hCoeff :=
    cutoffCoeff_le_uniform_contrast_tail_coeff hP4 hkm heps_pos heps_le
  have hθ_one : 1 ≤ θ := by
    simpa [θ] using one_le_thetaAtScale_of_P4 hP hStruct hP4 m
  have hθ_sub_nonneg : 0 ≤ θ - 1 := by linarith
  have hJ_le :
      Homogenization.Book.Ch04.expectedResponseJCubeSet P Q
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e)
        ≤ θ - 1 := by
    simpa [Q, θ] using
      expectedResponseJCubeSet_special_le_thetaAtScale_sub_one_of_vecNormSq_eq_one
        hP hStruct hP4 m e he
  have hJ_nonneg :
      0 ≤ Homogenization.Book.Ch04.expectedResponseJCubeSet P Q
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) :=
    expectedResponseJCubeSet_nonneg_rawWeak P Q
      (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
      (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e)
  have hCoeffTail_nonneg :
      0 ≤
        (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
          eps⁻¹ * (β ^ 2)⁻¹ *
          Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) := by
    have hbase :
        0 ≤ 8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d :=
      mul_nonneg
        (mul_nonneg (by norm_num) (quantitativeCubeCutoffGradientConst_nonneg d))
        (pow_nonneg (by norm_num) d)
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hbase (inv_nonneg.mpr heps_pos.le))
        (inv_nonneg.mpr (sq_nonneg _)))
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  calc
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant
          Q *
        Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffScaleSep
          Q j *
        Homogenization.Book.Ch04.expectedResponseJCubeSet P Q
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e)
      ≤
        ((8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
          eps⁻¹ * (β ^ 2)⁻¹ *
          Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ)))) *
          (θ - 1) := by
        exact mul_le_mul hCoeff hJ_le hJ_nonneg hCoeffTail_nonneg
    _ =
        (8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d) *
          eps⁻¹ * (β ^ 2)⁻¹ *
          Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) *
          (θ - 1) := by
        ring

theorem normalized_cutoffOscillation_special_expectedResponse_le_decay_tail
    {d : ℕ} [NeZero d] :
    ∃ C_osc : ℝ, 0 ≤ C_osc ∧
      ∀ {P : Homogenization.Book.Ch04.CoeffLaw d}
        (hP : Homogenization.Book.Ch04.LawCarrier P)
        (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
        {k m : ℕ}, k < m → ∀ e : Homogenization.Vec d,
        Homogenization.vecNormSq e = 1 →
        ∀ {eps C_norm : ℝ}, 0 < eps → eps ≤ 1 → 0 < C_norm →
        ∀ {T_edge decay : ℝ},
        (let β := section53CoarseFluctuationBeta hP4
         (C_osc * C_norm⁻¹) *
            ((β ^ 2)⁻¹ *
              Real.rpow (3 : ℝ)
                (-2 * β * (((m - k : ℕ) : ℝ))) *
              contrastExcessAtScale hP hStruct m) ≤ decay * T_edge) →
        let Q : Homogenization.TriadicCube d :=
          Homogenization.originCube d (m : ℤ)
        let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
        let p_e :=
          Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
        let q_e :=
          Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
        eps * C_norm⁻¹ *
            (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant
                Q *
              Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffScaleSep
                Q j *
              Homogenization.Book.Ch04.expectedResponseJCubeSet P Q p_e q_e)
          ≤ decay * T_edge := by
  rcases cutoffOscillation_special_expectedResponse_le_contrastTail_uniform
      (d := d) with ⟨C_osc, hC_osc_nonneg, hosc_all⟩
  refine ⟨C_osc, hC_osc_nonneg, ?_⟩
  intro P hP hStruct hP4 k m hkm e he eps C_norm heps_pos heps_le hC_norm_pos
    T_edge decay htail
  dsimp only at htail ⊢
  let β := section53CoarseFluctuationBeta hP4
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let geometricTerm : ℝ :=
    (β ^ 2)⁻¹ *
      Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) *
      contrastExcessAtScale hP hStruct m
  let thetaProduct : ℝ :=
    C_osc * eps⁻¹ * (β ^ 2)⁻¹ *
      Real.rpow (3 : ℝ) (-2 * β * (((m - k : ℕ) : ℝ))) *
      (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ) - 1)
  let oscTerm : ℝ :=
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant
        Q *
      Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffScaleSep
        Q j *
      Homogenization.Book.Ch04.expectedResponseJCubeSet P Q p_e q_e
  have hthetaProduct_eq : thetaProduct = C_osc * eps⁻¹ * geometricTerm := by
    dsimp [thetaProduct, geometricTerm, contrastExcessAtScale]
    ring
  have hosc : oscTerm ≤ C_osc * eps⁻¹ * geometricTerm := by
    have htheta : oscTerm ≤ thetaProduct :=
      hosc_all hP hStruct hP4 hkm e he heps_pos heps_le
    exact htheta.trans_eq hthetaProduct_eq
  have htail' : (C_osc * C_norm⁻¹) * geometricTerm ≤ decay * T_edge := by
    simpa [β, geometricTerm] using htail
  have hscale_nonneg : 0 ≤ eps * C_norm⁻¹ :=
    mul_nonneg heps_pos.le (inv_nonneg.mpr hC_norm_pos.le)
  calc
    eps * C_norm⁻¹ * oscTerm
        ≤ eps * C_norm⁻¹ * (C_osc * eps⁻¹ * geometricTerm) :=
          mul_le_mul_of_nonneg_left hosc hscale_nonneg
    _ = (C_osc * C_norm⁻¹) * geometricTerm := by
        calc
          eps * C_norm⁻¹ * (C_osc * eps⁻¹ * geometricTerm)
              = (eps * eps⁻¹) * ((C_osc * C_norm⁻¹) * geometricTerm) := by
                ring
          _ = (C_osc * C_norm⁻¹) * geometricTerm := by
                rw [mul_inv_cancel₀ (ne_of_gt heps_pos)]
                ring
    _ ≤ decay * T_edge := htail'

/--
Source labels `p.HC.CR`, `e.W.first.sum`, and `e.tau.sum.absorb`:
LIH's component decomposition for the paired special weak-norm squares, with
the mismatch component replaced by the local component slots.  This is the
faithful insertion point before LIH's scale-zero coarse-fluctuation shortcut:
the high-scale average, low-scale tail, and constant-tail components remain
visible, while the response-defect component has the corrected local
`P_{k,m}` coefficient.
-/
theorem paired_weakNormSquares_special_le_componentIntegrals_with_local_mismatch_slots
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hstat : Homogenization.Book.Ch04.StationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Homogenization.Vec d)
    (he : Homogenization.vecNormSq e = 1) :
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
    let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
    let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let K :=
      Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d
    let gradWeak :=
      Homogenization.Book.Ch04.canonicalScalarResponseGradientWeakNormCubeSet
        Q s p_e q_e p0_e
    let fluxWeak :=
      Homogenization.Book.Ch04.canonicalScalarResponseFluxWeakNormCubeSet
        Q t p_e q_e q0_e
    let highScaleAverage : ℝ :=
      ∫ a,
        (σ *
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientAverageTermAtScale
              (m : ℤ) (k : ℤ) s p_e q_e p0_e a) ^ 2 +
          σ⁻¹ *
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxAverageTermAtScale
              (m : ℤ) (k : ℤ) t p_e q_e q0_e a) ^ 2) ∂P
    let lowScaleTail : ℝ :=
      ∫ a,
        (σ *
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientLowScaleTailAtScale
              (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
          σ⁻¹ *
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxLowScaleTailAtScale
              (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P
    let constantTail : ℝ :=
      σ *
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientConstantTailAtScale
            (m : ℤ) (k : ℤ) s p0_e) ^ 2 +
        σ⁻¹ *
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxConstantTailAtScale
            (m : ℤ) (k : ℤ) t q0_e) ^ 2
    let lowerExcess := fun a : Homogenization.CoeffField d =>
      max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹)
        0
    let upperExcess := fun a : Homogenization.CoeffField d =>
      max
        (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
          hP.barSigmaAtScale hStruct (k : ℤ))
        0
    let defectSum := fun a : Homogenization.CoeffField d =>
      ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
        Real.rpow (3 : ℝ)
            (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          Real.sqrt
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
              (m : ℤ) n p_e q_e a)
    let lowerEdge : ℝ :=
      ∫ a,
        (σ * lowerExcess a + σ⁻¹ * upperExcess a) * defectSum a ^ 2 ∂P
    let localSlots : ℝ :=
      (1 + contrastExcessAtScale hP hStruct m) *
          coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m +
        (5 * localWeakNormScalarWeightAtScales hP hStruct k m * β⁻¹) *
          weightedTauSumAtScales hP hStruct hP4 k m e +
        lowerEdge +
        (1 + contrastExcessAtScale hP hStruct m) * 0
    σ * (∫ a, (gradWeak a) ^ 2 ∂P) +
        σ⁻¹ * (∫ a, (fluxWeak a) ^ 2 ∂P)
      ≤
        16 *
          (highScaleAverage + K ^ 2 * localSlots +
            K ^ 2 * lowScaleTail + K ^ 2 * constantTail) := by
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let s' := hP4.sLower + β
  let t := hP4.sUpper + 2 * β
  let t' := hP4.sUpper + β
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let K :=
    Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d
  let gradWeak :=
    Homogenization.Book.Ch04.canonicalScalarResponseGradientWeakNormCubeSet
      Q s p_e q_e p0_e
  let fluxWeak :=
    Homogenization.Book.Ch04.canonicalScalarResponseFluxWeakNormCubeSet
      Q t p_e q_e q0_e
  let highScaleAverage : ℝ :=
    ∫ a,
      (σ *
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientAverageTermAtScale
            (m : ℤ) (k : ℤ) s p_e q_e p0_e a) ^ 2 +
        σ⁻¹ *
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxAverageTermAtScale
            (m : ℤ) (k : ℤ) t p_e q_e q0_e a) ^ 2) ∂P
  let lowScaleTail : ℝ :=
    ∫ a,
      (σ *
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientLowScaleTailAtScale
            (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
        σ⁻¹ *
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxLowScaleTailAtScale
            (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P
  let constantTail : ℝ :=
    σ *
        (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientConstantTailAtScale
          (m : ℤ) (k : ℤ) s p0_e) ^ 2 +
      σ⁻¹ *
        (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxConstantTailAtScale
          (m : ℤ) (k : ℤ) t q0_e) ^ 2
  let lowerExcess := fun a : Homogenization.CoeffField d =>
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹)
      0
  let upperExcess := fun a : Homogenization.CoeffField d =>
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
        hP.barSigmaAtScale hStruct (k : ℤ))
      0
  let defectSum := fun a : Homogenization.CoeffField d =>
    ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
      Real.rpow (3 : ℝ)
          (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
        Real.sqrt
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
            (m : ℤ) n p_e q_e a)
  let lowerEdge : ℝ :=
    ∫ a, (σ * lowerExcess a + σ⁻¹ * upperExcess a) * defectSum a ^ 2 ∂P
  let localSlots : ℝ :=
    (1 + contrastExcessAtScale hP hStruct m) *
        coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m +
      (5 * localWeakNormScalarWeightAtScales hP hStruct k m * β⁻¹) *
        weightedTauSumAtScales hP hStruct hP4 k m e +
      lowerEdge +
      (1 + contrastExcessAtScale hP hStruct m) * 0
  have hGradSq : MeasureTheory.Integrable (fun a => (gradWeak a) ^ 2) P := by
    have hbase :
        MeasureTheory.Integrable
          (Internal.specialGradientWeakNormSquare hP hStruct hP4 m e) P :=
      integrable_specialGradientWeakNormSquare_from_weakNormMaximizer
        hP hstat hStruct hP4 hkm e he
    unfold Internal.specialGradientWeakNormSquare at hbase
    simpa [gradWeak, Q, s, p_e, q_e, p0_e, β] using hbase
  have hFluxSq : MeasureTheory.Integrable (fun a => (fluxWeak a) ^ 2) P := by
    have hbase :
        MeasureTheory.Integrable
          (Internal.specialFluxWeakNormSquare hP hStruct hP4 m e) P :=
      integrable_specialFluxWeakNormSquare_from_weakNormMaximizer
        hP hstat hStruct hP4 hkm e he
    unfold Internal.specialFluxWeakNormSquare at hbase
    simpa [fluxWeak, Q, t, p_e, q_e, q0_e, β] using hbase
  have hLowerEdge_int :
      MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d =>
          (σ * lowerExcess a + σ⁻¹ * upperExcess a) * defectSum a ^ 2) P := by
    simpa [β, s', t', Q, p_e, q_e, σ, lowerExcess, upperExcess,
      defectSum] using
      integrable_localPositiveExcess_defectSum_sq_special_of_P4
        hP hstat hStruct hP4 hkm e
  have hcomponent :
      σ * (∫ a, (gradWeak a) ^ 2 ∂P) +
          σ⁻¹ * (∫ a, (fluxWeak a) ^ 2 ∂P)
        ≤
      16 *
        (highScaleAverage +
          K ^ 2 *
            (∫ a,
              (σ *
                  (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientMismatchTermAtScale
                    (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
                σ⁻¹ *
                  (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxMismatchTermAtScale
                    (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P) +
          K ^ 2 * lowScaleTail + K ^ 2 * constantTail) := by
    simpa [β, s, s', t, t', Q, p_e, q_e, p0_e, q0_e, σ, K,
      gradWeak, fluxWeak, highScaleAverage, lowScaleTail, constantTail] using
      paired_weakNormSquares_special_le_componentIntegrals
        hP hstat hStruct hP4 hkm e he hGradSq hFluxSq
  have hmis :
      (∫ a,
        (σ *
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientMismatchTermAtScale
              (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
          σ⁻¹ *
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxMismatchTermAtScale
              (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P)
        ≤ localSlots := by
    simpa [β, s, s', t, t', Q, p_e, q_e, σ, lowerExcess, upperExcess,
      defectSum, lowerEdge, localSlots] using
      integral_paired_mismatchTermSquares_special_le_rawHighContrastWeakNormSlots_local
        hP hstat hStruct hP4 hkm e hLowerEdge_int
  have hmis_scaled :
      K ^ 2 *
        (∫ a,
          (σ *
              (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientMismatchTermAtScale
                (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
            σ⁻¹ *
              (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxMismatchTermAtScale
                (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P)
        ≤ K ^ 2 * localSlots :=
    mul_le_mul_of_nonneg_left hmis (sq_nonneg K)
  have hinside :
      highScaleAverage +
          K ^ 2 *
            (∫ a,
              (σ *
                  (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientMismatchTermAtScale
                    (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
                σ⁻¹ *
                  (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxMismatchTermAtScale
                    (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2) ∂P) +
          K ^ 2 * lowScaleTail + K ^ 2 * constantTail
        ≤
      highScaleAverage + K ^ 2 * localSlots +
        K ^ 2 * lowScaleTail + K ^ 2 * constantTail := by
    linarith
  exact hcomponent.trans
    (mul_le_mul_of_nonneg_left hinside (by norm_num : (0 : ℝ) ≤ 16))

end

end Homogenization.HighContrast.EntryScale
