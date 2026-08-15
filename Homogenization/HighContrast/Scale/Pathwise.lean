import Homogenization.HighContrast.Variance.ProbeMoment
import Homogenization.HighContrast.Scale.Capstone
import Homogenization.Book.Ch04.Theorems.StationaryExpectations
import Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.BudgetAbsorption

/-!
# the scale-uniform pathwise operator-norm budget (`C1′`)

This file discharges the single remaining analytic hypothesis of the
homogenization-scale capstone: the scale-uniform pathwise (C1′) bound

`√(fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct j Q a)
    ≤ pathwiseBudgetConstant d · Θ⁶`  a.e.,

for every `j : ℕ` and every triadic cube `Q` of scale `j`.  This is exactly the
`hpath` hypothesis of `thetaEllipticLaw_implies_homogenizationScale`
(`Capstone.lean`) and the `hPathwise` hypothesis of
`varianceBlockEstimate_of_thetaEllipticLaw` (`VarianceEstimate.lean`).

## Route

* **Origin cube (`origin_pathwise_bound`).**  The landed finite-net bound
  `fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_probeSqBudget_ae`
  controls the observable a.e. by `|BlockCoord d|² · fullBlockProbeSqBudget H`,
  a finite sum of squared quadratic probes of the normalized fluctuation matrix
  `H = D·(A − Ā)·D`.  Each probe equals the centered block quadratic
  (`fluctuation_probe_eq_centered_blockQuadratic`) of the diagonally rescaled
  probe vector; the coarse term is a.e.-Loewner-bounded
  (`ae_coarseBlockQuadratic_bounds_of_thetaEllipticLaw`) and the annealed term is
  its mean (`mean_zero_coarse_blockQuadratic`), so each probe is a.e. bounded in
  absolute value by `16Θ` (using `½ ≤ b`, `c ≤ 2Θ` from `ScalarBounds`, the
  `M`-factor bound, and `⟪q,q⟫ ≤ 4`).  Collecting: the budget is
  `≤ |BlockCoord d|⁴ · 9 · (16Θ)²`, the observable is
  `≤ |BlockCoord d|⁶ · 2304 · Θ²`, and its square root is `≤ 48·|BlockCoord d|³·Θ
  = pathwiseBudgetConstant d · Θ ≤ pathwiseBudgetConstant d · Θ⁶`.

* **Transfer to a general cube (`pathwise_transfer`).**  At nonnegative scale a
  triadic cube is an integer translate of the origin cube at the same scale
  (`cubeSet_eq_translateSet_originCube_of_nonneg_scale`), and the observable is
  translation-covariant in its set argument
  (`fullBlockNormalizedFluctuationOperatorNormSq_translation_covariant`).
  Stationarity (`hStruct.stationary`) makes `translateByInt z`
  measure-preserving, so `QuasiMeasurePreserving.ae` pushes the origin-cube a.e.
  bound forward to `Q`.

* **`pathwise_fluctuation_bound`.**  Combining the two steps gives
  the capstone hypothesis, sorry-free.  The two corollaries instantiate the
  variance block estimate and the capstone with `hPathwise`/`hpath` discharged.
-/

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch04
  (RestrictionCoeffLaw RestrictionLawCarrier RestrictionStructuralLaw annealedBlockMatrixAtScale scalarFullBlockInvSqrtDiag
    fullBlockNormalizedFluctuationOperatorNormSqAtScale
    fullBlockNormalizedFluctuationOperatorNormSq
    fullBlockNormalizedFluctuationOperatorNormSq_translation_covariant
    cubeSet_eq_translateSet_originCube_of_nonneg_scale scaleTranslationShift)
open Homogenization.Book.Ch05 (QuantitativeCoarseGrainedEllipticity)
open Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale
  (fullBlockNormalizedFluctuationMatrix fullBlockNormalizedFluctuationMatrix_isSymm_ae
    fullBlockQuadratic fullBlockProbeSqBudget fullBlockCoordinateProbe fullBlockPlusProbe
    fullBlockMinusProbe fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_probeSqBudget_ae
    dotProduct_coordinateProbe_self dotProduct_plusProbe_self_le_four
    dotProduct_minusProbe_self_le_four)

namespace Homogenization

open Homogenization.HighContrast.EntryScale

variable {d : ℕ}

/-! ## The `M`-factor bound for the diagonally rescaled probe vector -/

/-- With `½ ≤ b`, `0 ≤ c ≤ 2Θ`, the `N2` weight of the diagonally rescaled probe
vector `w = D q` (`D = diag(scalarFullBlockInvSqrtDiag b c)`) is at most
`2Θ·⟪q,q⟫`.  This is the (private) `M`-factor bound of `ProbeMoment.lean`,
re-derived here for the deterministic pathwise estimate. -/
private theorem mfactor_bound [NeZero d] {b c Θ : ℝ}
    (hb : (1 / 2 : ℝ) ≤ b) (hc0 : 0 ≤ c) (hc : c ≤ 2 * Θ) (hΘ : 1 ≤ Θ)
    (q : FullBlockVec d) :
    Θ * vecNormSq (ofFullBlockVec (Matrix.mulVec
          (Matrix.diagonal (scalarFullBlockInvSqrtDiag b c)) q)).1
      + vecNormSq (ofFullBlockVec (Matrix.mulVec
          (Matrix.diagonal (scalarFullBlockInvSqrtDiag b c)) q)).2
      ≤ 2 * Θ * dotProduct q q := by
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le (by norm_num) hb
  have hΘ0 : (0 : ℝ) ≤ Θ := le_trans (by norm_num) hΘ
  have hw1 : (ofFullBlockVec (Matrix.mulVec
        (Matrix.diagonal (scalarFullBlockInvSqrtDiag b c)) q)).1
      = (Real.sqrt b)⁻¹ • (fun i => q (Sum.inl i)) := by
    funext i
    simp [ofFullBlockVec, Matrix.mulVec_diagonal, scalarFullBlockInvSqrtDiag]
  have hw2 : (ofFullBlockVec (Matrix.mulVec
        (Matrix.diagonal (scalarFullBlockInvSqrtDiag b c)) q)).2
      = (Real.sqrt c) • (fun i => q (Sum.inr i)) := by
    funext i
    simp [ofFullBlockVec, Matrix.mulVec_diagonal, scalarFullBlockInvSqrtDiag]
  rw [hw1, hw2, vecNormSq_smul, vecNormSq_smul]
  have hsqb : (Real.sqrt b)⁻¹ ^ 2 = b⁻¹ := by rw [inv_pow, Real.sq_sqrt hb0.le]
  have hsqc : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc0
  rw [hsqb, hsqc]
  have hbinv : b⁻¹ ≤ 2 := by
    have h := (inv_le_inv₀ hb0 (show (0 : ℝ) < 1 / 2 by norm_num)).mpr hb
    norm_num at h; exact h
  have hqU : (0 : ℝ) ≤ vecNormSq (fun i => q (Sum.inl i)) := vecNormSq_nonneg _
  have hqL : (0 : ℝ) ≤ vecNormSq (fun i => q (Sum.inr i)) := vecNormSq_nonneg _
  have hdqq : dotProduct q q
      = vecNormSq (fun i => q (Sum.inl i)) + vecNormSq (fun i => q (Sum.inr i)) := by
    rw [dotProduct, Fintype.sum_sum_type]
    simp [vecNormSq, vecDot]
  rw [hdqq]
  have t1 : (0 : ℝ) ≤ (2 - b⁻¹) * (Θ * vecNormSq (fun i => q (Sum.inl i))) :=
    mul_nonneg (by linarith) (mul_nonneg hΘ0 hqU)
  have t2 : (0 : ℝ) ≤ (2 * Θ - c) * vecNormSq (fun i => q (Sum.inr i)) :=
    mul_nonneg (by linarith) hqL
  nlinarith [t1, t2]

/-! ## The finite probe-square budget under a uniform probe bound -/

/-- If every coordinate/plus/minus probe of a full-block matrix `M` has absolute
quadratic value at most `K ≥ 0`, then the dimension-weighted probe-square budget
is at most `|BlockCoord d|⁴ · 9K²`. -/
theorem fullBlockProbeSqBudget_le (M : FullBlockMat d) (K : ℝ) (_hK : 0 ≤ K)
    (hcoord : ∀ α : BlockCoord d, |fullBlockQuadratic M (fullBlockCoordinateProbe α)| ≤ K)
    (hplus : ∀ α β : BlockCoord d, |fullBlockQuadratic M (fullBlockPlusProbe α β)| ≤ K)
    (hminus : ∀ α β : BlockCoord d, |fullBlockQuadratic M (fullBlockMinusProbe α β)| ≤ K) :
    fullBlockProbeSqBudget M ≤ (Fintype.card (BlockCoord d) : ℝ) ^ 4 * (9 * K ^ 2) := by
  classical
  set n : ℝ := (Fintype.card (BlockCoord d) : ℝ) with hn
  have hn0 : 0 ≤ n := by rw [hn]; exact_mod_cast Nat.zero_le _
  -- pointwise inner bound
  have hg : ∀ α β : BlockCoord d,
      3 * ((fullBlockQuadratic M (fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
          (fullBlockQuadratic M (fullBlockPlusProbe α β)) ^ (2 : ℕ) +
          (fullBlockQuadratic M (fullBlockMinusProbe α β)) ^ (2 : ℕ)) ≤ 9 * K ^ 2 := by
    intro α β
    have h1 : (fullBlockQuadratic M (fullBlockCoordinateProbe α)) ^ (2 : ℕ) ≤ K ^ 2 :=
      sq_le_sq' (abs_le.mp (hcoord α)).1 (abs_le.mp (hcoord α)).2
    have h2 : (fullBlockQuadratic M (fullBlockPlusProbe α β)) ^ (2 : ℕ) ≤ K ^ 2 :=
      sq_le_sq' (abs_le.mp (hplus α β)).1 (abs_le.mp (hplus α β)).2
    have h3 : (fullBlockQuadratic M (fullBlockMinusProbe α β)) ^ (2 : ℕ) ≤ K ^ 2 :=
      sq_le_sq' (abs_le.mp (hminus α β)).1 (abs_le.mp (hminus α β)).2
    nlinarith [h1, h2, h3]
  -- per-`α` bound
  have hstep : ∀ α : BlockCoord d,
      n * ∑ β : BlockCoord d,
          3 * ((fullBlockQuadratic M (fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
            (fullBlockQuadratic M (fullBlockPlusProbe α β)) ^ (2 : ℕ) +
            (fullBlockQuadratic M (fullBlockMinusProbe α β)) ^ (2 : ℕ))
        ≤ n * (n * (9 * K ^ 2)) := by
    intro α
    have hβ :
        (∑ β : BlockCoord d,
            3 * ((fullBlockQuadratic M (fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
              (fullBlockQuadratic M (fullBlockPlusProbe α β)) ^ (2 : ℕ) +
              (fullBlockQuadratic M (fullBlockMinusProbe α β)) ^ (2 : ℕ)))
          ≤ n * (9 * K ^ 2) := by
      calc
        (∑ β : BlockCoord d,
            3 * ((fullBlockQuadratic M (fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
              (fullBlockQuadratic M (fullBlockPlusProbe α β)) ^ (2 : ℕ) +
              (fullBlockQuadratic M (fullBlockMinusProbe α β)) ^ (2 : ℕ)))
            ≤ ∑ _β : BlockCoord d, (9 * K ^ 2) :=
              Finset.sum_le_sum (fun β _ => hg α β)
        _ = n * (9 * K ^ 2) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn]
    exact mul_le_mul_of_nonneg_left hβ hn0
  -- assemble
  unfold fullBlockProbeSqBudget
  rw [← hn]
  calc
    n * ∑ α : BlockCoord d,
        n * ∑ β : BlockCoord d,
          3 * ((fullBlockQuadratic M (fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
            (fullBlockQuadratic M (fullBlockPlusProbe α β)) ^ (2 : ℕ) +
            (fullBlockQuadratic M (fullBlockMinusProbe α β)) ^ (2 : ℕ))
        ≤ n * ∑ _α : BlockCoord d, (n * (n * (9 * K ^ 2))) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun α _ => hstep α)) hn0
    _ = n * (n * (n * (n * (9 * K ^ 2)))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn]
    _ = n ^ 4 * (9 * K ^ 2) := by ring

/-! ## The a.e. per-probe pathwise bound at the origin cube -/

/-- Each quadratic probe of the normalized fluctuation matrix
`H = D·(A − Ā)·D` on the origin cube at scale `m` is a.e. bounded in absolute
value by `16Θ`, for any probe vector `q` with `⟪q,q⟫ ≤ 4`. -/
theorem probe_abs_le_ae [NeZero d] {Θ : ℝ} (hΘ : 1 ≤ Θ) {P : RestrictionCoeffLaw d}
    [IsProbabilityMeasure P] (hP : RestrictionLawCarrier P) (hStruct : RestrictionStructuralLaw P)
    (hLaw : ThetaEllipticLaw Θ P) (m : ℤ) (q : FullBlockVec d) (hq : dotProduct q q ≤ 4) :
    ∀ᵐ (a : RegCoeffField d) ∂P, |fullBlockQuadratic
        (fullBlockNormalizedFluctuationMatrix hP hStruct m (cubeSet (originCube d m)) a) q|
      ≤ 16 * Θ := by
  have hΘ0 : (0 : ℝ) ≤ Θ := le_trans (by norm_num) hΘ
  set b := hP.barSigmaAtScale hStruct m with hbdef
  set c := hP.barSigmaStarAtScale hStruct m with hcdef
  set w : BlockVec d := ofFullBlockVec (Matrix.mulVec
    (Matrix.diagonal (scalarFullBlockInvSqrtDiag b c)) q) with hwdef
  set c0 : ℝ := blockVecDot w (blockMatVecMul (annealedBlockMatrixAtScale P m) w) with hc0def
  -- probe = centered coarse block quadratic minus its annealed mean
  have hpt : ∀ a : RegCoeffField d,
      fullBlockQuadratic
          (fullBlockNormalizedFluctuationMatrix hP hStruct m (cubeSet (originCube d m)) a) q
        = blockVecDot w
            (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a) w) - c0 := by
    intro a
    rw [fluctuation_probe_eq_centered_blockQuadratic hP hStruct m q a,
      blockVecDot_blockMatVecMul_ofFullBlockMat_sub]
  -- coarse-block a.e. bounds and the annealed mean identity
  have hX_int := integrable_coarseBlockQuadratic_of_thetaEllipticLaw hΘ hP hLaw m w
  have hbounds := ae_coarseBlockQuadratic_bounds_of_thetaEllipticLaw hΘ hLaw m w
  have hmean := mean_zero_coarse_blockQuadratic hΘ hP hLaw m w
  -- the constant `c0 = E[X]` lies in `[0, Mub]`
  have hc0_lower : 0 ≤ c0 := by
    rw [hc0def, ← hmean]
    exact integral_nonneg_of_ae (hbounds.mono fun a ha => ha.1)
  have hc0_upper : c0 ≤ 2 * (Θ * vecNormSq w.1 + vecNormSq w.2) := by
    rw [hc0def, ← hmean]
    calc
      ∫ a, blockVecDot w
            (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a) w) ∂P
          ≤ ∫ _a, (2 * (Θ * vecNormSq w.1 + vecNormSq w.2)) ∂P :=
            integral_mono_ae hX_int (integrable_const _) (hbounds.mono fun a ha => ha.2)
      _ = 2 * (Θ * vecNormSq w.1 + vecNormSq w.2) := by simp
  -- the `M`-factor bound: `Mub ≤ 16Θ`
  have hmf : Θ * vecNormSq w.1 + vecNormSq w.2 ≤ 2 * Θ * dotProduct q q := by
    rw [hwdef]
    exact mfactor_bound (b := b) (c := c)
      (half_le_barSigmaAtScale hΘ hP hStruct hLaw m)
      (barSigmaStarAtScale_pos hΘ hP hStruct hLaw m).le
      (barSigmaStarAtScale_le_two_mul_Theta hΘ hP hStruct hLaw m) hΘ q
  have hMub_le : 2 * (Θ * vecNormSq w.1 + vecNormSq w.2) ≤ 16 * Θ := by
    have hdq : 2 * Θ * dotProduct q q ≤ 2 * Θ * 4 :=
      mul_le_mul_of_nonneg_left hq (by linarith)
    nlinarith [hmf, hdq]
  -- combine
  filter_upwards [hbounds] with a ha
  rw [hpt a, abs_le]
  refine ⟨by nlinarith [ha.1, ha.2, hc0_lower, hc0_upper, hMub_le],
    by nlinarith [ha.1, ha.2, hc0_lower, hc0_upper, hMub_le]⟩

/-! ## The origin-cube pathwise bound (`C1′`) -/

/-- **Step 1 — origin cube.**  The normalized fluctuation observable at the
origin cube of scale `m` satisfies the scale-uniform pathwise budget a.e. -/
theorem origin_pathwise_bound [NeZero d] {Θ : ℝ} (hΘ : 1 ≤ Θ) {P : RestrictionCoeffLaw d}
    [IsProbabilityMeasure P] (hP : RestrictionLawCarrier P) (hStruct : RestrictionStructuralLaw P)
    (hLaw : ThetaEllipticLaw Θ P) (m : ℤ) :
    ∀ᵐ a ∂P, Real.sqrt
        (fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct m (originCube d m) a)
      ≤ pathwiseBudgetConstant d * Θ ^ 6 := by
  classical
  have hK0 : (0 : ℝ) ≤ 16 * Θ := by linarith [hΘ]
  -- all three probe families are simultaneously bounded a.e.
  have hall : ∀ᵐ (a : RegCoeffField d) ∂P, ∀ α β : BlockCoord d,
      |fullBlockQuadratic
          (fullBlockNormalizedFluctuationMatrix hP hStruct m (cubeSet (originCube d m)) a)
          (fullBlockCoordinateProbe α)| ≤ 16 * Θ ∧
      |fullBlockQuadratic
          (fullBlockNormalizedFluctuationMatrix hP hStruct m (cubeSet (originCube d m)) a)
          (fullBlockPlusProbe α β)| ≤ 16 * Θ ∧
      |fullBlockQuadratic
          (fullBlockNormalizedFluctuationMatrix hP hStruct m (cubeSet (originCube d m)) a)
          (fullBlockMinusProbe α β)| ≤ 16 * Θ := by
    rw [ae_all_iff]
    intro α
    rw [ae_all_iff]
    intro β
    have hc := probe_abs_le_ae hΘ hP hStruct hLaw m (fullBlockCoordinateProbe α)
      (by rw [dotProduct_coordinateProbe_self]; norm_num)
    have hp := probe_abs_le_ae hΘ hP hStruct hLaw m (fullBlockPlusProbe α β)
      (dotProduct_plusProbe_self_le_four α β)
    have hmn := probe_abs_le_ae hΘ hP hStruct hLaw m (fullBlockMinusProbe α β)
      (dotProduct_minusProbe_self_le_four α β)
    filter_upwards [hc, hp, hmn] with a h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hprobe :=
    fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_probeSqBudget_ae
      hP hStruct m (originCube d m)
  filter_upwards [hall, hprobe] with a hb hpr
  -- budget bound at `K = 16Θ`
  have hbudget :
      fullBlockProbeSqBudget
          (fullBlockNormalizedFluctuationMatrix hP hStruct m (cubeSet (originCube d m)) a)
        ≤ (Fintype.card (BlockCoord d) : ℝ) ^ 4 * (9 * (16 * Θ) ^ 2) :=
    fullBlockProbeSqBudget_le _ (16 * Θ) hK0
      (fun α => (hb α α).1) (fun α β => (hb α β).2.1) (fun α β => (hb α β).2.2)
  -- observable bound
  have hobs_le :
      fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct m (originCube d m) a
        ≤ (Fintype.card (BlockCoord d) : ℝ) ^ 2 *
            ((Fintype.card (BlockCoord d) : ℝ) ^ 4 * (9 * (16 * Θ) ^ 2)) :=
    le_trans hpr (mul_le_mul_of_nonneg_left hbudget (by positivity))
  -- square-root arithmetic
  have hsq :
      (Fintype.card (BlockCoord d) : ℝ) ^ 2 *
          ((Fintype.card (BlockCoord d) : ℝ) ^ 4 * (9 * (16 * Θ) ^ 2))
        = (48 * (Fintype.card (BlockCoord d) : ℝ) ^ 3 * Θ) ^ 2 := by ring
  have hp2 : Θ ≤ Θ ^ 2 := by nlinarith [hΘ]
  have hp2' : (1 : ℝ) ≤ Θ ^ 2 := by nlinarith [hΘ]
  have hp4 : (1 : ℝ) ≤ Θ ^ 4 := by nlinarith [hp2', sq_nonneg (Θ ^ 2 - 1)]
  have hp6 : Θ ^ 2 ≤ Θ ^ 6 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ Θ ^ 4 - 1 by linarith [hp4]) (sq_nonneg Θ)]
  have hΘ6 : Θ ≤ Θ ^ 6 := le_trans hp2 hp6
  calc
    Real.sqrt
        (fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct m (originCube d m) a)
        ≤ Real.sqrt
            ((Fintype.card (BlockCoord d) : ℝ) ^ 2 *
              ((Fintype.card (BlockCoord d) : ℝ) ^ 4 * (9 * (16 * Θ) ^ 2))) :=
          Real.sqrt_le_sqrt hobs_le
    _ = 48 * (Fintype.card (BlockCoord d) : ℝ) ^ 3 * Θ := by
          rw [hsq, Real.sqrt_sq (by positivity)]
    _ ≤ pathwiseBudgetConstant d * Θ ^ 6 := by
          unfold pathwiseBudgetConstant
          have hcard : (0 : ℝ) ≤ 48 * (Fintype.card (BlockCoord d) : ℝ) ^ 3 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hΘ6 hcard]

/-! ## Transfer to a general cube of the same scale (`C1′`) -/

/-- **Step 2 — stationary transfer.**  A pathwise a.e. bound at the origin cube
of scale `Q.scale` transfers to any nonnegative-scale triadic cube `Q`, using
translation covariance of the observable and stationarity of `P`. -/
theorem pathwise_transfer [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hStruct : RestrictionStructuralLaw P) (center : ℤ) (Q : TriadicCube d)
    (hQ_nonneg : 0 ≤ Q.scale) (C : ℝ)
    (horigin : ∀ᵐ b ∂P, Real.sqrt
        (fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d Q.scale) b) ≤ C) :
    ∀ᵐ a ∂P, Real.sqrt
        (fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct center Q a) ≤ C := by
  set z : Fin d → ℤ := scaleTranslationShift Q.scale Q with hz
  have hmp : MeasurePreserving (translateReg (intVecToRealVec z)) P P :=
    ⟨measurable_translateReg (intVecToRealVec z), hStruct.stationary z⟩
  have htrans :=
    hmp.quasiMeasurePreserving.ae
      (p := fun b => Real.sqrt
        (fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct center (originCube d Q.scale) b) ≤ C) horigin
  have hset : cubeSet Q =
      translateSet (intVecToRealVec z) (cubeSet (originCube d Q.scale)) := by
    simpa [hz] using cubeSet_eq_translateSet_originCube_of_nonneg_scale (R := Q) hQ_nonneg
  filter_upwards [htrans] with a ha
  have hid :
      fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct center Q a
        = fullBlockNormalizedFluctuationOperatorNormSq hP hStruct center
            (cubeSet (originCube d Q.scale)) (translateReg (intVecToRealVec z) a) := by
    rw [fullBlockNormalizedFluctuationOperatorNormSqAtScale, hset]
    exact fullBlockNormalizedFluctuationOperatorNormSq_translation_covariant
      hP hStruct center (cubeSet (originCube d Q.scale)) z a
  rw [hid]
  exact ha

/-! ## The scale-uniform pathwise budget -/

/-- **The scale-uniform pathwise (C1′) operator-norm budget.**

For every `j : ℕ` and every triadic cube `Q` of scale `j`, the normalized
full-block fluctuation observable satisfies
`√(observable) ≤ pathwiseBudgetConstant d · Θ⁶` almost surely.  This is exactly
the `hpath` hypothesis of `thetaEllipticLaw_implies_homogenizationScale` and the
`hPathwise` hypothesis of `varianceBlockEstimate_of_thetaEllipticLaw`. -/
theorem pathwise_fluctuation_bound [NeZero d] {Θ : ℝ} (hΘ : 1 ≤ Θ) {P : RestrictionCoeffLaw d}
    [IsProbabilityMeasure P] (hP : RestrictionLawCarrier P) (hStruct : RestrictionStructuralLaw P)
    (hLaw : ThetaEllipticLaw Θ P) {j : ℕ} {Q : TriadicCube d} (hQ : Q.scale = (j : ℤ)) :
    ∀ᵐ a ∂P, Real.sqrt
        (fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct (j : ℤ) Q a)
      ≤ pathwiseBudgetConstant d * Θ ^ 6 := by
  have hQ_nonneg : 0 ≤ Q.scale := by rw [hQ]; exact_mod_cast Nat.zero_le j
  have horigin :
      ∀ᵐ b ∂P, Real.sqrt
          (fullBlockNormalizedFluctuationOperatorNormSqAtScale
            hP hStruct (j : ℤ) (originCube d Q.scale) b) ≤ pathwiseBudgetConstant d * Θ ^ 6 := by
    rw [hQ]
    exact origin_pathwise_bound hΘ hP hStruct hLaw (j : ℤ)
  exact pathwise_transfer hP hStruct (j : ℤ) Q hQ_nonneg
    (pathwiseBudgetConstant d * Θ ^ 6) horigin

/-! ## Corollaries — discharging the isolated inputs -/

/-- **Corollary — the variance block estimate, pathwise-discharged.**  The
`VarianceBlockEstimate` of `varianceBlockEstimate_of_thetaEllipticLaw` with its
`hPathwise` hypothesis supplied by `pathwise_fluctuation_bound`. -/
theorem varianceBlockEstimate_of_thetaEllipticLaw' [NeZero d] (hd : 3 ≤ d)
    {Θ : ℝ} (hΘ : 1 ≤ Θ) {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    (hP : RestrictionLawCarrier P) (hStruct : RestrictionStructuralLaw P)
    (hLaw : Homogenization.ThetaEllipticLaw Θ P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (N2 : ℕ) :
    VarianceBlockEstimate (vpParams d hd Θ) P
      (Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) N2
      (intermediateCoarseBlockDeviation hP hStruct (fun x : RegCoeffField d => x)) :=
  varianceBlockEstimate_of_thetaEllipticLaw hd hΘ hP hStruct hLaw hP4 N2
    (fun {_j} _ {_Q} hQ => pathwise_fluctuation_bound hΘ hP hStruct hLaw hQ)

/-- **Corollary — the homogenization-scale capstone, pathwise-discharged.**
`thetaEllipticLaw_implies_homogenizationScale` with its `hpath` hypothesis
supplied by `pathwise_fluctuation_bound`. -/
-- Intermediate: the pathwise-discharged per-`hP4` capstone; the unconditional
-- headline is `homogenizationScale_polynomial_of_unitRange` (`Final.lean`).
theorem thetaEllipticLaw_implies_homogenizationScale' {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    (hc : HighContrastExponents d)
    (params : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    (loc : LocalizationSmallContrastInput hc) (hcp : hc.params = params)
    {Θ : ℝ} (hΘ : 1 ≤ Θ) {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    (hP : RestrictionLawCarrier P) (hStruct : RestrictionStructuralLaw P)
    (hLaw : Homogenization.ThetaEllipticLaw Θ P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (hparams : hP4.params = params) :
    ∃ Cscale Ctriadic alpha : ℝ, 0 < Cscale ∧ 0 < Ctriadic ∧ 0 < alpha ∧
      ∃ N0 : ℕ,
        (∀ n : ℕ,
          Homogenization.Book.Ch05.thetaAtScale hP hStruct ((N0 + n : ℕ) : ℤ) - 1 ≤
            (3 : ℝ) ^ (-alpha * (n : ℝ))) ∧
        (N0 : ℝ) ≤ Cscale * Real.log (2 + Θ) ∧
        (3 : ℝ) ^ (N0 : ℝ) ≤ (2 + Θ) ^ Ctriadic :=
  thetaEllipticLaw_implies_homogenizationScale hd hc params loc hcp hΘ hP hStruct hLaw hP4 hparams
    (fun {_j} {_Q} hQ => pathwise_fluctuation_bound hΘ hP hStruct hLaw hQ)

end Homogenization
