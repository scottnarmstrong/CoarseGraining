import Homogenization.CoarseGraining.CoarseBounds.Sandwich
import Homogenization.CoarseGraining.CoarseBounds.AeBridge
import Homogenization.CoarseGraining.ThetaEllipticity
import Homogenization.Book.Ch04.Theorems.WidetildeTheta
import Homogenization.Book.Ch04.Theorems.MomentFactorBounds.FactorBounds
import Homogenization.CoarseGraining.OriginCubeOpenBridge
import Homogenization.CoarseGraining.Translation
import Homogenization.Geometry.TriadicCubeTranslation
import Homogenization.Book.Ch05.Definitions

/-!
# Uniform ellipticity controls `widetildeTheta`

Under a `ThetaEllipticLaw Θ P` on a probability law, the moment-enhanced contrast
`widetildeThetaAtScale P 0 sUpper sLower ξ` is bounded by `4 * Θ`.

Route: `widetildeThetaAtScale = LambdaMomentAtScale * lambdaInvMomentAtScale`.
The C1 upper sandwich gives, for every triadic cube `R`,
`matrixNorm (coarseBlockMatrix (cubeSet R) a).upperLeft ≤ 2Θ` and
`matrixNorm (coarseBlockMatrix (cubeSet R) a).lowerRight ≤ 2`; through the `q = 1`
tsum representation of `LambdaSqCoeffField` (geometric weights sum to `1`) this
yields `LambdaSqCoeffField … ≤ 2Θ` and `(lambdaSqCoeffField …)⁻¹ ≤ 2` a.s., hence
`LambdaMomentAtScale ≤ 2Θ`, `lambdaInvMomentAtScale ≤ 2`, and `widetildeTheta ≤ 4Θ`.
Constants: `C = 4`, `k = 1` (independent of `d`, `ξ`).
-/

namespace Homogenization

open Homogenization
open Homogenization.Book
open Homogenization.Book.Ch04
open MeasureTheory
open scoped Classical

noncomputable section

variable {d : ℕ} [NeZero d]

/-- A member is bounded by the real finite supremum. -/
private theorem le_finsetSupReal {α : Type*} (s : Finset α) (f : α → ℝ) {R : α}
    (hR : R ∈ s) : f R ≤ Ch02.finsetSupReal s f := by
  have hbdd : BddAbove (f '' (↑s : Set α)) := (s.finite_toSet.image f).bddAbove
  exact le_csSup hbdd ⟨R, hR, rfl⟩

/-! ## Deterministic per-cube operator-norm bounds -/

/-- Translate-ellipticity (local rebuild of the private LIH lemma): pointwise
ellipticity on `translateSet z U` transfers to the translated coefficient
field on `U`. -/
private theorem isEllipticFieldOn_translateCoeffField_of_translateSet
    {lam Lam : ℝ} {U : Set (Vec d)} {a : CoeffField d} (z : Vec d)
    (hEll : IsEllipticFieldOn lam Lam (translateSet z U) a) :
    IsEllipticFieldOn lam Lam U (translateCoeffField z a) := by
  classical
  refine ⟨?_, ?_⟩
  · have hshift : Measurable (fun x : Vec d => x + z) :=
      (continuous_id.add continuous_const).measurable
    have hcomp :
        Measurable (fun x i j => if x + z ∈ translateSet z U then a (x + z) i j else 0) := by
      simpa [Function.comp] using hEll.1.comp hshift
    have hEq :
        (fun x i j => if x + z ∈ translateSet z U then a (x + z) i j else 0) =
          (fun x i j => if x ∈ U then translateCoeffField z a x i j else 0) := by
      funext x i j
      have hadd_sub : x + z - z = x := by
        ext k; simp [sub_eq_add_neg, add_assoc]
      by_cases hx : x ∈ U
      · have hxt : x + z ∈ translateSet z U := by
          rw [mem_translateSet_iff_sub_mem, hadd_sub]; exact hx
        simp [hx, hxt]; rfl
      · have hxt : x + z ∉ translateSet z U := by
          intro hmem
          rw [mem_translateSet_iff_sub_mem, hadd_sub] at hmem
          exact hx hmem
        simp [hx, hxt]
    simpa [hEq] using hcomp
  · intro x hx
    have hxt : x + z ∈ translateSet z U := by
      have hadd_sub : x + z - z = x := by
        ext k; simp [sub_eq_add_neg, add_assoc]
      rw [mem_translateSet_iff_sub_mem, hadd_sub]; exact hx
    simpa [translateCoeffField] using hEll.2 (x + z) hxt

/-- General-cube coarse-block upper sandwich: the origin-cube C1 upper
sandwich, moved to an arbitrary triadic cube by translation covariance. -/
theorem coarseBlockMatrix_cubeSet_blockMatLoewnerLE_blockDiag
    {Q : TriadicCube d} {Θ : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet Q) a) :
    BlockMatLoewnerLE (coarseBlockMatrix (cubeSet Q) a)
      (Ch02.blockDiag ((2 * Θ) • (1 : Mat d)) ((2 : ℝ) • (1 : Mat d))) := by
  set z : Vec d := triadicCubeShift Q with hz
  have hcube : cubeSet Q = translateSet z (cubeSet (originCube d Q.scale)) :=
    cubeSet_eq_translateSet_originCube_of_triadicCube Q
  have hEllT :
      IsEllipticFieldOn 1 Θ (cubeSet (originCube d Q.scale)) (translateCoeffField z a) := by
    apply isEllipticFieldOn_translateCoeffField_of_translateSet z
    rwa [← hcube]
  have hmat :
      coarseBlockMatrix (cubeSet Q) a =
        coarseBlockMatrix (cubeSet (originCube d Q.scale)) (translateCoeffField z a) := by
    rw [hcube]
    exact coarseBlockMatrix_translateSet_eq_translateCoeffField z _ a
  rw [hmat]
  exact coarseBlockMatrix_blockMatLoewnerLE_blockDiag_cube hEllT

/-- PSD of the upper-left coarse block on any cube, from a.e.-local ellipticity. -/
private theorem coarseBlockMatrix_upperLeft_posSemidef
    {R : TriadicCube d} {a : CoeffField d}
    (ha : AELocallyUniformlyEllipticField a) :
    ((coarseBlockMatrix (cubeSet R) a).upperLeft).PosSemidef := by
  have hEqR :
      coarseBlockMatrix (cubeSet R) a =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain R)
          ((triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R) :=
    LawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
      ha R
  rw [hEqR]
  simpa using
    Ch02.bCoarse_posSemidef (Ch02.cubeDomain R)
      ((triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R)

/-- PSD of the lower-right coarse block on any cube, from a.e.-local ellipticity. -/
private theorem coarseBlockMatrix_lowerRight_posSemidef
    {R : TriadicCube d} {a : CoeffField d}
    (ha : AELocallyUniformlyEllipticField a) :
    ((coarseBlockMatrix (cubeSet R) a).lowerRight).PosSemidef := by
  have hEqR :
      coarseBlockMatrix (cubeSet R) a =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain R)
          ((triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R) :=
    LawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
      ha R
  rw [hEqR]
  exact
    (Ch02.sigmaStarInvCoarse_posDef (Ch02.cubeDomain R)
      ((triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R)).posSemidef

/-- The `cubeSet R`-truncated coefficient field is entrywise measurable. -/
private theorem measurable_ite_cubeSet
    {R : TriadicCube d} {a : CoeffField d}
    (hmeas : ∀ i j : Fin d, Measurable fun x : Vec d => a x i j) :
    Measurable (fun x => fun i j => if x ∈ cubeSet R then a x i j else 0) := by
  classical
  refine measurable_pi_iff.2 (fun i => measurable_pi_iff.2 (fun j => ?_))
  exact Measurable.ite (measurableSet_cubeSet R) (hmeas i j) measurable_const

/-- Operator-norm consequence of the general-cube upper sandwich, on an
everywhere-`(1,Θ)`-elliptic field with the block already known PSD.  All matrix
arguments are syntactically identical, avoiding whnf of the coarse matrix. -/
private theorem matrixNorm_upperLeft_le_of_isEllipticFieldOn
    {R : TriadicCube d} {Θ : ℝ} {b : CoeffField d} (hΘ0 : (0 : ℝ) ≤ 2 * Θ)
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet R) b)
    (hPSD : ((coarseBlockMatrix (cubeSet R) b).upperLeft).PosSemidef) :
    Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) b).upperLeft ≤ 2 * Θ := by
  have hblk :
      (Ch02.blockDiag ((2 * Θ) • (1 : Mat d)) ((2 : ℝ) • (1 : Mat d))).upperLeft =
        (2 * Θ) • (1 : Mat d) := rfl
  have hUL :=
    matLoewnerLE_upperLeft_of_blockMatLoewnerLE
      (coarseBlockMatrix_cubeSet_blockMatLoewnerLE_blockDiag hEll)
  rw [hblk] at hUL
  have hscal : ((2 * Θ) • (1 : Mat d)).PosSemidef := (Matrix.PosSemidef.one).smul hΘ0
  rw [Ch02.matrixNorm_eq_matrixOperatorNorm]
  calc
    Ch02.matrixOperatorNorm (coarseBlockMatrix (cubeSet R) b).upperLeft
        ≤ Ch02.matrixOperatorNorm ((2 * Θ) • (1 : Mat d)) :=
          Ch02.matrixOperatorNorm_le_of_matLoewnerLE_of_posSemidef hPSD hscal hUL
    _ = 2 * Θ := Ch02.matrixOperatorNorm_smul_one_eq_of_nonneg hΘ0

private theorem matrixNorm_lowerRight_le_of_isEllipticFieldOn
    {R : TriadicCube d} {Θ : ℝ} {b : CoeffField d}
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet R) b)
    (hPSD : ((coarseBlockMatrix (cubeSet R) b).lowerRight).PosSemidef) :
    Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) b).lowerRight ≤ 2 := by
  have hblk :
      (Ch02.blockDiag ((2 * Θ) • (1 : Mat d)) ((2 : ℝ) • (1 : Mat d))).lowerRight =
        (2 : ℝ) • (1 : Mat d) := rfl
  have hLR :=
    matLoewnerLE_lowerRight_of_blockMatLoewnerLE
      (coarseBlockMatrix_cubeSet_blockMatLoewnerLE_blockDiag hEll)
  rw [hblk] at hLR
  have hscal : ((2 : ℝ) • (1 : Mat d)).PosSemidef := (Matrix.PosSemidef.one).smul (by norm_num)
  rw [Ch02.matrixNorm_eq_matrixOperatorNorm]
  calc
    Ch02.matrixOperatorNorm (coarseBlockMatrix (cubeSet R) b).lowerRight
        ≤ Ch02.matrixOperatorNorm ((2 : ℝ) • (1 : Mat d)) :=
          Ch02.matrixOperatorNorm_le_of_matLoewnerLE_of_posSemidef hPSD hscal hLR
    _ = 2 := Ch02.matrixOperatorNorm_smul_one_eq_of_nonneg (by norm_num)

/-- **P1/P2-upper.** For an a.e.-`(1,Θ)`-elliptic, entrywise-measurable
realization, the upper-left coarse block on any cube has operator norm `≤ 2Θ`. -/
theorem matrixNorm_upperLeft_cubeSet_le
    {R : TriadicCube d} {Θ : ℝ} {a : CoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (hΘ : 1 ≤ Θ)
    (hmeas : ∀ i j : Fin d, Measurable fun x : Vec d => a x i j)
    (haeR : ∀ᵐ x ∂(volume.restrict (cubeSet R)), IsEllipticMatrix 1 Θ (a x)) :
    Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a).upperLeft ≤ 2 * Θ := by
  have hae_eq : a =ᵐ[volume.restrict (cubeSet R)] ellipticTruncate Θ a :=
    (ellipticTruncate_ae_eq haeR).symm
  have hM :
      coarseBlockMatrix (cubeSet R) a =
        coarseBlockMatrix (cubeSet R) (ellipticTruncate Θ a) :=
    coarseBlockMatrix_congr_of_ae_eq (measurableSet_cubeSet R) hae_eq
  have hEll' : IsEllipticFieldOn 1 Θ (cubeSet R) (ellipticTruncate Θ a) :=
    isEllipticFieldOn_ellipticTruncate (measurableSet_cubeSet R) hΘ
      (measurable_ite_cubeSet hmeas)
  have hPSD : ((coarseBlockMatrix (cubeSet R) (ellipticTruncate Θ a)).upperLeft).PosSemidef := by
    rw [← hM]; exact coarseBlockMatrix_upperLeft_posSemidef ha
  rw [hM]
  exact matrixNorm_upperLeft_le_of_isEllipticFieldOn (by linarith) hEll' hPSD

/-- **P1/P2-lower.** Lower-right coarse block operator norm `≤ 2`. -/
theorem matrixNorm_lowerRight_cubeSet_le
    {R : TriadicCube d} {Θ : ℝ} {a : CoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (hΘ : 1 ≤ Θ)
    (hmeas : ∀ i j : Fin d, Measurable fun x : Vec d => a x i j)
    (haeR : ∀ᵐ x ∂(volume.restrict (cubeSet R)), IsEllipticMatrix 1 Θ (a x)) :
    Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a).lowerRight ≤ 2 := by
  have hae_eq : a =ᵐ[volume.restrict (cubeSet R)] ellipticTruncate Θ a :=
    (ellipticTruncate_ae_eq haeR).symm
  have hM :
      coarseBlockMatrix (cubeSet R) a =
        coarseBlockMatrix (cubeSet R) (ellipticTruncate Θ a) :=
    coarseBlockMatrix_congr_of_ae_eq (measurableSet_cubeSet R) hae_eq
  have hEll' : IsEllipticFieldOn 1 Θ (cubeSet R) (ellipticTruncate Θ a) :=
    isEllipticFieldOn_ellipticTruncate (measurableSet_cubeSet R) hΘ
      (measurable_ite_cubeSet hmeas)
  have hPSD : ((coarseBlockMatrix (cubeSet R) (ellipticTruncate Θ a)).lowerRight).PosSemidef := by
    rw [← hM]; exact coarseBlockMatrix_lowerRight_posSemidef ha
  rw [hM]
  exact matrixNorm_lowerRight_le_of_isEllipticFieldOn hEll' hPSD

/-! ## `ThetaEllipticLaw` data → `AELocallyUniformlyEllipticField` -/

/-- Witness plumbing: an entrywise-measurable, a.e.-`(1,Θ)`-elliptic field is
locally a.e.-uniformly elliptic (uniform constants `(1,Θ)`). -/
theorem aeLocallyUniformlyEllipticField_of_ae_isEllipticMatrix
    {Θ : ℝ} {a : CoeffField d} (hΘ : 1 ≤ Θ)
    (hmeas : ∀ i j : Fin d, Measurable fun x : Vec d => a x i j)
    (hae : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 Θ (a x)) :
    AELocallyUniformlyEllipticField a := by
  intro Q
  refine ⟨1, Θ, one_pos, hΘ, (isOpen_openCubeSet Q).measurableSet, ?_, ?_⟩
  · intro i j
    have hcoord : Measurable fun x : Vec d => restrictCoeffField (openCubeSet Q) a x i j := by
      have h0 : Measurable fun x : Vec d => if x ∈ openCubeSet Q then a x i j else 0 :=
        Measurable.ite (isOpen_openCubeSet Q).measurableSet (hmeas i j) measurable_const
      have heq :
          (fun x : Vec d => restrictCoeffField (openCubeSet Q) a x i j) =
            fun x : Vec d => if x ∈ openCubeSet Q then a x i j else 0 := by
        funext x
        by_cases hx : x ∈ openCubeSet Q <;> simp [restrictCoeffField, hx]
      rw [heq]; exact h0
    exact hcoord.aestronglyMeasurable
  · exact ae_restrict_of_ae hae

/-! ## Pointwise `LambdaSqCoeffField` bounds via the `q = 1` tsum -/

/-- `(rpow c (1/2))² = c` for `c ≥ 0`. -/
private theorem rpow_half_sq {c : ℝ} (hc : 0 ≤ c) :
    (Real.rpow c (1 / 2)) ^ 2 = c := by
  show (c ^ (1 / 2 : ℝ)) ^ 2 = c
  rw [pow_two, ← Real.rpow_add' hc (by norm_num : (1 / 2 + 1 / 2 : ℝ) ≠ 0),
    show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one]

/-- **P3-upper.** Pointwise upper multiscale ellipticity bound at the origin
cube for an a.e.-elliptic, measurable realization. -/
theorem LambdaSqCoeffField_originCube_zero_le_of_ae
    {Θ s : ℝ} {a : CoeffField d} (hΘ : 1 ≤ Θ) (hs : 0 < s)
    (hmeas : ∀ i j : Fin d, Measurable fun x : Vec d => a x i j)
    (hae : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 Θ (a x)) :
    LambdaSqCoeffField (originCube d 0) s (.finite 1) a ≤ 2 * Θ := by
  have hΘ0 : (0 : ℝ) ≤ 2 * Θ := by linarith
  have ha : AELocallyUniformlyEllipticField a :=
    aeLocallyUniformlyEllipticField_of_ae_isEllipticMatrix hΘ hmeas hae
  set Q := originCube d 0 with hQ
  have hMax : ∀ n : ℕ,
      maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a ≤ 2 * Θ := by
    intro n
    have hk : Q.scale - (n : ℤ) ≤ Q.scale := by
      have : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
      linarith
    rw [LawCarrier.maxDescendantBMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae ha Q
      (Q.scale - (n : ℤ))]
    refine Ch02.finsetSupReal_le _ (descendantsAtScale_nonempty Q hk) ?_
    intro R _hR
    exact matrixNorm_upperLeft_cubeSet_le ha hΘ hmeas (ae_restrict_of_ae hae)
  have hMaxNonneg : ∀ n : ℕ,
      0 ≤ maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a := by
    intro n
    have hk : Q.scale - (n : ℤ) ≤ Q.scale := by
      have : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
      linarith
    rw [LawCarrier.maxDescendantBMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae ha Q
      (Q.scale - (n : ℤ))]
    obtain ⟨R, hR⟩ := descendantsAtScale_nonempty Q hk
    exact le_trans (Ch02.matrixNorm_nonneg (coarseBlockMatrix (cubeSet R) a).upperLeft)
      (le_finsetSupReal _
        (fun R => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a).upperLeft) hR)
  set C : ℝ := Real.rpow (2 * Θ) (1 / 2) with hC
  have hC0 : 0 ≤ C := Real.rpow_nonneg hΘ0 _
  have hterm : ∀ n : ℕ,
      Ch02.geometricWeight s 1 n *
          Real.rpow (maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2) ≤
        Ch02.geometricWeight s 1 n * C := by
    intro n
    have hw : 0 ≤ Ch02.geometricWeight s 1 n := by
      simpa [Ch02.geometricWeight_eq_old] using
        geometricWeight_nonneg (s := s) (q := 1) n (by positivity)
    have hrp : Real.rpow (maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a)
        (1 / 2) ≤ C := by
      rw [hC]
      exact Real.rpow_le_rpow (hMaxNonneg n) (hMax n) (by norm_num)
    exact mul_le_mul_of_nonneg_left hrp hw
  have hsummL :
      Summable (fun n : ℕ =>
        Ch02.geometricWeight s 1 n *
          Real.rpow (maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2)) :=
    LawCarrier.summable_weighted_maxDescendantBMatrixNormCoeffFieldAtScale Q a hs
  have hsummR : Summable (fun n : ℕ => Ch02.geometricWeight s 1 n * C) := by
    simpa [Ch02.geometricWeight_eq_old] using
      (summable_geometricWeight_one (s := s) hs).mul_right C
  have hTle :
      (∑' n : ℕ, Ch02.geometricWeight s 1 n *
        Real.rpow (maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a)
          (1 / 2)) ≤ C := by
    calc
      (∑' n : ℕ, Ch02.geometricWeight s 1 n *
          Real.rpow (maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2))
          ≤ ∑' n : ℕ, Ch02.geometricWeight s 1 n * C :=
            Summable.tsum_le_tsum hterm hsummL hsummR
      _ = (∑' n : ℕ, Ch02.geometricWeight s 1 n) * C := tsum_mul_right
      _ = C := by
            rw [show (∑' n : ℕ, Ch02.geometricWeight s 1 n) = 1 by
              simpa [Ch02.geometricWeight_eq_old] using
                tsum_geometricWeight_one_eq_one (s := s) hs]
            ring
  have hTnn :
      0 ≤ ∑' n : ℕ, Ch02.geometricWeight s 1 n *
        Real.rpow (maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a) (1 / 2) := by
    refine tsum_nonneg (fun n => ?_)
    have hw : 0 ≤ Ch02.geometricWeight s 1 n := by
      simpa [Ch02.geometricWeight_eq_old] using
        geometricWeight_nonneg (s := s) (q := 1) n (by positivity)
    exact mul_nonneg hw (Real.rpow_nonneg (hMaxNonneg n) _)
  rw [LawCarrier.LambdaSqCoeffField_finite_one_eq_tsum_sq Q a s]
  calc
    (∑' n : ℕ, Ch02.geometricWeight s 1 n *
        Real.rpow (maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a)
          (1 / 2)) ^ 2
        ≤ C ^ 2 := pow_le_pow_left₀ hTnn hTle 2
    _ = 2 * Θ := by rw [hC]; exact rpow_half_sq hΘ0

/-- **P3-lower.** Pointwise lower inverse multiscale ellipticity bound `≤ 2`. -/
theorem lambdaSqCoeffField_originCube_zero_inv_le_of_ae
    {Θ s : ℝ} {a : CoeffField d} (hΘ : 1 ≤ Θ) (hs : 0 < s)
    (hmeas : ∀ i j : Fin d, Measurable fun x : Vec d => a x i j)
    (hae : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 Θ (a x)) :
    (lambdaSqCoeffField (originCube d 0) s (.finite 1) a)⁻¹ ≤ 2 := by
  have ha : AELocallyUniformlyEllipticField a :=
    aeLocallyUniformlyEllipticField_of_ae_isEllipticMatrix hΘ hmeas hae
  set Q := originCube d 0 with hQ
  have hMax : ∀ n : ℕ,
      maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a ≤ 2 := by
    intro n
    have hk : Q.scale - (n : ℤ) ≤ Q.scale := by
      have : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
      linarith
    rw [LawCarrier.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae ha Q
      (Q.scale - (n : ℤ))]
    refine Ch02.finsetSupReal_le _ (descendantsAtScale_nonempty Q hk) ?_
    intro R _hR
    exact matrixNorm_lowerRight_cubeSet_le ha hΘ hmeas (ae_restrict_of_ae hae)
  have hMaxNonneg : ∀ n : ℕ,
      0 ≤ maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a := by
    intro n
    have hk : Q.scale - (n : ℤ) ≤ Q.scale := by
      have : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
      linarith
    rw [LawCarrier.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae ha Q
      (Q.scale - (n : ℤ))]
    obtain ⟨R, hR⟩ := descendantsAtScale_nonempty Q hk
    exact le_trans (Ch02.matrixNorm_nonneg (coarseBlockMatrix (cubeSet R) a).lowerRight)
      (le_finsetSupReal _
        (fun R => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a).lowerRight) hR)
  set C : ℝ := Real.rpow (2 : ℝ) (1 / 2) with hC
  have hC0 : 0 ≤ C := Real.rpow_nonneg (by norm_num) _
  have hterm : ∀ n : ℕ,
      Ch02.geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2) ≤
        Ch02.geometricWeight s 1 n * C := by
    intro n
    have hw : 0 ≤ Ch02.geometricWeight s 1 n := by
      simpa [Ch02.geometricWeight_eq_old] using
        geometricWeight_nonneg (s := s) (q := 1) n (by positivity)
    have hrp : Real.rpow (maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q
        (Q.scale - (n : ℤ)) a) (1 / 2) ≤ C := by
      rw [hC]
      exact Real.rpow_le_rpow (hMaxNonneg n) (hMax n) (by norm_num)
    exact mul_le_mul_of_nonneg_left hrp hw
  have hsummL :
      Summable (fun n : ℕ =>
        Ch02.geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2)) :=
    LawCarrier.summable_weighted_maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q a hs
  have hsummR : Summable (fun n : ℕ => Ch02.geometricWeight s 1 n * C) := by
    simpa [Ch02.geometricWeight_eq_old] using
      (summable_geometricWeight_one (s := s) hs).mul_right C
  have hTle :
      (∑' n : ℕ, Ch02.geometricWeight s 1 n *
        Real.rpow (maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a)
          (1 / 2)) ≤ C := by
    calc
      (∑' n : ℕ, Ch02.geometricWeight s 1 n *
          Real.rpow (maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2))
          ≤ ∑' n : ℕ, Ch02.geometricWeight s 1 n * C :=
            Summable.tsum_le_tsum hterm hsummL hsummR
      _ = (∑' n : ℕ, Ch02.geometricWeight s 1 n) * C := tsum_mul_right
      _ = C := by
            rw [show (∑' n : ℕ, Ch02.geometricWeight s 1 n) = 1 by
              simpa [Ch02.geometricWeight_eq_old] using
                tsum_geometricWeight_one_eq_one (s := s) hs]
            ring
  have hTnn :
      0 ≤ ∑' n : ℕ, Ch02.geometricWeight s 1 n *
        Real.rpow (maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a)
          (1 / 2) := by
    refine tsum_nonneg (fun n => ?_)
    have hw : 0 ≤ Ch02.geometricWeight s 1 n := by
      simpa [Ch02.geometricWeight_eq_old] using
        geometricWeight_nonneg (s := s) (q := 1) n (by positivity)
    exact mul_nonneg hw (Real.rpow_nonneg (hMaxNonneg n) _)
  rw [LawCarrier.lambdaSqCoeffField_finite_one_eq_tsum_sq_inv Q a hs, inv_inv]
  calc
    (∑' n : ℕ, Ch02.geometricWeight s 1 n *
        Real.rpow (maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a)
          (1 / 2)) ^ 2
        ≤ C ^ 2 := pow_le_pow_left₀ hTnn hTle 2
    _ = 2 := by rw [hC]; exact rpow_half_sq (by norm_num)

/-! ## Moment-root bounds -/

/-- The annealed moment root of a constant is that constant, on a probability
law (`ξ ≥ 1`, constant `≥ 0`). -/
private theorem annealedMomentRoot_const
    {P : CoeffLaw d} [IsProbabilityMeasure P] {ξ : ℕ} {c : ℝ}
    (hξ : 1 ≤ ξ) (hc : 0 ≤ c) :
    annealedMomentRoot P ξ (fun _ => c) = c := by
  have hξ0 : (ξ : ℝ) ≠ 0 := by
    have : ξ ≠ 0 := by omega
    exact_mod_cast this
  have hint : (∫ _a : CoeffField d, (fun _ => c) _a ^ ξ ∂P) = c ^ ξ := by
    simp [integral_const]
  rw [annealedMomentRoot, hint, ← Real.rpow_natCast c ξ, ← Real.rpow_mul hc,
    mul_one_div, div_self hξ0, Real.rpow_one]

/-- **P4-upper.** `LambdaMomentAtScale P 0 sUpper ξ ≤ 2 * Θ`. -/
theorem LambdaMomentAtScale_le
    {P : CoeffLaw d} {Θ sUpper : ℝ} {ξ : ℕ}
    (hΘ : 1 ≤ Θ) (hsU : 0 < sUpper) (hξ : 1 ≤ ξ)
    (hEllLaw : ThetaEllipticLaw Θ P) [IsProbabilityMeasure P]
    (hUpperInt :
      Integrable
        (fun a : CoeffField d =>
          (LambdaSqCoeffField (originCube d 0) sUpper (.finite 1) a) ^ ξ) P) :
    LambdaMomentAtScale P 0 sUpper ξ ≤ 2 * Θ := by
  have hΘ0 : (0 : ℝ) ≤ 2 * Θ := by linarith
  have hXY :
      (fun a => LambdaSqCoeffField (originCube d 0) sUpper (.finite 1) a) ≤ᵐ[P]
        fun _ => 2 * Θ := by
    filter_upwards [hEllLaw] with a ha
    exact LambdaSqCoeffField_originCube_zero_le_of_ae hΘ hsU ha.1 ha.2
  have hmono :
      annealedMomentRoot P ξ
          (fun a => LambdaSqCoeffField (originCube d 0) sUpper (.finite 1) a) ≤
        annealedMomentRoot P ξ (fun _ => 2 * Θ) :=
    annealedMomentRoot_le_of_ae_nonneg_le hξ
      (fun a => LambdaSqCoeffField_finite_nonneg (originCube d 0) a hsU (by norm_num))
      hUpperInt (integrable_const _) hXY
  rw [LambdaMomentAtScale]
  exact hmono.trans (le_of_eq (annealedMomentRoot_const hξ hΘ0))

/-- **P4-lower.** `lambdaInvMomentAtScale P 0 sLower ξ ≤ 2`. -/
theorem lambdaInvMomentAtScale_le
    {P : CoeffLaw d} {Θ sLower : ℝ} {ξ : ℕ}
    (hΘ : 1 ≤ Θ) (hsL : 0 < sLower) (hξ : 1 ≤ ξ)
    (hEllLaw : ThetaEllipticLaw Θ P) [IsProbabilityMeasure P]
    (hLowerInt :
      Integrable
        (fun a : CoeffField d =>
          ((lambdaSqCoeffField (originCube d 0) sLower (.finite 1) a)⁻¹) ^ ξ) P) :
    lambdaInvMomentAtScale P 0 sLower ξ ≤ 2 := by
  have hXY :
      (fun a => (lambdaSqCoeffField (originCube d 0) sLower (.finite 1) a)⁻¹) ≤ᵐ[P]
        fun _ => (2 : ℝ) := by
    filter_upwards [hEllLaw] with a ha
    exact lambdaSqCoeffField_originCube_zero_inv_le_of_ae hΘ hsL ha.1 ha.2
  have hmono :
      annealedMomentRoot P ξ
          (fun a => (lambdaSqCoeffField (originCube d 0) sLower (.finite 1) a)⁻¹) ≤
        annealedMomentRoot P ξ (fun _ => (2 : ℝ)) :=
    annealedMomentRoot_le_of_ae_nonneg_le hξ
      (fun a => inv_nonneg.mpr
        (lambdaSqCoeffField_finite_nonneg (originCube d 0) a hsL (by norm_num)))
      hLowerInt (integrable_const _) hXY
  rw [lambdaInvMomentAtScale]
  exact hmono.trans (le_of_eq (annealedMomentRoot_const hξ (by norm_num)))

/-! ## `1 ≤ Θ` from the law -/

/-- On a probability law, `ThetaEllipticLaw Θ P` forces `1 ≤ Θ`. -/
theorem one_le_Theta_of_thetaEllipticLaw
    {P : CoeffLaw d} {Θ : ℝ} [IsProbabilityMeasure P]
    (hEllLaw : ThetaEllipticLaw Θ P) :
    1 ≤ Θ := by
  obtain ⟨a, _hmeas, hae⟩ := hEllLaw.exists
  obtain ⟨x, hx⟩ := hae.exists
  exact hx.2.1

/-! ## Final target -/

/-- **Main.** Uniform ellipticity controls the moment-enhanced contrast:
`widetildeThetaAtScale P 0 sUpper sLower ξ ≤ 4 * Θ`.  Constants `C = 4`, `k = 1`. -/
theorem widetildeThetaAtScale_le
    {P : CoeffLaw d} {Θ sUpper sLower : ℝ} {ξ : ℕ}
    (hsU : 0 < sUpper) (hsL : 0 < sLower) (hξ : 1 ≤ ξ)
    (hEllLaw : ThetaEllipticLaw Θ P) [IsProbabilityMeasure P]
    (hUpperInt :
      Integrable
        (fun a : CoeffField d =>
          (LambdaSqCoeffField (originCube d 0) sUpper (.finite 1) a) ^ ξ) P)
    (hLowerInt :
      Integrable
        (fun a : CoeffField d =>
          ((lambdaSqCoeffField (originCube d 0) sLower (.finite 1) a)⁻¹) ^ ξ) P) :
    widetildeThetaAtScale P 0 sUpper sLower ξ ≤ 4 * Θ := by
  have hΘ : 1 ≤ Θ := one_le_Theta_of_thetaEllipticLaw hEllLaw
  have hΘ0 : (0 : ℝ) ≤ 2 * Θ := by linarith
  have hUpper : LambdaMomentAtScale P 0 sUpper ξ ≤ 2 * Θ :=
    LambdaMomentAtScale_le hΘ hsU hξ hEllLaw hUpperInt
  have hLower : lambdaInvMomentAtScale P 0 sLower ξ ≤ 2 :=
    lambdaInvMomentAtScale_le hΘ hsL hξ hEllLaw hLowerInt
  have hUpper0 : 0 ≤ LambdaMomentAtScale P 0 sUpper ξ :=
    LambdaMomentAtScale_nonneg P 0 ξ hsU
  have hLower0 : 0 ≤ lambdaInvMomentAtScale P 0 sLower ξ :=
    lambdaInvMomentAtScale_nonneg P 0 ξ hsL
  rw [widetildeThetaAtScale]
  calc
    LambdaMomentAtScale P 0 sUpper ξ * lambdaInvMomentAtScale P 0 sLower ξ
        ≤ (2 * Θ) * 2 := mul_le_mul hUpper hLower hLower0 hΘ0
    _ = 4 * Θ := by ring

/-- **Record form.** For any `QuantitativeCoarseGrainedEllipticity P`
record, the moment-enhanced contrast at its parameters is `≤ 4 * Θ`.  The
record's `dim_div_xi_lt_min` field (with `two_le_dim`, `xi_gt_two_mul_dim`)
forces `sUpper, sLower` strictly positive, and its integrability fields supply
the moment hypotheses. -/
theorem widetildeThetaAtScale_le_of_quantitativeCoarseGrainedEllipticity
    {P : CoeffLaw d} {Θ : ℝ}
    (hEllLaw : ThetaEllipticLaw Θ P) [IsProbabilityMeasure P]
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) :
    widetildeThetaAtScale P 0 hP4.sUpper hP4.sLower hP4.xi ≤ 4 * Θ := by
  have hdN : (0 : ℕ) < d := by have := hP4.two_le_dim; omega
  have hd : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdN
  have hξR : (0 : ℝ) < (hP4.xi : ℝ) := by exact_mod_cast hP4.xi_pos
  have hdxi : (0 : ℝ) < (d : ℝ) / (hP4.xi : ℝ) := div_pos hd hξR
  have hsU : 0 < hP4.sUpper :=
    lt_trans hdxi (lt_of_lt_of_le hP4.dim_div_xi_lt_min (min_le_left _ _))
  have hsL : 0 < hP4.sLower :=
    lt_trans hdxi (lt_of_lt_of_le hP4.dim_div_xi_lt_min (min_le_right _ _))
  exact widetildeThetaAtScale_le hsU hsL hP4.xi_pos hEllLaw
    hP4.upper_moment_integrable hP4.lower_inv_moment_integrable

end

end Homogenization
