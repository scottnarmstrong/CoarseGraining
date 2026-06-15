import Homogenization.Book.Ch04.Theorems.ScalarizationDefinitions
import Homogenization.Book.Ch04.Theorems.CoarseObservables
import Homogenization.CoarseGraining.AdjointSymmetry.BasicAdjoint
import Homogenization.CoarseGraining.OriginCubeOpenBridge

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Scalarization from isotropy

This file turns the structural symmetries of the law into the primitive
scalarization data used by the scalarized Chapter 4 moment surface.
-/

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

private theorem swap_mul_mul_swap_apply {d : ℕ} (i j r c : Fin d) (A : Mat d) :
    (Matrix.swap ℝ i j * A * Matrix.swap ℝ i j) r c =
      A (Equiv.swap i j r) (Equiv.swap i j c) := by
  by_cases hr_i : r = i
  · subst r
    by_cases hc_i : c = i
    · subst c
      simp
    · by_cases hc_j : c = j
      · subst c
        simp
      · simp [Matrix.mul_swap_of_ne hc_i hc_j, Equiv.swap_apply_of_ne_of_ne hc_i hc_j]
  · by_cases hr_j : r = j
    · subst r
      by_cases hc_i : c = i
      · subst c
        simp
      · by_cases hc_j : c = j
        · subst c
          simp
        · simp [Matrix.mul_swap_of_ne hc_i hc_j, Equiv.swap_apply_of_ne_of_ne hc_i hc_j]
    · by_cases hc_i : c = i
      · subst c
        simp [Matrix.swap_mul_of_ne hr_i hr_j, Equiv.swap_apply_of_ne_of_ne hr_i hr_j]
      · by_cases hc_j : c = j
        · subst c
          simp [Matrix.swap_mul_of_ne hr_i hr_j, Equiv.swap_apply_of_ne_of_ne hr_i hr_j]
        · simp [Matrix.swap_mul_of_ne hr_i hr_j, Matrix.mul_swap_of_ne hc_i hc_j,
            Equiv.swap_apply_of_ne_of_ne hr_i hr_j, Equiv.swap_apply_of_ne_of_ne hc_i hc_j]

private theorem coarseBlockMatrix_lowerRight_signFlip_cubeSet_originCube_of_exists
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix (openCubeSet (originCube d n)) a Abar)
    (i : Fin d) :
    (coarseBlockMatrix (cubeSet (originCube d n))
        (rotateCoeffField (signFlipMatrix i) a)).lowerRight =
      signFlipMatrix i *
        (coarseBlockMatrix (cubeSet (originCube d n)) a).lowerRight *
          signFlipMatrix i := by
  rw [coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet,
    coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
  exact coarseBlockMatrix_lowerRight_signFlip_openCubeSet_originCube_of_exists
    (n := n) (a := a) hex i

private theorem coarseBlockMatrix_lowerRight_swap_cubeSet_originCube_of_exists
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix (openCubeSet (originCube d n)) a Abar)
    (i j : Fin d) :
    (coarseBlockMatrix (cubeSet (originCube d n))
        (rotateCoeffField (Matrix.swap ℝ i j) a)).lowerRight =
      Matrix.swap ℝ i j *
        (coarseBlockMatrix (cubeSet (originCube d n)) a).lowerRight *
          Matrix.swap ℝ i j := by
  rw [coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet,
    coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
  exact coarseBlockMatrix_lowerRight_swap_openCubeSet_originCube_of_exists
    (n := n) (a := a) hex i j

private theorem coarseBlockMatrix_upperLeft_signFlip_cubeSet_originCube_of_exists
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix (openCubeSet (originCube d n)) a Abar)
    (i : Fin d) :
    (coarseBlockMatrix (cubeSet (originCube d n))
        (rotateCoeffField (signFlipMatrix i) a)).upperLeft =
      signFlipMatrix i *
        (coarseBlockMatrix (cubeSet (originCube d n)) a).upperLeft *
          signFlipMatrix i := by
  rw [coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet,
    coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
  exact coarseBlockMatrix_upperLeft_signFlip_openCubeSet_originCube_of_exists
    (n := n) (a := a) hex i

private theorem coarseBlockMatrix_upperLeft_swap_cubeSet_originCube_of_exists
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix (openCubeSet (originCube d n)) a Abar)
    (i j : Fin d) :
    (coarseBlockMatrix (cubeSet (originCube d n))
        (rotateCoeffField (Matrix.swap ℝ i j) a)).upperLeft =
      Matrix.swap ℝ i j *
        (coarseBlockMatrix (cubeSet (originCube d n)) a).upperLeft *
          Matrix.swap ℝ i j := by
  rw [coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet,
    coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
  exact coarseBlockMatrix_upperLeft_swap_openCubeSet_originCube_of_exists
    (n := n) (a := a) hex i j

private theorem coarseBlockMatrix_neg_lowerLeft_adjoint_cubeSet_originCube_of_exists
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix (openCubeSet (originCube d n)) a Abar) :
    -((coarseBlockMatrix (cubeSet (originCube d n))
        (adjointCoeffField a)).lowerLeft) =
      -(-((coarseBlockMatrix (cubeSet (originCube d n)) a).lowerLeft)) := by
  rw [coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet,
    coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
  exact congrArg Neg.neg
    (coarseBlockMatrix_lowerLeft_adjointCoeffField_of_exists
      (U := openCubeSet (originCube d n)) (a := a) hex)

private theorem annealedSigmaStarInvAtScale_isSignFlipInvariant_of_covariant_ae
    {d : ℕ} [NeZero d] (P : CoeffLaw d) (n : ℤ)
    (hIso : IsotropicLaw P)
    (hmeas : ∀ r c : Fin d,
      AEStronglyMeasurable
        (fun a => (coarseBlockMatrix (cubeSet (originCube d n)) a).lowerRight r c) P)
    (hcov : ∀ i : Fin d, ∀ᵐ a ∂P,
      (coarseBlockMatrix (cubeSet (originCube d n))
          (rotateCoeffField (signFlipMatrix i) a)).lowerRight =
        signFlipMatrix i *
          (coarseBlockMatrix (cubeSet (originCube d n)) a).lowerRight *
            signFlipMatrix i) :
    IsSignFlipInvariant (annealedSigmaStarInvAtScale P n) := by
  intro i
  ext r c
  let U := cubeSet (originCube d n)
  let s : ℝ := (if r = i then (-1 : ℝ) else 1) * (if c = i then (-1 : ℝ) else 1)
  calc
    (signFlipMatrix i * annealedSigmaStarInvAtScale P n * signFlipMatrix i) r c
        = s * ∫ a, (coarseBlockMatrix U a).lowerRight r c ∂P := by
          simp [annealedSigmaStarInvAtScale, annealedSigmaStarInv, annealedBlockMatrix,
            U, s, signFlipMatrix_mul_mul_signFlipMatrix_apply]
    _ = ∫ a, s * (coarseBlockMatrix U a).lowerRight r c ∂P := by
          symm
          simpa [s] using
            (MeasureTheory.integral_const_mul s
              (fun a => (coarseBlockMatrix U a).lowerRight r c))
    _ = ∫ a, (coarseBlockMatrix U (rotateCoeffField (signFlipMatrix i) a)).lowerRight r c
          ∂P := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hcov i] with a ha
          have hentry := congrArg (fun M => M r c) ha
          simpa [U, s, signFlipMatrix_mul_mul_signFlipMatrix_apply] using hentry.symm
    _ = ∫ a, (coarseBlockMatrix U a).lowerRight r c ∂P := by
          simpa [U] using
            integral_comp_rotateCoeffField_eq_of_isIsotropicInLaw (hP := hIso)
              (hR := isSignedPermutationMatrix_signFlipMatrix i)
              (f := fun a => (coarseBlockMatrix U a).lowerRight r c) (hf := hmeas r c)
    _ = annealedSigmaStarInvAtScale P n r c := by
          rfl

private theorem annealedSigmaStarInvAtScale_isSwapInvariant_of_covariant_ae
    {d : ℕ} [NeZero d] (P : CoeffLaw d) (n : ℤ)
    (hIso : IsotropicLaw P)
    (hmeas : ∀ r c : Fin d,
      AEStronglyMeasurable
        (fun a => (coarseBlockMatrix (cubeSet (originCube d n)) a).lowerRight r c) P)
    (hcov : ∀ i j : Fin d, ∀ᵐ a ∂P,
      (coarseBlockMatrix (cubeSet (originCube d n))
          (rotateCoeffField (Matrix.swap ℝ i j) a)).lowerRight =
        Matrix.swap ℝ i j *
          (coarseBlockMatrix (cubeSet (originCube d n)) a).lowerRight *
            Matrix.swap ℝ i j) :
    IsSwapInvariant (annealedSigmaStarInvAtScale P n) := by
  intro i j
  ext r c
  let U := cubeSet (originCube d n)
  calc
    (Matrix.swap ℝ i j * annealedSigmaStarInvAtScale P n * Matrix.swap ℝ i j) r c
        = ∫ a, (Matrix.swap ℝ i j *
            (coarseBlockMatrix U a).lowerRight * Matrix.swap ℝ i j) r c ∂P := by
          simp [annealedSigmaStarInvAtScale, annealedSigmaStarInv, annealedBlockMatrix,
            U, swap_mul_mul_swap_apply]
    _ = ∫ a, (coarseBlockMatrix U a).lowerRight
          (Equiv.swap i j r) (Equiv.swap i j c) ∂P := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with a
          simp [swap_mul_mul_swap_apply]
    _ = ∫ a, (coarseBlockMatrix U (rotateCoeffField (Matrix.swap ℝ i j) a)).lowerRight r c
          ∂P := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hcov i j] with a ha
          have hentry := congrArg (fun M => M r c) ha
          simpa [U, swap_mul_mul_swap_apply] using hentry.symm
    _ = ∫ a, (coarseBlockMatrix U a).lowerRight r c ∂P := by
          simpa [U] using
            integral_comp_rotateCoeffField_eq_of_isIsotropicInLaw (hP := hIso)
              (hR := isSignedPermutationMatrix_swap i j)
              (f := fun a => (coarseBlockMatrix U a).lowerRight r c) (hf := hmeas r c)
    _ = annealedSigmaStarInvAtScale P n r c := by
          rfl

private theorem annealedBAtScale_isSignFlipInvariant_of_covariant_ae
    {d : ℕ} [NeZero d] (P : CoeffLaw d) (n : ℤ)
    (hIso : IsotropicLaw P)
    (hmeas : ∀ r c : Fin d,
      AEStronglyMeasurable
        (fun a => (coarseBlockMatrix (cubeSet (originCube d n)) a).upperLeft r c) P)
    (hcov : ∀ i : Fin d, ∀ᵐ a ∂P,
      (coarseBlockMatrix (cubeSet (originCube d n))
          (rotateCoeffField (signFlipMatrix i) a)).upperLeft =
        signFlipMatrix i *
          (coarseBlockMatrix (cubeSet (originCube d n)) a).upperLeft *
            signFlipMatrix i) :
    IsSignFlipInvariant (annealedBAtScale P n) := by
  intro i
  ext r c
  let U := cubeSet (originCube d n)
  let s : ℝ := (if r = i then (-1 : ℝ) else 1) * (if c = i then (-1 : ℝ) else 1)
  calc
    (signFlipMatrix i * annealedBAtScale P n * signFlipMatrix i) r c
        = s * ∫ a, (coarseBlockMatrix U a).upperLeft r c ∂P := by
          simp [annealedBAtScale, annealedB, annealedBlockMatrix, U, s,
            signFlipMatrix_mul_mul_signFlipMatrix_apply]
    _ = ∫ a, s * (coarseBlockMatrix U a).upperLeft r c ∂P := by
          symm
          simpa [s] using
            (MeasureTheory.integral_const_mul s
              (fun a => (coarseBlockMatrix U a).upperLeft r c))
    _ = ∫ a, (coarseBlockMatrix U (rotateCoeffField (signFlipMatrix i) a)).upperLeft r c
          ∂P := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hcov i] with a ha
          have hentry := congrArg (fun M => M r c) ha
          simpa [U, s, signFlipMatrix_mul_mul_signFlipMatrix_apply] using hentry.symm
    _ = ∫ a, (coarseBlockMatrix U a).upperLeft r c ∂P := by
          simpa [U] using
            integral_comp_rotateCoeffField_eq_of_isIsotropicInLaw (hP := hIso)
              (hR := isSignedPermutationMatrix_signFlipMatrix i)
              (f := fun a => (coarseBlockMatrix U a).upperLeft r c) (hf := hmeas r c)
    _ = annealedBAtScale P n r c := by
          rfl

private theorem annealedBAtScale_isSwapInvariant_of_covariant_ae
    {d : ℕ} [NeZero d] (P : CoeffLaw d) (n : ℤ)
    (hIso : IsotropicLaw P)
    (hmeas : ∀ r c : Fin d,
      AEStronglyMeasurable
        (fun a => (coarseBlockMatrix (cubeSet (originCube d n)) a).upperLeft r c) P)
    (hcov : ∀ i j : Fin d, ∀ᵐ a ∂P,
      (coarseBlockMatrix (cubeSet (originCube d n))
          (rotateCoeffField (Matrix.swap ℝ i j) a)).upperLeft =
        Matrix.swap ℝ i j *
          (coarseBlockMatrix (cubeSet (originCube d n)) a).upperLeft *
            Matrix.swap ℝ i j) :
    IsSwapInvariant (annealedBAtScale P n) := by
  intro i j
  ext r c
  let U := cubeSet (originCube d n)
  calc
    (Matrix.swap ℝ i j * annealedBAtScale P n * Matrix.swap ℝ i j) r c
        = ∫ a, (Matrix.swap ℝ i j *
            (coarseBlockMatrix U a).upperLeft * Matrix.swap ℝ i j) r c ∂P := by
          simp [annealedBAtScale, annealedB, annealedBlockMatrix, U, swap_mul_mul_swap_apply]
    _ = ∫ a, (coarseBlockMatrix U a).upperLeft
          (Equiv.swap i j r) (Equiv.swap i j c) ∂P := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with a
          simp [swap_mul_mul_swap_apply]
    _ = ∫ a, (coarseBlockMatrix U (rotateCoeffField (Matrix.swap ℝ i j) a)).upperLeft r c
          ∂P := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hcov i j] with a ha
          have hentry := congrArg (fun M => M r c) ha
          simpa [U, swap_mul_mul_swap_apply] using hentry.symm
    _ = ∫ a, (coarseBlockMatrix U a).upperLeft r c ∂P := by
          simpa [U] using
            integral_comp_rotateCoeffField_eq_of_isIsotropicInLaw (hP := hIso)
              (hR := isSignedPermutationMatrix_swap i j)
              (f := fun a => (coarseBlockMatrix U a).upperLeft r c) (hf := hmeas r c)
    _ = annealedBAtScale P n r c := by
          rfl

private theorem annealedSigmaStarInvKappaMeanAtScale_eq_zero_of_adjoint_covariant_ae
    {d : ℕ} [NeZero d] (P : CoeffLaw d) (n : ℤ)
    (hAdj : AdjointInvariantLaw P)
    (hmeas : ∀ r c : Fin d,
      AEStronglyMeasurable
        (fun a => -((coarseBlockMatrix (cubeSet (originCube d n)) a).lowerLeft r c)) P)
    (hcov : ∀ᵐ a ∂P,
      -((coarseBlockMatrix (cubeSet (originCube d n))
          (adjointCoeffField a)).lowerLeft) =
        -(-((coarseBlockMatrix (cubeSet (originCube d n)) a).lowerLeft))) :
    annealedSigmaStarInvKappaMeanAtScale P n = 0 := by
  ext r c
  change annealedSigmaStarInvKappaMeanAtScale P n r c = 0
  let U := cubeSet (originCube d n)
  have hcomp :=
    integral_comp_adjointCoeffField_eq_of_isAdjointInvariantInLaw (hP := hAdj)
      (f := fun a => -((coarseBlockMatrix U a).lowerLeft r c)) (hf := hmeas r c)
  have hEq :
      annealedSigmaStarInvKappaMeanAtScale P n r c =
        -annealedSigmaStarInvKappaMeanAtScale P n r c := by
    calc
      annealedSigmaStarInvKappaMeanAtScale P n r c
          = -(∫ a, (coarseBlockMatrix U a).lowerLeft r c ∂P) := by
            simp [annealedSigmaStarInvKappaMeanAtScale, annealedSigmaStarInvKappaMean,
              annealedBlockMatrix, U]
      _ = ∫ a, -((coarseBlockMatrix U a).lowerLeft r c) ∂P := by
            simpa using
              (MeasureTheory.integral_neg
                (f := fun a => (coarseBlockMatrix U a).lowerLeft r c)).symm
      _ = ∫ a, -((coarseBlockMatrix U (adjointCoeffField a)).lowerLeft r c) ∂P := by
            symm
            simpa [U] using hcomp
      _ = ∫ a, (coarseBlockMatrix U a).lowerLeft r c ∂P := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [hcov] with a ha
            have hentry := congrArg (fun M => M r c) ha
            simpa [U] using hentry
      _ = -annealedSigmaStarInvKappaMeanAtScale P n r c := by
            simp [annealedSigmaStarInvKappaMeanAtScale, annealedSigmaStarInvKappaMean,
              annealedBlockMatrix, U]
  linarith

/--
Isotropy and adjoint invariance scalarize the primitive annealed blocks at a
fixed scale.  The a.s. deterministic coarse-block existence needed by the
covariance identities is supplied by `LawCarrier`.
-/
noncomputable def Internal.annealedPrimitiveScalarizationData_of_isotropic_adjoint
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hIso : IsotropicLaw P) (hAdj : AdjointInvariantLaw P) (n : ℤ) :
    Internal.AnnealedPrimitiveScalarizationData (d := d) P n :=
  let hex := hP.ae_exists_coarseBlockMatrix_openCubeSet_originCube n
  {
  sigmaStarInvFlip :=
    annealedSigmaStarInvAtScale_isSignFlipInvariant_of_covariant_ae P n hIso
      (fun r c =>
        (hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet
          (originCube d n) r c).aestronglyMeasurable)
      (fun i => by
        filter_upwards [hex] with a ha
        exact coarseBlockMatrix_lowerRight_signFlip_cubeSet_originCube_of_exists
          (n := n) (a := a) ha i)
  sigmaStarInvSwap :=
    annealedSigmaStarInvAtScale_isSwapInvariant_of_covariant_ae P n hIso
      (fun r c =>
        (hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet
          (originCube d n) r c).aestronglyMeasurable)
      (fun i j => by
        filter_upwards [hex] with a ha
        exact coarseBlockMatrix_lowerRight_swap_cubeSet_originCube_of_exists
          (n := n) (a := a) ha i j)
  bFlip :=
    annealedBAtScale_isSignFlipInvariant_of_covariant_ae P n hIso
      (fun r c =>
        (hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet
          (originCube d n) r c).aestronglyMeasurable)
      (fun i => by
        filter_upwards [hex] with a ha
        exact coarseBlockMatrix_upperLeft_signFlip_cubeSet_originCube_of_exists
          (n := n) (a := a) ha i)
  bSwap :=
    annealedBAtScale_isSwapInvariant_of_covariant_ae P n hIso
      (fun r c =>
        (hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet
          (originCube d n) r c).aestronglyMeasurable)
      (fun i j => by
        filter_upwards [hex] with a ha
        exact coarseBlockMatrix_upperLeft_swap_cubeSet_originCube_of_exists
          (n := n) (a := a) ha i j)
  sigmaStarInvKappaMean_eq_zero :=
    annealedSigmaStarInvKappaMeanAtScale_eq_zero_of_adjoint_covariant_ae P n hAdj
      (fun r c =>
        ((hP.aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet
          (originCube d n) r c).neg).aestronglyMeasurable)
      (by
        filter_upwards [hex] with a ha
        exact coarseBlockMatrix_neg_lowerLeft_adjoint_cubeSet_originCube_of_exists
          (n := n) (a := a) ha) }

/-- Structural-law version of
`Internal.annealedPrimitiveScalarizationData_of_isotropic_adjoint`. -/
noncomputable def Internal.annealedPrimitiveScalarizationData_of_structuralLaw
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hStruct : StructuralLaw P) (n : ℤ) :
    Internal.AnnealedPrimitiveScalarizationData (d := d) P n :=
  Internal.annealedPrimitiveScalarizationData_of_isotropic_adjoint hP
    hStruct.isotropic hStruct.adjoint_invariant n

/-- Isotropy and adjoint invariance give scalarization at a fixed scale. -/
theorem Internal.hasAnnealedScalarizationAtScale_of_isotropic_adjoint
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hIso : IsotropicLaw P) (hAdj : AdjointInvariantLaw P) (n : ℤ) :
    Internal.HasAnnealedScalarizationAtScale P n :=
  Internal.AnnealedScalarizationPrimitiveData.hasAnnealedScalarizationAtScale
    (Internal.annealedPrimitiveScalarizationData_of_isotropic_adjoint hP hIso hAdj n)

/-- Structural-law version of scalarization at a fixed scale. -/
theorem Internal.hasAnnealedScalarizationAtScale_of_structuralLaw
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hStruct : StructuralLaw P) (n : ℤ) :
    Internal.HasAnnealedScalarizationAtScale P n :=
  Internal.AnnealedScalarizationPrimitiveData.hasAnnealedScalarizationAtScale
    (Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct n)

/-- Isotropy and adjoint invariance give scalarization at every scale. -/
theorem Internal.annealedScalarizationTheory_of_isotropic_adjoint
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hIso : IsotropicLaw P) (hAdj : AdjointInvariantLaw P) :
    Internal.AnnealedScalarizationTheory P where
  scalarized n :=
    Internal.hasAnnealedScalarizationAtScale_of_isotropic_adjoint hP hIso hAdj n

/-- Structural-law version of scalarization at every scale. -/
theorem Internal.annealedScalarizationTheory_of_structuralLaw
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hStruct : StructuralLaw P) :
    Internal.AnnealedScalarizationTheory P :=
  Internal.annealedScalarizationTheory_of_isotropic_adjoint hP
    hStruct.isotropic hStruct.adjoint_invariant

/-- Structural-law scalar `\bar\sigma_n`. -/
noncomputable def LawCarrier.barSigmaAtScale
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hStruct : StructuralLaw P) (n : ℤ) : ℝ :=
  (Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct).barSigma n

/-- Structural-law scalar `\bar\sigma_{*,n}`. -/
noncomputable def LawCarrier.barSigmaStarAtScale
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hStruct : StructuralLaw P) (n : ℤ) : ℝ :=
  (Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct).barSigmaStar n

/-- Structural-law scalar upper-left coefficient `\bar b_n`. -/
noncomputable def LawCarrier.barBAtScale
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hStruct : StructuralLaw P) (n : ℤ) : ℝ :=
  (Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct n).barB

/-- Structural-law scalar inverse-star coefficient `\bar\sigma_{*,n}^{-1}`. -/
noncomputable def LawCarrier.barSigmaStarInvAtScale
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hStruct : StructuralLaw P) (n : ℤ) : ℝ :=
  (Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct n).barSigmaStarInv

/-- Structural-law contrast `\Theta_n = \bar\sigma_n \bar\sigma_{*,n}^{-1}`. -/
noncomputable def LawCarrier.thetaAtScale
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hStruct : StructuralLaw P) (n : ℤ) : ℝ :=
  hP.barSigmaAtScale hStruct n * (hP.barSigmaStarAtScale hStruct n)⁻¹

/-- The structural-law scalar `\bar\sigma_n` scalarizes the annealed matrix. -/
theorem LawCarrier.annealedSigmaAtScale_eq_barSigmaAtScale
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hStruct : StructuralLaw P) (n : ℤ) :
    annealedSigmaAtScale P n = hP.barSigmaAtScale hStruct n • (1 : Mat d) := by
  simpa [LawCarrier.barSigmaAtScale] using
    (Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct).annealedSigma_eq n

/-- The structural-law scalar `\bar\sigma_{*,n}` scalarizes the annealed
starred matrix. -/
theorem LawCarrier.annealedSigmaStarAtScale_eq_barSigmaStarAtScale
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hStruct : StructuralLaw P) (n : ℤ) :
    annealedSigmaStarAtScale P n =
      hP.barSigmaStarAtScale hStruct n • (1 : Mat d) := by
  simpa [LawCarrier.barSigmaStarAtScale] using
    (Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct).annealedSigmaStar_eq n

/-- The structural-law scalar `\bar b_n` scalarizes the annealed upper-left
block. -/
theorem LawCarrier.annealedBAtScale_eq_barBAtScale
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hStruct : StructuralLaw P) (n : ℤ) :
    annealedBAtScale P n = hP.barBAtScale hStruct n • (1 : Mat d) := by
  simpa [LawCarrier.barBAtScale] using
    (Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct n).b_eq

/-- The structural-law scalar `\bar\sigma_{*,n}^{-1}` scalarizes the annealed
inverse-star matrix. -/
theorem LawCarrier.annealedSigmaStarInvAtScale_eq_barSigmaStarInvAtScale
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hStruct : StructuralLaw P) (n : ℤ) :
    annealedSigmaStarInvAtScale P n =
      hP.barSigmaStarInvAtScale hStruct n • (1 : Mat d) := by
  simpa [LawCarrier.barSigmaStarInvAtScale] using
    (Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct n).sigmaStarInv_eq

/-- Under the structural law, the scalarized conductivity agrees with the
primitive upper-left scalar. -/
theorem LawCarrier.barSigmaAtScale_eq_barBAtScale
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hStruct : StructuralLaw P) (n : ℤ) :
    hP.barSigmaAtScale hStruct n = hP.barBAtScale hStruct n := by
  simpa [LawCarrier.barSigmaAtScale, LawCarrier.barBAtScale] using
    Internal.AnnealedPrimitiveScalarizationData.barSigma_eq_barB
      (Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct)
      (Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct n)

/-- Under the structural law, `\bar\sigma_{*,n}` is the inverse of the primitive
inverse-star scalar. -/
theorem LawCarrier.barSigmaStarAtScale_eq_inv_barSigmaStarInvAtScale
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hStruct : StructuralLaw P) (n : ℤ) :
    hP.barSigmaStarAtScale hStruct n =
      (hP.barSigmaStarInvAtScale hStruct n)⁻¹ := by
  simpa [LawCarrier.barSigmaStarAtScale, LawCarrier.barSigmaStarInvAtScale] using
    Internal.AnnealedPrimitiveScalarizationData.barSigmaStar_eq_inv_barSigmaStarInv
      (Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct)
      (Internal.annealedPrimitiveScalarizationData_of_structuralLaw hP hStruct n)

/-- Under the structural law, the annealed coupling matrix vanishes. -/
theorem LawCarrier.annealedKappaAtScale_eq_zero
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hStruct : StructuralLaw P) (n : ℤ) :
    annealedKappaAtScale P n = 0 := by
  simpa using
    (Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct).annealedKappa_eq_zero n

/-- Internal compatibility between the structural-law contrast and the
scalarization route contrast. -/
theorem Internal.thetaAtScale_eq_scalarization_contrast
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hStruct : StructuralLaw P) (n : ℤ) :
    hP.thetaAtScale hStruct n =
      (Internal.annealedScalarizationTheory_of_structuralLaw hP hStruct).contrast n := by
  rfl

end

end Ch04
end Book
end Homogenization
