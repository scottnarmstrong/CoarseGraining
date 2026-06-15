import Homogenization.Book.Ch02.Theorems.DeterministicIdentities
import Homogenization.Book.Ch04.CoeffFamily
import Homogenization.Book.Ch04.Theorems.Mu
import Homogenization.Book.Ch04.Internal.CoarseObservableMeasurability.Basic

namespace Homogenization
namespace Book
namespace Ch04

open MeasureTheory

/-!
# Coarse-observable measurability from `Mu`

This file is the public Chapter 4 handoff for the finite algebraic
consequences of `LawCarrier.aemeasurable_Mu_cubeSet`.

The surface is deliberately law-facing and definition-facing: downstream code
gets measurability of `Mu`, the coarse block matrices, and response/block
quantities through manuscript identities.  There are no provider structures and
no section-local wrapper tracks here.
-/

/-- Finite descendant averages preserve a.e.-measurability. -/
theorem aemeasurable_descendantsAverage
    {d : ℕ} {P : CoeffLaw d} {Q : TriadicCube d} {j : ℕ}
    {F : TriadicCube d → CoeffField d → ℝ}
    (hF : ∀ R, R ∈ descendantsAtDepth Q j → AEMeasurable (F R) P) :
    AEMeasurable
      (fun a : CoeffField d => descendantsAverage Q j (fun R => F R a)) P := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hsum : AEMeasurable (fun a : CoeffField d => D.sum (fun R => F R a)) P := by
    simpa using
      (D.aemeasurable_fun_sum (μ := P) (f := fun R => F R)
        (fun R hR => hF R (by simpa [D] using hR)))
  simpa [descendantsAverage, D] using hsum.const_mul ((D.card : ℝ)⁻¹)

namespace LawCarrier

/-- A locally a.e.-elliptic field has a deterministic coarse block matrix on
each triadic open cube, with the a.e. coefficient representative handled by the
Chapter 2 doubled-`Mu` theory. -/
theorem exists_coarseBlockMatrix_openCubeSet_of_aelocallyUniformlyEllipticField
    {d : ℕ} {a : CoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (Q : TriadicCube d) :
    ∃ Abar : BlockMat d, IsCoarseBlockMatrix (openCubeSet Q) a Abar := by
  let U : Ch02.Domain d := Ch02.cubeDomain Q
  let aQ : Ch02.CoeffOn U := coeffOnOfAEEllipticOn a Q (ha Q)
  refine ⟨Ch02.coarseBlockMatrix U aQ, ?_⟩
  refine ⟨Ch02.isSymmetricBlockMat_coarseBlockMatrix U aQ, ?_⟩
  intro P
  calc
    Mu (openCubeSet Q) P a
        = Mu (U : Set (Vec d)) P aQ.toCoeffField := by
            simp [U, aQ, Ch02.cubeDomain_coe]
    _ = Ch02.doubledMu U aQ P := by
          exact (Homogenization.Internal.Ch02.BookCh02.book_doubledMu_eq_Mu U aQ P).symm
    _ =
        (1 / 2 : ℝ) * blockVecDot P
          (blockMatVecMul (Ch02.coarseBlockMatrix U aQ) P) :=
          (Ch02.doubledMuTheory U aQ).doubledMu_eq_coarseBlockMatrix P

/-- The public cube-set coarse block matrix agrees with the Chapter 2
coarse block matrix built from the canonical a.e.-elliptic coefficient
representative on the cube. -/
theorem coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
    {d : ℕ} [NeZero d] {a : CoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (Q : TriadicCube d) :
    coarseBlockMatrix (cubeSet Q) a =
      Ch02.coarseBlockMatrix (Ch02.cubeDomain Q)
        ((triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) := by
  let U : Ch02.Domain d := Ch02.cubeDomain Q
  let aQ : Ch02.CoeffOn U :=
    (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q
  have hIso :
      IsCoarseBlockMatrix (openCubeSet Q) a
        (Ch02.coarseBlockMatrix U aQ) := by
    refine ⟨Ch02.isSymmetricBlockMat_coarseBlockMatrix U aQ, ?_⟩
    intro P
    calc
      Mu (openCubeSet Q) P a
          = Mu (U : Set (Vec d)) P aQ.toCoeffField := by
              simp [U, aQ, Ch02.cubeDomain_coe,
                triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
                coeffOnOfAEEllipticOn_toCoeffField]
      _ = Ch02.doubledMu U aQ P := by
            exact (Homogenization.Internal.Ch02.BookCh02.book_doubledMu_eq_Mu U aQ P).symm
      _ =
          (1 / 2 : ℝ) * blockVecDot P
            (blockMatVecMul (Ch02.coarseBlockMatrix U aQ) P) :=
            (Ch02.doubledMuTheory U aQ).doubledMu_eq_coarseBlockMatrix P
  calc
    coarseBlockMatrix (cubeSet Q) a = coarseBlockMatrix (openCubeSet Q) a :=
      coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q a
    _ = Ch02.coarseBlockMatrix U aQ :=
      (eq_coarseBlockMatrix_of_isCoarseBlockMatrix hIso).symm

/-- A law carrier almost surely supplies deterministic coarse block matrix
existence on every fixed triadic open cube. -/
theorem ae_exists_coarseBlockMatrix_openCubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P) (Q : TriadicCube d) :
    ∀ᵐ a ∂P, ∃ Abar : BlockMat d, IsCoarseBlockMatrix (openCubeSet Q) a Abar := by
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  exact exists_coarseBlockMatrix_openCubeSet_of_aelocallyUniformlyEllipticField ha Q

/-- Origin-cube specialization of
`LawCarrier.ae_exists_coarseBlockMatrix_openCubeSet`. -/
theorem ae_exists_coarseBlockMatrix_openCubeSet_originCube
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P) (n : ℤ) :
    ∀ᵐ a ∂P,
      ∃ Abar : BlockMat d, IsCoarseBlockMatrix (openCubeSet (originCube d n)) a Abar :=
  hP.ae_exists_coarseBlockMatrix_openCubeSet (originCube d n)

/-- The lower-right coarse entry `σ_*⁻¹(U; a)ᵢⱼ` is a.e.-measurable on a
deterministic triadic cube. -/
theorem aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (i j : Fin d) :
    AEMeasurable
      (fun a : CoeffField d => (coarseBlockMatrix (cubeSet Q) a).lowerRight i j) P := by
  by_cases hij : i = j
  · subst j
    have hEq :
        (fun a : CoeffField d => (coarseBlockMatrix (cubeSet Q) a).lowerRight i i) =
          (fun a : CoeffField d => (2 : ℝ) * Mu (cubeSet Q) (0, Pi.single i 1) a) := by
      funext a
      simp [coarseBlockMatrix_lowerRight_apply]
    rw [hEq]
    exact (hP.aemeasurable_Mu_cubeSet Q (0, Pi.single i 1)).const_mul (2 : ℝ)
  · have hsum :
        AEMeasurable
          (fun a : CoeffField d =>
            Mu (cubeSet Q) ((0, Pi.single i 1) + (0, Pi.single j 1)) a) P :=
      hP.aemeasurable_Mu_cubeSet Q ((0, Pi.single i 1) + (0, Pi.single j 1))
    have hi :
        AEMeasurable (fun a : CoeffField d => Mu (cubeSet Q) (0, Pi.single i 1) a) P :=
      hP.aemeasurable_Mu_cubeSet Q (0, Pi.single i 1)
    have hj :
        AEMeasurable (fun a : CoeffField d => Mu (cubeSet Q) (0, Pi.single j 1) a) P :=
      hP.aemeasurable_Mu_cubeSet Q (0, Pi.single j 1)
    have hEq :
        (fun a : CoeffField d => (coarseBlockMatrix (cubeSet Q) a).lowerRight i j) =
          (fun a : CoeffField d =>
            Mu (cubeSet Q) ((0, Pi.single i 1) + (0, Pi.single j 1)) a
              - Mu (cubeSet Q) (0, Pi.single i 1) a
              - Mu (cubeSet Q) (0, Pi.single j 1) a) := by
      funext a
      simp [coarseBlockMatrix_lowerRight_apply, hij]
    rw [hEq]
    exact (hsum.sub hi).sub hj

/-- The upper-left coarse entry `b(U; a)ᵢⱼ` is a.e.-measurable on a
deterministic triadic cube. -/
theorem aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (i j : Fin d) :
    AEMeasurable
      (fun a : CoeffField d => (coarseBlockMatrix (cubeSet Q) a).upperLeft i j) P := by
  by_cases hij : i = j
  · subst j
    have hEq :
        (fun a : CoeffField d => (coarseBlockMatrix (cubeSet Q) a).upperLeft i i) =
          (fun a : CoeffField d => (2 : ℝ) * Mu (cubeSet Q) (Pi.single i 1, 0) a) := by
      funext a
      simp [coarseBlockMatrix_upperLeft_apply]
    rw [hEq]
    exact (hP.aemeasurable_Mu_cubeSet Q (Pi.single i 1, 0)).const_mul (2 : ℝ)
  · have hsum :
        AEMeasurable
          (fun a : CoeffField d =>
            Mu (cubeSet Q) ((Pi.single i 1, 0) + (Pi.single j 1, 0)) a) P :=
      hP.aemeasurable_Mu_cubeSet Q ((Pi.single i 1, 0) + (Pi.single j 1, 0))
    have hi :
        AEMeasurable (fun a : CoeffField d => Mu (cubeSet Q) (Pi.single i 1, 0) a) P :=
      hP.aemeasurable_Mu_cubeSet Q (Pi.single i 1, 0)
    have hj :
        AEMeasurable (fun a : CoeffField d => Mu (cubeSet Q) (Pi.single j 1, 0) a) P :=
      hP.aemeasurable_Mu_cubeSet Q (Pi.single j 1, 0)
    have hEq :
        (fun a : CoeffField d => (coarseBlockMatrix (cubeSet Q) a).upperLeft i j) =
          (fun a : CoeffField d =>
            Mu (cubeSet Q) ((Pi.single i 1, 0) + (Pi.single j 1, 0)) a
              - Mu (cubeSet Q) (Pi.single i 1, 0) a
              - Mu (cubeSet Q) (Pi.single j 1, 0) a) := by
      funext a
      simp [coarseBlockMatrix_upperLeft_apply, hij]
    rw [hEq]
    exact (hsum.sub hi).sub hj

/-- Law-relative local-test representative for an upper-left coarse block
entry on a fixed triadic cube.  The representative is constructed from the
canonical `Mu` representatives and agrees a.e. with the raw coarse entry. -/
theorem exists_isLocalRandomVariable_ae_eq_coarseBlockMatrix_upperLeft_apply_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (i j : Fin d) :
    ∃ Y : CoeffField d → ℝ,
      IsLocalRandomVariable (cubeSet Q) Y ∧
        (fun a : CoeffField d => (coarseBlockMatrix (cubeSet Q) a).upperLeft i j)
          =ᵐ[P] Y := by
  by_cases hij : i = j
  · subst j
    rcases hP.exists_isLocalRandomVariable_ae_eq_Mu_cubeSet
        Q (Pi.single i 1, 0) with ⟨Y, hY_local, hY_eq⟩
    refine ⟨fun a => (2 : ℝ) * Y a, measurable_const.mul hY_local, ?_⟩
    filter_upwards [hY_eq] with a ha
    calc
      (coarseBlockMatrix (cubeSet Q) a).upperLeft i i =
          (2 : ℝ) * Mu (cubeSet Q) (Pi.single i 1, 0) a := by
            simp [coarseBlockMatrix_upperLeft_apply]
      _ = (2 : ℝ) * Y a := by rw [ha]
  · rcases hP.exists_isLocalRandomVariable_ae_eq_Mu_cubeSet
        Q ((Pi.single i 1, 0) + (Pi.single j 1, 0)) with
      ⟨Ysum, hYsum_local, hYsum_eq⟩
    rcases hP.exists_isLocalRandomVariable_ae_eq_Mu_cubeSet
        Q (Pi.single i 1, 0) with ⟨Yi, hYi_local, hYi_eq⟩
    rcases hP.exists_isLocalRandomVariable_ae_eq_Mu_cubeSet
        Q (Pi.single j 1, 0) with ⟨Yj, hYj_local, hYj_eq⟩
    refine ⟨fun a => Ysum a - Yi a - Yj a,
      (hYsum_local.sub hYi_local).sub hYj_local, ?_⟩
    filter_upwards [hYsum_eq, hYi_eq, hYj_eq] with a hsum hi hj
    calc
      (coarseBlockMatrix (cubeSet Q) a).upperLeft i j =
          Mu (cubeSet Q) ((Pi.single i 1, 0) + (Pi.single j 1, 0)) a -
            Mu (cubeSet Q) (Pi.single i 1, 0) a -
            Mu (cubeSet Q) (Pi.single j 1, 0) a := by
            simp [coarseBlockMatrix_upperLeft_apply, hij]
      _ = Ysum a - Yi a - Yj a := by rw [hsum, hi, hj]

/-- Law-relative local-test representative for a lower-right coarse block
entry on a fixed triadic cube.  The representative is constructed from the
canonical `Mu` representatives and agrees a.e. with the raw coarse entry. -/
theorem exists_isLocalRandomVariable_ae_eq_coarseBlockMatrix_lowerRight_apply_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (i j : Fin d) :
    ∃ Y : CoeffField d → ℝ,
      IsLocalRandomVariable (cubeSet Q) Y ∧
        (fun a : CoeffField d => (coarseBlockMatrix (cubeSet Q) a).lowerRight i j)
          =ᵐ[P] Y := by
  by_cases hij : i = j
  · subst j
    rcases hP.exists_isLocalRandomVariable_ae_eq_Mu_cubeSet
        Q (0, Pi.single i 1) with ⟨Y, hY_local, hY_eq⟩
    refine ⟨fun a => (2 : ℝ) * Y a, measurable_const.mul hY_local, ?_⟩
    filter_upwards [hY_eq] with a ha
    calc
      (coarseBlockMatrix (cubeSet Q) a).lowerRight i i =
          (2 : ℝ) * Mu (cubeSet Q) (0, Pi.single i 1) a := by
            simp [coarseBlockMatrix_lowerRight_apply]
      _ = (2 : ℝ) * Y a := by rw [ha]
  · rcases hP.exists_isLocalRandomVariable_ae_eq_Mu_cubeSet
        Q ((0, Pi.single i 1) + (0, Pi.single j 1)) with
      ⟨Ysum, hYsum_local, hYsum_eq⟩
    rcases hP.exists_isLocalRandomVariable_ae_eq_Mu_cubeSet
        Q (0, Pi.single i 1) with ⟨Yi, hYi_local, hYi_eq⟩
    rcases hP.exists_isLocalRandomVariable_ae_eq_Mu_cubeSet
        Q (0, Pi.single j 1) with ⟨Yj, hYj_local, hYj_eq⟩
    refine ⟨fun a => Ysum a - Yi a - Yj a,
      (hYsum_local.sub hYi_local).sub hYj_local, ?_⟩
    filter_upwards [hYsum_eq, hYi_eq, hYj_eq] with a hsum hi hj
    calc
      (coarseBlockMatrix (cubeSet Q) a).lowerRight i j =
          Mu (cubeSet Q) ((0, Pi.single i 1) + (0, Pi.single j 1)) a -
            Mu (cubeSet Q) (0, Pi.single i 1) a -
            Mu (cubeSet Q) (0, Pi.single j 1) a := by
            simp [coarseBlockMatrix_lowerRight_apply, hij]
      _ = Ysum a - Yi a - Yj a := by rw [hsum, hi, hj]

/-- The upper-right mixed coarse entry is a.e.-measurable on a deterministic
triadic cube. -/
theorem aemeasurable_coarseBlockMatrix_upperRight_apply_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (i j : Fin d) :
    AEMeasurable
      (fun a : CoeffField d => (coarseBlockMatrix (cubeSet Q) a).upperRight i j) P := by
  have hsum :
      AEMeasurable
        (fun a : CoeffField d =>
          Mu (cubeSet Q) ((Pi.single i 1, 0) + (0, Pi.single j 1)) a) P :=
    hP.aemeasurable_Mu_cubeSet Q ((Pi.single i 1, 0) + (0, Pi.single j 1))
  have hi :
      AEMeasurable (fun a : CoeffField d => Mu (cubeSet Q) (Pi.single i 1, 0) a) P :=
    hP.aemeasurable_Mu_cubeSet Q (Pi.single i 1, 0)
  have hj :
      AEMeasurable (fun a : CoeffField d => Mu (cubeSet Q) (0, Pi.single j 1) a) P :=
    hP.aemeasurable_Mu_cubeSet Q (0, Pi.single j 1)
  have hEq :
      (fun a : CoeffField d => (coarseBlockMatrix (cubeSet Q) a).upperRight i j) =
        (fun a : CoeffField d =>
          Mu (cubeSet Q) ((Pi.single i 1, 0) + (0, Pi.single j 1)) a
            - Mu (cubeSet Q) (Pi.single i 1, 0) a
            - Mu (cubeSet Q) (0, Pi.single j 1) a) := by
    funext a
    simp [coarseBlockMatrix_upperRight_apply]
  rw [hEq]
  exact (hsum.sub hi).sub hj

/-- The lower-left mixed coarse entry is a.e.-measurable on a deterministic
triadic cube. -/
theorem aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (i j : Fin d) :
    AEMeasurable
      (fun a : CoeffField d => (coarseBlockMatrix (cubeSet Q) a).lowerLeft i j) P := by
  have hsum :
      AEMeasurable
        (fun a : CoeffField d =>
          Mu (cubeSet Q) ((0, Pi.single i 1) + (Pi.single j 1, 0)) a) P :=
    hP.aemeasurable_Mu_cubeSet Q ((0, Pi.single i 1) + (Pi.single j 1, 0))
  have hi :
      AEMeasurable (fun a : CoeffField d => Mu (cubeSet Q) (0, Pi.single i 1) a) P :=
    hP.aemeasurable_Mu_cubeSet Q (0, Pi.single i 1)
  have hj :
      AEMeasurable (fun a : CoeffField d => Mu (cubeSet Q) (Pi.single j 1, 0) a) P :=
    hP.aemeasurable_Mu_cubeSet Q (Pi.single j 1, 0)
  have hEq :
      (fun a : CoeffField d => (coarseBlockMatrix (cubeSet Q) a).lowerLeft i j) =
        (fun a : CoeffField d =>
          Mu (cubeSet Q) ((0, Pi.single i 1) + (Pi.single j 1, 0)) a
            - Mu (cubeSet Q) (0, Pi.single i 1) a
            - Mu (cubeSet Q) (Pi.single j 1, 0) a) := by
    funext a
    simp [coarseBlockMatrix_lowerLeft_apply]
  rw [hEq]
  exact (hsum.sub hi).sub hj

/-- The full unfolded coarse block matrix is a.e.-measurable. -/
theorem aemeasurable_coarseFullBlockMatrix_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) :
    AEMeasurable
      (fun a : CoeffField d => toFullBlockMat (coarseBlockMatrix (cubeSet Q) a)) P := by
  rw [aemeasurable_pi_iff]
  intro α
  rw [aemeasurable_pi_iff]
  intro β
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          simpa [toFullBlockMat] using
            hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet Q i j
      | inr j =>
          simpa [toFullBlockMat] using
            hP.aemeasurable_coarseBlockMatrix_upperRight_apply_cubeSet Q i j
  | inr i =>
      cases β with
      | inl j =>
          simpa [toFullBlockMat] using
            hP.aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet Q i j
      | inr j =>
          simpa [toFullBlockMat] using
            hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet Q i j

/-- The upper-left block `b(U; a)` is a.e.-measurable as a matrix-valued
observable. -/
theorem aemeasurable_coarseB_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) :
    AEMeasurable
      (fun a : CoeffField d => (coarseBlockMatrix (cubeSet Q) a).upperLeft) P := by
  rw [aemeasurable_pi_iff]
  intro i
  rw [aemeasurable_pi_iff]
  intro j
  exact hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet Q i j

/-- The upper-right block of the doubled coarse matrix is a.e.-measurable. -/
theorem aemeasurable_coarseBlockMatrix_upperRight_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) :
    AEMeasurable
      (fun a : CoeffField d => (coarseBlockMatrix (cubeSet Q) a).upperRight) P := by
  rw [aemeasurable_pi_iff]
  intro i
  rw [aemeasurable_pi_iff]
  intro j
  exact hP.aemeasurable_coarseBlockMatrix_upperRight_apply_cubeSet Q i j

/-- The lower-left block of the doubled coarse matrix is a.e.-measurable. -/
theorem aemeasurable_coarseBlockMatrix_lowerLeft_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) :
    AEMeasurable
      (fun a : CoeffField d => (coarseBlockMatrix (cubeSet Q) a).lowerLeft) P := by
  rw [aemeasurable_pi_iff]
  intro i
  rw [aemeasurable_pi_iff]
  intro j
  exact hP.aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet Q i j

/-- The lower-right block `σ_*⁻¹(U; a)` is a.e.-measurable as a matrix-valued
observable. -/
theorem aemeasurable_coarseSigmaStarInv_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) :
    AEMeasurable
      (fun a : CoeffField d => (coarseBlockMatrix (cubeSet Q) a).lowerRight) P := by
  rw [aemeasurable_pi_iff]
  intro i
  rw [aemeasurable_pi_iff]
  intro j
  exact hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet Q i j

/-- The mixed observable `σ_*⁻¹(U; a)κ(U; a)`, represented as the negative
lower-left block, is a.e.-measurable as a matrix-valued observable. -/
theorem aemeasurable_coarseSigmaStarInvKappaMean_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) :
    AEMeasurable
      (fun a : CoeffField d => -((coarseBlockMatrix (cubeSet Q) a).lowerLeft)) P := by
  rw [aemeasurable_pi_iff]
  intro i
  rw [aemeasurable_pi_iff]
  intro j
  exact (hP.aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet Q i j).neg

/-- The full unfolded starred inverse coarse block matrix is a.e.-measurable. -/
theorem aemeasurable_coarseStarredFullBlockMatrixInv_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) :
    AEMeasurable
      (fun a : CoeffField d => toFullBlockMat (coarseStarredBlockMatrixInv (cubeSet Q) a)) P := by
  rw [aemeasurable_pi_iff]
  intro α
  rw [aemeasurable_pi_iff]
  intro β
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          simpa [toFullBlockMat, coarseStarredBlockMatrixInv_eq_blockReflect, blockReflect] using
            hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet Q i j
      | inr j =>
          simpa [toFullBlockMat, coarseStarredBlockMatrixInv_eq_blockReflect, blockReflect] using
            hP.aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet Q i j
  | inr i =>
      cases β with
      | inl j =>
          simpa [toFullBlockMat, coarseStarredBlockMatrixInv_eq_blockReflect, blockReflect] using
            hP.aemeasurable_coarseBlockMatrix_upperRight_apply_cubeSet Q i j
      | inr j =>
          simpa [toFullBlockMat, coarseStarredBlockMatrixInv_eq_blockReflect, blockReflect] using
            hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet Q i j

/-- Finite descendant averages of `Mu` over child cubes are a.e.-measurable. -/
theorem aemeasurable_descendantsAverage_Mu_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (j : ℕ) (P0 : BlockVec d) :
    AEMeasurable
      (fun a : CoeffField d =>
        descendantsAverage Q j (fun R => Mu (cubeSet R) P0 a)) P :=
  aemeasurable_descendantsAverage
    (P := P) (Q := Q) (j := j)
    (F := fun R a => Mu (cubeSet R) P0 a)
    (fun R _ => hP.aemeasurable_Mu_cubeSet R P0)

/-- Finite descendant averages of upper-left coarse entries are
a.e.-measurable. -/
theorem aemeasurable_descendantsAverage_coarseBlockMatrix_upperLeft_apply_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (j : ℕ) (i k : Fin d) :
    AEMeasurable
      (fun a : CoeffField d =>
        descendantsAverage Q j
          (fun R => (coarseBlockMatrix (cubeSet R) a).upperLeft i k)) P :=
  aemeasurable_descendantsAverage
    (P := P) (Q := Q) (j := j)
    (F := fun R a => (coarseBlockMatrix (cubeSet R) a).upperLeft i k)
    (fun R _ => hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet R i k)

/-- Finite descendant averages of upper-right coarse entries are
a.e.-measurable. -/
theorem aemeasurable_descendantsAverage_coarseBlockMatrix_upperRight_apply_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (j : ℕ) (i k : Fin d) :
    AEMeasurable
      (fun a : CoeffField d =>
        descendantsAverage Q j
          (fun R => (coarseBlockMatrix (cubeSet R) a).upperRight i k)) P :=
  aemeasurable_descendantsAverage
    (P := P) (Q := Q) (j := j)
    (F := fun R a => (coarseBlockMatrix (cubeSet R) a).upperRight i k)
    (fun R _ => hP.aemeasurable_coarseBlockMatrix_upperRight_apply_cubeSet R i k)

/-- Finite descendant averages of lower-left coarse entries are
a.e.-measurable. -/
theorem aemeasurable_descendantsAverage_coarseBlockMatrix_lowerLeft_apply_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (j : ℕ) (i k : Fin d) :
    AEMeasurable
      (fun a : CoeffField d =>
        descendantsAverage Q j
          (fun R => (coarseBlockMatrix (cubeSet R) a).lowerLeft i k)) P :=
  aemeasurable_descendantsAverage
    (P := P) (Q := Q) (j := j)
    (F := fun R a => (coarseBlockMatrix (cubeSet R) a).lowerLeft i k)
    (fun R _ => hP.aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet R i k)

/-- Finite descendant averages of lower-right coarse entries are
a.e.-measurable. -/
theorem aemeasurable_descendantsAverage_coarseBlockMatrix_lowerRight_apply_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (j : ℕ) (i k : Fin d) :
    AEMeasurable
      (fun a : CoeffField d =>
        descendantsAverage Q j
          (fun R => (coarseBlockMatrix (cubeSet R) a).lowerRight i k)) P :=
  aemeasurable_descendantsAverage
    (P := P) (Q := Q) (j := j)
    (F := fun R a => (coarseBlockMatrix (cubeSet R) a).lowerRight i k)
    (fun R _ => hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet R i k)

/-- Compose an a.e.-measurable observable with adjointing the coefficient
field when the law is adjoint-invariant. -/
theorem aemeasurable_comp_adjointCoeffField_of_adjointInvariantLaw
    {d : ℕ} {P : CoeffLaw d} {β : Type*} [MeasurableSpace β]
    {F : CoeffField d → β}
    (hAdj : AdjointInvariantLaw P) (hF : AEMeasurable F P) :
    AEMeasurable (fun a : CoeffField d => F (adjointCoeffField a)) P := by
  have hFMap :
      AEMeasurable F (Measure.map (adjointCoeffField (d := d)) P) := by
    rwa [hAdj]
  simpa [Function.comp_def] using
    hFMap.comp_measurable (measurable_adjointCoeffField (d := d))

/-- The adjointed `Mu` observable is a.e.-measurable under an adjoint-invariant
law. -/
theorem aemeasurable_Mu_adjointCoeffField_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (hAdj : AdjointInvariantLaw P) (Q : TriadicCube d) (P0 : BlockVec d) :
    AEMeasurable
      (fun a : CoeffField d => Mu (cubeSet Q) P0 (adjointCoeffField a)) P :=
  aemeasurable_comp_adjointCoeffField_of_adjointInvariantLaw hAdj
    (hP.aemeasurable_Mu_cubeSet Q P0)

/-- `ResponseJ` is a.e.-measurable whenever the manuscript identity expressing
it as `Mu(U; (-p,q)) - p·q` holds almost surely. -/
theorem aemeasurable_ResponseJ_cubeSet_of_ae_eq_mu
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (p q : Vec d)
    (hEq :
      (fun a : CoeffField d => ResponseJ (cubeSet Q) p q a) =ᵐ[P]
        (fun a : CoeffField d => Mu (cubeSet Q) (-p, q) a - vecDot p q)) :
    AEMeasurable (fun a : CoeffField d => ResponseJ (cubeSet Q) p q a) P := by
  have hMu :
      AEMeasurable
        (fun a : CoeffField d => Mu (cubeSet Q) (-p, q) a - vecDot p q) P :=
    (hP.aemeasurable_Mu_cubeSet Q (-p, q)).sub aemeasurable_const
  exact hMu.congr hEq.symm

/-- Under a law carrier, the deterministic Chapter 2 identity
`ResponseJ = Mu(-p,q) - p·q` holds almost surely on each deterministic
triadic cube. -/
theorem ResponseJ_cubeSet_eq_Mu_neg_left_sub_vecDot_ae
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (p q : Vec d) :
    (fun a : CoeffField d => ResponseJ (cubeSet Q) p q a) =ᵐ[P]
      (fun a : CoeffField d => Mu (cubeSet Q) (-p, q) a - vecDot p q) := by
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  have hId :=
    Ch02.ResponseJ_cubeSet_eq_Mu_neg_left_sub_vecDot
      (Q := Q) (a := coeffOnOfAEEllipticOn a Q (ha Q)) p q
  simpa [coeffOnOfAEEllipticOn_toCoeffField] using hId

/-- The scalar response observable is a.e.-measurable under a law carrier. -/
theorem aemeasurable_ResponseJ_cubeSet
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (p q : Vec d) :
    AEMeasurable (fun a : CoeffField d => ResponseJ (cubeSet Q) p q a) P :=
  hP.aemeasurable_ResponseJ_cubeSet_of_ae_eq_mu Q p q
    (hP.ResponseJ_cubeSet_eq_Mu_neg_left_sub_vecDot_ae Q p q)

/-- Finite descendant averages of `ResponseJ` are a.e.-measurable whenever each
child response is almost surely identified with the corresponding `Mu`
observable. -/
theorem aemeasurable_descendantsAverage_ResponseJ_cubeSet_of_ae_eq_mu
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d)
    (hEq :
      ∀ R, R ∈ descendantsAtDepth Q j →
        (fun a : CoeffField d => ResponseJ (cubeSet R) p q a) =ᵐ[P]
          (fun a : CoeffField d => Mu (cubeSet R) (-p, q) a - vecDot p q)) :
    AEMeasurable
      (fun a : CoeffField d =>
        descendantsAverage Q j (fun R => ResponseJ (cubeSet R) p q a)) P :=
  aemeasurable_descendantsAverage
    (P := P) (Q := Q) (j := j)
    (F := fun R a => ResponseJ (cubeSet R) p q a)
    (fun R hR => hP.aemeasurable_ResponseJ_cubeSet_of_ae_eq_mu R p q (hEq R hR))

/-- Finite descendant averages of scalar response observables are
a.e.-measurable under a law carrier. -/
theorem aemeasurable_descendantsAverage_ResponseJ_cubeSet
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    AEMeasurable
      (fun a : CoeffField d =>
        descendantsAverage Q j (fun R => ResponseJ (cubeSet R) p q a)) P :=
  aemeasurable_descendantsAverage
    (P := P) (Q := Q) (j := j)
    (F := fun R a => ResponseJ (cubeSet R) p q a)
    (fun R _hR => hP.aemeasurable_ResponseJ_cubeSet R p q)

/-- The adjointed `ResponseJ` observable is a.e.-measurable whenever the
manuscript identity expressing it through adjointed `Mu` holds almost surely. -/
theorem aemeasurable_ResponseJ_adjointCoeffField_cubeSet_of_ae_eq_mu
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (hAdj : AdjointInvariantLaw P) (Q : TriadicCube d) (p q : Vec d)
    (hEq :
      (fun a : CoeffField d => ResponseJ (cubeSet Q) p q (adjointCoeffField a)) =ᵐ[P]
        (fun a : CoeffField d =>
          Mu (cubeSet Q) (-p, q) (adjointCoeffField a) - vecDot p q)) :
    AEMeasurable
      (fun a : CoeffField d => ResponseJ (cubeSet Q) p q (adjointCoeffField a)) P := by
  have hMu :
      AEMeasurable
        (fun a : CoeffField d =>
          Mu (cubeSet Q) (-p, q) (adjointCoeffField a) - vecDot p q) P :=
    (hP.aemeasurable_Mu_adjointCoeffField_cubeSet hAdj Q (-p, q)).sub aemeasurable_const
  exact hMu.congr hEq.symm

end LawCarrier

end Ch04
end Book
end Homogenization
