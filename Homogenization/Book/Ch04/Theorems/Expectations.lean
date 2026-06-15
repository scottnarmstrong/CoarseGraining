import Homogenization.Book.Ch04.Theorems.CoarseObservables
import Homogenization.Book.Ch04.AnnealedDefinitions
import Homogenization.Deterministic.MultiscaleQuantitiesBasic.Foundation.Basic

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Expectations and finite response moments

This file is the public Chapter 4 surface for taking expectations of the
scalar response observables already exposed in `CoarseObservables`.

The surface is intentionally small: it names the observable, its expectation,
the centered observable used in the manuscript, and the finite descendant
average expectation theorem.  Integrability remains an explicit theorem
hypothesis; there is no extra moment carrier or section-local wrapper track.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal
open scoped Matrix.Norms.Elementwise

/-- Finite-dimensional matrix quadratic forms commute with entrywise
expectation under entrywise integrability. -/
theorem integral_vecDot_matVecMul_eq_entrywise_integral
    {d : ℕ} {P : CoeffLaw d} {M : CoeffField d → Mat d}
    (hM : ∀ i j, Integrable (fun a => M a i j) P) (x y : Vec d) :
    ∫ a, vecDot x (matVecMul (M a) y) ∂P =
      vecDot x (matVecMul (fun i j => ∫ a, M a i j ∂P) y) := by
  simp [vecDot, matVecMul]
  rw [MeasureTheory.integral_finset_sum Finset.univ]
  · congr 1
    ext i
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_finset_sum Finset.univ]
    · simp_rw [MeasureTheory.integral_mul_const]
    · intro j _hj
      exact (hM i j).mul_const (y j)
  · intro i _hi
    exact (MeasureTheory.integrable_finset_sum Finset.univ fun j _hj =>
      (hM i j).mul_const (y j)).const_mul (x i)

/-- Full coarse-block integrability gives entrywise integrability of the
corresponding doubled coarse matrix. -/
private theorem integrable_blockMatEntry_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} {P : CoeffLaw d} {Q : TriadicCube d}
    (hInt : Integrable (coarseFullBlockMatrixAtCube Q) P) :
    ∀ α β,
      Integrable
        (fun a : CoeffField d => blockMatEntry (coarseBlockMatrix (cubeSet Q) a) α β) P := by
  intro α β
  have hα : Integrable (fun a : CoeffField d => coarseFullBlockMatrixAtCube Q a α) P :=
    MeasureTheory.Integrable.eval hInt α
  have hαβ : Integrable (fun a : CoeffField d => coarseFullBlockMatrixAtCube Q a α β) P :=
    MeasureTheory.Integrable.eval hα β
  simpa [coarseFullBlockMatrixAtCube, coarseFullBlockMatrixObservable, toFullBlockMat,
    blockMatEntry] using hαβ

/-- Scalar response observable on a deterministic triadic cube. -/
noncomputable def responseJObservableCubeSet {d : ℕ}
    (Q : TriadicCube d) (p q : Vec d) : CoeffField d → ℝ :=
  fun a => ResponseJ (cubeSet Q) p q a

@[simp]
theorem responseJObservableCubeSet_apply {d : ℕ}
    (Q : TriadicCube d) (p q : Vec d) (a : CoeffField d) :
    responseJObservableCubeSet Q p q a = ResponseJ (cubeSet Q) p q a :=
  rfl

/-- The scalar response observable is pointwise nonnegative. -/
theorem responseJObservableCubeSet_nonneg {d : ℕ}
    (Q : TriadicCube d) (p q : Vec d) (a : CoeffField d) :
    0 ≤ responseJObservableCubeSet Q p q a := by
  simpa [responseJObservableCubeSet] using responseJ_nonneg (cubeSet Q) p q a

theorem responseJObservableCubeSet_ae_eq_quadratic_coarseBlockMatrix_of_lawCarrier
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (p q : Vec d) :
    (fun a : CoeffField d => responseJObservableCubeSet Q p q a) =ᵐ[P]
      (fun a : CoeffField d =>
        (1 / 2 : ℝ) * vecDot q (matVecMul (coarseBlockMatrix (cubeSet Q) a).lowerRight q) -
          vecDot p q -
          vecDot q (matVecMul (coarseBlockMatrix (cubeSet Q) a).lowerLeft p) +
          (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix (cubeSet Q) a).upperLeft p)) := by
  filter_upwards
    [hP.ResponseJ_cubeSet_eq_Mu_neg_left_sub_vecDot_ae Q p q,
      hP.ae_exists_coarseBlockMatrix_openCubeSet Q] with a hResponse hex
  have hCoarse :
      IsCoarseBlockMatrix (openCubeSet Q) a (coarseBlockMatrix (openCubeSet Q) a) :=
    isCoarseBlockMatrix_coarseBlockMatrix hex
  calc
    responseJObservableCubeSet Q p q a = ResponseJ (cubeSet Q) p q a := rfl
    _ = Mu (cubeSet Q) (-p, q) a - vecDot p q := hResponse
    _ = Mu (openCubeSet Q) (-p, q) a - vecDot p q := by
      rw [Mu_cubeSet_eq_openCubeSet_of_triadicCube (Q := Q) (P := (-p, q)) (a := a)]
    _ =
        (1 / 2 : ℝ) *
            blockVecDot (-p, q)
              (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) (-p, q)) -
          vecDot p q := by
        rw [Mu_eq_half_blockVecDot_coarseBlockMatrix hex (-p, q)]
    _ =
        (1 / 2 : ℝ) *
            vecDot q (matVecMul (coarseBlockMatrix (openCubeSet Q) a).lowerRight q) -
          vecDot p q -
          vecDot q (matVecMul (coarseBlockMatrix (openCubeSet Q) a).lowerLeft p) +
          (1 / 2 : ℝ) *
            vecDot p (matVecMul (coarseBlockMatrix (openCubeSet Q) a).upperLeft p) := by
        rw [magic_half_blockVecDot_neg_left_of_isSymmetricBlockMat hCoarse.1 p q]
        ring
    _ =
        (1 / 2 : ℝ) *
            vecDot q (matVecMul (coarseBlockMatrix (cubeSet Q) a).lowerRight q) -
          vecDot p q -
          vecDot q (matVecMul (coarseBlockMatrix (cubeSet Q) a).lowerLeft p) +
          (1 / 2 : ℝ) *
            vecDot p (matVecMul (coarseBlockMatrix (cubeSet Q) a).upperLeft p) := by
        rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q a]

private theorem integrable_responseJQuadratic_coarseBlockMatrix_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} {P : CoeffLaw d} [IsFiniteMeasure P] {Q : TriadicCube d} (p q : Vec d)
    (hBlock : Integrable (coarseFullBlockMatrixAtCube Q) P) :
    Integrable
      (fun a : CoeffField d =>
        (1 / 2 : ℝ) * vecDot q (matVecMul (coarseBlockMatrix (cubeSet Q) a).lowerRight q) -
          vecDot p q -
          vecDot q (matVecMul (coarseBlockMatrix (cubeSet Q) a).lowerLeft p) +
          (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix (cubeSet Q) a).upperLeft p)) P := by
  let M : CoeffField d → BlockMat d := fun a => coarseBlockMatrix (cubeSet Q) a
  have hEntry := integrable_blockMatEntry_of_integrable_coarseFullBlockMatrixAtCube hBlock
  have hLR : ∀ i j, Integrable (fun a : CoeffField d => (M a).lowerRight i j) P := by
    intro i j
    simpa [M, blockMatEntry] using hEntry (Sum.inr i) (Sum.inr j)
  have hLL : ∀ i j, Integrable (fun a : CoeffField d => (M a).lowerLeft i j) P := by
    intro i j
    simpa [M, blockMatEntry] using hEntry (Sum.inr i) (Sum.inl j)
  have hUL : ∀ i j, Integrable (fun a : CoeffField d => (M a).upperLeft i j) P := by
    intro i j
    simpa [M, blockMatEntry] using hEntry (Sum.inl i) (Sum.inl j)
  have hTermLR :
      Integrable (fun a : CoeffField d => vecDot q (matVecMul (M a).lowerRight q)) P := by
    simp [vecDot, matVecMul]
    exact MeasureTheory.integrable_finset_sum Finset.univ fun i _ =>
      (MeasureTheory.integrable_finset_sum Finset.univ fun j _ =>
        (hLR i j).mul_const (q j)).const_mul (q i)
  have hTermLL :
      Integrable (fun a : CoeffField d => vecDot q (matVecMul (M a).lowerLeft p)) P := by
    simp [vecDot, matVecMul]
    exact MeasureTheory.integrable_finset_sum Finset.univ fun i _ =>
      (MeasureTheory.integrable_finset_sum Finset.univ fun j _ =>
        (hLL i j).mul_const (p j)).const_mul (q i)
  have hTermUL :
      Integrable (fun a : CoeffField d => vecDot p (matVecMul (M a).upperLeft p)) P := by
    simp [vecDot, matVecMul]
    exact MeasureTheory.integrable_finset_sum Finset.univ fun i _ =>
      (MeasureTheory.integrable_finset_sum Finset.univ fun j _ =>
        (hUL i j).mul_const (p j)).const_mul (p i)
  simpa [M] using
    (((hTermLR.const_mul (1 / 2 : ℝ)).sub (integrable_const _)).sub hTermLL).add
      (hTermUL.const_mul (1 / 2 : ℝ))

namespace LawCarrier

/-- Full coarse-block integrability makes the scalar response integrable.

The law carrier supplies the a.s. elliptic support and the deterministic
`ResponseJ = Mu(-p,q) - p·q` identity; the only remaining analytic input is
integrability of the finite-dimensional coarse block. -/
theorem integrable_responseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (p q : Vec d)
    (hBlock : Integrable (coarseFullBlockMatrixAtCube Q) P) :
    Integrable (responseJObservableCubeSet Q p q) P := by
  letI : IsProbabilityMeasure P := hP.isProbability
  exact
    (integrable_responseJQuadratic_coarseBlockMatrix_of_integrable_coarseFullBlockMatrixAtCube
      (P := P) (Q := Q) p q hBlock).congr
        (responseJObservableCubeSet_ae_eq_quadratic_coarseBlockMatrix_of_lawCarrier
          hP Q p q).symm

/-- Expected scalar response expressed through the annealed coarse block
matrix, with the stochastic hypotheses packaged in `LawCarrier`.

This is the note-facing Chapter 4 source identity: Ch5 should call this rather
than passing deterministic coarse-data witnesses. -/
theorem integral_responseJObservableCubeSet_eq_quadratic_annealedBlockMatrix
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (p q : Vec d)
    (hBlock : Integrable (coarseFullBlockMatrixAtCube Q) P) :
    ∫ a, responseJObservableCubeSet Q p q a ∂P =
      (1 / 2 : ℝ) * vecDot q (matVecMul (annealedBlockMatrix P (cubeSet Q)).lowerRight q) -
        vecDot p q -
        vecDot q (matVecMul (annealedBlockMatrix P (cubeSet Q)).lowerLeft p) +
        (1 / 2 : ℝ) * vecDot p (matVecMul (annealedBlockMatrix P (cubeSet Q)).upperLeft p) := by
  letI : IsProbabilityMeasure P := hP.isProbability
  let M : CoeffField d → BlockMat d := fun a => coarseBlockMatrix (cubeSet Q) a
  have hEntry := integrable_blockMatEntry_of_integrable_coarseFullBlockMatrixAtCube hBlock
  have hLR : ∀ i j, Integrable (fun a : CoeffField d => (M a).lowerRight i j) P := by
    intro i j
    simpa [M, blockMatEntry] using hEntry (Sum.inr i) (Sum.inr j)
  have hLL : ∀ i j, Integrable (fun a : CoeffField d => (M a).lowerLeft i j) P := by
    intro i j
    simpa [M, blockMatEntry] using hEntry (Sum.inr i) (Sum.inl j)
  have hUL : ∀ i j, Integrable (fun a : CoeffField d => (M a).upperLeft i j) P := by
    intro i j
    simpa [M, blockMatEntry] using hEntry (Sum.inl i) (Sum.inl j)
  have hFormula :=
    responseJObservableCubeSet_ae_eq_quadratic_coarseBlockMatrix_of_lawCarrier hP Q p q
  have hLRint := integral_vecDot_matVecMul_eq_entrywise_integral (P := P) hLR q q
  have hLLint := integral_vecDot_matVecMul_eq_entrywise_integral (P := P) hLL q p
  have hULint := integral_vecDot_matVecMul_eq_entrywise_integral (P := P) hUL p p
  calc
    ∫ a, responseJObservableCubeSet Q p q a ∂P
        =
      ∫ a,
        (1 / 2 : ℝ) * vecDot q (matVecMul (M a).lowerRight q) -
          vecDot p q -
          vecDot q (matVecMul (M a).lowerLeft p) +
          (1 / 2 : ℝ) * vecDot p (matVecMul (M a).upperLeft p) ∂P :=
        integral_congr_ae hFormula
    _ =
      (1 / 2 : ℝ) * ∫ a, vecDot q (matVecMul (M a).lowerRight q) ∂P -
        vecDot p q -
        ∫ a, vecDot q (matVecMul (M a).lowerLeft p) ∂P +
        (1 / 2 : ℝ) * ∫ a, vecDot p (matVecMul (M a).upperLeft p) ∂P := by
        let f : CoeffField d → ℝ := fun a => vecDot q (matVecMul (M a).lowerRight q)
        let g : CoeffField d → ℝ := fun a => vecDot q (matVecMul (M a).lowerLeft p)
        let h : CoeffField d → ℝ := fun a => vecDot p (matVecMul (M a).upperLeft p)
        have hf : Integrable f P := by
          simp [f, vecDot, matVecMul]
          exact MeasureTheory.integrable_finset_sum Finset.univ fun i _ =>
            (MeasureTheory.integrable_finset_sum Finset.univ fun j _ =>
              (hLR i j).mul_const (q j)).const_mul (q i)
        have hg : Integrable g P := by
          simp [g, vecDot, matVecMul]
          exact MeasureTheory.integrable_finset_sum Finset.univ fun i _ =>
            (MeasureTheory.integrable_finset_sum Finset.univ fun j _ =>
              (hLL i j).mul_const (p j)).const_mul (q i)
        have hh : Integrable h P := by
          simp [h, vecDot, matVecMul]
          exact MeasureTheory.integrable_finset_sum Finset.univ fun i _ =>
            (MeasureTheory.integrable_finset_sum Finset.univ fun j _ =>
              (hUL i j).mul_const (p j)).const_mul (p i)
        rw [integral_add]
        · rw [integral_sub]
          · rw [integral_sub]
            · rw [integral_const_mul]
              rw [integral_const]
              rw [integral_const_mul]
              simp [Measure.real, IsProbabilityMeasure.measure_univ]
            · exact hf.const_mul (1 / 2 : ℝ)
            · exact integrable_const _
          · exact (hf.const_mul (1 / 2 : ℝ)).sub (integrable_const _)
          · exact hg
        · exact ((hf.const_mul (1 / 2 : ℝ)).sub (integrable_const _)).sub hg
        · exact hh.const_mul (1 / 2 : ℝ)
    _ =
      (1 / 2 : ℝ) * vecDot q (matVecMul (annealedBlockMatrix P (cubeSet Q)).lowerRight q) -
        vecDot p q -
        vecDot q (matVecMul (annealedBlockMatrix P (cubeSet Q)).lowerLeft p) +
        (1 / 2 : ℝ) * vecDot p (matVecMul (annealedBlockMatrix P (cubeSet Q)).upperLeft p) := by
        rw [hLRint, hLLint, hULint]
        rfl

end LawCarrier

/-- Centered scalar response observable on a deterministic triadic cube. -/
noncomputable def centeredResponseJObservableCubeSet {d : ℕ}
    (Q : TriadicCube d) (p q p0 q0 : Vec d) : CoeffField d → ℝ :=
  fun a => responseJObservableCubeSet Q p q a - (1 / 2 : ℝ) * vecDot p0 q0

@[simp]
theorem centeredResponseJObservableCubeSet_apply {d : ℕ}
    (Q : TriadicCube d) (p q p0 q0 : Vec d) (a : CoeffField d) :
    centeredResponseJObservableCubeSet Q p q p0 q0 a =
      responseJObservableCubeSet Q p q a - (1 / 2 : ℝ) * vecDot p0 q0 :=
  rfl

/-- Annealed scalar response on a deterministic triadic cube. -/
noncomputable def expectedResponseJCubeSet {d : ℕ}
    (P : CoeffLaw d) (Q : TriadicCube d) (p q : Vec d) : ℝ :=
  ∫ a, responseJObservableCubeSet Q p q a ∂P

/-- Expected scalar response expressed through the annealed coarse block matrix.

The only stochastic hypotheses are the deterministic coarse-data identity
almost surely and integrability of the full coarse block.  Scalarization is
not used here; Ch5 gets its scalar formula by specializing this source
identity. -/
theorem integral_responseJObservableCubeSet_eq_quadratic_annealedBlockMatrix
    {d : ℕ} [NeZero d] {P : CoeffLaw d} [IsProbabilityMeasure P]
    (Q : TriadicCube d) (p q : Vec d)
    (hData : ∀ᵐ a ∂P, OpenCubeDeterministicCoarseData Q a)
    (hBlock : Integrable (coarseFullBlockMatrixAtCube Q) P) :
    ∫ a, responseJObservableCubeSet Q p q a ∂P =
      (1 / 2 : ℝ) * vecDot q (matVecMul (annealedBlockMatrix P (cubeSet Q)).lowerRight q) -
        vecDot p q -
        vecDot q (matVecMul (annealedBlockMatrix P (cubeSet Q)).lowerLeft p) +
        (1 / 2 : ℝ) * vecDot p (matVecMul (annealedBlockMatrix P (cubeSet Q)).upperLeft p) := by
  let M : CoeffField d → BlockMat d := fun a => coarseBlockMatrix (cubeSet Q) a
  have hEntry := integrable_blockMatEntry_of_integrable_coarseFullBlockMatrixAtCube hBlock
  have hLR : ∀ i j, Integrable (fun a : CoeffField d => (M a).lowerRight i j) P := by
    intro i j
    simpa [M, blockMatEntry] using hEntry (Sum.inr i) (Sum.inr j)
  have hLL : ∀ i j, Integrable (fun a : CoeffField d => (M a).lowerLeft i j) P := by
    intro i j
    simpa [M, blockMatEntry] using hEntry (Sum.inr i) (Sum.inl j)
  have hUL : ∀ i j, Integrable (fun a : CoeffField d => (M a).upperLeft i j) P := by
    intro i j
    simpa [M, blockMatEntry] using hEntry (Sum.inl i) (Sum.inl j)
  have hTermLR :
      Integrable (fun a : CoeffField d => vecDot q (matVecMul (M a).lowerRight q)) P := by
    simp [vecDot, matVecMul]
    exact MeasureTheory.integrable_finset_sum Finset.univ fun i _ =>
      (MeasureTheory.integrable_finset_sum Finset.univ fun j _ =>
        (hLR i j).mul_const (q j)).const_mul (q i)
  have hTermLL :
      Integrable (fun a : CoeffField d => vecDot q (matVecMul (M a).lowerLeft p)) P := by
    simp [vecDot, matVecMul]
    exact MeasureTheory.integrable_finset_sum Finset.univ fun i _ =>
      (MeasureTheory.integrable_finset_sum Finset.univ fun j _ =>
        (hLL i j).mul_const (p j)).const_mul (q i)
  have hTermUL :
      Integrable (fun a : CoeffField d => vecDot p (matVecMul (M a).upperLeft p)) P := by
    simp [vecDot, matVecMul]
    exact MeasureTheory.integrable_finset_sum Finset.univ fun i _ =>
      (MeasureTheory.integrable_finset_sum Finset.univ fun j _ =>
        (hUL i j).mul_const (p j)).const_mul (p i)
  have hFormula :
      (fun a : CoeffField d => responseJObservableCubeSet Q p q a) =ᵐ[P]
        (fun a : CoeffField d =>
          (1 / 2 : ℝ) * vecDot q (matVecMul (M a).lowerRight q) -
            vecDot p q -
            vecDot q (matVecMul (M a).lowerLeft p) +
            (1 / 2 : ℝ) * vecDot p (matVecMul (M a).upperLeft p)) := by
    filter_upwards [hData] with a ha
    calc
      responseJObservableCubeSet Q p q a = ResponseJ (cubeSet Q) p q a := rfl
      _ = ResponseJ (openCubeSet Q) p q a :=
        responseJ_cubeSet_eq_openCubeSet_of_triadicCube Q p q a
      _ =
        (1 / 2 : ℝ) *
            vecDot q (matVecMul (coarseBlockMatrix (openCubeSet Q) a).lowerRight q) -
          vecDot p q -
          vecDot q (matVecMul (coarseBlockMatrix (openCubeSet Q) a).lowerLeft p) +
          (1 / 2 : ℝ) *
            vecDot p (matVecMul (coarseBlockMatrix (openCubeSet Q) a).upperLeft p) :=
        responseJ_formula_coarseBlockMatrix_openCubeSet_of_deterministicCoarseData ha p q
      _ =
        (1 / 2 : ℝ) * vecDot q (matVecMul (M a).lowerRight q) -
          vecDot p q -
          vecDot q (matVecMul (M a).lowerLeft p) +
          (1 / 2 : ℝ) * vecDot p (matVecMul (M a).upperLeft p) := by
        rw [← coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q a]
  have hLRint := integral_vecDot_matVecMul_eq_entrywise_integral (P := P) hLR q q
  have hLLint := integral_vecDot_matVecMul_eq_entrywise_integral (P := P) hLL q p
  have hULint := integral_vecDot_matVecMul_eq_entrywise_integral (P := P) hUL p p
  calc
    ∫ a, responseJObservableCubeSet Q p q a ∂P
        =
      ∫ a,
        (1 / 2 : ℝ) * vecDot q (matVecMul (M a).lowerRight q) -
          vecDot p q -
          vecDot q (matVecMul (M a).lowerLeft p) +
          (1 / 2 : ℝ) * vecDot p (matVecMul (M a).upperLeft p) ∂P :=
        integral_congr_ae hFormula
    _ =
      (1 / 2 : ℝ) * ∫ a, vecDot q (matVecMul (M a).lowerRight q) ∂P -
        vecDot p q -
        ∫ a, vecDot q (matVecMul (M a).lowerLeft p) ∂P +
        (1 / 2 : ℝ) * ∫ a, vecDot p (matVecMul (M a).upperLeft p) ∂P := by
        rw [integral_add]
        · rw [integral_sub]
          · rw [integral_sub]
            · rw [integral_const_mul]
              rw [integral_const]
              rw [integral_const_mul]
              simp [Measure.real, IsProbabilityMeasure.measure_univ]
            · exact hTermLR.const_mul (1 / 2 : ℝ)
            · exact integrable_const _
          · exact (hTermLR.const_mul (1 / 2 : ℝ)).sub (integrable_const _)
          · exact hTermLL
        · exact ((hTermLR.const_mul (1 / 2 : ℝ)).sub (integrable_const _)).sub hTermLL
        · exact hTermUL.const_mul (1 / 2 : ℝ)
    _ =
      (1 / 2 : ℝ) * vecDot q (matVecMul (annealedBlockMatrix P (cubeSet Q)).lowerRight q) -
        vecDot p q -
        vecDot q (matVecMul (annealedBlockMatrix P (cubeSet Q)).lowerLeft p) +
        (1 / 2 : ℝ) * vecDot p (matVecMul (annealedBlockMatrix P (cubeSet Q)).upperLeft p) := by
        rw [hLRint, hLLint, hULint]
        rfl

/-- Annealed finite descendant average of scalar responses. -/
noncomputable def expectedDescendantsAverageResponseJCubeSet {d : ℕ}
    (P : CoeffLaw d) (Q : TriadicCube d) (j : ℕ) (p q : Vec d) : ℝ :=
  descendantsAverage Q j (fun R => expectedResponseJCubeSet P R p q)

/-- Difference of two annealed scalar responses, the basic `τ`-type quantity. -/
noncomputable def tauResponseJCubeSet {d : ℕ}
    (P : CoeffLaw d) (Qchild Qparent : TriadicCube d) (p q : Vec d) : ℝ :=
  expectedResponseJCubeSet P Qchild p q - expectedResponseJCubeSet P Qparent p q

/-- Finite descendant averages preserve integrability. -/
theorem integrable_descendantsAverage
    {d : ℕ} {P : CoeffLaw d} {Q : TriadicCube d} {j : ℕ}
    {F : TriadicCube d → CoeffField d → ℝ}
    (hF : ∀ R, R ∈ descendantsAtDepth Q j → Integrable (F R) P) :
    Integrable
      (fun a : CoeffField d => descendantsAverage Q j (fun R => F R a)) P := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hsum :
      Integrable (fun a : CoeffField d => ∑ R ∈ D, F R a) P := by
    exact MeasureTheory.integrable_finset_sum D
      (fun R hR => hF R (by simpa [D] using hR))
  simpa [descendantsAverage, D] using hsum.const_mul ((D.card : ℝ)⁻¹)

/-- Finite descendant averages commute with expectation under childwise
integrability. -/
theorem integral_descendantsAverage_eq_descendantsAverage_integral
    {d : ℕ} {P : CoeffLaw d} {Q : TriadicCube d} {j : ℕ}
    {F : TriadicCube d → CoeffField d → ℝ}
    (hF : ∀ R, R ∈ descendantsAtDepth Q j → Integrable (F R) P) :
    ∫ a, descendantsAverage Q j (fun R => F R a) ∂P =
      descendantsAverage Q j (fun R => ∫ a, F R a ∂P) := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  calc
    ∫ a, descendantsAverage Q j (fun R => F R a) ∂P
        =
      ∫ a,
        (D.card : ℝ)⁻¹ * (∑ R ∈ D, F R a) ∂P := by
          rfl
    _ =
      (D.card : ℝ)⁻¹ *
        ∫ a, ∑ R ∈ D, F R a ∂P := by
          rw [integral_const_mul]
    _ =
      (D.card : ℝ)⁻¹ *
        (∑ R ∈ D, ∫ a, F R a ∂P) := by
          rw [MeasureTheory.integral_finset_sum D
            (fun R hR => hF R (by simpa [D] using hR))]
    _ = descendantsAverage Q j (fun R => ∫ a, F R a ∂P) := by
          simp [descendantsAverage, D]

/-- Finite descendant averages preserve `MemLp`. -/
theorem memLp_descendantsAverage
    {d : ℕ} {P : CoeffLaw d} {Q : TriadicCube d} {j : ℕ} {r : ℝ≥0∞}
    {F : TriadicCube d → CoeffField d → ℝ}
    (hF : ∀ R, R ∈ descendantsAtDepth Q j → MemLp (F R) r P) :
    MemLp
      (fun a : CoeffField d => descendantsAverage Q j (fun R => F R a)) r P := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hsum :
      MemLp (fun a : CoeffField d => ∑ R ∈ D, F R a) r P := by
    exact MeasureTheory.memLp_finset_sum D
      (fun R hR => hF R (by simpa [D] using hR))
  simpa [descendantsAverage, D] using hsum.const_mul ((D.card : ℝ)⁻¹)

/-- Finite descendant averages of response observables are integrable if the
child responses are integrable. -/
theorem integrable_descendantsAverage_responseJObservableCubeSet
    {d : ℕ} {P : CoeffLaw d} {Q : TriadicCube d} {j : ℕ} {p q : Vec d}
    (hJ : ∀ R, R ∈ descendantsAtDepth Q j →
      Integrable (responseJObservableCubeSet R p q) P) :
    Integrable
      (fun a : CoeffField d =>
        descendantsAverage Q j (fun R => responseJObservableCubeSet R p q a)) P :=
  integrable_descendantsAverage
    (P := P) (Q := Q) (j := j)
    (F := fun R a => responseJObservableCubeSet R p q a) hJ

/-- Finite descendant averages of response observables are in `L^r` if the
child responses are in `L^r`. -/
theorem memLp_descendantsAverage_responseJObservableCubeSet
    {d : ℕ} {P : CoeffLaw d} {Q : TriadicCube d} {j : ℕ} {r : ℝ≥0∞}
    {p q : Vec d}
    (hJ : ∀ R, R ∈ descendantsAtDepth Q j →
      MemLp (responseJObservableCubeSet R p q) r P) :
    MemLp
      (fun a : CoeffField d =>
        descendantsAverage Q j (fun R => responseJObservableCubeSet R p q a)) r P :=
  memLp_descendantsAverage
    (P := P) (Q := Q) (j := j) (r := r)
    (F := fun R a => responseJObservableCubeSet R p q a) hJ

/-- Centering by a deterministic scalar preserves integrability. -/
theorem integrable_centeredResponseJObservableCubeSet
    {d : ℕ} {P : CoeffLaw d} [IsFiniteMeasure P]
    (Q : TriadicCube d) (p q p0 q0 : Vec d)
    (hJ : Integrable (responseJObservableCubeSet Q p q) P) :
    Integrable (centeredResponseJObservableCubeSet Q p q p0 q0) P := by
  simpa [centeredResponseJObservableCubeSet] using hJ.sub (integrable_const _)

/-- Centering by a deterministic scalar preserves `MemLp` under a finite
measure. -/
theorem memLp_centeredResponseJObservableCubeSet
    {d : ℕ} {P : CoeffLaw d} {r : ℝ≥0∞} [IsFiniteMeasure P]
    (Q : TriadicCube d) (p q p0 q0 : Vec d)
    (hJ : MemLp (responseJObservableCubeSet Q p q) r P) :
    MemLp (centeredResponseJObservableCubeSet Q p q p0 q0) r P := by
  convert
    hJ.sub
      (MeasureTheory.memLp_const
        (μ := P) (p := r) (c := (1 / 2 : ℝ) * vecDot p0 q0)) using 1

/-- The integral of the centered response is the annealed response minus the
deterministic centering scalar. -/
theorem integral_centeredResponseJObservableCubeSet_eq_expectedResponseJCubeSet_sub_half_dot
    {d : ℕ} {P : CoeffLaw d} [IsProbabilityMeasure P]
    (Q : TriadicCube d) (p q p0 q0 : Vec d)
    (hJ : Integrable (responseJObservableCubeSet Q p q) P) :
    ∫ a, centeredResponseJObservableCubeSet Q p q p0 q0 a ∂P =
      expectedResponseJCubeSet P Q p q - (1 / 2 : ℝ) * vecDot p0 q0 := by
  have hConst :
      Integrable (fun _ : CoeffField d => (1 / 2 : ℝ) * vecDot p0 q0) P :=
    integrable_const _
  calc
    ∫ a, centeredResponseJObservableCubeSet Q p q p0 q0 a ∂P
        = ∫ a,
            responseJObservableCubeSet Q p q a -
              (1 / 2 : ℝ) * vecDot p0 q0 ∂P := by
          rfl
    _ = ∫ a, responseJObservableCubeSet Q p q a ∂P -
          ∫ _a : CoeffField d, (1 / 2 : ℝ) * vecDot p0 q0 ∂P := by
          rw [integral_sub hJ hConst]
    _ = expectedResponseJCubeSet P Q p q - (1 / 2 : ℝ) * vecDot p0 q0 := by
          rw [integral_const]
          simp [expectedResponseJCubeSet, Measure.real, IsProbabilityMeasure.measure_univ]

/-- Finite descendant response averages commute with expectation, assuming
childwise integrability. -/
theorem integral_descendantsAverage_responseJObservableCubeSet_eq_expectedDescendantsAverageResponseJCubeSet
    {d : ℕ} {P : CoeffLaw d}
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d)
    (hJ : ∀ R, R ∈ descendantsAtDepth Q j →
      Integrable (responseJObservableCubeSet R p q) P) :
    ∫ a,
        descendantsAverage Q j (fun R => responseJObservableCubeSet R p q a) ∂P =
      expectedDescendantsAverageResponseJCubeSet P Q j p q := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  calc
    ∫ a,
        descendantsAverage Q j (fun R => responseJObservableCubeSet R p q a) ∂P
        =
      ∫ a,
        (D.card : ℝ)⁻¹ *
          (∑ R ∈ D, responseJObservableCubeSet R p q a) ∂P := by
          rfl
    _ =
      (D.card : ℝ)⁻¹ *
        ∫ a, ∑ R ∈ D, responseJObservableCubeSet R p q a ∂P := by
          rw [integral_const_mul]
    _ =
      (D.card : ℝ)⁻¹ *
        (∑ R ∈ D, ∫ a, responseJObservableCubeSet R p q a ∂P) := by
          rw [MeasureTheory.integral_finset_sum D
            (fun R hR => hJ R (by simpa [D] using hR))]
    _ = expectedDescendantsAverageResponseJCubeSet P Q j p q := by
          simp [expectedDescendantsAverageResponseJCubeSet, expectedResponseJCubeSet,
            descendantsAverage, D]

namespace LawCarrier

/-- The named response observable is a.e.-measurable under a law carrier. -/
theorem aemeasurable_responseJObservableCubeSet
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (p q : Vec d) :
    AEMeasurable (responseJObservableCubeSet Q p q) P := by
  simpa [responseJObservableCubeSet] using hP.aemeasurable_ResponseJ_cubeSet Q p q

/-- The named response observable is a.e.-strongly-measurable under a law
carrier. -/
theorem aestronglyMeasurable_responseJObservableCubeSet
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (p q : Vec d) :
    AEStronglyMeasurable (responseJObservableCubeSet Q p q) P :=
  (hP.aemeasurable_responseJObservableCubeSet Q p q).aestronglyMeasurable

/-- Centered response observables are a.e.-measurable under a law carrier. -/
theorem aemeasurable_centeredResponseJObservableCubeSet
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (p q p0 q0 : Vec d) :
    AEMeasurable (centeredResponseJObservableCubeSet Q p q p0 q0) P := by
  simpa [centeredResponseJObservableCubeSet] using
    (hP.aemeasurable_responseJObservableCubeSet Q p q).sub aemeasurable_const

/-- Centered response observables are a.e.-strongly-measurable under a law
carrier. -/
theorem aestronglyMeasurable_centeredResponseJObservableCubeSet
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (p q p0 q0 : Vec d) :
    AEStronglyMeasurable (centeredResponseJObservableCubeSet Q p q p0 q0) P :=
  (hP.aemeasurable_centeredResponseJObservableCubeSet Q p q p0 q0).aestronglyMeasurable

/-- Finite descendant averages of the named response observables are
a.e.-measurable under a law carrier. -/
theorem aemeasurable_descendantsAverage_responseJObservableCubeSet
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    AEMeasurable
      (fun a : CoeffField d =>
        descendantsAverage Q j (fun R => responseJObservableCubeSet R p q a)) P := by
  simpa [responseJObservableCubeSet] using
    hP.aemeasurable_descendantsAverage_ResponseJ_cubeSet Q j p q

/-- Finite descendant averages of the named response observables are
a.e.-strongly-measurable under a law carrier. -/
theorem aestronglyMeasurable_descendantsAverage_responseJObservableCubeSet
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    AEStronglyMeasurable
      (fun a : CoeffField d =>
        descendantsAverage Q j (fun R => responseJObservableCubeSet R p q a)) P :=
  (hP.aemeasurable_descendantsAverage_responseJObservableCubeSet Q j p q).aestronglyMeasurable

end LawCarrier

end

end Ch04
end Book
end Homogenization
