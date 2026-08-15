import Mathlib
import Homogenization.Examples.RandomCheckerboard.CarrierLaw
import Audit.CheckerboardScale.SolutionBasic

attribute [-instance] Homogenization.instMeasurableSpaceVec
attribute [-instance] Homogenization.instMeasurableSpaceMat
attribute [-instance] Homogenization.instMeasurableSpaceCoeffField

/-!
# Solution for the checkerboard homogenization-scale challenge

This file is the comparator solution surface for the Bernoulli-checkerboard
instantiation of the unconditional homogenization-scale capstone
`Homogenization.homogenizationScale_polynomial_of_unitRange`
(`Homogenization/HighContrast/Scale/Final.lean`, applied to the checkerboard
law of `Homogenization/Examples/RandomCheckerboard/CarrierLaw.lean`).

The corresponding challenge imports only Mathlib.  This solution imports the
repository theorem surface, together with the shared statement vocabulary of
`Audit.CheckerboardScale.SolutionBasic`, and proves the same
`StatementAudit.CheckerboardScale` theorem surface.

The audited theorem carries the explicit dimension restriction `hd : 3 ≤ d`
(`d > 2`); the capstone's ellipticity parameter is instantiated at `Θ = Lam`,
in whose quadratic-form ellipticity class `IsEllipticMatrix 1 Lam`
(coercivity together with the inverse quadratic-form bound; the fields are
general non-symmetric matrices) the checkerboard realizations lie, so the
polynomial entry-scale bound reads `3^{N₀} ≤ (2 + Lam)^Ctriadic` — an
explicit algebraic dependence on the contrast.

The private bridges below transport the audit vocabulary to the repository
vocabulary:

* the carrier bridge (`toRepoReg`/`ofRepoReg` and the measurable equivalence
  `regEquiv`) transports laws along the identity on the underlying data;
* the `H1Function`/`H10Function` record bridges transport the Sobolev
  witnesses inside the potential/solenoidal trace predicates;
* the block-state bridge transports the `Mu` admissible class, giving
  `muValueSet`/`Mu` equality, hence equality of the polarized coarse block
  matrices, of the annealed matrices, and finally of the scalar contrast;
* the law identification (`law_eq_map_ofRepoReg`) recognizes the audit
  checkerboard law as the transported repository checkerboard law, so the
  repository's contrast selector for the checkerboard agrees with the
  audit's total `(0,0)`-entry mirror `PolynomialScale.thetaAtScale`.

The final theorem is exactly the repository capstone applied to the
checkerboard witnesses `lawCarrier`, `structuralLaw`, and
`thetaEllipticLaw` (with `Θ = Lam`), composed with these bridges — the
comparator-facing form of the repository's satisfiability regression guard.
-/

namespace Homogenization
namespace StatementAudit

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

/-! ## Solution-only bridges to the repository theorem -/

/-! ### Carrier bridge

The audit carrier `RegCoeffField` is a statement-level copy of the repository
carrier `Homogenization.RegCoeffField`, with the same underlying data and the
same generating families for the σ-algebra (pointwise lane and entry-test
lane).  The identity on the underlying data is therefore a measurable
equivalence between the two carriers; laws and almost-everywhere statements
transport along it. -/

private def toRepoReg {d : ℕ} (a : RegCoeffField d) :
    _root_.Homogenization.RegCoeffField d where
  toFun := a.toFun
  entry_measurable := a.entry_measurable
  entry_locInt := a.entry_locInt

private def ofRepoReg {d : ℕ} (a : _root_.Homogenization.RegCoeffField d) :
    RegCoeffField d where
  toFun := a.toFun
  entry_measurable := a.entry_measurable
  entry_locInt := a.entry_locInt

@[simp] private theorem toRepoReg_toFun {d : ℕ} (a : RegCoeffField d) :
    (toRepoReg a).toFun = a.toFun := rfl

@[simp] private theorem ofRepoReg_toFun {d : ℕ}
    (a : _root_.Homogenization.RegCoeffField d) :
    (ofRepoReg a).toFun = a.toFun := rfl

@[simp] private theorem toRepoReg_ofRepoReg {d : ℕ}
    (a : _root_.Homogenization.RegCoeffField d) :
    toRepoReg (ofRepoReg a) = a := rfl

@[simp] private theorem ofRepoReg_toRepoReg {d : ℕ} (a : RegCoeffField d) :
    ofRepoReg (toRepoReg a) = a := rfl

private theorem isProbeR_toRepo {d : ℕ} {φ : Vec d → ℝ} (h : IsProbeR φ) :
    _root_.Homogenization.IsProbeR φ :=
  ⟨h.measurable, h.bounded, h.hasCompactSupport⟩

private theorem isProbeR_ofRepo {d : ℕ} {φ : Vec d → ℝ}
    (h : _root_.Homogenization.IsProbeR (d := d) φ) : IsProbeR φ :=
  ⟨h.measurable, h.bounded, h.hasCompactSupport⟩

private theorem measurable_into_sup_audit {α β : Type*} {dom : MeasurableSpace α}
    {m1 m2 : MeasurableSpace β} {f : α → β}
    (h1 : @Measurable α β dom m1 f) (h2 : @Measurable α β dom m2 f) :
    @Measurable α β dom (m1 ⊔ m2) f := by
  rw [measurable_iff_comap_le, MeasurableSpace.comap_sup]
  exact sup_le h1.comap_le h2.comap_le

private theorem measurable_auditToFun {d : ℕ} :
    @Measurable (RegCoeffField d) (Vec d → Mat d) _
      (pointwiseCoeffFieldMeasurableSpace d) RegCoeffField.toFun := by
  have h : @Measurable (RegCoeffField d) (Vec d → Mat d) (pointwiseSigmaR d)
      (pointwiseCoeffFieldMeasurableSpace d) RegCoeffField.toFun :=
    Measurable.of_comap_le le_rfl
  exact h.mono le_sup_left le_rfl

private theorem measurable_apply_entry_audit {d : ℕ} (y : Vec d) (i j : Fin d) :
    Measurable (fun a : RegCoeffField d => a.toFun y i j) := by
  have h1 : @Measurable (Vec d → Mat d) (Mat d) (pointwiseCoeffFieldMeasurableSpace d)
      (instMeasurableSpaceMat d) (fun f => f y) := measurable_pi_apply y
  have h3 : @Measurable (Mat d) (Fin d → ℝ) (instMeasurableSpaceMat d)
      MeasurableSpace.pi (fun A => A i) := measurable_pi_apply i
  have h2 : @Measurable (Mat d) ℝ (instMeasurableSpaceMat d) _ (fun A => A i j) :=
    (measurable_pi_apply j).comp h3
  exact (h2.comp h1).comp measurable_auditToFun

private theorem measurable_entryTestR_audit {d : ℕ} (i j : Fin d) {φ : Vec d → ℝ}
    (hφ : IsProbeR φ) : Measurable (entryTestR i j φ) := by
  have h : @Measurable (RegCoeffField d) ℝ (entryTestSigmaR d) _ (entryTestR i j φ) := by
    intro t ht
    exact MeasurableSpace.measurableSet_generateFrom ⟨i, j, φ, hφ, t, ht, rfl⟩
  exact h.mono le_sup_right le_rfl

private theorem measurable_toRepoReg {d : ℕ} : Measurable (toRepoReg (d := d)) := by
  refine _root_.Homogenization.measurable_into_regCoeffField' ?_ ?_
  · intro y i j
    exact measurable_apply_entry_audit y i j
  · intro i j φ hφ
    exact measurable_entryTestR_audit i j (isProbeR_ofRepo hφ)

private theorem measurable_ofRepoReg {d : ℕ} : Measurable (ofRepoReg (d := d)) := by
  refine measurable_into_sup_audit ?_ ?_
  · rw [measurable_iff_comap_le, pointwiseSigmaR, MeasurableSpace.comap_comp]
    exact _root_.Homogenization.pointwiseSigmaR_le d
  · refine measurable_generateFrom ?_
    rintro s ⟨i, j, φ, hφ, t, ht, rfl⟩
    exact _root_.Homogenization.measurable_entryTestR i j (isProbeR_toRepo hφ) ht

/-- The audit carrier and the repository carrier are measurably equivalent via
the identity on the underlying data. -/
private def regEquiv (d : ℕ) :
    _root_.Homogenization.RegCoeffField d ≃ᵐ RegCoeffField d where
  toEquiv :=
    { toFun := ofRepoReg
      invFun := toRepoReg
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  measurable_toFun := measurable_ofRepoReg
  measurable_invFun := measurable_toRepoReg

private def toRepoH1Function {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) : _root_.Homogenization.H1Function U where
  toFun := u.toFun
  grad := u.grad
  memL2 := by
    simpa [MemL2On, _root_.Homogenization.MemL2On] using u.memL2
  gradMemL2 := by
    simpa [GradMemL2On, _root_.Homogenization.GradMemL2On,
      MemL2On, _root_.Homogenization.MemL2On] using u.gradMemL2
  hasWeakGradient := by
    simpa [HasWeakGradientOn, _root_.Homogenization.HasWeakGradientOn,
      HasWeakPartialDerivOn, _root_.Homogenization.HasWeakPartialDerivOn,
      basisVec, _root_.Homogenization.basisVec] using u.hasWeakGradient

private def ofRepoH1Function {d : ℕ} {U : Set (Vec d)}
    (u : _root_.Homogenization.H1Function U) : H1Function U where
  toFun := u.toFun
  grad := u.grad
  memL2 := by
    simpa [MemL2On, _root_.Homogenization.MemL2On] using u.memL2
  gradMemL2 := by
    simpa [GradMemL2On, _root_.Homogenization.GradMemL2On,
      MemL2On, _root_.Homogenization.MemL2On] using u.gradMemL2
  hasWeakGradient := by
    simpa [HasWeakGradientOn, _root_.Homogenization.HasWeakGradientOn,
      HasWeakPartialDerivOn, _root_.Homogenization.HasWeakPartialDerivOn,
      basisVec, _root_.Homogenization.basisVec] using u.hasWeakGradient

private def toRepoH10Function {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) : _root_.Homogenization.H10Function U where
  toH1Function := toRepoH1Function u.toH1Function
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_hasCompactSupport := u.approx_hasCompactSupport
  approx_support_subset := u.approx_support_subset
  tendsto_approx := by
    simpa [toRepoH1Function] using u.tendsto_approx
  tendsto_approx_grad := by
    intro i
    simpa [toRepoH1Function, basisVec, _root_.Homogenization.basisVec] using
      u.tendsto_approx_grad i

private def ofRepoH10Function {d : ℕ} {U : Set (Vec d)}
    (u : _root_.Homogenization.H10Function U) : H10Function U where
  toH1Function := ofRepoH1Function u.toH1Function
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_hasCompactSupport := u.approx_hasCompactSupport
  approx_support_subset := u.approx_support_subset
  tendsto_approx := by
    simpa [ofRepoH1Function] using u.tendsto_approx
  tendsto_approx_grad := by
    intro i
    simpa [ofRepoH1Function, basisVec, _root_.Homogenization.basisVec] using
      u.tendsto_approx_grad i

/-! ## Bridges for the block formalism, `Mu`, and the contrast selector -/

namespace PolynomialScale

private def toRepoBlockState {d : ℕ} (X : BlockState d) :
    _root_.Homogenization.BlockState d where
  potential := X.potential
  flux := X.flux

private def ofRepoBlockState {d : ℕ} (X : _root_.Homogenization.BlockState d) :
    BlockState d where
  potential := X.potential
  flux := X.flux

/-! ### Bridge B1 — `Mu`: transport of the admissible class

The audit `BlockState`/`H1Function`/`H10Function` records are statement-level
copies of the repository records over the definitionally equal ambient types,
so the admissibility conjuncts transport along the evident record maps and the
two `muValueSet`s coincide; `Mu` equality follows by `sInf` congruence. -/

private theorem toRepo_isPotentialZeroTraceOn {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → Vec d} (h : IsPotentialZeroTraceOn U f) :
    _root_.Homogenization.IsPotentialZeroTraceOn U f := by
  rcases h with ⟨u, hu⟩
  exact ⟨toRepoH10Function u, hu⟩

private theorem ofRepo_isPotentialZeroTraceOn {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → Vec d} (h : _root_.Homogenization.IsPotentialZeroTraceOn U f) :
    IsPotentialZeroTraceOn U f := by
  rcases h with ⟨u, hu⟩
  exact ⟨ofRepoH10Function u, hu⟩

private theorem toRepo_isSolenoidalZeroNormalTraceOn {d : ℕ} {U : Set (Vec d)}
    {g : Vec d → Vec d} (h : IsSolenoidalZeroNormalTraceOn U g) :
    _root_.Homogenization.IsSolenoidalZeroNormalTraceOn U g := by
  intro φ
  exact h (ofRepoH1Function φ)

private theorem ofRepo_isSolenoidalZeroNormalTraceOn {d : ℕ} {U : Set (Vec d)}
    {g : Vec d → Vec d}
    (h : _root_.Homogenization.IsSolenoidalZeroNormalTraceOn U g) :
    IsSolenoidalZeroNormalTraceOn U g := by
  intro φ
  exact h (toRepoH1Function φ)

private theorem toRepo_isBlockMuAdmissible {d : ℕ} {U : Set (Vec d)}
    {P : BlockVec d} {X : BlockState d} (h : IsBlockMuAdmissible U P X) :
    _root_.Homogenization.IsBlockMuAdmissible U P (toRepoBlockState X) :=
  ⟨h.1, toRepo_isPotentialZeroTraceOn h.2.1, h.2.2.1,
    toRepo_isSolenoidalZeroNormalTraceOn h.2.2.2⟩

private theorem ofRepo_isBlockMuAdmissible {d : ℕ} {U : Set (Vec d)}
    {P : BlockVec d} {X : _root_.Homogenization.BlockState d}
    (h : _root_.Homogenization.IsBlockMuAdmissible U P X) :
    IsBlockMuAdmissible U P (ofRepoBlockState X) :=
  ⟨h.1, ofRepo_isPotentialZeroTraceOn h.2.1, h.2.2.1,
    ofRepo_isSolenoidalZeroNormalTraceOn h.2.2.2⟩

private theorem muValueSet_toRepo {d : ℕ} (U : Set (Vec d)) (P : BlockVec d)
    (a : CoeffField d) :
    muValueSet U P a = _root_.Homogenization.muValueSet U P a := by
  ext m
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact ⟨toRepoBlockState X, toRepo_isBlockMuAdmissible hX, rfl⟩
  · rintro ⟨X, hX, rfl⟩
    exact ⟨ofRepoBlockState X, ofRepo_isBlockMuAdmissible hX, rfl⟩

private theorem mu_toRepo {d : ℕ} (U : Set (Vec d)) (P : BlockVec d)
    (a : CoeffField d) :
    Mu U P a = _root_.Homogenization.Mu U P a := by
  unfold Mu _root_.Homogenization.Mu
  rw [muValueSet_toRepo]

/-! ### Bridge B2 — the coarse block matrix: polarization through the
repository's private entry selector, which is definitionally transparent. -/

private theorem coarseBlockEntry_toRepo {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) (α β : BlockCoord d) :
    coarseBlockEntry U a α β =
      if _h : α = β then
        2 * _root_.Homogenization.Mu U (blockBasis α) a
      else
        _root_.Homogenization.Mu U (blockBasis α + blockBasis β) a
          - _root_.Homogenization.Mu U (blockBasis α) a
          - _root_.Homogenization.Mu U (blockBasis β) a := by
  unfold coarseBlockEntry
  by_cases h : α = β
  · rw [dif_pos h, dif_pos h, mu_toRepo]
  · rw [dif_neg h, dif_neg h, mu_toRepo, mu_toRepo, mu_toRepo]

private theorem coarseBlockMatrix_upperLeft_toRepo {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) (i j : Fin d) :
    (coarseBlockMatrix U a).upperLeft i j =
      (_root_.Homogenization.coarseBlockMatrix U a).upperLeft i j := by
  have hrepo :
      (_root_.Homogenization.coarseBlockMatrix U a).upperLeft i j =
        (if _h : (Sum.inl i : BlockCoord d) = Sum.inl j then
          2 * _root_.Homogenization.Mu U (blockBasis (Sum.inl i)) a
        else
          _root_.Homogenization.Mu U
              (blockBasis (Sum.inl i) + blockBasis (Sum.inl j)) a
            - _root_.Homogenization.Mu U (blockBasis (Sum.inl i)) a
            - _root_.Homogenization.Mu U (blockBasis (Sum.inl j)) a) := rfl
  rw [hrepo]
  exact coarseBlockEntry_toRepo U a (Sum.inl i) (Sum.inl j)

private theorem coarseBlockMatrix_upperRight_toRepo {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) (i j : Fin d) :
    (coarseBlockMatrix U a).upperRight i j =
      (_root_.Homogenization.coarseBlockMatrix U a).upperRight i j := by
  have hrepo :
      (_root_.Homogenization.coarseBlockMatrix U a).upperRight i j =
        (if _h : (Sum.inl i : BlockCoord d) = Sum.inr j then
          2 * _root_.Homogenization.Mu U (blockBasis (Sum.inl i)) a
        else
          _root_.Homogenization.Mu U
              (blockBasis (Sum.inl i) + blockBasis (Sum.inr j)) a
            - _root_.Homogenization.Mu U (blockBasis (Sum.inl i)) a
            - _root_.Homogenization.Mu U (blockBasis (Sum.inr j)) a) := rfl
  rw [hrepo]
  exact coarseBlockEntry_toRepo U a (Sum.inl i) (Sum.inr j)

private theorem coarseBlockMatrix_lowerLeft_toRepo {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) (i j : Fin d) :
    (coarseBlockMatrix U a).lowerLeft i j =
      (_root_.Homogenization.coarseBlockMatrix U a).lowerLeft i j := by
  have hrepo :
      (_root_.Homogenization.coarseBlockMatrix U a).lowerLeft i j =
        (if _h : (Sum.inr i : BlockCoord d) = Sum.inl j then
          2 * _root_.Homogenization.Mu U (blockBasis (Sum.inr i)) a
        else
          _root_.Homogenization.Mu U
              (blockBasis (Sum.inr i) + blockBasis (Sum.inl j)) a
            - _root_.Homogenization.Mu U (blockBasis (Sum.inr i)) a
            - _root_.Homogenization.Mu U (blockBasis (Sum.inl j)) a) := rfl
  rw [hrepo]
  exact coarseBlockEntry_toRepo U a (Sum.inr i) (Sum.inl j)

private theorem coarseBlockMatrix_lowerRight_toRepo {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) (i j : Fin d) :
    (coarseBlockMatrix U a).lowerRight i j =
      (_root_.Homogenization.coarseBlockMatrix U a).lowerRight i j := by
  have hrepo :
      (_root_.Homogenization.coarseBlockMatrix U a).lowerRight i j =
        (if _h : (Sum.inr i : BlockCoord d) = Sum.inr j then
          2 * _root_.Homogenization.Mu U (blockBasis (Sum.inr i)) a
        else
          _root_.Homogenization.Mu U
              (blockBasis (Sum.inr i) + blockBasis (Sum.inr j)) a
            - _root_.Homogenization.Mu U (blockBasis (Sum.inr i)) a
            - _root_.Homogenization.Mu U (blockBasis (Sum.inr j)) a) := rfl
  rw [hrepo]
  exact coarseBlockEntry_toRepo U a (Sum.inr i) (Sum.inr j)

/-! ### Bridge B3 — annealed matrices: the annealed integrals transport along
the carrier equivalence `regEquiv`, and the matrix algebra is congruent. -/

private theorem annealedBlockMatrix_upperLeft_toRepo {d : ℕ} (P : RestrictionCoeffLaw d)
    (U : Set (Vec d)) :
    (annealedBlockMatrix P U).upperLeft =
      (_root_.Homogenization.Book.Ch04.annealedBlockMatrix
        (Measure.map (toRepoReg (d := d)) P) U).upperLeft := by
  funext i j
  show (∫ a, (coarseBlockMatrix U a.toFun).upperLeft i j ∂P) =
    ∫ b, (_root_.Homogenization.coarseBlockMatrix U b.toFun).upperLeft i j
      ∂(Measure.map (toRepoReg (d := d)) P)
  rw [show Measure.map (toRepoReg (d := d)) P
      = Measure.map ((regEquiv d).symm) P from rfl,
    MeasureTheory.integral_map_equiv]
  congr 1
  funext a
  exact coarseBlockMatrix_upperLeft_toRepo U a.toFun i j

private theorem annealedBlockMatrix_upperRight_toRepo {d : ℕ} (P : RestrictionCoeffLaw d)
    (U : Set (Vec d)) :
    (annealedBlockMatrix P U).upperRight =
      (_root_.Homogenization.Book.Ch04.annealedBlockMatrix
        (Measure.map (toRepoReg (d := d)) P) U).upperRight := by
  funext i j
  show (∫ a, (coarseBlockMatrix U a.toFun).upperRight i j ∂P) =
    ∫ b, (_root_.Homogenization.coarseBlockMatrix U b.toFun).upperRight i j
      ∂(Measure.map (toRepoReg (d := d)) P)
  rw [show Measure.map (toRepoReg (d := d)) P
      = Measure.map ((regEquiv d).symm) P from rfl,
    MeasureTheory.integral_map_equiv]
  congr 1
  funext a
  exact coarseBlockMatrix_upperRight_toRepo U a.toFun i j

private theorem annealedBlockMatrix_lowerLeft_toRepo {d : ℕ} (P : RestrictionCoeffLaw d)
    (U : Set (Vec d)) :
    (annealedBlockMatrix P U).lowerLeft =
      (_root_.Homogenization.Book.Ch04.annealedBlockMatrix
        (Measure.map (toRepoReg (d := d)) P) U).lowerLeft := by
  funext i j
  show (∫ a, (coarseBlockMatrix U a.toFun).lowerLeft i j ∂P) =
    ∫ b, (_root_.Homogenization.coarseBlockMatrix U b.toFun).lowerLeft i j
      ∂(Measure.map (toRepoReg (d := d)) P)
  rw [show Measure.map (toRepoReg (d := d)) P
      = Measure.map ((regEquiv d).symm) P from rfl,
    MeasureTheory.integral_map_equiv]
  congr 1
  funext a
  exact coarseBlockMatrix_lowerLeft_toRepo U a.toFun i j

private theorem annealedBlockMatrix_lowerRight_toRepo {d : ℕ} (P : RestrictionCoeffLaw d)
    (U : Set (Vec d)) :
    (annealedBlockMatrix P U).lowerRight =
      (_root_.Homogenization.Book.Ch04.annealedBlockMatrix
        (Measure.map (toRepoReg (d := d)) P) U).lowerRight := by
  funext i j
  show (∫ a, (coarseBlockMatrix U a.toFun).lowerRight i j ∂P) =
    ∫ b, (_root_.Homogenization.coarseBlockMatrix U b.toFun).lowerRight i j
      ∂(Measure.map (toRepoReg (d := d)) P)
  rw [show Measure.map (toRepoReg (d := d)) P
      = Measure.map ((regEquiv d).symm) P from rfl,
    MeasureTheory.integral_map_equiv]
  congr 1
  funext a
  exact coarseBlockMatrix_lowerRight_toRepo U a.toFun i j

private theorem annealedSigmaStarInv_toRepo {d : ℕ} (P : RestrictionCoeffLaw d)
    (U : Set (Vec d)) :
    annealedSigmaStarInv P U =
      _root_.Homogenization.Book.Ch04.annealedSigmaStarInv
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedSigmaStarInv
    _root_.Homogenization.Book.Ch04.annealedSigmaStarInv
  exact annealedBlockMatrix_lowerRight_toRepo P U

private theorem annealedSigmaStar_toRepo {d : ℕ} (P : RestrictionCoeffLaw d)
    (U : Set (Vec d)) :
    annealedSigmaStar P U =
      _root_.Homogenization.Book.Ch04.annealedSigmaStar
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedSigmaStar _root_.Homogenization.Book.Ch04.annealedSigmaStar
  rw [annealedSigmaStarInv_toRepo]

private theorem annealedSigmaStarInvKappaMean_toRepo {d : ℕ} (P : RestrictionCoeffLaw d)
    (U : Set (Vec d)) :
    annealedSigmaStarInvKappaMean P U =
      _root_.Homogenization.Book.Ch04.annealedSigmaStarInvKappaMean
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedSigmaStarInvKappaMean
    _root_.Homogenization.Book.Ch04.annealedSigmaStarInvKappaMean
  rw [annealedBlockMatrix_lowerLeft_toRepo]

private theorem annealedKappa_toRepo {d : ℕ} (P : RestrictionCoeffLaw d)
    (U : Set (Vec d)) :
    annealedKappa P U =
      _root_.Homogenization.Book.Ch04.annealedKappa
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedKappa _root_.Homogenization.Book.Ch04.annealedKappa
  rw [annealedSigmaStar_toRepo, annealedSigmaStarInvKappaMean_toRepo]

private theorem annealedB_toRepo {d : ℕ} (P : RestrictionCoeffLaw d)
    (U : Set (Vec d)) :
    annealedB P U =
      _root_.Homogenization.Book.Ch04.annealedB
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedB _root_.Homogenization.Book.Ch04.annealedB
  exact annealedBlockMatrix_upperLeft_toRepo P U

private theorem annealedSigma_toRepo {d : ℕ} (P : RestrictionCoeffLaw d)
    (U : Set (Vec d)) :
    annealedSigma P U =
      _root_.Homogenization.Book.Ch04.annealedSigma
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedSigma _root_.Homogenization.Book.Ch04.annealedSigma
  rw [annealedB_toRepo, annealedKappa_toRepo, annealedSigmaStarInv_toRepo]
  rfl

private theorem annealedSigmaAtScale_toRepo {d : ℕ} (P : RestrictionCoeffLaw d) (n : ℤ) :
    annealedSigmaAtScale P n =
      _root_.Homogenization.Book.Ch04.annealedSigmaAtScale
        (Measure.map (toRepoReg (d := d)) P) n := by
  unfold annealedSigmaAtScale
    _root_.Homogenization.Book.Ch04.annealedSigmaAtScale
  exact annealedSigma_toRepo P _

private theorem annealedSigmaStarAtScale_toRepo {d : ℕ} (P : RestrictionCoeffLaw d)
    (n : ℤ) :
    annealedSigmaStarAtScale P n =
      _root_.Homogenization.Book.Ch04.annealedSigmaStarAtScale
        (Measure.map (toRepoReg (d := d)) P) n := by
  unfold annealedSigmaStarAtScale
    _root_.Homogenization.Book.Ch04.annealedSigmaStarAtScale
  exact annealedSigmaStar_toRepo P _

/-! ### The contrast selector bridge

The repository's `Book.Ch05.thetaAtScale hP hStruct n` selects, via the
scalarization witnesses built from the structural law, the scalars
`barSigma`, `barSigmaStar` with `annealedSigmaAtScale P n = barSigma • 1` and
`annealedSigmaStarAtScale P n = barSigmaStar • 1`, and returns
`barSigma * barSigmaStar⁻¹`.  Since scalar matrices are determined by their
`(0, 0)` entry (`NeZero d`), the selector agrees with the total
`(0, 0)`-entry formula, which the annealed bridges transport to the audit's
total mirror `thetaAtScale P n`. -/

private theorem repo_thetaAtScale_eq_entry_formula {d : ℕ} [NeZero d]
    {P : _root_.Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : _root_.Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : _root_.Homogenization.Book.Ch04.RestrictionStructuralLaw P) (n : ℤ) :
    _root_.Homogenization.Book.Ch05.thetaAtScale hP hStruct n =
      _root_.Homogenization.Book.Ch04.annealedSigmaAtScale P n 0 0 *
        (_root_.Homogenization.Book.Ch04.annealedSigmaStarAtScale P n 0 0)⁻¹ := by
  have h1 := hP.annealedSigmaAtScale_eq_barSigmaAtScale hStruct n
  have h2 := hP.annealedSigmaStarAtScale_eq_barSigmaStarAtScale hStruct n
  have e1 : _root_.Homogenization.Book.Ch04.annealedSigmaAtScale P n 0 0 =
      hP.barSigmaAtScale hStruct n := by
    rw [h1]
    simp [Matrix.smul_apply]
  have e2 : _root_.Homogenization.Book.Ch04.annealedSigmaStarAtScale P n 0 0 =
      hP.barSigmaStarAtScale hStruct n := by
    rw [h2]
    simp [Matrix.smul_apply]
  rw [e1, e2]
  rfl

end PolynomialScale

/-! ## The law identification and the audited theorem -/

namespace RandomCheckerboard

/-- The audit checkerboard sample map is the repository sample map read
through the carrier equivalence. -/
private theorem checkerRegField_eq_comp {d : ℕ} (lam Lam : ℝ) :
    (checkerRegField (d := d) lam Lam) =
      ofRepoReg ∘
        _root_.Homogenization.Examples.RandomCheckerboard.checkerRegField lam Lam := by
  funext ω
  rfl

/-- The audit checkerboard law is the transported repository checkerboard
law. -/
private theorem law_eq_map_ofRepoReg {d : ℕ} (lam Lam : ℝ) (p : ℝ≥0) (hp : p ≤ 1) :
    law d lam Lam p hp =
      Measure.map (ofRepoReg (d := d))
        (_root_.Homogenization.Examples.RandomCheckerboard.law d lam Lam p hp) := by
  rw [law, _root_.Homogenization.Examples.RandomCheckerboard.law,
    Measure.map_map measurable_ofRepoReg
      (_root_.Homogenization.Examples.RandomCheckerboard.measurable_checkerRegField
        (d := d) lam Lam),
    ← checkerRegField_eq_comp]
  rfl

/-- Pushing the audit checkerboard law back to the repository carrier
recovers the repository checkerboard law. -/
private theorem map_toRepoReg_law {d : ℕ} (lam Lam : ℝ) (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map (toRepoReg (d := d)) (law d lam Lam p hp) =
      _root_.Homogenization.Examples.RandomCheckerboard.law d lam Lam p hp := by
  rw [law_eq_map_ofRepoReg lam Lam p hp,
    Measure.map_map measurable_toRepoReg measurable_ofRepoReg]
  have hco : (toRepoReg (d := d)) ∘ (ofRepoReg (d := d)) = id :=
    funext fun _ => rfl
  rw [hco, Measure.map_id]

end RandomCheckerboard

namespace CheckerboardScale

open PolynomialScale

/-- The repository contrast selector of the checkerboard law agrees with the
audit's total `(0,0)`-entry mirror evaluated at the audit checkerboard law:
the selector reduces to the entry formula
(`repo_thetaAtScale_eq_entry_formula`), and the annealed bridges transport
the entries along the carrier equivalence and the law identification. -/
private theorem thetaAtScale_checkerboard {d : ℕ} [NeZero d] {lam Lam : ℝ}
    (p : ℝ≥0) (hp : p ≤ 1)
    (hP : _root_.Homogenization.Book.Ch04.RestrictionLawCarrier
      (_root_.Homogenization.Examples.RandomCheckerboard.law d lam Lam p hp))
    (hStruct : _root_.Homogenization.Book.Ch04.RestrictionStructuralLaw
      (_root_.Homogenization.Examples.RandomCheckerboard.law d lam Lam p hp))
    (n : ℤ) :
    _root_.Homogenization.Book.Ch05.thetaAtScale hP hStruct n =
      thetaAtScale (RandomCheckerboard.law d lam Lam p hp) n := by
  rw [repo_thetaAtScale_eq_entry_formula hP hStruct n,
    ← RandomCheckerboard.map_toRepoReg_law lam Lam p hp,
    ← annealedSigmaAtScale_toRepo (RandomCheckerboard.law d lam Lam p hp) n,
    ← annealedSigmaStarAtScale_toRepo (RandomCheckerboard.law d lam Lam p hp) n]
  rfl

/-- Mirror of the Bernoulli-checkerboard instantiation of
`Homogenization.homogenizationScale_polynomial_of_unitRange`
(`Homogenization/HighContrast/Scale/Final.lean` applied via
`Homogenization/Examples/RandomCheckerboard/CarrierLaw.lean`).  The dimension
restriction `3 ≤ d` (i.e. `d > 2`) is explicit; the capstone's ellipticity
parameter is instantiated at `Θ = Lam` — the checkerboard realizations lie in
the quadratic-form ellipticity class `IsEllipticMatrix 1 Lam` — so the
polynomial entry-scale bound reads `3^{N₀} ≤ (2 + Lam)^Ctriadic`, an explicit
algebraic dependence on the contrast. -/
theorem randomCheckerboard_homogenizationScale
    {d : ℕ} [NeZero d] (hd : 3 ≤ d) :
    ∃ Cscale Ctriadic alpha : ℝ, 0 < Cscale ∧ 0 < Ctriadic ∧ 0 < alpha ∧
      ∀ {lam Lam : ℝ} (_h1 : 1 ≤ lam) (_hle : lam ≤ Lam) (p : ℝ≥0) (hp : p ≤ 1),
        ∃ N0 : ℕ,
          (∀ n : ℕ,
            thetaAtScale (RandomCheckerboard.law d lam Lam p hp) ((N0 + n : ℕ) : ℤ) - 1 ≤
              (3 : ℝ) ^ (-alpha * (n : ℝ))) ∧
          (N0 : ℝ) ≤ Cscale * Real.log (2 + Lam) ∧
          (3 : ℝ) ^ ((N0 : ℕ) : ℝ) ≤ (2 + Lam) ^ Ctriadic := by
  obtain ⟨Cscale, Ctriadic, alpha, hCs, hCt, halpha, hmain⟩ :=
    _root_.Homogenization.homogenizationScale_polynomial_of_unitRange (d := d) hd
  refine ⟨Cscale, Ctriadic, alpha, hCs, hCt, halpha, ?_⟩
  intro lam Lam h1 hle p hp
  have hlam : 0 < lam := lt_of_lt_of_le one_pos h1
  have hΘ : (1 : ℝ) ≤ Lam := le_trans h1 hle
  have hP :=
    _root_.Homogenization.Examples.RandomCheckerboard.lawCarrier
      (d := d) hlam hle p hp
  have hStruct :=
    _root_.Homogenization.Examples.RandomCheckerboard.structuralLaw
      (d := d) (lam := lam) (Lam := Lam) p hp
  have hLaw :=
    _root_.Homogenization.Examples.RandomCheckerboard.thetaEllipticLaw
      (d := d) h1 hle le_rfl p hp
  obtain ⟨N0, hdecay, hlog, htriadic⟩ := hmain hΘ hP hStruct hLaw
  refine ⟨N0, ?_, hlog, htriadic⟩
  intro n
  have h := hdecay n
  rwa [thetaAtScale_checkerboard p hp hP hStruct] at h

end CheckerboardScale

end

end StatementAudit
end Homogenization
