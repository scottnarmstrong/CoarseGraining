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
(`Homogenization/HighContrast/Scale/Final.lean`), applied to the checkerboard
law of `Homogenization/Examples/RandomCheckerboard/CarrierLaw.lean`.

The corresponding challenge imports only Mathlib.  This solution imports the
repository theorem surface together with the statement vocabulary of
`Audit.CheckerboardScale.SolutionBasic` — a byte-identical copy of the
challenge vocabulary — and proves the same
`StatementAudit.CheckerboardScale` theorem surface.

The audited theorem carries the explicit dimension restriction `hd : 3 ≤ d`
(`d > 2`); the capstone's ellipticity parameter is instantiated at `Θ = Lam`,
in whose quadratic-form ellipticity class the checkerboard realizations lie,
so the polynomial entry-scale bound reads `3 ^ N0 ≤ (2 + Lam) ^ Ctriadic` — an
explicit algebraic dependence on the contrast.  All hypotheses of the general
capstone (probability, honest-carrier ellipticity, stationarity, unit-range
dependence, isotropy, adjoint invariance) are discharged by the repository's
checkerboard construction, which is why the audited statement is
unconditional in `lam`, `Lam` and `p`.

The private bridges below transport the audit vocabulary to the repository
vocabulary:

* the **carrier bridge** (`toRepoReg`/`ofRepoReg` and the measurable
  equivalence `regEquiv`).  The audit carrier σ-algebra is *one* comap of the
  observable σ-algebra on raw fields, while the repository carrier σ-algebra
  is a join on the carrier; measurability in both directions is proved from
  the repository's own generator lemmas;
* the **`WeakH1`/`WeakH10` record bridges**, which after the challenge
  redesign are pure field renamings;
* the **block-state bridge**, transporting the `Mu` admissible class, hence
  `muValueSet`/`Mu` equality, hence equality of the polarized coarse block
  matrices, of the annealed matrices, and finally of the scalar contrast;
* the **law identification** (`law_eq_map_ofRepoReg`, `map_toRepoReg_law`),
  recognizing the audit checkerboard law as the transported repository
  checkerboard law, so the repository's contrast selector for the checkerboard
  agrees with the audit's total `(0,0)`-entry mirror `thetaAtScale`.

The final theorem is exactly the repository capstone applied to the
checkerboard witnesses `lawCarrier`, `structuralLaw` and `thetaEllipticLaw`
(at `Θ = Lam`), composed with these bridges.
-/

namespace Homogenization
namespace StatementAudit

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

/-! ## Solution-only bridges to the repository theorem -/

/-! ### Probe classes -/

/-- The challenge probe class is the repository probe class. -/
private theorem isProbeR_of_isProbe {d : ℕ} {φ : Vec d → ℝ} (h : IsProbe φ) :
    _root_.Homogenization.IsProbeR (d := d) φ :=
  ⟨h.measurable, h.bounded, h.compactSupport⟩

/-- The repository probe class is the challenge probe class. -/
private theorem isProbe_of_isProbeR {d : ℕ} {φ : Vec d → ℝ}
    (h : _root_.Homogenization.IsProbeR (d := d) φ) : IsProbe φ :=
  ⟨h.measurable, h.bounded, h.hasCompactSupport⟩

/-! ### The carrier bridge

`CoefficientField d` and `Homogenization.RegCoeffField d` are the same
three-field structure (one field name differs), so the identity on the
underlying raw field is a bijection between them. -/

/-- The audit carrier viewed as the repository carrier. -/
private def toRepoReg {d : ℕ} (a : CoefficientField d) :
    _root_.Homogenization.RegCoeffField d where
  toFun := a.toFun
  entry_measurable := a.entry_measurable
  entry_locInt := a.entry_locallyIntegrable

/-- The repository carrier viewed as the audit carrier. -/
private def ofRepoReg {d : ℕ} (a : _root_.Homogenization.RegCoeffField d) :
    CoefficientField d where
  toFun := a.toFun
  entry_measurable := a.entry_measurable
  entry_locallyIntegrable := a.entry_locInt

@[simp] private theorem toRepoReg_toFun {d : ℕ} (a : CoefficientField d) :
    (toRepoReg a).toFun = a.toFun := rfl

@[simp] private theorem ofRepoReg_toFun {d : ℕ}
    (a : _root_.Homogenization.RegCoeffField d) :
    (ofRepoReg a).toFun = a.toFun := rfl

@[simp] private theorem toRepoReg_ofRepoReg {d : ℕ}
    (a : _root_.Homogenization.RegCoeffField d) :
    toRepoReg (ofRepoReg a) = a := rfl

@[simp] private theorem ofRepoReg_toRepoReg {d : ℕ} (a : CoefficientField d) :
    ofRepoReg (toRepoReg a) = a := rfl

/-! ### The observable σ-algebra and measurability of the carrier bridge

The bare function type `RawCoeffField d` deliberately carries no global
`MeasurableSpace` instance in the challenge.  Inside the section below the
observable σ-algebra is installed as a section-local instance so that the
measurability lemmas can be written in ordinary `Measurable` vocabulary.  No
statement exported from the section mentions the local instance. -/

section CarrierMeasurability

/-- The observable σ-algebra on raw fields, as a section-local instance. -/
local instance instRawFieldsObservable (d : ℕ) :
    MeasurableSpace (RawCoeffField d) :=
  observableFieldSigma d

/-- `CoefficientField.toFun` is measurable from the carrier σ-algebra to the
observable σ-algebra: the former is by definition the comap of the latter. -/
private theorem measurable_coefficientField_toFun (d : ℕ) :
    Measurable (fun a : CoefficientField d => a.toFun) :=
  Measurable.of_comap_le le_rfl

/-- Point evaluation of a single matrix entry is observable. -/
private theorem measurable_rawApplyEntry {d : ℕ} (y : Vec d) (i j : Fin d) :
    Measurable (fun f : RawCoeffField d => f y i j) := by
  have h1 : @Measurable (RawCoeffField d) (Mat d) (pointwiseFieldSigma d)
      (instMeasurableSpaceMat d) (fun f => f y) := measurable_pi_apply y
  have h3 : @Measurable (Mat d) (Fin d → ℝ) (instMeasurableSpaceMat d)
      MeasurableSpace.pi (fun A => A i) := measurable_pi_apply i
  have h2 : @Measurable (Mat d) ℝ (instMeasurableSpaceMat d) _ (fun A => A i j) :=
    (measurable_pi_apply j).comp h3
  exact (h2.comp h1).mono le_sup_left le_rfl

/-- Every probe integral is observable. -/
private theorem measurable_rawEntryTest {d : ℕ} (i j : Fin d) {φ : Vec d → ℝ}
    (hφ : IsProbe φ) : Measurable (entryTest i j φ) := by
  have h : @Measurable (RawCoeffField d) ℝ (probeFieldSigma d) _
      (entryTest i j φ) := by
    intro t ht
    exact MeasurableSpace.measurableSet_generateFrom ⟨i, j, φ, hφ, t, ht, rfl⟩
  exact h.mono le_sup_right le_rfl

/-- Measurability into the carrier reduces to measurability of the underlying
raw field for the observable σ-algebra (the carrier σ-algebra is a comap). -/
private theorem measurable_into_coefficientField {α : Type*} [MeasurableSpace α]
    {d : ℕ} {F : α → CoefficientField d}
    (h : Measurable (fun a => (F a).toFun)) : Measurable F := by
  rw [measurable_iff_comap_le, instMeasurableSpaceCoefficientField,
    MeasurableSpace.comap_comp]
  exact h.comap_le

/-- The underlying raw field of a repository carrier element is observable. -/
private theorem measurable_repoRegToFun {d : ℕ} :
    Measurable (fun a : _root_.Homogenization.RegCoeffField d => a.toFun) := by
  refine _root_.Homogenization.measurable_into_sup ?_ ?_
  · exact Measurable.of_comap_le (_root_.Homogenization.pointwiseSigmaR_le d)
  · refine measurable_generateFrom ?_
    rintro s ⟨i, j, φ, hφ, t, ht, rfl⟩
    exact _root_.Homogenization.measurable_entryTestR i j (isProbeR_of_isProbe hφ) ht

private theorem measurable_toRepoReg {d : ℕ} : Measurable (toRepoReg (d := d)) := by
  refine _root_.Homogenization.measurable_into_regCoeffField' ?_ ?_
  · intro y i j
    exact (measurable_rawApplyEntry y i j).comp (measurable_coefficientField_toFun d)
  · intro i j φ hφ
    exact (measurable_rawEntryTest i j (isProbe_of_isProbeR hφ)).comp
      (measurable_coefficientField_toFun d)

private theorem measurable_ofRepoReg {d : ℕ} : Measurable (ofRepoReg (d := d)) :=
  measurable_into_coefficientField measurable_repoRegToFun

end CarrierMeasurability

/-- The audit carrier and the repository carrier are measurably equivalent via
the identity on the underlying raw field. -/
private def regEquiv (d : ℕ) :
    _root_.Homogenization.RegCoeffField d ≃ᵐ CoefficientField d where
  toEquiv :=
    { toFun := ofRepoReg
      invFun := toRepoReg
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  measurable_toFun := measurable_ofRepoReg
  measurable_invFun := measurable_toRepoReg

/-! ### The Sobolev record bridges

After the challenge redesign these are pure field renamings:
`approx_compactSupport` ↔ `approx_hasCompactSupport`, `approx_supportedIn` ↔
`approx_support_subset`, `toWeakH1` ↔ `toH1Function`. -/

private def toRepoWeakH1 {d : ℕ} {U : Set (Vec d)} (u : WeakH1 U) :
    _root_.Homogenization.H1Function U where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memL2
  gradMemL2 := u.gradMemL2
  hasWeakGradient := u.hasWeakGradient

private def ofRepoWeakH1 {d : ℕ} {U : Set (Vec d)}
    (u : _root_.Homogenization.H1Function U) : WeakH1 U where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memL2
  gradMemL2 := u.gradMemL2
  hasWeakGradient := u.hasWeakGradient

private def toRepoWeakH10 {d : ℕ} {U : Set (Vec d)} (u : WeakH10 U) :
    _root_.Homogenization.H10Function U where
  toH1Function := toRepoWeakH1 u.toWeakH1
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_hasCompactSupport := u.approx_compactSupport
  approx_support_subset := u.approx_supportedIn
  tendsto_approx := u.tendsto_approx
  tendsto_approx_grad := u.tendsto_approx_grad

private def ofRepoWeakH10 {d : ℕ} {U : Set (Vec d)}
    (u : _root_.Homogenization.H10Function U) : WeakH10 U where
  toWeakH1 := ofRepoWeakH1 u.toH1Function
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_compactSupport := u.approx_hasCompactSupport
  approx_supportedIn := u.approx_support_subset
  tendsto_approx := u.tendsto_approx
  tendsto_approx_grad := u.tendsto_approx_grad

/-! ### The block formalism and `Mu`

The audit `BlockState`/`WeakH1`/`WeakH10` records are statement-level copies
of the repository records over definitionally equal ambient types, so the
admissibility conjuncts transport along the evident record maps and the two
`muValueSet`s coincide; `Mu` equality follows by `sInf` congruence. -/

private def toRepoBlockState {d : ℕ} (X : BlockState d) :
    _root_.Homogenization.BlockState d where
  potential := X.potential
  flux := X.flux

private def ofRepoBlockState {d : ℕ} (X : _root_.Homogenization.BlockState d) :
    BlockState d where
  potential := X.potential
  flux := X.flux

private theorem toRepo_isPotentialZeroTraceOn {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → Vec d} (h : IsPotentialZeroTraceOn U f) :
    _root_.Homogenization.IsPotentialZeroTraceOn U f := by
  obtain ⟨u, hu⟩ := h
  exact ⟨toRepoWeakH10 u, hu⟩

private theorem ofRepo_isPotentialZeroTraceOn {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → Vec d} (h : _root_.Homogenization.IsPotentialZeroTraceOn U f) :
    IsPotentialZeroTraceOn U f := by
  obtain ⟨u, hu⟩ := h
  exact ⟨ofRepoWeakH10 u, hu⟩

private theorem toRepo_isSolenoidalZeroNormalTraceOn {d : ℕ} {U : Set (Vec d)}
    {g : Vec d → Vec d} (h : IsSolenoidalZeroNormalTraceOn U g) :
    _root_.Homogenization.IsSolenoidalZeroNormalTraceOn U g :=
  fun φ => h (ofRepoWeakH1 φ)

private theorem ofRepo_isSolenoidalZeroNormalTraceOn {d : ℕ} {U : Set (Vec d)}
    {g : Vec d → Vec d}
    (h : _root_.Homogenization.IsSolenoidalZeroNormalTraceOn U g) :
    IsSolenoidalZeroNormalTraceOn U g :=
  fun φ => h (toRepoWeakH1 φ)

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
    (a : RawCoeffField d) :
    muValueSet U P a = _root_.Homogenization.muValueSet U P a := by
  ext m
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact ⟨toRepoBlockState X, toRepo_isBlockMuAdmissible hX, rfl⟩
  · rintro ⟨X, hX, rfl⟩
    exact ⟨ofRepoBlockState X, ofRepo_isBlockMuAdmissible hX, rfl⟩

private theorem mu_toRepo {d : ℕ} (U : Set (Vec d)) (P : BlockVec d)
    (a : RawCoeffField d) :
    Mu U P a = _root_.Homogenization.Mu U P a := by
  unfold Mu _root_.Homogenization.Mu
  rw [muValueSet_toRepo]

/-! ### The coarse block matrix

Polarization through the repository's private entry selector, which is
definitionally transparent. -/

private theorem coarseBlockEntry_toRepo {d : ℕ} (U : Set (Vec d))
    (a : RawCoeffField d) (α β : BlockCoord d) :
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
    (a : RawCoeffField d) (i j : Fin d) :
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
    (a : RawCoeffField d) (i j : Fin d) :
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
    (a : RawCoeffField d) (i j : Fin d) :
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
    (a : RawCoeffField d) (i j : Fin d) :
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

/-! ### The annealed matrices

The annealed integrals transport along the carrier equivalence `regEquiv`, and
the matrix algebra is congruent. -/

private theorem annealedBlockMatrix_upperLeft_toRepo {d : ℕ}
    (P : CoefficientLaw d) (U : Set (Vec d)) :
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

private theorem annealedBlockMatrix_lowerLeft_toRepo {d : ℕ}
    (P : CoefficientLaw d) (U : Set (Vec d)) :
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

private theorem annealedBlockMatrix_lowerRight_toRepo {d : ℕ}
    (P : CoefficientLaw d) (U : Set (Vec d)) :
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

private theorem annealedSigmaStarInv_toRepo {d : ℕ} (P : CoefficientLaw d)
    (U : Set (Vec d)) :
    annealedSigmaStarInv P U =
      _root_.Homogenization.Book.Ch04.annealedSigmaStarInv
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedSigmaStarInv
    _root_.Homogenization.Book.Ch04.annealedSigmaStarInv
  exact annealedBlockMatrix_lowerRight_toRepo P U

private theorem annealedSigmaStar_toRepo {d : ℕ} (P : CoefficientLaw d)
    (U : Set (Vec d)) :
    annealedSigmaStar P U =
      _root_.Homogenization.Book.Ch04.annealedSigmaStar
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedSigmaStar _root_.Homogenization.Book.Ch04.annealedSigmaStar
  rw [annealedSigmaStarInv_toRepo]

private theorem annealedSigmaStarInvKappa_toRepo {d : ℕ} (P : CoefficientLaw d)
    (U : Set (Vec d)) :
    annealedSigmaStarInvKappa P U =
      _root_.Homogenization.Book.Ch04.annealedSigmaStarInvKappaMean
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedSigmaStarInvKappa
    _root_.Homogenization.Book.Ch04.annealedSigmaStarInvKappaMean
  rw [annealedBlockMatrix_lowerLeft_toRepo]

private theorem annealedKappa_toRepo {d : ℕ} (P : CoefficientLaw d)
    (U : Set (Vec d)) :
    annealedKappa P U =
      _root_.Homogenization.Book.Ch04.annealedKappa
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedKappa _root_.Homogenization.Book.Ch04.annealedKappa
  rw [annealedSigmaStar_toRepo, annealedSigmaStarInvKappa_toRepo]

private theorem annealedSigma_toRepo {d : ℕ} (P : CoefficientLaw d)
    (U : Set (Vec d)) :
    annealedSigma P U =
      _root_.Homogenization.Book.Ch04.annealedSigma
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedSigma _root_.Homogenization.Book.Ch04.annealedSigma
    _root_.Homogenization.Book.Ch04.annealedB
  rw [annealedBlockMatrix_upperLeft_toRepo, annealedKappa_toRepo,
    annealedSigmaStarInv_toRepo]
  rfl

private theorem annealedSigmaAtScale_toRepo {d : ℕ} [NeZero d]
    (P : CoefficientLaw d) (n : ℕ) :
    annealedSigmaAtScale P n =
      _root_.Homogenization.Book.Ch04.annealedSigmaAtScale
        (Measure.map (toRepoReg (d := d)) P) (n : ℤ) := by
  unfold annealedSigmaAtScale
    _root_.Homogenization.Book.Ch04.annealedSigmaAtScale
  exact annealedSigma_toRepo P _

private theorem annealedSigmaStarAtScale_toRepo {d : ℕ} [NeZero d]
    (P : CoefficientLaw d) (n : ℕ) :
    annealedSigmaStarAtScale P n =
      _root_.Homogenization.Book.Ch04.annealedSigmaStarAtScale
        (Measure.map (toRepoReg (d := d)) P) (n : ℤ) := by
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
total mirror `thetaAtScale`. -/

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

/-! ## The checkerboard law identification -/

namespace RandomCheckerboard

/-- The audit checkerboard realization is the repository sample map read
through the carrier equivalence. -/
private theorem realization_eq_comp {d : ℕ} (lam Lam : ℝ) :
    (realization (d := d) lam Lam) =
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
    ← realization_eq_comp]
  rfl

/-- Pushing the audit checkerboard law back to the repository carrier recovers
the repository checkerboard law. -/
private theorem map_toRepoReg_law {d : ℕ} (lam Lam : ℝ) (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map (toRepoReg (d := d)) (law d lam Lam p hp) =
      _root_.Homogenization.Examples.RandomCheckerboard.law d lam Lam p hp := by
  rw [law_eq_map_ofRepoReg lam Lam p hp,
    Measure.map_map measurable_toRepoReg measurable_ofRepoReg]
  have hco : (toRepoReg (d := d)) ∘ (ofRepoReg (d := d)) = id :=
    funext fun _ => rfl
  rw [hco, Measure.map_id]

end RandomCheckerboard

/-! ## The audited theorem -/

namespace CheckerboardScale

/-- The repository contrast selector of the checkerboard law agrees with the
audit's total `(0,0)`-entry mirror evaluated at the audit checkerboard law:
the selector reduces to the entry formula
(`repo_thetaAtScale_eq_entry_formula`), and the annealed bridges transport the
entries along the carrier equivalence and the law identification. -/
private theorem thetaAtScale_checkerboard {d : ℕ} [NeZero d] {lam Lam : ℝ}
    (p : ℝ≥0) (hp : p ≤ 1)
    (hP : _root_.Homogenization.Book.Ch04.RestrictionLawCarrier
      (_root_.Homogenization.Examples.RandomCheckerboard.law d lam Lam p hp))
    (hStruct : _root_.Homogenization.Book.Ch04.RestrictionStructuralLaw
      (_root_.Homogenization.Examples.RandomCheckerboard.law d lam Lam p hp))
    (n : ℕ) :
    _root_.Homogenization.Book.Ch05.thetaAtScale hP hStruct (n : ℤ) =
      thetaAtScale (RandomCheckerboard.law d lam Lam p hp) n := by
  rw [repo_thetaAtScale_eq_entry_formula hP hStruct (n : ℤ),
    ← RandomCheckerboard.map_toRepoReg_law lam Lam p hp,
    ← annealedSigmaAtScale_toRepo (RandomCheckerboard.law d lam Lam p hp) n,
    ← annealedSigmaStarAtScale_toRepo (RandomCheckerboard.law d lam Lam p hp) n]
  rfl

/-- **Homogenization scale for the Bernoulli checkerboard.**  In dimension
`d ≥ 3` there are dimensional constants `Cscale, Ctriadic, alpha > 0` such that
for all conductances `1 ≤ lam ≤ Lam` and every coin parameter `p ≤ 1` the
checkerboard law has an entry scale `N0` above which the scalar contrast decays
geometrically, with `N0` logarithmic and `3 ^ N0` polynomial in the contrast.

Mirrors the checkerboard instantiation of
`Homogenization.homogenizationScale_polynomial_of_unitRange`. -/
theorem randomCheckerboard_homogenizationScale
    {d : ℕ} [NeZero d] (hd : 3 ≤ d) :
    ∃ Cscale Ctriadic alpha : ℝ, 0 < Cscale ∧ 0 < Ctriadic ∧ 0 < alpha ∧
      ∀ {lam Lam : ℝ}, 1 ≤ lam → lam ≤ Lam → ∀ (p : ℝ≥0) (hp : p ≤ 1),
        ∃ N0 : ℕ,
          (∀ n : ℕ,
            thetaAtScale (RandomCheckerboard.law d lam Lam p hp) (N0 + n) - 1 ≤
              (3 : ℝ) ^ (-alpha * (n : ℝ))) ∧
          (N0 : ℝ) ≤ Cscale * Real.log (2 + Lam) ∧
          (3 : ℝ) ^ (N0 : ℝ) ≤ (2 + Lam) ^ Ctriadic := by
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
