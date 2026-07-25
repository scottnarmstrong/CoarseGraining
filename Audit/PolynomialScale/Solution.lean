import Mathlib
import Homogenization.HighContrast.Scale.Final
import Audit.PolynomialScale.SolutionBasic

attribute [-instance] Homogenization.instMeasurableSpaceVec
attribute [-instance] Homogenization.instMeasurableSpaceMat
attribute [-instance] Homogenization.instMeasurableSpaceCoeffField

/-!
# Solution for the polynomial homogenization-scale challenge

This file is the comparator solution surface for the unconditional
homogenization-scale capstone
`Homogenization.homogenizationScale_polynomial_of_unitRange`
(`Homogenization/HighContrast/Scale/Final.lean`).

The corresponding challenge imports only Mathlib.  This solution imports the
repository theorem, together with the shared statement vocabulary of
`Audit.PolynomialScale.SolutionBasic`, and proves the same
`StatementAudit.PolynomialScale` theorem surface.

The audited theorem carries the explicit dimension restriction `hd : 3 ≤ d`
(`d > 2`), and its ellipticity hypothesis enters only through the
quadratic-form class `IsEllipticMatrix 1 Θ` (coercivity together with the
inverse quadratic-form bound); the coefficient fields are general
(non-symmetric) matrices.

The private bridges below transport the audit vocabulary to the repository
vocabulary:

* the carrier bridge (`toRepoReg`/`ofRepoReg` and the measurable equivalence
  `regEquiv`) transports laws, law hypotheses, and almost-sure statements;
* the `H1Function`/`H10Function` record bridges transport the Sobolev
  witnesses inside the potential/solenoidal trace predicates;
* the block-state bridge transports the `Mu` admissible class, giving
  `muValueSet`/`Mu` equality, hence equality of the polarized coarse block
  matrices, of the annealed matrices, and finally of the scalar contrast:
  the repository's structural-law contrast selector agrees with the audit's
  total `(0,0)`-entry ratio `thetaAtScale`.
-/

namespace Homogenization
namespace StatementAudit

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-! ## Solution-only bridges to the repository theorem -/

private def toRepoTriadicCube {d : ℕ} (Q : TriadicCube d) :
    _root_.Homogenization.TriadicCube d :=
  { scale := Q.scale
    index := Q.index }

private def ofRepoTriadicCube {d : ℕ}
    (Q : _root_.Homogenization.TriadicCube d) : TriadicCube d :=
  { scale := Q.scale
    index := Q.index }

private theorem cubeSet_ofRepoTriadicCube {d : ℕ}
    (Q : _root_.Homogenization.TriadicCube d) :
    cubeSet (ofRepoTriadicCube Q) = _root_.Homogenization.cubeSet Q :=
  rfl

private theorem openCubeSet_ofRepoTriadicCube {d : ℕ}
    (Q : _root_.Homogenization.TriadicCube d) :
    openCubeSet (ofRepoTriadicCube Q) = _root_.Homogenization.openCubeSet Q :=
  rfl

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

private theorem ae_map_toRepoReg_iff {d : ℕ}
    {μ : Measure (RegCoeffField d)}
    {p : _root_.Homogenization.RegCoeffField d → Prop} :
    (∀ᵐ b ∂Measure.map (toRepoReg (d := d)) μ, p b) ↔
      ∀ᵐ a ∂μ, p (toRepoReg a) := by
  rw [show Measure.map (toRepoReg (d := d)) μ = Measure.map (regEquiv d).symm μ from rfl,
    ← MeasurableEquiv.map_ae]
  exact Filter.eventually_map

private theorem toRepo_isAEEllipticFieldOn {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} {a : CoeffField d}
    (h : IsAEEllipticFieldOn lam Lam U a) :
    _root_.Homogenization.IsAEEllipticFieldOn lam Lam U a := by
  simpa [IsAEEllipticFieldOn, _root_.Homogenization.IsAEEllipticFieldOn,
    restrictCoeffField, _root_.Homogenization.restrictCoeffField,
    IsEllipticMatrix, _root_.Homogenization.IsEllipticMatrix,
    vecDot, _root_.Homogenization.vecDot, vecNormSq, _root_.Homogenization.vecNormSq,
    matVecMul, _root_.Homogenization.matVecMul] using h

private theorem toRepo_AELocallyUniformlyEllipticField {d : ℕ}
    {a : RegCoeffField d} (ha : AELocallyUniformlyEllipticField a) :
    _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField (toRepoReg a) := by
  intro Q
  rcases ha (ofRepoTriadicCube Q) with ⟨lam, Lam, hlam, hle, hEll⟩
  refine ⟨lam, Lam, hlam, hle, ?_⟩
  have hRepo := toRepo_isAEEllipticFieldOn hEll
  simpa [_root_.Homogenization.Book.Ch04.AEEllipticOn,
    openCubeSet_ofRepoTriadicCube] using hRepo

private theorem toRepoLawCarrier {d : ℕ} {P : CoeffLaw d}
    (hP : LawCarrier P) :
    _root_.Homogenization.Book.Ch04.LawCarrier
      (Measure.map (toRepoReg (d := d)) P) where
  isProbability := by
    haveI := hP.isProbability
    exact Measure.isProbabilityMeasure_map measurable_toRepoReg.aemeasurable
  ae_locally_uniformly_elliptic := by
    refine (ae_map_toRepoReg_iff (μ := P)).2 ?_
    filter_upwards [hP.ae_locally_uniformly_elliptic] with a ha
    exact toRepo_AELocallyUniformlyEllipticField ha

/-- Pushforward transport of a law-invariance along the carrier equivalence:
if the audit endomorphism `T` is intertwined with the repository endomorphism
`Trepo` and preserves the audit law, then `Trepo` preserves the transported
law. -/
private theorem map_transport {d : ℕ} {P : CoeffLaw d}
    (T : RegCoeffField d → RegCoeffField d)
    (Trepo : _root_.Homogenization.RegCoeffField d →
      _root_.Homogenization.RegCoeffField d)
    (hTrepo : Measurable Trepo)
    (hEq : T = ofRepoReg ∘ Trepo ∘ toRepoReg)
    (hInv : Measure.map T P = P) :
    Measure.map Trepo (Measure.map (toRepoReg (d := d)) P)
      = Measure.map (toRepoReg (d := d)) P := by
  have hT_meas : Measurable T := by
    rw [hEq]
    exact measurable_ofRepoReg.comp (hTrepo.comp measurable_toRepoReg)
  have hcomp : Trepo ∘ toRepoReg = toRepoReg ∘ T := by
    funext a
    have h := congrFun hEq a
    show Trepo (toRepoReg a) = toRepoReg (T a)
    rw [h]
    rfl
  calc
    Measure.map Trepo (Measure.map (toRepoReg (d := d)) P)
        = Measure.map (Trepo ∘ toRepoReg) P :=
          Measure.map_map hTrepo measurable_toRepoReg
    _ = Measure.map (toRepoReg ∘ T) P := by rw [hcomp]
    _ = Measure.map (toRepoReg (d := d)) (Measure.map T P) :=
          (Measure.map_map measurable_toRepoReg hT_meas).symm
    _ = Measure.map (toRepoReg (d := d)) P := by rw [hInv]

private theorem toRepoStructuralLaw {d : ℕ} {P : CoeffLaw d}
    (hStruct : StructuralLaw P) :
    _root_.Homogenization.Book.Ch04.StructuralLaw
      (Measure.map (toRepoReg (d := d)) P) where
  stationary := by
    intro z
    exact map_transport (translateReg (intVecToRealVec z))
      (_root_.Homogenization.translateReg (_root_.Homogenization.intVecToRealVec z))
      (_root_.Homogenization.measurable_translateReg _)
      (funext fun a => rfl) (hStruct.stationary z)
  unit_range := by
    intro U V hU hV hsep
    have hsep_aud : AreUnitSeparated U V := hsep
    have haud := hStruct.unit_range U V hU hV hsep_aud
    rw [ProbabilityTheory.Indep_iff]
    intro s t hs ht
    have hs_amb : MeasurableSet s :=
      _root_.Homogenization.restrictionSigmaR_le U hU s hs
    have ht_amb : MeasurableSet t :=
      _root_.Homogenization.restrictionSigmaR_le V hV t ht
    have hs_aud : @MeasurableSet (RegCoeffField d) (RestrictionSigmaR U hU)
        (toRepoReg ⁻¹' s) := by
      rcases hs with ⟨t0, ht0, rfl⟩
      exact ⟨toRepoReg ⁻¹' t0, measurable_toRepoReg ht0, rfl⟩
    have ht_aud : @MeasurableSet (RegCoeffField d) (RestrictionSigmaR V hV)
        (toRepoReg ⁻¹' t) := by
      rcases ht with ⟨t0, ht0, rfl⟩
      exact ⟨toRepoReg ⁻¹' t0, measurable_toRepoReg ht0, rfl⟩
    have hprod := (ProbabilityTheory.Indep_iff _ _ _).1 haud _ _ hs_aud ht_aud
    rw [Measure.map_apply measurable_toRepoReg (hs_amb.inter ht_amb),
      Measure.map_apply measurable_toRepoReg hs_amb,
      Measure.map_apply measurable_toRepoReg ht_amb]
    simpa [Set.preimage_inter] using hprod
  isotropic := by
    intro R hR
    have hR_aud : IsSignedPermutationMatrix R := hR
    exact map_transport (rotateReg R hR_aud)
      (_root_.Homogenization.rotateReg R hR)
      (_root_.Homogenization.measurable_rotateReg R hR)
      (funext fun a => rfl) (hStruct.isotropic R hR_aud)
  adjoint_invariant := by
    exact map_transport adjointReg _root_.Homogenization.adjointReg
      _root_.Homogenization.measurable_adjointReg
      (funext fun a => rfl) hStruct.adjoint_invariant

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

private theorem annealedBlockMatrix_upperLeft_toRepo {d : ℕ} (P : CoeffLaw d)
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

private theorem annealedBlockMatrix_upperRight_toRepo {d : ℕ} (P : CoeffLaw d)
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

private theorem annealedBlockMatrix_lowerLeft_toRepo {d : ℕ} (P : CoeffLaw d)
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

private theorem annealedBlockMatrix_lowerRight_toRepo {d : ℕ} (P : CoeffLaw d)
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

private theorem annealedSigmaStarInv_toRepo {d : ℕ} (P : CoeffLaw d)
    (U : Set (Vec d)) :
    annealedSigmaStarInv P U =
      _root_.Homogenization.Book.Ch04.annealedSigmaStarInv
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedSigmaStarInv
    _root_.Homogenization.Book.Ch04.annealedSigmaStarInv
  exact annealedBlockMatrix_lowerRight_toRepo P U

private theorem annealedSigmaStar_toRepo {d : ℕ} (P : CoeffLaw d)
    (U : Set (Vec d)) :
    annealedSigmaStar P U =
      _root_.Homogenization.Book.Ch04.annealedSigmaStar
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedSigmaStar _root_.Homogenization.Book.Ch04.annealedSigmaStar
  rw [annealedSigmaStarInv_toRepo]

private theorem annealedSigmaStarInvKappaMean_toRepo {d : ℕ} (P : CoeffLaw d)
    (U : Set (Vec d)) :
    annealedSigmaStarInvKappaMean P U =
      _root_.Homogenization.Book.Ch04.annealedSigmaStarInvKappaMean
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedSigmaStarInvKappaMean
    _root_.Homogenization.Book.Ch04.annealedSigmaStarInvKappaMean
  rw [annealedBlockMatrix_lowerLeft_toRepo]

private theorem annealedKappa_toRepo {d : ℕ} (P : CoeffLaw d)
    (U : Set (Vec d)) :
    annealedKappa P U =
      _root_.Homogenization.Book.Ch04.annealedKappa
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedKappa _root_.Homogenization.Book.Ch04.annealedKappa
  rw [annealedSigmaStar_toRepo, annealedSigmaStarInvKappaMean_toRepo]

private theorem annealedB_toRepo {d : ℕ} (P : CoeffLaw d)
    (U : Set (Vec d)) :
    annealedB P U =
      _root_.Homogenization.Book.Ch04.annealedB
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedB _root_.Homogenization.Book.Ch04.annealedB
  exact annealedBlockMatrix_upperLeft_toRepo P U

private theorem annealedSigma_toRepo {d : ℕ} (P : CoeffLaw d)
    (U : Set (Vec d)) :
    annealedSigma P U =
      _root_.Homogenization.Book.Ch04.annealedSigma
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedSigma _root_.Homogenization.Book.Ch04.annealedSigma
  rw [annealedB_toRepo, annealedKappa_toRepo, annealedSigmaStarInv_toRepo]
  rfl

private theorem annealedSigmaAtScale_toRepo {d : ℕ} (P : CoeffLaw d) (n : ℤ) :
    annealedSigmaAtScale P n =
      _root_.Homogenization.Book.Ch04.annealedSigmaAtScale
        (Measure.map (toRepoReg (d := d)) P) n := by
  unfold annealedSigmaAtScale
    _root_.Homogenization.Book.Ch04.annealedSigmaAtScale
  exact annealedSigma_toRepo P _

private theorem annealedSigmaStarAtScale_toRepo {d : ℕ} (P : CoeffLaw d)
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
    {P : _root_.Homogenization.Book.Ch04.CoeffLaw d}
    (hP : _root_.Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : _root_.Homogenization.Book.Ch04.StructuralLaw P) (n : ℤ) :
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

private theorem thetaAtScale_toRepo {d : ℕ} [NeZero d] (P : CoeffLaw d)
    (hP : _root_.Homogenization.Book.Ch04.LawCarrier
      (Measure.map (toRepoReg (d := d)) P))
    (hStruct : _root_.Homogenization.Book.Ch04.StructuralLaw
      (Measure.map (toRepoReg (d := d)) P)) (n : ℤ) :
    _root_.Homogenization.Book.Ch05.thetaAtScale hP hStruct n =
      thetaAtScale P n := by
  rw [repo_thetaAtScale_eq_entry_formula hP hStruct n,
    ← annealedSigmaAtScale_toRepo P n, ← annealedSigmaStarAtScale_toRepo P n]
  rfl

/-! ### The `Θ`-ellipticity transport (quadratic-form class only) -/

private theorem toRepoThetaEllipticLaw {d : ℕ} {Θ : ℝ} {P : CoeffLaw d}
    (h : ThetaEllipticLaw Θ P) :
    _root_.Homogenization.ThetaEllipticLaw Θ
      (Measure.map (toRepoReg (d := d)) P) := by
  have h' : ∀ᵐ b ∂(Measure.map (toRepoReg (d := d)) P),
      ∀ᵐ x ∂(MeasureTheory.volume : Measure (Vec d)),
        _root_.Homogenization.IsEllipticMatrix 1 Θ (b x) := by
    refine (ae_map_toRepoReg_iff (μ := P)).2 ?_
    filter_upwards [h] with a ha
    filter_upwards [ha] with x hx
    exact hx
  exact h'

/-! ### The audited theorem -/

/-- Mirror of `Homogenization.homogenizationScale_polynomial_of_unitRange`
(`Homogenization/HighContrast/Scale/Final.lean`).  The dimension restriction
`3 ≤ d` (i.e. `d > 2`) is explicit; ellipticity enters only through the
quadratic-form class `IsEllipticMatrix 1 Θ`. -/
theorem homogenizationScale_polynomial_of_unitRange
    {d : ℕ} [NeZero d] (hd : 3 ≤ d) :
    ∃ Cscale Ctriadic alpha : ℝ, 0 < Cscale ∧ 0 < Ctriadic ∧ 0 < alpha ∧
      ∀ {Θ : ℝ} (_hΘ : 1 ≤ Θ) {P : CoeffLaw d} [IsProbabilityMeasure P]
        (_hP : LawCarrier P) (_hStruct : StructuralLaw P)
        (_hLaw : ThetaEllipticLaw Θ P),
      ∃ N0 : ℕ,
        (∀ n : ℕ,
          thetaAtScale P ((N0 + n : ℕ) : ℤ) - 1 ≤
            (3 : ℝ) ^ (-alpha * (n : ℝ))) ∧
        (N0 : ℝ) ≤ Cscale * Real.log (2 + Θ) ∧
        (3 : ℝ) ^ ((N0 : ℕ) : ℝ) ≤ (2 + Θ) ^ Ctriadic := by
  obtain ⟨Cscale, Ctriadic, alpha, hCs, hCt, halpha, hmain⟩ :=
    _root_.Homogenization.homogenizationScale_polynomial_of_unitRange
      (d := d) hd
  refine ⟨Cscale, Ctriadic, alpha, hCs, hCt, halpha, ?_⟩
  intro Θ hΘ P _hProb hP hStruct hLaw
  haveI : IsProbabilityMeasure (Measure.map (toRepoReg (d := d)) P) :=
    Measure.isProbabilityMeasure_map measurable_toRepoReg.aemeasurable
  have hP' := toRepoLawCarrier hP
  have hStruct' := toRepoStructuralLaw hStruct
  have hLaw' := toRepoThetaEllipticLaw hLaw
  obtain ⟨N0, hdecay, hlog, htriadic⟩ := hmain hΘ hP' hStruct' hLaw'
  refine ⟨N0, ?_, hlog, htriadic⟩
  intro n
  have h := hdecay n
  rwa [thetaAtScale_toRepo P hP' hStruct'] at h

end PolynomialScale

end

end StatementAudit
end Homogenization
