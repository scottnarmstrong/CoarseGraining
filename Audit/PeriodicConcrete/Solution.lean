import Mathlib
import Homogenization.Examples.Periodic.PeriodicConcreteComparison
import Audit.PeriodicConcrete.SolutionBasic

attribute [-instance] Homogenization.instMeasurableSpaceVec
attribute [-instance] Homogenization.instMeasurableSpaceMat
attribute [-instance] Homogenization.instMeasurableSpaceCoeffField

/-!
# Solution: periodic homogenization comparison (explicit field)

This file is the comparator solution surface for the explicit periodic
specialization of the quenched homogenization comparison theorem: the Dirac law
at `a(x) = m(x) • I`, `m(x) = d + 2 + ∑ i, cos (2 π xᵢ)`.

The corresponding challenge (`Audit/PeriodicConcrete/Challenge.lean`) imports
only Mathlib.  This file imports the repository theorem
`Homogenization.Examples.Periodic.periodicConcrete_comparison` together with the
statement vocabulary copied from the challenge (`SolutionBasic.lean`), and
proves the challenge statement verbatim.

The bridges below are all `private`.  They identify the audit vocabulary with
the repository objects it mirrors:

* triadic cubes and the descendant hierarchy (`Homogenization/Geometry`);
* the fixed `s = 3/4`, `p = q = 2` Besov/Gagliardo quantities against the
  repository's generic ones (`Homogenization/Besov`, `Homogenization/Book/Ch01`,
  `Homogenization/Book/Ch03`);
* the coefficient carrier and its observable σ-algebra
  (`Homogenization/Probability/RegCoeffField`);
* weak `H¹`/`H¹₀` functions and the two weak equations
  (`Homogenization/Sobolev/H1`, `Homogenization/Book/Ch03`);
* the comparison pair, defect and data
  (`Homogenization/Book/Ch05/.../Section57`, `Homogenization/Book/MainResults`).
-/

namespace Homogenization
namespace StatementAudit

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-! ## 1. Triadic cubes -/

private def toRepoCube {d : ℕ} (Q : TriadicCube d) :
    _root_.Homogenization.TriadicCube d :=
  { scale := Q.scale
    index := Q.index }

private def ofRepoCube {d : ℕ} (Q : _root_.Homogenization.TriadicCube d) :
    TriadicCube d :=
  { scale := Q.scale
    index := Q.index }

private theorem interior_ofRepoCube {d : ℕ}
    (Q : _root_.Homogenization.TriadicCube d) :
    (ofRepoCube Q).interior = _root_.Homogenization.openCubeSet Q :=
  rfl

private theorem toRepoCube_injective {d : ℕ} :
    Function.Injective (toRepoCube (d := d)) := by
  intro Q R h
  cases Q
  cases R
  simp [toRepoCube] at h
  simpa using h

private def toRepoCubeEmbedding (d : ℕ) :
    TriadicCube d ↪ _root_.Homogenization.TriadicCube d where
  toFun := toRepoCube
  inj' := toRepoCube_injective

private theorem toRepo_ofRepoCube {d : ℕ}
    (Q : _root_.Homogenization.TriadicCube d) :
    toRepoCube (ofRepoCube Q) = Q := by
  cases Q
  rfl

private theorem children_toRepo {d : ℕ} (Q : TriadicCube d) :
    Q.children.map (toRepoCubeEmbedding d) =
      _root_.Homogenization.childCubes (toRepoCube Q) := by
  ext R
  constructor
  · intro h
    rcases Finset.mem_map.mp h with ⟨R', hR', rfl⟩
    rcases Finset.mem_image.mp hR' with ⟨digits, _hdigits, rfl⟩
    exact Finset.mem_image.mpr ⟨digits, Finset.mem_univ digits, rfl⟩
  · intro h
    rcases Finset.mem_image.mp h with ⟨digits, _hdigits, hR⟩
    refine Finset.mem_map.mpr ?_
    let R' : TriadicCube d :=
      { scale := Q.scale - 1
        index := fun i => 3 * Q.index i + (digits i : ℤ) - 1 }
    refine ⟨R', ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨digits, Finset.mem_univ digits, rfl⟩
    · simpa [R', toRepoCubeEmbedding, toRepoCube] using hR

private theorem descendants_toRepo {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    (Q.descendants n).map (toRepoCubeEmbedding d) =
      _root_.Homogenization.descendantsAtDepth (toRepoCube Q) n := by
  induction n with
  | zero =>
      simp [TriadicCube.descendants, _root_.Homogenization.descendantsAtDepth,
        toRepoCubeEmbedding]
  | succ n ih =>
      ext R
      constructor
      · intro h
        rcases Finset.mem_map.mp h with ⟨R', hR', rfl⟩
        rcases Finset.mem_biUnion.mp hR' with ⟨S, hS, hchild⟩
        have hSrepo : toRepoCube S ∈
            _root_.Homogenization.descendantsAtDepth (toRepoCube Q) n := by
          rw [← ih]
          exact Finset.mem_map.mpr ⟨S, hS, rfl⟩
        have hchildRepo : toRepoCube R' ∈
            _root_.Homogenization.childCubes (toRepoCube S) := by
          rw [← children_toRepo]
          exact Finset.mem_map.mpr ⟨R', hchild, rfl⟩
        exact Finset.mem_biUnion.mpr ⟨toRepoCube S, hSrepo, hchildRepo⟩
      · intro h
        rcases Finset.mem_biUnion.mp h with ⟨Srepo, hSrepo, hchildRepo⟩
        let S : TriadicCube d := ofRepoCube Srepo
        have hS : S ∈ Q.descendants n := by
          have hmap : toRepoCube S ∈
              _root_.Homogenization.descendantsAtDepth (toRepoCube Q) n := by
            simpa [S, toRepo_ofRepoCube] using hSrepo
          rw [← ih] at hmap
          rcases Finset.mem_map.mp hmap with ⟨S', hS', hS'eq⟩
          have : S' = S := toRepoCube_injective hS'eq
          simpa [this] using hS'
        have hchild : ofRepoCube R ∈ S.children := by
          have hmap : toRepoCube (ofRepoCube R) ∈
              _root_.Homogenization.childCubes (toRepoCube S) := by
            simpa [S, toRepo_ofRepoCube] using hchildRepo
          rw [← children_toRepo] at hmap
          rcases Finset.mem_map.mp hmap with ⟨R', hR', hR'eq⟩
          have : R' = ofRepoCube R := toRepoCube_injective hR'eq
          simpa [this] using hR'
        refine Finset.mem_map.mpr ?_
        refine ⟨ofRepoCube R, ?_, ?_⟩
        · exact Finset.mem_biUnion.mpr ⟨S, hS, hchild⟩
        · exact toRepo_ofRepoCube R

private theorem mem_descendants_toRepo {d : ℕ} (Q R : TriadicCube d) (j : ℕ) :
    toRepoCube R ∈
        _root_.Homogenization.descendantsAtDepth (toRepoCube Q) j ↔
      R ∈ Q.descendants j := by
  rw [← descendants_toRepo Q j]
  constructor
  · intro h
    rcases Finset.mem_map.mp h with ⟨R', hR', hR'eq⟩
    have : R' = R := toRepoCube_injective hR'eq
    simpa [this] using hR'
  · intro h
    exact Finset.mem_map.mpr ⟨R, h, rfl⟩

private theorem descendantAverage_toRepo {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (F : _root_.Homogenization.TriadicCube d → ℝ) :
    _root_.Homogenization.descendantsAverage (toRepoCube Q) j F =
      Q.descendantAverage j (fun R => F (toRepoCube R)) := by
  unfold _root_.Homogenization.descendantsAverage TriadicCube.descendantAverage
  rw [← descendants_toRepo Q j]
  simp [Finset.sum_map, toRepoCubeEmbedding]

private theorem originCube_toRepo {d : ℕ} [NeZero d] (m : ℕ) :
    toRepoCube (originCube d m) =
      _root_.Homogenization.Book.MainResults.originCube d m :=
  rfl

/-! ## 2. The fixed `s = 3/4`, `p = q = 2` Sobolev quantities

The repository states the negative and positive fractional-Sobolev quantities
for general exponents.  The audit vocabulary is the specialization at
`s = comparisonS = 3/4` and `p = q = 2`; the conjugate exponent of `2` is `2`,
so the `q = ∞` branch of the repository's dual test norm is never taken. -/

private theorem conj_two : ENNReal.conjExponent (2 : ℝ≥0∞) = 2 := by
  rw [ENNReal.conjExponent]
  rw [show (2 : ℝ≥0∞) - 1 = 1 by
    rw [show (2 : ℝ≥0∞) = 1 + 1 by norm_num, ENNReal.add_sub_cancel_left (by simp)]]
  norm_num

private theorem depthAverage_toRepo {d : ℕ} (Q : TriadicCube d)
    (φ : Vec d → ℝ) (j : ℕ) :
    _root_.Homogenization.cubeBesovDepthAverage (toRepoCube Q) (2 : ℝ≥0∞) φ j =
      Sobolev34.depthAverage Q φ j := by
  rw [_root_.Homogenization.cubeBesovDepthAverage, descendantAverage_toRepo]
  simp only [ENNReal.toReal_ofNat]
  rfl

private theorem depthSeminorm_toRepo {d : ℕ} (Q : TriadicCube d)
    (φ : Vec d → ℝ) (j : ℕ) :
    _root_.Homogenization.cubeBesovDepthSeminorm (toRepoCube Q) comparisonS
        (2 : ℝ≥0∞) φ j = Sobolev34.depthSeminorm Q φ j := by
  rw [_root_.Homogenization.cubeBesovDepthSeminorm, depthAverage_toRepo]
  simp only [ENNReal.toReal_ofNat]
  rfl

private theorem partialTestNorm_toRepo {d : ℕ} (Q : TriadicCube d) (N : ℕ)
    (φ : Vec d → ℝ) :
    _root_.Homogenization.cubeBesovDualTestNorm (toRepoCube Q) comparisonS
        (2 : ℝ≥0∞) (2 : ℝ≥0∞) N φ = Sobolev34.partialTestNorm Q N φ := by
  rw [_root_.Homogenization.cubeBesovDualTestNorm,
    _root_.Homogenization.cubeBesovConjExponent, conj_two, if_neg (by simp)]
  simp only [_root_.Homogenization.cubeBesovPartialNorm,
    _root_.Homogenization.cubeBesovPartialSeminorm,
    _root_.Homogenization.cubeBesovScaleWeight,
    Sobolev34.partialTestNorm, depthSeminorm_toRepo, ENNReal.toReal_ofNat]
  rfl

private theorem locallyL2OnDescendants_toRepo {d : ℕ} (Q : TriadicCube d)
    (φ : Vec d → ℝ) :
    _root_.Homogenization.CubeBesovDualLocalMemLpGlobal (toRepoCube Q)
        (2 : ℝ≥0∞) φ ↔ Sobolev34.LocallyL2OnDescendants Q φ := by
  constructor
  · intro h j R hR
    have hRepo := h j (toRepoCube R) ((mem_descendants_toRepo Q R j).2 hR)
    rwa [_root_.Homogenization.cubeBesovConjExponent, conj_two] at hRepo
  · intro h j R hR
    have hR' : ofRepoCube R ∈ Q.descendants j := by
      refine (mem_descendants_toRepo Q (ofRepoCube R) j).1 ?_
      simpa [toRepo_ofRepoCube] using hR
    have hAudit := h j (ofRepoCube R) hR'
    rw [_root_.Homogenization.cubeBesovConjExponent, conj_two]
    simpa [toRepo_ofRepoCube] using hAudit

private theorem isDualTest_toRepo {d : ℕ} (Q : TriadicCube d) (φ : Vec d → ℝ) :
    _root_.Homogenization.CubeBesovDualFullTest (toRepoCube Q) comparisonS
        (2 : ℝ≥0∞) (2 : ℝ≥0∞) φ ↔ Sobolev34.IsDualTest Q φ := by
  constructor
  · intro h
    exact ⟨fun N => by rw [← partialTestNorm_toRepo]; exact h.1 N,
      (locallyL2OnDescendants_toRepo Q φ).1 h.2⟩
  · intro h
    exact ⟨fun N => by rw [partialTestNorm_toRepo]; exact h.1 N,
      (locallyL2OnDescendants_toRepo Q φ).2 h.2⟩

private theorem negativeNorm_toRepo {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ) :
    _root_.Homogenization.cubeBesovDualFullNorm (toRepoCube Q) comparisonS
        (2 : ℝ≥0∞) (2 : ℝ≥0∞) f = Sobolev34.negativeNorm Q f := by
  rw [_root_.Homogenization.cubeBesovDualFullNorm, Sobolev34.negativeNorm,
    _root_.Homogenization.cubeBesovDualFullNormValueSet]
  congr 1
  ext r
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨φ, (isDualTest_toRepo Q φ).1 hφ, rfl⟩
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨φ, (isDualTest_toRepo Q φ).2 hφ, rfl⟩

private theorem scaledNegativeVectorNorm_toRepo {d : ℕ} (Q : TriadicCube d)
    (F : Vec d → Vec d) :
    _root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedNegativeSobolevVectorNormTwo
        (toRepoCube Q) comparisonS F =
      Sobolev34.scaledNegativeVectorNorm Q F := by
  unfold
    _root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedNegativeSobolevVectorNormTwo
    _root_.Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
    Sobolev34.scaledNegativeVectorNorm Sobolev34.negativeScaleFactor
  rw [show ((toRepoCube Q).scale : ℤ) = Q.scale from rfl]
  congr 1
  exact Finset.sum_congr rfl fun i _hi => negativeNorm_toRepo Q (fun x => F x i)

private theorem kernel_toRepo {d : ℕ} (u : Vec d → ℝ) :
    _root_.Homogenization.Gagliardo.gagliardoKernel comparisonS (2 : ℝ≥0∞) u =
      Sobolev34.kernel u := by
  funext z
  simp [_root_.Homogenization.Gagliardo.gagliardoKernel, Sobolev34.kernel,
    _root_.Homogenization.Gagliardo.kernelExponent, Sobolev34.kernelExponent]

private theorem productMeasure_toRepo {d : ℕ} (Q : TriadicCube d) :
    _root_.Homogenization.Gagliardo.gagliardoCubeMeasure (toRepoCube Q) =
      Sobolev34.productMeasure Q :=
  rfl

private theorem seminorm_toRepo {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) :
    _root_.Homogenization.Book.Ch01.Legacy.fractionalSobolevSeminorm
        (toRepoCube Q) comparisonS (2 : ℝ≥0∞) u = Sobolev34.seminorm Q u := by
  rw [_root_.Homogenization.Book.Ch01.Legacy.fractionalSobolevSeminorm,
    _root_.Homogenization.Gagliardo.cubeGagliardoSeminorm,
    _root_.Homogenization.Gagliardo.cubeGagliardoESeminorm, kernel_toRepo,
    productMeasure_toRepo, Sobolev34.seminorm]

private theorem memH34_toRepo {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) :
    _root_.Homogenization.Book.Ch01.Legacy.MemFractionalSobolev (toRepoCube Q)
        comparisonS (2 : ℝ≥0∞) u ↔ Sobolev34.MemH34 Q u := by
  rw [_root_.Homogenization.Book.Ch01.Legacy.MemFractionalSobolev,
    _root_.Homogenization.Gagliardo.MemWsp, kernel_toRepo, productMeasure_toRepo,
    Sobolev34.MemH34]
  exact Iff.rfl

private theorem forceInH34_toRepo {d : ℕ} (Q : TriadicCube d)
    (g : Vec d → Vec d) :
    ForceInH34 Q g →
      _root_.Homogenization.Book.Ch03.Legacy.ForceSobolevRegularity
        (toRepoCube Q) comparisonS g := by
  intro hg i
  exact (memH34_toRepo Q (fun x => g x i)).2 (hg i)

private theorem scaledForceH34Seminorm_toRepo {d : ℕ} (Q : TriadicCube d)
    (g : Vec d → Vec d) :
    _root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
        (toRepoCube Q) comparisonS g = scaledForceH34Seminorm Q g := by
  have hsum : ∑ i : Fin d,
      _root_.Homogenization.Book.Ch01.Legacy.fractionalSobolevSeminorm
        (toRepoCube Q) comparisonS (2 : ℝ≥0∞) (fun x => g x i)
      = ∑ i : Fin d, Sobolev34.seminorm Q (fun x => g x i) :=
    Finset.sum_congr rfl fun i _hi => seminorm_toRepo Q (fun x => g x i)
  unfold
    _root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
    _root_.Homogenization.cubeBesovScaleWeight scaledForceH34Seminorm
  rw [neg_neg, hsum]
  rfl

/-! ## 3. The coefficient carrier and its observable σ-algebra

The audit carrier `CoefficientField` is a copy of the repository carrier
`Homogenization.RegCoeffField` with the same underlying data.  Its σ-algebra is
the `comap` along `toFun` of the join of the pointwise and probe σ-algebras on
raw fields, which is the repository's join of the two pulled-back lanes; only
the direction `audit → repository` is needed below, and it is what transports
the Dirac law. -/

private def toRepoReg {d : ℕ} (a : CoefficientField d) :
    _root_.Homogenization.RegCoeffField d where
  toFun := a.toFun
  entry_measurable := a.entry_measurable
  entry_locInt := a.entry_locallyIntegrable

/-- The audit copy of the explicit periodic field is the repository's. -/
private theorem toRepoReg_periodicField {d : ℕ} :
    toRepoReg (periodicField d) =
      _root_.Homogenization.Examples.Periodic.mFieldReg (d := d) :=
  rfl

private theorem isProbe_ofRepo {d : ℕ} {φ : Vec d → ℝ}
    (h : _root_.Homogenization.IsProbeR (d := d) φ) : IsProbe φ :=
  ⟨h.measurable, h.bounded, h.hasCompactSupport⟩

private theorem measurable_toFun_audit {d : ℕ} :
    @Measurable (CoefficientField d) (RawCoeffField d) _
      (observableFieldSigma d) CoefficientField.toFun :=
  Measurable.of_comap_le le_rfl

private theorem measurable_apply_entry_audit {d : ℕ} (y : Vec d) (i j : Fin d) :
    Measurable (fun a : CoefficientField d => a.toFun y i j) := by
  have h1 : @Measurable (RawCoeffField d) (Mat d) (pointwiseFieldSigma d)
      (instMeasurableSpaceMat d) (fun f => f y) := measurable_pi_apply y
  have h3 : @Measurable (Mat d) (Fin d → ℝ) (instMeasurableSpaceMat d)
      MeasurableSpace.pi (fun A => A i) := measurable_pi_apply i
  have h2 : @Measurable (Mat d) ℝ (instMeasurableSpaceMat d) _ (fun A => A i j) :=
    (measurable_pi_apply j).comp h3
  have h4 : @Measurable (RawCoeffField d) ℝ (observableFieldSigma d) _
      (fun f => f y i j) := (h2.comp h1).mono le_sup_left le_rfl
  exact h4.comp measurable_toFun_audit

private theorem measurable_entryTest_audit {d : ℕ} (i j : Fin d) {φ : Vec d → ℝ}
    (hφ : IsProbe φ) :
    Measurable (fun a : CoefficientField d => entryTest i j φ a.toFun) := by
  have h : @Measurable (RawCoeffField d) ℝ (probeFieldSigma d) _
      (entryTest i j φ) := by
    intro t ht
    exact MeasurableSpace.measurableSet_generateFrom ⟨i, j, φ, hφ, t, ht, rfl⟩
  exact (h.mono le_sup_right le_rfl).comp measurable_toFun_audit

private theorem measurable_toRepoReg {d : ℕ} :
    Measurable (toRepoReg (d := d)) := by
  refine _root_.Homogenization.measurable_into_regCoeffField' ?_ ?_
  · intro y i j
    exact measurable_apply_entry_audit y i j
  · intro i j φ hφ
    exact measurable_entryTest_audit i j (isProbe_ofRepo hφ)

/-! ## 4. Local ellipticity

The audit predicate drops two clauses that the repository's carries: that the
observation set is measurable and that the restricted entries are
a.e.-strongly-measurable.  Both are unconditionally true on cube interiors, so
the audit hypothesis rebuilds the repository one. -/

private theorem measurableSet_interior {d : ℕ} (Q : TriadicCube d) :
    MeasurableSet Q.interior := by
  have h : Q.interior = ⋂ i : Fin d, (fun x : Vec d => x i) ⁻¹'
      Set.Ioo (((Q.index i : ℝ) - (1 / 2 : ℝ)) * Q.side)
        (((Q.index i : ℝ) + (1 / 2 : ℝ)) * Q.side) := by
    ext x
    simp [TriadicCube.interior, Set.mem_Ioo]
  rw [h]
  exact MeasurableSet.iInter fun i => (measurable_pi_apply i) measurableSet_Ioo

open scoped Classical in
private theorem aestronglyMeasurable_restrict_entry {d : ℕ} (U : Set (Vec d))
    (hU : MeasurableSet U) (a : CoefficientField d) (i j : Fin d) :
    AEStronglyMeasurable
      (fun x : Vec d =>
        _root_.Homogenization.restrictCoeffField U a.toFun x i j)
      (volumeOn U) := by
  classical
  have h : (fun x : Vec d =>
        _root_.Homogenization.restrictCoeffField U a.toFun x i j)
      = fun x => if x ∈ U then a.toFun x i j else 0 := by
    funext x
    by_cases hx : x ∈ U <;>
      simp [_root_.Homogenization.restrictCoeffField, hx]
  rw [h]
  exact (Measurable.ite hU (a.entry_measurable i j)
    measurable_const).aestronglyMeasurable

private theorem toRepo_locallyUniformlyElliptic {d : ℕ}
    {a : CoefficientField d} (ha : LocallyUniformlyElliptic a) :
    _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (toRepoReg a) := by
  intro Q
  obtain ⟨lam, Lam, hlam, hle, hEll⟩ := ha (ofRepoCube Q)
  refine ⟨lam, Lam, hlam, hle, ?_, ?_, ?_⟩
  · rw [← interior_ofRepoCube Q]
    exact measurableSet_interior (ofRepoCube Q)
  · intro i j
    rw [← interior_ofRepoCube Q]
    exact aestronglyMeasurable_restrict_entry _
      (measurableSet_interior (ofRepoCube Q)) a i j
  · exact hEll

/-! ## 5. Weak `H¹` functions, the weak equations, and the comparison pair -/

private def toRepoWeakH1 {d : ℕ} {U : Set (Vec d)} (u : WeakH1 U) :
    _root_.Homogenization.H1Function U where
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
  toWeakH1 :=
    { toFun := u.toH1Function.toFun
      grad := u.toH1Function.grad
      memL2 := u.toH1Function.memL2
      gradMemL2 := u.toH1Function.gradMemL2
      hasWeakGradient := u.toH1Function.hasWeakGradient }
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_compactSupport := u.approx_hasCompactSupport
  approx_supportedIn := u.approx_support_subset
  tendsto_approx := u.tendsto_approx
  tendsto_approx_grad := u.tendsto_approx_grad

private def toRepoWeakH1Origin {d : ℕ} [NeZero d] {m : ℕ}
    (u : WeakH1 (originCube d m).interior) :
    _root_.Homogenization.H1Function
      (_root_.Homogenization.Book.Ch02.cubeDomain
        (_root_.Homogenization.Book.MainResults.originCube d m) : Set (Vec d)) :=
  toRepoWeakH1 u

private def toRepoWeakH10Origin {d : ℕ} [NeZero d] {m : ℕ}
    (u : WeakH10 (originCube d m).interior) :
    _root_.Homogenization.H10Function
      (_root_.Homogenization.Book.Ch02.cubeDomain
        (_root_.Homogenization.Book.MainResults.originCube d m) : Set (Vec d)) :=
  toRepoWeakH10 u

private def toRepoComparisonPair {d : ℕ} [NeZero d] {sigmaBar : ℝ}
    (hsigma : 0 < sigmaBar) {a : CoefficientField d}
    (haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (toRepoReg a))
    {m : ℕ} {g : Vec d → Vec d}
    (pair : ComparisonPair sigmaBar a (originCube d m) g) :
    _root_.Homogenization.Book.Ch05.Section57.assemblyComparisonDatumOfScalar
      sigmaBar hsigma (toRepoReg a) haRepo m g where
  u := toRepoWeakH1Origin pair.u
  v := toRepoWeakH1Origin pair.v
  uWeakSolution := fun φ => pair.u_solves (ofRepoWeakH10 φ)
  vWeakSolution := fun φ => pair.v_solves (ofRepoWeakH10 φ)
  zeroTraceDifference := by
    obtain ⟨w, hw⟩ := pair.sameBoundaryData
    exact ⟨toRepoWeakH10Origin w, hw⟩

/-! ## 6. The defect and the data size -/

private theorem energyNorm_toRepo {d : ℕ} [NeZero d] {a : CoefficientField d}
    (haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (toRepoReg a))
    {m : ℕ} (u : WeakH1 (originCube d m).interior) :
    _root_.Homogenization.Book.Ch03.h1EnergyNormOnCube
        (_root_.Homogenization.Book.MainResults.originCube d m)
        (_root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily
          (toRepoReg a) haRepo)
        (toRepoWeakH1Origin u) =
      energyNorm (originCube d m) a.toFun u :=
  rfl

private theorem constantGradientMismatch_toRepo {d : ℕ} [NeZero d]
    {sigmaBar : ℝ} (hsigma : 0 < sigmaBar) {m : ℕ}
    (u v : WeakH1 (originCube d m).interior) :
    _root_.Homogenization.Book.Ch03.homogenizationComparisonConstantGradientField
        (_root_.Homogenization.Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar
          sigmaBar hsigma)
        (toRepoWeakH1Origin u) (toRepoWeakH1Origin v) =
      constantGradientMismatch sigmaBar u v :=
  rfl

private theorem fluxMismatch_toRepo {d : ℕ} [NeZero d] {sigmaBar : ℝ}
    (hsigma : 0 < sigmaBar) {a : CoefficientField d}
    (haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (toRepoReg a))
    {m : ℕ} (u v : WeakH1 (originCube d m).interior) :
    _root_.Homogenization.Book.Ch03.homogenizationComparisonFluxField
        (_root_.Homogenization.Book.MainResults.originCube d m)
        (_root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily
          (toRepoReg a) haRepo)
        (_root_.Homogenization.Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar
          sigmaBar hsigma)
        (toRepoWeakH1Origin u) (toRepoWeakH1Origin v) =
      fluxMismatch a.toFun sigmaBar u v :=
  rfl

private theorem comparisonDefect_toRepo {d : ℕ} [NeZero d] {sigmaBar : ℝ}
    (hsigma : 0 < sigmaBar) {a : CoefficientField d}
    (haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (toRepoReg a))
    {m : ℕ} {g : Vec d → Vec d}
    (pair : ComparisonPair sigmaBar a (originCube d m) g) :
    _root_.Homogenization.Book.Ch03.Legacy.homogenizationComparisonNegativeSobolevLHS
        (_root_.Homogenization.Book.MainResults.originCube d m)
        (_root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily
          (toRepoReg a) haRepo)
        (_root_.Homogenization.Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar
          sigmaBar hsigma)
        comparisonS (toRepoWeakH1Origin pair.u) (toRepoWeakH1Origin pair.v) =
      comparisonDefect pair := by
  rw [_root_.Homogenization.Book.Ch03.Legacy.homogenizationComparisonNegativeSobolevLHS,
    constantGradientMismatch_toRepo hsigma pair.u pair.v,
    fluxMismatch_toRepo hsigma haRepo pair.u pair.v,
    ← originCube_toRepo (d := d) m,
    scaledNegativeVectorNorm_toRepo, scaledNegativeVectorNorm_toRepo,
    comparisonDefect]

private theorem comparisonData_toRepo {d : ℕ} [NeZero d] {sigmaBar : ℝ}
    {a : CoefficientField d}
    (haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (toRepoReg a))
    {m : ℕ} {g : Vec d → Vec d}
    (pair : ComparisonPair sigmaBar a (originCube d m) g) :
    Real.sqrt sigmaBar *
        _root_.Homogenization.Book.Ch03.h1EnergyNormOnCube
          (_root_.Homogenization.Book.MainResults.originCube d m)
          (_root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily
            (toRepoReg a) haRepo)
          (toRepoWeakH1Origin pair.u) +
      _root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
        (_root_.Homogenization.Book.MainResults.originCube d m) comparisonS g =
      comparisonData pair := by
  rw [energyNorm_toRepo haRepo pair.u, ← originCube_toRepo (d := d) m,
    scaledForceH34Seminorm_toRepo, comparisonData]

namespace PeriodicConcrete

/-- Fixed-exponent homogenization comparison for the Dirac law at the explicit
periodic field `a(x) = m(x) • I`, `m(x) = d + 2 + ∑ i, cos (2 π xᵢ)`.

The constants `C`, `alpha`, `Cscale` are chosen before the dimension datum
`2 ≤ d`, hence depend only on `d`.  The Sobolev exponent is fixed to `3/4`
throughout (`comparisonS`). -/
theorem periodicConcrete_comparison
    {d : ℕ} [NeZero d] :
    ∃ C alpha Cscale : ℝ,
      0 < C ∧ 0 < alpha ∧ 0 < Cscale ∧
      ∀ (_two_le_dim : 2 ≤ d),
        ∃ sigmaBar : ℝ,
          0 < sigmaBar ∧
          ∃ X : CoefficientField d → ℝ,
            IsMinimalScale X Cscale ∧
            ∀ᵐ a ∂periodicLaw d,
              ∀ (_locallyElliptic : LocallyUniformlyElliptic a)
                {m : ℕ} {g : Vec d → Vec d}
                (pair : ComparisonPair sigmaBar a (originCube d m) g),
                X a ≤ (3 : ℝ) ^ m →
                ForceInH34 (originCube d m) g →
                comparisonDefect pair ≤
                  C * ((3 : ℝ) ^ m / X a) ^ (-alpha) * comparisonData pair := by
  obtain ⟨C, alpha, Cscale, hC, halpha, hCscale, hmain⟩ :=
    _root_.Homogenization.Examples.Periodic.periodicConcrete_comparison (d := d)
  refine ⟨C, alpha, Cscale, hC, halpha, hCscale, ?_⟩
  intro two_le_dim
  let Lam : ℝ := 2 * (d : ℝ) + 2
  let Srepo : _root_.Homogenization.Book.MainResults.Setup d :=
    _root_.Homogenization.Examples.Periodic.periodicSetup
      two_le_dim (_root_.Homogenization.Examples.Periodic.mFieldReg (d := d)) 2 Lam
      _root_.Homogenization.Examples.Periodic.mFieldCoeff_periodic
      _root_.Homogenization.Examples.Periodic.mFieldCoeff_isotropic
      _root_.Homogenization.Examples.Periodic.mFieldCoeff_adjointInvariant
      (by norm_num)
      (by
        have hd : (0 : ℝ) ≤ (d : ℝ) := by positivity
        simp only [Lam]
        linarith)
      (fun Q => _root_.Homogenization.Examples.Periodic.mFieldReg_aeeEllipticOn
        (_root_.Homogenization.measurableSet_openCubeSet Q))
  let sigmaBar : ℝ :=
    _root_.Homogenization.Book.Ch05.Section57.barSigmaLimit Srepo.hP Srepo.hStruct
  have hsigma : 0 < sigmaBar := Srepo.barSigmaLimit_pos
  obtain ⟨_sigmaBar, _hsigma, X, hX, hmainS⟩ := hmain two_le_dim
  -- The Dirac law of the audit carrier pushes forward to the repository law.
  have hmap : Measure.map (toRepoReg (d := d)) (periodicLaw d) =
      Measure.dirac (_root_.Homogenization.Examples.Periodic.mFieldReg (d := d)) := by
    rw [periodicLaw, Measure.map_dirac measurable_toRepoReg, toRepoReg_periodicField]
  refine ⟨sigmaBar, hsigma, fun a => X (toRepoReg a), ?_, ?_⟩
  · -- The minimal-scale package transports along the pushforward.
    obtain ⟨hXone, hXtail⟩ := hX
    refine ⟨fun a => hXone (toRepoReg a), ?_⟩
    intro t ht
    have hrepo :
        (Measure.dirac
            (_root_.Homogenization.Examples.Periodic.mFieldReg (d := d))).real
            {b | minimalScaleTailSize d Cscale * t < |X b|} ≤
          (Real.exp (t ^ (d : ℝ)))⁻¹ := hXtail ht
    have hle :
        (periodicLaw d)
            {a | minimalScaleTailSize d Cscale * t < |X (toRepoReg a)|} ≤
          (Measure.dirac
            (_root_.Homogenization.Examples.Periodic.mFieldReg (d := d)))
            {b | minimalScaleTailSize d Cscale * t < |X b|} := by
      have h := Measure.le_map_apply (μ := periodicLaw d) (f := toRepoReg (d := d))
        measurable_toRepoReg.aemeasurable
        {b | minimalScaleTailSize d Cscale * t < |X b|}
      rwa [hmap] at h
    refine le_trans ?_ hrepo
    rw [measureReal_def, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top _ _) hle
  · -- The comparison estimate transports along the pushforward.
    have hmainDirac : ∀ᵐ b ∂(Measure.map (toRepoReg (d := d)) (periodicLaw d)),
        ∀ (haRepo :
            _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField b)
          {m : ℕ} {g : Vec d → Vec d}
          (pair : Srepo.ComparisonPair b haRepo m g),
          X b ≤ (3 : ℝ) ^ m →
          _root_.Homogenization.Book.Ch03.Legacy.ForceSobolevRegularity
            (_root_.Homogenization.Book.MainResults.originCube d m)
            _root_.Homogenization.Book.MainResults.fixedComparisonS g →
          Srepo.comparisonDefect
              _root_.Homogenization.Book.MainResults.fixedComparisonS pair ≤
            C * ((3 : ℝ) ^ m / X b) ^ (-alpha) *
              Srepo.comparisonData
                _root_.Homogenization.Book.MainResults.fixedComparisonS pair := by
      rw [hmap]
      exact hmainS
    have hae := (Measure.tendsto_ae_map (μ := periodicLaw d)
      (measurable_toRepoReg (d := d)).aemeasurable).eventually hmainDirac
    filter_upwards [hae] with a hb
    intro hLocEll m g pair hXm hg
    have haRepo :
        _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
          (toRepoReg a) := toRepo_locallyUniformlyElliptic hLocEll
    have hgRepo :
        _root_.Homogenization.Book.Ch03.Legacy.ForceSobolevRegularity
          (_root_.Homogenization.Book.MainResults.originCube d m)
          _root_.Homogenization.Book.MainResults.fixedComparisonS g := by
      rw [← originCube_toRepo (d := d) m]
      exact forceInH34_toRepo (originCube d m) g hg
    have hstep := hb haRepo (toRepoComparisonPair hsigma haRepo pair) hXm hgRepo
    have hdefect := comparisonDefect_toRepo hsigma haRepo pair
    have hdata := comparisonData_toRepo haRepo pair
    rw [← hdefect, ← hdata]
    exact hstep

end PeriodicConcrete

end

end StatementAudit
end Homogenization
