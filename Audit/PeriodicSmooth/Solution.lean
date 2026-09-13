import Mathlib
import Homogenization.Examples.Periodic.PeriodicSmoothComparison
import Audit.PeriodicSmooth.SolutionBasic

attribute [-instance] Homogenization.instMeasurableSpaceVec
attribute [-instance] Homogenization.instMeasurableSpaceMat
attribute [-instance] Homogenization.instMeasurableSpaceCoeffField

/-!
# Solution: classical (smooth) periodic homogenization comparison

This file is the comparator solution surface for the classical-solution form of
the explicit periodic comparison theorem; the weak `H¹` comparison datum is built
from smooth solutions of the divergence-form equations by integration by parts on
the repository side.

The corresponding challenge imports only Mathlib.  This solution imports the
repository theorem `Homogenization.Examples.Periodic.periodicSmooth_comparison`
and proves the same `StatementAudit` theorem surface; the statement vocabulary
is the verbatim copy carried by `Audit/PeriodicSmooth/SolutionBasic.lean`.

The bridges below are solution-only: they are private, they do not occur in the
audited statement, and they identify the audit vocabulary with the repository
vocabulary.

* `toRepoCube` / `ofRepoCube` — the triadic-cube bridge, together with the
  child/descendant transport needed by the depth averages.
* `Sobolev34.*_eq_repo` — the fixed-exponent (`s = 3/4`, `p = q = 2`)
  identification of the audit Sobolev layer with the repository's generic
  Besov-dual and Gagliardo layers.  The only non-definitional step is
  `ENNReal.conjExponent 2 = 2`, which selects the `else` branch of the
  repository's dual test norm.
* `toRepoField` / `ofRepoField` — the carrier bridge.  The audit carrier
  σ-algebra is `MeasurableSpace.comap CoefficientField.toFun
  (pointwiseFieldSigma d ⊔ probeFieldSigma d)`; the repository's is the join
  `pointwiseSigmaR d ⊔ entryTestSigmaR d`.  `MeasurableSpace.comap_sup` and
  `MeasurableSpace.comap_generateFrom` identify the two, so the identity on the
  underlying data is a measurable equivalence and the Dirac law transports.
* `toRepo_locallyUniformlyElliptic` — reconstruction of the two ellipticity
  side conjuncts (`MeasurableSet` of the cube interior, and
  `AEStronglyMeasurable` of the restricted entries) that the audit statement
  drops.
-/

namespace Homogenization
namespace StatementAudit

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-! ## Solution-only bridges: triadic cubes -/

private def toRepoCube {d : ℕ} (Q : TriadicCube d) :
    _root_.Homogenization.TriadicCube d :=
  { scale := Q.scale
    index := Q.index }

private def ofRepoCube {d : ℕ} (Q : _root_.Homogenization.TriadicCube d) :
    TriadicCube d :=
  { scale := Q.scale
    index := Q.index }

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

private theorem toRepoCube_ofRepoCube {d : ℕ}
    (Q : _root_.Homogenization.TriadicCube d) :
    toRepoCube (ofRepoCube Q) = Q := by
  cases Q
  rfl

private theorem toRepoCube_originCube {d : ℕ} [NeZero d] (m : ℕ) :
    toRepoCube (originCube d m) =
      _root_.Homogenization.Book.MainResults.originCube d m :=
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
            simpa [S, toRepoCube_ofRepoCube] using hSrepo
          rw [← ih] at hmap
          rcases Finset.mem_map.mp hmap with ⟨S', hS', hS'eq⟩
          have : S' = S := toRepoCube_injective hS'eq
          simpa [this] using hS'
        have hchild : ofRepoCube R ∈ S.children := by
          have hmap : toRepoCube (ofRepoCube R) ∈
              _root_.Homogenization.childCubes (toRepoCube S) := by
            simpa [S, toRepoCube_ofRepoCube] using hchildRepo
          rw [← children_toRepo] at hmap
          rcases Finset.mem_map.mp hmap with ⟨R', hR', hR'eq⟩
          have : R' = ofRepoCube R := toRepoCube_injective hR'eq
          simpa [this] using hR'
        refine Finset.mem_map.mpr ?_
        refine ⟨ofRepoCube R, ?_, ?_⟩
        · exact Finset.mem_biUnion.mpr ⟨S, hS, hchild⟩
        · exact toRepoCube_ofRepoCube R

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

/-! ## Solution-only bridges: the fixed-exponent Sobolev layer -/

private theorem conjExponent_two : ENNReal.conjExponent (2 : ℝ≥0∞) = 2 := by
  rw [ENNReal.conjExponent]
  have h : (2 : ℝ≥0∞) - 1 = 1 := by
    rw [show (2 : ℝ≥0∞) = 1 + 1 from by norm_num]
    exact ENNReal.add_sub_cancel_right ENNReal.one_ne_top
  rw [h, inv_one]
  norm_num

private theorem depthAverage_eq_repo {d : ℕ} (Q : TriadicCube d)
    (φ : Vec d → ℝ) (j : ℕ) :
    Sobolev34.depthAverage Q φ j =
      _root_.Homogenization.cubeBesovDepthAverage (toRepoCube Q) 2 φ j := by
  unfold Sobolev34.depthAverage _root_.Homogenization.cubeBesovDepthAverage
  rw [descendantAverage_toRepo]
  rfl

private theorem depthSeminorm_eq_repo {d : ℕ} (Q : TriadicCube d)
    (φ : Vec d → ℝ) (j : ℕ) :
    Sobolev34.depthSeminorm Q φ j =
      _root_.Homogenization.cubeBesovDepthSeminorm (toRepoCube Q) comparisonS 2 φ j := by
  unfold Sobolev34.depthSeminorm _root_.Homogenization.cubeBesovDepthSeminorm
  rw [depthAverage_eq_repo]
  rfl

private theorem partialTestNorm_eq_repo {d : ℕ} (Q : TriadicCube d)
    (N : ℕ) (φ : Vec d → ℝ) :
    Sobolev34.partialTestNorm Q N φ =
      _root_.Homogenization.cubeBesovPartialNorm (toRepoCube Q) comparisonS 2 2 N φ := by
  unfold Sobolev34.partialTestNorm _root_.Homogenization.cubeBesovPartialNorm
    _root_.Homogenization.cubeBesovPartialSeminorm
  have hsum : ∀ j : ℕ, (Sobolev34.depthSeminorm Q φ j) ^ (2 : ℝ) =
      (_root_.Homogenization.cubeBesovDepthSeminorm (toRepoCube Q) comparisonS 2 φ j) ^
        (2 : ℝ≥0∞).toReal := by
    intro j
    rw [depthSeminorm_eq_repo]
    rfl
  simp only [hsum]
  rfl

private theorem dualTestNorm_eq_repo {d : ℕ} (Q : TriadicCube d)
    (N : ℕ) (φ : Vec d → ℝ) :
    Sobolev34.partialTestNorm Q N φ =
      _root_.Homogenization.cubeBesovDualTestNorm (toRepoCube Q) comparisonS 2 2 N φ := by
  rw [partialTestNorm_eq_repo, _root_.Homogenization.cubeBesovDualTestNorm,
    _root_.Homogenization.cubeBesovConjExponent, conjExponent_two,
    if_neg (by simp)]

private theorem locallyL2_eq_repo {d : ℕ} (Q : TriadicCube d) (φ : Vec d → ℝ) :
    Sobolev34.LocallyL2OnDescendants Q φ ↔
      _root_.Homogenization.CubeBesovDualLocalMemLpGlobal (toRepoCube Q) 2 φ := by
  constructor
  · intro h j R hR
    have hR' : ofRepoCube R ∈ Q.descendants j := by
      refine (mem_descendants_toRepo Q (ofRepoCube R) j).1 ?_
      simpa [toRepoCube_ofRepoCube] using hR
    have := h j (ofRepoCube R) hR'
    rw [_root_.Homogenization.cubeBesovConjExponent, conjExponent_two]
    simpa [toRepoCube_ofRepoCube] using! this
  · intro h j R hR
    have hR' := h j (toRepoCube R) ((mem_descendants_toRepo Q R j).2 hR)
    rw [_root_.Homogenization.cubeBesovConjExponent, conjExponent_two] at hR'
    exact hR'

private theorem isDualTest_eq_repo {d : ℕ} (Q : TriadicCube d) (φ : Vec d → ℝ) :
    Sobolev34.IsDualTest Q φ ↔
      _root_.Homogenization.CubeBesovDualFullTest (toRepoCube Q) comparisonS 2 2 φ := by
  constructor
  · intro h
    refine ⟨fun N => ?_, (locallyL2_eq_repo Q φ).1 h.2⟩
    rw [← dualTestNorm_eq_repo]
    exact h.1 N
  · intro h
    refine ⟨fun N => ?_, (locallyL2_eq_repo Q φ).2 h.2⟩
    rw [dualTestNorm_eq_repo]
    exact h.1 N

private theorem negativeNorm_eq_repo {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ) :
    Sobolev34.negativeNorm Q f =
      _root_.Homogenization.cubeBesovDualFullNorm (toRepoCube Q) comparisonS 2 2 f := by
  unfold Sobolev34.negativeNorm _root_.Homogenization.cubeBesovDualFullNorm
    _root_.Homogenization.cubeBesovDualFullNormValueSet
  congr 1
  ext r
  constructor
  · rintro ⟨φ, hφ, hr⟩
    exact ⟨φ, (isDualTest_eq_repo Q φ).1 hφ, hr⟩
  · rintro ⟨φ, hφ, hr⟩
    exact ⟨φ, (isDualTest_eq_repo Q φ).2 hφ, hr⟩

private theorem scaledNegativeVectorNorm_eq_repo {d : ℕ} (Q : TriadicCube d)
    (F : Vec d → Vec d) :
    Sobolev34.scaledNegativeVectorNorm Q F =
      _root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedNegativeSobolevVectorNormTwo
        (toRepoCube Q) comparisonS F := by
  unfold Sobolev34.scaledNegativeVectorNorm
    _root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedNegativeSobolevVectorNormTwo
    _root_.Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
  congr 1
  exact Finset.sum_congr rfl fun i _hi => negativeNorm_eq_repo Q (fun x => F x i)

private theorem scaledForceH34Seminorm_eq_repo {d : ℕ} (Q : TriadicCube d)
    (g : Vec d → Vec d) :
    scaledForceH34Seminorm Q g =
      _root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
        (toRepoCube Q) comparisonS g := by
  unfold scaledForceH34Seminorm
    _root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
    _root_.Homogenization.cubeBesovScaleWeight
  rw [neg_neg]
  rfl

private theorem forceInH34_eq_repo {d : ℕ} (Q : TriadicCube d)
    (g : Vec d → Vec d) :
    ForceInH34 Q g ↔
      _root_.Homogenization.Book.Ch03.Legacy.ForceSobolevRegularity
        (toRepoCube Q) comparisonS g :=
  Iff.rfl

/-! ## Solution-only bridges: the carrier

The audit carrier `CoefficientField` is a statement-level copy of the repository
carrier `Homogenization.RegCoeffField` with the same underlying data.  The audit
σ-algebra is the comap along `toFun` of the join of the pointwise and probe
σ-algebras on raw fields, and the repository's is the join of the two comaps;
`MeasurableSpace.comap_sup` and `MeasurableSpace.comap_generateFrom` identify
them, so the identity on the underlying data is a measurable equivalence. -/

private def toRepoField {d : ℕ} (a : CoefficientField d) :
    _root_.Homogenization.RegCoeffField d where
  toFun := a.toFun
  entry_measurable := a.entry_measurable
  entry_locInt := a.entry_locallyIntegrable

private def ofRepoField {d : ℕ} (a : _root_.Homogenization.RegCoeffField d) :
    CoefficientField d where
  toFun := a.toFun
  entry_measurable := a.entry_measurable
  entry_locallyIntegrable := a.entry_locInt

@[simp] private theorem toRepoField_ofRepoField {d : ℕ}
    (a : _root_.Homogenization.RegCoeffField d) :
    toRepoField (ofRepoField a) = a := rfl

@[simp] private theorem ofRepoField_toRepoField {d : ℕ} (a : CoefficientField d) :
    ofRepoField (toRepoField a) = a := rfl

private theorem isProbe_toRepo {d : ℕ} {φ : Vec d → ℝ} (h : IsProbe φ) :
    _root_.Homogenization.IsProbeR φ :=
  ⟨h.measurable, h.bounded, h.compactSupport⟩

private theorem isProbe_ofRepo {d : ℕ} {φ : Vec d → ℝ}
    (h : _root_.Homogenization.IsProbeR (d := d) φ) : IsProbe φ :=
  ⟨h.measurable, h.bounded, h.hasCompactSupport⟩

private theorem measurable_carrier_toFun {d : ℕ} :
    @Measurable (CoefficientField d) (RawCoeffField d) _
      (observableFieldSigma d) CoefficientField.toFun :=
  Measurable.of_comap_le le_rfl

private theorem measurable_apply_entry_audit {d : ℕ} (y : Vec d) (i j : Fin d) :
    Measurable (fun a : CoefficientField d => a.toFun y i j) := by
  have hpt : @Measurable (CoefficientField d) (RawCoeffField d) _
      (pointwiseFieldSigma d) CoefficientField.toFun :=
    measurable_carrier_toFun.mono le_rfl le_sup_left
  have h1 : @Measurable (RawCoeffField d) (Mat d) (pointwiseFieldSigma d)
      (instMeasurableSpaceMat d) (fun f => f y) := measurable_pi_apply y
  have h3 : @Measurable (Mat d) (Fin d → ℝ) (instMeasurableSpaceMat d)
      MeasurableSpace.pi (fun A => A i) := measurable_pi_apply i
  have h2 : @Measurable (Mat d) ℝ (instMeasurableSpaceMat d) _ (fun A => A i j) :=
    (measurable_pi_apply j).comp h3
  exact (h2.comp h1).comp hpt

private theorem measurable_entryTest_raw {d : ℕ} (i j : Fin d) {φ : Vec d → ℝ}
    (hφ : IsProbe φ) :
    @Measurable (RawCoeffField d) ℝ (observableFieldSigma d) _
      (entryTest i j φ) := by
  have h : @Measurable (RawCoeffField d) ℝ (probeFieldSigma d) _
      (entryTest i j φ) := by
    intro t ht
    exact MeasurableSpace.measurableSet_generateFrom ⟨i, j, φ, hφ, t, ht, rfl⟩
  exact h.mono le_sup_right le_rfl

private theorem measurable_toRepoField {d : ℕ} :
    Measurable (toRepoField (d := d)) := by
  refine _root_.Homogenization.measurable_into_regCoeffField' ?_ ?_
  · intro y i j
    exact measurable_apply_entry_audit y i j
  · intro i j φ hφ
    exact (measurable_entryTest_raw i j (isProbe_ofRepo hφ)).comp
      measurable_carrier_toFun

private theorem measurable_ofRepoField {d : ℕ} :
    Measurable (ofRepoField (d := d)) := by
  refine Measurable.of_comap_le ?_
  have hcomap :
      MeasurableSpace.comap (ofRepoField (d := d))
          (instMeasurableSpaceCoefficientField d)
        = MeasurableSpace.comap
            (fun a : _root_.Homogenization.RegCoeffField d => a.toFun)
            (observableFieldSigma d) := by
    rw [instMeasurableSpaceCoefficientField, MeasurableSpace.comap_comp]
    rfl
  rw [hcomap, observableFieldSigma, MeasurableSpace.comap_sup]
  refine sup_le ?_ ?_
  · exact _root_.Homogenization.pointwiseSigmaR_le d
  · rw [probeFieldSigma, MeasurableSpace.comap_generateFrom]
    refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨t, ⟨i, j, φ, hφ, u, hu, rfl⟩, rfl⟩
    exact _root_.Homogenization.measurable_entryTestR i j (isProbe_toRepo hφ) hu

/-- The audit carrier and the repository carrier are measurably equivalent via
the identity on the underlying data. -/
private def fieldEquiv (d : ℕ) :
    _root_.Homogenization.RegCoeffField d ≃ᵐ CoefficientField d where
  toEquiv :=
    { toFun := ofRepoField
      invFun := toRepoField
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  measurable_toFun := measurable_ofRepoField
  measurable_invFun := measurable_toRepoField

private theorem dirac_eq_map_ofRepoField {d : ℕ} (a₀ : CoefficientField d) :
    (Measure.dirac a₀ : Measure (CoefficientField d)) =
      Measure.map (ofRepoField (d := d)) (Measure.dirac (toRepoField a₀)) := by
  rw [Measure.map_dirac' measurable_ofRepoField, ofRepoField_toRepoField]

private theorem ae_dirac_iff_repo {d : ℕ} (a₀ : CoefficientField d)
    {p : CoefficientField d → Prop} :
    (∀ᵐ a ∂(Measure.dirac a₀ : Measure (CoefficientField d)), p a) ↔
      ∀ᵐ b ∂(Measure.dirac (toRepoField a₀) :
        Measure (_root_.Homogenization.RegCoeffField d)), p (ofRepoField b) := by
  rw [dirac_eq_map_ofRepoField a₀,
    show Measure.map (ofRepoField (d := d)) (Measure.dirac (toRepoField a₀))
        = Measure.map (fieldEquiv d) (Measure.dirac (toRepoField a₀)) from rfl,
    ← MeasurableEquiv.map_ae]
  exact Filter.eventually_map

private theorem dirac_real_eq {d : ℕ} (a₀ : CoefficientField d)
    (E : Set (CoefficientField d)) :
    (Measure.dirac a₀ : Measure (CoefficientField d)).real E =
      (Measure.dirac (toRepoField a₀) :
        Measure (_root_.Homogenization.RegCoeffField d)).real
        (ofRepoField ⁻¹' E) := by
  rw [measureReal_def, measureReal_def, dirac_eq_map_ofRepoField a₀]
  congr 1
  exact (fieldEquiv d).map_apply E

/-! ## Solution-only bridges: ellipticity

The audit hypothesis `LocallyUniformlyElliptic` drops the `MeasurableSet` and
`AEStronglyMeasurable` conjuncts of the repository's `AEEllipticOn`.  Both are
provable outright, so the weaker audit hypothesis still yields the repository
hypothesis. -/

private theorem aestronglyMeasurable_restrict_entry {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) (a : CoefficientField d) (i j : Fin d) :
    AEStronglyMeasurable
      (fun x : Vec d =>
        _root_.Homogenization.restrictCoeffField U a.toFun x i j)
      (volume.restrict U) := by
  have hEq : (fun x : Vec d =>
      _root_.Homogenization.restrictCoeffField U a.toFun x i j)
      = Set.indicator U (fun x => a.toFun x i j) := by
    funext x
    by_cases hx : x ∈ U <;>
      simp [_root_.Homogenization.restrictCoeffField, hx, Set.indicator_of_mem,
        Set.indicator_of_notMem]
  rw [hEq]
  exact ((a.entry_measurable i j).indicator hU).stronglyMeasurable.aestronglyMeasurable

private theorem toRepo_locallyUniformlyElliptic {d : ℕ}
    {a : CoefficientField d} (ha : LocallyUniformlyElliptic a) :
    _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (toRepoField a) := by
  intro Q
  obtain ⟨lam, Lam, hlam, hle, hell⟩ := ha (ofRepoCube Q)
  refine ⟨lam, Lam, hlam, hle, ?_, ?_, ?_⟩
  · exact _root_.Homogenization.measurableSet_openCubeSet Q
  · intro i j
    exact aestronglyMeasurable_restrict_entry
      (_root_.Homogenization.measurableSet_openCubeSet Q) a i j
  · exact hell

/-! ## The audited theorem -/

namespace PeriodicSmooth

/-- Fixed-exponent homogenization comparison for smooth classical solution data
over the explicit periodic coefficient field `a(x) = m(x) • I`, stated for its
Dirac law.  The constants are chosen before the dimension data, hence depend
only on `d`. -/
theorem periodicSmooth_comparison
    {d : ℕ} [NeZero d] :
    ∃ C alpha Cscale : ℝ,
      0 < C ∧ 0 < alpha ∧ 0 < Cscale ∧
      ∀ (_two_le_dim : 2 ≤ d),
        ∃ sigmaBar : ℝ,
          0 < sigmaBar ∧
          ∃ X : CoefficientField d → ℝ,
            IsMinimalScale (periodicLaw d) X Cscale ∧
            ∀ᵐ a ∂periodicLaw d,
              ∀ (_locallyElliptic : LocallyUniformlyElliptic a)
                {m : ℕ} {g : Vec d → Vec d}
                (pair : ComparisonPair sigmaBar a (originCube d m) g),
                X a ≤ (3 : ℝ) ^ m →
                ForceInH34 (originCube d m) g →
                comparisonDefect pair ≤
                  C * ((3 : ℝ) ^ m / X a) ^ (-alpha) * comparisonData pair := by
  obtain ⟨C, alpha, Cscale, hC, halpha, hCscale, hmain⟩ :=
    _root_.Homogenization.Examples.Periodic.periodicSmooth_comparison (d := d)
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
        nlinarith [show 0 ≤ (d : ℝ) by exact_mod_cast Nat.zero_le d])
      (fun Q => _root_.Homogenization.Examples.Periodic.mFieldReg_aeeEllipticOn
        (_root_.Homogenization.measurableSet_openCubeSet Q))
  obtain ⟨sigmaBar, hsigma, X, hX, hmainS⟩ := hmain two_le_dim
  refine ⟨sigmaBar, hsigma, fun a => X (toRepoField a), ?_, ?_⟩
  · -- the minimal-scale package transports along the carrier equivalence
    have hXmin :
        (∀ b, 1 ≤ X b) ∧
          _root_.Homogenization.Book.Ch04.IsBigO
            (Measure.dirac
              (_root_.Homogenization.Examples.Periodic.mFieldReg (d := d)))
            (_root_.Homogenization.Book.Ch04.gammaSigma ((d : ℕ) : ℝ)) X
            (minimalScaleTailSize d Cscale) := by
      simpa [Srepo, Lam, minimalScaleTailSize, thetaHat, coarseUpperBound,
        coarseInverseLowerBound,
        _root_.Homogenization.Book.MainResults.Setup.IsMinimalScale,
        _root_.Homogenization.Book.MainResults.Setup.thetaHat,
        _root_.Homogenization.Book.Ch05.Section57.mainResultsThetaHat,
        _root_.Homogenization.Book.Ch05.Section57.uniformUpperBlockConst,
        _root_.Homogenization.Book.Ch05.Section57.uniformLowerInvBlockConst,
        _root_.Homogenization.Examples.Periodic.periodicSetup,
        _root_.Homogenization.Examples.Periodic.dirac_setup,
        _root_.Homogenization.Examples.Periodic.diracCoeffLaw] using hX
    refine ⟨fun a => hXmin.1 (toRepoField a), ?_⟩
    intro t ht
    have hrepo := hXmin.2 ht
    show (Measure.dirac (periodicField d)).real _ ≤ _
    rw [dirac_real_eq (periodicField d)]
    exact hrepo
  · have hmainDirac :
        ∀ᵐ b ∂(Measure.dirac
            (_root_.Homogenization.Examples.Periodic.mFieldReg (d := d)) :
            Measure (_root_.Homogenization.RegCoeffField d)),
          ∀ (_haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField b)
            {m : ℕ} {u v : Vec d → ℝ} {g : Vec d → Vec d}
            (_hu : ContDiff ℝ (⊤ : ℕ∞) u)
            (_hv : ContDiff ℝ (⊤ : ℕ∞) v)
            (_hg : ContDiff ℝ 1 g)
            (_haflux : ContDiff ℝ 1
              (fun x => _root_.Homogenization.matVecMul (b x)
                (_root_.Homogenization.euclideanGradient u x)))
            (_hvflux : ContDiff ℝ 1
              (fun x => _root_.Homogenization.matVecMul
                (_root_.Homogenization.scalarMatrix (d := d) sigmaBar)
                (_root_.Homogenization.euclideanGradient v x)))
            (_hlower_zero : ∀ i : Fin d, ∀ x : Vec d,
              (u - v)
                (_root_.Homogenization.cubeLowerFaceProjection
                  (_root_.Homogenization.Book.MainResults.originCube d m) i x) = 0)
            (_hupper_zero : ∀ i : Fin d, ∀ x : Vec d,
              (u - v)
                (_root_.Homogenization.cubeUpperFaceProjection
                  (_root_.Homogenization.Book.MainResults.originCube d m) i x) = 0)
            (_hu_div : ∀ x : Vec d,
              _root_.Homogenization.Examples.Periodic.euclideanDivergence
                  (fun y => _root_.Homogenization.matVecMul (b y)
                    (_root_.Homogenization.euclideanGradient u y)) x =
                _root_.Homogenization.Examples.Periodic.euclideanDivergence g x)
            (_hv_div : ∀ x : Vec d,
              _root_.Homogenization.Examples.Periodic.euclideanDivergence
                  (fun y => _root_.Homogenization.matVecMul
                    (_root_.Homogenization.scalarMatrix (d := d) sigmaBar)
                    (_root_.Homogenization.euclideanGradient v y)) x =
                _root_.Homogenization.Examples.Periodic.euclideanDivergence g x),
            X b ≤ (3 : ℝ) ^ m →
            _root_.Homogenization.Book.Ch03.Legacy.ForceSobolevRegularity
              (_root_.Homogenization.Book.MainResults.originCube d m)
              _root_.Homogenization.Book.MainResults.fixedComparisonS g →
            _root_.Homogenization.Examples.Periodic.classicalComparisonDefect
                (_root_.Homogenization.scalarMatrix (d := d) sigmaBar)
                _root_.Homogenization.Book.MainResults.fixedComparisonS b.toFun m u v ≤
              C * ((3 : ℝ) ^ m / X b) ^ (-alpha) *
                _root_.Homogenization.Examples.Periodic.classicalComparisonData
                  sigmaBar _root_.Homogenization.Book.MainResults.fixedComparisonS
                  b.toFun m g u := by
      simpa [Srepo, Lam,
        _root_.Homogenization.Examples.Periodic.periodicSetup,
        _root_.Homogenization.Examples.Periodic.dirac_setup,
        _root_.Homogenization.Examples.Periodic.diracCoeffLaw] using hmainS
    show ∀ᵐ a ∂(Measure.dirac (periodicField d)), _
    rw [ae_dirac_iff_repo (periodicField d)]
    filter_upwards [hmainDirac] with b hmain_b
    intro ha m g pair hXm hgsob
    have hstep := hmain_b (toRepo_locallyUniformlyElliptic ha)
      pair.u_smooth pair.v_smooth pair.force_smooth
      pair.flux_smooth pair.homogenizedFlux_smooth
      (fun i x => pair.agree_on_lowerFaces i x)
      (fun i x => pair.agree_on_upperFaces i x)
      pair.u_solves pair.v_solves hXm
      ((forceInH34_eq_repo (originCube d m) g).1 hgsob)
    calc
      comparisonDefect pair
          = _root_.Homogenization.Examples.Periodic.classicalComparisonDefect
              (_root_.Homogenization.scalarMatrix (d := d) sigmaBar)
              _root_.Homogenization.Book.MainResults.fixedComparisonS
              b.toFun m pair.u pair.v := by
            unfold comparisonDefect
              _root_.Homogenization.Examples.Periodic.classicalComparisonDefect
            rw [scaledNegativeVectorNorm_eq_repo, scaledNegativeVectorNorm_eq_repo,
              toRepoCube_originCube]
            rfl
      _ ≤ C * ((3 : ℝ) ^ m / X b) ^ (-alpha) *
              _root_.Homogenization.Examples.Periodic.classicalComparisonData
                sigmaBar _root_.Homogenization.Book.MainResults.fixedComparisonS
                b.toFun m g pair.u := hstep
      _ = C * ((3 : ℝ) ^ m / X (toRepoField (ofRepoField b))) ^ (-alpha) *
              comparisonData pair := by
            unfold comparisonData
              _root_.Homogenization.Examples.Periodic.classicalComparisonData
            rw [scaledForceH34Seminorm_eq_repo, toRepoCube_originCube]
            rfl

end PeriodicSmooth

end

end StatementAudit
end Homogenization
