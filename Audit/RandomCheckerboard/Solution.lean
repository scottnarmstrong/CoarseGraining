import Mathlib
import Homogenization.Examples.RandomCheckerboard.CarrierLaw
import Audit.RandomCheckerboard.SolutionBasic

attribute [-instance] Homogenization.instMeasurableSpaceVec
attribute [-instance] Homogenization.instMeasurableSpaceMat
attribute [-instance] Homogenization.instMeasurableSpaceCoeffField

/-!
# Solution: random Bernoulli checkerboard homogenization comparison

This file is the comparator solution surface for the random Bernoulli
checkerboard specialization of the quenched homogenization comparison theorem.

The corresponding challenge imports only Mathlib.  This solution imports the
repository theorem
`Homogenization.Examples.RandomCheckerboard.randomCheckerboard_quenchedComparison`
and proves the same `StatementAudit` theorem surface, whose statement
vocabulary is the byte-identical copy of the challenge vocabulary kept in
`Audit/RandomCheckerboard/SolutionBasic.lean`.

The bridges below are all `private`.  They fall into the following groups.

* **Triadic cubes.**  The audit cube type is a statement-level copy of the
  repository one; the identity on `(scale, index)` is an embedding, and the
  descendant Finsets correspond under it.
* **Fixed-exponent Sobolev quantities.**  The audit's `Sobolev34` namespace is
  the repository's generic Besov/Gagliardo machinery specialized at
  `s = 3/4`, `p = q = 2`; the specialization uses
  `ENNReal.conjExponent 2 = 2`, `(2 : ℝ≥0∞).toReal = 2`, `neg_neg` and
  `smul_eq_mul`.
* **The carrier.**  The audit carrier σ-algebra is the pullback along `toFun`
  of the observable σ-algebra on raw fields; it is transported to the
  repository's `pointwiseSigmaR ⊔ entryTestSigmaR` by `comap_sup` and
  `comap_generateFrom`, giving a measurable equivalence of the two carriers.
* **Ellipticity.**  The audit hypothesis drops the `MeasurableSet` and
  `AEStronglyMeasurable` conjuncts of the repository's `AEEllipticOn`; both are
  reconstructed here (cube interiors are open, carrier entries are Borel).
* **The checkerboard law.**  The audit's region-form `conductance` is proved
  pointwise equal to the repository's `Classical.choose`-based `scalarAt`,
  lifted to equal carrier elements by proof irrelevance, and then to equal
  pushforward laws.
-/

namespace Homogenization
namespace StatementAudit

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

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
    (Q.children).map (toRepoCubeEmbedding d) =
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

private theorem toRepoCube_originCube {d : ℕ} [NeZero d] (m : ℕ) :
    toRepoCube (originCube d m) =
      _root_.Homogenization.Book.MainResults.originCube d m :=
  rfl

/-! ## 2. Fixed-exponent Sobolev quantities -/

private theorem toReal_two : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by
  norm_num

private theorem conjExponent_two :
    _root_.Homogenization.cubeBesovConjExponent (2 : ℝ≥0∞) = 2 := by
  rw [_root_.Homogenization.cubeBesovConjExponent, ENNReal.conjExponent]
  have h : (2 : ℝ≥0∞) - 1 = 1 := by
    rw [show (2 : ℝ≥0∞) = 1 + 1 from by norm_num]
    exact ENNReal.add_sub_cancel_right ENNReal.one_ne_top
  rw [h, inv_one]
  norm_num

private theorem conjExponent_two_ne_top :
    _root_.Homogenization.cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
  rw [conjExponent_two]
  norm_num

private theorem oscillation_toRepo {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) :
    _root_.Homogenization.cubeBesovOscillation (toRepoCube Q) (2 : ℝ≥0∞) u =
      Q.l2Norm (Q.fluctuation u) :=
  rfl

private theorem depthAverage_toRepo {d : ℕ} (Q : TriadicCube d)
    (φ : Vec d → ℝ) (j : ℕ) :
    _root_.Homogenization.cubeBesovDepthAverage (toRepoCube Q) (2 : ℝ≥0∞) φ j =
      Sobolev34.depthAverage Q φ j := by
  rw [_root_.Homogenization.cubeBesovDepthAverage, descendantAverage_toRepo,
    Sobolev34.depthAverage]
  refine congrArg _ ?_
  funext R
  rw [oscillation_toRepo, toReal_two]

private theorem depthSeminorm_toRepo {d : ℕ} (Q : TriadicCube d)
    (φ : Vec d → ℝ) (j : ℕ) :
    _root_.Homogenization.cubeBesovDepthSeminorm (toRepoCube Q) comparisonS
        (2 : ℝ≥0∞) φ j =
      Sobolev34.depthSeminorm Q φ j := by
  rw [_root_.Homogenization.cubeBesovDepthSeminorm, Sobolev34.depthSeminorm,
    depthAverage_toRepo, toReal_two]
  rfl

private theorem partialNorm_toRepo {d : ℕ} (Q : TriadicCube d) (N : ℕ)
    (φ : Vec d → ℝ) :
    _root_.Homogenization.cubeBesovPartialNorm (toRepoCube Q) comparisonS
        (2 : ℝ≥0∞) (2 : ℝ≥0∞) N φ =
      Sobolev34.partialTestNorm Q N φ := by
  rw [_root_.Homogenization.cubeBesovPartialNorm,
    _root_.Homogenization.cubeBesovPartialSeminorm, Sobolev34.partialTestNorm,
    toReal_two]
  refine congrArg₂ _ ?_ rfl
  refine congrArg (fun s : ℝ => s ^ (1 / (2 : ℝ))) ?_
  exact Finset.sum_congr rfl fun j _ => by rw [depthSeminorm_toRepo]

private theorem dualTestNorm_toRepo {d : ℕ} (Q : TriadicCube d) (N : ℕ)
    (φ : Vec d → ℝ) :
    _root_.Homogenization.cubeBesovDualTestNorm (toRepoCube Q) comparisonS
        (2 : ℝ≥0∞) (2 : ℝ≥0∞) N φ =
      Sobolev34.partialTestNorm Q N φ := by
  rw [_root_.Homogenization.cubeBesovDualTestNorm, if_neg conjExponent_two_ne_top,
    conjExponent_two, partialNorm_toRepo]

private theorem localMemLp_toRepo {d : ℕ} (Q : TriadicCube d) (φ : Vec d → ℝ) :
    _root_.Homogenization.CubeBesovDualLocalMemLpGlobal (toRepoCube Q)
        (2 : ℝ≥0∞) φ ↔
      Sobolev34.LocallyL2OnDescendants Q φ := by
  rw [_root_.Homogenization.CubeBesovDualLocalMemLpGlobal,
    Sobolev34.LocallyL2OnDescendants, conjExponent_two]
  constructor
  · intro h j R hR
    exact h j (toRepoCube R) ((mem_descendants_toRepo Q R j).2 hR)
  · intro h j R hR
    have hR' : ofRepoCube R ∈ Q.descendants j := by
      refine (mem_descendants_toRepo Q (ofRepoCube R) j).1 ?_
      simpa [toRepo_ofRepoCube] using hR
    have := h j (ofRepoCube R) hR'
    simpa [toRepo_ofRepoCube] using! this

private theorem isDualTest_toRepo {d : ℕ} (Q : TriadicCube d) (φ : Vec d → ℝ) :
    _root_.Homogenization.CubeBesovDualFullTest (toRepoCube Q) comparisonS
        (2 : ℝ≥0∞) (2 : ℝ≥0∞) φ ↔
      Sobolev34.IsDualTest Q φ := by
  constructor
  · intro h
    refine ⟨fun N => ?_, (localMemLp_toRepo Q φ).1 h.2⟩
    rw [← dualTestNorm_toRepo]
    exact h.1 N
  · intro h
    refine ⟨fun N => ?_, (localMemLp_toRepo Q φ).2 h.2⟩
    rw [dualTestNorm_toRepo]
    exact h.1 N

private theorem negativeNorm_toRepo {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ) :
    _root_.Homogenization.cubeBesovDualFullNorm (toRepoCube Q) comparisonS
        (2 : ℝ≥0∞) (2 : ℝ≥0∞) f =
      Sobolev34.negativeNorm Q f := by
  rw [_root_.Homogenization.cubeBesovDualFullNorm, Sobolev34.negativeNorm,
    _root_.Homogenization.cubeBesovDualFullNormValueSet]
  refine congrArg _ ?_
  ext r
  constructor
  · rintro ⟨φ, hφ, hr⟩
    exact ⟨φ, (isDualTest_toRepo Q φ).1 hφ, hr⟩
  · rintro ⟨φ, hφ, hr⟩
    exact ⟨φ, (isDualTest_toRepo Q φ).2 hφ, hr⟩

private theorem scaledNegativeVectorNorm_toRepo {d : ℕ} (Q : TriadicCube d)
    (F : Vec d → Vec d) :
    _root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedNegativeSobolevVectorNormTwo
        (toRepoCube Q) comparisonS F =
      Sobolev34.scaledNegativeVectorNorm Q F := by
  unfold
    _root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedNegativeSobolevVectorNormTwo
    _root_.Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
    Sobolev34.scaledNegativeVectorNorm
  refine congrArg₂ _ rfl ?_
  exact Finset.sum_congr rfl fun i _ =>
    negativeNorm_toRepo Q (fun x => F x i)

private theorem scaledNegativeVectorNorm_originCube {d : ℕ} [NeZero d] (m : ℕ)
    (F : Vec d → Vec d) :
    _root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedNegativeSobolevVectorNormTwo
        (_root_.Homogenization.Book.MainResults.originCube d m) comparisonS F =
      Sobolev34.scaledNegativeVectorNorm (originCube d m) F :=
  scaledNegativeVectorNorm_toRepo (originCube d m) F

private theorem gagliardoKernel_toRepo {d : ℕ} (u : Vec d → ℝ) :
    _root_.Homogenization.Gagliardo.gagliardoKernel comparisonS (2 : ℝ≥0∞) u =
      Sobolev34.kernel u := by
  funext z
  rw [_root_.Homogenization.Gagliardo.gagliardoKernel, Sobolev34.kernel,
    _root_.Homogenization.Gagliardo.kernelExponent, Sobolev34.kernelExponent,
    toReal_two, smul_eq_mul]

private theorem productMeasure_toRepo {d : ℕ} (Q : TriadicCube d) :
    _root_.Homogenization.Gagliardo.gagliardoCubeMeasure (toRepoCube Q) =
      Sobolev34.productMeasure Q :=
  rfl

private theorem seminorm_toRepo {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) :
    _root_.Homogenization.Book.Ch01.Legacy.fractionalSobolevSeminorm
        (toRepoCube Q) comparisonS (2 : ℝ≥0∞) u =
      Sobolev34.seminorm Q u := by
  rw [_root_.Homogenization.Book.Ch01.Legacy.fractionalSobolevSeminorm,
    _root_.Homogenization.Gagliardo.cubeGagliardoSeminorm,
    _root_.Homogenization.Gagliardo.cubeGagliardoESeminorm, Sobolev34.seminorm,
    gagliardoKernel_toRepo, productMeasure_toRepo]

private theorem memH34_toRepo {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) :
    _root_.Homogenization.Book.Ch01.Legacy.MemFractionalSobolev (toRepoCube Q)
        comparisonS (2 : ℝ≥0∞) u ↔
      Sobolev34.MemH34 Q u := by
  rw [_root_.Homogenization.Book.Ch01.Legacy.MemFractionalSobolev,
    Sobolev34.MemH34, _root_.Homogenization.Gagliardo.MemWsp,
    gagliardoKernel_toRepo, productMeasure_toRepo]
  exact Iff.rfl

private theorem forceInH34_toRepo {d : ℕ} (Q : TriadicCube d)
    (g : Vec d → Vec d) (hg : ForceInH34 Q g) :
    _root_.Homogenization.Book.Ch03.Legacy.ForceSobolevRegularity
      (toRepoCube Q) comparisonS g := by
  intro i
  exact (memH34_toRepo Q (fun x => g x i)).2 (hg i)

private theorem scaledForceH34Seminorm_toRepo {d : ℕ} (Q : TriadicCube d)
    (g : Vec d → Vec d) :
    _root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
        (toRepoCube Q) comparisonS g =
      scaledForceH34Seminorm Q g := by
  rw [_root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo,
    scaledForceH34Seminorm, _root_.Homogenization.cubeBesovScaleWeight, neg_neg]
  refine congrArg₂ _ rfl ?_
  exact Finset.sum_congr rfl fun i _ => seminorm_toRepo Q (fun x => g x i)

private theorem forceInH34_originCube {d : ℕ} [NeZero d] (m : ℕ)
    (g : Vec d → Vec d) (hg : ForceInH34 (originCube d m) g) :
    _root_.Homogenization.Book.Ch03.Legacy.ForceSobolevRegularity
      (_root_.Homogenization.Book.MainResults.originCube d m)
      _root_.Homogenization.Book.MainResults.fixedComparisonS g :=
  forceInH34_toRepo (originCube d m) g hg

private theorem scaledForceH34Seminorm_originCube {d : ℕ} [NeZero d] (m : ℕ)
    (g : Vec d → Vec d) :
    _root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
        (_root_.Homogenization.Book.MainResults.originCube d m) comparisonS g =
      scaledForceH34Seminorm (originCube d m) g :=
  scaledForceH34Seminorm_toRepo (originCube d m) g

/-! ## 3. The coefficient-field carrier -/

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

private theorem coefficientField_ext {d : ℕ} {a b : CoefficientField d}
    (h : a.toFun = b.toFun) : a = b := by
  cases a
  cases b
  subst h
  rfl

private theorem toRepoField_ofRepoField {d : ℕ}
    (a : _root_.Homogenization.RegCoeffField d) :
    toRepoField (ofRepoField a) = a :=
  rfl

private theorem ofRepoField_toRepoField {d : ℕ} (a : CoefficientField d) :
    ofRepoField (toRepoField a) = a :=
  rfl

private theorem isProbe_toRepo {d : ℕ} {φ : Vec d → ℝ} (h : IsProbe φ) :
    _root_.Homogenization.IsProbeR (d := d) φ :=
  ⟨h.measurable, h.bounded, h.compactSupport⟩

private theorem isProbe_ofRepo {d : ℕ} {φ : Vec d → ℝ}
    (h : _root_.Homogenization.IsProbeR (d := d) φ) : IsProbe φ :=
  ⟨h.measurable, h.bounded, h.hasCompactSupport⟩

private theorem measurable_toFun_observable {d : ℕ} :
    @Measurable (CoefficientField d) (RawCoeffField d) _
      (observableFieldSigma d) CoefficientField.toFun :=
  Measurable.of_comap_le le_rfl

private theorem measurable_entry_audit {d : ℕ} (y : Vec d) (i j : Fin d) :
    Measurable (fun a : CoefficientField d => a.toFun y i j) := by
  have h1 : @Measurable (RawCoeffField d) (Mat d) (pointwiseFieldSigma d)
      (instMeasurableSpaceMat d) (fun f => f y) := measurable_pi_apply y
  have h3 : @Measurable (Mat d) (Fin d → ℝ) (instMeasurableSpaceMat d)
      MeasurableSpace.pi (fun A => A i) := measurable_pi_apply i
  have h2 : @Measurable (Mat d) ℝ (instMeasurableSpaceMat d) _
      (fun A => A i j) := (measurable_pi_apply j).comp h3
  have h : @Measurable (RawCoeffField d) ℝ (observableFieldSigma d) _
      (fun f => f y i j) := (h2.comp h1).mono le_sup_left le_rfl
  exact h.comp measurable_toFun_observable

private theorem measurable_entryTest_audit {d : ℕ} (i j : Fin d)
    {φ : Vec d → ℝ} (hφ : IsProbe φ) :
    Measurable (fun a : CoefficientField d => entryTest i j φ a.toFun) := by
  have h : @Measurable (RawCoeffField d) ℝ (probeFieldSigma d) _
      (entryTest i j φ) := by
    intro t ht
    exact MeasurableSpace.measurableSet_generateFrom ⟨i, j, φ, hφ, t, ht, rfl⟩
  exact (h.mono le_sup_right le_rfl).comp measurable_toFun_observable

private theorem measurable_toRepoField {d : ℕ} :
    Measurable (toRepoField (d := d)) := by
  refine _root_.Homogenization.measurable_into_regCoeffField' ?_ ?_
  · intro y i j
    exact measurable_entry_audit y i j
  · intro i j φ hφ
    exact measurable_entryTest_audit i j (isProbe_ofRepo hφ)

private theorem measurable_ofRepoField {d : ℕ} :
    Measurable (ofRepoField (d := d)) := by
  refine Measurable.of_comap_le ?_
  have hcomp :
      MeasurableSpace.comap (ofRepoField (d := d))
          (MeasurableSpace.comap CoefficientField.toFun
            (observableFieldSigma d))
        = MeasurableSpace.comap
            (fun b : _root_.Homogenization.RegCoeffField d => b.toFun)
            (observableFieldSigma d) := by
    rw [MeasurableSpace.comap_comp]
    rfl
  rw [show (instMeasurableSpaceCoefficientField d :
        MeasurableSpace (CoefficientField d))
      = MeasurableSpace.comap CoefficientField.toFun
          (observableFieldSigma d) from rfl, hcomp,
    observableFieldSigma, MeasurableSpace.comap_sup]
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

private theorem ae_map_ofRepoField_iff {d : ℕ}
    {μ : Measure (_root_.Homogenization.RegCoeffField d)}
    {p : CoefficientField d → Prop} :
    (∀ᵐ a ∂Measure.map (ofRepoField (d := d)) μ, p a) ↔
      ∀ᵐ b ∂μ, p (ofRepoField b) := by
  rw [show Measure.map (ofRepoField (d := d)) μ = Measure.map (fieldEquiv d) μ
      from rfl, ← MeasurableEquiv.map_ae]
  exact Filter.eventually_map

private theorem map_ofRepoField_real_eq {d : ℕ}
    (μ : Measure (_root_.Homogenization.RegCoeffField d))
    (E : Set (CoefficientField d)) :
    (Measure.map (ofRepoField (d := d)) μ).real E =
      μ.real (ofRepoField ⁻¹' E) := by
  rw [measureReal_def, measureReal_def,
    show Measure.map (ofRepoField (d := d)) μ = Measure.map (fieldEquiv d) μ
      from rfl, (fieldEquiv d).map_apply E]
  rfl

/-! ## 4. Ellipticity conjunct reconstruction -/

private theorem measurableSet_interior {d : ℕ} (Q : TriadicCube d) :
    MeasurableSet Q.interior := by
  have h : Q.interior = ⋂ i : Fin d, (fun x : Vec d => x i) ⁻¹'
      (Set.Ioo (((Q.index i : ℝ) - (1 / 2 : ℝ)) * Q.side)
        (((Q.index i : ℝ) + (1 / 2 : ℝ)) * Q.side)) := by
    ext x
    simp [TriadicCube.interior, Set.mem_Ioo]
  rw [h]
  exact MeasurableSet.iInter fun i => (measurable_pi_apply i) measurableSet_Ioo

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
  exact ((a.entry_measurable i j).indicator
    hU).stronglyMeasurable.aestronglyMeasurable

private theorem toRepo_locallyUniformlyElliptic {d : ℕ}
    {a : CoefficientField d} (ha : LocallyUniformlyElliptic a) :
    _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (toRepoField a) := by
  intro Q
  obtain ⟨lam, Lam, hlam, hle, hEll⟩ := ha (ofRepoCube Q)
  have hmeas : MeasurableSet (_root_.Homogenization.openCubeSet Q) := by
    rw [← interior_ofRepoCube Q]
    exact measurableSet_interior (ofRepoCube Q)
  refine ⟨lam, Lam, hlam, hle, hmeas, ?_, ?_⟩
  · intro i j
    exact aestronglyMeasurable_restrict_entry hmeas a i j
  · exact hEll

/-! ## 5. Weak `H¹` functions -/

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

/-! ## 6. Comparison pairs and the compared quantities -/

private noncomputable def toRepoComparisonPair {d : ℕ} [NeZero d]
    {sigmaBar : ℝ} (hsigma : 0 < sigmaBar) {a : CoefficientField d}
    (haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (toRepoField a))
    {m : ℕ} {g : Vec d → Vec d}
    (pair : ComparisonPair sigmaBar a (originCube d m) g) :
    _root_.Homogenization.Book.Ch05.Section57.assemblyComparisonDatumOfScalar
      sigmaBar hsigma (toRepoField a) haRepo m g where
  u := toRepoWeakH1 pair.u
  v := toRepoWeakH1 pair.v
  uWeakSolution := by
    intro φ
    exact pair.u_solves (ofRepoWeakH10 φ)
  vWeakSolution := by
    intro φ
    exact pair.v_solves (ofRepoWeakH10 φ)
  zeroTraceDifference := by
    obtain ⟨w, hw⟩ := pair.sameBoundaryData
    exact ⟨toRepoWeakH10 w, hw⟩

private theorem energyNorm_toRepo {d : ℕ} [NeZero d] {a : CoefficientField d}
    {haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (toRepoField a)}
    {m : ℕ} (u : WeakH1 (originCube d m).interior) :
    _root_.Homogenization.Book.Ch03.h1EnergyNormOnCube
        (_root_.Homogenization.Book.MainResults.originCube d m)
        (_root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily
          (toRepoField a) haRepo)
        (toRepoWeakH1 u) =
      energyNorm (originCube d m) a.toFun u :=
  rfl

private theorem comparisonDefect_toRepo {d : ℕ} [NeZero d]
    {sigmaBar : ℝ} (hsigma : 0 < sigmaBar) {a : CoefficientField d}
    {haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (toRepoField a)}
    {m : ℕ} {g : Vec d → Vec d}
    (pair : ComparisonPair sigmaBar a (originCube d m) g) :
    _root_.Homogenization.Book.Ch03.Legacy.homogenizationComparisonNegativeSobolevLHS
        (_root_.Homogenization.Book.MainResults.originCube d m)
        (_root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily
          (toRepoField a) haRepo)
        (_root_.Homogenization.Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar
          sigmaBar hsigma)
        comparisonS (toRepoWeakH1 pair.u) (toRepoWeakH1 pair.v) =
      comparisonDefect pair := by
  rw [_root_.Homogenization.Book.Ch03.Legacy.homogenizationComparisonNegativeSobolevLHS,
    comparisonDefect, scaledNegativeVectorNorm_originCube,
    scaledNegativeVectorNorm_originCube]
  rfl

private theorem comparisonData_toRepo {d : ℕ} [NeZero d]
    {sigmaBar : ℝ} {a : CoefficientField d}
    {haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (toRepoField a)}
    {m : ℕ} {g : Vec d → Vec d}
    (pair : ComparisonPair sigmaBar a (originCube d m) g) :
    Real.sqrt sigmaBar *
        _root_.Homogenization.Book.Ch03.h1EnergyNormOnCube
          (_root_.Homogenization.Book.MainResults.originCube d m)
          (_root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily
            (toRepoField a) haRepo)
          (toRepoWeakH1 pair.u) +
      _root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
        (_root_.Homogenization.Book.MainResults.originCube d m) comparisonS g =
      comparisonData pair := by
  rw [energyNorm_toRepo (haRepo := haRepo) pair.u, comparisonData,
    scaledForceH34Seminorm_originCube]

/-! ## 7. The Bernoulli checkerboard law -/

namespace RandomCheckerboard

private theorem conductance_eq_scalarAt {d : ℕ} (lam Lam : ℝ) (ω : Sample d)
    (x : Vec d) :
    conductance lam Lam ω x =
      _root_.Homogenization.Examples.RandomCheckerboard.scalarAt lam Lam ω x := by
  classical
  by_cases hx : ∃ z : Lattice d, x ∈ openUnitCell z
  · obtain ⟨z, hz⟩ := hx
    rw [_root_.Homogenization.Examples.RandomCheckerboard.scalarAt_of_mem_openUnitCell
      (lam := lam) (Lam := Lam) (ω := ω) hz]
    cases hz' : ω z with
    | false =>
        have hmem : x ∈ highConductanceRegion ω :=
          Set.mem_biUnion (s := {z : Lattice d | ω z = false})
            (by simpa using hz') hz
        simp [conductance, hmem,
          _root_.Homogenization.Examples.RandomCheckerboard.coinConductance]
    | true =>
        have hnot : x ∉ highConductanceRegion ω := by
          intro hmem
          rw [highConductanceRegion, Set.mem_iUnion₂] at hmem
          obtain ⟨w, hw, hxw⟩ := hmem
          have hwz : w = z :=
            _root_.Homogenization.Examples.RandomCheckerboard.openUnitCell_unique
              hxw hz
          subst hwz
          simp only [Set.mem_ofPred_eq] at hw
          rw [hw] at hz'
          exact Bool.noConfusion hz'
        simp [conductance, hnot,
          _root_.Homogenization.Examples.RandomCheckerboard.coinConductance]
  · have hnot : x ∉ highConductanceRegion ω := by
      intro hmem
      rw [highConductanceRegion, Set.mem_iUnion₂] at hmem
      obtain ⟨w, _, hxw⟩ := hmem
      exact hx ⟨w, hxw⟩
    rw [conductance, if_neg hnot,
      _root_.Homogenization.Examples.RandomCheckerboard.scalarAt_of_not_mem_any_openUnitCell
        (lam := lam) (Lam := Lam) (ω := ω) hx]

private theorem checkerboardField_eq {d : ℕ} (lam Lam : ℝ) (ω : Sample d) :
    checkerboardField lam Lam ω =
      ofRepoField
        (_root_.Homogenization.Examples.RandomCheckerboard.checkerRegField
          lam Lam ω) := by
  refine coefficientField_ext ?_
  funext x
  show scalarMatrix (conductance lam Lam ω x) =
    _root_.Homogenization.Examples.RandomCheckerboard.coeffField lam Lam ω x
  rw [conductance_eq_scalarAt]
  rfl

private theorem checkerboardField_eq_comp {d : ℕ} (lam Lam : ℝ) :
    (checkerboardField (d := d) lam Lam) =
      ofRepoField ∘
        _root_.Homogenization.Examples.RandomCheckerboard.checkerRegField
          lam Lam := by
  funext ω
  exact checkerboardField_eq lam Lam ω

private theorem coinSampleMeasure_eq {d : ℕ} (p : ℝ≥0) (hp : p ≤ 1) :
    coinSampleMeasure d p hp =
      _root_.Homogenization.Examples.RandomCheckerboard.sampleMeasure d p hp :=
  rfl

private theorem rescale_eq_comp {d : ℕ} (k : ℕ) :
    (rescale (d := d) k) =
      ofRepoField ∘ _root_.Homogenization.rescaleReg k ∘ toRepoField := by
  funext a
  exact coefficientField_ext rfl

private theorem measurable_rescale {d : ℕ} (k : ℕ) :
    Measurable (rescale (d := d) k) := by
  rw [rescale_eq_comp]
  exact measurable_ofRepoField.comp
    ((_root_.Homogenization.measurable_rescaleReg k).comp measurable_toRepoField)

private theorem checkerboardLaw_eq {d : ℕ} [NeZero d] (S : Setup d) :
    S.checkerboardLaw =
      Measure.map (ofRepoField (d := d))
        (_root_.Homogenization.Examples.RandomCheckerboard.law d S.lam S.Lam
          S.bias S.bias_le_one) := by
  rw [Setup.checkerboardLaw, coinSampleMeasure_eq,
    _root_.Homogenization.Examples.RandomCheckerboard.law,
    Measure.map_map measurable_ofRepoField
      (_root_.Homogenization.Examples.RandomCheckerboard.measurable_checkerRegField
        (d := d) S.lam S.Lam),
    ← checkerboardField_eq_comp]

private theorem P_eq_map {d : ℕ} [NeZero d] (S : Setup d) :
    S.P =
      Measure.map (ofRepoField (d := d))
        (_root_.Homogenization.Examples.RandomCheckerboard.scaledLaw d S.lam
          S.Lam S.bias S.bias_le_one
          _root_.Homogenization.Examples.RandomCheckerboard.publicScale) := by
  rw [Setup.P, checkerboardLaw_eq,
    _root_.Homogenization.Examples.RandomCheckerboard.scaledLaw,
    _root_.Homogenization.Book.Ch04.restrictionScaleNormalizedLaw_eq_map_rescaleReg,
    Measure.map_map (measurable_rescale 1) measurable_ofRepoField,
    Measure.map_map measurable_ofRepoField
      (_root_.Homogenization.measurable_rescaleReg
        _root_.Homogenization.Examples.RandomCheckerboard.publicScale),
    rescale_eq_comp]
  rfl

/-- Fixed-exponent quenched homogenization comparison for the triadically
rescaled Bernoulli checkerboard.  The constants are chosen before the medium,
hence depend only on `d`. -/
theorem randomCheckerboard_quenchedComparison
    {d : ℕ} [NeZero d] :
    ∃ C alpha Cscale : ℝ,
      0 < C ∧ 0 < alpha ∧ 0 < Cscale ∧
      ∀ S : Setup d,
        ∃ sigmaBar : ℝ,
          0 < sigmaBar ∧
          ∃ X : CoefficientField d → ℝ,
            S.IsMinimalScale X Cscale ∧
            ∀ᵐ a ∂S.P,
              LocallyUniformlyElliptic a →
              ∀ {m : ℕ} {g : Vec d → Vec d}
                (pair : ComparisonPair sigmaBar a (originCube d m) g),
                X a ≤ (3 : ℝ) ^ m →
                ForceInH34 (originCube d m) g →
                comparisonDefect pair ≤
                  C * ((3 : ℝ) ^ m / X a) ^ (-alpha) * comparisonData pair := by
  classical
  obtain ⟨C, alpha, Cscale, hC, halpha, hCscale, hmain⟩ :=
    _root_.Homogenization.Examples.RandomCheckerboard.randomCheckerboard_quenchedComparison
      (d := d)
  refine ⟨C, alpha, Cscale, hC, halpha, hCscale, ?_⟩
  intro S
  let Srepo : _root_.Homogenization.Book.MainResults.Setup d :=
    _root_.Homogenization.Examples.RandomCheckerboard.checkerboardSetup
      S.two_le_dim S.lam S.Lam S.lam_pos S.lam_le_Lam S.bias S.bias_le_one
  let sigmaBar : ℝ :=
    _root_.Homogenization.Book.Ch05.Section57.barSigmaLimit Srepo.hP Srepo.hStruct
  have hsigma : 0 < sigmaBar := Srepo.barSigmaLimit_pos
  obtain ⟨_sigmaBar, _hsigma, X, hX, hmainS⟩ :=
    hmain S.two_le_dim S.lam S.Lam S.lam_pos S.lam_le_Lam S.bias S.bias_le_one
  refine ⟨sigmaBar, hsigma, fun a => X (toRepoField a), ?_, ?_⟩
  · refine ⟨fun a => hX.1 (toRepoField a), ?_⟩
    intro t ht
    have hrepo := hX.2 ht
    rw [P_eq_map S, map_ofRepoField_real_eq]
    exact hrepo
  · rw [P_eq_map S, ae_map_ofRepoField_iff]
    filter_upwards [hmainS] with b hb
    intro ha m g pair hXm hg
    have haRepo :
        _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
          (toRepoField (ofRepoField b)) :=
      toRepo_locallyUniformlyElliptic ha
    have hgRepo :
        _root_.Homogenization.Book.Ch03.Legacy.ForceSobolevRegularity
          (_root_.Homogenization.Book.MainResults.originCube d m)
          _root_.Homogenization.Book.MainResults.fixedComparisonS g :=
      forceInH34_originCube m g hg
    have hstep :=
      hb haRepo
        (toRepoComparisonPair (a := ofRepoField b) hsigma haRepo pair) hXm hgRepo
    have hdefect :=
      comparisonDefect_toRepo (a := ofRepoField b) (haRepo := haRepo) hsigma pair
    have hdata :=
      comparisonData_toRepo (a := ofRepoField b) (haRepo := haRepo) pair
    rw [← hdefect, ← hdata]
    exact hstep

end RandomCheckerboard

end

end StatementAudit
end Homogenization
