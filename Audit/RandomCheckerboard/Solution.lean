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
repository theorem and proves the same `StatementAudit` theorem surface.
The theorem does not expose the project's internal
construction of the homogenized coefficient.  Instead it is the Mathlib-only
existential-scalar corollary of the public theorem: it asserts existence of a
positive scalar homogenized coefficient `sigmaBar`, and states the comparison
estimate directly for weak solutions of the heterogeneous equation and the
constant-coefficient equation with matrix `sigmaBar • I`.

The definitions below are statement-level copies of the objects needed to state
this corollary.  The main source correspondences are:

* ambient fields and ellipticity: `Homogenization/Ambient/CoefficientField.lean`;
* coefficient laws and uniform ellipticity: `Homogenization/Book/Ch04/Law.lean`
  and `Homogenization/Book/Ch04/Theorems/UniformEllipticityBridge.lean`;
* cubes, weak equations, and energy quantities: `Homogenization/Book/Ch02` and
  `Homogenization/Book/Ch03`;
* positive and negative Sobolev quantities: `Homogenization/Book/Ch03/Theorems`;
* the public theorem surface: `Homogenization/Book/MainResults.lean`.
-/

namespace Homogenization
namespace StatementAudit

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Solution-only bridges to the repository theorem -/

private def toRepoTriadicCube {d : ℕ} (Q : TriadicCube d) :
    _root_.Homogenization.TriadicCube d :=
  { scale := Q.scale
    index := Q.index }

private def ofRepoTriadicCube {d : ℕ}
    (Q : _root_.Homogenization.TriadicCube d) : TriadicCube d :=
  { scale := Q.scale
    index := Q.index }

private theorem openCubeSet_ofRepoTriadicCube {d : ℕ}
    (Q : _root_.Homogenization.TriadicCube d) :
    openCubeSet (ofRepoTriadicCube Q) = _root_.Homogenization.openCubeSet Q :=
  rfl

private theorem toRepoTriadicCube_injective {d : ℕ} :
    Function.Injective (toRepoTriadicCube (d := d)) := by
  intro Q R h
  cases Q
  cases R
  simp [toRepoTriadicCube] at h
  simpa using h

private def toRepoTriadicCubeEmbedding (d : ℕ) :
    TriadicCube d ↪ _root_.Homogenization.TriadicCube d where
  toFun := toRepoTriadicCube
  inj' := toRepoTriadicCube_injective

private theorem toRepo_ofRepoTriadicCube {d : ℕ}
    (Q : _root_.Homogenization.TriadicCube d) :
    toRepoTriadicCube (ofRepoTriadicCube Q) = Q := by
  cases Q
  rfl

private theorem childCubes_toRepo {d : ℕ} (Q : TriadicCube d) :
    (childCubes Q).map (toRepoTriadicCubeEmbedding d) =
      _root_.Homogenization.childCubes (toRepoTriadicCube Q) := by
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
    · simpa [R', toRepoTriadicCubeEmbedding, toRepoTriadicCube] using hR

private theorem descendantsAtDepth_toRepo {d : ℕ}
    (Q : TriadicCube d) (n : ℕ) :
    (descendantsAtDepth Q n).map (toRepoTriadicCubeEmbedding d) =
      _root_.Homogenization.descendantsAtDepth (toRepoTriadicCube Q) n := by
  induction n with
  | zero =>
      simp [descendantsAtDepth, _root_.Homogenization.descendantsAtDepth,
        toRepoTriadicCubeEmbedding]
  | succ n ih =>
      ext R
      constructor
      · intro h
        rcases Finset.mem_map.mp h with ⟨R', hR', rfl⟩
        rcases Finset.mem_biUnion.mp hR' with ⟨S, hS, hchild⟩
        have hSrepo : toRepoTriadicCube S ∈
            _root_.Homogenization.descendantsAtDepth (toRepoTriadicCube Q) n := by
          rw [← ih]
          exact Finset.mem_map.mpr ⟨S, hS, rfl⟩
        have hchildRepo : toRepoTriadicCube R' ∈
            _root_.Homogenization.childCubes (toRepoTriadicCube S) := by
          rw [← childCubes_toRepo]
          exact Finset.mem_map.mpr ⟨R', hchild, rfl⟩
        exact Finset.mem_biUnion.mpr ⟨toRepoTriadicCube S, hSrepo, hchildRepo⟩
      · intro h
        rcases Finset.mem_biUnion.mp h with ⟨Srepo, hSrepo, hchildRepo⟩
        let S : TriadicCube d := ofRepoTriadicCube Srepo
        have hS : S ∈ descendantsAtDepth Q n := by
          have hmap : toRepoTriadicCube S ∈
              _root_.Homogenization.descendantsAtDepth (toRepoTriadicCube Q) n := by
            simpa [S, toRepo_ofRepoTriadicCube] using hSrepo
          rw [← ih] at hmap
          rcases Finset.mem_map.mp hmap with ⟨S', hS', hS'eq⟩
          have : S' = S := toRepoTriadicCube_injective hS'eq
          simpa [this] using hS'
        have hchild : ofRepoTriadicCube R ∈ childCubes S := by
          have hmap : toRepoTriadicCube (ofRepoTriadicCube R) ∈
              _root_.Homogenization.childCubes (toRepoTriadicCube S) := by
            simpa [S, toRepo_ofRepoTriadicCube] using hchildRepo
          rw [← childCubes_toRepo] at hmap
          rcases Finset.mem_map.mp hmap with ⟨R', hR', hR'eq⟩
          have : R' = ofRepoTriadicCube R := toRepoTriadicCube_injective hR'eq
          simpa [this] using hR'
        refine Finset.mem_map.mpr ?_
        refine ⟨ofRepoTriadicCube R, ?_, ?_⟩
        · exact Finset.mem_biUnion.mpr ⟨S, hS, hchild⟩
        · exact toRepo_ofRepoTriadicCube R

private theorem descendantsAverage_toRepo {d : ℕ} (Q : TriadicCube d)
    (j : ℕ) (F : _root_.Homogenization.TriadicCube d → ℝ) :
    _root_.Homogenization.descendantsAverage (toRepoTriadicCube Q) j F =
      descendantsAverage Q j (fun R => F (toRepoTriadicCube R)) := by
  unfold _root_.Homogenization.descendantsAverage descendantsAverage
  rw [← descendantsAtDepth_toRepo Q j]
  simp [Finset.sum_map, toRepoTriadicCubeEmbedding]

private theorem cubeAverage_toRepo {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ) :
    _root_.Homogenization.cubeAverage (toRepoTriadicCube Q) f =
      cubeAverage Q f :=
  rfl

private theorem normalizedCubeMeasure_toRepo {d : ℕ} (Q : TriadicCube d) :
    _root_.Homogenization.normalizedCubeMeasure (toRepoTriadicCube Q) =
      normalizedCubeMeasure Q :=
  rfl

private theorem cubeFluctuation_toRepo {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ) :
    _root_.Homogenization.cubeFluctuation (toRepoTriadicCube Q) f =
      cubeFluctuation Q f :=
  rfl

private theorem cubeBesovOscillation_toRepo {d : ℕ} (Q : TriadicCube d)
    (p : ℝ≥0∞) (u : Vec d → ℝ) :
    _root_.Homogenization.cubeBesovOscillation (toRepoTriadicCube Q) p u =
      cubeBesovOscillation Q p u :=
  rfl

private theorem cubeBesovScaleWeight_toRepo {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) :
    _root_.Homogenization.cubeBesovScaleWeight s (toRepoTriadicCube Q) =
      cubeBesovScaleWeight s Q :=
  rfl

private theorem cubeBesovDepthWeight_toRepo {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (j : ℕ) :
    _root_.Homogenization.cubeBesovDepthWeight (toRepoTriadicCube Q) s j =
      cubeBesovDepthWeight Q s j :=
  rfl

private theorem cubeBesovDepthAverage_toRepo {d : ℕ} (Q : TriadicCube d)
    (p : ℝ≥0∞) (u : Vec d → ℝ) (j : ℕ) :
    _root_.Homogenization.cubeBesovDepthAverage (toRepoTriadicCube Q) p u j =
      cubeBesovDepthAverage Q p u j := by
  simp [_root_.Homogenization.cubeBesovDepthAverage, cubeBesovDepthAverage,
    descendantsAverage_toRepo, cubeBesovOscillation_toRepo]

private theorem cubeBesovDepthSeminorm_toRepo {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) (j : ℕ) :
    _root_.Homogenization.cubeBesovDepthSeminorm (toRepoTriadicCube Q) s p u j =
      cubeBesovDepthSeminorm Q s p u j := by
  unfold _root_.Homogenization.cubeBesovDepthSeminorm cubeBesovDepthSeminorm
  rw [cubeBesovDepthWeight_toRepo, cubeBesovDepthAverage_toRepo]

private theorem cubeBesovPartialSeminorm_toRepo {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) :
    _root_.Homogenization.cubeBesovPartialSeminorm
        (toRepoTriadicCube Q) s p q N u =
      cubeBesovPartialSeminorm Q s p q N u := by
  simp [_root_.Homogenization.cubeBesovPartialSeminorm,
    cubeBesovPartialSeminorm, cubeBesovDepthSeminorm_toRepo]

private theorem cubeBesovPartialSeminormTop_toRepo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (N : ℕ)
    (u : Vec d → ℝ) :
    _root_.Homogenization.cubeBesovPartialSeminormTop
        (toRepoTriadicCube Q) s p N u =
      cubeBesovPartialSeminormTop Q s p N u := by
  simp [_root_.Homogenization.cubeBesovPartialSeminormTop,
    cubeBesovPartialSeminormTop, cubeBesovDepthSeminorm_toRepo]

private theorem cubeBesovPartialNorm_toRepo {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) :
    _root_.Homogenization.cubeBesovPartialNorm
        (toRepoTriadicCube Q) s p q N u =
      cubeBesovPartialNorm Q s p q N u := by
  simp [_root_.Homogenization.cubeBesovPartialNorm, cubeBesovPartialNorm,
    cubeBesovPartialSeminorm_toRepo, cubeBesovScaleWeight_toRepo,
    cubeAverage_toRepo]

private theorem cubeBesovPartialNormTop_toRepo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (N : ℕ)
    (u : Vec d → ℝ) :
    _root_.Homogenization.cubeBesovPartialNormTop
        (toRepoTriadicCube Q) s p N u =
      cubeBesovPartialNormTop Q s p N u := by
  simp [_root_.Homogenization.cubeBesovPartialNormTop,
    cubeBesovPartialNormTop, cubeBesovPartialSeminormTop_toRepo,
    cubeBesovScaleWeight_toRepo, cubeAverage_toRepo]

private theorem mem_descendantsAtDepth_toRepo {d : ℕ}
    (Q R : TriadicCube d) (j : ℕ) :
    toRepoTriadicCube R ∈
        _root_.Homogenization.descendantsAtDepth (toRepoTriadicCube Q) j ↔
      R ∈ descendantsAtDepth Q j := by
  rw [← descendantsAtDepth_toRepo Q j]
  constructor
  · intro h
    rcases Finset.mem_map.mp h with ⟨R', hR', hR'eq⟩
    have : R' = R := toRepoTriadicCube_injective hR'eq
    simpa [this] using hR'
  · intro h
    exact Finset.mem_map.mpr ⟨R, h, rfl⟩

private theorem cubeBesovDualTestNorm_toRepo {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (g : Vec d → ℝ) :
    _root_.Homogenization.cubeBesovDualTestNorm
        (toRepoTriadicCube Q) s p q N g =
      cubeBesovDualTestNorm Q s p q N g := by
  by_cases hq : ENNReal.conjExponent q = ∞
  · simp [_root_.Homogenization.cubeBesovDualTestNorm,
      cubeBesovDualTestNorm, hq, cubeBesovPartialNormTop_toRepo,
      _root_.Homogenization.cubeBesovConjExponent, cubeBesovConjExponent]
  · simp [_root_.Homogenization.cubeBesovDualTestNorm,
      cubeBesovDualTestNorm, hq, cubeBesovPartialNorm_toRepo,
      _root_.Homogenization.cubeBesovConjExponent, cubeBesovConjExponent]

private theorem CubeBesovDualLocalMemLpGlobal_toRepo {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (g : Vec d → ℝ) :
    _root_.Homogenization.CubeBesovDualLocalMemLpGlobal
        (toRepoTriadicCube Q) p g ↔
      CubeBesovDualLocalMemLpGlobal Q p g := by
  constructor
  · intro h j R hR
    have hRepo := h j (toRepoTriadicCube R)
      ((mem_descendantsAtDepth_toRepo Q R j).2 hR)
    simpa [_root_.Homogenization.CubeBesovDualLocalMemLpGlobal,
      CubeBesovDualLocalMemLpGlobal, cubeFluctuation_toRepo,
      normalizedCubeMeasure_toRepo,
      _root_.Homogenization.cubeBesovConjExponent, cubeBesovConjExponent] using hRepo
  · intro h j R hR
    let R' : TriadicCube d := ofRepoTriadicCube R
    have hR' : R' ∈ descendantsAtDepth Q j := by
      have hRepo : toRepoTriadicCube R' ∈
          _root_.Homogenization.descendantsAtDepth (toRepoTriadicCube Q) j := by
        simpa [R', toRepo_ofRepoTriadicCube] using hR
      exact (mem_descendantsAtDepth_toRepo Q R' j).1 hRepo
    have hAudit := h j R' hR'
    simpa [R', toRepo_ofRepoTriadicCube,
      _root_.Homogenization.CubeBesovDualLocalMemLpGlobal,
      CubeBesovDualLocalMemLpGlobal, cubeFluctuation_toRepo,
      normalizedCubeMeasure_toRepo,
      _root_.Homogenization.cubeBesovConjExponent, cubeBesovConjExponent] using hAudit

private theorem CubeBesovDualFullTest_toRepo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (g : Vec d → ℝ) :
    _root_.Homogenization.CubeBesovDualFullTest
        (toRepoTriadicCube Q) s p q g ↔
      CubeBesovDualFullTest Q s p q g := by
  constructor
  · intro h
    constructor
    · intro N
      simpa [cubeBesovDualTestNorm_toRepo] using h.1 N
    · exact (CubeBesovDualLocalMemLpGlobal_toRepo Q p g).1 h.2
  · intro h
    constructor
    · intro N
      simpa [cubeBesovDualTestNorm_toRepo] using h.1 N
    · exact (CubeBesovDualLocalMemLpGlobal_toRepo Q p g).2 h.2

private theorem cubeBesovPairing_toRepo {d : ℕ}
    (Q : TriadicCube d) (f g : Vec d → ℝ) :
    _root_.Homogenization.cubeBesovPairing (toRepoTriadicCube Q) f g =
      cubeBesovPairing Q f g :=
  rfl

private theorem cubeBesovDualFullNormValueSet_toRepo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (f : Vec d → ℝ) :
    _root_.Homogenization.cubeBesovDualFullNormValueSet
        (toRepoTriadicCube Q) s p q f =
      cubeBesovDualFullNormValueSet Q s p q f := by
  ext r
  constructor
  · rintro ⟨g, hg, hr⟩
    refine ⟨g, (CubeBesovDualFullTest_toRepo Q s p q g).1 hg, ?_⟩
    simpa [cubeBesovPairing_toRepo] using hr
  · rintro ⟨g, hg, hr⟩
    refine ⟨g, (CubeBesovDualFullTest_toRepo Q s p q g).2 hg, ?_⟩
    simpa [cubeBesovPairing_toRepo] using hr

private theorem cubeBesovDualFullNorm_toRepo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (f : Vec d → ℝ) :
    _root_.Homogenization.cubeBesovDualFullNorm
        (toRepoTriadicCube Q) s p q f =
      cubeBesovDualFullNorm Q s p q f := by
  rw [_root_.Homogenization.cubeBesovDualFullNorm,
    cubeBesovDualFullNorm, cubeBesovDualFullNormValueSet_toRepo]

private theorem scaleNormalizedNegativeSobolevVectorNormTwo_toRepo
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) :
    _root_.Homogenization.Book.Ch03.scaleNormalizedNegativeSobolevVectorNormTwo
        (toRepoTriadicCube Q) s F =
      scaleNormalizedNegativeSobolevVectorNormTwo Q s F := by
  unfold _root_.Homogenization.Book.Ch03.scaleNormalizedNegativeSobolevVectorNormTwo
    _root_.Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
    scaleNormalizedNegativeSobolevVectorNormTwo
  rw [show ((toRepoTriadicCube Q).scale : ℤ) = Q.scale by rfl]
  congr 1
  exact Finset.sum_congr rfl fun i _hi =>
    cubeBesovDualFullNorm_toRepo Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => F x i)

private theorem toRepo_originCube {d : ℕ} [NeZero d] (m : ℕ) :
    toRepoTriadicCube (originCube d m) =
      _root_.Homogenization.Book.MainResults.originCube d m :=
  rfl

private theorem gagliardoKernel_toRepo {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : ℝ) (p : ℝ≥0∞) (u : Vec d → E) :
    _root_.Homogenization.Gagliardo.gagliardoKernel s p u =
      Gagliardo.gagliardoKernel s p u := by
  funext z
  rfl

private theorem scaleNormalizedPositiveSobolevVectorSeminormTwo_toRepo
    {d : ℕ} [NeZero d] (m : ℕ) (s : ℝ) (g : Vec d → Vec d) :
    _root_.Homogenization.Book.Ch03.scaleNormalizedPositiveSobolevVectorSeminormTwo
        (_root_.Homogenization.Book.MainResults.originCube d m) s g =
      scaleNormalizedPositiveSobolevVectorSeminormTwo (originCube d m) s g := by
  simp [_root_.Homogenization.Book.Ch03.scaleNormalizedPositiveSobolevVectorSeminormTwo,
    scaleNormalizedPositiveSobolevVectorSeminormTwo,
    _root_.Homogenization.Book.Ch01.fractionalSobolevSeminorm,
    fractionalSobolevSeminorm,
    _root_.Homogenization.Gagliardo.cubeGagliardoSeminorm,
    Gagliardo.cubeGagliardoSeminorm,
    _root_.Homogenization.Gagliardo.cubeGagliardoESeminorm,
    Gagliardo.cubeGagliardoESeminorm,
    _root_.Homogenization.Gagliardo.gagliardoCubeMeasure,
    Gagliardo.gagliardoCubeMeasure,
    gagliardoKernel_toRepo,
    _root_.Homogenization.Book.MainResults.originCube,
    _root_.Homogenization.Book.Ch05.Section57.assemblyOriginCube,
    _root_.Homogenization.originCube, originCube, triadicOriginCube,
    _root_.Homogenization.normalizedCubeMeasure, normalizedCubeMeasure,
    _root_.Homogenization.cubeMeasure, cubeMeasure,
    _root_.Homogenization.cubeVolume, cubeVolume,
    _root_.Homogenization.cubeSet, cubeSet,
    _root_.Homogenization.cubeBesovScaleWeight, cubeBesovScaleWeight,
    _root_.Homogenization.cubeScaleFactor, cubeScaleFactor]

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

private theorem ae_map_ofRepoReg_iff {d : ℕ}
    {μ : Measure (_root_.Homogenization.RegCoeffField d)}
    {p : RegCoeffField d → Prop} :
    (∀ᵐ a ∂Measure.map (ofRepoReg (d := d)) μ, p a) ↔
      ∀ᵐ b ∂μ, p (ofRepoReg b) := by
  rw [show Measure.map (ofRepoReg (d := d)) μ = Measure.map (regEquiv d) μ from rfl,
    ← MeasurableEquiv.map_ae]
  exact Filter.eventually_map

private theorem map_ofRepoReg_real_eq {d : ℕ}
    (μ : Measure (_root_.Homogenization.RegCoeffField d))
    (E : Set (RegCoeffField d)) :
    (Measure.map (ofRepoReg (d := d)) μ).real E = μ.real (ofRepoReg ⁻¹' E) := by
  rw [measureReal_def, measureReal_def,
    show Measure.map (ofRepoReg (d := d)) μ = Measure.map (regEquiv d) μ from rfl,
    (regEquiv d).map_apply E]
  rfl

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

private def toRepoH1Origin {d : ℕ} [NeZero d] {m : ℕ}
    (u : H1Function (openCubeSet (originCube d m))) :
    _root_.Homogenization.H1Function
      (_root_.Homogenization.Book.Ch02.cubeDomain
        (_root_.Homogenization.Book.MainResults.originCube d m) : Set (Vec d)) := by
  simpa [_root_.Homogenization.Book.MainResults.originCube,
    _root_.Homogenization.Book.Ch05.Section57.assemblyOriginCube,
    _root_.Homogenization.originCube, originCube, triadicOriginCube,
    _root_.Homogenization.Book.Ch02.cubeDomain_coe,
    _root_.Homogenization.openCubeSet, openCubeSet,
    _root_.Homogenization.cubeScaleFactor, cubeScaleFactor] using
    toRepoH1Function u

private def toRepoH10Origin {d : ℕ} [NeZero d] {m : ℕ}
    (u : H10Function (openCubeSet (originCube d m))) :
    _root_.Homogenization.H10Function
      (_root_.Homogenization.Book.Ch02.cubeDomain
        (_root_.Homogenization.Book.MainResults.originCube d m) : Set (Vec d)) := by
  simpa [_root_.Homogenization.Book.MainResults.originCube,
    _root_.Homogenization.Book.Ch05.Section57.assemblyOriginCube,
    _root_.Homogenization.originCube, originCube, triadicOriginCube,
    _root_.Homogenization.Book.Ch02.cubeDomain_coe,
    _root_.Homogenization.openCubeSet, openCubeSet,
    _root_.Homogenization.cubeScaleFactor, cubeScaleFactor] using
    toRepoH10Function u

@[simp] private theorem toRepoH1Function_toFun {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) :
    (toRepoH1Function u).toFun = u.toFun :=
  rfl

@[simp] private theorem toRepoH1Function_grad {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) :
    (toRepoH1Function u).grad = u.grad :=
  rfl

@[simp] private theorem ofRepoH1Function_toFun {d : ℕ} {U : Set (Vec d)}
    (u : _root_.Homogenization.H1Function U) :
    (ofRepoH1Function u).toFun = u.toFun :=
  rfl

@[simp] private theorem ofRepoH1Function_grad {d : ℕ} {U : Set (Vec d)}
    (u : _root_.Homogenization.H1Function U) :
    (ofRepoH1Function u).grad = u.grad :=
  rfl

@[simp] private theorem toRepoH10Function_toFun {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) :
    (toRepoH10Function u).toFun = u.toFun :=
  rfl

@[simp] private theorem toRepoH1Origin_toFun {d : ℕ} [NeZero d] {m : ℕ}
    (u : H1Function (openCubeSet (originCube d m))) :
    (toRepoH1Origin u).toFun = u.toFun := by
  simp [toRepoH1Origin]

@[simp] private theorem toRepoH1Origin_grad {d : ℕ} [NeZero d] {m : ℕ}
    (u : H1Function (openCubeSet (originCube d m))) :
    (toRepoH1Origin u).grad = u.grad := by
  simp [toRepoH1Origin]

@[simp] private theorem toRepoH10Origin_toFun {d : ℕ} [NeZero d] {m : ℕ}
    (u : H10Function (openCubeSet (originCube d m))) :
    (toRepoH10Origin u).toFun = u.toFun := by
  simp [toRepoH10Origin]

@[simp] private theorem ofRepoH10Function_grad {d : ℕ} {U : Set (Vec d)}
    (u : _root_.Homogenization.H10Function U) :
    (ofRepoH10Function u).toH1Function.grad = u.toH1Function.grad := by
  simp [ofRepoH10Function]

private theorem toRepo_ForceSobolevRegularity {d : ℕ} [NeZero d]
    {m : ℕ} {s : ℝ} {g : Vec d → Vec d}
    (hg : ForceSobolevRegularity (originCube d m) s g) :
    _root_.Homogenization.Book.Ch03.ForceSobolevRegularity
      (_root_.Homogenization.Book.MainResults.originCube d m) s g := by
  simpa [_root_.Homogenization.Book.Ch03.ForceSobolevRegularity,
    ForceSobolevRegularity,
    _root_.Homogenization.Book.Ch01.MemFractionalSobolev,
    MemFractionalSobolev,
    _root_.Homogenization.Book.Ch01.fractionalSobolevSeminorm,
    fractionalSobolevSeminorm,
    _root_.Homogenization.Gagliardo.MemWsp, Gagliardo.MemWsp,
    _root_.Homogenization.Gagliardo.gagliardoKernel, Gagliardo.gagliardoKernel,
    _root_.Homogenization.Gagliardo.gagliardoCubeMeasure,
    Gagliardo.gagliardoCubeMeasure,
    _root_.Homogenization.Gagliardo.kernelExponent, Gagliardo.kernelExponent,
    _root_.Homogenization.normalizedCubeMeasure, normalizedCubeMeasure,
    _root_.Homogenization.cubeMeasure, cubeMeasure,
    _root_.Homogenization.Book.MainResults.originCube,
    _root_.Homogenization.Book.Ch05.Section57.assemblyOriginCube,
    _root_.Homogenization.originCube, originCube, triadicOriginCube,
    _root_.Homogenization.cubeSet, cubeSet,
    _root_.Homogenization.cubeScaleFactor, cubeScaleFactor] using hg

private noncomputable def toRepoComparisonPair {d : ℕ} [NeZero d]
    {sigmaBar : ℝ} (hsigma : 0 < sigmaBar)
    {a : RegCoeffField d} {ha : AELocallyUniformlyEllipticField a}
    (haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField (toRepoReg a))
    {m : ℕ} {g : Vec d → Vec d}
    (pair : ComparisonPair sigmaBar a ha m g) :
    _root_.Homogenization.Book.Ch05.Section57.assemblyComparisonDatumOfScalar
      sigmaBar hsigma (toRepoReg a) haRepo m g where
  u := by
    simpa [_root_.Homogenization.Book.MainResults.originCube] using
      toRepoH1Origin pair.u
  v := by
    simpa [_root_.Homogenization.Book.MainResults.originCube] using
      toRepoH1Origin pair.v
  uWeakSolution := by
    intro phi
    have hphi := pair.uWeakSolution (ofRepoH10Function phi)
    simpa [_root_.Homogenization.Book.Ch03.IsForcedEquation, IsForcedEquation,
      _root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily,
      _root_.Homogenization.Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
      _root_.Homogenization.Book.Ch04.coeffOnOfAEEllipticOn,
      _root_.Homogenization.Book.Ch02.cubeDomain_coe,
      _root_.Homogenization.Book.Ch05.Section57.assemblyOriginCube,
      _root_.Homogenization.originCube, originCube, triadicOriginCube,
      _root_.Homogenization.openCubeSet, openCubeSet,
      _root_.Homogenization.cubeScaleFactor, cubeScaleFactor,
      toRepoH1Function, ofRepoH10Function, toRepoReg_toFun,
      _root_.Homogenization.vecDot, vecDot,
      _root_.Homogenization.matVecMul, matVecMul] using hphi
  vWeakSolution := by
    intro phi
    have hphi := pair.vWeakSolution (ofRepoH10Function phi)
    simpa [_root_.Homogenization.Book.Ch03.IsConstantCoeffForcedEquation,
      IsConstantCoeffForcedEquation,
      _root_.Homogenization.Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar,
      _root_.Homogenization.Book.Ch05.Section57.scalarConstantCoeffMatrix,
      _root_.Homogenization.Book.Ch05.Section57.assemblyOriginCube,
      _root_.Homogenization.originCube, originCube, triadicOriginCube,
      _root_.Homogenization.Book.Ch02.cubeDomain_coe,
      _root_.Homogenization.openCubeSet, openCubeSet,
      _root_.Homogenization.cubeScaleFactor, cubeScaleFactor,
      toRepoH1Function, ofRepoH10Function,
      _root_.Homogenization.scalarMatrix, scalarMatrix,
      _root_.Homogenization.vecDot, vecDot,
      _root_.Homogenization.matVecMul, matVecMul] using hphi
  zeroTraceDifference := by
    rcases pair.zeroTraceDifference with ⟨w, hw⟩
    refine ⟨?_, ?_⟩
    · simpa [_root_.Homogenization.Book.Ch05.Section57.assemblyOriginCube,
        _root_.Homogenization.originCube, originCube, triadicOriginCube,
        _root_.Homogenization.Book.Ch02.cubeDomain_coe,
        _root_.Homogenization.openCubeSet, openCubeSet,
        _root_.Homogenization.cubeScaleFactor, cubeScaleFactor] using
        (toRepoH10Origin w)
    · simpa [toRepoH10Function, toRepoH1Function,
        _root_.Homogenization.Book.Ch05.Section57.assemblyOriginCube,
        _root_.Homogenization.originCube, originCube, triadicOriginCube,
        _root_.Homogenization.Book.Ch02.cubeDomain_coe,
        _root_.Homogenization.openCubeSet, openCubeSet,
        _root_.Homogenization.cubeScaleFactor, cubeScaleFactor] using hw

private theorem h1EnergyNormOnCube_toRepo {d : ℕ} [NeZero d]
    {a : RegCoeffField d}
    {haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField (toRepoReg a)}
    {m : ℕ} (u : H1Function (openCubeSet (originCube d m))) :
    _root_.Homogenization.Book.Ch03.h1EnergyNormOnCube
        (_root_.Homogenization.Book.MainResults.originCube d m)
        (_root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily (toRepoReg a) haRepo)
        (toRepoH1Origin u) =
      h1EnergyNormOnCube (originCube d m) a.toFun u := by
  simp [_root_.Homogenization.Book.Ch03.h1EnergyNormOnCube,
    _root_.Homogenization.Book.Ch03.localizedCoeffEnergyValue,
    _root_.Homogenization.Book.Ch03.normalizedSetAverage,
    h1EnergyNormOnCube,
    _root_.Homogenization.volumeAverage, volumeAverage,
    _root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily,
    _root_.Homogenization.Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
    _root_.Homogenization.Book.Ch04.coeffOnOfAEEllipticOn,
    _root_.Homogenization.Book.Ch02.cubeDomain_coe,
    _root_.Homogenization.Book.MainResults.originCube,
    _root_.Homogenization.Book.Ch05.Section57.assemblyOriginCube,
    _root_.Homogenization.originCube, originCube, triadicOriginCube,
    _root_.Homogenization.openCubeSet, openCubeSet,
    _root_.Homogenization.cubeScaleFactor, cubeScaleFactor,
    _root_.Homogenization.symmPart, symmPart, toRepoReg_toFun,
    _root_.Homogenization.vecDot, vecDot,
    _root_.Homogenization.matVecMul, matVecMul,
    toRepoH1Origin, toRepoH1Function]

private theorem comparisonDefect_toRepo {d : ℕ} [NeZero d]
    {sigmaBar : ℝ} (hsigma : 0 < sigmaBar)
    {a : RegCoeffField d} {ha : AELocallyUniformlyEllipticField a}
    {haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField (toRepoReg a)}
    {m : ℕ} {g : Vec d → Vec d} (s : ℝ)
    (pair : ComparisonPair sigmaBar a ha m g) :
    _root_.Homogenization.Book.Ch03.homogenizationComparisonNegativeSobolevLHS
        (_root_.Homogenization.Book.MainResults.originCube d m)
        (_root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily (toRepoReg a) haRepo)
        (_root_.Homogenization.Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar
          sigmaBar hsigma)
        s (toRepoH1Origin pair.u) (toRepoH1Origin pair.v) =
      comparisonDefect sigmaBar s pair := by
  have hgrad :
      _root_.Homogenization.Book.Ch03.homogenizationComparisonConstantGradientField
          (_root_.Homogenization.Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar
            sigmaBar hsigma)
          (toRepoH1Origin pair.u) (toRepoH1Origin pair.v) =
        comparisonConstantGradientField sigmaBar pair.u pair.v := by
    funext x i
    simp [_root_.Homogenization.Book.Ch03.homogenizationComparisonConstantGradientField,
      comparisonConstantGradientField,
      _root_.Homogenization.Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar,
      _root_.Homogenization.Book.Ch05.Section57.scalarConstantCoeffMatrix,
      _root_.Homogenization.scalarMatrix, scalarMatrix,
      _root_.Homogenization.matVecMul, matVecMul, toRepoH1Origin, toRepoH1Function]
  have hflux :
      _root_.Homogenization.Book.Ch03.homogenizationComparisonFluxField
          (_root_.Homogenization.Book.MainResults.originCube d m)
          (_root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily (toRepoReg a) haRepo)
          (_root_.Homogenization.Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar
            sigmaBar hsigma)
          (toRepoH1Origin pair.u) (toRepoH1Origin pair.v) =
        comparisonFluxField (originCube d m) a.toFun sigmaBar pair.u pair.v := by
    funext x i
    simp [_root_.Homogenization.Book.Ch03.homogenizationComparisonFluxField,
      comparisonFluxField,
      _root_.Homogenization.Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar,
      _root_.Homogenization.Book.Ch05.Section57.scalarConstantCoeffMatrix,
      _root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily,
      _root_.Homogenization.Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
      _root_.Homogenization.Book.Ch04.coeffOnOfAEEllipticOn,
      _root_.Homogenization.Book.Ch02.cubeDomain_coe,
      _root_.Homogenization.originCube, triadicOriginCube,
      _root_.Homogenization.scalarMatrix, scalarMatrix, toRepoReg_toFun,
      _root_.Homogenization.matVecMul, matVecMul, toRepoH1Origin, toRepoH1Function]
  unfold _root_.Homogenization.Book.Ch03.homogenizationComparisonNegativeSobolevLHS
    comparisonDefect
  rw [hgrad, hflux, ← toRepo_originCube (d := d) m]
  rw [scaleNormalizedNegativeSobolevVectorNormTwo_toRepo,
    scaleNormalizedNegativeSobolevVectorNormTwo_toRepo]

private theorem comparisonData_toRepo {d : ℕ} [NeZero d]
    {sigmaBar : ℝ} {a : RegCoeffField d}
    {ha : AELocallyUniformlyEllipticField a}
    {haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField (toRepoReg a)}
    {m : ℕ} {g : Vec d → Vec d} (s : ℝ)
    (pair : ComparisonPair sigmaBar a ha m g) :
    Real.sqrt sigmaBar *
        _root_.Homogenization.Book.Ch03.h1EnergyNormOnCube
          (_root_.Homogenization.Book.MainResults.originCube d m)
          (_root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily (toRepoReg a) haRepo)
          (toRepoH1Origin pair.u) +
      _root_.Homogenization.Book.Ch03.scaleNormalizedPositiveSobolevVectorSeminormTwo
        (_root_.Homogenization.Book.MainResults.originCube d m) s g =
      comparisonData sigmaBar s pair := by
  rw [h1EnergyNormOnCube_toRepo, scaleNormalizedPositiveSobolevVectorSeminormTwo_toRepo]
  rfl

namespace RandomCheckerboard
private theorem checkerRegField_eq_comp {d : ℕ} (lam Lam : ℝ) :
    (checkerRegField (d := d) lam Lam) =
      ofRepoReg ∘
        _root_.Homogenization.Examples.RandomCheckerboard.checkerRegField lam Lam := by
  funext ω
  rfl

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

private theorem rescaleReg_eq_comp {d : ℕ} (k : ℕ) :
    (rescaleReg (d := d) k) =
      ofRepoReg ∘ _root_.Homogenization.rescaleReg k ∘ toRepoReg := by
  funext a
  rfl

private theorem measurable_rescaleReg_audit {d : ℕ} (k : ℕ) :
    Measurable (rescaleReg (d := d) k) := by
  rw [rescaleReg_eq_comp]
  exact measurable_ofRepoReg.comp
    ((_root_.Homogenization.measurable_rescaleReg k).comp measurable_toRepoReg)

private theorem scaledLaw_eq_map_ofRepoReg {d : ℕ} (lam Lam : ℝ)
    (p : ℝ≥0) (hp : p ≤ 1) (k : ℕ) :
    scaledLaw d lam Lam p hp k =
      Measure.map (ofRepoReg (d := d))
        (_root_.Homogenization.Examples.RandomCheckerboard.scaledLaw d lam Lam p hp k) := by
  rw [scaledLaw, law_eq_map_ofRepoReg,
    _root_.Homogenization.Examples.RandomCheckerboard.scaledLaw,
    _root_.Homogenization.Book.Ch04.scaleNormalizedLaw_eq_map_rescaleReg,
    Measure.map_map (measurable_rescaleReg_audit k) measurable_ofRepoReg,
    Measure.map_map measurable_ofRepoReg
      (_root_.Homogenization.measurable_rescaleReg k),
    rescaleReg_eq_comp]
  rfl

/-- Fixed-exponent quenched homogenization comparison for the triadically
scaled Bernoulli checkerboard. -/
theorem randomCheckerboard_quenchedComparison
    {d : ℕ} [NeZero d] :
    ∃ C alpha Cscale : ℝ,
      0 < C ∧ 0 < alpha ∧ 0 < Cscale ∧
      ∀ (_two_le_dim : 2 ≤ d) (lam Lam : ℝ)
        (_hlam : 0 < lam) (_hle : lam ≤ Lam)
        (p : ℝ≥0) (hp : p ≤ 1),
        let P : CoeffLaw d := scaledLaw d lam Lam p hp publicScale
        ∃ sigmaBar : ℝ,
          0 < sigmaBar ∧
          ∃ X : RegCoeffField d → ℝ,
            IsCheckerboardMinimalScale P lam Lam X Cscale ∧
            ∀ᵐ aω ∂P,
              ∀ (ha : AELocallyUniformlyEllipticField aω)
                {m : ℕ} {g : Vec d → Vec d}
                (pair : ComparisonPair sigmaBar aω ha m g),
                X aω ≤ (3 : ℝ) ^ m →
                ForceSobolevRegularity (originCube d m) fixedComparisonS g →
                comparisonDefect sigmaBar fixedComparisonS pair ≤
                  C * ((3 : ℝ) ^ m / X aω) ^ (-alpha) *
                    comparisonData sigmaBar fixedComparisonS pair := by
  classical
  obtain ⟨C, alpha, Cscale, hC, halpha, hCscale, hmain⟩ :=
    _root_.Homogenization.Examples.RandomCheckerboard.randomCheckerboard_quenchedComparison
      (d := d)
  refine ⟨C, alpha, Cscale, hC, halpha, hCscale, ?_⟩
  intro two_le_dim lam Lam hlam hle p hp
  let Srepo : _root_.Homogenization.Book.MainResults.Setup d :=
    _root_.Homogenization.Examples.RandomCheckerboard.checkerboardSetup
      two_le_dim lam Lam hlam hle p hp
  let sigmaBar : ℝ :=
    _root_.Homogenization.Book.Ch05.Section57.barSigmaLimit Srepo.hP Srepo.hStruct
  have hsigma : 0 < sigmaBar := by
    dsimp [sigmaBar]
    exact Srepo.barSigmaLimit_pos
  obtain ⟨_sigmaBar, _hsigma, X, hX, hmainS⟩ :=
    hmain two_le_dim lam Lam hlam hle p hp
  refine ⟨sigmaBar, hsigma, fun a => X (toRepoReg a), ?_, ?_⟩
  · -- the minimal-scale package transports along the carrier equivalence
    have hXmin :
        (∀ b, 1 ≤ X b) ∧
          _root_.Homogenization.IndependentSums.IsBigO
            (_root_.Homogenization.Examples.RandomCheckerboard.scaledLaw d lam Lam p hp
              _root_.Homogenization.Examples.RandomCheckerboard.publicScale)
            (_root_.Homogenization.IndependentSums.gammaSigma ((d : ℕ) : ℝ)) X
            (Real.exp (Cscale *
              (Real.log (2 + checkerboardThetaHat d lam Lam)) ^ (2 : ℕ))) := by
      simpa [Srepo, checkerboardThetaHat,
        _root_.Homogenization.Book.MainResults.Setup.IsMinimalScale,
        _root_.Homogenization.Book.MainResults.Setup.thetaHat,
        _root_.Homogenization.Book.Ch05.Section57.mainResultsThetaHat,
        _root_.Homogenization.Book.Ch05.Section57.uniformUpperBlockConst,
        _root_.Homogenization.Book.Ch05.Section57.uniformLowerInvBlockConst,
        _root_.Homogenization.Examples.RandomCheckerboard.checkerboardSetup] using hX
    refine ⟨fun a => hXmin.1 (toRepoReg a), ?_⟩
    intro t ht
    have hrepo := hXmin.2 ht
    have hreal :
        (scaledLaw d lam Lam p hp publicScale).real
            (IndependentSums.upperTailEvent
              (fun a : RegCoeffField d => |X (toRepoReg a)|)
              (Real.exp (Cscale *
                (Real.log (2 + checkerboardThetaHat d lam Lam)) ^ (2 : ℕ)) * t))
          ≤ (IndependentSums.gammaSigma ((d : ℕ) : ℝ) t)⁻¹ := by
      rw [scaledLaw_eq_map_ofRepoReg, map_ofRepoReg_real_eq]
      exact hrepo
    exact hreal
  · have hmainLaw :
        ∀ᵐ b ∂(_root_.Homogenization.Examples.RandomCheckerboard.scaledLaw d lam Lam p hp
            _root_.Homogenization.Examples.RandomCheckerboard.publicScale),
          ∀ (haRepo :
              _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField b)
            {m : ℕ} {g : Vec d → Vec d}
            (pair : Srepo.ComparisonPair b haRepo m g),
            X b ≤ (3 : ℝ) ^ m →
            _root_.Homogenization.Book.Ch03.ForceSobolevRegularity
              (_root_.Homogenization.Book.MainResults.originCube d m)
              _root_.Homogenization.Book.MainResults.fixedComparisonS g →
            Srepo.comparisonDefect
                _root_.Homogenization.Book.MainResults.fixedComparisonS pair ≤
              C * ((3 : ℝ) ^ m / X b) ^ (-alpha) *
                Srepo.comparisonData
                  _root_.Homogenization.Book.MainResults.fixedComparisonS pair := by
      simpa [Srepo,
        _root_.Homogenization.Examples.RandomCheckerboard.checkerboardSetup] using hmainS
    rw [scaledLaw_eq_map_ofRepoReg lam Lam p hp publicScale]
    rw [show (_root_.Homogenization.Examples.RandomCheckerboard.scaledLaw d lam Lam p hp
          publicScale)
        = _root_.Homogenization.Examples.RandomCheckerboard.scaledLaw d lam Lam p hp
            _root_.Homogenization.Examples.RandomCheckerboard.publicScale from rfl]
    rw [ae_map_ofRepoReg_iff]
    filter_upwards [hmainLaw] with b hmain_b
    intro ha m g pair hXm hg
    let haRepo :
        _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField b :=
      toRepo_AELocallyUniformlyEllipticField ha
    let repoPair :
        Srepo.ComparisonPair b haRepo m g :=
      by
        simpa [Srepo, sigmaBar,
          _root_.Homogenization.Book.MainResults.Setup.ComparisonPair,
          _root_.Homogenization.Book.MainResults.Setup.homogenizedMatrix] using
          toRepoComparisonPair (a := ofRepoReg b) hsigma haRepo pair
    have hgRepo :
        _root_.Homogenization.Book.Ch03.ForceSobolevRegularity
          (_root_.Homogenization.Book.MainResults.originCube d m)
          _root_.Homogenization.Book.MainResults.fixedComparisonS g := by
      simpa [fixedComparisonS,
        _root_.Homogenization.Book.MainResults.fixedComparisonS] using
        toRepo_ForceSobolevRegularity hg
    have hstep := hmain_b haRepo repoPair hXm hgRepo
    have hdefect :
        Srepo.comparisonDefect
            _root_.Homogenization.Book.MainResults.fixedComparisonS repoPair =
          comparisonDefect sigmaBar fixedComparisonS pair := by
      simpa [repoPair, toRepoComparisonPair,
        _root_.Homogenization.Book.MainResults.Setup.comparisonDefect,
        _root_.Homogenization.Book.MainResults.Setup.homogenizedMatrix,
        Srepo, sigmaBar, fixedComparisonS,
        _root_.Homogenization.Book.MainResults.fixedComparisonS] using
        (comparisonDefect_toRepo (d := d) (sigmaBar := sigmaBar)
          (a := ofRepoReg b) (ha := ha) (haRepo := haRepo) hsigma fixedComparisonS pair)
    have hdata :
        Srepo.comparisonData
            _root_.Homogenization.Book.MainResults.fixedComparisonS repoPair =
          comparisonData sigmaBar fixedComparisonS pair := by
      simpa [repoPair, toRepoComparisonPair,
        _root_.Homogenization.Book.MainResults.Setup.comparisonData,
        _root_.Homogenization.Book.MainResults.Setup.homogenizedMatrix,
        Srepo, sigmaBar, fixedComparisonS,
        _root_.Homogenization.Book.MainResults.fixedComparisonS] using
        (comparisonData_toRepo (d := d) (sigmaBar := sigmaBar)
          (a := ofRepoReg b) (ha := ha) (haRepo := haRepo) fixedComparisonS pair)
    rw [hdefect, hdata] at hstep
    exact hstep

end RandomCheckerboard

end

end StatementAudit
end Homogenization
