import Mathlib
import Homogenization.Book.MainResults
import Audit.QuenchedComparison.SolutionBasic

attribute [-instance] Homogenization.instMeasurableSpaceVec
attribute [-instance] Homogenization.instMeasurableSpaceMat
attribute [-instance] Homogenization.instMeasurableSpaceCoeffField

/-!
# Solution for the quenched comparison theorem challenge

This file is the comparator solution surface for the uniformly elliptic
quenched homogenization comparison theorem.

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
  · have hqAudit : cubeBesovConjExponent q = ∞ := by
      simpa [cubeBesovConjExponent] using hq
    have hqRepo :
        _root_.Homogenization.cubeBesovConjExponent q = ∞ := by
      simpa [_root_.Homogenization.cubeBesovConjExponent] using hq
    simp [_root_.Homogenization.cubeBesovDualTestNorm,
      cubeBesovDualTestNorm, hq, cubeBesovPartialNormTop_toRepo,
      _root_.Homogenization.cubeBesovConjExponent, cubeBesovConjExponent]
  · have hqRepo :
        _root_.Homogenization.cubeBesovConjExponent q ≠ ∞ := by
      simpa [_root_.Homogenization.cubeBesovConjExponent] using hq
    have hqAudit : cubeBesovConjExponent q ≠ ∞ := by
      simpa [cubeBesovConjExponent] using hq
    simp [_root_.Homogenization.cubeBesovDualTestNorm,
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

private theorem ae_map_toRepoReg_iff {d : ℕ}
    {μ : Measure (RegCoeffField d)}
    {p : _root_.Homogenization.RegCoeffField d → Prop} :
    (∀ᵐ b ∂Measure.map (toRepoReg (d := d)) μ, p b) ↔
      ∀ᵐ a ∂μ, p (toRepoReg a) := by
  rw [show Measure.map (toRepoReg (d := d)) μ = Measure.map (regEquiv d).symm μ from rfl,
    ← MeasurableEquiv.map_ae]
  exact Filter.eventually_map

private theorem map_toRepoReg_real_eq {d : ℕ}
    (μ : Measure (RegCoeffField d))
    (E : Set (_root_.Homogenization.RegCoeffField d)) :
    (Measure.map (toRepoReg (d := d)) μ).real E = μ.real (toRepoReg ⁻¹' E) := by
  rw [measureReal_def, measureReal_def,
    show Measure.map (toRepoReg (d := d)) μ = Measure.map (regEquiv d).symm μ from rfl,
    ((regEquiv d).symm).map_apply E]
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

private theorem toRepoUniformEllipticityBounds {d : ℕ} {P : CoeffLaw d}
    {lam Lam : ℝ} (hUE : UniformEllipticityBounds P lam Lam) :
    _root_.Homogenization.Book.Ch05.Section57.UniformEllipticityBounds
      (Measure.map (toRepoReg (d := d)) P) lam Lam where
  lam_pos := hUE.lam_pos
  lam_le_Lam := hUE.lam_le_Lam
  aee_elliptic := by
    refine (ae_map_toRepoReg_iff (μ := P)).2 ?_
    filter_upwards [hUE.aee_elliptic] with a ha
    intro Q
    have hRepo := toRepo_isAEEllipticFieldOn (ha (ofRepoTriadicCube Q))
    simpa [_root_.Homogenization.Book.Ch04.AEEllipticOn,
      openCubeSet_ofRepoTriadicCube] using hRepo

private noncomputable def toRepoSetup {d : ℕ} [NeZero d] (S : Setup d) :
    _root_.Homogenization.Book.MainResults.Setup d where
  two_le_dim := S.two_le_dim
  P := Measure.map (toRepoReg (d := d)) S.P
  hP := toRepoLawCarrier S.hP
  hStruct := toRepoStructuralLaw S.hStruct
  lam := S.lam
  Lam := S.Lam
  hUE := toRepoUniformEllipticityBounds S.hUE

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

/-- Fixed-exponent quenched homogenization comparison in the uniformly elliptic case.

This is the Mathlib-only existential-scalar corollary of the public theorem.
The repository proves the comparison for its internally constructed scalar
homogenized coefficient; this challenge statement exposes only the resulting
existence of a positive scalar `sigmaBar`.

The Sobolev exponent is fixed to `s = 3/4` (an auxiliary internal exponent
`t = 1/8` with `4 t < s < 1` is used in the proof but does not appear in this
statement).  The constants
`C`, `alpha`, and `Cscale` are therefore chosen before the probability law
`S : Setup d`; in particular they do not depend on the law, on the ellipticity
bounds, or on exponent variables. -/
theorem homogenizationComparison_uniformEllipticity
    {d : ℕ} [NeZero d] :
    ∃ C alpha Cscale : ℝ,
      0 < C ∧ 0 < alpha ∧ 0 < Cscale ∧
      ∀ S : Setup d,
        ∃ sigmaBar : ℝ,
          0 < sigmaBar ∧
          ∃ X : RegCoeffField d → ℝ,
            S.IsMinimalScale X Cscale ∧
            ∀ᵐ a ∂S.P,
              ∀ (ha : AELocallyUniformlyEllipticField a)
                {m : ℕ} {g : Vec d → Vec d}
                (pair : ComparisonPair sigmaBar a ha m g),
                X a ≤ (3 : ℝ) ^ m →
                ForceSobolevRegularity (originCube d m) fixedComparisonS g →
                comparisonDefect sigmaBar fixedComparisonS pair ≤
                  C * ((3 : ℝ) ^ m / X a) ^ (-alpha) *
                    comparisonData sigmaBar fixedComparisonS pair := by
  obtain ⟨C, alpha, Cscale, hC, halpha, hCscale, hmain⟩ :=
    _root_.Homogenization.Book.MainResults.homogenizationComparison_uniformEllipticity
      (d := d)
  refine ⟨C, alpha, Cscale, hC, halpha, hCscale, ?_⟩
  intro S
  let Srepo : _root_.Homogenization.Book.MainResults.Setup d := toRepoSetup S
  let sigmaBar : ℝ :=
    _root_.Homogenization.Book.Ch05.Section57.barSigmaLimit Srepo.hP Srepo.hStruct
  have hsigma : 0 < sigmaBar := by
    dsimp [sigmaBar]
    exact Srepo.barSigmaLimit_pos
  obtain ⟨_sigmaBar, _hsigma, X, hX, hmainS⟩ := hmain Srepo
  refine ⟨sigmaBar, hsigma, fun a => X (toRepoReg a), ?_, ?_⟩
  · -- the minimal-scale package transports along the carrier equivalence
    constructor
    · intro a
      exact hX.1 (toRepoReg a)
    · intro t ht
      have hrepo := hX.2 ht
      have hrepo' :
          (Measure.map (toRepoReg (d := d)) S.P).real
              (_root_.Homogenization.IndependentSums.upperTailEvent
                (fun b => |X b|)
                (Real.exp (Cscale * (Real.log (2 + Srepo.thetaHat)) ^ (2 : ℕ)) * t))
            ≤ (_root_.Homogenization.IndependentSums.gammaSigma ((d : ℕ) : ℝ) t)⁻¹ :=
        hrepo
      rw [map_toRepoReg_real_eq] at hrepo'
      exact hrepo'
  · have hmainAud := (ae_map_toRepoReg_iff (μ := S.P)).1 hmainS
    filter_upwards [hmainAud] with a hmain_a
    intro ha m g pair hXm hg
    let haRepo :
        _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField (toRepoReg a) :=
      toRepo_AELocallyUniformlyEllipticField ha
    let repoPair :
        Srepo.ComparisonPair (toRepoReg a) haRepo m g :=
      by
        simpa [Srepo, sigmaBar, toRepoSetup,
          _root_.Homogenization.Book.MainResults.Setup.ComparisonPair,
          _root_.Homogenization.Book.MainResults.Setup.homogenizedMatrix] using
          toRepoComparisonPair (a := a) hsigma haRepo pair
    have hgRepo :
        _root_.Homogenization.Book.Ch03.ForceSobolevRegularity
          (_root_.Homogenization.Book.MainResults.originCube d m)
          _root_.Homogenization.Book.MainResults.fixedComparisonS g := by
      simpa [fixedComparisonS,
        _root_.Homogenization.Book.MainResults.fixedComparisonS] using
        toRepo_ForceSobolevRegularity hg
    have hstep := hmain_a haRepo repoPair hXm hgRepo
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
          (a := a) (ha := ha) (haRepo := haRepo) hsigma fixedComparisonS pair)
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
          (a := a) (ha := ha) (haRepo := haRepo) fixedComparisonS pair)
    rw [hdefect, hdata] at hstep
    exact hstep

end

end StatementAudit
end Homogenization
