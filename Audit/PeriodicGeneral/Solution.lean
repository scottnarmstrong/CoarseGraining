import Mathlib
import Homogenization.Examples.Periodic.PeriodicGeneralComparison
import Audit.PeriodicGeneral.SolutionBasic

attribute [-instance] Homogenization.instMeasurableSpaceVec
attribute [-instance] Homogenization.instMeasurableSpaceMat
attribute [-instance] Homogenization.instMeasurableSpaceCoeffField

/-!
# Solution: periodic homogenization comparison (general field)

This file is the comparator solution surface for the deterministic periodic
specialization of the quenched homogenization comparison theorem (Dirac law at
an arbitrary periodic, signed-coordinate-invariant, adjoint-invariant,
uniformly elliptic field).

The challenge module `Audit/PeriodicGeneral/Challenge.lean` imports only
Mathlib.  This solution imports the repository theorem
`Homogenization.Examples.Periodic.periodicGeneral_comparison` together with
`Audit.PeriodicGeneral.SolutionBasic`, which is a verbatim copy of the
challenge's statement vocabulary, and proves the audited theorem with a
byte-identical statement.

The private bridges below connect the audited vocabulary to the repository
objects.  The main correspondences are:

* triadic cubes and their descendants: `Homogenization/Geometry`;
* the honest coefficient-field carrier and its σ-algebra:
  `Homogenization/Probability/RegCoeffField.lean` and
  `Homogenization/Probability/RegCoeffField/Sigma.lean`;
* cubes, weak equations, and energy quantities: `Homogenization/Book/Ch02` and
  `Homogenization/Book/Ch03`;
* the fixed-exponent (`s = 3/4`, `p = q = 2`) specializations of the positive
  and negative Sobolev quantities: `Homogenization/Book/Ch01/Theorems` and
  `Homogenization/Book/Ch03/Theorems`;
* the public theorem surface: `Homogenization/Book/MainResults.lean`.
-/

namespace Homogenization
namespace StatementAudit

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-! ## 1. Triadic cubes -/

private def toRepoTriadicCube {d : ℕ} (Q : TriadicCube d) :
    _root_.Homogenization.TriadicCube d :=
  { scale := Q.scale
    index := Q.index }

private def ofRepoTriadicCube {d : ℕ}
    (Q : _root_.Homogenization.TriadicCube d) : TriadicCube d :=
  { scale := Q.scale
    index := Q.index }

private theorem interior_ofRepoTriadicCube {d : ℕ}
    (Q : _root_.Homogenization.TriadicCube d) :
    (ofRepoTriadicCube Q).interior = _root_.Homogenization.openCubeSet Q :=
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

private theorem children_toRepo {d : ℕ} (Q : TriadicCube d) :
    Q.children.map (toRepoTriadicCubeEmbedding d) =
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

private theorem descendants_toRepo {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    (Q.descendants n).map (toRepoTriadicCubeEmbedding d) =
      _root_.Homogenization.descendantsAtDepth (toRepoTriadicCube Q) n := by
  induction n with
  | zero =>
      simp [TriadicCube.descendants, _root_.Homogenization.descendantsAtDepth,
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
          rw [← children_toRepo]
          exact Finset.mem_map.mpr ⟨R', hchild, rfl⟩
        exact Finset.mem_biUnion.mpr ⟨toRepoTriadicCube S, hSrepo, hchildRepo⟩
      · intro h
        rcases Finset.mem_biUnion.mp h with ⟨Srepo, hSrepo, hchildRepo⟩
        let S : TriadicCube d := ofRepoTriadicCube Srepo
        have hS : S ∈ Q.descendants n := by
          have hmap : toRepoTriadicCube S ∈
              _root_.Homogenization.descendantsAtDepth (toRepoTriadicCube Q) n := by
            simpa [S, toRepo_ofRepoTriadicCube] using hSrepo
          rw [← ih] at hmap
          rcases Finset.mem_map.mp hmap with ⟨S', hS', hS'eq⟩
          have : S' = S := toRepoTriadicCube_injective hS'eq
          simpa [this] using hS'
        have hchild : ofRepoTriadicCube R ∈ S.children := by
          have hmap : toRepoTriadicCube (ofRepoTriadicCube R) ∈
              _root_.Homogenization.childCubes (toRepoTriadicCube S) := by
            simpa [S, toRepo_ofRepoTriadicCube] using hchildRepo
          rw [← children_toRepo] at hmap
          rcases Finset.mem_map.mp hmap with ⟨R', hR', hR'eq⟩
          have : R' = ofRepoTriadicCube R := toRepoTriadicCube_injective hR'eq
          simpa [this] using hR'
        refine Finset.mem_map.mpr ?_
        refine ⟨ofRepoTriadicCube R, ?_, ?_⟩
        · exact Finset.mem_biUnion.mpr ⟨S, hS, hchild⟩
        · exact toRepo_ofRepoTriadicCube R

private theorem mem_descendants_toRepo {d : ℕ}
    (Q R : TriadicCube d) (j : ℕ) :
    toRepoTriadicCube R ∈
        _root_.Homogenization.descendantsAtDepth (toRepoTriadicCube Q) j ↔
      R ∈ Q.descendants j := by
  rw [← descendants_toRepo Q j]
  constructor
  · intro h
    rcases Finset.mem_map.mp h with ⟨R', hR', hR'eq⟩
    have : R' = R := toRepoTriadicCube_injective hR'eq
    simpa [this] using hR'
  · intro h
    exact Finset.mem_map.mpr ⟨R, h, rfl⟩

private theorem descendantAverage_toRepo {d : ℕ} (Q : TriadicCube d)
    (j : ℕ) (F : _root_.Homogenization.TriadicCube d → ℝ) :
    _root_.Homogenization.descendantsAverage (toRepoTriadicCube Q) j F =
      Q.descendantAverage j (fun R => F (toRepoTriadicCube R)) := by
  unfold _root_.Homogenization.descendantsAverage TriadicCube.descendantAverage
  rw [← descendants_toRepo Q j]
  simp [Finset.sum_map, toRepoTriadicCubeEmbedding]

private theorem average_toRepo {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) :
    _root_.Homogenization.cubeAverage (toRepoTriadicCube Q) f = Q.average f :=
  rfl

private theorem normalizedMeasure_toRepo {d : ℕ} (Q : TriadicCube d) :
    _root_.Homogenization.normalizedCubeMeasure (toRepoTriadicCube Q) =
      Q.normalizedMeasure :=
  rfl

private theorem fluctuation_toRepo {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) :
    _root_.Homogenization.cubeFluctuation (toRepoTriadicCube Q) f =
      Q.fluctuation f :=
  rfl

private theorem toRepo_originCube {d : ℕ} [NeZero d] (m : ℕ) :
    toRepoTriadicCube (originCube d m) =
      _root_.Homogenization.Book.MainResults.originCube d m :=
  rfl

/-! ## 2. The two exponent facts used to specialize the Sobolev machinery -/

private theorem toReal_two : (2 : ℝ≥0∞).toReal = 2 := by
  norm_num

private theorem conjExponent_two : ENNReal.conjExponent (2 : ℝ≥0∞) = 2 := by
  rw [ENNReal.conjExponent]
  have h : (2 : ℝ≥0∞) - 1 = 1 := by
    rw [show (2 : ℝ≥0∞) = 1 + 1 from by norm_num]
    exact ENNReal.add_sub_cancel_right ENNReal.one_ne_top
  rw [h, inv_one]
  norm_num

private theorem cubeBesovConjExponent_two :
    _root_.Homogenization.cubeBesovConjExponent (2 : ℝ≥0∞) = 2 := by
  rw [_root_.Homogenization.cubeBesovConjExponent]
  exact conjExponent_two

private theorem cubeBesovConjExponent_two_ne_top :
    _root_.Homogenization.cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
  rw [cubeBesovConjExponent_two]
  exact ENNReal.ofNat_ne_top

/-! ## 3. The `H^{-3/4}` dual test norm -/

private theorem l2Norm_toRepo {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) :
    _root_.Homogenization.cubeBesovOscillation (toRepoTriadicCube Q)
        (2 : ℝ≥0∞) u = Q.l2Norm (Q.fluctuation u) :=
  rfl

private theorem depthAverage_toRepo {d : ℕ} (Q : TriadicCube d)
    (u : Vec d → ℝ) (j : ℕ) :
    _root_.Homogenization.cubeBesovDepthAverage (toRepoTriadicCube Q)
        (2 : ℝ≥0∞) u j = Sobolev34.depthAverage Q u j := by
  unfold _root_.Homogenization.cubeBesovDepthAverage Sobolev34.depthAverage
  rw [descendantAverage_toRepo]
  simp only [l2Norm_toRepo, toReal_two]

private theorem depthSeminorm_toRepo {d : ℕ} (Q : TriadicCube d)
    (u : Vec d → ℝ) (j : ℕ) :
    _root_.Homogenization.cubeBesovDepthSeminorm (toRepoTriadicCube Q)
        comparisonS (2 : ℝ≥0∞) u j = Sobolev34.depthSeminorm Q u j := by
  unfold _root_.Homogenization.cubeBesovDepthSeminorm Sobolev34.depthSeminorm
    _root_.Homogenization.cubeBesovDepthWeight
  rw [depthAverage_toRepo, toReal_two]
  rfl

private theorem partialTestNorm_toRepo {d : ℕ} (Q : TriadicCube d)
    (N : ℕ) (u : Vec d → ℝ) :
    _root_.Homogenization.cubeBesovPartialNorm (toRepoTriadicCube Q)
        comparisonS (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u =
      Sobolev34.partialTestNorm Q N u := by
  unfold _root_.Homogenization.cubeBesovPartialNorm
    _root_.Homogenization.cubeBesovPartialSeminorm
    _root_.Homogenization.cubeBesovScaleWeight Sobolev34.partialTestNorm
  rw [average_toRepo]
  simp only [depthSeminorm_toRepo, toReal_two]
  rfl

private theorem dualTestNorm_toRepo {d : ℕ} (Q : TriadicCube d)
    (N : ℕ) (u : Vec d → ℝ) :
    _root_.Homogenization.cubeBesovDualTestNorm (toRepoTriadicCube Q)
        comparisonS (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u =
      Sobolev34.partialTestNorm Q N u := by
  unfold _root_.Homogenization.cubeBesovDualTestNorm
  rw [if_neg cubeBesovConjExponent_two_ne_top, cubeBesovConjExponent_two]
  exact partialTestNorm_toRepo Q N u

private theorem locallyL2_toRepo {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) :
    _root_.Homogenization.CubeBesovDualLocalMemLpGlobal (toRepoTriadicCube Q)
        (2 : ℝ≥0∞) u ↔ Sobolev34.LocallyL2OnDescendants Q u := by
  unfold _root_.Homogenization.CubeBesovDualLocalMemLpGlobal
    Sobolev34.LocallyL2OnDescendants
  rw [cubeBesovConjExponent_two]
  constructor
  · intro h j R hR
    exact h j (toRepoTriadicCube R) ((mem_descendants_toRepo Q R j).2 hR)
  · intro h j R hR
    have hR' : ofRepoTriadicCube R ∈ Q.descendants j := by
      refine (mem_descendants_toRepo Q (ofRepoTriadicCube R) j).1 ?_
      simpa [toRepo_ofRepoTriadicCube] using hR
    have := h j (ofRepoTriadicCube R) hR'
    simpa [toRepo_ofRepoTriadicCube] using this

private theorem isDualTest_toRepo {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) :
    _root_.Homogenization.CubeBesovDualFullTest (toRepoTriadicCube Q)
        comparisonS (2 : ℝ≥0∞) (2 : ℝ≥0∞) u ↔ Sobolev34.IsDualTest Q u := by
  unfold _root_.Homogenization.CubeBesovDualFullTest Sobolev34.IsDualTest
  rw [locallyL2_toRepo]
  constructor
  · intro h
    exact ⟨fun N => (dualTestNorm_toRepo Q N u) ▸ h.1 N, h.2⟩
  · intro h
    exact ⟨fun N => (dualTestNorm_toRepo Q N u).symm ▸ h.1 N, h.2⟩

private theorem pairing_toRepo {d : ℕ} (Q : TriadicCube d) (f u : Vec d → ℝ) :
    _root_.Homogenization.cubeBesovPairing (toRepoTriadicCube Q) f u =
      Sobolev34.pairing Q f u :=
  rfl

private theorem negativeNorm_toRepo {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ) :
    _root_.Homogenization.cubeBesovDualFullNorm (toRepoTriadicCube Q)
        comparisonS (2 : ℝ≥0∞) (2 : ℝ≥0∞) f = Sobolev34.negativeNorm Q f := by
  unfold _root_.Homogenization.cubeBesovDualFullNorm
    _root_.Homogenization.cubeBesovDualFullNormValueSet Sobolev34.negativeNorm
  congr 1
  ext r
  constructor
  · rintro ⟨u, hu, hr⟩
    exact ⟨u, (isDualTest_toRepo Q u).1 hu, by simpa [pairing_toRepo] using hr⟩
  · rintro ⟨u, hu, hr⟩
    exact ⟨u, (isDualTest_toRepo Q u).2 hu, by simpa [pairing_toRepo] using hr⟩

private theorem scaledNegativeVectorNorm_toRepo {d : ℕ} (Q : TriadicCube d)
    (F : Vec d → Vec d) :
    _root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedNegativeSobolevVectorNormTwo
        (toRepoTriadicCube Q) comparisonS F =
      Sobolev34.scaledNegativeVectorNorm Q F := by
  unfold
    _root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedNegativeSobolevVectorNormTwo
    _root_.Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
    Sobolev34.scaledNegativeVectorNorm Sobolev34.negativeScaleFactor
  refine congrArg _ (Finset.sum_congr rfl fun i _hi => ?_)
  exact negativeNorm_toRepo Q (fun x => F x i)

/-! ## 4. The positive `H^{3/4}` seminorm -/

private theorem kernel_toRepo {d : ℕ} (u : Vec d → ℝ) :
    _root_.Homogenization.Gagliardo.gagliardoKernel (d := d) (E := ℝ)
        comparisonS (2 : ℝ≥0∞) u = Sobolev34.kernel u := by
  funext z
  simp only [_root_.Homogenization.Gagliardo.gagliardoKernel, Sobolev34.kernel,
    _root_.Homogenization.Gagliardo.kernelExponent, Sobolev34.kernelExponent,
    toReal_two, smul_eq_mul]

private theorem productMeasure_toRepo {d : ℕ} (Q : TriadicCube d) :
    _root_.Homogenization.Gagliardo.gagliardoCubeMeasure (toRepoTriadicCube Q) =
      Sobolev34.productMeasure Q :=
  rfl

private theorem seminorm_toRepo {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) :
    _root_.Homogenization.Book.Ch01.Legacy.fractionalSobolevSeminorm
        (toRepoTriadicCube Q) comparisonS (2 : ℝ≥0∞) u =
      Sobolev34.seminorm Q u := by
  unfold _root_.Homogenization.Book.Ch01.Legacy.fractionalSobolevSeminorm
    _root_.Homogenization.Gagliardo.cubeGagliardoSeminorm
    _root_.Homogenization.Gagliardo.cubeGagliardoESeminorm
    Sobolev34.seminorm
  rw [kernel_toRepo, productMeasure_toRepo]

private theorem memH34_toRepo {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ)
    (hu : Sobolev34.MemH34 Q u) :
    _root_.Homogenization.Book.Ch01.Legacy.MemFractionalSobolev
      (toRepoTriadicCube Q) comparisonS (2 : ℝ≥0∞) u := by
  refine ⟨hu.1, ?_⟩
  unfold _root_.Homogenization.Gagliardo.MemWsp
  rw [kernel_toRepo, productMeasure_toRepo]
  exact hu.2

private theorem forceInH34_toRepo {d : ℕ} (Q : TriadicCube d)
    (g : Vec d → Vec d) (hg : ForceInH34 Q g) :
    _root_.Homogenization.Book.Ch03.Legacy.ForceSobolevRegularity
      (toRepoTriadicCube Q) comparisonS g :=
  fun i => memH34_toRepo Q (fun x => g x i) (hg i)

private theorem scaledForceH34Seminorm_toRepo {d : ℕ} (Q : TriadicCube d)
    (g : Vec d → Vec d) :
    _root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
        (toRepoTriadicCube Q) comparisonS g =
      scaledForceH34Seminorm Q g := by
  unfold
    _root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
    _root_.Homogenization.cubeBesovScaleWeight scaledForceH34Seminorm
  rw [neg_neg]
  refine congrArg _ (Finset.sum_congr rfl fun i _hi => ?_)
  exact seminorm_toRepo Q (fun x => g x i)

/-! ## 5. The honest coefficient-field carrier -/

private def toRepoReg {d : ℕ} (a : CoefficientField d) :
    _root_.Homogenization.RegCoeffField d where
  toFun := a.toFun
  entry_measurable := a.entry_measurable
  entry_locInt := a.entry_locallyIntegrable

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

private theorem isProbe_toRepo {d : ℕ} {φ : Vec d → ℝ} (h : IsProbe (d := d) φ) :
    _root_.Homogenization.IsProbeR φ :=
  ⟨h.measurable, h.bounded, h.compactSupport⟩

private theorem isProbe_ofRepo {d : ℕ} {φ : Vec d → ℝ}
    (h : _root_.Homogenization.IsProbeR (d := d) φ) : IsProbe φ :=
  ⟨h.measurable, h.bounded, h.hasCompactSupport⟩

/-- The carrier σ-algebra of the audited surface — one `comap` of the observable
σ-algebra — is the join of the pointwise pullback and the probe-integral
σ-algebra, which is the shape used by the repository carrier. -/
private theorem carrierSigma_eq_join (d : ℕ) :
    (instMeasurableSpaceCoefficientField d :
        MeasurableSpace (CoefficientField d))
      = MeasurableSpace.comap CoefficientField.toFun (pointwiseFieldSigma d)
        ⊔ MeasurableSpace.generateFrom
            {s | ∃ (i j : Fin d) (φ : Vec d → ℝ), IsProbe φ ∧
              ∃ t : Set ℝ, MeasurableSet t ∧
                s = (fun a : CoefficientField d =>
                  entryTest i j φ a.toFun) ⁻¹' t} := by
  unfold instMeasurableSpaceCoefficientField observableFieldSigma probeFieldSigma
  rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_generateFrom]
  have hset :
      (Set.preimage CoefficientField.toFun) ''
        {s | ∃ (i j : Fin d) (φ : Vec d → ℝ), IsProbe φ ∧
          ∃ t : Set ℝ, MeasurableSet t ∧ s = entryTest i j φ ⁻¹' t}
      = {s | ∃ (i j : Fin d) (φ : Vec d → ℝ), IsProbe φ ∧
          ∃ t : Set ℝ, MeasurableSet t ∧
            s = (fun a : CoefficientField d =>
              entryTest i j φ a.toFun) ⁻¹' t} := by
    apply Set.eq_of_subset_of_subset
    · rintro s ⟨t, ⟨i, j, φ, hφ, u, hu, rfl⟩, rfl⟩
      exact ⟨i, j, φ, hφ, u, hu, rfl⟩
    · rintro s ⟨i, j, φ, hφ, u, hu, rfl⟩
      exact ⟨entryTest i j φ ⁻¹' u, ⟨i, j, φ, hφ, u, hu, rfl⟩, rfl⟩
  rw [hset]

private theorem measurable_toFun_audit {d : ℕ} :
    @Measurable (CoefficientField d) (RawCoeffField d) _
      (pointwiseFieldSigma d) CoefficientField.toFun := by
  have h : @Measurable (CoefficientField d) (RawCoeffField d)
      (instMeasurableSpaceCoefficientField d) (observableFieldSigma d)
      CoefficientField.toFun := Measurable.of_comap_le le_rfl
  exact h.mono le_rfl le_sup_left

private theorem measurable_apply_entry_audit {d : ℕ} (y : Vec d) (i j : Fin d) :
    Measurable (fun a : CoefficientField d => a.toFun y i j) := by
  have h1 : @Measurable (RawCoeffField d) (Mat d) (pointwiseFieldSigma d)
      (instMeasurableSpaceMat d) (fun f => f y) := measurable_pi_apply y
  have h3 : @Measurable (Mat d) (Fin d → ℝ) (instMeasurableSpaceMat d)
      MeasurableSpace.pi (fun A => A i) := measurable_pi_apply i
  have h2 : @Measurable (Mat d) ℝ (instMeasurableSpaceMat d) _ (fun A => A i j) :=
    (measurable_pi_apply j).comp h3
  exact (h2.comp h1).comp measurable_toFun_audit

private theorem measurable_entryTest_audit {d : ℕ} (i j : Fin d) {φ : Vec d → ℝ}
    (hφ : IsProbe φ) :
    Measurable (fun a : CoefficientField d => entryTest i j φ a.toFun) := by
  have hraw : @Measurable (RawCoeffField d) ℝ (probeFieldSigma d) _
      (entryTest i j φ) := by
    intro t ht
    exact MeasurableSpace.measurableSet_generateFrom ⟨i, j, φ, hφ, t, ht, rfl⟩
  have htoFun : @Measurable (CoefficientField d) (RawCoeffField d) _
      (probeFieldSigma d) CoefficientField.toFun := by
    have h : @Measurable (CoefficientField d) (RawCoeffField d)
        (instMeasurableSpaceCoefficientField d) (observableFieldSigma d)
        CoefficientField.toFun := Measurable.of_comap_le le_rfl
    exact h.mono le_rfl le_sup_right
  exact hraw.comp htoFun

private theorem measurable_toRepoReg {d : ℕ} : Measurable (toRepoReg (d := d)) := by
  refine _root_.Homogenization.measurable_into_regCoeffField' ?_ ?_
  · intro y i j
    exact measurable_apply_entry_audit y i j
  · intro i j φ hφ
    exact measurable_entryTest_audit i j (isProbe_ofRepo hφ)

private theorem measurable_ofRepoReg {d : ℕ} : Measurable (ofRepoReg (d := d)) := by
  refine Measurable.of_comap_le ?_
  rw [carrierSigma_eq_join, MeasurableSpace.comap_sup]
  refine sup_le ?_ ?_
  · rw [MeasurableSpace.comap_comp]
    exact _root_.Homogenization.pointwiseSigmaR_le d
  · rw [MeasurableSpace.comap_generateFrom]
    refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨t, ⟨i, j, φ, hφ, u, hu, rfl⟩, rfl⟩
    exact _root_.Homogenization.measurable_entryTestR i j (isProbe_toRepo hφ) hu

/-- The audited carrier and the repository carrier are measurably equivalent
via the identity on the underlying data. -/
private def regEquiv (d : ℕ) :
    _root_.Homogenization.RegCoeffField d ≃ᵐ CoefficientField d where
  toEquiv :=
    { toFun := ofRepoReg
      invFun := toRepoReg
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  measurable_toFun := measurable_ofRepoReg
  measurable_invFun := measurable_toRepoReg

private theorem dirac_eq_map_ofRepoReg {d : ℕ} (a₀ : CoefficientField d) :
    (Measure.dirac a₀ : Measure (CoefficientField d)) =
      Measure.map (ofRepoReg (d := d)) (Measure.dirac (toRepoReg a₀)) := by
  rw [Measure.map_dirac measurable_ofRepoReg, ofRepoReg_toRepoReg]

private theorem ae_dirac_iff_repo {d : ℕ} (a₀ : CoefficientField d)
    {p : CoefficientField d → Prop} :
    (∀ᵐ a ∂(Measure.dirac a₀ : Measure (CoefficientField d)), p a) ↔
      ∀ᵐ b ∂(Measure.dirac (toRepoReg a₀) :
        Measure (_root_.Homogenization.RegCoeffField d)), p (ofRepoReg b) := by
  rw [dirac_eq_map_ofRepoReg a₀,
    show Measure.map (ofRepoReg (d := d)) (Measure.dirac (toRepoReg a₀))
        = Measure.map (regEquiv d) (Measure.dirac (toRepoReg a₀)) from rfl,
    ← MeasurableEquiv.map_ae]
  exact Filter.eventually_map

private theorem dirac_real_eq {d : ℕ} (a₀ : CoefficientField d)
    (E : Set (CoefficientField d)) :
    (Measure.dirac a₀ : Measure (CoefficientField d)).real E =
      (Measure.dirac (toRepoReg a₀) :
        Measure (_root_.Homogenization.RegCoeffField d)).real (ofRepoReg ⁻¹' E) := by
  rw [measureReal_def, measureReal_def, dirac_eq_map_ofRepoReg a₀]
  congr 1
  exact (regEquiv d).map_apply E

/-! ## 6. Ellipticity: reconstructing the two bookkeeping conjuncts -/

private theorem measurableSet_interior {d : ℕ} (Q : TriadicCube d) :
    MeasurableSet Q.interior :=
  _root_.Homogenization.measurableSet_openCubeSet (toRepoTriadicCube Q)

private theorem aestronglyMeasurable_restrict_entry {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) (a : CoefficientField d) (i j : Fin d) :
    AEStronglyMeasurable
      (fun x : Vec d => _root_.Homogenization.restrictCoeffField U a.toFun x i j)
      (MeasureTheory.volume.restrict U) := by
  have hEq :
      (fun x : Vec d =>
        _root_.Homogenization.restrictCoeffField U a.toFun x i j)
      = Set.indicator U (fun x => a.toFun x i j) := by
    funext x
    by_cases hx : x ∈ U <;>
      simp [_root_.Homogenization.restrictCoeffField, hx, Set.indicator_of_mem,
        Set.indicator_of_notMem]
  rw [hEq]
  exact ((a.entry_measurable i j).indicator hU).stronglyMeasurable.aestronglyMeasurable

private theorem toRepo_EllipticOnCube {d : ℕ} {lam Lam : ℝ} {Q : TriadicCube d}
    {a : CoefficientField d} (h : EllipticOnCube lam Lam Q a) :
    _root_.Homogenization.Book.Ch04.AEEllipticOn lam Lam Q.interior
      (toRepoReg a) := by
  refine ⟨measurableSet_interior Q, ?_, ?_⟩
  · intro i j
    exact aestronglyMeasurable_restrict_entry (measurableSet_interior Q) a i j
  · exact h

private theorem toRepo_LocallyUniformlyElliptic {d : ℕ} {a : CoefficientField d}
    (ha : LocallyUniformlyElliptic a) :
    _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (toRepoReg a) := by
  intro Q
  obtain ⟨lam, Lam, hlam, hle, hEll⟩ := ha (ofRepoTriadicCube Q)
  exact ⟨lam, Lam, hlam, hle, toRepo_EllipticOnCube hEll⟩

/-! ## 7. Weak `H¹` functions -/

private def toRepoH1 {d : ℕ} {Q : TriadicCube d} (u : WeakH1 Q.interior) :
    _root_.Homogenization.H1Function
      (_root_.Homogenization.Book.Ch02.cubeDomain
        (toRepoTriadicCube Q) : Set (Vec d)) where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memL2
  gradMemL2 := u.gradMemL2
  hasWeakGradient := u.hasWeakGradient

private def ofRepoH10 {d : ℕ} {Q : TriadicCube d}
    (u : _root_.Homogenization.H10Function
      (_root_.Homogenization.Book.Ch02.cubeDomain
        (toRepoTriadicCube Q) : Set (Vec d))) :
    WeakH10 Q.interior where
  toFun := u.toH1Function.toFun
  grad := u.toH1Function.grad
  memL2 := u.toH1Function.memL2
  gradMemL2 := u.toH1Function.gradMemL2
  hasWeakGradient := u.toH1Function.hasWeakGradient
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_compactSupport := u.approx_hasCompactSupport
  approx_supportedIn := u.approx_support_subset
  tendsto_approx := u.tendsto_approx
  tendsto_approx_grad := u.tendsto_approx_grad

private def toRepoH10 {d : ℕ} {Q : TriadicCube d} (u : WeakH10 Q.interior) :
    _root_.Homogenization.H10Function
      (_root_.Homogenization.Book.Ch02.cubeDomain
        (toRepoTriadicCube Q) : Set (Vec d)) where
  toFun := u.toWeakH1.toFun
  grad := u.toWeakH1.grad
  memL2 := u.toWeakH1.memL2
  gradMemL2 := u.toWeakH1.gradMemL2
  hasWeakGradient := u.toWeakH1.hasWeakGradient
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_hasCompactSupport := u.approx_compactSupport
  approx_support_subset := u.approx_supportedIn
  tendsto_approx := u.tendsto_approx
  tendsto_approx_grad := u.tendsto_approx_grad

@[simp] private theorem toRepoH1_toFun {d : ℕ} {Q : TriadicCube d}
    (u : WeakH1 Q.interior) : (toRepoH1 u).toFun = u.toFun := rfl

@[simp] private theorem toRepoH1_grad {d : ℕ} {Q : TriadicCube d}
    (u : WeakH1 Q.interior) : (toRepoH1 u).grad = u.grad := rfl

@[simp] private theorem ofRepoH10_grad {d : ℕ} {Q : TriadicCube d}
    (u : _root_.Homogenization.H10Function
      (_root_.Homogenization.Book.Ch02.cubeDomain
        (toRepoTriadicCube Q) : Set (Vec d))) :
    (ofRepoH10 u).toWeakH1.grad = u.toH1Function.grad := rfl

@[simp] private theorem toRepoH10_toFun {d : ℕ} {Q : TriadicCube d}
    (u : WeakH10 Q.interior) :
    (toRepoH10 u).toH1Function.toFun = u.toWeakH1.toFun := rfl

/-! ## 8. Comparison pairs -/

private def toRepoComparisonPair {d : ℕ} [NeZero d]
    {sigmaBar : ℝ} (hsigma : 0 < sigmaBar)
    {a : CoefficientField d}
    (haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (toRepoReg a))
    {m : ℕ} {g : Vec d → Vec d}
    (pair : ComparisonPair sigmaBar a (originCube d m) g) :
    _root_.Homogenization.Book.Ch05.Section57.assemblyComparisonDatumOfScalar
      sigmaBar hsigma (toRepoReg a) haRepo m g where
  u := toRepoH1 pair.u
  v := toRepoH1 pair.v
  uWeakSolution := by
    intro φ
    have hφ := pair.u_solves (ofRepoH10 φ)
    simpa [_root_.Homogenization.Book.Ch03.IsForcedEquation, SolvesEquation,
      _root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily,
      _root_.Homogenization.Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
      _root_.Homogenization.Book.Ch04.coeffOnOfAEEllipticOn,
      _root_.Homogenization.Book.Ch02.cubeDomain_coe,
      _root_.Homogenization.Book.Ch05.Section57.assemblyOriginCube,
      _root_.Homogenization.originCube, originCube, toRepoTriadicCube,
      _root_.Homogenization.openCubeSet, TriadicCube.interior,
      _root_.Homogenization.cubeScaleFactor, TriadicCube.side,
      toRepoH1, ofRepoH10, toRepoReg_toFun,
      _root_.Homogenization.vecDot, vecDot,
      _root_.Homogenization.matVecMul, matVecMul] using hφ
  vWeakSolution := by
    intro φ
    have hφ := pair.v_solves (ofRepoH10 φ)
    simpa [_root_.Homogenization.Book.Ch03.IsConstantCoeffForcedEquation,
      SolvesEquation,
      _root_.Homogenization.Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar,
      _root_.Homogenization.Book.Ch05.Section57.scalarConstantCoeffMatrix,
      _root_.Homogenization.Book.Ch05.Section57.assemblyOriginCube,
      _root_.Homogenization.originCube, originCube, toRepoTriadicCube,
      _root_.Homogenization.Book.Ch02.cubeDomain_coe,
      _root_.Homogenization.openCubeSet, TriadicCube.interior,
      _root_.Homogenization.cubeScaleFactor, TriadicCube.side,
      toRepoH1, ofRepoH10,
      _root_.Homogenization.scalarMatrix, scalarMatrix,
      _root_.Homogenization.vecDot, vecDot,
      _root_.Homogenization.matVecMul, matVecMul] using hφ
  zeroTraceDifference := by
    obtain ⟨w, hw⟩ := pair.sameBoundaryData
    exact ⟨toRepoH10 w, hw⟩

private theorem energyNorm_toRepo {d : ℕ} [NeZero d]
    {a : CoefficientField d}
    {haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (toRepoReg a)}
    {m : ℕ} (u : WeakH1 (originCube d m).interior) :
    _root_.Homogenization.Book.Ch03.h1EnergyNormOnCube
        (_root_.Homogenization.Book.MainResults.originCube d m)
        (_root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily
          (toRepoReg a) haRepo)
        (toRepoH1 u) =
      energyNorm (originCube d m) a.toFun u := by
  simp [_root_.Homogenization.Book.Ch03.h1EnergyNormOnCube,
    _root_.Homogenization.Book.Ch03.localizedCoeffEnergyValue,
    _root_.Homogenization.Book.Ch03.normalizedSetAverage,
    energyNorm, _root_.Homogenization.volumeAverage, volumeAverage,
    _root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily,
    _root_.Homogenization.Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
    _root_.Homogenization.Book.Ch04.coeffOnOfAEEllipticOn,
    _root_.Homogenization.Book.Ch02.cubeDomain_coe,
    _root_.Homogenization.Book.MainResults.originCube,
    _root_.Homogenization.Book.Ch05.Section57.assemblyOriginCube,
    _root_.Homogenization.originCube, originCube,
    _root_.Homogenization.openCubeSet, TriadicCube.interior,
    _root_.Homogenization.cubeScaleFactor, TriadicCube.side,
    _root_.Homogenization.symmPart, symmPart, toRepoReg_toFun,
    _root_.Homogenization.vecDot, vecDot,
    _root_.Homogenization.matVecMul, matVecMul, toRepoH1]

private theorem comparisonDefect_toRepo {d : ℕ} [NeZero d]
    {sigmaBar : ℝ} (hsigma : 0 < sigmaBar)
    {a : CoefficientField d}
    {haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (toRepoReg a)}
    {m : ℕ} {g : Vec d → Vec d}
    (pair : ComparisonPair sigmaBar a (originCube d m) g) :
    _root_.Homogenization.Book.Ch03.Legacy.homogenizationComparisonNegativeSobolevLHS
        (_root_.Homogenization.Book.MainResults.originCube d m)
        (_root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily
          (toRepoReg a) haRepo)
        (_root_.Homogenization.Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar
          sigmaBar hsigma)
        comparisonS (toRepoH1 pair.u) (toRepoH1 pair.v) =
      comparisonDefect pair := by
  have hgrad :
      _root_.Homogenization.Book.Ch03.homogenizationComparisonConstantGradientField
          (_root_.Homogenization.Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar
            sigmaBar hsigma)
          (toRepoH1 pair.u) (toRepoH1 pair.v) =
        constantGradientMismatch sigmaBar pair.u pair.v := by
    funext x i
    simp [_root_.Homogenization.Book.Ch03.homogenizationComparisonConstantGradientField,
      constantGradientMismatch,
      _root_.Homogenization.Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar,
      _root_.Homogenization.Book.Ch05.Section57.scalarConstantCoeffMatrix,
      _root_.Homogenization.scalarMatrix, scalarMatrix,
      _root_.Homogenization.matVecMul, matVecMul, toRepoH1]
  have hflux :
      _root_.Homogenization.Book.Ch03.homogenizationComparisonFluxField
          (_root_.Homogenization.Book.MainResults.originCube d m)
          (_root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily
            (toRepoReg a) haRepo)
          (_root_.Homogenization.Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar
            sigmaBar hsigma)
          (toRepoH1 pair.u) (toRepoH1 pair.v) =
        fluxMismatch a.toFun sigmaBar pair.u pair.v := by
    funext x i
    simp [_root_.Homogenization.Book.Ch03.homogenizationComparisonFluxField,
      fluxMismatch,
      _root_.Homogenization.Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar,
      _root_.Homogenization.Book.Ch05.Section57.scalarConstantCoeffMatrix,
      _root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily,
      _root_.Homogenization.Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
      _root_.Homogenization.Book.Ch04.coeffOnOfAEEllipticOn,
      _root_.Homogenization.Book.Ch02.cubeDomain_coe,
      _root_.Homogenization.originCube,
      _root_.Homogenization.scalarMatrix, scalarMatrix, toRepoReg_toFun,
      _root_.Homogenization.matVecMul, matVecMul, toRepoH1]
  unfold
    _root_.Homogenization.Book.Ch03.Legacy.homogenizationComparisonNegativeSobolevLHS
    comparisonDefect
  rw [hgrad, hflux, ← toRepo_originCube (d := d) m,
    scaledNegativeVectorNorm_toRepo, scaledNegativeVectorNorm_toRepo]

private theorem comparisonData_toRepo {d : ℕ} [NeZero d]
    {sigmaBar : ℝ} {a : CoefficientField d}
    {haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (toRepoReg a)}
    {m : ℕ} {g : Vec d → Vec d}
    (pair : ComparisonPair sigmaBar a (originCube d m) g) :
    Real.sqrt sigmaBar *
        _root_.Homogenization.Book.Ch03.h1EnergyNormOnCube
          (_root_.Homogenization.Book.MainResults.originCube d m)
          (_root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily
            (toRepoReg a) haRepo)
          (toRepoH1 pair.u) +
      _root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
        (_root_.Homogenization.Book.MainResults.originCube d m) comparisonS g =
      comparisonData pair := by
  rw [energyNorm_toRepo (haRepo := haRepo), ← toRepo_originCube (d := d) m,
    scaledForceH34Seminorm_toRepo]
  rfl

/-! ## 9. The audited theorem -/

namespace PeriodicGeneral

/-- Fixed-exponent homogenization comparison for a deterministic periodic
coefficient field, stated for the Dirac law concentrated at that field.

The constants `C`, `alpha`, `Cscale` are chosen before the field and its
ellipticity bounds, hence depend only on `d`.  The estimate bounds the
comparison defect (a scale-normalized `H⁻³ᐟ⁴` distance between the
heterogeneous and homogenized flux/gradient pairs) by the energy data times the
algebraic rate `(3 ^ m / X a) ^ (-alpha)`, where `3 ^ m` is the cube sidelength
and `X a` the minimal scale. -/
theorem periodicGeneral_comparison
    {d : ℕ} [NeZero d] :
    ∃ C alpha Cscale : ℝ,
      0 < C ∧ 0 < alpha ∧ 0 < Cscale ∧
      ∀ S : Setup d,
        ∃ sigmaBar : ℝ,
          0 < sigmaBar ∧
          ∃ X : CoefficientField d → ℝ,
            S.IsMinimalScale X Cscale ∧
            ∀ᵐ a ∂Measure.dirac S.a₀,
              ∀ (_ha : LocallyUniformlyElliptic a)
                {m : ℕ} {g : Vec d → Vec d}
                (pair : ComparisonPair sigmaBar a (originCube d m) g),
                X a ≤ (3 : ℝ) ^ m →
                ForceInH34 (originCube d m) g →
                comparisonDefect pair ≤
                  C * ((3 : ℝ) ^ m / X a) ^ (-alpha) * comparisonData pair := by
  obtain ⟨C, alpha, Cscale, hC, halpha, hCscale, hmain⟩ :=
    _root_.Homogenization.Examples.Periodic.periodicGeneral_comparison (d := d)
  refine ⟨C, alpha, Cscale, hC, halpha, hCscale, ?_⟩
  intro S
  have hperRepo :
      _root_.Homogenization.Examples.Periodic.IsPeriodicCoeffField
        (toRepoReg S.a₀).toFun := by
    intro z
    simpa [_root_.Homogenization.translateByInt,
      _root_.Homogenization.translateCoeffField,
      _root_.Homogenization.intVecToRealVec,
      translateCoeffField, intVecToRealVec] using S.periodic z
  have hisoRepo :
      _root_.Homogenization.Examples.Periodic.IsIsotropicCoeffField
        (toRepoReg S.a₀).toFun := by
    intro M hM
    obtain ⟨sigma, signs, hsigns, hM'⟩ := hM
    have hEq :
        (SignedPermutation.mk sigma (fun j => ⟨signs j, hsigns j⟩)).matrix = M := by
      funext i j
      exact (hM' i j).symm
    have h := S.signedCoordinateInvariant
      (SignedPermutation.mk sigma (fun j => ⟨signs j, hsigns j⟩))
    rw [← hEq]
    exact h
  have hadjRepo :
      _root_.Homogenization.Examples.Periodic.IsAdjointInvariantCoeffField
        (toRepoReg S.a₀).toFun := by
    simpa [_root_.Homogenization.adjointCoeffField,
      _root_.Homogenization.matTranspose, adjointCoeffField] using S.adjointInvariant
  have hellRepo :
      ∀ Q : _root_.Homogenization.TriadicCube d,
        _root_.Homogenization.Book.Ch04.AEEllipticOn S.lam S.Lam
          (_root_.Homogenization.openCubeSet Q) (toRepoReg S.a₀) := by
    intro Q
    exact toRepo_EllipticOnCube (S.uniformlyElliptic (ofRepoTriadicCube Q))
  let Srepo : _root_.Homogenization.Book.MainResults.Setup d :=
    _root_.Homogenization.Examples.Periodic.periodicSetup
      S.two_le_dim (toRepoReg S.a₀) S.lam S.Lam hperRepo hisoRepo hadjRepo
      S.lam_pos S.lam_le_Lam hellRepo
  let sigmaBar : ℝ :=
    _root_.Homogenization.Book.Ch05.Section57.barSigmaLimit Srepo.hP Srepo.hStruct
  have hsigma : 0 < sigmaBar := by
    dsimp [sigmaBar]
    exact Srepo.barSigmaLimit_pos
  obtain ⟨_sigmaBar, _hsigma, X, hX, hmainS⟩ :=
    hmain S.two_le_dim (toRepoReg S.a₀) S.lam S.Lam hperRepo hisoRepo hadjRepo
      S.lam_pos S.lam_le_Lam hellRepo
  refine ⟨sigmaBar, hsigma, fun a => X (toRepoReg a), ?_, ?_⟩
  · have hXmin :
        (∀ b, 1 ≤ X b) ∧
          _root_.Homogenization.IndependentSums.IsBigO
            (Measure.dirac (toRepoReg S.a₀))
            (_root_.Homogenization.IndependentSums.gammaSigma ((d : ℕ) : ℝ)) X
            (Real.exp (Cscale *
              (Real.log (2 + S.thetaHat)) ^ (2 : ℕ))) := by
      simpa [Srepo, Setup.thetaHat, Setup.coarseUpperBound,
        Setup.coarseInverseLowerBound,
        _root_.Homogenization.Book.MainResults.Setup.IsMinimalScale,
        _root_.Homogenization.Book.MainResults.Setup.thetaHat,
        _root_.Homogenization.Book.Ch05.Section57.mainResultsThetaHat,
        _root_.Homogenization.Book.Ch05.Section57.uniformUpperBlockConst,
        _root_.Homogenization.Book.Ch05.Section57.uniformLowerInvBlockConst,
        _root_.Homogenization.Examples.Periodic.periodicSetup,
        _root_.Homogenization.Examples.Periodic.dirac_setup,
        _root_.Homogenization.Examples.Periodic.diracCoeffLaw] using hX
    refine ⟨fun a => hXmin.1 (toRepoReg a), ?_⟩
    intro t ht
    rw [dirac_real_eq S.a₀]
    exact hXmin.2 ht
  · have hmainDirac :
        ∀ᵐ b ∂(Measure.dirac (toRepoReg S.a₀) :
            Measure (_root_.Homogenization.RegCoeffField d)),
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
      simpa [Srepo,
        _root_.Homogenization.Examples.Periodic.periodicSetup,
        _root_.Homogenization.Examples.Periodic.dirac_setup,
        _root_.Homogenization.Examples.Periodic.diracCoeffLaw] using hmainS
    rw [ae_dirac_iff_repo S.a₀]
    filter_upwards [hmainDirac] with b hmain_b
    intro ha m g pair hXm hg
    let haRepo :
        _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField b :=
      toRepo_LocallyUniformlyElliptic ha
    let repoPair : Srepo.ComparisonPair b haRepo m g := by
      simpa [Srepo, sigmaBar,
        _root_.Homogenization.Book.MainResults.Setup.ComparisonPair,
        _root_.Homogenization.Book.MainResults.Setup.homogenizedMatrix] using
        toRepoComparisonPair (a := ofRepoReg b) hsigma haRepo pair
    have hgRepo :
        _root_.Homogenization.Book.Ch03.Legacy.ForceSobolevRegularity
          (_root_.Homogenization.Book.MainResults.originCube d m)
          _root_.Homogenization.Book.MainResults.fixedComparisonS g := by
      simpa [comparisonS,
        _root_.Homogenization.Book.MainResults.fixedComparisonS,
        toRepo_originCube] using
        forceInH34_toRepo (originCube d m) g hg
    have hstep := hmain_b haRepo repoPair hXm hgRepo
    have hdefect :
        Srepo.comparisonDefect
            _root_.Homogenization.Book.MainResults.fixedComparisonS repoPair =
          comparisonDefect pair := by
      simpa [repoPair, toRepoComparisonPair,
        _root_.Homogenization.Book.MainResults.Setup.comparisonDefect,
        _root_.Homogenization.Book.MainResults.Setup.homogenizedMatrix,
        Srepo, sigmaBar, comparisonS,
        _root_.Homogenization.Book.MainResults.fixedComparisonS] using
        (comparisonDefect_toRepo (d := d) (sigmaBar := sigmaBar)
          (a := ofRepoReg b) (haRepo := haRepo) hsigma pair)
    have hdata :
        Srepo.comparisonData
            _root_.Homogenization.Book.MainResults.fixedComparisonS repoPair =
          comparisonData pair := by
      simpa [repoPair, toRepoComparisonPair,
        _root_.Homogenization.Book.MainResults.Setup.comparisonData,
        _root_.Homogenization.Book.MainResults.Setup.homogenizedMatrix,
        Srepo, sigmaBar, comparisonS,
        _root_.Homogenization.Book.MainResults.fixedComparisonS] using
        (comparisonData_toRepo (d := d) (sigmaBar := sigmaBar)
          (a := ofRepoReg b) (haRepo := haRepo) pair)
    rw [hdefect, hdata] at hstep
    exact hstep

end PeriodicGeneral

end

end StatementAudit
end Homogenization
