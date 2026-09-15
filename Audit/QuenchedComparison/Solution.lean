import Mathlib
import Homogenization.Book.MainResults
import Homogenization.Sobolev.Fractional.ClassicalDualComparison
import Audit.QuenchedComparison.SolutionBasic

attribute [-instance] Homogenization.instMeasurableSpaceVec
attribute [-instance] Homogenization.instMeasurableSpaceMat
attribute [-instance] Homogenization.instMeasurableSpaceCoeffField

/-!
# Solution for the quenched comparison theorem challenge

This file is the comparator solution surface for the uniformly elliptic
quenched homogenization comparison theorem.

The corresponding challenge imports only Mathlib.  This solution imports the
repository theorem and proves the same `StatementAudit` theorem surface, whose
definitional vocabulary is reproduced verbatim in
`Audit/QuenchedComparison/SolutionBasic.lean`.

**Do not add repository imports to `SolutionBasic.lean`.**  The comparator does
not merely compare theorem statements: it walks the whole dependency closure and
requires each constant to agree with the challenge's.  A vocabulary constant
whose type mentions `fderiv`, `eLpNorm`, or any other instance-carrying Mathlib
notion picks up whatever instance path its *own* module's environment offers, so
adding a repository import to the vocabulary module changes those paths and
makes constants such as `WeakH10.mk` differ from the challenge's even though the
source text is byte-identical.  `SolutionBasic.lean` therefore imports only
Mathlib, exactly like the challenge; the repository import and the three
`attribute [-instance]` erasures live here, where they are needed for the
bridges below.  Importing an olean cannot retroactively re-elaborate the
constants inside it, so the vocabulary stays challenge-identical.

Everything between the vocabulary and the final theorem is private bridge
machinery translating the challenge's self-contained presentation into the
repository's objects.  The bridges are grouped by the equivalence obligations they discharge:

* **A/B** — the observable σ-algebra on `CoefficientField d` and the
  carrier-law/raw-law transport (`repoSigma_eq_comap_toFun`,
  `map_toFun_injective`, `map_eq_iff_lawInvariantUnder`, `map_transport`);
* **C** — signed permutations as data versus matrices with an
  `IsSignedPermutationMatrix` witness (`isSignedPermutationMatrix_matrix`,
  `exists_signedPermutation`);
* **D** — restriction σ-algebras
  (`comap_toRepoField_restrictionSigmaR_le`);
* **E** — reconstruction of the `MeasurableSet`/`AEStronglyMeasurable`
  conjuncts dropped from `UniformlyEllipticRealization`
  (`aeEllipticOn_of_uniformlyEllipticRealization`);
* **F** — witness-free comparison pairs (`toRepoComparisonPair`);
* **G** — the single weak-equation predicate (discharged definitionally inside
  `toRepoComparisonPair`);
* **H** — the fixed-exponent Sobolev comparisons (`Sobolev34` section);
* **I** — the minimal-scale tail (discharged inside the final proof).

The main source correspondences are:

* ambient fields and ellipticity: `Homogenization/Ambient/CoefficientField.lean`;
* the honest-fields carrier: `Homogenization/Probability/RegCoeffField.lean`;
* coefficient laws and uniform ellipticity: `Homogenization/Book/Ch04/RestrictionLaw.lean`
  and `Homogenization/Book/Ch05/Theorems/Section57/UniformEllipticityBridge.lean`;
* cubes, weak equations, and energy quantities: `Homogenization/Book/Ch02` and
  `Homogenization/Book/Ch03`;
* positive and negative Sobolev quantities: `Homogenization/Besov` and
  `Homogenization/Sobolev/Fractional`;
* the public theorem surface: `Homogenization/Book/MainResults.lean`.
-/

namespace Homogenization
namespace StatementAudit

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-! ## Triadic cubes

The audit `TriadicCube` and the repository `Homogenization.TriadicCube` are
distinct inductive types with the same fields. The conversion preserves their
geometric and measure-theoretic definitions. -/

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

/-! ### Definitional cube dictionaries

Every geometric and averaging quantity of the audit vocabulary is the repository
quantity at the transported cube, definitionally. -/

private theorem side_toRepo {d : ℕ} (Q : TriadicCube d) :
    _root_.Homogenization.cubeScaleFactor (toRepoCube Q) = Q.side := rfl

private theorem interior_toRepo {d : ℕ} (Q : TriadicCube d) :
    _root_.Homogenization.openCubeSet (toRepoCube Q) = Q.interior := rfl

private theorem normalizedMeasure_toRepo {d : ℕ} (Q : TriadicCube d) :
    _root_.Homogenization.normalizedCubeMeasure (toRepoCube Q) =
      Q.normalizedMeasure := rfl

private theorem average_toRepo {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) :
    _root_.Homogenization.cubeAverage (toRepoCube Q) f = Q.average f := rfl

private theorem toRepo_originCube {d : ℕ} [NeZero d] (m : ℕ) :
    toRepoCube (originCube d m) =
      _root_.Homogenization.Book.MainResults.originCube d m := rfl

/-! ## Obligation H: the fixed `s = 3/4`, `p = q = 2` Sobolev identifications -/

private theorem toReal_two : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by
  norm_num

private theorem kernel_toRepo {d : ℕ} (u : Vec d → ℝ) :
    _root_.Homogenization.Gagliardo.gagliardoKernel (d := d) comparisonS
        (2 : ℝ≥0∞) u = Sobolev34.kernel u := by
  funext z
  rw [_root_.Homogenization.Gagliardo.gagliardoKernel,
    _root_.Homogenization.Gagliardo.kernelExponent, Sobolev34.kernel,
    Sobolev34.kernelExponent]
  simp only [toReal_two, smul_eq_mul]

private theorem memH34_toRepo {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) :
    _root_.Homogenization.Book.Ch01.Legacy.MemFractionalSobolev (toRepoCube Q)
        comparisonS (2 : ℝ≥0∞) u ↔ Sobolev34.MemH34 Q u := by
  rw [_root_.Homogenization.Book.Ch01.Legacy.MemFractionalSobolev,
    _root_.Homogenization.Gagliardo.MemWsp, Sobolev34.MemH34, kernel_toRepo]
  exact Iff.rfl

private theorem seminorm_toRepo {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) :
    _root_.Homogenization.Book.Ch01.Legacy.fractionalSobolevSeminorm (toRepoCube Q)
        comparisonS (2 : ℝ≥0∞) u = Sobolev34.seminorm Q u := by
  rw [_root_.Homogenization.Book.Ch01.Legacy.fractionalSobolevSeminorm,
    _root_.Homogenization.Gagliardo.cubeGagliardoSeminorm,
    _root_.Homogenization.Gagliardo.cubeGagliardoESeminorm, kernel_toRepo]
  rfl

private theorem forceInH34_toRepo {d : ℕ} (Q : TriadicCube d)
    (g : Vec d → Vec d) (hg : ForceInH34 Q g) :
    _root_.Homogenization.Book.Ch03.Legacy.ForceSobolevRegularity (toRepoCube Q)
      comparisonS g := by
  intro i
  exact (memH34_toRepo Q (fun x => g x i)).2 (hg i)

private theorem scaledForceH34Seminorm_toRepo {d : ℕ} (Q : TriadicCube d)
    (g : Vec d → Vec d) :
    _root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
        (toRepoCube Q) comparisonS g = scaledForceH34Seminorm Q g := by
  rw [_root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo,
    _root_.Homogenization.cubeBesovScaleWeight, scaledForceH34Seminorm,
    neg_neg, side_toRepo]
  refine congrArg (fun r => Q.side ^ comparisonS * r) ?_
  exact Finset.sum_congr rfl fun i _hi => seminorm_toRepo Q (fun x => g x i)

/-! ### The same identifications at the origin cube, in the repository's own
spelling of the cube and the fixed exponent.  Both are the general lemma above
at `Q = originCube d m`; only the presentation of the two definitionally equal
arguments differs, which is what makes them usable by `rw` in the final proof
(rewriting the cube itself is blocked by the cube-indexed `H1Function`). -/

private theorem scaledForceH34Seminorm_toRepo_origin {d : ℕ} [NeZero d] (m : ℕ)
    (g : Vec d → Vec d) :
    _root_.Homogenization.Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
        (_root_.Homogenization.Book.MainResults.originCube d m)
        _root_.Homogenization.Book.MainResults.fixedComparisonS g =
      scaledForceH34Seminorm (originCube d m) g :=
  scaledForceH34Seminorm_toRepo (originCube d m) g

/-! ## The carrier bridge (obligations A and B)

The audit carrier `CoefficientField d` and the repository carrier
`Homogenization.RegCoeffField d` carry the same data, and their σ-algebras are
both the pullback of `observableFieldSigma d` along the underlying raw field.
The identity on the underlying data is therefore a measurable equivalence. -/

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

private theorem toRepoField_ofRepoField {d : ℕ}
    (a : _root_.Homogenization.RegCoeffField d) :
    toRepoField (ofRepoField a) = a := rfl

private theorem ofRepoField_toRepoField {d : ℕ} (a : CoefficientField d) :
    ofRepoField (toRepoField a) = a := rfl

private theorem isProbe_toRepo {d : ℕ} {φ : Vec d → ℝ} (h : IsProbe φ) :
    _root_.Homogenization.IsProbeR (d := d) φ :=
  ⟨h.measurable, h.bounded, h.compactSupport⟩

private theorem isProbe_ofRepo {d : ℕ} {φ : Vec d → ℝ}
    (h : _root_.Homogenization.IsProbeR (d := d) φ) : IsProbe φ :=
  ⟨h.measurable, h.bounded, h.hasCompactSupport⟩

private theorem measurable_into_sup {α β : Type*} {dom : MeasurableSpace α}
    {m1 m2 : MeasurableSpace β} {f : α → β}
    (h1 : @Measurable α β dom m1 f) (h2 : @Measurable α β dom m2 f) :
    @Measurable α β dom (m1 ⊔ m2) f := by
  rw [measurable_iff_comap_le, MeasurableSpace.comap_sup]
  exact sup_le h1.comap_le h2.comap_le

/-- The underlying raw field of an audit carrier element is measurable into the
observable σ-algebra: the carrier σ-algebra is by definition its pullback. -/
private theorem measurable_coefficientField_toFun {d : ℕ} :
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
  exact ((h2.comp h1).mono le_sup_left le_rfl).comp measurable_coefficientField_toFun

private theorem measurable_entryTest_audit {d : ℕ} (i j : Fin d) {φ : Vec d → ℝ}
    (hφ : IsProbe φ) :
    Measurable (fun a : CoefficientField d => entryTest i j φ a.toFun) := by
  have h : @Measurable (RawCoeffField d) ℝ (probeFieldSigma d) _
      (entryTest i j φ) := by
    intro t ht
    exact MeasurableSpace.measurableSet_generateFrom ⟨i, j, φ, hφ, t, ht, rfl⟩
  exact (h.mono le_sup_right le_rfl).comp measurable_coefficientField_toFun

private theorem measurable_toRepoField {d : ℕ} :
    Measurable (toRepoField (d := d)) := by
  refine _root_.Homogenization.measurable_into_regCoeffField' ?_ ?_
  · intro y i j
    exact measurable_apply_entry_audit y i j
  · intro i j φ hφ
    exact measurable_entryTest_audit i j (isProbe_ofRepo hφ)

private theorem measurable_ofRepoField {d : ℕ} :
    Measurable (ofRepoField (d := d)) := by
  refine Measurable.of_comap_le ?_
  rw [instMeasurableSpaceCoefficientField, MeasurableSpace.comap_comp,
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

/-- **Obligation A.**  The repository carrier σ-algebra is the pullback of the
observable σ-algebra on raw fields, exactly like the audit carrier σ-algebra. -/
private theorem repoSigma_eq_comap_toFun {d : ℕ} :
    _root_.Homogenization.instMeasurableSpaceRegCoeffField d
      = MeasurableSpace.comap
          (fun b : _root_.Homogenization.RegCoeffField d => b.toFun)
          (observableFieldSigma d) := by
  have h1 : MeasurableSpace.comap (ofRepoField (d := d))
        (instMeasurableSpaceCoefficientField d)
      = _root_.Homogenization.instMeasurableSpaceRegCoeffField d := by
    refine le_antisymm (measurable_iff_comap_le.mp measurable_ofRepoField) ?_
    intro s hs
    exact ⟨toRepoField ⁻¹' s, measurable_toRepoField hs, rfl⟩
  rw [← h1, instMeasurableSpaceCoefficientField, MeasurableSpace.comap_comp]
  rfl

private theorem ae_map_toRepoField_iff {d : ℕ}
    {μ : Measure (CoefficientField d)}
    {p : _root_.Homogenization.RegCoeffField d → Prop} :
    (∀ᵐ b ∂Measure.map (toRepoField (d := d)) μ, p b) ↔
      ∀ᵐ a ∂μ, p (toRepoField a) := by
  rw [show Measure.map (toRepoField (d := d)) μ
      = Measure.map (fieldEquiv d).symm μ from rfl, ← MeasurableEquiv.map_ae]
  exact Filter.eventually_map

private theorem map_toRepoField_real_eq {d : ℕ}
    (μ : Measure (CoefficientField d))
    (E : Set (_root_.Homogenization.RegCoeffField d)) :
    (Measure.map (toRepoField (d := d)) μ).real E =
      μ.real (toRepoField ⁻¹' E) := by
  rw [measureReal_def, measureReal_def,
    show Measure.map (toRepoField (d := d)) μ
      = Measure.map (fieldEquiv d).symm μ from rfl,
    ((fieldEquiv d).symm).map_apply E]
  rfl

/-- Pushforward along `toFun` is injective on carrier measures: every measurable
carrier set is a `toFun`-preimage of an observable set. -/
private theorem map_toFun_injective {d : ℕ}
    {mu nu : Measure (CoefficientField d)}
    (h : @Measure.map _ _ _ (observableFieldSigma d)
        (fun a : CoefficientField d => a.toFun) mu
      = @Measure.map _ _ _ (observableFieldSigma d)
        (fun a : CoefficientField d => a.toFun) nu) :
    mu = nu := by
  refine Measure.ext fun S hS => ?_
  obtain ⟨S0, hS0, rfl⟩ :
      ∃ S0, MeasurableSet[observableFieldSigma d] S0 ∧
        (fun a : CoefficientField d => a.toFun) ⁻¹' S0 = S := hS
  rw [← Measure.map_apply measurable_coefficientField_toFun hS0,
      ← Measure.map_apply measurable_coefficientField_toFun hS0, h]

/-- **Obligation B.**  Carrier-pushforward invariance and observable-law
invariance are equivalent, for any measurable carrier transformation `Tc`
intertwining with the raw transformation `T`. -/
private theorem map_eq_of_lawInvariantUnder {d : ℕ} (P : CoefficientLaw d)
    (Tc : CoefficientField d → CoefficientField d)
    (T : RawCoeffField d → RawCoeffField d)
    (hcomm : ∀ a, (Tc a).toFun = T a.toFun) (hTc : Measurable Tc)
    (hT : LawInvariantUnder P T) :
    Measure.map Tc P = P := by
  have hfun : (fun a : CoefficientField d => (Tc a).toFun)
      = fun a : CoefficientField d => T a.toFun := funext hcomm
  have hkey : @Measure.map _ _ _ (observableFieldSigma d)
        (fun a : CoefficientField d => a.toFun) (Measure.map Tc P)
      = rawLawAfter P T := by
    rw [Measure.map_map measurable_coefficientField_toFun hTc]
    exact congrArg (fun f => @Measure.map _ _ _ (observableFieldSigma d) f P) hfun
  refine map_toFun_injective ?_
  rw [hkey]
  exact hT

/-- Transport a carrier-law invariance along the carrier equivalence. -/
private theorem map_transport {d : ℕ} {P : CoefficientLaw d}
    (Tc : CoefficientField d → CoefficientField d)
    (Trepo : _root_.Homogenization.RegCoeffField d →
      _root_.Homogenization.RegCoeffField d)
    (hTrepo : Measurable Trepo)
    (hEq : Tc = ofRepoField ∘ Trepo ∘ toRepoField)
    (hInv : Measure.map Tc P = P) :
    Measure.map Trepo (Measure.map (toRepoField (d := d)) P)
      = Measure.map (toRepoField (d := d)) P := by
  have hTc_meas : Measurable Tc := by
    rw [hEq]
    exact measurable_ofRepoField.comp (hTrepo.comp measurable_toRepoField)
  have hcomp : Trepo ∘ toRepoField = toRepoField ∘ Tc := by
    funext a
    have h := congrFun hEq a
    show Trepo (toRepoField a) = toRepoField (Tc a)
    rw [h]
    rfl
  calc
    Measure.map Trepo (Measure.map (toRepoField (d := d)) P)
        = Measure.map (Trepo ∘ toRepoField) P :=
          Measure.map_map hTrepo measurable_toRepoField
    _ = Measure.map (toRepoField ∘ Tc) P := by rw [hcomp]
    _ = Measure.map (toRepoField (d := d)) (Measure.map Tc P) :=
          (Measure.map_map measurable_toRepoField hTc_meas).symm
    _ = Measure.map (toRepoField (d := d)) P := by rw [hInv]

/-- The generic law-transport step: an observable-law invariance of the audit
law becomes a carrier-law invariance of the transported repository law. -/
private theorem map_repo_of_lawInvariantUnder {d : ℕ} {P : CoefficientLaw d}
    (T : RawCoeffField d → RawCoeffField d)
    (Trepo : _root_.Homogenization.RegCoeffField d →
      _root_.Homogenization.RegCoeffField d)
    (hTrepo : Measurable Trepo)
    (hcomm : ∀ b : _root_.Homogenization.RegCoeffField d,
      (Trepo b).toFun = T b.toFun)
    (hT : LawInvariantUnder P T) :
    Measure.map Trepo (Measure.map (toRepoField (d := d)) P)
      = Measure.map (toRepoField (d := d)) P := by
  refine map_transport (ofRepoField ∘ Trepo ∘ toRepoField) Trepo hTrepo rfl ?_
  refine map_eq_of_lawInvariantUnder P _ T (fun a => hcomm (toRepoField a)) ?_ hT
  exact measurable_ofRepoField.comp (hTrepo.comp measurable_toRepoField)

/-! ## Obligation C: signed permutations as data -/

private theorem isSignedPermutationMatrix_matrix {d : ℕ}
    (R : SignedPermutation d) :
    _root_.Homogenization.IsSignedPermutationMatrix R.matrix :=
  ⟨R.perm, fun i => (R.axisSign i : ℝ), fun i => (R.axisSign i).2, fun _ _ => rfl⟩

/-! ## Obligation D: restriction σ-algebras -/

private theorem comap_toRepoField_restrictionSigmaR_le {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) :
    MeasurableSpace.comap (toRepoField (d := d))
        (_root_.Homogenization.RestrictionSigmaR U hU) ≤ restrictionSigma U := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  obtain ⟨t0, ht0, rfl⟩ := ht
  rw [repoSigma_eq_comap_toFun] at ht0
  obtain ⟨T, hT, rfl⟩ := ht0
  exact ⟨T, hT, rfl⟩

/-! ## Obligation E: rebuilding the dropped ellipticity conjuncts -/

private theorem aestronglyMeasurable_restrict_entry {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) (a : CoefficientField d) (i j : Fin d) :
    AEStronglyMeasurable
      (fun x : Vec d =>
        _root_.Homogenization.restrictCoeffField U a.toFun x i j)
      (MeasureTheory.volume.restrict U) := by
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

private theorem aeEllipticOn_of_uniformlyEllipticRealization {d : ℕ}
    {lam Lam : ℝ} {a : CoefficientField d}
    (ha : UniformlyEllipticRealization lam Lam a)
    (Q : _root_.Homogenization.TriadicCube d) :
    _root_.Homogenization.Book.Ch04.AEEllipticOn lam Lam
      (_root_.Homogenization.openCubeSet Q) (toRepoField a) := by
  have hU : MeasurableSet (_root_.Homogenization.openCubeSet Q) :=
    _root_.Homogenization.measurableSet_openCubeSet Q
  refine ⟨hU, ?_, ?_⟩
  · intro i j
    exact aestronglyMeasurable_restrict_entry hU a i j
  · exact ha (ofRepoCube Q)

private theorem aeLocallyUniformlyElliptic_of_uniformlyEllipticRealization
    {d : ℕ} {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    {a : CoefficientField d} (ha : UniformlyEllipticRealization lam Lam a) :
    _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (toRepoField a) := fun Q =>
  ⟨lam, Lam, hlam, hle, aeEllipticOn_of_uniformlyEllipticRealization ha Q⟩

/-! ## The `Setup` conversion -/

private theorem toRepoLawCarrier {d : ℕ} [NeZero d] (S : Setup d) :
    _root_.Homogenization.Book.Ch04.RestrictionLawCarrier
      (Measure.map (toRepoField (d := d)) S.P) where
  isProbability := by
    have := S.isProbability
    exact Measure.isProbabilityMeasure_map measurable_toRepoField.aemeasurable
  ae_locally_uniformly_elliptic := by
    refine (ae_map_toRepoField_iff (μ := S.P)).2 ?_
    filter_upwards [S.uniformlyElliptic] with a ha
    exact aeLocallyUniformlyElliptic_of_uniformlyEllipticRealization
      S.lam_pos S.lam_le_Lam ha

private theorem toRepoStructuralLaw {d : ℕ} [NeZero d] (S : Setup d) :
    _root_.Homogenization.Book.Ch04.RestrictionStructuralLaw
      (Measure.map (toRepoField (d := d)) S.P) where
  stationary := by
    intro z
    refine map_repo_of_lawInvariantUnder
      (translateCoeffField (intVecToRealVec z))
      (_root_.Homogenization.translateReg
        (_root_.Homogenization.intVecToRealVec z))
      (_root_.Homogenization.measurable_translateReg _) (fun _ => rfl)
      (S.integerStationary z)
  unit_range := by
    intro U V hU hV hsep
    have haud := S.unitRange U V hU hV hsep
    rw [ProbabilityTheory.Indep_iff]
    intro s t hs ht
    have hs_amb : MeasurableSet s :=
      _root_.Homogenization.restrictionSigmaR_le U hU s hs
    have ht_amb : MeasurableSet t :=
      _root_.Homogenization.restrictionSigmaR_le V hV t ht
    have hs_aud : @MeasurableSet (CoefficientField d) (restrictionSigma U)
        (toRepoField ⁻¹' s) :=
      comap_toRepoField_restrictionSigmaR_le U hU _ ⟨s, hs, rfl⟩
    have ht_aud : @MeasurableSet (CoefficientField d) (restrictionSigma V)
        (toRepoField ⁻¹' t) :=
      comap_toRepoField_restrictionSigmaR_le V hV _ ⟨t, ht, rfl⟩
    have hprod := (ProbabilityTheory.Indep_iff _ _ _).1 haud _ _ hs_aud ht_aud
    rw [Measure.map_apply measurable_toRepoField (hs_amb.inter ht_amb),
      Measure.map_apply measurable_toRepoField hs_amb,
      Measure.map_apply measurable_toRepoField ht_amb]
    simpa [Set.preimage_inter] using hprod
  isotropic := by
    intro R hR
    obtain ⟨σ, s, hs, hRdef⟩ := hR
    let Rsp : SignedPermutation d :=
      { perm := σ
        axisSign := fun i => ⟨s i, hs i⟩ }
    have hmat : Rsp.matrix = R := by
      funext i j
      rw [hRdef i j]
      rfl
    refine map_repo_of_lawInvariantUnder (rotateCoeffField Rsp)
      (_root_.Homogenization.rotateReg R ⟨σ, s, hs, hRdef⟩)
      (_root_.Homogenization.measurable_rotateReg R ⟨σ, s, hs, hRdef⟩) ?_
      (S.signedCoordinateInvariant Rsp)
    intro b
    have hb : rotateCoeffField Rsp b.toFun
        = fun x => R.transpose * b.toFun (matVecMul R x) * R := by
      funext x
      simp only [rotateCoeffField, hmat]
    rw [hb]
    rfl
  adjoint_invariant := by
    refine map_repo_of_lawInvariantUnder adjointCoeffField
      _root_.Homogenization.adjointReg
      _root_.Homogenization.measurable_adjointReg (fun _ => rfl)
      S.adjointInvariant

private theorem toRepoUniformEllipticityBounds {d : ℕ} [NeZero d] (S : Setup d) :
    _root_.Homogenization.Book.Ch05.Section57.UniformEllipticityBounds
      (Measure.map (toRepoField (d := d)) S.P) S.lam S.Lam where
  lam_pos := S.lam_pos
  lam_le_Lam := S.lam_le_Lam
  aee_elliptic := by
    refine (ae_map_toRepoField_iff (μ := S.P)).2 ?_
    filter_upwards [S.uniformlyElliptic] with a ha Q
    exact aeEllipticOn_of_uniformlyEllipticRealization ha Q

private def toRepoSetup {d : ℕ} [NeZero d] (S : Setup d) :
    _root_.Homogenization.Book.MainResults.Setup d where
  two_le_dim := S.two_le_dim
  P := Measure.map (toRepoField (d := d)) S.P
  hP := toRepoLawCarrier S
  hStruct := toRepoStructuralLaw S
  lam := S.lam
  Lam := S.Lam
  hUE := toRepoUniformEllipticityBounds S

/-! ## Weak `H¹` bridges (obligation G) -/

private def toRepoH1 {d : ℕ} {U : Set (Vec d)} (u : WeakH1 U) :
    _root_.Homogenization.H1Function U where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memL2
  gradMemL2 := u.gradMemL2
  hasWeakGradient := u.hasWeakGradient

private def ofRepoH1 {d : ℕ} {U : Set (Vec d)}
    (u : _root_.Homogenization.H1Function U) : WeakH1 U where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memL2
  gradMemL2 := u.gradMemL2
  hasWeakGradient := u.hasWeakGradient

private def toRepoH10 {d : ℕ} {U : Set (Vec d)} (u : WeakH10 U) :
    _root_.Homogenization.H10Function U where
  toH1Function := toRepoH1 u.toWeakH1
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_hasCompactSupport := u.approx_compactSupport
  approx_support_subset := u.approx_supportedIn
  tendsto_approx := u.tendsto_approx
  tendsto_approx_grad := u.tendsto_approx_grad

private def ofRepoH10 {d : ℕ} {U : Set (Vec d)}
    (u : _root_.Homogenization.H10Function U) : WeakH10 U where
  toWeakH1 := ofRepoH1 u.toH1Function
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_compactSupport := u.approx_hasCompactSupport
  approx_supportedIn := u.approx_support_subset
  tendsto_approx := u.tendsto_approx
  tendsto_approx_grad := u.tendsto_approx_grad

/-! ## Obligation F: the witness-free comparison pair -/

private def toRepoComparisonPair {d : ℕ} [NeZero d]
    {sigmaBar : ℝ} (hsigma : 0 < sigmaBar) {a : CoefficientField d}
    (haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (toRepoField a))
    {m : ℕ} {g : Vec d → Vec d}
    (pair : ComparisonPair sigmaBar a (originCube d m) g) :
    _root_.Homogenization.Book.Ch05.Section57.assemblyComparisonDatumOfScalar
      sigmaBar hsigma (toRepoField a) haRepo m g where
  u := toRepoH1 pair.u
  v := toRepoH1 pair.v
  uWeakSolution := fun φ => pair.u_solves (ofRepoH10 φ)
  vWeakSolution := fun φ => pair.v_solves (ofRepoH10 φ)
  zeroTraceDifference := by
    obtain ⟨w, hw⟩ := pair.sameBoundaryData
    exact ⟨toRepoH10 w, hw⟩

private theorem energyNorm_toRepo {d : ℕ} [NeZero d]
    {a : CoefficientField d}
    (haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
      (toRepoField a))
    {m : ℕ} (u : WeakH1 ((originCube d m).interior)) :
    _root_.Homogenization.Book.Ch03.h1EnergyNormOnCube
        (_root_.Homogenization.Book.MainResults.originCube d m)
        (_root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily
          (toRepoField a) haRepo)
        (toRepoH1 u) =
      energyNorm (originCube d m) a.toFun u := rfl

/-! ### Integrability of the two comparison fields

The dual comparison is used only on L² fields. Weak H¹ membership and the
existing ellipticity bounds supply this regularity, including the transfer
across the cube's null boundary. -/

open Book.Ch03 in
private theorem comparisonFields_memL2 {d : ℕ} [NeZero d]
    (Q : _root_.Homogenization.TriadicCube d) (a : CoeffFamily d)
    (a0 : ConstantCoeffMatrix d)
    (u v : H1Function (Book.Ch02.cubeDomain Q : Set (Vec d))) :
    MemVectorL2 (cubeSet Q) (homogenizationComparisonConstantGradientField a0 u v) ∧
      MemVectorL2 (cubeSet Q) (homogenizationComparisonFluxField Q a a0 u v) := by
  have huGrad : MemVectorL2 (cubeSet Q) u.grad := by
    simpa using (publicH1ToCubeSet u).grad_memVectorL2
  have hvGrad : MemVectorL2 (cubeSet Q) v.grad := by
    simpa using (publicH1ToCubeSet v).grad_memVectorL2
  have hEll0 : IsEllipticFieldOn a0.lam a0.Lam (cubeSet Q)
      (constantCoeffField a0.matrix) :=
    constantCoeffMatrix_isEllipticFieldOn_constantCoeffField a0 (measurableSet_cubeSet Q)
  constructor
  · simpa [homogenizationComparisonConstantGradientField, constantCoeffField] using!
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll0 (huGrad.sub hvGrad)
  · have hfluxA : MemVectorL2 (cubeSet Q)
        (fun x => _root_.Homogenization.matVecMul (publicCoeffField Q a x) (u.grad x)) :=
      memVectorL2_matVecMul_of_isEllipticFieldOn
        (publicCoeffField_isEllipticFieldOn_cubeSet Q a) huGrad
    have hflux0 : MemVectorL2 (cubeSet Q)
        (fun x => _root_.Homogenization.matVecMul a0.matrix (v.grad x)) := by
      simpa [constantCoeffField] using
        memVectorL2_matVecMul_of_isEllipticFieldOn hEll0 hvGrad
    exact MeasureTheory.MemLp.ae_eq
      (homogenizationComparisonFluxField_ae_eq_fluxComparison_publicCoeffField_cubeSet
        (Q := Q) (a := a) (a0 := a0) u v).symm (hfluxA.sub hflux0)

private theorem classicalKernel_toRepo {d : ℕ} (φ : Vec d → ℝ) :
    ClassicalSobolev34.kernel φ = Sobolev34.classicalKernel φ := by
  funext z
  simp only [ClassicalSobolev34.kernel, Sobolev34.classicalKernel,
    Sobolev34.euclideanDistance, euclideanDist, euclideanNorm, _root_.Homogenization.vecNormSq,
    _root_.Homogenization.vecDot, Pi.sub_apply, pow_two, comparisonS]

private theorem classicalNegativeNorm_toRepo {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ) :
    ClassicalSobolev34.negativeNorm (toRepoCube Q) f = Sobolev34.negativeNorm Q f := by
  simp only [ClassicalSobolev34.negativeNorm, ClassicalSobolev34.valueSet,
    ClassicalSobolev34.isDualTest, ClassicalSobolev34.memH34,
    ClassicalSobolev34.testNorm, ClassicalSobolev34.seminorm,
    classicalKernel_toRepo, Sobolev34.negativeNorm, Sobolev34.IsDualTest,
    Sobolev34.MemClassicalH34, Sobolev34.classicalTestNorm, Sobolev34.classicalSeminorm]
  rfl

private theorem scaledNegativeVectorNorm_le_toRepo {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (F : Vec d → Vec d) (hd : 2 ≤ d)
    (hF : MemVectorL2 (cubeSet (toRepoCube Q)) F) :
    Sobolev34.scaledNegativeVectorNorm Q F ≤
      ClassicalSobolev34.comparisonConstant d *
        Book.Ch03.Legacy.scaleNormalizedNegativeSobolevVectorNormTwo
          (toRepoCube Q) comparisonS F := by
  have hi (i : Fin d) : Sobolev34.negativeNorm Q (fun x => F x i) ≤
      ClassicalSobolev34.comparisonConstant d *
        cubeBesovDualFullNorm (toRepoCube Q) comparisonS 2 2 (fun x => F x i) := by
    rw [← classicalNegativeNorm_toRepo]
    apply ClassicalSobolev34.negativeNorm_le_mul_dualFullNorm _ _ hd
    exact (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp'
      (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet (toRepoCube Q) hF)
  unfold Sobolev34.scaledNegativeVectorNorm Sobolev34.negativeScaleFactor
    Book.Ch03.Legacy.scaleNormalizedNegativeSobolevVectorNormTwo
    Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
  calc
    _ ≤ Real.rpow 3 (-comparisonS * (Q.scale : ℝ)) *
        ∑ i, ClassicalSobolev34.comparisonConstant d *
          cubeBesovDualFullNorm (toRepoCube Q) comparisonS 2 2 (fun x => F x i) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hi i)
        (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by
      rw [← Finset.mul_sum]
      change _ = ClassicalSobolev34.comparisonConstant d *
        (Real.rpow 3 (-comparisonS * (Q.scale : ℝ)) * _)
      ring

/-! ## The audited theorem -/

/-- Fixed-exponent quenched homogenization comparison in the uniformly elliptic
case.  The constants are chosen before the law, hence depend only on `d`. -/
theorem homogenizationComparison_uniformEllipticity
    {d : ℕ} [NeZero d] :
    ∃ C alpha Cscale : ℝ,
      0 < C ∧ 0 < alpha ∧ 0 < Cscale ∧
      ∀ S : Setup d,
        ∃ sigmaBar : ℝ,
          0 < sigmaBar ∧
          ∃ X : CoefficientField d → ℝ,
            S.IsMinimalScale X Cscale ∧
            ∀ᵐ a ∂S.P,
              ∀ {m : ℕ} {g : Vec d → Vec d}
                (pair : ComparisonPair sigmaBar a (originCube d m) g),
                X a ≤ (3 : ℝ) ^ m →
                ForceInH34 (originCube d m) g →
                comparisonDefect pair ≤
                  C * ((3 : ℝ) ^ m / X a) ^ (-alpha) * comparisonData pair := by
  obtain ⟨C, alpha, Cscale, hC, halpha, hCscale, hmain⟩ :=
    _root_.Homogenization.Book.MainResults.homogenizationComparison_uniformEllipticity
      (d := d)
  refine ⟨ClassicalSobolev34.comparisonConstant d * C, alpha, Cscale,
    mul_pos ClassicalSobolev34.comparisonConstant_pos hC, halpha, hCscale, ?_⟩
  intro S
  let Srepo : _root_.Homogenization.Book.MainResults.Setup d := toRepoSetup S
  let sigmaBar : ℝ :=
    _root_.Homogenization.Book.Ch05.Section57.barSigmaLimit Srepo.hP Srepo.hStruct
  have hsigma : 0 < sigmaBar := Srepo.barSigmaLimit_pos
  obtain ⟨_sigmaBar, _hsigma, X, hX, hmainS⟩ := hmain Srepo
  refine ⟨sigmaBar, hsigma, fun a => X (toRepoField a), ?_, ?_⟩
  · refine ⟨fun a => hX.1 (toRepoField a), ?_⟩
    intro t ht
    have hrepo := hX.2 ht
    have hPeq : Srepo.P = Measure.map (toRepoField (d := d)) S.P := rfl
    rw [hPeq, map_toRepoField_real_eq] at hrepo
    exact hrepo
  · have hmainAud := (ae_map_toRepoField_iff (μ := S.P)).1 hmainS
    filter_upwards [hmainAud, S.uniformlyElliptic] with a hmain_a hell_a
    intro m g pair hXm hg
    have haRepo :
        _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
          (toRepoField a) :=
      aeLocallyUniformlyElliptic_of_uniformlyEllipticRealization
        S.lam_pos S.lam_le_Lam hell_a
    have hgRepo :
        _root_.Homogenization.Book.Ch03.Legacy.ForceSobolevRegularity
          (_root_.Homogenization.Book.MainResults.originCube d m)
          _root_.Homogenization.Book.MainResults.fixedComparisonS g :=
      forceInH34_toRepo (originCube d m) g hg
    have hstep := hmain_a haRepo (toRepoComparisonPair hsigma haRepo pair) hXm hgRepo
    let pairRepo := toRepoComparisonPair hsigma haRepo pair
    have hfields := comparisonFields_memL2
      (_root_.Homogenization.Book.MainResults.originCube d m)
      (Book.Ch05.Section57.assemblyCoeffFamily (toRepoField a) haRepo)
      (Book.Ch05.Section57.scalarConstantCoeffMatrix sigmaBar hsigma)
      pairRepo.u pairRepo.v
    have hdefect : comparisonDefect pair ≤
        ClassicalSobolev34.comparisonConstant d *
          Srepo.comparisonDefect Book.MainResults.fixedComparisonS pairRepo := by
      have hgrad := scaledNegativeVectorNorm_le_toRepo (originCube d m)
        (constantGradientMismatch sigmaBar pair.u pair.v) S.two_le_dim hfields.1
      have hflux := scaledNegativeVectorNorm_le_toRepo (originCube d m)
        (fluxMismatch a.toFun sigmaBar pair.u pair.v) S.two_le_dim hfields.2
      exact (add_le_add hgrad hflux).trans_eq (mul_add _ _ _).symm
    have hdata :
        Srepo.comparisonData
            _root_.Homogenization.Book.MainResults.fixedComparisonS
            (toRepoComparisonPair hsigma haRepo pair) =
          comparisonData pair := by
      rw [_root_.Homogenization.Book.MainResults.Setup.comparisonData,
        scaledForceH34Seminorm_toRepo_origin]
      rfl
    rw [hdata] at hstep
    calc
      comparisonDefect pair ≤ _ := hdefect
      _ ≤ ClassicalSobolev34.comparisonConstant d *
          (C * ((3 : ℝ) ^ m / X (toRepoField a)) ^ (-alpha) * comparisonData pair) :=
        mul_le_mul_of_nonneg_left hstep ClassicalSobolev34.comparisonConstant_pos.le
      _ = _ := by ring

end

end StatementAudit
end Homogenization
