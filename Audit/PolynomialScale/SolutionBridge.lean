import Mathlib
import Homogenization.HighContrast.Scale.Final
import Audit.PolynomialScale.SolutionBasic

attribute [-instance] Homogenization.instMeasurableSpaceVec
attribute [-instance] Homogenization.instMeasurableSpaceMat
attribute [-instance] Homogenization.instMeasurableSpaceCoeffField

/-!
# Repository bridges for the polynomial homogenization-scale audit

This file carries the **solution-side bridge layer** from the Mathlib-only
statement vocabulary of `Audit/PolynomialScale/SolutionBasic.lean` to the
repository development.  Nothing here is part of the audited statement.

The vocabulary itself deliberately lives in a separate, repository-free
module: the comparator compares the entire dependency closure of the audited
theorem constant by constant against the Mathlib-only challenge, so the
vocabulary must elaborate in exactly the challenge's environment.  This file
is where the repository enters.

It contains:

* the identification of the honest-fields carrier `CoefficientField d` with
  the repository carrier `Homogenization.RegCoeffField d`, as a measurable
  equivalence (`regEquiv`);
* measurability of the four carrier endomorphisms — translation, signed
  permutation rotation, adjoint and restriction — for the carrier σ-algebra
  `MeasurableSpace.comap CoefficientField.toFun (observableFieldSigma d)`;
* the raw-law/carrier-law transport (`map_eq_iff_lawInvariantUnder`,
  `map_repo_transport`), turning the challenge's observable-distribution
  invariance `LawInvariantUnder P T` into the repository's pushforward
  invariance `Measure.map Trepo (Measure.map toRepoReg P) = …`;
* reconstruction of the repository law hypotheses (`RestrictionLawCarrier`,
  `RestrictionStructuralLaw`, `ThetaEllipticLaw`) from a single `Setup d`;
* the `WeakH1`/`WeakH10`, block-state, `Mu`, coarse/annealed and contrast
  bridges, ending in `thetaAtScale_toRepo`.

`Solution.lean` imports this file and states the audited theorem.
-/

namespace Homogenization
namespace StatementAudit

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-! ### Probe classes and signed permutations -/

/-- The challenge probe class is the repository probe class. -/
theorem isProbeR_of_isProbe {d : ℕ} {φ : Vec d → ℝ} (h : IsProbe φ) :
    _root_.Homogenization.IsProbeR (d := d) φ :=
  ⟨h.measurable, h.bounded, h.compactSupport⟩

/-- The repository probe class is the challenge probe class. -/
theorem isProbe_of_isProbeR {d : ℕ} {φ : Vec d → ℝ}
    (h : _root_.Homogenization.IsProbeR (d := d) φ) : IsProbe φ :=
  ⟨h.measurable, h.bounded, h.hasCompactSupport⟩

/-- Obligation C, easy direction: the matrix of a `SignedPermutation` satisfies
the repository's signed-permutation predicate. -/
theorem SignedPermutation.isSignedPermutationMatrix {d : ℕ}
    (R : SignedPermutation d) :
    _root_.Homogenization.IsSignedPermutationMatrix R.matrix :=
  ⟨R.perm, fun j => ((R.axisSign j : ℝ)), fun i => (R.axisSign i).2, fun _ _ => rfl⟩

/-- Obligation C, converse direction: every matrix satisfying the repository's
signed-permutation predicate is the matrix of a `SignedPermutation`. -/
theorem exists_signedPermutation_matrix_eq {d : ℕ} {R : Mat d}
    (hR : _root_.Homogenization.IsSignedPermutationMatrix R) :
    ∃ S : SignedPermutation d, S.matrix = R := by
  obtain ⟨σ, s, hs, hRdef⟩ := hR
  refine ⟨{ perm := σ, axisSign := fun j => ⟨s j, hs j⟩ }, ?_⟩
  funext i j
  rw [hRdef i j]
  rfl

/-! ### The carrier bridge

`CoefficientField d` and `Homogenization.RegCoeffField d` are the same
three-field structure (two field names differ), so the identity on the
underlying raw field is a bijection between them. -/

/-- The audit carrier viewed as the repository carrier. -/
def toRepoReg {d : ℕ} (a : CoefficientField d) :
    _root_.Homogenization.RegCoeffField d where
  toFun := a.toFun
  entry_measurable := a.entry_measurable
  entry_locInt := a.entry_locallyIntegrable

/-- The repository carrier viewed as the audit carrier. -/
def ofRepoReg {d : ℕ} (a : _root_.Homogenization.RegCoeffField d) :
    CoefficientField d where
  toFun := a.toFun
  entry_measurable := a.entry_measurable
  entry_locallyIntegrable := a.entry_locInt

@[simp] theorem toRepoReg_toFun {d : ℕ} (a : CoefficientField d) :
    (toRepoReg a).toFun = a.toFun := rfl

@[simp] theorem ofRepoReg_toFun {d : ℕ}
    (a : _root_.Homogenization.RegCoeffField d) :
    (ofRepoReg a).toFun = a.toFun := rfl

@[simp] theorem toRepoReg_ofRepoReg {d : ℕ}
    (a : _root_.Homogenization.RegCoeffField d) :
    toRepoReg (ofRepoReg a) = a := rfl

@[simp] theorem ofRepoReg_toRepoReg {d : ℕ} (a : CoefficientField d) :
    ofRepoReg (toRepoReg a) = a := rfl

/-! ### The observable σ-algebra and measurability into the carrier

The bare function type `RawCoeffField d` carries no global `MeasurableSpace`
instance — this is deliberate in the challenge, where `rawLawAfter` pins
`observableFieldSigma d` with `letI`.  Inside the section below the same
σ-algebra is installed as a section-local instance so that the transport
lemmas can be written in ordinary `Measurable`/`Measure.map` vocabulary.  No
statement exported from the section mentions the local instance. -/

section LawTransport

/-- The observable σ-algebra on raw fields, as a section-local instance. -/
local instance instRawFieldsObservable (d : ℕ) :
    MeasurableSpace (RawCoeffField d) :=
  observableFieldSigma d

/-- `CoefficientField.toFun` is measurable from the carrier σ-algebra to the
observable σ-algebra: the former is by definition the comap of the latter. -/
theorem measurable_coefficientField_toFun (d : ℕ) :
    Measurable (fun a : CoefficientField d => a.toFun) :=
  Measurable.of_comap_le le_rfl

/-- Point evaluation of a single matrix entry is observable. -/
theorem measurable_rawApplyEntry {d : ℕ} (y : Vec d) (i j : Fin d) :
    Measurable (fun f : RawCoeffField d => f y i j) := by
  have h1 : @Measurable (RawCoeffField d) (Mat d) (pointwiseFieldSigma d)
      (instMeasurableSpaceMat d) (fun f => f y) := measurable_pi_apply y
  have h3 : @Measurable (Mat d) (Fin d → ℝ) (instMeasurableSpaceMat d)
      MeasurableSpace.pi (fun A => A i) := measurable_pi_apply i
  have h2 : @Measurable (Mat d) ℝ (instMeasurableSpaceMat d) _ (fun A => A i j) :=
    (measurable_pi_apply j).comp h3
  exact (h2.comp h1).mono le_sup_left le_rfl

/-- Every probe integral is observable. -/
theorem measurable_rawEntryTest {d : ℕ} (i j : Fin d) {φ : Vec d → ℝ}
    (hφ : IsProbe φ) : Measurable (entryTest i j φ) := by
  have h : @Measurable (RawCoeffField d) ℝ (probeFieldSigma d) _
      (entryTest i j φ) := by
    intro t ht
    exact MeasurableSpace.measurableSet_generateFrom ⟨i, j, φ, hφ, t, ht, rfl⟩
  exact h.mono le_sup_right le_rfl

/-- Measurability into the carrier reduces to measurability of the underlying
raw field for the observable σ-algebra (the carrier σ-algebra is a comap). -/
theorem measurable_into_coefficientField {α : Type*} [MeasurableSpace α] {d : ℕ}
    {F : α → CoefficientField d}
    (h : Measurable (fun a => (F a).toFun)) : Measurable F := by
  rw [measurable_iff_comap_le, instMeasurableSpaceCoefficientField,
    MeasurableSpace.comap_comp]
  exact h.comap_le

/-- The underlying raw field of a repository carrier element is observable. -/
theorem measurable_repoRegToFun {d : ℕ} :
    Measurable (fun a : _root_.Homogenization.RegCoeffField d => a.toFun) := by
  refine _root_.Homogenization.measurable_into_sup ?_ ?_
  · exact Measurable.of_comap_le (_root_.Homogenization.pointwiseSigmaR_le d)
  · refine measurable_generateFrom ?_
    rintro s ⟨i, j, φ, hφ, t, ht, rfl⟩
    exact _root_.Homogenization.measurable_entryTestR i j (isProbeR_of_isProbe hφ) ht

theorem measurable_toRepoReg {d : ℕ} : Measurable (toRepoReg (d := d)) := by
  refine _root_.Homogenization.measurable_into_regCoeffField' ?_ ?_
  · intro y i j
    exact (measurable_rawApplyEntry y i j).comp (measurable_coefficientField_toFun d)
  · intro i j φ hφ
    exact (measurable_rawEntryTest i j (isProbe_of_isProbeR hφ)).comp
      (measurable_coefficientField_toFun d)

theorem measurable_ofRepoReg {d : ℕ} : Measurable (ofRepoReg (d := d)) :=
  measurable_into_coefficientField measurable_repoRegToFun

/-- Pushforward along `toFun` is injective on carrier measures: every
measurable carrier set is a `toFun`-preimage of an observable set. -/
theorem map_toFun_injective {d : ℕ} {mu nu : CoefficientLaw d}
    (h : Measure.map (fun a : CoefficientField d => a.toFun) mu
       = Measure.map (fun a : CoefficientField d => a.toFun) nu) :
    mu = nu := by
  refine Measure.ext fun S hS => ?_
  obtain ⟨S0, hS0, rfl⟩ :
      ∃ S0, MeasurableSet[observableFieldSigma d] S0 ∧
        (fun a : CoefficientField d => a.toFun) ⁻¹' S0 = S := hS
  rw [← Measure.map_apply (measurable_coefficientField_toFun d) hS0,
      ← Measure.map_apply (measurable_coefficientField_toFun d) hS0, h]

/-- **Obligation B.**  Carrier-pushforward invariance and observable-law
invariance are equivalent, for any measurable carrier transformation `Tc`
intertwining with the raw transformation `T`. -/
theorem map_eq_iff_lawInvariantUnder {d : ℕ} (P : CoefficientLaw d)
    (Tc : CoefficientField d → CoefficientField d)
    (T : RawCoeffField d → RawCoeffField d)
    (hcomm : ∀ a, (Tc a).toFun = T a.toFun) (hTc : Measurable Tc) :
    Measure.map Tc P = P ↔ LawInvariantUnder P T := by
  have hkey : rawLawAfter P T
      = Measure.map (fun a : CoefficientField d => a.toFun)
          (Measure.map Tc P) := by
    rw [Measure.map_map (measurable_coefficientField_toFun d) hTc]
    unfold rawLawAfter
    exact congrArg (fun f => Measure.map f P) (funext fun a => (hcomm a).symm)
  unfold LawInvariantUnder
  rw [hkey]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact map_toFun_injective h

end LawTransport

/-- The audit carrier and the repository carrier are measurably equivalent via
the identity on the underlying raw field. -/
def regEquiv (d : ℕ) :
    _root_.Homogenization.RegCoeffField d ≃ᵐ CoefficientField d where
  toEquiv :=
    { toFun := ofRepoReg
      invFun := toRepoReg
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  measurable_toFun := measurable_ofRepoReg
  measurable_invFun := measurable_toRepoReg

theorem ae_map_toRepoReg_iff {d : ℕ} {μ : CoefficientLaw d}
    {p : _root_.Homogenization.RegCoeffField d → Prop} :
    (∀ᵐ b ∂Measure.map (toRepoReg (d := d)) μ, p b) ↔ ∀ᵐ a ∂μ, p (toRepoReg a) := by
  rw [show Measure.map (toRepoReg (d := d)) μ = Measure.map (regEquiv d).symm μ from rfl,
    ← MeasurableEquiv.map_ae]
  exact Filter.eventually_map

/-! ### The four carrier endomorphisms and their measurability

Each raw transformation of the challenge lifts to the carrier; the lift is the
repository endomorphism conjugated by the carrier equivalence, so carrier
preservation and measurability are inherited from the repository layer. -/

/-- Spatial translation, as a carrier endomorphism. -/
def translateCoeff {d : ℕ} (z : Vec d) (a : CoefficientField d) :
    CoefficientField d :=
  ofRepoReg (_root_.Homogenization.translateReg z (toRepoReg a))

/-- Signed-permutation rotation, as a carrier endomorphism. -/
def rotateCoeff {d : ℕ} (R : SignedPermutation d) (a : CoefficientField d) :
    CoefficientField d :=
  ofRepoReg (_root_.Homogenization.rotateReg R.matrix
    R.isSignedPermutationMatrix (toRepoReg a))

/-- The entrywise adjoint, as a carrier endomorphism. -/
def adjointCoeff {d : ℕ} (a : CoefficientField d) : CoefficientField d :=
  ofRepoReg (_root_.Homogenization.adjointReg (toRepoReg a))

/-- Restriction to a measurable set, as a carrier endomorphism. -/
def restrictCoeff {d : ℕ} (U : Set (Vec d)) (hU : MeasurableSet U)
    (a : CoefficientField d) : CoefficientField d :=
  ofRepoReg (_root_.Homogenization.restrictReg U hU (toRepoReg a))

@[simp] theorem translateCoeff_toFun {d : ℕ} (z : Vec d) (a : CoefficientField d) :
    (translateCoeff z a).toFun = translateCoeffField z a.toFun := rfl

@[simp] theorem rotateCoeff_toFun {d : ℕ} (R : SignedPermutation d)
    (a : CoefficientField d) :
    (rotateCoeff R a).toFun = rotateCoeffField R a.toFun := rfl

@[simp] theorem adjointCoeff_toFun {d : ℕ} (a : CoefficientField d) :
    (adjointCoeff a).toFun = adjointCoeffField a.toFun := rfl

@[simp] theorem restrictCoeff_toFun {d : ℕ} (U : Set (Vec d)) (hU : MeasurableSet U)
    (a : CoefficientField d) :
    (restrictCoeff U hU a).toFun = restrictCoeffField U a.toFun := rfl

theorem measurable_translateCoeff {d : ℕ} (z : Vec d) :
    Measurable (translateCoeff (d := d) z) :=
  measurable_ofRepoReg.comp
    ((_root_.Homogenization.measurable_translateReg z).comp measurable_toRepoReg)

theorem measurable_rotateCoeff {d : ℕ} (R : SignedPermutation d) :
    Measurable (rotateCoeff R) :=
  measurable_ofRepoReg.comp
    ((_root_.Homogenization.measurable_rotateReg R.matrix
      R.isSignedPermutationMatrix).comp measurable_toRepoReg)

theorem measurable_adjointCoeff {d : ℕ} :
    Measurable (adjointCoeff (d := d)) :=
  measurable_ofRepoReg.comp
    (_root_.Homogenization.measurable_adjointReg.comp measurable_toRepoReg)

theorem measurable_restrictCoeff {d : ℕ} (U : Set (Vec d)) (hU : MeasurableSet U) :
    Measurable (restrictCoeff U hU) :=
  measurable_ofRepoReg.comp
    ((_root_.Homogenization.measurable_restrictReg U hU).comp measurable_toRepoReg)

/-! ### The restriction σ-algebra -/

/-- **Obligation D.**  The challenge's restriction σ-algebra — the comap of the
observable σ-algebra along `restrictCoeffField U ∘ toFun` — is the comap of the
carrier σ-algebra along the restriction endomorphism. -/
theorem comap_restrictCoeff_eq_restrictionSigma {d : ℕ} (U : Set (Vec d))
    (hU : MeasurableSet U) :
    MeasurableSpace.comap (restrictCoeff U hU)
        (instMeasurableSpaceCoefficientField d)
      = restrictionSigma U := by
  unfold instMeasurableSpaceCoefficientField restrictionSigma
  rw [MeasurableSpace.comap_comp]
  rfl

/-- The restriction endomorphism is measurable from the restriction
σ-algebra. -/
theorem measurable_restrictCoeff_restrictionSigma {d : ℕ} (U : Set (Vec d))
    (hU : MeasurableSet U) :
    @Measurable (CoefficientField d) (CoefficientField d) (restrictionSigma U)
      (instMeasurableSpaceCoefficientField d) (restrictCoeff U hU) :=
  measurable_iff_comap_le.2 (le_of_eq (comap_restrictCoeff_eq_restrictionSigma U hU))

/-! ### Transport of law invariance to the repository carrier -/

/-- The single transport lemma: an observable-law invariance of the challenge
becomes a pushforward invariance of the transported repository law, for any
measurable repository endomorphism intertwining with the raw transformation. -/
theorem map_repo_transport {d : ℕ} {P : CoefficientLaw d}
    (T : RawCoeffField d → RawCoeffField d)
    (Trepo : _root_.Homogenization.RegCoeffField d →
      _root_.Homogenization.RegCoeffField d)
    (hTrepo : Measurable Trepo)
    (hcomm : ∀ a : CoefficientField d, (Trepo (toRepoReg a)).toFun = T a.toFun)
    (hInv : LawInvariantUnder P T) :
    Measure.map Trepo (Measure.map (toRepoReg (d := d)) P)
      = Measure.map (toRepoReg (d := d)) P := by
  have hTc_meas : Measurable (fun a : CoefficientField d =>
      ofRepoReg (Trepo (toRepoReg a))) :=
    measurable_ofRepoReg.comp (hTrepo.comp measurable_toRepoReg)
  have hmapTc : Measure.map (fun a : CoefficientField d =>
      ofRepoReg (Trepo (toRepoReg a))) P = P :=
    (map_eq_iff_lawInvariantUnder P _ T hcomm hTc_meas).2 hInv
  have hcompose : Trepo ∘ (toRepoReg (d := d))
      = (toRepoReg (d := d)) ∘ (fun a : CoefficientField d =>
          ofRepoReg (Trepo (toRepoReg a))) := rfl
  calc Measure.map Trepo (Measure.map (toRepoReg (d := d)) P)
      = Measure.map (Trepo ∘ (toRepoReg (d := d))) P :=
        Measure.map_map hTrepo measurable_toRepoReg
    _ = Measure.map ((toRepoReg (d := d)) ∘ (fun a : CoefficientField d =>
          ofRepoReg (Trepo (toRepoReg a)))) P := by rw [hcompose]
    _ = Measure.map (toRepoReg (d := d)) (Measure.map (fun a : CoefficientField d =>
          ofRepoReg (Trepo (toRepoReg a))) P) :=
        (Measure.map_map measurable_toRepoReg hTc_meas).symm
    _ = Measure.map (toRepoReg (d := d)) P := by rw [hmapTc]

theorem toRepoStationary {d : ℕ} {P : CoefficientLaw d} (h : IntegerStationary P) :
    _root_.Homogenization.IsStationaryR (Measure.map (toRepoReg (d := d)) P) := by
  intro z
  exact map_repo_transport _ _
    (_root_.Homogenization.measurable_translateReg
      (_root_.Homogenization.intVecToRealVec z))
    (fun _ => rfl) (h z)

theorem toRepoIsotropic {d : ℕ} {P : CoefficientLaw d}
    (h : SignedCoordinateInvariant P) :
    _root_.Homogenization.IsIsotropicInLawR (Measure.map (toRepoReg (d := d)) P) := by
  intro R hR
  obtain ⟨S, hS⟩ := exists_signedPermutation_matrix_eq hR
  refine map_repo_transport (rotateCoeffField S)
    (_root_.Homogenization.rotateReg R hR)
    (_root_.Homogenization.measurable_rotateReg R hR) ?_ (h S)
  intro a
  have hrot : rotateCoeffField S a.toFun
      = fun x => (Matrix.transpose R) * (a.toFun (matVecMul R x)) * R := by
    unfold rotateCoeffField
    rw [hS]
  rw [hrot]
  rfl

theorem toRepoAdjoint {d : ℕ} {P : CoefficientLaw d} (h : AdjointInvariant P) :
    _root_.Homogenization.IsAdjointInvariantInLawR
      (Measure.map (toRepoReg (d := d)) P) :=
  map_repo_transport adjointCoeffField _root_.Homogenization.adjointReg
    _root_.Homogenization.measurable_adjointReg (fun _ => rfl) h

theorem toRepoUnitRange {d : ℕ} {P : CoefficientLaw d} (h : UnitRangeDependent P) :
    _root_.Homogenization.IsRestrictionUnitRangeDependentR
      (Measure.map (toRepoReg (d := d)) P) := by
  intro U V hU hV hsep
  have haud := h U V hU hV hsep
  rw [ProbabilityTheory.Indep_iff]
  intro s t hs ht
  have hs_amb : MeasurableSet s :=
    _root_.Homogenization.restrictionSigmaR_le U hU s hs
  have ht_amb : MeasurableSet t :=
    _root_.Homogenization.restrictionSigmaR_le V hV t ht
  have hs_aud : @MeasurableSet (CoefficientField d) (restrictionSigma U)
      (toRepoReg ⁻¹' s) := by
    obtain ⟨s0, hs0, rfl⟩ := hs
    exact measurable_restrictCoeff_restrictionSigma U hU (measurable_toRepoReg hs0)
  have ht_aud : @MeasurableSet (CoefficientField d) (restrictionSigma V)
      (toRepoReg ⁻¹' t) := by
    obtain ⟨t0, ht0, rfl⟩ := ht
    exact measurable_restrictCoeff_restrictionSigma V hV (measurable_toRepoReg ht0)
  have hprod := (ProbabilityTheory.Indep_iff _ _ _).1 haud _ _ hs_aud ht_aud
  rw [Measure.map_apply measurable_toRepoReg (hs_amb.inter ht_amb),
    Measure.map_apply measurable_toRepoReg hs_amb,
    Measure.map_apply measurable_toRepoReg ht_amb]
  simpa [Set.preimage_inter] using hprod

/-! ### Reconstruction of the repository law hypotheses from `Setup` -/

/-- The old surface's `AEStronglyMeasurable` conjunct is free on the honest
carrier. -/
theorem aestronglyMeasurable_repoRestrict_entry {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) (a : CoefficientField d) (i j : Fin d) :
    AEStronglyMeasurable
      (fun x : Vec d => _root_.Homogenization.restrictCoeffField U a.toFun x i j)
      (MeasureTheory.volume.restrict U) := by
  classical
  have hEq : (fun x : Vec d =>
      _root_.Homogenization.restrictCoeffField U a.toFun x i j)
      = Set.indicator U (fun x => a.toFun x i j) := by
    funext x
    by_cases hx : x ∈ U <;>
      simp [_root_.Homogenization.restrictCoeffField, hx, Set.indicator_of_mem,
        Set.indicator_of_notMem]
  rw [hEq]
  exact ((a.entry_measurable i j).indicator hU).stronglyMeasurable.aestronglyMeasurable

theorem isProbabilityMeasure_map_toRepoReg {d : ℕ} (P : CoefficientLaw d)
    [IsProbabilityMeasure P] :
    IsProbabilityMeasure (Measure.map (toRepoReg (d := d)) P) :=
  Measure.isProbabilityMeasure_map measurable_toRepoReg.aemeasurable

/-- **The dropped law-carrier hypothesis, rebuilt from the flat `Setup`.** -/
theorem toRepoLawCarrier {d : ℕ} [NeZero d] (S : Setup d) :
    _root_.Homogenization.Book.Ch04.RestrictionLawCarrier
      (Measure.map (toRepoReg (d := d)) S.P) where
  isProbability := by
    haveI := S.isProbability
    exact isProbabilityMeasure_map_toRepoReg S.P
  ae_locally_uniformly_elliptic := by
    refine (ae_map_toRepoReg_iff (μ := S.P)).2 ?_
    filter_upwards [S.thetaElliptic] with a ha
    intro Q
    refine ⟨1, S.Θ, one_pos, S.one_le_theta,
      _root_.Homogenization.measurableSet_openCubeSet Q,
      fun i j => aestronglyMeasurable_repoRestrict_entry
        (_root_.Homogenization.measurableSet_openCubeSet Q) a i j, ?_⟩
    exact ae_restrict_of_ae ha

theorem toRepoStructuralLaw {d : ℕ} [NeZero d] (S : Setup d) :
    _root_.Homogenization.Book.Ch04.RestrictionStructuralLaw
      (Measure.map (toRepoReg (d := d)) S.P) where
  stationary := toRepoStationary S.integerStationary
  unit_range := toRepoUnitRange S.unitRange
  isotropic := toRepoIsotropic S.signedCoordinateInvariant
  adjoint_invariant := toRepoAdjoint S.adjointInvariant

theorem toRepoThetaEllipticLaw {d : ℕ} [NeZero d] (S : Setup d) :
    _root_.Homogenization.ThetaEllipticLaw S.Θ
      (Measure.map (toRepoReg (d := d)) S.P) := by
  refine (ae_map_toRepoReg_iff (μ := S.P)).2 ?_
  filter_upwards [S.thetaElliptic] with a ha
  exact ha

/-! ### The Sobolev record bridges -/

def toRepoWeakH1 {d : ℕ} {U : Set (Vec d)} (u : WeakH1 U) :
    _root_.Homogenization.H1Function U where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memL2
  gradMemL2 := u.gradMemL2
  hasWeakGradient := u.hasWeakGradient

def ofRepoWeakH1 {d : ℕ} {U : Set (Vec d)} (u : _root_.Homogenization.H1Function U) :
    WeakH1 U where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memL2
  gradMemL2 := u.gradMemL2
  hasWeakGradient := u.hasWeakGradient

def toRepoWeakH10 {d : ℕ} {U : Set (Vec d)} (u : WeakH10 U) :
    _root_.Homogenization.H10Function U where
  toH1Function := toRepoWeakH1 u.toWeakH1
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_hasCompactSupport := u.approx_compactSupport
  approx_support_subset := u.approx_supportedIn
  tendsto_approx := u.tendsto_approx
  tendsto_approx_grad := u.tendsto_approx_grad

def ofRepoWeakH10 {d : ℕ} {U : Set (Vec d)}
    (u : _root_.Homogenization.H10Function U) : WeakH10 U where
  toWeakH1 := ofRepoWeakH1 u.toH1Function
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_compactSupport := u.approx_hasCompactSupport
  approx_supportedIn := u.approx_support_subset
  tendsto_approx := u.tendsto_approx
  tendsto_approx_grad := u.tendsto_approx_grad

namespace PolynomialScale

/-! ### The block formalism, `Mu`, the annealed matrices and the contrast -/

def toRepoBlockState {d : ℕ} (X : BlockState d) :
    _root_.Homogenization.BlockState d where
  potential := X.potential
  flux := X.flux

def ofRepoBlockState {d : ℕ} (X : _root_.Homogenization.BlockState d) :
    BlockState d where
  potential := X.potential
  flux := X.flux

theorem toRepo_isPotentialZeroTraceOn {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → Vec d} (h : IsPotentialZeroTraceOn U f) :
    _root_.Homogenization.IsPotentialZeroTraceOn U f := by
  obtain ⟨u, hu⟩ := h
  exact ⟨toRepoWeakH10 u, hu⟩

theorem ofRepo_isPotentialZeroTraceOn {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → Vec d} (h : _root_.Homogenization.IsPotentialZeroTraceOn U f) :
    IsPotentialZeroTraceOn U f := by
  obtain ⟨u, hu⟩ := h
  exact ⟨ofRepoWeakH10 u, hu⟩

theorem toRepo_isSolenoidalZeroNormalTraceOn {d : ℕ} {U : Set (Vec d)}
    {g : Vec d → Vec d} (h : IsSolenoidalZeroNormalTraceOn U g) :
    _root_.Homogenization.IsSolenoidalZeroNormalTraceOn U g :=
  fun φ => h (ofRepoWeakH1 φ)

theorem ofRepo_isSolenoidalZeroNormalTraceOn {d : ℕ} {U : Set (Vec d)}
    {g : Vec d → Vec d}
    (h : _root_.Homogenization.IsSolenoidalZeroNormalTraceOn U g) :
    IsSolenoidalZeroNormalTraceOn U g :=
  fun φ => h (toRepoWeakH1 φ)

theorem toRepo_isBlockMuAdmissible {d : ℕ} {U : Set (Vec d)}
    {p : BlockVec d} {X : BlockState d} (h : IsBlockMuAdmissible U p X) :
    _root_.Homogenization.IsBlockMuAdmissible U p (toRepoBlockState X) :=
  ⟨h.1, toRepo_isPotentialZeroTraceOn h.2.1, h.2.2.1,
    toRepo_isSolenoidalZeroNormalTraceOn h.2.2.2⟩

theorem ofRepo_isBlockMuAdmissible {d : ℕ} {U : Set (Vec d)}
    {p : BlockVec d} {X : _root_.Homogenization.BlockState d}
    (h : _root_.Homogenization.IsBlockMuAdmissible U p X) :
    IsBlockMuAdmissible U p (ofRepoBlockState X) :=
  ⟨h.1, ofRepo_isPotentialZeroTraceOn h.2.1, h.2.2.1,
    ofRepo_isSolenoidalZeroNormalTraceOn h.2.2.2⟩

theorem muValueSet_toRepo {d : ℕ} (U : Set (Vec d)) (p : BlockVec d)
    (a : RawCoeffField d) :
    muValueSet U p a = _root_.Homogenization.muValueSet U p a := by
  ext m
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact ⟨toRepoBlockState X, toRepo_isBlockMuAdmissible hX, rfl⟩
  · rintro ⟨X, hX, rfl⟩
    exact ⟨ofRepoBlockState X, ofRepo_isBlockMuAdmissible hX, rfl⟩

theorem mu_toRepo {d : ℕ} (U : Set (Vec d)) (p : BlockVec d)
    (a : RawCoeffField d) :
    Mu U p a = _root_.Homogenization.Mu U p a := by
  unfold Mu _root_.Homogenization.Mu
  rw [muValueSet_toRepo]

theorem coarseBlockEntry_toRepo {d : ℕ} (U : Set (Vec d))
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
  · rw [if_pos h, dif_pos h, mu_toRepo]
  · rw [if_neg h, dif_neg h, mu_toRepo, mu_toRepo, mu_toRepo]

theorem coarseBlockMatrix_upperLeft_toRepo {d : ℕ} (U : Set (Vec d))
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

theorem coarseBlockMatrix_upperRight_toRepo {d : ℕ} (U : Set (Vec d))
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

theorem coarseBlockMatrix_lowerLeft_toRepo {d : ℕ} (U : Set (Vec d))
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

theorem coarseBlockMatrix_lowerRight_toRepo {d : ℕ} (U : Set (Vec d))
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

theorem annealedBlockMatrix_upperLeft_toRepo {d : ℕ} (P : CoefficientLaw d)
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

theorem annealedBlockMatrix_upperRight_toRepo {d : ℕ} (P : CoefficientLaw d)
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

theorem annealedBlockMatrix_lowerLeft_toRepo {d : ℕ} (P : CoefficientLaw d)
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

theorem annealedBlockMatrix_lowerRight_toRepo {d : ℕ} (P : CoefficientLaw d)
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

theorem annealedSigmaStarInv_toRepo {d : ℕ} (P : CoefficientLaw d)
    (U : Set (Vec d)) :
    annealedSigmaStarInv P U =
      _root_.Homogenization.Book.Ch04.annealedSigmaStarInv
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedSigmaStarInv
    _root_.Homogenization.Book.Ch04.annealedSigmaStarInv
  exact annealedBlockMatrix_lowerRight_toRepo P U

theorem annealedSigmaStar_toRepo {d : ℕ} (P : CoefficientLaw d)
    (U : Set (Vec d)) :
    annealedSigmaStar P U =
      _root_.Homogenization.Book.Ch04.annealedSigmaStar
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedSigmaStar _root_.Homogenization.Book.Ch04.annealedSigmaStar
  rw [annealedSigmaStarInv_toRepo]

theorem annealedSigmaStarInvKappaMean_toRepo {d : ℕ} (P : CoefficientLaw d)
    (U : Set (Vec d)) :
    annealedSigmaStarInvKappaMean P U =
      _root_.Homogenization.Book.Ch04.annealedSigmaStarInvKappaMean
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedSigmaStarInvKappaMean
    _root_.Homogenization.Book.Ch04.annealedSigmaStarInvKappaMean
  rw [annealedBlockMatrix_lowerLeft_toRepo]

theorem annealedKappa_toRepo {d : ℕ} (P : CoefficientLaw d)
    (U : Set (Vec d)) :
    annealedKappa P U =
      _root_.Homogenization.Book.Ch04.annealedKappa
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedKappa _root_.Homogenization.Book.Ch04.annealedKappa
  rw [annealedSigmaStar_toRepo, annealedSigmaStarInvKappaMean_toRepo]

theorem annealedB_toRepo {d : ℕ} (P : CoefficientLaw d) (U : Set (Vec d)) :
    annealedB P U =
      _root_.Homogenization.Book.Ch04.annealedB
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedB _root_.Homogenization.Book.Ch04.annealedB
  exact annealedBlockMatrix_upperLeft_toRepo P U

theorem annealedSigma_toRepo {d : ℕ} (P : CoefficientLaw d) (U : Set (Vec d)) :
    annealedSigma P U =
      _root_.Homogenization.Book.Ch04.annealedSigma
        (Measure.map (toRepoReg (d := d)) P) U := by
  unfold annealedSigma _root_.Homogenization.Book.Ch04.annealedSigma
  rw [annealedB_toRepo, annealedKappa_toRepo, annealedSigmaStarInv_toRepo]
  rfl

theorem annealedSigmaAtScale_toRepo {d : ℕ} (P : CoefficientLaw d) (n : ℤ) :
    annealedSigmaAtScale P n =
      _root_.Homogenization.Book.Ch04.annealedSigmaAtScale
        (Measure.map (toRepoReg (d := d)) P) n := by
  unfold annealedSigmaAtScale
    _root_.Homogenization.Book.Ch04.annealedSigmaAtScale
  exact annealedSigma_toRepo P _

theorem annealedSigmaStarAtScale_toRepo {d : ℕ} (P : CoefficientLaw d) (n : ℤ) :
    annealedSigmaStarAtScale P n =
      _root_.Homogenization.Book.Ch04.annealedSigmaStarAtScale
        (Measure.map (toRepoReg (d := d)) P) n := by
  unfold annealedSigmaStarAtScale
    _root_.Homogenization.Book.Ch04.annealedSigmaStarAtScale
  exact annealedSigmaStar_toRepo P _

/-- The repository's structural-law contrast selector is the total
`(0,0)`-entry ratio. -/
theorem repo_thetaAtScale_eq_entry_formula {d : ℕ} [NeZero d]
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

theorem thetaAtScale_toRepo {d : ℕ} [NeZero d] (P : CoefficientLaw d)
    (hP : _root_.Homogenization.Book.Ch04.RestrictionLawCarrier
      (Measure.map (toRepoReg (d := d)) P))
    (hStruct : _root_.Homogenization.Book.Ch04.RestrictionStructuralLaw
      (Measure.map (toRepoReg (d := d)) P)) (n : ℤ) :
    _root_.Homogenization.Book.Ch05.thetaAtScale hP hStruct n =
      thetaAtScale P n := by
  rw [repo_thetaAtScale_eq_entry_formula hP hStruct n,
    ← annealedSigmaAtScale_toRepo P n, ← annealedSigmaStarAtScale_toRepo P n]
  rfl

end PolynomialScale

end

end StatementAudit
end Homogenization
