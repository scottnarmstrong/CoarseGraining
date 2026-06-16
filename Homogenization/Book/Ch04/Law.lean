import Homogenization.Ambient.ScalarMatrix
import Homogenization.Book.Ch02.Definitions
import Homogenization.Probability.LocalEllipticitySlices
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace Homogenization
namespace Book
namespace Ch04

open MeasureTheory

/-!
# Chapter 4 law assumptions

This file owns the stochastic assumptions used by Chapter 4 and later chapters.
There is one public law carrier.  Section-specific measurability tracks should
not be added here.
-/

/-- Combine finitely many almost-everywhere statements into one statement over
all members of a finset. -/
theorem ae_forall_mem_finset {α ι : Type*} [MeasurableSpace α]
    {P : Measure α} (s : Finset ι) {p : ι → α → Prop}
    (h : ∀ i, i ∈ s → ∀ᵐ a ∂P, p i a) :
    ∀ᵐ a ∂P, ∀ i, i ∈ s → p i a := by
  classical
  revert h
  refine Finset.induction_on s ?empty ?insert
  · intro h
    exact Filter.Eventually.of_forall (by simp)
  · intro i s his ih h
    have hi : ∀ᵐ a ∂P, p i a := h i (by simp)
    have hs : ∀ᵐ a ∂P, ∀ j, j ∈ s → p j a := by
      exact ih fun j hj => h j (by simp [hj])
    filter_upwards [hi, hs] with a ha_i ha_s j hj
    simp only [Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · exact ha_i
    · exact ha_s j hj

/-- Nested finite version of `ae_forall_mem_finset`. -/
theorem ae_forall_mem_finset_nested {α ι κ : Type*} [MeasurableSpace α]
    {P : Measure α} (s : Finset ι) (t : ι → Finset κ)
    {p : ι → κ → α → Prop}
    (h : ∀ i, i ∈ s → ∀ j, j ∈ t i → ∀ᵐ a ∂P, p i j a) :
    ∀ᵐ a ∂P, ∀ i, i ∈ s → ∀ j, j ∈ t i → p i j a :=
  ae_forall_mem_finset (P := P) s fun i hi =>
    ae_forall_mem_finset (P := P) (t i) fun j hj =>
      h i hi j hj

/-- A Chapter 4 law on global coefficient fields. -/
abbrev CoeffLaw (d : ℕ) :=
  Measure (CoeffField d)

/-- The local coefficient-field sigma algebra on an observation set. -/
abbrev localSigma {d : ℕ} (U : Set (Vec d)) : MeasurableSpace (CoeffField d) :=
  Homogenization.LocalSigma U

/-- The measurable restriction-local coefficient-field sigma algebra on an
observation set. -/
abbrev restrictionSigma {d : ℕ} (U : Set (Vec d)) : MeasurableSpace (CoeffField d) :=
  Homogenization.RestrictionSigma U

/-- Spatial a.e. ellipticity of a coefficient field on an observation set. -/
def AEEllipticOn {d : ℕ} (lam Lam : ℝ) (U : Set (Vec d))
    (a : CoeffField d) : Prop :=
  IsAEEllipticFieldOn lam Lam U a

/-- Public locally a.e.-uniform ellipticity: every triadic cube has
deterministic spatial a.e. ellipticity constants. -/
def AELocallyUniformlyEllipticField {d : ℕ} (a : CoeffField d) : Prop :=
  ∀ Q : TriadicCube d,
    ∃ lam Lam : ℝ,
      0 < lam ∧ lam ≤ Lam ∧
        AEEllipticOn lam Lam (openCubeSet Q) a

/-- A law is supported on locally a.e.-uniformly elliptic fields. -/
def AELocallyUniformlyEllipticLaw {d : ℕ} (P : CoeffLaw d) : Prop :=
  ∀ᵐ a ∂P, AELocallyUniformlyEllipticField a

/-- A locally a.e.-uniformly elliptic field is a.e.-elliptic on each half-open
cube as well as on its open core. -/
theorem AELocallyUniformlyEllipticField.exists_aeeEllipticOn_cubeSet
    {d : ℕ} {a : CoeffField d}
    (h : AELocallyUniformlyEllipticField a) (Q : TriadicCube d) :
    ∃ lam Lam : ℝ,
      0 < lam ∧ lam ≤ Lam ∧
        AEEllipticOn lam Lam (cubeSet Q) a := by
  rcases h Q with ⟨lam, Lam, hlam, hle, hEll⟩
  exact ⟨lam, Lam, hlam, hle, IsAEEllipticFieldOn.cubeSet_of_openCubeSet hEll⟩

/-- A locally a.e.-uniformly elliptic field lies in some countable AEE
quantitative slice on each half-open triadic cube. -/
theorem AELocallyUniformlyEllipticField.exists_aeeQuantitativeEllipticSlice_cubeSet
    {d : ℕ} {a : CoeffField d}
    (h : AELocallyUniformlyEllipticField a) (Q : TriadicCube d) :
    ∃ k : ℕ, AEEQuantitativeEllipticSlice (cubeSet Q) k a := by
  rcases h.exists_aeeEllipticOn_cubeSet Q with ⟨lam, _Lam, hlam, _hle, hEll⟩
  exact AEEQuantitativeEllipticSlice.exists_of_aeeEllipticOn hlam hEll

/-- A locally a.e.-elliptic law gives an a.s. countable AEE quantitative-slice
cover for each deterministic triadic cube. -/
theorem AELocallyUniformlyEllipticLaw.ae_exists_aeeQuantitativeEllipticSlice_cubeSet
    {d : ℕ} {P : CoeffLaw d}
    (hP : AELocallyUniformlyEllipticLaw P) (Q : TriadicCube d) :
    ∀ᵐ a ∂P, ∃ k : ℕ, AEEQuantitativeEllipticSlice (cubeSet Q) k a := by
  filter_upwards [hP] with a ha
  exact ha.exists_aeeQuantitativeEllipticSlice_cubeSet Q

/-- A law treats local coefficient-field events as null-measurable for
integration against the ambient coefficient-field measure. -/
structure LocalObservableLawCarrier {d : ℕ} (P : CoeffLaw d) : Prop where
  nullMeasurable_localSigma :
    ∀ (U : Set (Vec d)), Bornology.IsBounded U → ∀ (s : Set (CoeffField d)),
      @MeasurableSet (CoeffField d) (localSigma U) s →
        NullMeasurableSet s P

/-- Every ambient coefficient-field law sees bounded local events as
null-measurable, because the ambient coefficient-field sigma algebra contains
every bounded local sigma algebra by construction. -/
theorem localObservableLawCarrier_of_any_law {d : ℕ} (P : CoeffLaw d) :
    LocalObservableLawCarrier P where
  nullMeasurable_localSigma := by
    intro U hU s hs
    exact (localSigma_le_coeffField_of_isBounded hU s hs).nullMeasurableSet

/-- The single public Chapter 4 law carrier. -/
structure LawCarrier {d : ℕ} (P : CoeffLaw d) : Prop where
  isProbability : IsProbabilityMeasure P
  ae_locally_uniformly_elliptic : AELocallyUniformlyEllipticLaw P
  local_observable_measurable : LocalObservableLawCarrier P
  aee_quantitative_slice_measurable :
    ∀ (Q : TriadicCube d) (k : ℕ),
      @MeasurableSet (CoeffField d) (localSigma (cubeSet Q))
        {a : CoeffField d | AEEQuantitativeEllipticSlice (cubeSet Q) k a}

/-- A probability law supported on locally a.e.-uniformly elliptic fields is a
Chapter 4 law carrier.  The local-observable and AEE-slice measurability fields
are now consequences of the coefficient-field measurable-space API. -/
theorem lawCarrier_of_aeLocallyUniformlyElliptic {d : ℕ} {P : CoeffLaw d}
    [IsProbabilityMeasure P] (hP : AELocallyUniformlyEllipticLaw P) :
    LawCarrier P where
  isProbability := inferInstance
  ae_locally_uniformly_elliptic := hP
  local_observable_measurable := localObservableLawCarrier_of_any_law P
  aee_quantitative_slice_measurable := by
    intro Q k
    exact AEEQuantitativeEllipticSlice.measurableSet_localSigma (cubeSet Q) k

namespace LawCarrier

/-- Canonical access to the a.s. locally a.e.-uniform ellipticity support of a
Chapter 4 law carrier. -/
theorem ae_locallyUniformlyEllipticField {d : ℕ} {P : CoeffLaw d}
    (hP : LawCarrier P) :
    ∀ᵐ a ∂P, AELocallyUniformlyEllipticField a :=
  hP.ae_locally_uniformly_elliptic

end LawCarrier

/-- Public stationarity assumption `(P1)`. -/
abbrev StationaryLaw {d : ℕ} (P : CoeffLaw d) : Prop :=
  Homogenization.IsStationary P

/-- Public unit-range dependence assumption `(P2)`. -/
abbrev UnitRangeDependentLaw {d : ℕ} (P : CoeffLaw d) : Prop :=
  Homogenization.IsUnitRangeDependent P

/-- Public isotropy assumption `(P3)`, restricted to signed permutations. -/
abbrev IsotropicLaw {d : ℕ} (P : CoeffLaw d) : Prop :=
  Homogenization.IsIsotropicInLaw P

/-- Public adjoint-invariance assumption. -/
abbrev AdjointInvariantLaw {d : ℕ} (P : CoeffLaw d) : Prop :=
  Homogenization.IsAdjointInvariantInLaw P

/-- The combined structural law assumptions, kept separate from measurability
and ellipticity so downstream theorems request only what they use. -/
structure StructuralLaw {d : ℕ} (P : CoeffLaw d) : Prop where
  stationary : StationaryLaw P
  unit_range : UnitRangeDependentLaw P
  isotropic : IsotropicLaw P
  adjoint_invariant : AdjointInvariantLaw P

end Ch04
end Book
end Homogenization
