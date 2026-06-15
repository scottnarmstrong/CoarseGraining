import Homogenization.Book.Ch04.Observable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Topology.Metrizable.Basic

namespace Homogenization
namespace Book
namespace Ch04

open MeasureTheory

/-!
# Law-relative measurability promotion

This is the canonical Ch4 bridge:

`IsLocalRandomVariable U X → AEMeasurable X P → AEStronglyMeasurable X P`.

Later chapters should not introduce section-local copies of this bridge.
-/

namespace IsLocalRandomVariable

/-- A local random variable is null-measurable under a law that sees local-test
events as null-measurable. -/
theorem nullMeasurable {β : Type*} [MeasurableSpace β] {d : ℕ}
    {P : CoeffLaw d} (hP : LocalObservableLawCarrier P)
    {U : Set (Vec d)} {X : CoeffField d → β}
    (hX : IsLocalRandomVariable U X) :
    NullMeasurable X P := by
  intro s hs
  exact hP.nullMeasurable_localSigma U (X ⁻¹' s) (hX hs)

/-- A local random variable with countably generated target sigma algebra is
a.e. measurable under a law that sees local-test events as null-measurable. -/
theorem aemeasurable {β : Type*} [MeasurableSpace β]
    [MeasurableSpace.CountablyGenerated β] {d : ℕ}
    {P : CoeffLaw d} (hP : LocalObservableLawCarrier P)
    {U : Set (Vec d)} {X : CoeffField d → β}
    (hX : IsLocalRandomVariable U X) :
    AEMeasurable X P :=
  (hX.nullMeasurable hP).aemeasurable

/-- A local random variable into a second-countable pseudometrizable measurable
space is a.e. strongly measurable under a local-observable law carrier. -/
theorem aestronglyMeasurable {β : Type*} [TopologicalSpace β]
    [MeasurableSpace β] [TopologicalSpace.PseudoMetrizableSpace β]
    [OpensMeasurableSpace β] [SecondCountableTopology β]
    [MeasurableSpace.CountablyGenerated β]
    {d : ℕ} {P : CoeffLaw d} (hP : LocalObservableLawCarrier P)
    {U : Set (Vec d)} {X : CoeffField d → β}
    (hX : IsLocalRandomVariable U X) :
    AEStronglyMeasurable X P :=
  (hX.aemeasurable hP).aestronglyMeasurable

end IsLocalRandomVariable

namespace LawCarrier

/-- Dot-notation promotion from local-test measurability to null measurability. -/
theorem nullMeasurable_of_isLocalRandomVariable
    {β : Type*} [MeasurableSpace β] {d : ℕ} {P : CoeffLaw d}
    (hP : LawCarrier P) {U : Set (Vec d)}
    {X : CoeffField d → β} (hX : IsLocalRandomVariable U X) :
    NullMeasurable X P :=
  hX.nullMeasurable hP.local_observable_measurable

/-- Dot-notation promotion from local-test measurability to a.e.
measurability. -/
theorem aemeasurable_of_isLocalRandomVariable
    {β : Type*} [MeasurableSpace β] [MeasurableSpace.CountablyGenerated β]
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    {U : Set (Vec d)} {X : CoeffField d → β}
    (hX : IsLocalRandomVariable U X) :
    AEMeasurable X P :=
  hX.aemeasurable hP.local_observable_measurable

/-- Dot-notation promotion from local-test measurability to a.e. strong
measurability. -/
theorem aestronglyMeasurable_of_isLocalRandomVariable
    {β : Type*} [TopologicalSpace β] [MeasurableSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] [OpensMeasurableSpace β]
    [SecondCountableTopology β] [MeasurableSpace.CountablyGenerated β]
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    {U : Set (Vec d)} {X : CoeffField d → β}
    (hX : IsLocalRandomVariable U X) :
    AEStronglyMeasurable X P :=
  hX.aestronglyMeasurable hP.local_observable_measurable

/-- Bundled-observable promotion to null measurability. -/
theorem nullMeasurable_observable
    {β : Type*} [MeasurableSpace β] {d : ℕ} {P : CoeffLaw d}
    (hP : LawCarrier P) {U : Set (Vec d)} (X : Observable d U β) :
    NullMeasurable X P :=
  hP.nullMeasurable_of_isLocalRandomVariable X.isLocal

/-- Bundled-observable promotion to a.e. measurability. -/
theorem aemeasurable_observable
    {β : Type*} [MeasurableSpace β] [MeasurableSpace.CountablyGenerated β]
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    {U : Set (Vec d)} (X : Observable d U β) :
    AEMeasurable X P :=
  hP.aemeasurable_of_isLocalRandomVariable X.isLocal

/-- Bundled-observable promotion to a.e. strong measurability. -/
theorem aestronglyMeasurable_observable
    {β : Type*} [TopologicalSpace β] [MeasurableSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] [OpensMeasurableSpace β]
    [SecondCountableTopology β] [MeasurableSpace.CountablyGenerated β]
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    {U : Set (Vec d)} (X : Observable d U β) :
    AEStronglyMeasurable X P :=
  hP.aestronglyMeasurable_of_isLocalRandomVariable X.isLocal

/-- Canonical access to AEE quantitative slice local measurability. -/
theorem measurableSet_aeeQuantitativeEllipticSlice_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (k : ℕ) :
    @MeasurableSet (CoeffField d) (localSigma (cubeSet Q))
      {a : CoeffField d | AEEQuantitativeEllipticSlice (cubeSet Q) k a} :=
  hP.aee_quantitative_slice_measurable Q k

/-- A Chapter 4 law carrier gives the a.s. countable AEE quantitative-slice
cover on each deterministic triadic cube. -/
theorem ae_exists_aeeQuantitativeEllipticSlice_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P) (Q : TriadicCube d) :
    ∀ᵐ a ∂P, ∃ k : ℕ, AEEQuantitativeEllipticSlice (cubeSet Q) k a :=
  hP.ae_locally_uniformly_elliptic.ae_exists_aeeQuantitativeEllipticSlice_cubeSet Q

end LawCarrier

end Ch04
end Book
end Homogenization
