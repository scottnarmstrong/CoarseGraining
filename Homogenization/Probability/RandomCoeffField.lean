import Homogenization.Probability.RandomFieldMeasurability

namespace Homogenization

/-!
Actual random coefficient fields over a sample space.

The probability layer in the rest of the project is law-centric: the main
objects are measures on `CoeffField d`. This file adds the lightweight bundled
object `RandomCoeffField Ω d` so we can also speak cleanly about measurable
sample-space-valued coefficient fields and the local sigma-algebras they induce
on `Ω`.
-/

/-- A coefficient field valued random object on a sample space `Ω`. -/
structure RandomCoeffField (Ω : Type*) [MeasurableSpace Ω] (d : ℕ) where
  /-- The sample-space realization of the coefficient field. -/
  toFun : Ω → CoeffField d
  /-- Measurability into the ambient product sigma-algebra on `CoeffField d`. -/
  measurable_toFun : Measurable toFun

namespace RandomCoeffField

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

instance : CoeFun (RandomCoeffField Ω d) (fun _ => Ω → CoeffField d) := ⟨toFun⟩

theorem measurable (A : RandomCoeffField Ω d) : Measurable A :=
  A.measurable_toFun

@[ext] theorem ext {A B : RandomCoeffField Ω d} (h : ∀ ω, A ω = B ω) : A = B := by
  cases A
  cases B
  simp only [RandomCoeffField.mk.injEq]
  exact funext h

/-- The law of a random coefficient field under a base measure `μ`. -/
noncomputable def law (A : RandomCoeffField Ω d) (μ : MeasureTheory.Measure Ω) :
    MeasureTheory.Measure (CoeffField d) :=
  MeasureTheory.Measure.map A μ

theorem map_law_eq {A : RandomCoeffField Ω d} (μ : MeasureTheory.Measure Ω)
    {β : Type*} [MeasurableSpace β] (f : CoeffField d → β) (hf : Measurable f) :
    MeasureTheory.Measure.map f (A.law μ) =
      MeasureTheory.Measure.map (fun ω => f (A ω)) μ := by
  simpa [RandomCoeffField.law, Function.comp] using
    (MeasureTheory.Measure.map_map hf A.measurable (μ := μ))

/-- Apply a measurable coefficient-field transform pointwise to a random
coefficient field. -/
def map (A : RandomCoeffField Ω d) (f : CoeffField d → CoeffField d)
    (hf : Measurable f) : RandomCoeffField Ω d where
  toFun := fun ω => f (A ω)
  measurable_toFun := hf.comp A.measurable

/-- Integer-translate a random coefficient field. -/
def translateByInt (A : RandomCoeffField Ω d) (z : Fin d → ℤ) : RandomCoeffField Ω d where
  toFun := (A.map (Homogenization.translateByInt z) (measurable_translateByInt z)).toFun
  measurable_toFun :=
    (A.map (Homogenization.translateByInt z) (measurable_translateByInt z)).measurable_toFun

/-- Rotate a random coefficient field by a signed permutation matrix. -/
def rotate (A : RandomCoeffField Ω d) (R : Mat d) : RandomCoeffField Ω d where
  toFun := (A.map (rotateCoeffField R) (measurable_rotateCoeffField R)).toFun
  measurable_toFun := (A.map (rotateCoeffField R) (measurable_rotateCoeffField R)).measurable_toFun

/-- Take the adjoint random coefficient field. -/
def adjoint (A : RandomCoeffField Ω d) : RandomCoeffField Ω d where
  toFun := (A.map adjointCoeffField measurable_adjointCoeffField).toFun
  measurable_toFun := (A.map adjointCoeffField measurable_adjointCoeffField).measurable_toFun

/-- Restrict a random coefficient field to a deterministic domain. -/
noncomputable def restrictSet (A : RandomCoeffField Ω d) (U : Set (Vec d)) :
    RandomCoeffField Ω d :=
  A.map (restrictCoeffField U) (measurable_restrictCoeffField U)

/-- Take the symmetric part of a random coefficient field. -/
noncomputable def symmPart (A : RandomCoeffField Ω d) : RandomCoeffField Ω d :=
  A.map symmCoeffField measurable_symmCoeffField

/-- Take the skew part of a random coefficient field. -/
noncomputable def skewPart (A : RandomCoeffField Ω d) : RandomCoeffField Ω d :=
  A.map skewCoeffField measurable_skewCoeffField

theorem law_map (A : RandomCoeffField Ω d) (μ : MeasureTheory.Measure Ω)
    (f : CoeffField d → CoeffField d) (hf : Measurable f) :
    (A.map f hf).law μ = MeasureTheory.Measure.map f (A.law μ) := by
  simpa [RandomCoeffField.map] using
    (A.map_law_eq μ f hf).symm

theorem law_restrictSet (A : RandomCoeffField Ω d) (μ : MeasureTheory.Measure Ω)
    (U : Set (Vec d)) :
    (A.restrictSet U).law μ = MeasureTheory.Measure.map (restrictCoeffField U) (A.law μ) := by
  simpa [RandomCoeffField.restrictSet] using
    A.law_map μ (restrictCoeffField U) (measurable_restrictCoeffField U)

theorem law_translateByInt (A : RandomCoeffField Ω d) (μ : MeasureTheory.Measure Ω)
    (z : Fin d → ℤ) :
    (A.translateByInt z).law μ = MeasureTheory.Measure.map (Homogenization.translateByInt z) (A.law μ) := by
  simpa [RandomCoeffField.translateByInt] using
    (A.map_law_eq μ (Homogenization.translateByInt z) (measurable_translateByInt z)).symm

theorem law_rotate (A : RandomCoeffField Ω d) (μ : MeasureTheory.Measure Ω) (R : Mat d) :
    (A.rotate R).law μ = MeasureTheory.Measure.map (rotateCoeffField R) (A.law μ) := by
  simpa [RandomCoeffField.rotate] using
    (A.map_law_eq μ (rotateCoeffField R) (measurable_rotateCoeffField R)).symm

theorem law_adjoint (A : RandomCoeffField Ω d) (μ : MeasureTheory.Measure Ω) :
    (A.adjoint).law μ = MeasureTheory.Measure.map adjointCoeffField (A.law μ) := by
  simpa [RandomCoeffField.adjoint] using
    (A.map_law_eq μ adjointCoeffField measurable_adjointCoeffField).symm

theorem law_symmPart (A : RandomCoeffField Ω d) (μ : MeasureTheory.Measure Ω) :
    (A.symmPart).law μ = MeasureTheory.Measure.map symmCoeffField (A.law μ) := by
  simpa [RandomCoeffField.symmPart] using
    A.law_map μ symmCoeffField measurable_symmCoeffField

theorem law_skewPart (A : RandomCoeffField Ω d) (μ : MeasureTheory.Measure Ω) :
    (A.skewPart).law μ = MeasureTheory.Measure.map skewCoeffField (A.law μ) := by
  simpa [RandomCoeffField.skewPart] using
    A.law_map μ skewCoeffField measurable_skewCoeffField

/-- The local sigma-algebra on the sample space induced by a random coefficient
field and the deterministic region `U`. -/
def localSigma (A : RandomCoeffField Ω d) (U : Set (Vec d)) : MeasurableSpace Ω :=
  (LocalSigma U).comap A

/-- The restriction sigma-algebra on the sample space induced by a random
coefficient field and the deterministic region `U`. This is the pullback of
`RestrictionSigma U`, hence the sigma-algebra naturally matched to pointwise
local observables. -/
def restrictionSigma (A : RandomCoeffField Ω d) (U : Set (Vec d)) : MeasurableSpace Ω :=
  (RestrictionSigma U).comap A

theorem measurable_localSigma (A : RandomCoeffField Ω d) (U : Set (Vec d)) :
    @Measurable Ω (CoeffField d) (A.localSigma U) (LocalSigma U) A :=
  comap_measurable A

theorem measurable_restrictionSigma (A : RandomCoeffField Ω d) (U : Set (Vec d)) :
    @Measurable Ω (CoeffField d) (A.restrictionSigma U) (RestrictionSigma U) A :=
  comap_measurable A

theorem measurable_localTestObservable (A : RandomCoeffField Ω d) (U : Set (Vec d))
    (e e' : Vec d) {φ : Vec d → ℝ} (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_support : tsupport φ ⊆ U) :
    @Measurable Ω ℝ (A.localSigma U) (borel ℝ)
      (fun ω => localTestObservable e e' φ (A ω)) := by
  exact
    (measurable_localTestObservable_localSigma (U := U) e e' hφ_cont hφ_compact hφ_support).comp
      (measurable_localSigma (A := A) U)

end RandomCoeffField

end Homogenization
