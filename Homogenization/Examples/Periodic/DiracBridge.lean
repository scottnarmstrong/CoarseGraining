import Homogenization.Book.MainResults
import Homogenization.Deterministic.HomogenizationBlackBoxes.Duality
import Homogenization.Probability.RandomFieldMeasurability

/-!
# Dirac-law bridge for deterministic periodic examples

**Shared foundation.** Builds the periodic stochastic `Setup` from a deterministic
coefficient field (`periodicSetup`), the engine consumed by all three periodic
comparators (`PeriodicGeneralComparison`, `PeriodicConcreteComparison`,
`PeriodicSmoothComparison`).  See `Audit/README.md` for the comparator map.

This file collects the deterministic-to-law bridge lemmas used by periodic
examples.  The pushforward invariance fields of the stochastic setup reduce
directly to pointwise invariance of the deterministic coefficient field.  The
local-observable and AEE-slice measurability fields are supplied by the public
coefficient-field measurable-space API.
-/

namespace Homogenization
namespace Examples
namespace Periodic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The deterministic law concentrated at a coefficient field. -/
abbrev diracCoeffLaw {d : ℕ} (a₀ : CoeffField d) : Book.Ch04.CoeffLaw d :=
  Measure.dirac a₀

/-- Integer-periodicity of a deterministic coefficient field. -/
def IsPeriodicCoeffField {d : ℕ} (a₀ : CoeffField d) : Prop :=
  ∀ z : Fin d → ℤ, translateByInt z a₀ = a₀

/-- Signed-permutation invariance of a deterministic coefficient field. -/
def IsIsotropicCoeffField {d : ℕ} (a₀ : CoeffField d) : Prop :=
  ∀ R : Mat d, IsSignedPermutationMatrix R → rotateCoeffField R a₀ = a₀

/-- Adjoint invariance of a deterministic coefficient field. -/
def IsAdjointInvariantCoeffField {d : ℕ} (a₀ : CoeffField d) : Prop :=
  adjointCoeffField a₀ = a₀

/-- Pointwise periodicity gives stationarity of the Dirac law. -/
theorem dirac_stationary {d : ℕ} {a₀ : CoeffField d}
    (hper : IsPeriodicCoeffField a₀) :
    Book.Ch04.StationaryLaw (diracCoeffLaw a₀) := by
  intro z
  rw [diracCoeffLaw, Measure.map_dirac (measurable_translateByInt z), hper z]

/-- Pointwise signed-permutation invariance gives isotropy of the Dirac law. -/
theorem dirac_isotropic {d : ℕ} {a₀ : CoeffField d}
    (hiso : IsIsotropicCoeffField a₀) :
  Book.Ch04.IsotropicLaw (diracCoeffLaw a₀) := by
  intro R hR
  rw [diracCoeffLaw, Measure.map_dirac (measurable_rotateCoeffField R hR), hiso R hR]

/-- Pointwise adjoint invariance gives adjoint invariance of the Dirac law. -/
theorem dirac_adjointInvariant {d : ℕ} {a₀ : CoeffField d}
    (hadj : IsAdjointInvariantCoeffField a₀) :
    Book.Ch04.AdjointInvariantLaw (diracCoeffLaw a₀) := by
  change Measure.map (adjointCoeffField (d := d)) (Measure.dirac a₀) = Measure.dirac a₀
  rw [Measure.map_dirac (measurable_adjointCoeffField (d := d)), hadj]

/-- On null-measurable sets, the Dirac law has its usual atomic value. -/
theorem dirac_apply_of_nullMeasurable {α : Type*} [MeasurableSpace α]
    {a : α} {s : Set α}
    (hs : NullMeasurableSet s (Measure.dirac a)) :
    Measure.dirac a s = s.indicator 1 a := by
  by_cases ha : a ∈ s
  · rw [Measure.dirac_apply_of_mem ha]
    simp [ha]
  · have hcomp_mem : a ∈ sᶜ := by simpa using ha
    have hcomp : Measure.dirac a sᶜ = 1 := Measure.dirac_apply_of_mem hcomp_mem
    have hsum := measure_add_measure_compl₀ (μ := Measure.dirac a) hs
    have huniv : Measure.dirac a Set.univ = 1 :=
      Measure.dirac_apply_of_mem (Set.mem_univ a)
    rw [hcomp, huniv] at hsum
    have hzero : Measure.dirac a s = (0 : ℝ≥0∞) := by
      calc
        Measure.dirac a s = (1 : ℝ≥0∞) - 1 :=
          ENNReal.eq_sub_of_add_eq ENNReal.one_ne_top hsum
        _ = 0 := by norm_num
    rw [hzero]
    simp [ha]

/--
Once local coefficient-field events are null-measurable under the Dirac law,
unit-range dependence is formal.
-/
theorem dirac_unitRangeDependent_of_localObservable {d : ℕ} {a₀ : CoeffField d}
    (_hlocal : Book.Ch04.LocalObservableLawCarrier (diracCoeffLaw a₀)) :
    Book.Ch04.UnitRangeDependentLaw (diracCoeffLaw a₀) := by
  intro U V _hsep
  rw [ProbabilityTheory.Indep_iff]
  intro s t hs ht
  have hsnm : NullMeasurableSet s (diracCoeffLaw a₀) :=
    (restrictionSigma_le_coeffField U s hs).nullMeasurableSet
  have htnm : NullMeasurableSet t (diracCoeffLaw a₀) :=
    (restrictionSigma_le_coeffField V t ht).nullMeasurableSet
  have hstnm : NullMeasurableSet (s ∩ t) (diracCoeffLaw a₀) :=
    hsnm.inter htnm
  rw [dirac_apply_of_nullMeasurable hstnm,
    dirac_apply_of_nullMeasurable hsnm,
    dirac_apply_of_nullMeasurable htnm]
  by_cases hs0 : a₀ ∈ s <;> by_cases ht0 : a₀ ∈ t <;> simp [hs0, ht0]

/-- Unit-range dependence of a deterministic Dirac law is automatic. -/
theorem dirac_unitRangeDependent {d : ℕ} (a₀ : CoeffField d) :
    Book.Ch04.UnitRangeDependentLaw (diracCoeffLaw a₀) :=
  dirac_unitRangeDependent_of_localObservable
    (Book.Ch04.localObservableLawCarrier_of_any_law (diracCoeffLaw a₀))

/--
Pointwise membership in a null-measurable Dirac support event gives the
corresponding almost-sure statement.
-/
theorem ae_dirac_of_nullMeasurable {α : Type*} [MeasurableSpace α]
    {a : α} {p : α → Prop}
    (hnull : NullMeasurableSet {x | p x} (Measure.dirac a))
    (ha : p a) :
    ∀ᵐ x ∂Measure.dirac a, p x := by
  rw [ae_iff]
  have hcompl : NullMeasurableSet {x | ¬ p x} (Measure.dirac a) := by
    simpa only [Set.compl_setOf] using hnull.compl
  rw [dirac_apply_of_nullMeasurable hcompl]
  simp [ha]

/-- Uniform ellipticity for the deterministic field gives the law-level uniform
ellipticity statement for the Dirac law. -/
theorem dirac_uniformEllipticityBounds {d : ℕ}
    {a₀ : CoeffField d} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hell : ∀ Q : TriadicCube d,
      Book.Ch04.AEEllipticOn lam Lam (openCubeSet Q) a₀) :
    Book.MainResults.UniformEllipticityBounds (diracCoeffLaw a₀) lam Lam where
  lam_pos := hlam
  lam_le_Lam := hle
  aee_elliptic := by
    have hQ :
        ∀ Q : TriadicCube d,
          MeasurableSet
            {a : CoeffField d | Book.Ch04.AEEllipticOn lam Lam (openCubeSet Q) a} := by
      intro Q
      exact localSigma_le_coeffField_of_isBounded (isBounded_openCubeSet Q) _
        (IsAEEllipticFieldOn.measurableSet_localSigma lam Lam (openCubeSet Q))
    have hAll :
        MeasurableSet
          {a : CoeffField d |
            ∀ Q : TriadicCube d,
              Book.Ch04.AEEllipticOn lam Lam (openCubeSet Q) a} := by
      simpa [Set.iInter_setOf] using
        (MeasurableSet.iInter hQ :
          MeasurableSet
            (⋂ Q : TriadicCube d,
              {a : CoeffField d | Book.Ch04.AEEllipticOn lam Lam (openCubeSet Q) a}))
    exact (MeasureTheory.ae_dirac_iff hAll).2 hell

/-- The law-carrier part of the Dirac bridge follows from law-level uniform
ellipticity support. -/
theorem dirac_lawCarrier {d : ℕ} {a₀ : CoeffField d} {lam Lam : ℝ}
    (hUE : Book.MainResults.UniformEllipticityBounds (diracCoeffLaw a₀) lam Lam) :
    Book.Ch04.LawCarrier (diracCoeffLaw a₀) :=
  Book.Ch04.lawCarrier_of_aeLocallyUniformlyElliptic
    hUE.toAELocallyUniformlyEllipticLaw

/--
The structural-law part of the Dirac bridge.  Stationarity, isotropy, and
adjoint invariance reduce to pointwise deterministic invariance, while
unit-range dependence is automatic for a Dirac law.
-/
theorem dirac_structuralLaw {d : ℕ} {a₀ : CoeffField d}
    (hper : IsPeriodicCoeffField a₀)
    (hiso : IsIsotropicCoeffField a₀)
    (hadj : IsAdjointInvariantCoeffField a₀) :
    Book.Ch04.StructuralLaw (diracCoeffLaw a₀) where
  stationary := dirac_stationary hper
  unit_range := dirac_unitRangeDependent a₀
  isotropic := dirac_isotropic hiso
  adjoint_invariant := dirac_adjointInvariant hadj

/-- Assemble a `MainResults.Setup` from a deterministic coefficient field. -/
def dirac_setup {d : ℕ} [NeZero d]
    (two_le_dim : 2 ≤ d) (a₀ : CoeffField d) (lam Lam : ℝ)
    (hper : IsPeriodicCoeffField a₀)
    (hiso : IsIsotropicCoeffField a₀)
    (hadj : IsAdjointInvariantCoeffField a₀)
    (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hell : ∀ Q : TriadicCube d,
      Book.Ch04.AEEllipticOn lam Lam (openCubeSet Q) a₀) :
    Book.MainResults.Setup d where
  two_le_dim := two_le_dim
  P := diracCoeffLaw a₀
  hP := dirac_lawCarrier
    (dirac_uniformEllipticityBounds (a₀ := a₀) hlam hle hell)
  hStruct := dirac_structuralLaw hper hiso hadj
  lam := lam
  Lam := Lam
  hUE := dirac_uniformEllipticityBounds (a₀ := a₀) hlam hle hell

/-- Public periodic deterministic setup constructor. -/
def periodicSetup {d : ℕ} [NeZero d]
    (two_le_dim : 2 ≤ d) (a₀ : CoeffField d) (lam Lam : ℝ)
    (hper : IsPeriodicCoeffField a₀)
    (hiso : IsIsotropicCoeffField a₀)
    (hadj : IsAdjointInvariantCoeffField a₀)
    (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hell : ∀ Q : TriadicCube d,
      Book.Ch04.AEEllipticOn lam Lam (openCubeSet Q) a₀) :
    Book.MainResults.Setup d :=
  dirac_setup two_le_dim a₀ lam Lam hper hiso hadj hlam hle hell

/-! ## A concrete constant scalar periodic witness -/

/-- The constant scalar coefficient field `x ↦ σ I`. -/
abbrev constantScalarCoeffField {d : ℕ} (σ : ℝ) : CoeffField d :=
  constantCoeffField (scalarMatrix (d := d) σ)

/-- Constant scalar fields are integer-periodic. -/
theorem constantScalarCoeffField_periodic {d : ℕ} (σ : ℝ) :
    IsPeriodicCoeffField (constantScalarCoeffField (d := d) σ) := by
  intro z
  ext x i j
  simp [constantScalarCoeffField, constantCoeffField, translateByInt, translateCoeffField]

/-- Rotating a constant scalar field by a signed permutation leaves it unchanged. -/
theorem constantScalarCoeffField_isotropic {d : ℕ} (σ : ℝ) :
    IsIsotropicCoeffField (constantScalarCoeffField (d := d) σ) := by
  intro R hR
  ext x i j
  simp [constantScalarCoeffField, constantCoeffField, rotateCoeffField, scalarMatrix,
    hR.transpose_mul_self]

/-- Constant scalar fields are adjoint-invariant. -/
theorem constantScalarCoeffField_adjointInvariant {d : ℕ} (σ : ℝ) :
    IsAdjointInvariantCoeffField (constantScalarCoeffField (d := d) σ) := by
  ext x i j
  by_cases hij : i = j
  · subst j
    simp [constantScalarCoeffField, constantCoeffField, adjointCoeffField,
      matTranspose, scalarMatrix]
  · have hji : j ≠ i := Ne.symm hij
    simp [constantScalarCoeffField, constantCoeffField, adjointCoeffField,
      matTranspose, scalarMatrix, hij, hji]

/-- A positive constant scalar field is a.e. elliptic on every measurable set. -/
theorem constantScalarCoeffField_aeeEllipticOn {d : ℕ} {U : Set (Vec d)} {σ : ℝ}
    (hU : MeasurableSet U) (hσ : 0 < σ) :
    Book.Ch04.AEEllipticOn σ σ U (constantScalarCoeffField (d := d) σ) := by
  exact IsAEEllipticFieldOn.of_isEllipticFieldOn
    (isEllipticFieldOn_constantCoeffField hU (isEllipticMatrix_scalarMatrix hσ))

/--
Concrete non-vacuity witness for the public main-theorem setup: the Dirac law
concentrated on the constant scalar coefficient field `x ↦ σ I`.
-/
def constantScalarPeriodicSetup {d : ℕ} [NeZero d]
    (two_le_dim : 2 ≤ d) {σ : ℝ} (hσ : 0 < σ) :
    Book.MainResults.Setup d :=
  periodicSetup two_le_dim (constantScalarCoeffField (d := d) σ) σ σ
    (constantScalarCoeffField_periodic σ)
    (constantScalarCoeffField_isotropic σ)
    (constantScalarCoeffField_adjointInvariant σ)
    hσ le_rfl
    (fun Q => constantScalarCoeffField_aeeEllipticOn (measurableSet_openCubeSet Q) hσ)

end

end Periodic
end Examples
end Homogenization
