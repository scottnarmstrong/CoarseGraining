import Mathlib

/-!
# Statement-level audit vocabulary (carrier mirror)

This Mathlib-only file holds the statement vocabulary of the comparator
challenge `Audit/PeriodicConcrete/Challenge.lean`, copied verbatim: the
ambient vectors and matrices, the coefficient carrier and its observable
σ-algebra, the explicit periodic field and its Dirac law, triadic cubes, local
ellipticity and the minimal scale, weak `H¹` solutions, the fixed `H^{3/4}`
quantities, and the comparison defect and data.

Everything below `namespace Homogenization` is byte-identical to the
corresponding block of `Challenge.lean`; only the file header (imports and
this docstring) differs, and the final theorem is omitted.  Because this file
imports **only** Mathlib — exactly like the challenge — every constant of the
vocabulary elaborates against the same instance environment as the challenge
does, so the comparator sees literally the same definitions (this matters in
particular for the `Module ℝ (Vec d)` instance buried inside `fderiv` in
`weakFDeriv`, hence inside the `WeakH1`/`WeakH10` fields).

`Solution.lean` imports this file together with the repository theorem and
adds the private bridges and the audited theorem itself.
-/

namespace Homogenization
namespace StatementAudit

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-! ## 1. Euclidean vectors, matrices, and ellipticity -/

abbrev Vec (d : ℕ) := Fin d → ℝ
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ
abbrev RawCoeffField (d : ℕ) := Vec d → Mat d

instance instMeasurableSpaceMat (d : ℕ) : MeasurableSpace (Mat d) := by
  exact @MeasurableSpace.pi (Fin d) (fun _ => Fin d → ℝ)
    (fun _ => @MeasurableSpace.pi (Fin d) (fun _ => ℝ)
      (fun _ => (RCLike.measurableSpace : MeasurableSpace ℝ)))

def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i

def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x

def matVecMul {d : ℕ} (A : Mat d) (x : Vec d) : Vec d :=
  fun i => ∑ j, A i j * x j

abbrev scalarMatrix {d : ℕ} (sigma : ℝ) : Mat d :=
  sigma • (1 : Mat d)

noncomputable def symmPart {d : ℕ} (A : Mat d) : Mat d :=
  fun i j => (A i j + A j i) / 2

/-- Quadratic-form ellipticity for a possibly non-symmetric matrix. -/
def IsEllipticMatrix {d : ℕ} (lam Lam : ℝ) (A : Mat d) : Prop :=
  0 < lam ∧
    lam ≤ Lam ∧
    (∀ ξ : Vec d, lam * vecNormSq ξ ≤ vecDot ξ (matVecMul A ξ)) ∧
    (∀ ξ : Vec d, Lam⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul A⁻¹ ξ))

/-! ## 2. Coefficient fields and their observable law -/

/-- An honest coefficient field: every matrix entry is Borel measurable and
locally integrable. -/
structure CoefficientField (d : ℕ) where
  toFun : RawCoeffField d
  entry_measurable : ∀ i j : Fin d, Measurable (fun x => toFun x i j)
  entry_locallyIntegrable : ∀ i j : Fin d,
    LocallyIntegrable (fun x => toFun x i j) volume

instance {d : ℕ} : CoeFun (CoefficientField d) (fun _ => RawCoeffField d) :=
  ⟨CoefficientField.toFun⟩

/-- Compactly supported bounded probes used to observe a coefficient field. -/
structure IsProbe {d : ℕ} (φ : Vec d → ℝ) : Prop where
  measurable : Measurable φ
  bounded : ∃ C : ℝ, ∀ x, |φ x| ≤ C
  compactSupport : HasCompactSupport φ

noncomputable def entryTest {d : ℕ} (i j : Fin d) (φ : Vec d → ℝ)
    (a : RawCoeffField d) : ℝ :=
  ∫ x, a x i j * φ x ∂volume

/-- The observable σ-algebra on raw fields: point evaluations together with
all compactly supported bounded entry integrals. -/
def pointwiseFieldSigma (d : ℕ) : MeasurableSpace (RawCoeffField d) := by
  exact @MeasurableSpace.pi (Vec d) (fun _ => Mat d)
    (fun _ => instMeasurableSpaceMat d)

def probeFieldSigma (d : ℕ) : MeasurableSpace (RawCoeffField d) :=
  MeasurableSpace.generateFrom
    {s | ∃ (i j : Fin d) (φ : Vec d → ℝ), IsProbe φ ∧
      ∃ t : Set ℝ, MeasurableSet t ∧ s = entryTest i j φ ⁻¹' t}

def observableFieldSigma (d : ℕ) : MeasurableSpace (RawCoeffField d) :=
  pointwiseFieldSigma d ⊔ probeFieldSigma d

instance instMeasurableSpaceCoefficientField (d : ℕ) :
    MeasurableSpace (CoefficientField d) :=
  MeasurableSpace.comap CoefficientField.toFun (observableFieldSigma d)

abbrev CoefficientLaw (d : ℕ) := Measure (CoefficientField d)

/-! ## 3. The explicit periodic field and its law -/

/-- The scalar multiplier `m(x) = d + 2 + ∑ i, cos (2 π xᵢ)`.  It is invariant
under translation by any integer vector. -/
noncomputable def periodicMultiplier {d : ℕ} (x : Vec d) : ℝ :=
  ((d : ℝ) + 2) + ∑ i : Fin d, Real.cos (2 * Real.pi * x i)

theorem two_le_periodicMultiplier {d : ℕ} (x : Vec d) :
    (2 : ℝ) ≤ periodicMultiplier x := by
  have hsum : -((d : ℝ)) ≤ ∑ i : Fin d, Real.cos (2 * Real.pi * x i) := by
    calc -((d : ℝ)) = ∑ _i : Fin d, (-1 : ℝ) := by simp
      _ ≤ ∑ i : Fin d, Real.cos (2 * Real.pi * x i) :=
          Finset.sum_le_sum fun i _hi => Real.neg_one_le_cos _
  simp only [periodicMultiplier]
  linarith

theorem periodicMultiplier_le {d : ℕ} (x : Vec d) :
    periodicMultiplier x ≤ 2 * (d : ℝ) + 2 := by
  have hsum : (∑ i : Fin d, Real.cos (2 * Real.pi * x i)) ≤ (d : ℝ) := by
    calc (∑ i : Fin d, Real.cos (2 * Real.pi * x i)) ≤ ∑ _i : Fin d, (1 : ℝ) :=
          Finset.sum_le_sum fun i _hi => Real.cos_le_one _
      _ = (d : ℝ) := by simp
  simp only [periodicMultiplier]
  linarith

theorem abs_periodicMultiplier_le {d : ℕ} (x : Vec d) :
    |periodicMultiplier x| ≤ 2 * (d : ℝ) + 2 := by
  have hd : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have hlo := two_le_periodicMultiplier (d := d) x
  have hhi := periodicMultiplier_le (d := d) x
  rw [abs_le]
  constructor <;> linarith

theorem measurable_periodicMultiplier {d : ℕ} :
    Measurable (periodicMultiplier (d := d)) := by
  unfold periodicMultiplier
  fun_prop

/-- The explicit periodic field `a(x) = m(x) • I`, as a raw matrix field. -/
noncomputable def periodicRawField (d : ℕ) : RawCoeffField d :=
  fun x => scalarMatrix (periodicMultiplier x)

/-- A bounded measurable scalar field is locally integrable. -/
theorem locallyIntegrable_of_bounded {d : ℕ} {f : Vec d → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    LocallyIntegrable f volume := by
  rw [MeasureTheory.locallyIntegrable_iff]
  intro k hk
  refine MeasureTheory.Measure.integrableOn_of_bounded (hk.measure_lt_top).ne
    hf.aestronglyMeasurable (M := C) ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using hC x

/-- The explicit periodic field as an element of the coefficient carrier. -/
noncomputable def periodicField (d : ℕ) : CoefficientField d where
  toFun := periodicRawField d
  entry_measurable := fun i j => by
    by_cases hij : i = j
    · subst hij
      simpa [periodicRawField, scalarMatrix] using
        measurable_periodicMultiplier (d := d)
    · simp [periodicRawField, scalarMatrix, hij]
  entry_locallyIntegrable := fun i j => by
    by_cases hij : i = j
    · subst hij
      have hmeas : Measurable fun x : Vec d => periodicRawField d x i i := by
        simpa [periodicRawField, scalarMatrix] using
          measurable_periodicMultiplier (d := d)
      refine locallyIntegrable_of_bounded hmeas (C := 2 * (d : ℝ) + 2) fun x => ?_
      simpa [periodicRawField, scalarMatrix] using
        abs_periodicMultiplier_le (d := d) x
    · have hzero : (fun x : Vec d => periodicRawField d x i j)
          = fun _ : Vec d => (0 : ℝ) := by
        funext x
        simp [periodicRawField, scalarMatrix, hij]
      rw [hzero]
      exact locallyIntegrable_const (0 : ℝ)

/-- The deterministic coefficient law of this challenge: the Dirac point mass
at the explicit periodic field. -/
noncomputable def periodicLaw (d : ℕ) : CoefficientLaw d :=
  Measure.dirac (periodicField d)

/-! ## 4. Triadic cubes and normalized averages -/

noncomputable abbrev volumeOn {d : ℕ} (U : Set (Vec d)) :=
  volume.restrict U

structure TriadicCube (d : ℕ) where
  scale : ℤ
  index : Fin d → ℤ
deriving DecidableEq, Repr

namespace TriadicCube

noncomputable def side {d : ℕ} (Q : TriadicCube d) : ℝ :=
  (3 : ℝ) ^ Q.scale

def set {d : ℕ} (Q : TriadicCube d) : Set (Vec d) :=
  {x | ∀ i,
    (((Q.index i : ℝ) - (1 / 2 : ℝ)) * Q.side ≤ x i) ∧
    (x i < ((Q.index i : ℝ) + (1 / 2 : ℝ)) * Q.side)}

def interior {d : ℕ} (Q : TriadicCube d) : Set (Vec d) :=
  {x | ∀ i,
    (((Q.index i : ℝ) - (1 / 2 : ℝ)) * Q.side < x i) ∧
    (x i < ((Q.index i : ℝ) + (1 / 2 : ℝ)) * Q.side)}

def children {d : ℕ} (Q : TriadicCube d) : Finset (TriadicCube d) :=
  Finset.univ.image fun digits : Fin d → Fin 3 =>
    { scale := Q.scale - 1
      index := fun i => 3 * Q.index i + (digits i : ℤ) - 1 }

def descendants {d : ℕ} (Q : TriadicCube d) : ℕ → Finset (TriadicCube d)
  | 0 => {Q}
  | n + 1 => (Q.descendants n).biUnion children

noncomputable def volume {d : ℕ} (Q : TriadicCube d) : ℝ :=
  Q.side ^ d

noncomputable def measure {d : ℕ} (Q : TriadicCube d) : Measure (Vec d) :=
  MeasureTheory.volume.restrict Q.set

noncomputable def normalizedMeasure {d : ℕ} (Q : TriadicCube d) :
    Measure (Vec d) :=
  ENNReal.ofReal Q.volume⁻¹ • Q.measure

noncomputable def average {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ) : ℝ :=
  Q.volume⁻¹ * ∫ x in Q.set, f x ∂MeasureTheory.volume

noncomputable def fluctuation {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ) : Vec d → ℝ :=
  fun x => f x - Q.average f

noncomputable def l2Norm {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ) : ℝ :=
  (eLpNorm f (2 : ℝ≥0∞) Q.normalizedMeasure).toReal

noncomputable def descendantAverage {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (F : TriadicCube d → ℝ) : ℝ := by
  let D := Q.descendants j
  exact (D.card : ℝ)⁻¹ * D.sum F

end TriadicCube

/-- The triadic cube centered at the origin with sidelength `3^m`. -/
def originCube (d : ℕ) [NeZero d] (m : ℕ) : TriadicCube d :=
  { scale := (m : ℤ)
    index := 0 }

noncomputable def volumeAverage {d : ℕ} (U : Set (Vec d))
    (f : Vec d → ℝ) : ℝ :=
  (MeasureTheory.volume U).toReal⁻¹ * ∫ x in U, f x ∂MeasureTheory.volume

/-! ## 5. Local ellipticity and the minimal scale -/

/-- On every triadic cube the field is elliptic almost everywhere, with a pair
of constants that may depend on the cube. -/
def LocallyUniformlyElliptic {d : ℕ} (a : CoefficientField d) : Prop :=
  ∀ Q : TriadicCube d,
    ∃ lam Lam : ℝ,
      0 < lam ∧ lam ≤ Lam ∧
        ∀ᵐ x ∂volumeOn Q.interior, IsEllipticMatrix lam Lam (a x)

/-- The coarse upper ellipticity ratio at the ellipticity constants of the
explicit field, `lam = 2` and `Lam = 2 d + 2`. -/
noncomputable def coarseUpperBound (d : ℕ) : ℝ :=
  4 * (Fintype.card (Fin d) : ℝ) * (2 : ℝ)⁻¹ * (2 * (d : ℝ) + 2) ^ (2 : ℕ)

/-- The coarse lower ellipticity ratio at `lam = 2`. -/
noncomputable def coarseInverseLowerBound (d : ℕ) : ℝ :=
  4 * (Fintype.card (Fin d) : ℝ) * (2 : ℝ)⁻¹

/-- The deterministic coarse ellipticity size entering the tail estimate. -/
noncomputable def thetaHat (d : ℕ) : ℝ :=
  1 + coarseInverseLowerBound d * coarseUpperBound d +
    coarseUpperBound d * coarseInverseLowerBound d

noncomputable def minimalScaleTailSize (d : ℕ) (Cscale : ℝ) : ℝ :=
  Real.exp (Cscale * (Real.log (2 + thetaHat d)) ^ (2 : ℕ))

/-- `X` is at least one and has the required `Gamma_d` tail under the law. -/
structure IsMinimalScale {d : ℕ} (X : CoefficientField d → ℝ)
    (Cscale : ℝ) : Prop where
  one_le : ∀ a, 1 ≤ X a
  tail : ∀ ⦃t : ℝ⦄, 1 ≤ t →
    (periodicLaw d).real {a | minimalScaleTailSize d Cscale * t < |X a|} ≤
      (Real.exp (t ^ (d : ℝ)))⁻¹

/-! ## 6. Weak `H¹` solutions -/

noncomputable def weakFDeriv {d : ℕ} (φ : Vec d → ℝ) (x : Vec d) :=
  fderiv ℝ φ x

def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)

def HasWeakPartialDerivativeOn {d : ℕ} (U : Set (Vec d)) (i : Fin d)
    (u gi : Vec d → ℝ) : Prop :=
  ∀ φ : Vec d → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    tsupport φ ⊆ U →
    ∫ x in U, u x * (weakFDeriv φ x) (basisVec i) ∂volume =
      -∫ x in U, gi x * φ x ∂volume

def HasWeakGradientOn {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ)
    (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, HasWeakPartialDerivativeOn U i u (fun x => Du x i)

abbrev MemL2On {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  MemLp u 2 (volumeOn U)

def GradientMemL2On {d : ℕ} (U : Set (Vec d))
    (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, MemL2On U (fun x => Du x i)

/-- A function together with a chosen weak gradient. -/
structure WeakH1 {d : ℕ} (U : Set (Vec d)) where
  toFun : Vec d → ℝ
  grad : Vec d → Vec d
  memL2 : MemL2On U toFun
  gradMemL2 : GradientMemL2On U grad
  hasWeakGradient : HasWeakGradientOn U toFun grad

instance {d : ℕ} {U : Set (Vec d)} : CoeFun (WeakH1 U)
    (fun _ => Vec d → ℝ) :=
  ⟨WeakH1.toFun⟩

/-- The closure of smooth compactly supported functions in the `H¹` norm. -/
structure WeakH10 {d : ℕ} (U : Set (Vec d)) extends WeakH1 U where
  approx : ℕ → Vec d → ℝ
  approx_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (approx n)
  approx_compactSupport : ∀ n, HasCompactSupport (approx n)
  approx_supportedIn : ∀ n, tsupport (approx n) ⊆ U
  tendsto_approx :
    Filter.Tendsto
      (fun n => eLpNorm (fun x => approx n x - toWeakH1.toFun x) 2 (volumeOn U))
      Filter.atTop (nhds 0)
  tendsto_approx_grad :
    ∀ i : Fin d,
      Filter.Tendsto
        (fun n => eLpNorm
          (fun x => (weakFDeriv (approx n) x) (basisVec i) - toWeakH1.grad x i)
          2 (volumeOn U))
        Filter.atTop (nhds 0)

/-- Weak formulation of `-div(A grad u) = -div g` on `Q`. -/
def SolvesEquation {d : ℕ} (Q : TriadicCube d) (A : RawCoeffField d)
    (u : WeakH1 Q.interior) (g : Vec d → Vec d) : Prop :=
  ∀ φ : WeakH10 Q.interior,
    ∫ x in Q.interior,
        vecDot (matVecMul (A x) (u.grad x)) (φ.toWeakH1.grad x) ∂volume =
      ∫ x in Q.interior, vecDot (g x) (φ.toWeakH1.grad x) ∂volume

/-- The two weak solutions being compared: same force and same boundary data. -/
structure ComparisonPair {d : ℕ} (sigmaBar : ℝ) (a : CoefficientField d)
    (Q : TriadicCube d) (g : Vec d → Vec d) where
  u : WeakH1 Q.interior
  v : WeakH1 Q.interior
  u_solves : SolvesEquation Q a.toFun u g
  v_solves : SolvesEquation Q (fun _ => scalarMatrix sigmaBar) v g
  sameBoundaryData :
    ∃ w : WeakH10 Q.interior,
      w.toWeakH1.toFun =ᵐ[volumeOn Q.interior] fun x => u.toFun x - v.toFun x

/-! ## 7. The fixed `H^{3/4}` and `H^{-3/4}` quantities -/

noncomputable abbrev comparisonS : ℝ := 3 / 4

namespace Sobolev34

/-! ### The negative norm, represented as the dual of `B^{3/4}_{2,2}` -/

noncomputable def depthAverage {d : ℕ} (Q : TriadicCube d)
    (φ : Vec d → ℝ) (j : ℕ) : ℝ :=
  Q.descendantAverage j fun R => (R.l2Norm (R.fluctuation φ)) ^ (2 : ℝ)

noncomputable def depthSeminorm {d : ℕ} (Q : TriadicCube d)
    (φ : Vec d → ℝ) (j : ℕ) : ℝ :=
  (Q.side / (3 : ℝ) ^ j) ^ (-comparisonS) *
    (depthAverage Q φ j) ^ (1 / (2 : ℝ))

noncomputable def partialTestNorm {d : ℕ} (Q : TriadicCube d)
    (N : ℕ) (φ : Vec d → ℝ) : ℝ :=
  (Finset.sum (Finset.range (N + 1))
      (fun j => (depthSeminorm Q φ j) ^ (2 : ℝ))) ^ (1 / (2 : ℝ)) +
    Q.side ^ (-comparisonS) * ‖Q.average φ‖

def LocallyL2OnDescendants {d : ℕ} (Q : TriadicCube d)
    (φ : Vec d → ℝ) : Prop :=
  ∀ j : ℕ, ∀ R ∈ Q.descendants j,
    MemLp (R.fluctuation φ) (2 : ℝ≥0∞) R.normalizedMeasure

def IsDualTest {d : ℕ} (Q : TriadicCube d) (φ : Vec d → ℝ) : Prop :=
  (∀ N : ℕ, partialTestNorm Q N φ ≤ 1) ∧ LocallyL2OnDescendants Q φ

noncomputable def pairing {d : ℕ} (Q : TriadicCube d)
    (f φ : Vec d → ℝ) : ℝ :=
  Q.average fun x => f x * φ x

noncomputable def negativeNorm {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ) : ℝ :=
  sSup {r | ∃ φ : Vec d → ℝ, IsDualTest Q φ ∧ r = |pairing Q f φ|}

noncomputable def negativeScaleFactor {d : ℕ} (Q : TriadicCube d) : ℝ :=
  Real.rpow 3 (-comparisonS * (Q.scale : ℝ))

noncomputable def scaledNegativeVectorNorm {d : ℕ} (Q : TriadicCube d)
    (F : Vec d → Vec d) : ℝ :=
  negativeScaleFactor Q * ∑ i : Fin d, negativeNorm Q (fun x => F x i)

/-! ### The positive `H^{3/4}` seminorm of the force -/

def kernelExponent (d : ℕ) : ℝ :=
  comparisonS + (d : ℝ) / 2

noncomputable def kernel {d : ℕ} (u : Vec d → ℝ) :
    Vec d × Vec d → ℝ :=
  fun z => dist z.1 z.2 ^ (-kernelExponent d) * (u z.1 - u z.2)

noncomputable def productMeasure {d : ℕ} (Q : TriadicCube d) :
    Measure (Vec d × Vec d) :=
  Q.normalizedMeasure.prod Q.measure

/-- Membership in the fixed fractional Sobolev space on `Q`. -/
def MemH34 {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) : Prop :=
  MemLp u (2 : ℝ≥0∞) Q.normalizedMeasure ∧
    MemLp (kernel u) (2 : ℝ≥0∞) (productMeasure Q)

noncomputable def seminorm {d : ℕ} (Q : TriadicCube d)
    (u : Vec d → ℝ) : ℝ :=
  (eLpNorm (kernel u) (2 : ℝ≥0∞) (productMeasure Q)).toReal

end Sobolev34

/-- Componentwise `H^{3/4}` regularity of the vector force. -/
def ForceInH34 {d : ℕ} (Q : TriadicCube d) (g : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, Sobolev34.MemH34 Q (fun x => g x i)

noncomputable def scaledForceH34Seminorm {d : ℕ} (Q : TriadicCube d)
    (g : Vec d → Vec d) : ℝ :=
  Q.side ^ comparisonS *
    ∑ i : Fin d, Sobolev34.seminorm Q (fun x => g x i)

/-! ## 8. Error, data size, and the theorem -/

noncomputable def energyNorm {d : ℕ} (Q : TriadicCube d)
    (a : RawCoeffField d) (u : WeakH1 Q.interior) : ℝ :=
  Real.sqrt <| volumeAverage Q.interior fun x =>
    vecDot (u.grad x) (matVecMul (symmPart (a x)) (u.grad x))

noncomputable def constantGradientMismatch {d : ℕ} {Q : TriadicCube d}
    (sigmaBar : ℝ) (u v : WeakH1 Q.interior) : Vec d → Vec d :=
  fun x => matVecMul (scalarMatrix (d := d) sigmaBar) (u.grad x - v.grad x)

noncomputable def fluxMismatch {d : ℕ} (a : RawCoeffField d) (sigmaBar : ℝ)
    {Q : TriadicCube d} (u v : WeakH1 Q.interior) : Vec d → Vec d :=
  fun x => matVecMul (a x) (u.grad x) -
    matVecMul (scalarMatrix (d := d) sigmaBar) (v.grad x)

noncomputable def comparisonDefect {d : ℕ} {sigmaBar : ℝ}
    {a : CoefficientField d} {Q : TriadicCube d} {g : Vec d → Vec d}
    (pair : ComparisonPair sigmaBar a Q g) : ℝ :=
  Sobolev34.scaledNegativeVectorNorm Q
      (constantGradientMismatch sigmaBar pair.u pair.v) +
    Sobolev34.scaledNegativeVectorNorm Q
      (fluxMismatch a.toFun sigmaBar pair.u pair.v)

noncomputable def comparisonData {d : ℕ} {sigmaBar : ℝ}
    {a : CoefficientField d} {Q : TriadicCube d} {g : Vec d → Vec d}
    (pair : ComparisonPair sigmaBar a Q g) : ℝ :=
  Real.sqrt sigmaBar * energyNorm Q a.toFun pair.u +
    scaledForceH34Seminorm Q g

end

end StatementAudit
end Homogenization
