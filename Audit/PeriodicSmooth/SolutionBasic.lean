import Mathlib

/-!
# Statement vocabulary for the smooth periodic comparison solution

This file carries the statement-level vocabulary of the comparator challenge
`Audit/PeriodicSmooth/Challenge.lean`, copied verbatim (the block below is a
byte-for-byte copy of the challenge file with only its header docstring and its
final theorem removed).  `Audit/PeriodicSmooth/Solution.lean` imports this file,
adds the solution-only bridges to the repository theorem, and proves the
challenge theorem itself.

The solution must not import the challenge — the two modules declare the same
theorem name — so the vocabulary is re-declared here instead.  Keeping the copy
verbatim is what makes the comparator's statement comparison succeed.

This file imports **only Mathlib**, exactly like the challenge.  That is not a
stylistic choice: the comparator compares the entire dependency closure of the
audited theorem constant by constant, and instance resolution inside the
vocabulary (for instance the `Module ℝ (Fin d → ℝ)` selected under `fderiv` in
`euclideanCoordDeriv`) depends on which instances are in scope.  Importing the
repository here would let repository instances win and make the elaborated
vocabulary constants differ from the challenge's.  The repository import and the
instance erasures it needs live in `Solution.lean` instead, downstream of the
vocabulary.

The main source correspondences on the repository side are:

* ambient fields and ellipticity: `Homogenization/Ambient/CoefficientField.lean`;
* the regular-fields carrier: `Homogenization/Probability/RegCoeffField.lean`
  and `Homogenization/Probability/RegCoeffField/Sigma.lean`;
* cubes and normalized averages: `Homogenization/Geometry/TriadicCube.lean`,
  `Homogenization/Multiscale/NormalizedNorms.lean`;
* positive and negative Sobolev quantities: `Homogenization/Besov/*` and
  `Homogenization/Book/Ch03/Theorems/SobolevPublic.lean`;
* the public theorem surface:
  `Homogenization/Examples/Periodic/PeriodicSmoothComparison.lean`.
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

set_option warn.classDefReducibility false in
/-- The observable σ-algebra on raw fields: point evaluations together with
all compactly supported bounded entry integrals.

The bare function type `RawCoeffField d` deliberately carries no global
`MeasurableSpace` instance: Mathlib's product instance would also apply to it,
and the meaning of the statement must not depend on which instance wins.  The
σ-algebra is used only through the explicit pullback below. -/
def pointwiseFieldSigma (d : ℕ) : MeasurableSpace (RawCoeffField d) := by
  exact @MeasurableSpace.pi (Vec d) (fun _ => Mat d)
    (fun _ => instMeasurableSpaceMat d)

set_option warn.classDefReducibility false in
def probeFieldSigma (d : ℕ) : MeasurableSpace (RawCoeffField d) :=
  MeasurableSpace.generateFrom
    {s | ∃ (i j : Fin d) (φ : Vec d → ℝ), IsProbe φ ∧
      ∃ t : Set ℝ, MeasurableSet t ∧ s = entryTest i j φ ⁻¹' t}

set_option warn.classDefReducibility false in
def observableFieldSigma (d : ℕ) : MeasurableSpace (RawCoeffField d) :=
  pointwiseFieldSigma d ⊔ probeFieldSigma d

instance instMeasurableSpaceCoefficientField (d : ℕ) :
    MeasurableSpace (CoefficientField d) :=
  MeasurableSpace.comap CoefficientField.toFun (observableFieldSigma d)

abbrev CoefficientLaw (d : ℕ) := Measure (CoefficientField d)

/-! ## 3. The explicit periodic medium -/

/-- The scalar multiplier `m(x) = d + 2 + ∑ i, cos (2 π xᵢ)`.  It is `1`-periodic
in every coordinate and satisfies `2 ≤ m ≤ 2 d + 2` everywhere. -/
noncomputable def periodicMultiplier {d : ℕ} (x : Vec d) : ℝ :=
  ((d : ℝ) + 2) + ∑ i : Fin d, Real.cos (2 * Real.pi * x i)

/-- The explicit periodic coefficient field `a(x) = m(x) • I`. -/
noncomputable def periodicRawField {d : ℕ} : RawCoeffField d :=
  fun x => scalarMatrix (periodicMultiplier x)

theorem continuous_periodicMultiplier {d : ℕ} :
    Continuous (periodicMultiplier (d := d)) := by
  unfold periodicMultiplier
  fun_prop

theorem continuous_periodicRawField_entry {d : ℕ} (i j : Fin d) :
    Continuous fun x : Vec d => periodicRawField (d := d) x i j := by
  have h : (fun x : Vec d => periodicRawField (d := d) x i j)
      = fun x : Vec d => periodicMultiplier x * (1 : Mat d) i j := rfl
  rw [h]
  exact continuous_periodicMultiplier.mul continuous_const

/-- The periodic field as an element of the carrier. -/
noncomputable def periodicField (d : ℕ) : CoefficientField d where
  toFun := periodicRawField
  entry_measurable i j := (continuous_periodicRawField_entry i j).measurable
  entry_locallyIntegrable i j :=
    (continuous_periodicRawField_entry i j).locallyIntegrable

/-- The medium is deterministic: its law is the Dirac mass at the periodic
field. -/
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

/-- The `i`-th coordinate of the lower `i`-normal face of `Q`. -/
def lowerFaceCoord {d : ℕ} (Q : TriadicCube d) (i : Fin d) : ℝ :=
  ((Q.index i : ℝ) - (1 / 2 : ℝ)) * Q.side

/-- The `i`-th coordinate of the upper `i`-normal face of `Q`. -/
def upperFaceCoord {d : ℕ} (Q : TriadicCube d) (i : Fin d) : ℝ :=
  ((Q.index i : ℝ) + (1 / 2 : ℝ)) * Q.side

/-- Projection onto the lower `i`-normal face, changing only coordinate `i`. -/
def lowerFaceProjection {d : ℕ} (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    Vec d :=
  Function.update x i (Q.lowerFaceCoord i)

/-- Projection onto the upper `i`-normal face, changing only coordinate `i`. -/
def upperFaceProjection {d : ℕ} (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    Vec d :=
  Function.update x i (Q.upperFaceCoord i)

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

/-! ## 5. Ellipticity of a realization, and the minimal scale -/

/-- On every triadic cube some pair of ellipticity constants works almost
everywhere.  The periodic field itself satisfies this with the fixed constants
`lam = 2` and `Lam = 2 d + 2` used below. -/
def LocallyUniformlyElliptic {d : ℕ} (a : CoefficientField d) : Prop :=
  ∀ Q : TriadicCube d,
    ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
      ∀ᵐ x ∂volumeOn Q.interior, IsEllipticMatrix lam Lam (a x)

/-- Coarse ellipticity size of the periodic medium, at `lam = 2`,
`Lam = 2 d + 2`. -/
noncomputable def coarseUpperBound (d : ℕ) : ℝ :=
  4 * (Fintype.card (Fin d) : ℝ) * (2 : ℝ)⁻¹ * (2 * (d : ℝ) + 2) ^ (2 : ℕ)

noncomputable def coarseInverseLowerBound (d : ℕ) : ℝ :=
  4 * (Fintype.card (Fin d) : ℝ) * (2 : ℝ)⁻¹

/-- The deterministic coarse ellipticity size entering the tail estimate. -/
noncomputable def thetaHat (d : ℕ) : ℝ :=
  1 + coarseInverseLowerBound d * coarseUpperBound d +
    coarseUpperBound d * coarseInverseLowerBound d

noncomputable def minimalScaleTailSize (d : ℕ) (Cscale : ℝ) : ℝ :=
  Real.exp (Cscale * (Real.log (2 + thetaHat d)) ^ (2 : ℕ))

/-- `X` is at least one and has the required `Gamma_d` tail under the law `P`. -/
structure IsMinimalScale {d : ℕ} (P : CoefficientLaw d)
    (X : CoefficientField d → ℝ) (Cscale : ℝ) : Prop where
  one_le : ∀ a, 1 ≤ X a
  tail : ∀ ⦃t : ℝ⦄, 1 ≤ t →
    P.real {a | minimalScaleTailSize d Cscale * t < |X a|} ≤
      (Real.exp (t ^ (d : ℝ)))⁻¹

/-! ## 6. Smooth solutions of the two equations -/

def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)

/-- The classical `i`-th partial derivative. -/
noncomputable def euclideanCoordDeriv {d : ℕ} (i : Fin d)
    (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  (fderiv ℝ f x) (basisVec i)

noncomputable def euclideanGradient {d : ℕ} (f : Vec d → ℝ) : Vec d → Vec d :=
  fun x i => euclideanCoordDeriv i f x

noncomputable def euclideanDivergence {d : ℕ} (F : Vec d → Vec d) : Vec d → ℝ :=
  fun x => ∑ i : Fin d, euclideanCoordDeriv i (fun y => F y i) x

/-- The flux `A ∇u` of `u` in the medium `A`. -/
noncomputable def fluxField {d : ℕ} (A : RawCoeffField d) (u : Vec d → ℝ) :
    Vec d → Vec d :=
  fun x => matVecMul (A x) (euclideanGradient u x)

/-- Classical (pointwise) form of `∇ · (A ∇u) = ∇ · g`. -/
def SolvesEquation {d : ℕ} (A : RawCoeffField d) (u : Vec d → ℝ)
    (g : Vec d → Vec d) : Prop :=
  ∀ x : Vec d, euclideanDivergence (fluxField A u) x = euclideanDivergence g x

/-- The two smooth solutions being compared on `Q`: same force `g`, and the same
values on every face of `Q`.  The smoothness fields are exactly what is needed
to integrate the two equations by parts against `H¹` test functions. -/
structure ComparisonPair {d : ℕ} (sigmaBar : ℝ) (a : CoefficientField d)
    (Q : TriadicCube d) (g : Vec d → Vec d) where
  u : Vec d → ℝ
  v : Vec d → ℝ
  u_smooth : ContDiff ℝ (⊤ : ℕ∞) u
  v_smooth : ContDiff ℝ (⊤ : ℕ∞) v
  force_smooth : ContDiff ℝ 1 g
  flux_smooth : ContDiff ℝ 1 (fluxField a.toFun u)
  homogenizedFlux_smooth :
    ContDiff ℝ 1 (fluxField (fun _ => scalarMatrix (d := d) sigmaBar) v)
  u_solves : SolvesEquation a.toFun u g
  v_solves : SolvesEquation (fun _ => scalarMatrix (d := d) sigmaBar) v g
  agree_on_lowerFaces : ∀ (i : Fin d) (x : Vec d),
    u (Q.lowerFaceProjection i x) - v (Q.lowerFaceProjection i x) = 0
  agree_on_upperFaces : ∀ (i : Fin d) (x : Vec d),
    u (Q.upperFaceProjection i x) - v (Q.upperFaceProjection i x) = 0

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
    (a : RawCoeffField d) (u : Vec d → ℝ) : ℝ :=
  Real.sqrt <| volumeAverage Q.interior fun x =>
    vecDot (euclideanGradient u x)
      (matVecMul (symmPart (a x)) (euclideanGradient u x))

noncomputable def constantGradientMismatch {d : ℕ} (sigmaBar : ℝ)
    (u v : Vec d → ℝ) : Vec d → Vec d :=
  fun x => matVecMul (scalarMatrix (d := d) sigmaBar)
    (euclideanGradient u x - euclideanGradient v x)

noncomputable def fluxMismatch {d : ℕ} (a : RawCoeffField d) (sigmaBar : ℝ)
    (u v : Vec d → ℝ) : Vec d → Vec d :=
  fun x => matVecMul (a x) (euclideanGradient u x) -
    matVecMul (scalarMatrix (d := d) sigmaBar) (euclideanGradient v x)

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
