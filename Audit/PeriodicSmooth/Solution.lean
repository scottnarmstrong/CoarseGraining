import Mathlib
import Homogenization.Examples.Periodic.PeriodicSmoothComparison

attribute [-instance] Homogenization.instMeasurableSpaceVec
attribute [-instance] Homogenization.instMeasurableSpaceMat
attribute [-instance] Homogenization.instMeasurableSpaceCoeffField

/-!
# Solution: classical (smooth) periodic homogenization comparison

This file is the comparator solution surface for the classical-solution form of
the explicit periodic comparison theorem; the weak `H¹` comparison datum is built
from smooth solutions of the divergence-form equations by integration by parts.

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

/-! ## Ambient fields and matrices -/

abbrev Vec (d : ℕ) := Fin d → ℝ

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

instance instMeasurableSpaceMat (d : ℕ) : MeasurableSpace (Mat d) := by
  exact @MeasurableSpace.pi (Fin d) (fun _ => Fin d → ℝ)
    (fun _ => @MeasurableSpace.pi (Fin d) (fun _ => ℝ)
      (fun _ => (RCLike.measurableSpace : MeasurableSpace ℝ)))

abbrev CoeffField (d : ℕ) := Vec d → Mat d

def LocalAgreementOn {d : ℕ} (U : Set (Vec d)) (a b : CoeffField d) : Prop :=
  ∀ x, x ∈ U → a x = b x

def IsLocalEvent {d : ℕ} (U : Set (Vec d)) (s : Set (CoeffField d)) : Prop :=
  ∀ ⦃a b : CoeffField d⦄, LocalAgreementOn U a b → (a ∈ s ↔ b ∈ s)

def LocalSigma {d : ℕ} (U : Set (Vec d)) : MeasurableSpace (CoeffField d) :=
  MeasurableSpace.generateFrom {s | IsLocalEvent U s}

def pointwiseCoeffFieldMeasurableSpace (d : ℕ) : MeasurableSpace (CoeffField d) := by
  exact @MeasurableSpace.pi (Vec d) (fun _ => Mat d)
    (fun _ => instMeasurableSpaceMat d)

def boundedLocalCoeffFieldMeasurableSpace (d : ℕ) :
    MeasurableSpace (CoeffField d) :=
  ⨆ U : {U : Set (Vec d) // Bornology.IsBounded U}, LocalSigma U.1

instance instMeasurableSpaceCoeffField (d : ℕ) : MeasurableSpace (CoeffField d) :=
  pointwiseCoeffFieldMeasurableSpace d ⊔ boundedLocalCoeffFieldMeasurableSpace d

def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i

def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x

def matVecMul {d : ℕ} (A : Mat d) (x : Vec d) : Vec d :=
  fun i => ∑ j, A i j * x j

abbrev scalarMatrix {d : ℕ} (sigma : ℝ) : Mat d :=
  sigma • (1 : Mat d)

/-- The scalar multiplier `m(x) = d + 2 + sum_i cos (2 pi x_i)`. -/
noncomputable def mField {d : ℕ} (x : Vec d) : ℝ :=
  ((d : ℝ) + 2) + ∑ i : Fin d, Real.cos (2 * Real.pi * x i)

/-- The explicit periodic coefficient field `a(x) = m(x) I`. -/
noncomputable def mFieldCoeff {d : ℕ} : CoeffField d :=
  fun x => scalarMatrix (d := d) (mField x)

noncomputable def symmPart {d : ℕ} (A : Mat d) : Mat d :=
  fun i j => (A i j + A j i) / 2

def IsEllipticMatrix {d : ℕ} (lam Lam : ℝ) (A : Mat d) : Prop :=
  0 < lam ∧
    lam ≤ Lam ∧
    (∀ ξ : Vec d, lam * vecNormSq ξ ≤ vecDot ξ (matVecMul A ξ)) ∧
    (∀ ξ : Vec d, Lam⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul A⁻¹ ξ))

noncomputable def restrictCoeffField {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) : CoeffField d := by
  classical
  exact fun x => if x ∈ U then a x else 0

/-! ## Cubes and normalized cube averages -/

noncomputable abbrev volumeMeasureOn {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.volume.restrict U

structure TriadicCube (d : ℕ) where
  scale : ℤ
  index : Fin d → ℤ
deriving DecidableEq, Repr

noncomputable def cubeScaleFactor {d : ℕ} (Q : TriadicCube d) : ℝ :=
  (3 : ℝ) ^ Q.scale

def cubeSet {d : ℕ} (Q : TriadicCube d) : Set (Vec d) :=
  { x | ∀ i,
      (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q ≤ x i) ∧
      (x i < (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)) }

def openCubeSet {d : ℕ} (Q : TriadicCube d) : Set (Vec d) :=
  { x | ∀ i,
      (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q < x i) ∧
      (x i < (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)) }

/-- Lower coordinate face of a triadic cube. -/
def cubeLowerFaceCoord {d : ℕ} (Q : TriadicCube d) (i : Fin d) : ℝ :=
  (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q)

/-- Upper coordinate face of a triadic cube. -/
def cubeUpperFaceCoord {d : ℕ} (Q : TriadicCube d) (i : Fin d) : ℝ :=
  (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)

/-- Projection onto the lower `i`-normal face, changing only coordinate `i`. -/
def cubeLowerFaceProjection {d : ℕ} (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    Vec d :=
  Function.update x i (cubeLowerFaceCoord Q i)

/-- Projection onto the upper `i`-normal face, changing only coordinate `i`. -/
def cubeUpperFaceProjection {d : ℕ} (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    Vec d :=
  Function.update x i (cubeUpperFaceCoord Q i)

/-- The triadic cube centered at the origin with integer scale `m`. -/
def triadicOriginCube (d : ℕ) (m : ℤ) : TriadicCube d :=
  { scale := m
    index := 0 }

/-- The public theorem uses natural scales, coerced to integer triadic scales. -/
abbrev originCube (d : ℕ) [NeZero d] (m : ℕ) : TriadicCube d :=
  triadicOriginCube d ((m : ℕ) : ℤ)

/-- Fixed public Sobolev exponent used by the comparator-audited theorem. -/
noncomputable abbrev fixedComparisonS : ℝ := 3 / 4

def childCubes {d : ℕ} (Q : TriadicCube d) : Finset (TriadicCube d) :=
  Finset.univ.image fun digits : Fin d → Fin 3 =>
    { scale := Q.scale - 1
      index := fun i => 3 * Q.index i + (digits i : ℤ) - 1 }

def descendantsAtDepth {d : ℕ} (Q : TriadicCube d) : ℕ → Finset (TriadicCube d)
  | 0 => {Q}
  | n + 1 => (descendantsAtDepth Q n).biUnion childCubes

noncomputable def cubeVolume {d : ℕ} (Q : TriadicCube d) : ℝ :=
  (cubeScaleFactor Q) ^ d

noncomputable def cubeMeasure {d : ℕ} (Q : TriadicCube d) :
    Measure (Vec d) :=
  MeasureTheory.volume.restrict (cubeSet Q)

noncomputable def normalizedCubeMeasure {d : ℕ} (Q : TriadicCube d) :
    Measure (Vec d) :=
  ENNReal.ofReal ((cubeVolume Q)⁻¹) • cubeMeasure Q

noncomputable def cubeAverage {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) : ℝ :=
  (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, f x ∂MeasureTheory.volume

noncomputable def volumeAverage {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ) : ℝ :=
  (MeasureTheory.volume U).toReal⁻¹ * ∫ x in U, f x ∂MeasureTheory.volume

noncomputable def cubeLpNorm {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (p : ℝ≥0∞) (f : Vec d → E) : ℝ :=
  (MeasureTheory.eLpNorm f p (normalizedCubeMeasure Q)).toReal

noncomputable def cubeFluctuation {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ) : Vec d → ℝ :=
  fun x => f x - cubeAverage Q f

/-! ## Ellipticity assumptions -/

def IsAEEllipticFieldOn {d : ℕ} (lam Lam : ℝ) (U : Set (Vec d))
    (a : CoeffField d) : Prop :=
  MeasurableSet U ∧
    (∀ i j : Fin d,
      AEStronglyMeasurable
        (fun x : Vec d => restrictCoeffField U a x i j) (volumeMeasureOn U)) ∧
      ∀ᵐ x ∂ volumeMeasureOn U, IsEllipticMatrix lam Lam (a x)

def AELocallyUniformlyEllipticField {d : ℕ} (a : CoeffField d) : Prop :=
  ∀ Q : TriadicCube d,
    ∃ lam Lam : ℝ,
      0 < lam ∧ lam ≤ Lam ∧
        IsAEEllipticFieldOn lam Lam (openCubeSet Q) a

/-! ## Weak-tail notation for the random minimal scale -/

namespace IndependentSums

variable {Omega : Type*} [MeasurableSpace Omega]

def upperTailEvent (X : Omega → ℝ) (a : ℝ) : Set Omega :=
  {omega | a < X omega}

def IsBigOWith (mu : Measure Omega) (Psi : ℝ → ℝ) (X : Omega → ℝ)
    (A : ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, 1 ≤ t → mu.real (upperTailEvent X (A * t)) ≤ (Psi t)⁻¹

def IsBigO (mu : Measure Omega) (Psi : ℝ → ℝ) (X : Omega → ℝ)
    (A : ℝ) : Prop :=
  IsBigOWith mu Psi (fun omega => |X omega|) A

noncomputable def gammaSigma (sigma : ℝ) : ℝ → ℝ :=
  fun t => Real.exp (t ^ sigma)

end IndependentSums

open IndependentSums

/-! ## Sobolev weak solutions -/

noncomputable def vecModule (d : ℕ) : Module ℝ (Vec d) :=
  @Pi.Function.module (Fin d) ℝ ℝ _ _ _

def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)

noncomputable def euclideanCoordDeriv {d : ℕ} (i : Fin d)
    (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  (@fderiv ℝ _ (Vec d) _ (vecModule d) _ ℝ _ _ _ f x) (basisVec i)

noncomputable def euclideanGradient {d : ℕ} (f : Vec d → ℝ) :
    Vec d → Vec d :=
  fun x i => euclideanCoordDeriv i f x

noncomputable def euclideanDivergence {d : ℕ} (F : Vec d → Vec d) : Vec d → ℝ :=
  fun x => ∑ i : Fin d, euclideanCoordDeriv i (fun y => F y i) x

/-! ## Fractional Sobolev and dual negative norms -/

noncomputable def cubeBesovOscillation {d : ℕ} (Q : TriadicCube d)
    (p : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  cubeLpNorm Q p (cubeFluctuation Q u)

noncomputable def cubeBesovScaleWeight {d : ℕ} (s : ℝ) (Q : TriadicCube d) : ℝ :=
  (cubeScaleFactor Q) ^ (-s)

noncomputable def descendantsAverage {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (F : TriadicCube d → ℝ) : ℝ := by
  let D := descendantsAtDepth Q j
  exact ((D.card : ℝ)⁻¹) * D.sum F

noncomputable def cubeBesovDepthAverage {d : ℕ} (Q : TriadicCube d)
    (p : ℝ≥0∞) (u : Vec d → ℝ) (j : ℕ) : ℝ :=
  descendantsAverage Q j fun R => (cubeBesovOscillation R p u) ^ p.toReal

noncomputable def cubeBesovDepthWeight {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (j : ℕ) : ℝ :=
  (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ (-s)

noncomputable def cubeBesovDepthSeminorm {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) (j : ℕ) : ℝ :=
  cubeBesovDepthWeight Q s j * (cubeBesovDepthAverage Q p u j) ^ (1 / p.toReal)

noncomputable def cubeBesovPartialSeminorm {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  (Finset.sum (Finset.range (N + 1))
    (fun j => (cubeBesovDepthSeminorm Q s p u j) ^ q.toReal)) ^ (1 / q.toReal)

noncomputable def cubeBesovPartialSeminormTop {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  (Finset.range (N + 1)).sup' ⟨0, by simp⟩
    (fun j => cubeBesovDepthSeminorm Q s p u j)

noncomputable def cubeBesovPartialNorm {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  cubeBesovPartialSeminorm Q s p q N u + cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖

noncomputable def cubeBesovPartialNormTop {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  cubeBesovPartialSeminormTop Q s p N u + cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖

noncomputable def cubeBesovConjExponent (p : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.conjExponent p

noncomputable def cubeBesovDualTestNorm {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (g : Vec d → ℝ) : ℝ :=
  if cubeBesovConjExponent q = ∞ then
    cubeBesovPartialNormTop Q s (cubeBesovConjExponent p) N g
  else
    cubeBesovPartialNorm Q s (cubeBesovConjExponent p) (cubeBesovConjExponent q) N g

noncomputable def CubeBesovDualLocalMemLpGlobal {d : ℕ} (Q : TriadicCube d)
    (p : ℝ≥0∞) (g : Vec d → ℝ) : Prop :=
  ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
    MemLp (cubeFluctuation R g) (cubeBesovConjExponent p) (normalizedCubeMeasure R)

def CubeBesovDualFullTest {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (g : Vec d → ℝ) : Prop :=
  (∀ N : ℕ, cubeBesovDualTestNorm Q s p q N g ≤ 1) ∧
    CubeBesovDualLocalMemLpGlobal Q p g

noncomputable def cubeBesovPairing {d : ℕ} (Q : TriadicCube d)
    (f g : Vec d → ℝ) : ℝ :=
  cubeAverage Q (fun x => f x * g x)

noncomputable def cubeBesovDualFullNormValueSet {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p q : ℝ≥0∞) (f : Vec d → ℝ) : Set ℝ :=
  {r | ∃ g : Vec d → ℝ, CubeBesovDualFullTest Q s p q g ∧
    r = |cubeBesovPairing Q f g|}

noncomputable def cubeBesovDualFullNorm {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (f : Vec d → ℝ) : ℝ :=
  sSup (cubeBesovDualFullNormValueSet Q s p q f)

noncomputable def scaleNormalizedNegativeSobolevVectorNormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) : ℝ :=
  Real.rpow (3 : ℝ) (-s * (((Q.scale : ℤ) : ℝ))) *
    ∑ i : Fin d,
      cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
        (fun x => F x i)

namespace Gagliardo

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def kernelExponent (d : ℕ) (s : ℝ) (p : ℝ≥0∞) : ℝ :=
  s + (d : ℝ) / p.toReal

noncomputable def gagliardoKernel (s : ℝ) (p : ℝ≥0∞) (u : Vec d → E) :
    Vec d × Vec d → E :=
  fun z => (dist z.1 z.2 ^ (-kernelExponent d s p)) • (u z.1 - u z.2)

noncomputable def gagliardoCubeMeasure (Q : TriadicCube d) :
    Measure (Vec d × Vec d) :=
  (normalizedCubeMeasure Q).prod (cubeMeasure Q)

noncomputable def cubeGagliardoESeminorm (Q : TriadicCube d) (s : ℝ)
    (p : ℝ≥0∞) (u : Vec d → E) : ℝ≥0∞ :=
  eLpNorm (gagliardoKernel s p u) p (gagliardoCubeMeasure Q)

noncomputable def cubeGagliardoSeminorm (Q : TriadicCube d) (s : ℝ)
    (p : ℝ≥0∞) (u : Vec d → E) : ℝ :=
  (cubeGagliardoESeminorm Q s p u).toReal

def MemWsp (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → E) : Prop :=
  MemLp (gagliardoKernel s p u) p (gagliardoCubeMeasure Q)

end Gagliardo

noncomputable abbrev fractionalSobolevSeminorm {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  Gagliardo.cubeGagliardoSeminorm Q s p u

def MemFractionalSobolev {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞)
    (u : Vec d → ℝ) : Prop :=
  MemLp u p (normalizedCubeMeasure Q) ∧ Gagliardo.MemWsp Q s p u

def ForceSobolevRegularity {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (g : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, MemFractionalSobolev Q s (2 : ℝ≥0∞) (fun x => g x i)

noncomputable def scaleNormalizedPositiveSobolevVectorSeminormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (g : Vec d → Vec d) : ℝ :=
  cubeBesovScaleWeight (-s) Q *
    ∑ i : Fin d, fractionalSobolevSeminorm Q s (2 : ℝ≥0∞) (fun x => g x i)

/-! ## Classical comparison estimate quantities -/

noncomputable def classicalComparisonConstantGradientField {d : ℕ}
    (abar : Mat d) (u v : Vec d → ℝ) : Vec d → Vec d :=
  fun x => matVecMul abar (euclideanGradient u x - euclideanGradient v x)

noncomputable def classicalComparisonFluxField {d : ℕ}
    (a : CoeffField d) (abar : Mat d) (u v : Vec d → ℝ) : Vec d → Vec d :=
  fun x => matVecMul (a x) (euclideanGradient u x) -
    matVecMul abar (euclideanGradient v x)

noncomputable def classicalComparisonDefect {d : ℕ} [NeZero d]
    (abar : Mat d) (s : ℝ) (a : CoeffField d) (m : ℕ)
    (u v : Vec d → ℝ) : ℝ :=
  scaleNormalizedNegativeSobolevVectorNormTwo (originCube d m) s
      (classicalComparisonConstantGradientField abar u v) +
    scaleNormalizedNegativeSobolevVectorNormTwo (originCube d m) s
      (classicalComparisonFluxField a abar u v)

noncomputable def classicalH1EnergyNormOnCube {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (u : Vec d → ℝ) : ℝ :=
  Real.sqrt <|
    volumeAverage (openCubeSet Q) fun x =>
      vecDot (euclideanGradient u x)
        (matVecMul (symmPart (a x)) (euclideanGradient u x))

noncomputable def classicalComparisonData {d : ℕ} [NeZero d]
    (sigmaBar : ℝ) (s : ℝ) (a : CoeffField d) (m : ℕ)
    (g : Vec d → Vec d) (u : Vec d → ℝ) : ℝ :=
  Real.sqrt sigmaBar *
      classicalH1EnergyNormOnCube (originCube d m) a u +
    scaleNormalizedPositiveSobolevVectorSeminormTwo (originCube d m) s g

/-- The deterministic endpoint size used by the periodic Dirac specialization. -/
noncomputable def periodicThetaHat (d : ℕ) (lam Lam : ℝ) : ℝ :=
  let upper := 4 * (Fintype.card (Fin d) : ℝ) * lam⁻¹ * Lam ^ (2 : ℕ)
  let lower := 4 * (Fintype.card (Fin d) : ℝ) * lam⁻¹
  1 + lower * upper + upper * lower

def IsPeriodicMinimalScale {d : ℕ} (a₀ : CoeffField d) (lam Lam : ℝ)
    (X : CoeffField d → ℝ) (Cscale : ℝ) : Prop :=
  (∀ a, 1 ≤ X a) ∧
    IsBigO (Measure.dirac a₀) (gammaSigma ((d : ℕ) : ℝ)) X
      (Real.exp (Cscale * (Real.log (2 + periodicThetaHat d lam Lam)) ^ (2 : ℕ)))

/-! ## Solution-only bridges to the repository theorem -/

private def toRepoTriadicCube {d : ℕ} (Q : TriadicCube d) :
    _root_.Homogenization.TriadicCube d :=
  { scale := Q.scale
    index := Q.index }

private def ofRepoTriadicCube {d : ℕ}
    (Q : _root_.Homogenization.TriadicCube d) : TriadicCube d :=
  { scale := Q.scale
    index := Q.index }

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

private theorem cubeBesovDualFullNorm_originCube_toRepo {d : ℕ} [NeZero d]
    (m : ℕ) (s : ℝ) (p q : ℝ≥0∞) (f : Vec d → ℝ) :
    _root_.Homogenization.cubeBesovDualFullNorm
        (_root_.Homogenization.Book.MainResults.originCube d m) s p q f =
      cubeBesovDualFullNorm (originCube d m) s p q f := by
  simpa [toRepo_originCube] using
    cubeBesovDualFullNorm_toRepo (originCube d m) s p q f

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
    {a : CoeffField d} (ha : AELocallyUniformlyEllipticField a) :
    _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a := by
  intro Q
  rcases ha (ofRepoTriadicCube Q) with ⟨lam, Lam, hlam, hle, hEll⟩
  refine ⟨lam, Lam, hlam, hle, ?_⟩
  have hRepo := toRepo_isAEEllipticFieldOn hEll
  simpa [_root_.Homogenization.Book.Ch04.AEEllipticOn,
    openCubeSet_ofRepoTriadicCube] using hRepo

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

namespace PeriodicSmooth

/-- Fixed-exponent homogenization comparison for smooth classical flux data over
the explicit deterministic periodic coefficient field `mFieldCoeff`, stated for
its Dirac law.

The Sobolev exponent is fixed to `s = 3/4` (an auxiliary internal exponent
`t = 1/8` with `4 t < s < 1` is used in the proof but does not appear in this
statement).  The constants
`C`, `alpha`, and `Cscale` are chosen before the dimension data. -/
theorem periodicSmooth_comparison
    {d : ℕ} [NeZero d] :
    ∃ C alpha Cscale : ℝ,
      0 < C ∧ 0 < alpha ∧ 0 < Cscale ∧
      ∀ (_two_le_dim : 2 ≤ d),
        ∃ sigmaBar : ℝ,
          0 < sigmaBar ∧
          ∃ X : CoeffField d → ℝ,
            IsPeriodicMinimalScale (mFieldCoeff (d := d)) 2 (2 * (d : ℝ) + 2) X Cscale ∧
            ∀ᵐ aω ∂Measure.dirac (mFieldCoeff (d := d)),
              ∀ (_ha : AELocallyUniformlyEllipticField aω)
                {m : ℕ} {u v : Vec d → ℝ} {g : Vec d → Vec d}
                (_hu : ContDiff ℝ (⊤ : ℕ∞) u)
                (_hv : ContDiff ℝ (⊤ : ℕ∞) v)
                (_hg : ContDiff ℝ 1 g)
                (_haflux : ContDiff ℝ 1
                  (fun x => matVecMul (aω x) (euclideanGradient u x)))
                (_hvflux : ContDiff ℝ 1
                  (fun x => matVecMul (scalarMatrix (d := d) sigmaBar) (euclideanGradient v x)))
                (_hlower_zero : ∀ i : Fin d, ∀ x : Vec d,
                  (u - v) (cubeLowerFaceProjection (originCube d m) i x) = 0)
                (_hupper_zero : ∀ i : Fin d, ∀ x : Vec d,
                  (u - v) (cubeUpperFaceProjection (originCube d m) i x) = 0)
                (_hu_div : ∀ x : Vec d,
                  euclideanDivergence (fun y => matVecMul (aω y) (euclideanGradient u y)) x =
                    euclideanDivergence g x)
                (_hv_div : ∀ x : Vec d,
                  euclideanDivergence
                      (fun y =>
                        matVecMul (scalarMatrix (d := d) sigmaBar) (euclideanGradient v y)) x =
                    euclideanDivergence g x),
                X aω ≤ (3 : ℝ) ^ m →
                ForceSobolevRegularity (originCube d m) fixedComparisonS g →
                classicalComparisonDefect (scalarMatrix (d := d) sigmaBar)
                    fixedComparisonS aω m u v ≤
                  C * ((3 : ℝ) ^ m / X aω) ^ (-alpha) *
                    classicalComparisonData sigmaBar fixedComparisonS aω m g u := by
  obtain ⟨C, alpha, Cscale, hC, halpha, hCscale, hmain⟩ :=
    _root_.Homogenization.Examples.Periodic.periodicSmooth_comparison (d := d)
  refine ⟨C, alpha, Cscale, hC, halpha, hCscale, ?_⟩
  intro two_le_dim
  let Lam : ℝ := 2 * (d : ℝ) + 2
  let Srepo : _root_.Homogenization.Book.MainResults.Setup d :=
    _root_.Homogenization.Examples.Periodic.periodicSetup
      two_le_dim (_root_.Homogenization.Examples.Periodic.mFieldCoeff (d := d)) 2 Lam
      _root_.Homogenization.Examples.Periodic.mFieldCoeff_periodic
      _root_.Homogenization.Examples.Periodic.mFieldCoeff_isotropic
      _root_.Homogenization.Examples.Periodic.mFieldCoeff_adjointInvariant
      (by norm_num)
      (by
        nlinarith [show 0 ≤ (d : ℝ) by exact_mod_cast Nat.zero_le d])
      (fun Q => _root_.Homogenization.Examples.Periodic.mFieldCoeff_aeeEllipticOn
        (_root_.Homogenization.measurableSet_openCubeSet Q))
  obtain ⟨sigmaBar, hsigma, X, hX, hmainS⟩ := hmain two_le_dim
  refine ⟨sigmaBar, hsigma, X, ?_, ?_⟩
  · simpa [Srepo, Lam, IsPeriodicMinimalScale, periodicThetaHat,
      mFieldCoeff, mField,
      _root_.Homogenization.Examples.Periodic.mFieldCoeff,
      _root_.Homogenization.Examples.Periodic.mField,
      _root_.Homogenization.Book.MainResults.Setup.IsMinimalScale,
      _root_.Homogenization.Book.MainResults.Setup.thetaHat,
      _root_.Homogenization.Book.Ch05.Section57.mainResultsThetaHat,
      _root_.Homogenization.Book.Ch05.Section57.uniformUpperBlockConst,
      _root_.Homogenization.Book.Ch05.Section57.uniformLowerInvBlockConst,
      _root_.Homogenization.Examples.Periodic.periodicSetup,
      _root_.Homogenization.Examples.Periodic.dirac_setup,
      _root_.Homogenization.Examples.Periodic.diracCoeffLaw,
      IndependentSums.IsBigO, _root_.Homogenization.IndependentSums.IsBigO,
      IndependentSums.IsBigOWith, _root_.Homogenization.IndependentSums.IsBigOWith,
      IndependentSums.upperTailEvent,
      _root_.Homogenization.IndependentSums.upperTailEvent,
      IndependentSums.gammaSigma, _root_.Homogenization.IndependentSums.gammaSigma] using hX
  · have hmainDirac :
        ∀ᵐ a ∂Measure.dirac (mFieldCoeff (d := d)),
          ∀ (haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a)
            {m : ℕ} {u v : Vec d → ℝ} {g : Vec d → Vec d}
            (hu : ContDiff ℝ (⊤ : ℕ∞) u)
            (hv : ContDiff ℝ (⊤ : ℕ∞) v)
            (hg : ContDiff ℝ 1 g)
            (haflux : ContDiff ℝ 1
              (fun x => _root_.Homogenization.matVecMul (a x)
                (_root_.Homogenization.euclideanGradient u x)))
            (hvflux : ContDiff ℝ 1
              (fun x => _root_.Homogenization.matVecMul
                (_root_.Homogenization.scalarMatrix (d := d) sigmaBar)
                (_root_.Homogenization.euclideanGradient v x)))
            (hlower_zero : ∀ i : Fin d, ∀ x : Vec d,
              (u - v)
                (_root_.Homogenization.cubeLowerFaceProjection
                  (_root_.Homogenization.Book.MainResults.originCube d m) i x) = 0)
            (hupper_zero : ∀ i : Fin d, ∀ x : Vec d,
              (u - v)
                (_root_.Homogenization.cubeUpperFaceProjection
                  (_root_.Homogenization.Book.MainResults.originCube d m) i x) = 0)
            (hu_div : ∀ x : Vec d,
              _root_.Homogenization.Examples.Periodic.euclideanDivergence
                  (fun y => _root_.Homogenization.matVecMul (a y)
                    (_root_.Homogenization.euclideanGradient u y)) x =
                _root_.Homogenization.Examples.Periodic.euclideanDivergence g x)
            (hv_div : ∀ x : Vec d,
              _root_.Homogenization.Examples.Periodic.euclideanDivergence
                  (fun y => _root_.Homogenization.matVecMul
                    (_root_.Homogenization.scalarMatrix (d := d) sigmaBar)
                    (_root_.Homogenization.euclideanGradient v y)) x =
                _root_.Homogenization.Examples.Periodic.euclideanDivergence g x),
            X a ≤ (3 : ℝ) ^ m →
            _root_.Homogenization.Book.Ch03.ForceSobolevRegularity
              (_root_.Homogenization.Book.MainResults.originCube d m)
              _root_.Homogenization.Book.MainResults.fixedComparisonS g →
            _root_.Homogenization.Examples.Periodic.classicalComparisonDefect
                (_root_.Homogenization.scalarMatrix (d := d) sigmaBar)
                _root_.Homogenization.Book.MainResults.fixedComparisonS a m u v ≤
              C * ((3 : ℝ) ^ m / X a) ^ (-alpha) *
                _root_.Homogenization.Examples.Periodic.classicalComparisonData
                  sigmaBar _root_.Homogenization.Book.MainResults.fixedComparisonS a m g u := by
      simpa [Srepo, Lam, mFieldCoeff, mField,
        _root_.Homogenization.Examples.Periodic.mFieldCoeff,
        _root_.Homogenization.Examples.Periodic.mField,
        _root_.Homogenization.Examples.Periodic.periodicSetup,
        _root_.Homogenization.Examples.Periodic.dirac_setup,
        _root_.Homogenization.Examples.Periodic.diracCoeffLaw] using hmainS
    filter_upwards [hmainDirac] with a hmain_a
    intro ha m u v g hu hv hg haflux hvflux hlower_zero hupper_zero hu_div hv_div hXm hgsob
    let haRepo :
        _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a :=
      toRepo_AELocallyUniformlyEllipticField ha
    have hgRepo :
        _root_.Homogenization.Book.Ch03.ForceSobolevRegularity
          (_root_.Homogenization.Book.MainResults.originCube d m)
          _root_.Homogenization.Book.MainResults.fixedComparisonS g := by
      simpa [fixedComparisonS,
        _root_.Homogenization.Book.MainResults.fixedComparisonS] using
        toRepo_ForceSobolevRegularity hgsob
    have hlowerRepo : ∀ i : Fin d, ∀ x : Vec d,
        (u - v)
          (_root_.Homogenization.cubeLowerFaceProjection
            (_root_.Homogenization.Book.MainResults.originCube d m) i x) = 0 := by
      intro i x
      simpa [_root_.Homogenization.cubeLowerFaceProjection,
        cubeLowerFaceProjection,
        _root_.Homogenization.cubeLowerFaceCoord, cubeLowerFaceCoord,
        _root_.Homogenization.Book.MainResults.originCube,
        _root_.Homogenization.Book.Ch05.Section57.assemblyOriginCube,
        _root_.Homogenization.originCube, originCube, triadicOriginCube,
        _root_.Homogenization.cubeScaleFactor, cubeScaleFactor] using
        hlower_zero i x
    have hupperRepo : ∀ i : Fin d, ∀ x : Vec d,
        (u - v)
          (_root_.Homogenization.cubeUpperFaceProjection
            (_root_.Homogenization.Book.MainResults.originCube d m) i x) = 0 := by
      intro i x
      simpa [_root_.Homogenization.cubeUpperFaceProjection,
        cubeUpperFaceProjection,
        _root_.Homogenization.cubeUpperFaceCoord, cubeUpperFaceCoord,
        _root_.Homogenization.Book.MainResults.originCube,
        _root_.Homogenization.Book.Ch05.Section57.assemblyOriginCube,
        _root_.Homogenization.originCube, originCube, triadicOriginCube,
        _root_.Homogenization.cubeScaleFactor, cubeScaleFactor] using
        hupper_zero i x
    have hafluxFun :
        (fun x => _root_.Homogenization.matVecMul (a x)
            (_root_.Homogenization.euclideanGradient u x))
          = fun x => matVecMul (a x) (euclideanGradient u x) := by
      funext x
      funext i
      simp [_root_.Homogenization.matVecMul, matVecMul,
        _root_.Homogenization.euclideanGradient, euclideanGradient,
        _root_.Homogenization.euclideanCoordDeriv, euclideanCoordDeriv,
        _root_.Homogenization.basisVec, basisVec]
    have hvfluxFun :
        (fun x => _root_.Homogenization.matVecMul
            (_root_.Homogenization.scalarMatrix (d := d) sigmaBar)
            (_root_.Homogenization.euclideanGradient v x))
          = fun x => matVecMul (scalarMatrix (d := d) sigmaBar) (euclideanGradient v x) := by
      funext x
      funext i
      simp [_root_.Homogenization.matVecMul, matVecMul,
        _root_.Homogenization.scalarMatrix, scalarMatrix,
        _root_.Homogenization.euclideanGradient, euclideanGradient,
        _root_.Homogenization.euclideanCoordDeriv, euclideanCoordDeriv,
        _root_.Homogenization.basisVec, basisVec]
    have hafluxRepo : ContDiff ℝ 1
        (fun x => _root_.Homogenization.matVecMul (a x)
          (_root_.Homogenization.euclideanGradient u x)) := by
      rw [hafluxFun]; exact haflux
    have hvfluxRepo : ContDiff ℝ 1
        (fun x => _root_.Homogenization.matVecMul
          (_root_.Homogenization.scalarMatrix (d := d) sigmaBar)
          (_root_.Homogenization.euclideanGradient v x)) := by
      rw [hvfluxFun]; exact hvflux
    have huDivRepo : ∀ x : Vec d,
        _root_.Homogenization.Examples.Periodic.euclideanDivergence
            (fun y => _root_.Homogenization.matVecMul (a y)
              (_root_.Homogenization.euclideanGradient u y)) x =
          _root_.Homogenization.Examples.Periodic.euclideanDivergence g x := by
      intro x
      simpa [_root_.Homogenization.Examples.Periodic.euclideanDivergence,
        euclideanDivergence,
        _root_.Homogenization.matVecMul, matVecMul,
        _root_.Homogenization.euclideanGradient, euclideanGradient,
        _root_.Homogenization.euclideanCoordDeriv, euclideanCoordDeriv,
        _root_.Homogenization.basisVec, basisVec] using hu_div x
    have hvDivRepo : ∀ x : Vec d,
        _root_.Homogenization.Examples.Periodic.euclideanDivergence
            (fun y => _root_.Homogenization.matVecMul
              (_root_.Homogenization.scalarMatrix (d := d) sigmaBar)
              (_root_.Homogenization.euclideanGradient v y)) x =
          _root_.Homogenization.Examples.Periodic.euclideanDivergence g x := by
      intro x
      simpa [_root_.Homogenization.Examples.Periodic.euclideanDivergence,
        euclideanDivergence,
        _root_.Homogenization.matVecMul, matVecMul,
        _root_.Homogenization.scalarMatrix, scalarMatrix,
        _root_.Homogenization.euclideanGradient, euclideanGradient,
        _root_.Homogenization.euclideanCoordDeriv, euclideanCoordDeriv,
        _root_.Homogenization.basisVec, basisVec] using hv_div x
    have hstep := hmain_a haRepo hu hv hg hafluxRepo hvfluxRepo hlowerRepo hupperRepo
      huDivRepo hvDivRepo hXm hgRepo
    simpa [fixedComparisonS,
      _root_.Homogenization.Book.MainResults.fixedComparisonS,
      _root_.Homogenization.Examples.Periodic.classicalComparisonDefect,
      classicalComparisonDefect,
      _root_.Homogenization.Examples.Periodic.classicalComparisonConstantGradientField,
      classicalComparisonConstantGradientField,
      _root_.Homogenization.Examples.Periodic.classicalComparisonFluxField,
      classicalComparisonFluxField,
      _root_.Homogenization.Examples.Periodic.classicalComparisonData,
      classicalComparisonData,
      _root_.Homogenization.Examples.Periodic.classicalH1EnergyNormOnCube,
      classicalH1EnergyNormOnCube,
      _root_.Homogenization.matVecMul, matVecMul,
      _root_.Homogenization.scalarMatrix, scalarMatrix,
      _root_.Homogenization.euclideanGradient, euclideanGradient,
      _root_.Homogenization.euclideanCoordDeriv, euclideanCoordDeriv,
      _root_.Homogenization.basisVec, basisVec,
      _root_.Homogenization.vecDot, vecDot,
      _root_.Homogenization.symmPart, symmPart,
      _root_.Homogenization.volumeAverage, volumeAverage,
      _root_.Homogenization.openCubeSet, openCubeSet,
      toRepo_originCube,
      cubeBesovDualFullNorm_originCube_toRepo,
      scaleNormalizedNegativeSobolevVectorNormTwo_toRepo,
      scaleNormalizedPositiveSobolevVectorSeminormTwo_toRepo,
      cubeBesovDualFullNorm_toRepo,
      gagliardoKernel_toRepo,
      _root_.Homogenization.Book.Ch03.scaleNormalizedNegativeSobolevVectorNormTwo,
      _root_.Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo,
      scaleNormalizedNegativeSobolevVectorNormTwo,
      _root_.Homogenization.Book.Ch03.scaleNormalizedPositiveSobolevVectorSeminormTwo,
      scaleNormalizedPositiveSobolevVectorSeminormTwo,
      _root_.Homogenization.Book.Ch01.fractionalSobolevSeminorm,
      fractionalSobolevSeminorm,
      _root_.Homogenization.Gagliardo.gagliardoKernel,
      Gagliardo.gagliardoKernel,
      _root_.Homogenization.Gagliardo.kernelExponent,
      Gagliardo.kernelExponent,
      _root_.Homogenization.Gagliardo.cubeGagliardoSeminorm,
      Gagliardo.cubeGagliardoSeminorm,
      _root_.Homogenization.Gagliardo.cubeGagliardoESeminorm,
      Gagliardo.cubeGagliardoESeminorm,
      _root_.Homogenization.Gagliardo.gagliardoCubeMeasure,
      Gagliardo.gagliardoCubeMeasure,
      _root_.Homogenization.cubeBesovScaleWeight, cubeBesovScaleWeight,
      _root_.Homogenization.cubeScaleFactor, cubeScaleFactor,
      _root_.Homogenization.cubeMeasure, cubeMeasure,
      _root_.Homogenization.cubeSet, cubeSet,
      _root_.Homogenization.normalizedCubeMeasure, normalizedCubeMeasure,
      _root_.Homogenization.cubeVolume, cubeVolume] using hstep

end PeriodicSmooth

end

end StatementAudit
end Homogenization
