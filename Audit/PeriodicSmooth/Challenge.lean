import Mathlib

/-!
# Mathlib-only challenge: classical (smooth) periodic homogenization comparison

This file is the comparator challenge surface for the *classical-solution* form
of the explicit periodic comparison theorem (field `a(x) = m(x) • I`,
`m(x) = d + 2 + ∑ i, cos (2 π xᵢ)`).  The solutions `u`, `v` are smooth scalar
fields solving the divergence-form equations `∇·(a∇u) = ∇·g` and `∇·(σ̄∇v) = ∇·g`
pointwise, with `u − v` vanishing on the cube faces; the weak `H¹` comparison
datum is constructed from this classical data by integration by parts, so no
weak-solution hypothesis is assumed.

It imports only Mathlib.  The theorem does not expose the project's internal
construction of the homogenized coefficient.  Instead it is the Mathlib-only
existential-scalar corollary of the public theorem: it asserts existence of a
positive scalar homogenized coefficient `sigmaBar`, and states the comparison
estimate directly for the classical solution data described above.

The definitions below are statement-level copies of the objects needed to state
this corollary.  The main source correspondences are:

* ambient fields and ellipticity: `Homogenization/Ambient/CoefficientField.lean`;
* coefficient laws and uniform ellipticity: `Homogenization/Book/Ch04/Law.lean`
  and `Homogenization/Book/Ch04/Theorems/UniformEllipticityBridge.lean`;
* cubes, weak equations, and energy quantities: `Homogenization/Book/Ch02` and
  `Homogenization/Book/Ch03`;
* positive and negative Sobolev quantities: `Homogenization/Book/Ch03/Theorems`;
* the public theorem surface: `Homogenization/Book/MainResults.lean`.

The only proof omitted in this challenge file is the final theorem proof.
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

/-! ## Almost-everywhere ellipticity -/

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

/-! ## Classical derivatives -/

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

def MemWsp (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞)
    (u : Vec d → E) : Prop :=
  MemLp (gagliardoKernel s p u) p (gagliardoCubeMeasure Q)

end Gagliardo

noncomputable abbrev fractionalSobolevSeminorm {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  Gagliardo.cubeGagliardoSeminorm Q s p u

def MemFractionalSobolev {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) : Prop :=
  MemLp u p (normalizedCubeMeasure Q) ∧ Gagliardo.MemWsp Q s p u

def ForceSobolevRegularity {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (g : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, MemFractionalSobolev Q s (2 : ℝ≥0∞) (fun x => g x i)

noncomputable def scaleNormalizedPositiveSobolevVectorSeminormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (g : Vec d → Vec d) : ℝ :=
  cubeBesovScaleWeight (-s) Q *
    ∑ i : Fin d, fractionalSobolevSeminorm Q s (2 : ℝ≥0∞) (fun x => g x i)

/-! ## Comparison estimate quantities -/

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

namespace PeriodicSmooth

/-- Fixed-exponent homogenization comparison for smooth classical solution data
over the explicit deterministic periodic coefficient field `mFieldCoeff`, stated
for its Dirac law.  The solutions `u`, `v` are smooth and solve the
divergence-form equations `∇·(a∇u) = ∇·g`, `∇·(σ̄∇v) = ∇·g` pointwise, with
`u − v` zero on the cube faces; the weak comparison datum is built from them by
integration by parts.

The estimate bounds the (classical) comparison defect by the energy data times
the algebraic rate `(3 ^ m / X a) ^ (-alpha)`.

The Sobolev exponent is fixed to `s = 3/4` (`fixedComparisonS`); the decay
exponent `alpha` and the constants `C`, `Cscale` are existential and chosen
before the dimension data.  (An auxiliary internal exponent `t = 1/8` with
`4 t < s < 1` is used in the proof but does not appear here.) -/
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
  sorry

end PeriodicSmooth

end

end StatementAudit
end Homogenization
