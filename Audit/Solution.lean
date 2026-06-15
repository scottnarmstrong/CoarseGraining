import Mathlib
import Homogenization.Book.MainResults

attribute [-instance] Homogenization.instMeasurableSpaceVec
attribute [-instance] Homogenization.instMeasurableSpaceMat
attribute [-instance] Homogenization.instMeasurableSpaceCoeffField

/-!
# Solution for the quenched comparison theorem challenge

This file is the comparator solution surface for the uniformly elliptic
quenched homogenization comparison theorem.

The corresponding challenge imports only Mathlib.  This solution imports the
repository theorem and proves the same `StatementAudit` theorem surface.
The theorem does not expose the project's internal
construction of the homogenized coefficient.  Instead it is the Mathlib-only
existential-scalar corollary of the public theorem: it asserts existence of a
positive scalar homogenized coefficient `sigmaBar`, and states the comparison
estimate directly for weak solutions of the heterogeneous equation and the
constant-coefficient equation with matrix `sigmaBar • I`.

The definitions below are deliberately statement-level copies of the objects
needed to state this corollary.  The main source correspondences are:

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

instance instMeasurableSpaceVec (d : ℕ) : MeasurableSpace (Vec d) := by
  exact @MeasurableSpace.pi (Fin d) (fun _ => ℝ)
    (fun _ => (RCLike.measurableSpace : MeasurableSpace ℝ))

instance instMeasurableSpaceMat (d : ℕ) : MeasurableSpace (Mat d) := by
  exact @MeasurableSpace.pi (Fin d) (fun _ => Fin d → ℝ)
    (fun _ => @MeasurableSpace.pi (Fin d) (fun _ => ℝ)
      (fun _ => (RCLike.measurableSpace : MeasurableSpace ℝ)))

abbrev CoeffField (d : ℕ) := Vec d → Mat d

instance instMeasurableSpaceCoeffField (d : ℕ) : MeasurableSpace (CoeffField d) := by
  exact @MeasurableSpace.pi (Vec d) (fun _ => Mat d)
    (fun _ => instMeasurableSpaceMat d)

abbrev CoeffLaw (d : ℕ) := Measure (CoeffField d)

def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i

def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x

def matVecMul {d : ℕ} (A : Mat d) (x : Vec d) : Vec d :=
  fun i => ∑ j, A i j * x j

def matTranspose {d : ℕ} (A : Mat d) : Mat d :=
  Matrix.transpose A

abbrev scalarMatrix {d : ℕ} (sigma : ℝ) : Mat d :=
  sigma • (1 : Mat d)

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

def translateCoeffField {d : ℕ} (z : Vec d) (a : CoeffField d) : CoeffField d :=
  fun x => a (fun i => x i + z i)

def intVecToRealVec {d : ℕ} (z : Fin d → ℤ) : Vec d :=
  fun i => (z i : ℝ)

def translateByInt {d : ℕ} (z : Fin d → ℤ) : CoeffField d → CoeffField d :=
  translateCoeffField (intVecToRealVec z)

def rotateCoeffField {d : ℕ} (R : Mat d) (a : CoeffField d) : CoeffField d :=
  fun x => (matTranspose R) * (a (matVecMul R x)) * R

def adjointCoeffField {d : ℕ} (a : CoeffField d) : CoeffField d :=
  fun x => matTranspose (a x)

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

/-! ## Law assumptions -/

noncomputable def localTestObservable {d : ℕ} (e e' : Vec d) (phi : Vec d → ℝ)
    (a : CoeffField d) : ℝ :=
  ∫ x, (vecDot e' (matVecMul (a x) e) * phi x) ∂MeasureTheory.volume

def LocalSigma {d : ℕ} (U : Set (Vec d)) : MeasurableSpace (CoeffField d) :=
  MeasurableSpace.generateFrom
    { s |
        ∃ e e' : Vec d, ∃ phi : Vec d → ℝ, ∃ t : Set ℝ,
          ContDiff ℝ (⊤ : ℕ∞) phi ∧
            HasCompactSupport phi ∧
            tsupport phi ⊆ U ∧
            MeasurableSet t ∧
            s = localTestObservable e e' phi ⁻¹' t }

def IsStationary {d : ℕ} (P : CoeffLaw d) : Prop :=
  ∀ z : Fin d → ℤ, Measure.map (translateByInt z) P = P

def AreUnitSeparated {d : ℕ} (U V : Set (Vec d)) : Prop :=
  ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V → 1 ≤ dist x y

def IsUnitRangeDependent {d : ℕ} (P : CoeffLaw d) : Prop :=
  ∀ U V : Set (Vec d), AreUnitSeparated U V →
    ProbabilityTheory.Indep (LocalSigma U) (LocalSigma V) P

def IsSignedPermutationMatrix {d : ℕ} (R : Mat d) : Prop :=
  ∃ sigma : Equiv.Perm (Fin d), ∃ signs : Fin d → ℝ,
    (∀ i, signs i = 1 ∨ signs i = -1) ∧
      ∀ i j, R i j = if i = sigma j then signs j else 0

def IsIsotropicInLaw {d : ℕ} (P : CoeffLaw d) : Prop :=
  ∀ R : Mat d, IsSignedPermutationMatrix R →
    Measure.map (rotateCoeffField R) P = P

def IsAdjointInvariantInLaw {d : ℕ} (P : CoeffLaw d) : Prop :=
  Measure.map adjointCoeffField P = P

def IsAEEllipticFieldOn {d : ℕ} (lam Lam : ℝ) (U : Set (Vec d))
    (a : CoeffField d) : Prop :=
  MeasurableSet U ∧
    (∀ i j : Fin d,
      AEStronglyMeasurable
        (fun x : Vec d => restrictCoeffField U a x i j) (volumeMeasureOn U)) ∧
      ∀ᵐ x ∂ volumeMeasureOn U, IsEllipticMatrix lam Lam (a x)

def AEEQuantitativeEllipticSlice {d : ℕ} (U : Set (Vec d)) (k : ℕ)
    (a : CoeffField d) : Prop :=
  IsAEEllipticFieldOn ((k + 1 : ℝ)⁻¹) (k + 1 : ℝ) U a

def AELocallyUniformlyEllipticField {d : ℕ} (a : CoeffField d) : Prop :=
  ∀ Q : TriadicCube d,
    ∃ lam Lam : ℝ,
      0 < lam ∧ lam ≤ Lam ∧
        IsAEEllipticFieldOn lam Lam (openCubeSet Q) a

def AELocallyUniformlyEllipticLaw {d : ℕ} (P : CoeffLaw d) : Prop :=
  ∀ᵐ a ∂P, AELocallyUniformlyEllipticField a

structure LocalObservableLawCarrier {d : ℕ} (P : CoeffLaw d) : Prop where
  nullMeasurable_localSigma :
    ∀ (U : Set (Vec d)) (s : Set (CoeffField d)),
      @MeasurableSet (CoeffField d) (LocalSigma U) s →
        NullMeasurableSet s P

structure LawCarrier {d : ℕ} (P : CoeffLaw d) : Prop where
  isProbability : IsProbabilityMeasure P
  ae_locally_uniformly_elliptic : AELocallyUniformlyEllipticLaw P
  local_observable_measurable : LocalObservableLawCarrier P
  aee_quantitative_slice_measurable :
    ∀ (Q : TriadicCube d) (k : ℕ),
      @MeasurableSet (CoeffField d) (LocalSigma (cubeSet Q))
        {a : CoeffField d | AEEQuantitativeEllipticSlice (cubeSet Q) k a}

structure StructuralLaw {d : ℕ} (P : CoeffLaw d) : Prop where
  stationary : IsStationary P
  unit_range : IsUnitRangeDependent P
  isotropic : IsIsotropicInLaw P
  adjoint_invariant : IsAdjointInvariantInLaw P

structure UniformEllipticityBounds {d : ℕ}
    (P : CoeffLaw d) (lam Lam : ℝ) : Prop where
  lam_pos : 0 < lam
  lam_le_Lam : lam ≤ Lam
  aee_elliptic :
    ∀ᵐ a ∂P,
      ∀ Q : TriadicCube d,
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

noncomputable def weakFDeriv {d : ℕ} (phi : Vec d → ℝ) (x : Vec d) :=
  @fderiv ℝ _ (Vec d) _ (vecModule d) _ ℝ _ _ _ phi x

def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)

def HasWeakPartialDerivOn {d : ℕ} (U : Set (Vec d)) (i : Fin d)
    (u gi : Vec d → ℝ) : Prop :=
  ∀ phi : Vec d → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) phi →
    HasCompactSupport phi →
    tsupport phi ⊆ U →
    ∫ x in U, u x * (weakFDeriv phi x) (basisVec i) ∂MeasureTheory.volume =
      -∫ x in U, gi x * phi x ∂MeasureTheory.volume

def HasWeakGradientOn {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ)
    (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, HasWeakPartialDerivOn U i u (fun x => Du x i)

abbrev MemL2On {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  MemLp u 2 (MeasureTheory.volume.restrict U)

def GradMemL2On {d : ℕ} (U : Set (Vec d)) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, MemL2On U (fun x => Du x i)

structure H1Function {d : ℕ} (U : Set (Vec d)) where
  toFun : Vec d → ℝ
  grad : Vec d → Vec d
  memL2 : MemL2On U toFun
  gradMemL2 : GradMemL2On U grad
  hasWeakGradient : HasWeakGradientOn U toFun grad

instance {d : ℕ} {U : Set (Vec d)} : CoeFun (H1Function U)
    (fun _ => Vec d → ℝ) where
  coe u := u.toFun

structure H10Function {d : ℕ} (U : Set (Vec d)) extends H1Function U where
  approx : ℕ → Vec d → ℝ
  approx_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (approx n)
  approx_hasCompactSupport : ∀ n, HasCompactSupport (approx n)
  approx_support_subset : ∀ n, tsupport (approx n) ⊆ U
  tendsto_approx :
    Filter.Tendsto
      (fun n => eLpNorm (fun x => approx n x - toH1Function.toFun x) 2
        (MeasureTheory.volume.restrict U))
      Filter.atTop (nhds 0)
  tendsto_approx_grad :
    ∀ i : Fin d,
      Filter.Tendsto
        (fun n => eLpNorm
          (fun x => (weakFDeriv (approx n) x) (basisVec i) - toH1Function.grad x i) 2
          (MeasureTheory.volume.restrict U))
        Filter.atTop (nhds 0)

def IsForcedEquation {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (u : H1Function (openCubeSet Q)) (g : Vec d → Vec d) : Prop :=
  ∀ phi : H10Function (openCubeSet Q),
    ∫ x in openCubeSet Q,
        vecDot (matVecMul (a x) (u.grad x)) (phi.toH1Function.grad x)
          ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q,
        vecDot (g x) (phi.toH1Function.grad x) ∂MeasureTheory.volume

def IsConstantCoeffForcedEquation {d : ℕ} (Q : TriadicCube d) (sigmaBar : ℝ)
    (v : H1Function (openCubeSet Q)) (g : Vec d → Vec d) : Prop :=
  ∀ phi : H10Function (openCubeSet Q),
    ∫ x in openCubeSet Q,
        vecDot (matVecMul (scalarMatrix (d := d) sigmaBar) (v.grad x))
          (phi.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q,
        vecDot (g x) (phi.toH1Function.grad x) ∂MeasureTheory.volume

/--
The unfolded comparison datum used in the theorem.

In the repository, the public comparison pair is built from an almost-sure
ellipticity witness and an assembled coefficient family.  In the uniformly
elliptic scalar challenge, that assembled field evaluates to the raw field
`a`; the witness is still an explicit parameter so the theorem surface has the
same dependency shape as the public result.
-/
structure ComparisonPair {d : ℕ} [NeZero d] (sigmaBar : ℝ)
    (a : CoeffField d) (_ha : AELocallyUniformlyEllipticField a)
    (m : ℕ) (g : Vec d → Vec d) where
  u : H1Function (openCubeSet (originCube d m))
  v : H1Function (openCubeSet (originCube d m))
  uWeakSolution : IsForcedEquation (originCube d m) a u g
  vWeakSolution : IsConstantCoeffForcedEquation (originCube d m) sigmaBar v g
  zeroTraceDifference :
    ∃ w : H10Function (openCubeSet (originCube d m)),
      w.toH1Function.toFun =ᵐ[volumeMeasureOn (openCubeSet (originCube d m))]
        fun x => u.toFun x - v.toFun x

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

/-! ## Comparison estimate quantities -/

noncomputable def h1EnergyNormOnCube {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (u : H1Function (openCubeSet Q)) : ℝ :=
  Real.sqrt <|
    volumeAverage (openCubeSet Q) fun x =>
      vecDot (u.grad x) (matVecMul (symmPart (a x)) (u.grad x))

noncomputable def comparisonConstantGradientField {d : ℕ} {Q : TriadicCube d}
    (sigmaBar : ℝ) (u v : H1Function (openCubeSet Q)) : Vec d → Vec d :=
  fun x => matVecMul (scalarMatrix (d := d) sigmaBar) (u.grad x - v.grad x)

noncomputable def comparisonFluxField {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (sigmaBar : ℝ)
    (u v : H1Function (openCubeSet Q)) : Vec d → Vec d :=
  fun x => matVecMul (a x) (u.grad x) -
    matVecMul (scalarMatrix (d := d) sigmaBar) (v.grad x)

noncomputable def comparisonDefect {d : ℕ} [NeZero d] (sigmaBar : ℝ)
    (s : ℝ) {a : CoeffField d} {ha : AELocallyUniformlyEllipticField a}
    {m : ℕ} {g : Vec d → Vec d} (pair : ComparisonPair sigmaBar a ha m g) : ℝ :=
  scaleNormalizedNegativeSobolevVectorNormTwo (originCube d m) s
      (comparisonConstantGradientField sigmaBar pair.u pair.v) +
    scaleNormalizedNegativeSobolevVectorNormTwo (originCube d m) s
      (comparisonFluxField (originCube d m) a sigmaBar pair.u pair.v)

noncomputable def comparisonData {d : ℕ} [NeZero d] (sigmaBar : ℝ)
    (s : ℝ) {a : CoeffField d} {ha : AELocallyUniformlyEllipticField a}
    {m : ℕ} {g : Vec d → Vec d} (pair : ComparisonPair sigmaBar a ha m g) : ℝ :=
  Real.sqrt sigmaBar * h1EnergyNormOnCube (originCube d m) a pair.u +
    scaleNormalizedPositiveSobolevVectorSeminormTwo (originCube d m) s g

/-! ## Uniformly elliptic main theorem surface -/

structure Setup (d : ℕ) [NeZero d] where
  two_le_dim : 2 ≤ d
  P : CoeffLaw d
  hP : LawCarrier P
  hStruct : StructuralLaw P
  lam : ℝ
  Lam : ℝ
  hUE : UniformEllipticityBounds P lam Lam

namespace Setup

variable {d : ℕ} [NeZero d] (S : Setup d)

noncomputable def uniformUpperBlockConst : ℝ :=
  4 * (Fintype.card (Fin d) : ℝ) * S.lam⁻¹ * S.Lam ^ (2 : ℕ)

noncomputable def uniformLowerInvBlockConst : ℝ :=
  4 * (Fintype.card (Fin d) : ℝ) * S.lam⁻¹

noncomputable def thetaHat : ℝ :=
  1 + S.uniformLowerInvBlockConst * S.uniformUpperBlockConst +
    S.uniformUpperBlockConst * S.uniformLowerInvBlockConst

def IsMinimalScale (X : CoeffField d → ℝ) (Cscale : ℝ) : Prop :=
  (∀ a, 1 ≤ X a) ∧
    IsBigO S.P (gammaSigma ((d : ℕ) : ℝ)) X
      (Real.exp (Cscale * (Real.log (2 + S.thetaHat)) ^ (2 : ℕ)))

end Setup

/-! ## Solution-only bridges to the repository theorem -/

private def toRepoTriadicCube {d : ℕ} (Q : TriadicCube d) :
    _root_.Homogenization.TriadicCube d :=
  { scale := Q.scale
    index := Q.index }

private def ofRepoTriadicCube {d : ℕ}
    (Q : _root_.Homogenization.TriadicCube d) : TriadicCube d :=
  { scale := Q.scale
    index := Q.index }

private theorem cubeSet_ofRepoTriadicCube {d : ℕ}
    (Q : _root_.Homogenization.TriadicCube d) :
    cubeSet (ofRepoTriadicCube Q) = _root_.Homogenization.cubeSet Q :=
  rfl

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

private def toRepoLocalObservableLawCarrier {d : ℕ} {P : CoeffLaw d}
    (h : LocalObservableLawCarrier P) :
    _root_.Homogenization.Book.Ch04.LocalObservableLawCarrier P where
  nullMeasurable_localSigma := by
    intro U s hs
    have hsAudit : @MeasurableSet (CoeffField d) (LocalSigma U) s := by
      simpa [_root_.Homogenization.Book.Ch04.localSigma,
        _root_.Homogenization.LocalSigma, LocalSigma,
        _root_.Homogenization.localTestObservable, localTestObservable,
        vecDot, _root_.Homogenization.vecDot,
        matVecMul, _root_.Homogenization.matVecMul] using hs
    exact h.nullMeasurable_localSigma U s hsAudit

private def toRepoLawCarrier {d : ℕ} {P : CoeffLaw d}
    (hP : LawCarrier P) :
    _root_.Homogenization.Book.Ch04.LawCarrier P where
  isProbability := hP.isProbability
  ae_locally_uniformly_elliptic := by
    filter_upwards [hP.ae_locally_uniformly_elliptic] with a ha
    exact toRepo_AELocallyUniformlyEllipticField ha
  local_observable_measurable :=
    toRepoLocalObservableLawCarrier hP.local_observable_measurable
  aee_quantitative_slice_measurable := by
    intro Q k
    have hAudit :=
      hP.aee_quantitative_slice_measurable (ofRepoTriadicCube Q) k
    simpa [_root_.Homogenization.Book.Ch04.localSigma,
      _root_.Homogenization.LocalSigma, LocalSigma,
      _root_.Homogenization.localTestObservable, localTestObservable,
      _root_.Homogenization.AEEQuantitativeEllipticSlice,
      AEEQuantitativeEllipticSlice,
      _root_.Homogenization.Book.Ch04.AEEllipticOn,
      _root_.Homogenization.IsAEEllipticFieldOn, IsAEEllipticFieldOn,
      _root_.Homogenization.restrictCoeffField, restrictCoeffField,
      _root_.Homogenization.IsEllipticMatrix, IsEllipticMatrix,
      _root_.Homogenization.vecDot, vecDot,
      _root_.Homogenization.vecNormSq, vecNormSq,
      _root_.Homogenization.matVecMul, matVecMul,
      cubeSet_ofRepoTriadicCube] using hAudit

private def toRepoStructuralLaw {d : ℕ} {P : CoeffLaw d}
    (hStruct : StructuralLaw P) :
    _root_.Homogenization.Book.Ch04.StructuralLaw P where
  stationary := by
    simpa [_root_.Homogenization.Book.Ch04.StationaryLaw,
      _root_.Homogenization.IsStationary, IsStationary,
      _root_.Homogenization.translateByInt, translateByInt,
      _root_.Homogenization.intVecToRealVec, intVecToRealVec,
      _root_.Homogenization.translateCoeffField, translateCoeffField] using
      hStruct.stationary
  unit_range := by
    simpa [_root_.Homogenization.Book.Ch04.UnitRangeDependentLaw,
      _root_.Homogenization.IsUnitRangeDependent, IsUnitRangeDependent,
      _root_.Homogenization.AreUnitSeparated, AreUnitSeparated,
      _root_.Homogenization.LocalSigma, LocalSigma,
      _root_.Homogenization.localTestObservable, localTestObservable,
      _root_.Homogenization.vecDot, vecDot,
      _root_.Homogenization.matVecMul, matVecMul] using hStruct.unit_range
  isotropic := by
    simpa [_root_.Homogenization.Book.Ch04.IsotropicLaw,
      _root_.Homogenization.IsIsotropicInLaw, IsIsotropicInLaw,
      _root_.Homogenization.IsSignedPermutationMatrix, IsSignedPermutationMatrix,
      _root_.Homogenization.rotateCoeffField, rotateCoeffField,
      _root_.Homogenization.matTranspose, matTranspose,
      _root_.Homogenization.matVecMul, matVecMul] using hStruct.isotropic
  adjoint_invariant := by
    simpa [_root_.Homogenization.Book.Ch04.AdjointInvariantLaw,
      _root_.Homogenization.IsAdjointInvariantInLaw, IsAdjointInvariantInLaw,
      _root_.Homogenization.adjointCoeffField, adjointCoeffField,
      _root_.Homogenization.matTranspose, matTranspose] using
      hStruct.adjoint_invariant

private def toRepoUniformEllipticityBounds {d : ℕ} {P : CoeffLaw d}
    {lam Lam : ℝ} (hUE : UniformEllipticityBounds P lam Lam) :
    _root_.Homogenization.Book.Ch05.Section57.UniformEllipticityBounds P lam Lam where
  lam_pos := hUE.lam_pos
  lam_le_Lam := hUE.lam_le_Lam
  aee_elliptic := by
    filter_upwards [hUE.aee_elliptic] with a ha Q
    have hRepo := toRepo_isAEEllipticFieldOn (ha (ofRepoTriadicCube Q))
    simpa [openCubeSet_ofRepoTriadicCube] using hRepo

private noncomputable def toRepoSetup {d : ℕ} [NeZero d] (S : Setup d) :
    _root_.Homogenization.Book.MainResults.Setup d where
  two_le_dim := S.two_le_dim
  P := S.P
  hP := toRepoLawCarrier S.hP
  hStruct := toRepoStructuralLaw S.hStruct
  lam := S.lam
  Lam := S.Lam
  hUE := toRepoUniformEllipticityBounds S.hUE

private def toRepoH1Function {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) : _root_.Homogenization.H1Function U where
  toFun := u.toFun
  grad := u.grad
  memL2 := by
    simpa [MemL2On, _root_.Homogenization.MemL2On] using u.memL2
  gradMemL2 := by
    simpa [GradMemL2On, _root_.Homogenization.GradMemL2On,
      MemL2On, _root_.Homogenization.MemL2On] using u.gradMemL2
  hasWeakGradient := by
    simpa [HasWeakGradientOn, _root_.Homogenization.HasWeakGradientOn,
      HasWeakPartialDerivOn, _root_.Homogenization.HasWeakPartialDerivOn,
      basisVec, _root_.Homogenization.basisVec] using u.hasWeakGradient

private def ofRepoH1Function {d : ℕ} {U : Set (Vec d)}
    (u : _root_.Homogenization.H1Function U) : H1Function U where
  toFun := u.toFun
  grad := u.grad
  memL2 := by
    simpa [MemL2On, _root_.Homogenization.MemL2On] using u.memL2
  gradMemL2 := by
    simpa [GradMemL2On, _root_.Homogenization.GradMemL2On,
      MemL2On, _root_.Homogenization.MemL2On] using u.gradMemL2
  hasWeakGradient := by
    simpa [HasWeakGradientOn, _root_.Homogenization.HasWeakGradientOn,
      HasWeakPartialDerivOn, _root_.Homogenization.HasWeakPartialDerivOn,
      basisVec, _root_.Homogenization.basisVec] using u.hasWeakGradient

private def toRepoH10Function {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) : _root_.Homogenization.H10Function U where
  toH1Function := toRepoH1Function u.toH1Function
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_hasCompactSupport := u.approx_hasCompactSupport
  approx_support_subset := u.approx_support_subset
  tendsto_approx := by
    simpa [toRepoH1Function] using u.tendsto_approx
  tendsto_approx_grad := by
    intro i
    simpa [toRepoH1Function, basisVec, _root_.Homogenization.basisVec] using
      u.tendsto_approx_grad i

private def ofRepoH10Function {d : ℕ} {U : Set (Vec d)}
    (u : _root_.Homogenization.H10Function U) : H10Function U where
  toH1Function := ofRepoH1Function u.toH1Function
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_hasCompactSupport := u.approx_hasCompactSupport
  approx_support_subset := u.approx_support_subset
  tendsto_approx := by
    simpa [ofRepoH1Function] using u.tendsto_approx
  tendsto_approx_grad := by
    intro i
    simpa [ofRepoH1Function, basisVec, _root_.Homogenization.basisVec] using
      u.tendsto_approx_grad i

private def toRepoH1Origin {d : ℕ} [NeZero d] {m : ℕ}
    (u : H1Function (openCubeSet (originCube d m))) :
    _root_.Homogenization.H1Function
      (_root_.Homogenization.Book.Ch02.cubeDomain
        (_root_.Homogenization.Book.MainResults.originCube d m) : Set (Vec d)) := by
  simpa [_root_.Homogenization.Book.MainResults.originCube,
    _root_.Homogenization.Book.Ch05.Section57.assemblyOriginCube,
    _root_.Homogenization.originCube, originCube, triadicOriginCube,
    _root_.Homogenization.Book.Ch02.cubeDomain_coe,
    _root_.Homogenization.openCubeSet, openCubeSet,
    _root_.Homogenization.cubeScaleFactor, cubeScaleFactor] using
    toRepoH1Function u

private def toRepoH10Origin {d : ℕ} [NeZero d] {m : ℕ}
    (u : H10Function (openCubeSet (originCube d m))) :
    _root_.Homogenization.H10Function
      (_root_.Homogenization.Book.Ch02.cubeDomain
        (_root_.Homogenization.Book.MainResults.originCube d m) : Set (Vec d)) := by
  simpa [_root_.Homogenization.Book.MainResults.originCube,
    _root_.Homogenization.Book.Ch05.Section57.assemblyOriginCube,
    _root_.Homogenization.originCube, originCube, triadicOriginCube,
    _root_.Homogenization.Book.Ch02.cubeDomain_coe,
    _root_.Homogenization.openCubeSet, openCubeSet,
    _root_.Homogenization.cubeScaleFactor, cubeScaleFactor] using
    toRepoH10Function u

@[simp] private theorem toRepoH1Function_toFun {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) :
    (toRepoH1Function u).toFun = u.toFun :=
  rfl

@[simp] private theorem toRepoH1Function_grad {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) :
    (toRepoH1Function u).grad = u.grad :=
  rfl

@[simp] private theorem ofRepoH1Function_toFun {d : ℕ} {U : Set (Vec d)}
    (u : _root_.Homogenization.H1Function U) :
    (ofRepoH1Function u).toFun = u.toFun :=
  rfl

@[simp] private theorem ofRepoH1Function_grad {d : ℕ} {U : Set (Vec d)}
    (u : _root_.Homogenization.H1Function U) :
    (ofRepoH1Function u).grad = u.grad :=
  rfl

@[simp] private theorem toRepoH10Function_toFun {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) :
    (toRepoH10Function u).toFun = u.toFun :=
  rfl

@[simp] private theorem toRepoH1Origin_toFun {d : ℕ} [NeZero d] {m : ℕ}
    (u : H1Function (openCubeSet (originCube d m))) :
    (toRepoH1Origin u).toFun = u.toFun := by
  simp [toRepoH1Origin]

@[simp] private theorem toRepoH1Origin_grad {d : ℕ} [NeZero d] {m : ℕ}
    (u : H1Function (openCubeSet (originCube d m))) :
    (toRepoH1Origin u).grad = u.grad := by
  simp [toRepoH1Origin]

@[simp] private theorem toRepoH10Origin_toFun {d : ℕ} [NeZero d] {m : ℕ}
    (u : H10Function (openCubeSet (originCube d m))) :
    (toRepoH10Origin u).toFun = u.toFun := by
  simp [toRepoH10Origin]

@[simp] private theorem ofRepoH10Function_grad {d : ℕ} {U : Set (Vec d)}
    (u : _root_.Homogenization.H10Function U) :
    (ofRepoH10Function u).toH1Function.grad = u.toH1Function.grad := by
  simp [ofRepoH10Function]

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

private noncomputable def toRepoComparisonPair {d : ℕ} [NeZero d]
    {sigmaBar : ℝ} (hsigma : 0 < sigmaBar)
    {a : CoeffField d} {ha : AELocallyUniformlyEllipticField a}
    (haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a)
    {m : ℕ} {g : Vec d → Vec d}
    (pair : ComparisonPair sigmaBar a ha m g) :
    _root_.Homogenization.Book.Ch05.Section57.assemblyComparisonDatumOfScalar
      sigmaBar hsigma a haRepo m g where
  u := by
    simpa [_root_.Homogenization.Book.MainResults.originCube] using
      toRepoH1Origin pair.u
  v := by
    simpa [_root_.Homogenization.Book.MainResults.originCube] using
      toRepoH1Origin pair.v
  uWeakSolution := by
    intro phi
    have hphi := pair.uWeakSolution (ofRepoH10Function phi)
    simpa [_root_.Homogenization.Book.Ch03.IsForcedEquation, IsForcedEquation,
      _root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily,
      _root_.Homogenization.Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
      _root_.Homogenization.Book.Ch04.coeffOnOfAEEllipticOn,
      _root_.Homogenization.Book.Ch02.cubeDomain_coe,
      _root_.Homogenization.Book.Ch05.Section57.assemblyOriginCube,
      _root_.Homogenization.originCube, originCube, triadicOriginCube,
      _root_.Homogenization.openCubeSet, openCubeSet,
      _root_.Homogenization.cubeScaleFactor, cubeScaleFactor,
      toRepoH1Function, ofRepoH10Function,
      _root_.Homogenization.vecDot, vecDot,
      _root_.Homogenization.matVecMul, matVecMul] using hphi
  vWeakSolution := by
    intro phi
    have hphi := pair.vWeakSolution (ofRepoH10Function phi)
    simpa [_root_.Homogenization.Book.Ch03.IsConstantCoeffForcedEquation,
      IsConstantCoeffForcedEquation,
      _root_.Homogenization.Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar,
      _root_.Homogenization.Book.Ch05.Section57.scalarConstantCoeffMatrix,
      _root_.Homogenization.Book.Ch05.Section57.assemblyOriginCube,
      _root_.Homogenization.originCube, originCube, triadicOriginCube,
      _root_.Homogenization.Book.Ch02.cubeDomain_coe,
      _root_.Homogenization.openCubeSet, openCubeSet,
      _root_.Homogenization.cubeScaleFactor, cubeScaleFactor,
      toRepoH1Function, ofRepoH10Function,
      _root_.Homogenization.scalarMatrix, scalarMatrix,
      _root_.Homogenization.vecDot, vecDot,
      _root_.Homogenization.matVecMul, matVecMul] using hphi
  zeroTraceDifference := by
    rcases pair.zeroTraceDifference with ⟨w, hw⟩
    refine ⟨?_, ?_⟩
    · simpa [_root_.Homogenization.Book.Ch05.Section57.assemblyOriginCube,
        _root_.Homogenization.originCube, originCube, triadicOriginCube,
        _root_.Homogenization.Book.Ch02.cubeDomain_coe,
        _root_.Homogenization.openCubeSet, openCubeSet,
        _root_.Homogenization.cubeScaleFactor, cubeScaleFactor] using
        (toRepoH10Origin w)
    · simpa [toRepoH10Function, toRepoH1Function,
        _root_.Homogenization.Book.Ch05.Section57.assemblyOriginCube,
        _root_.Homogenization.originCube, originCube, triadicOriginCube,
        _root_.Homogenization.Book.Ch02.cubeDomain_coe,
        _root_.Homogenization.openCubeSet, openCubeSet,
        _root_.Homogenization.cubeScaleFactor, cubeScaleFactor] using hw

private theorem h1EnergyNormOnCube_toRepo {d : ℕ} [NeZero d]
    {a : CoeffField d}
    {haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a}
    {m : ℕ} (u : H1Function (openCubeSet (originCube d m))) :
    _root_.Homogenization.Book.Ch03.h1EnergyNormOnCube
        (_root_.Homogenization.Book.MainResults.originCube d m)
        (_root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily a haRepo)
        (toRepoH1Origin u) =
      h1EnergyNormOnCube (originCube d m) a u := by
  simp [_root_.Homogenization.Book.Ch03.h1EnergyNormOnCube,
    _root_.Homogenization.Book.Ch03.localizedCoeffEnergyValue,
    _root_.Homogenization.Book.Ch03.normalizedSetAverage,
    h1EnergyNormOnCube,
    _root_.Homogenization.volumeAverage, volumeAverage,
    _root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily,
    _root_.Homogenization.Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
    _root_.Homogenization.Book.Ch04.coeffOnOfAEEllipticOn,
    _root_.Homogenization.Book.Ch02.cubeDomain_coe,
    _root_.Homogenization.Book.MainResults.originCube,
    _root_.Homogenization.Book.Ch05.Section57.assemblyOriginCube,
    _root_.Homogenization.originCube, originCube, triadicOriginCube,
    _root_.Homogenization.openCubeSet, openCubeSet,
    _root_.Homogenization.cubeScaleFactor, cubeScaleFactor,
    _root_.Homogenization.symmPart, symmPart,
    _root_.Homogenization.vecDot, vecDot,
    _root_.Homogenization.matVecMul, matVecMul,
    toRepoH1Origin, toRepoH1Function]

private theorem comparisonDefect_toRepo {d : ℕ} [NeZero d]
    {sigmaBar : ℝ} (hsigma : 0 < sigmaBar)
    {a : CoeffField d} {ha : AELocallyUniformlyEllipticField a}
    {haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a}
    {m : ℕ} {g : Vec d → Vec d} (s : ℝ)
    (pair : ComparisonPair sigmaBar a ha m g) :
    _root_.Homogenization.Book.Ch03.homogenizationComparisonNegativeSobolevLHS
        (_root_.Homogenization.Book.MainResults.originCube d m)
        (_root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily a haRepo)
        (_root_.Homogenization.Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar
          sigmaBar hsigma)
        s (toRepoH1Origin pair.u) (toRepoH1Origin pair.v) =
      comparisonDefect sigmaBar s pair := by
  have hgrad :
      _root_.Homogenization.Book.Ch03.homogenizationComparisonConstantGradientField
          (_root_.Homogenization.Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar
            sigmaBar hsigma)
          (toRepoH1Origin pair.u) (toRepoH1Origin pair.v) =
        comparisonConstantGradientField sigmaBar pair.u pair.v := by
    funext x i
    simp [_root_.Homogenization.Book.Ch03.homogenizationComparisonConstantGradientField,
      comparisonConstantGradientField,
      _root_.Homogenization.Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar,
      _root_.Homogenization.Book.Ch05.Section57.scalarConstantCoeffMatrix,
      _root_.Homogenization.scalarMatrix, scalarMatrix,
      _root_.Homogenization.matVecMul, matVecMul, toRepoH1Origin, toRepoH1Function]
  have hflux :
      _root_.Homogenization.Book.Ch03.homogenizationComparisonFluxField
          (_root_.Homogenization.Book.MainResults.originCube d m)
          (_root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily a haRepo)
          (_root_.Homogenization.Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar
            sigmaBar hsigma)
          (toRepoH1Origin pair.u) (toRepoH1Origin pair.v) =
        comparisonFluxField (originCube d m) a sigmaBar pair.u pair.v := by
    funext x i
    simp [_root_.Homogenization.Book.Ch03.homogenizationComparisonFluxField,
      comparisonFluxField,
      _root_.Homogenization.Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar,
      _root_.Homogenization.Book.Ch05.Section57.scalarConstantCoeffMatrix,
      _root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily,
      _root_.Homogenization.Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
      _root_.Homogenization.Book.Ch04.coeffOnOfAEEllipticOn,
      _root_.Homogenization.Book.Ch02.cubeDomain_coe,
      _root_.Homogenization.originCube, triadicOriginCube,
      _root_.Homogenization.scalarMatrix, scalarMatrix,
      _root_.Homogenization.matVecMul, matVecMul, toRepoH1Origin, toRepoH1Function]
  unfold _root_.Homogenization.Book.Ch03.homogenizationComparisonNegativeSobolevLHS
    comparisonDefect
  rw [hgrad, hflux, ← toRepo_originCube (d := d) m]
  rw [scaleNormalizedNegativeSobolevVectorNormTwo_toRepo,
    scaleNormalizedNegativeSobolevVectorNormTwo_toRepo]

private theorem comparisonData_toRepo {d : ℕ} [NeZero d]
    {sigmaBar : ℝ} {a : CoeffField d}
    {ha : AELocallyUniformlyEllipticField a}
    {haRepo : _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a}
    {m : ℕ} {g : Vec d → Vec d} (s : ℝ)
    (pair : ComparisonPair sigmaBar a ha m g) :
    Real.sqrt sigmaBar *
        _root_.Homogenization.Book.Ch03.h1EnergyNormOnCube
          (_root_.Homogenization.Book.MainResults.originCube d m)
          (_root_.Homogenization.Book.Ch05.Section57.assemblyCoeffFamily a haRepo)
          (toRepoH1Origin pair.u) +
      _root_.Homogenization.Book.Ch03.scaleNormalizedPositiveSobolevVectorSeminormTwo
        (_root_.Homogenization.Book.MainResults.originCube d m) s g =
      comparisonData sigmaBar s pair := by
  rw [h1EnergyNormOnCube_toRepo, scaleNormalizedPositiveSobolevVectorSeminormTwo_toRepo]
  rfl

/-- Fixed-exponent quenched homogenization comparison in the uniformly elliptic case.

This is the Mathlib-only existential-scalar corollary of the public theorem.
The repository proves the comparison for its internally constructed scalar
homogenized coefficient; this challenge statement exposes only the resulting
existence of a positive scalar `sigmaBar`.

The public exponents are fixed to `t = 1/8` and `s = 3/4`.  The constants
`C`, `alpha`, and `Cscale` are therefore chosen before the probability law
`S : Setup d`; in particular they do not depend on the law, on the ellipticity
bounds, or on exponent variables. -/
theorem homogenizationComparison_uniformEllipticity
    {d : ℕ} [NeZero d] :
    ∃ C alpha Cscale : ℝ,
      0 < C ∧ 0 < alpha ∧ 0 < Cscale ∧
      ∀ S : Setup d,
        ∃ sigmaBar : ℝ,
          0 < sigmaBar ∧
          ∃ X : CoeffField d → ℝ,
            S.IsMinimalScale X Cscale ∧
            ∀ᵐ a ∂S.P,
              ∀ (ha : AELocallyUniformlyEllipticField a)
                {m : ℕ} {g : Vec d → Vec d}
                (pair : ComparisonPair sigmaBar a ha m g),
                X a ≤ (3 : ℝ) ^ m →
                ForceSobolevRegularity (originCube d m) fixedComparisonS g →
                comparisonDefect sigmaBar fixedComparisonS pair ≤
                  C * ((3 : ℝ) ^ m / X a) ^ (-alpha) *
                    comparisonData sigmaBar fixedComparisonS pair := by
  obtain ⟨C, alpha, Cscale, hC, halpha, hCscale, hmain⟩ :=
    _root_.Homogenization.Book.MainResults.homogenizationComparison_uniformEllipticity
      (d := d)
  refine ⟨C, alpha, Cscale, hC, halpha, hCscale, ?_⟩
  intro S
  let Srepo : _root_.Homogenization.Book.MainResults.Setup d := toRepoSetup S
  let sigmaBar : ℝ :=
    _root_.Homogenization.Book.Ch05.Section57.barSigmaLimit Srepo.hP Srepo.hStruct
  have hsigma : 0 < sigmaBar := by
    dsimp [sigmaBar]
    exact Srepo.barSigmaLimit_pos
  obtain ⟨_sigmaBar, _hsigma, X, hX, hmainS⟩ := hmain Srepo
  refine ⟨sigmaBar, hsigma, X, ?_, ?_⟩
  · simpa [Srepo, toRepoSetup, Setup.IsMinimalScale,
      _root_.Homogenization.Book.MainResults.Setup.IsMinimalScale,
      Setup.thetaHat, Setup.uniformUpperBlockConst, Setup.uniformLowerInvBlockConst,
      _root_.Homogenization.Book.MainResults.Setup.thetaHat,
      _root_.Homogenization.Book.Ch05.Section57.mainResultsThetaHat,
      _root_.Homogenization.Book.Ch05.Section57.uniformUpperBlockConst,
      _root_.Homogenization.Book.Ch05.Section57.uniformLowerInvBlockConst,
      IndependentSums.IsBigO, _root_.Homogenization.IndependentSums.IsBigO,
      IndependentSums.IsBigOWith, _root_.Homogenization.IndependentSums.IsBigOWith,
      IndependentSums.upperTailEvent,
      _root_.Homogenization.IndependentSums.upperTailEvent,
      IndependentSums.gammaSigma, _root_.Homogenization.IndependentSums.gammaSigma] using hX
  · filter_upwards [hmainS] with a hmain_a
    intro ha m g pair hXm hg
    let haRepo :
        _root_.Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a :=
      toRepo_AELocallyUniformlyEllipticField ha
    let repoPair :
        Srepo.ComparisonPair a haRepo m g :=
      by
        simpa [Srepo, sigmaBar, toRepoSetup,
          _root_.Homogenization.Book.MainResults.Setup.ComparisonPair,
          _root_.Homogenization.Book.MainResults.Setup.homogenizedMatrix] using
          toRepoComparisonPair hsigma haRepo pair
    have hgRepo :
        _root_.Homogenization.Book.Ch03.ForceSobolevRegularity
          (_root_.Homogenization.Book.MainResults.originCube d m)
          _root_.Homogenization.Book.MainResults.fixedComparisonS g := by
      simpa [fixedComparisonS,
        _root_.Homogenization.Book.MainResults.fixedComparisonS] using
        toRepo_ForceSobolevRegularity hg
    have hstep := hmain_a haRepo repoPair hXm hgRepo
    have hdefect :
        Srepo.comparisonDefect
            _root_.Homogenization.Book.MainResults.fixedComparisonS repoPair =
          comparisonDefect sigmaBar fixedComparisonS pair := by
      simpa [repoPair, toRepoComparisonPair,
        _root_.Homogenization.Book.MainResults.Setup.comparisonDefect,
        _root_.Homogenization.Book.MainResults.Setup.homogenizedMatrix,
        Srepo, sigmaBar, fixedComparisonS,
        _root_.Homogenization.Book.MainResults.fixedComparisonS] using
        (comparisonDefect_toRepo (d := d) (sigmaBar := sigmaBar)
          (a := a) (ha := ha) (haRepo := haRepo) hsigma fixedComparisonS pair)
    have hdata :
        Srepo.comparisonData
            _root_.Homogenization.Book.MainResults.fixedComparisonS repoPair =
          comparisonData sigmaBar fixedComparisonS pair := by
      simpa [repoPair, toRepoComparisonPair,
        _root_.Homogenization.Book.MainResults.Setup.comparisonData,
        _root_.Homogenization.Book.MainResults.Setup.homogenizedMatrix,
        Srepo, sigmaBar, fixedComparisonS,
        _root_.Homogenization.Book.MainResults.fixedComparisonS] using
        (comparisonData_toRepo (d := d) (sigmaBar := sigmaBar)
          (a := a) (ha := ha) (haRepo := haRepo) fixedComparisonS pair)
    rw [hdefect, hdata] at hstep
    exact hstep

end

end StatementAudit
end Homogenization
