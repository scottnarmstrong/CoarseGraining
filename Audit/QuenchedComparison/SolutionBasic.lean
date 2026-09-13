import Mathlib

/-!
# Statement-level audit vocabulary for the quenched comparison challenge

This file is a **verbatim copy** of the definitional vocabulary of
`Audit/QuenchedComparison/Challenge.lean` (everything in that file except the
final theorem), reproduced in the same namespace `Homogenization.StatementAudit`
so that the solution's theorem statement is byte-identical to the challenge's.

Only the file header differs from the challenge: the docstring above, and
nothing else.  In particular this file imports **only Mathlib**, exactly like
the challenge, so that every vocabulary constant elaborates in an environment
identical to the challenge's and comes out with the same instance paths (for
example the `Module ℝ (Vec d)` occurring inside `fderiv` in `weakFDeriv`).
Importing the repository here would silently change those instance paths and
make the constants differ from the challenge's even though the source text is
identical.  Nothing between `namespace Homogenization` and the final `end`s is
changed.

`Solution.lean` imports this file *and* the repository, adds the private
bridges to the repository theorem, and states and proves the audited theorem.
Because imports cannot retroactively re-elaborate the constants of an already
compiled module, the vocabulary below stays challenge-identical.
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
all compactly supported bounded entry integrals. -/
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

/-! ### Geometric actions on raw fields -/

noncomputable def restrictCoeffField {d : ℕ} (U : Set (Vec d))
    (a : RawCoeffField d) : RawCoeffField d := by
  classical
  exact Set.indicator U a

def translateCoeffField {d : ℕ} (z : Vec d)
    (a : RawCoeffField d) : RawCoeffField d :=
  fun x => a (fun i => x i + z i)

def intVecToRealVec {d : ℕ} (z : Fin d → ℤ) : Vec d :=
  fun i => (z i : ℝ)

/-- One of the two signs `+1` and `-1`. -/
abbrev Sign := {r : ℝ // r = 1 ∨ r = -1}

/-- A permutation of the coordinate axes, followed by independent sign flips. -/
structure SignedPermutation (d : ℕ) where
  perm : Equiv.Perm (Fin d)
  axisSign : Fin d → Sign

namespace SignedPermutation

def matrix {d : ℕ} (R : SignedPermutation d) : Mat d :=
  fun i j => if i = R.perm j then (R.axisSign j : ℝ) else 0

end SignedPermutation

def rotateCoeffField {d : ℕ} (R : SignedPermutation d)
    (a : RawCoeffField d) : RawCoeffField d :=
  fun x => (R.matrix.transpose) * (a (matVecMul R.matrix x)) * R.matrix

def adjointCoeffField {d : ℕ} (a : RawCoeffField d) : RawCoeffField d :=
  fun x => (a x).transpose

/-! ### Equality in distribution and restrictions -/

/-- Observable distribution of the transformed raw field `T a`.

The σ-algebra on raw fields is pinned to `observableFieldSigma d` in the type
itself.  The bare function type `RawCoeffField d` deliberately carries no
global `MeasurableSpace` instance: Mathlib's product instance would also apply
to it, and the meaning of the invariance assumptions below must not depend on
which instance wins. -/
noncomputable def rawLawAfter {d : ℕ} (P : CoefficientLaw d)
    (T : RawCoeffField d → RawCoeffField d) :
    @Measure (RawCoeffField d) (observableFieldSigma d) :=
  letI : MeasurableSpace (RawCoeffField d) := observableFieldSigma d
  Measure.map (fun a : CoefficientField d => T a.toFun) P

/-- `T a` has the same observable law as `a`. -/
def LawInvariantUnder {d : ℕ} (P : CoefficientLaw d)
    (T : RawCoeffField d → RawCoeffField d) : Prop :=
  rawLawAfter P T = rawLawAfter P id

set_option warn.classDefReducibility false in
/-- The σ-algebra generated by observing the field only inside `U`. -/
def restrictionSigma {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace (CoefficientField d) :=
  MeasurableSpace.comap
    (fun a : CoefficientField d => restrictCoeffField U a.toFun)
    (observableFieldSigma d)

/-! ## 3. Triadic cubes and normalized averages -/

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

/-! ## 4. Assumptions on the random medium -/

/-- The restrictions to `U` and `V` are independent whenever the sets are at
least unit distance apart. -/
def UnitSeparated {d : ℕ} (U V : Set (Vec d)) : Prop :=
  ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V → 1 ≤ dist x y

def IntegerStationary {d : ℕ} (P : CoefficientLaw d) : Prop :=
  ∀ z : Fin d → ℤ,
    LawInvariantUnder P (translateCoeffField (intVecToRealVec z))

def UnitRangeDependent {d : ℕ} (P : CoefficientLaw d) : Prop :=
  ∀ (U V : Set (Vec d)), MeasurableSet U → MeasurableSet V →
    UnitSeparated U V →
      ProbabilityTheory.Indep (restrictionSigma U) (restrictionSigma V) P

def SignedCoordinateInvariant {d : ℕ} (P : CoefficientLaw d) : Prop :=
  ∀ R : SignedPermutation d, LawInvariantUnder P (rotateCoeffField R)

def AdjointInvariant {d : ℕ} (P : CoefficientLaw d) : Prop :=
  LawInvariantUnder P adjointCoeffField

/-- The same fixed ellipticity bounds hold almost everywhere on every
triadic cube. -/
def UniformlyEllipticRealization {d : ℕ} (lam Lam : ℝ)
    (a : CoefficientField d) : Prop :=
  ∀ Q : TriadicCube d,
    ∀ᵐ x ∂volumeOn Q.interior, IsEllipticMatrix lam Lam (a x)

/-- All data describing the random coefficient field.  The structure is flat
so that a reader sees the complete list of hypotheses in one place. -/
structure Setup (d : ℕ) [NeZero d] where
  two_le_dim : 2 ≤ d
  P : CoefficientLaw d
  isProbability : IsProbabilityMeasure P
  integerStationary : IntegerStationary P
  unitRange : UnitRangeDependent P
  signedCoordinateInvariant : SignedCoordinateInvariant P
  adjointInvariant : AdjointInvariant P
  lam : ℝ
  Lam : ℝ
  lam_pos : 0 < lam
  lam_le_Lam : lam ≤ Lam
  uniformlyElliptic : ∀ᵐ a ∂P, UniformlyEllipticRealization lam Lam a

namespace Setup

variable {d : ℕ} [NeZero d] (S : Setup d)

noncomputable def coarseUpperBound : ℝ :=
  4 * (Fintype.card (Fin d) : ℝ) * S.lam⁻¹ * S.Lam ^ (2 : ℕ)

noncomputable def coarseInverseLowerBound : ℝ :=
  4 * (Fintype.card (Fin d) : ℝ) * S.lam⁻¹

/-- The deterministic coarse ellipticity size entering the tail estimate. -/
noncomputable def thetaHat : ℝ :=
  1 + S.coarseInverseLowerBound * S.coarseUpperBound +
    S.coarseUpperBound * S.coarseInverseLowerBound

noncomputable def minimalScaleTailSize (Cscale : ℝ) : ℝ :=
  Real.exp (Cscale * (Real.log (2 + S.thetaHat)) ^ (2 : ℕ))

/-- `X` is at least one and has the required `Gamma_d` tail. -/
structure IsMinimalScale (X : CoefficientField d → ℝ) (Cscale : ℝ) : Prop where
  one_le : ∀ a, 1 ≤ X a
  tail : ∀ ⦃t : ℝ⦄, 1 ≤ t →
    S.P.real {a | S.minimalScaleTailSize Cscale * t < |X a|} ≤
      (Real.exp (t ^ (d : ℝ)))⁻¹

end Setup

/-! ## 5. Weak `H¹` solutions -/

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

/-! ## 6. The fixed `H^{3/4}` and `H^{-3/4}` quantities -/

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

/-! ## 7. Error, data size, and the theorem -/

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
