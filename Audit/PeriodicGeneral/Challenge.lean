import Mathlib

/-!
# Periodic homogenization for a general periodic coefficient field

This is a Mathlib-only comparator challenge for the deterministic periodic
specialization of the uniformly elliptic quenched comparison theorem.

The mathematical content is the following.  In every dimension `d ≥ 2`, there
are dimensional constants `C, α, Cscale > 0` such that every uniformly elliptic
coefficient field `a₀` which is

* periodic under all integer translations,
* invariant under signed coordinate changes, and
* equal to its own adjoint

has:

* a positive scalar homogenized coefficient `sigmaBar`, and
* a minimal scale `X ≥ 1` with the prescribed stretched-exponential tail under
  the Dirac point mass `δ_{a₀}`,

for which the heterogeneous and homogenized weak solutions on the origin cube
of sidelength `3^m` satisfy the quantitative `H⁻³ᐟ⁴` comparison estimate as soon
as `X ≤ 3^m`.

The coefficient law of this specialization is the Dirac point mass at `a₀`, so
the three symmetry assumptions are *pointwise identities of the field itself*,
not merely equalities in law.

Only definitions needed to read that assertion occur below.  In particular:

* all Sobolev definitions are specialized to the one exponent used by the
  theorem, namely `s = 3/4` and `p = 2`;
* the deterministic-medium assumptions are presented in one flat structure;
* the minimal-scale tail is written out rather than routed through a generic
  `IsBigO` wrapper.

The sole intentional `sorry` is the proof of the final theorem.
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

/-! ## 2. Coefficient fields and their observable σ-algebra -/

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

/-- The carrier σ-algebra, pinned as the pullback of the observable σ-algebra.

The bare function type `RawCoeffField d` deliberately carries no global
`MeasurableSpace` instance: Mathlib's product instance would also apply to it,
and the meaning of the statement below must not depend on which instance
wins. -/
instance instMeasurableSpaceCoefficientField (d : ℕ) :
    MeasurableSpace (CoefficientField d) :=
  MeasurableSpace.comap CoefficientField.toFun (observableFieldSigma d)

/-! ### Geometric actions on raw fields -/

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

/-! ## 4. Assumptions on the periodic medium -/

/-- Invariance of the field itself under every integer translation. -/
def IsPeriodic {d : ℕ} (a : RawCoeffField d) : Prop :=
  ∀ z : Fin d → ℤ, translateCoeffField (intVecToRealVec z) a = a

/-- Invariance of the field itself under every signed coordinate change. -/
def IsSignedCoordinateInvariant {d : ℕ} (a : RawCoeffField d) : Prop :=
  ∀ R : SignedPermutation d, rotateCoeffField R a = a

/-- The field is equal to its own pointwise transpose. -/
def IsAdjointInvariant {d : ℕ} (a : RawCoeffField d) : Prop :=
  adjointCoeffField a = a

/-- The ellipticity bounds `lam, Lam` hold almost everywhere on `Q`. -/
def EllipticOnCube {d : ℕ} (lam Lam : ℝ) (Q : TriadicCube d)
    (a : CoefficientField d) : Prop :=
  ∀ᵐ x ∂volumeOn Q.interior, IsEllipticMatrix lam Lam (a x)

/-- The same fixed ellipticity bounds hold almost everywhere on every
triadic cube. -/
def UniformlyEllipticRealization {d : ℕ} (lam Lam : ℝ)
    (a : CoefficientField d) : Prop :=
  ∀ Q : TriadicCube d, EllipticOnCube lam Lam Q a

/-- Every triadic cube carries *some* pair of ellipticity bounds. -/
def LocallyUniformlyElliptic {d : ℕ} (a : CoefficientField d) : Prop :=
  ∀ Q : TriadicCube d,
    ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧ EllipticOnCube lam Lam Q a

/-- All data describing the periodic coefficient field.  The structure is flat
so that a reader sees the complete list of hypotheses in one place. -/
structure Setup (d : ℕ) [NeZero d] where
  two_le_dim : 2 ≤ d
  a₀ : CoefficientField d
  periodic : IsPeriodic a₀.toFun
  signedCoordinateInvariant : IsSignedCoordinateInvariant a₀.toFun
  adjointInvariant : IsAdjointInvariant a₀.toFun
  lam : ℝ
  Lam : ℝ
  lam_pos : 0 < lam
  lam_le_Lam : lam ≤ Lam
  uniformlyElliptic : UniformlyEllipticRealization lam Lam a₀

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

/-- `X` is at least one and has the required `Gamma_d` tail under the Dirac
point mass at the periodic field. -/
structure IsMinimalScale (X : CoefficientField d → ℝ) (Cscale : ℝ) : Prop where
  one_le : ∀ a, 1 ≤ X a
  tail : ∀ ⦃t : ℝ⦄, 1 ≤ t →
    (Measure.dirac S.a₀).real {a | S.minimalScaleTailSize Cscale * t < |X a|} ≤
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

namespace PeriodicGeneral

/-- Fixed-exponent homogenization comparison for a deterministic periodic
coefficient field, stated for the Dirac law concentrated at that field.

The constants `C`, `alpha`, `Cscale` are chosen before the field and its
ellipticity bounds, hence depend only on `d`.  The estimate bounds the
comparison defect (a scale-normalized `H⁻³ᐟ⁴` distance between the
heterogeneous and homogenized flux/gradient pairs) by the energy data times the
algebraic rate `(3 ^ m / X a) ^ (-alpha)`, where `3 ^ m` is the cube sidelength
and `X a` the minimal scale. -/
theorem periodicGeneral_comparison
    {d : ℕ} [NeZero d] :
    ∃ C alpha Cscale : ℝ,
      0 < C ∧ 0 < alpha ∧ 0 < Cscale ∧
      ∀ S : Setup d,
        ∃ sigmaBar : ℝ,
          0 < sigmaBar ∧
          ∃ X : CoefficientField d → ℝ,
            S.IsMinimalScale X Cscale ∧
            ∀ᵐ a ∂Measure.dirac S.a₀,
              ∀ (_ha : LocallyUniformlyElliptic a)
                {m : ℕ} {g : Vec d → Vec d}
                (pair : ComparisonPair sigmaBar a (originCube d m) g),
                X a ≤ (3 : ℝ) ^ m →
                ForceInH34 (originCube d m) g →
                comparisonDefect pair ≤
                  C * ((3 : ℝ) ^ m / X a) ^ (-alpha) * comparisonData pair := by
  sorry

end PeriodicGeneral

end

end StatementAudit
end Homogenization
