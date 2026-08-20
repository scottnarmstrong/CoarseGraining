import Mathlib

/-!
# Statement-level audit vocabulary for the polynomial homogenization scale

This Mathlib-only file holds the statement vocabulary of the comparator
challenge `Audit/PolynomialScale/Challenge.lean`: the ambient vectors and
matrices, the honest coefficient-field carrier with its observable σ-algebra,
the geometric actions and law invariances, triadic cubes and volume averages,
the flat `Setup` of assumptions on the random medium, weak `H¹` and `H¹₀`, the
block formalism with the coarse-graining variational quantity `Mu`, and the
annealed coarse matrices together with the scalar contrast `thetaAtScale`.

Every declaration below is a **verbatim** copy of the corresponding
declaration of `Challenge.lean`; only the file header (the import and this
docstring) differs, and the final theorem — together with its section
header — is omitted.  Byte-identity of these bodies is what makes the theorem
statement in `Solution.lean` match the challenge statement, so the copy must
not be edited: any change to it is a change to the audited statement.

The file is deliberately **self-contained** and Mathlib-only: it imports
nothing from the repository.  That is not cosmetic.  The comparator compares
the whole dependency closure of the audited theorem constant by constant, and
a repository import in scope changes which instances the elaborator picks
inside the vocabulary — for instance the `Module ℝ (Fin d → ℝ)` instance
buried in `fderiv` inside `weakFDeriv`, hence in
`HasWeakPartialDerivativeOn`.  Elaborating the copy in a Mathlib-only
environment, identical to the challenge's, is what makes those constants
match.

The repository bridges live in `Audit/PolynomialScale/SolutionBridge.lean`,
which imports this file together with the repository; `Solution.lean` imports
that bridge module and states the audited theorem.
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

/-- The symmetric part of a possibly non-symmetric matrix. -/
noncomputable def symmPart {d : ℕ} (A : Mat d) : Mat d :=
  fun i j => (A i j + A j i) / 2

/-- The antisymmetric part of a possibly non-symmetric matrix. -/
noncomputable def skewPart {d : ℕ} (A : Mat d) : Mat d :=
  fun i j => (A i j - A j i) / 2

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

/-- The σ-algebra generated by observing the field only inside `U`. -/
def restrictionSigma {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace (CoefficientField d) :=
  MeasurableSpace.comap
    (fun a : CoefficientField d => restrictCoeffField U a.toFun)
    (observableFieldSigma d)

/-! ## 3. Triadic cubes and volume averages -/

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

end TriadicCube

/-- The triadic cube centered at the origin with sidelength `3 ^ m`. -/
def originCube (d : ℕ) (m : ℤ) : TriadicCube d :=
  { scale := m
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

/-- `Θ`-ellipticity of one realization: the quadratic form is bounded below by
`1` and the inverse quadratic form by `Θ⁻¹`, at almost every point of space. -/
def ThetaEllipticRealization {d : ℕ} (Θ : ℝ) (a : CoefficientField d) : Prop :=
  ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 Θ (a x)

/-- All data describing the random coefficient field.  The structure is flat
so that a reader sees the complete list of hypotheses in one place. -/
structure Setup (d : ℕ) [NeZero d] where
  Θ : ℝ
  one_le_theta : 1 ≤ Θ
  P : CoefficientLaw d
  isProbability : IsProbabilityMeasure P
  integerStationary : IntegerStationary P
  unitRange : UnitRangeDependent P
  signedCoordinateInvariant : SignedCoordinateInvariant P
  adjointInvariant : AdjointInvariant P
  thetaElliptic : ∀ᵐ a ∂P, ThetaEllipticRealization Θ a

/-! ## 5. Weak `H¹` and `H¹₀` -/

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

abbrev MemVectorL2On {d : ℕ} (U : Set (Vec d)) (f : Vec d → Vec d) : Prop :=
  MemLp f 2 (volumeOn U)

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

namespace PolynomialScale

/-! ## 6. Block states and the coarse-graining quantity `Mu` -/

/-- A pair of vector fields: a potential slot and a flux slot. -/
abbrev BlockVec (d : ℕ) := Vec d × Vec d

/-- The `2d` coordinates of a block vector. -/
abbrev BlockCoord (d : ℕ) := Sum (Fin d) (Fin d)

/-- A `2d × 2d` matrix, written as four `d × d` blocks. -/
structure BlockMat (d : ℕ) where
  upperLeft : Mat d
  upperRight : Mat d
  lowerLeft : Mat d
  lowerRight : Mat d

def blockVecDot {d : ℕ} (X Y : BlockVec d) : ℝ :=
  vecDot X.1 Y.1 + vecDot X.2 Y.2

def blockMatVecMul {d : ℕ} (A : BlockMat d) (X : BlockVec d) : BlockVec d :=
  ( matVecMul A.upperLeft X.1 + matVecMul A.upperRight X.2
  , matVecMul A.lowerLeft X.1 + matVecMul A.lowerRight X.2 )

def blockBasis {d : ℕ} : BlockCoord d → BlockVec d
  | Sum.inl i => (basisVec i, 0)
  | Sum.inr i => (0, basisVec i)

/-- The `2d × 2d` coefficient of the doubled variational problem, built from
the symmetric part `s` and the antisymmetric part `k` of `A`. -/
noncomputable def blockMatrixOfCoeff {d : ℕ} (A : Mat d) : BlockMat d :=
  let s := symmPart A
  let k := skewPart A
  let sInv := s⁻¹
  { upperLeft := s + k.transpose * sInv * k
    upperRight := -(k.transpose * sInv)
    lowerLeft := -(sInv * k)
    lowerRight := sInv }

noncomputable def blockCoeffField {d : ℕ} (a : RawCoeffField d) :
    Vec d → BlockMat d :=
  fun x => blockMatrixOfCoeff (a x)

/-- A candidate for the doubled variational problem: a potential field and a
flux field. -/
structure BlockState (d : ℕ) where
  potential : Vec d → Vec d
  flux : Vec d → Vec d

def BlockState.eval {d : ℕ} (X : BlockState d) (x : Vec d) : BlockVec d :=
  (X.potential x, X.flux x)

/-- `f` is the gradient of a weak `H¹₀` function on `U`. -/
def IsPotentialZeroTraceOn {d : ℕ} (U : Set (Vec d))
    (f : Vec d → Vec d) : Prop :=
  ∃ u : WeakH10 U, u.toWeakH1.grad = f

/-- `g` is divergence free on `U` with vanishing normal trace: it is
orthogonal to every weak `H¹` gradient. -/
def IsSolenoidalZeroNormalTraceOn {d : ℕ} (U : Set (Vec d))
    (g : Vec d → Vec d) : Prop :=
  ∀ φ : WeakH1 U,
    ∫ x in U, vecDot (g x) (φ.grad x) ∂volume = 0

/-- Block states admissible for the block parameter `p = (p₁, p₂)`: the
potential part has mean-`p₁` fluctuation in `H¹₀` and the flux part has
mean-`p₂` fluctuation which is solenoidal with zero normal trace. -/
def IsBlockMuAdmissible {d : ℕ} (U : Set (Vec d)) (p : BlockVec d)
    (X : BlockState d) : Prop :=
  MemVectorL2On U (fun x => X.potential x - p.1) ∧
    IsPotentialZeroTraceOn U (fun x => X.potential x - p.1) ∧
    MemVectorL2On U (fun x => X.flux x - p.2) ∧
    IsSolenoidalZeroNormalTraceOn U (fun x => X.flux x - p.2)

noncomputable def blockEnergyDensity {d : ℕ} (a : RawCoeffField d)
    (X : BlockState d) (x : Vec d) : ℝ :=
  (1 / 2 : ℝ) *
    blockVecDot (X.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x))

noncomputable def muValueSet {d : ℕ} (U : Set (Vec d)) (p : BlockVec d)
    (a : RawCoeffField d) : Set ℝ :=
  {m | ∃ X : BlockState d,
    IsBlockMuAdmissible U p X ∧ m = volumeAverage U (blockEnergyDensity a X)}

/-- The coarse-graining variational quantity: the infimum of the averaged
block energy over the admissible block states. -/
noncomputable def Mu {d : ℕ} (U : Set (Vec d)) (p : BlockVec d)
    (a : RawCoeffField d) : ℝ :=
  sInf (muValueSet U p a)

/-! ## 7. Coarse and annealed matrices, and the scalar contrast -/

/-- The `(α, β)` entry of the coarse block matrix, obtained by polarizing the
quantity `Mu` in its block parameter. -/
noncomputable def coarseBlockEntry {d : ℕ} (U : Set (Vec d))
    (a : RawCoeffField d) (α β : BlockCoord d) : ℝ :=
  if α = β then
    2 * Mu U (blockBasis α) a
  else
    Mu U (blockBasis α + blockBasis β) a - Mu U (blockBasis α) a -
      Mu U (blockBasis β) a

noncomputable def coarseBlockMatrix {d : ℕ} (U : Set (Vec d))
    (a : RawCoeffField d) : BlockMat d :=
  { upperLeft := fun i j => coarseBlockEntry U a (Sum.inl i) (Sum.inl j)
    upperRight := fun i j => coarseBlockEntry U a (Sum.inl i) (Sum.inr j)
    lowerLeft := fun i j => coarseBlockEntry U a (Sum.inr i) (Sum.inl j)
    lowerRight := fun i j => coarseBlockEntry U a (Sum.inr i) (Sum.inr j) }

/-- The entrywise expectation of the coarse block matrix under the law `P`. -/
noncomputable def annealedBlockMatrix {d : ℕ} (P : CoefficientLaw d)
    (U : Set (Vec d)) : BlockMat d :=
  { upperLeft := fun i j => ∫ a, (coarseBlockMatrix U a.toFun).upperLeft i j ∂P
    upperRight := fun i j => ∫ a, (coarseBlockMatrix U a.toFun).upperRight i j ∂P
    lowerLeft := fun i j => ∫ a, (coarseBlockMatrix U a.toFun).lowerLeft i j ∂P
    lowerRight := fun i j =>
      ∫ a, (coarseBlockMatrix U a.toFun).lowerRight i j ∂P }

/-- `σ*⁻¹`: the lower-right block of the annealed block matrix. -/
noncomputable def annealedSigmaStarInv {d : ℕ} (P : CoefficientLaw d)
    (U : Set (Vec d)) : Mat d :=
  (annealedBlockMatrix P U).lowerRight

/-- `σ*`: the inverse of the lower-right block. -/
noncomputable def annealedSigmaStar {d : ℕ} (P : CoefficientLaw d)
    (U : Set (Vec d)) : Mat d :=
  (annealedSigmaStarInv P U)⁻¹

/-- `σ*⁻¹κ`: minus the lower-left block of the annealed block matrix. -/
noncomputable def annealedSigmaStarInvKappaMean {d : ℕ}
    (P : CoefficientLaw d) (U : Set (Vec d)) : Mat d :=
  -((annealedBlockMatrix P U).lowerLeft)

/-- `κ`: the annealed drift block, `σ*` applied to `σ*⁻¹κ`. -/
noncomputable def annealedKappa {d : ℕ} (P : CoefficientLaw d)
    (U : Set (Vec d)) : Mat d :=
  annealedSigmaStar P U * annealedSigmaStarInvKappaMean P U

/-- `b`: the upper-left block of the annealed block matrix. -/
noncomputable def annealedB {d : ℕ} (P : CoefficientLaw d)
    (U : Set (Vec d)) : Mat d :=
  (annealedBlockMatrix P U).upperLeft

/-- `σ = b - κᵀ σ*⁻¹ κ`: the annealed conductivity matrix. -/
noncomputable def annealedSigma {d : ℕ} (P : CoefficientLaw d)
    (U : Set (Vec d)) : Mat d :=
  annealedB P U
    - (annealedKappa P U).transpose * annealedSigmaStarInv P U *
      annealedKappa P U

noncomputable def annealedSigmaAtScale {d : ℕ}
    (P : CoefficientLaw d) (n : ℤ) : Mat d :=
  annealedSigma P (originCube d n).set

noncomputable def annealedSigmaStarAtScale {d : ℕ}
    (P : CoefficientLaw d) (n : ℤ) : Mat d :=
  annealedSigmaStar P (originCube d n).set

/-- The scalar contrast at scale `n`.

Under the structural hypotheses both annealed matrices are scalar multiples of
the identity, and a scalar matrix is determined by its `(0,0)` entry, so this
total function is the ratio of those two scalars. -/
noncomputable def thetaAtScale {d : ℕ} [NeZero d] (P : CoefficientLaw d)
    (n : ℤ) : ℝ :=
  annealedSigmaAtScale P n 0 0 * (annealedSigmaStarAtScale P n 0 0)⁻¹


end PolynomialScale

end

end StatementAudit
end Homogenization
