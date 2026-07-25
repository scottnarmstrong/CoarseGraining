import Mathlib

/-!
# Mathlib-only challenge: the checkerboard homogenization-scale corollary

This file is the comparator challenge surface for the Bernoulli-checkerboard
instantiation of the unconditional homogenization-scale capstone
`Homogenization.homogenizationScale_polynomial_of_unitRange`
(`Homogenization/HighContrast/Scale/Final.lean`, applied to the checkerboard
law of `Homogenization/Examples/RandomCheckerboard/CarrierLaw.lean`).

It imports only Mathlib.  The theorem asserts: for every dimension `d > 2`
(the explicit hypothesis `hd : 3 ≤ d`) there are dimensional constants
`Cscale, Ctriadic, alpha > 0` such that for every `1 ≤ lam ≤ Lam` and every
coin parameter `p ≤ 1`, the Bernoulli checkerboard law with conductances
`lam`, `Lam` satisfies the homogenization-scale contrast decay:

* the scalar contrast decays geometrically from an entry scale `N₀`,
  `θ_{N₀+n} - 1 ≤ 3^(-alpha·n)`;
* the entry scale is logarithmic in the contrast, `N₀ ≤ Cscale · log(2 + Lam)`;
* the physical entry scale is polynomial, `3^{N₀} ≤ (2 + Lam)^Ctriadic`.

The capstone's ellipticity parameter is instantiated at `Θ = Lam`: every
checkerboard realization takes the scalar values `lam` or `Lam` cellwise, so
it lies pointwise in the quadratic-form ellipticity class
`IsEllipticMatrix 1 Lam` (coercivity `∀ ξ, |ξ|² ≤ ξ · A ξ` together with the
inverse quadratic-form bound `∀ ξ, Lam⁻¹ |ξ|² ≤ ξ · A⁻¹ ξ`; the class is
stated for general non-symmetric matrices, and no symmetric-ordering phrasing
appears anywhere).  All the capstone's law hypotheses — the probability
instance, the law carrier, the structural law (stationarity, unit-range
dependence, isotropy, adjoint invariance), and the `Θ`-ellipticity class
membership — are discharged by the checkerboard construction, so none of them
appears in the statement: the bounds are unconditional in the parameters, and
the triadic bound `3^{N₀} ≤ (2 + Lam)^Ctriadic` exhibits the entry scale as an
explicit algebraic (polynomial) function of the contrast `Lam`.

The scalar contrast `thetaAtScale P n` is defined here as the `(0,0)`-entry
ratio of the annealed conductivity matrices
`annealedSigmaAtScale P n · (annealedSigmaStarAtScale P n)⁻¹`, built by
polarization from the coarse-graining variational quantity `Mu` (an infimum
of averaged block energies over admissible potential/flux block states).
Under the structural hypotheses both annealed matrices are scalar multiples
of the identity, so this entry ratio agrees with the repository's scalar
contrast selector.

The definitions below are statement-level copies of the objects needed to
state this corollary.  The main source correspondences are:

* ambient fields and ellipticity: `Homogenization/Ambient/CoefficientField.lean`
  and `Homogenization/CoarseGraining/ThetaEllipticity.lean`;
* the regular-fields carrier `RegCoeffField` and its σ-algebra:
  `Homogenization/Probability/RegCoeffField.lean` and
  `Homogenization/Probability/RegCoeffField/Sigma.lean`;
* cubes: `Homogenization/Geometry/TriadicCube.lean`;
* Sobolev objects: `Homogenization/Sobolev/*`;
* block formalism and `Mu`: `Homogenization/Ambient/{Basic,BlockMatrix}.lean`,
  `Homogenization/CoarseGraining/BlockFormalism/{Structures,Properties}.lean`,
  and `Homogenization/CoarseGraining/Definitions.lean`;
* annealed coarse matrices and the contrast:
  `Homogenization/Book/Ch04/AnnealedDefinitions.lean` and
  `Homogenization/Book/Ch05/Definitions.lean`;
* the Bernoulli checkerboard law:
  `Homogenization/Examples/RandomCheckerboard/Basic.lean` and
  `Homogenization/Examples/RandomCheckerboard/CarrierLaw.lean`;
* the instantiated theorem surface:
  `Homogenization/HighContrast/Scale/Final.lean` applied in
  `Homogenization/Examples/RandomCheckerboard/CarrierLaw.lean`.

The only proof omitted in this challenge file is the final theorem proof.
-/

namespace Homogenization
namespace StatementAudit

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section
/-! ## Ambient fields and matrices -/

abbrev Vec (d : ℕ) := Fin d → ℝ

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

instance instMeasurableSpaceMat (d : ℕ) : MeasurableSpace (Mat d) := by
  exact @MeasurableSpace.pi (Fin d) (fun _ => Fin d → ℝ)
    (fun _ => @MeasurableSpace.pi (Fin d) (fun _ => ℝ)
      (fun _ => (RCLike.measurableSpace : MeasurableSpace ℝ)))

abbrev CoeffField (d : ℕ) := Vec d → Mat d

def pointwiseCoeffFieldMeasurableSpace (d : ℕ) : MeasurableSpace (CoeffField d) := by
  exact @MeasurableSpace.pi (Vec d) (fun _ => Mat d)
    (fun _ => instMeasurableSpaceMat d)

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

/-! ## The regular-fields carrier

Following the carrier redesign, the probability layer lives on the carrier of
*honest* coefficient fields: entrywise Borel-measurable, locally integrable
maps `Vec d → Mat d`.  On the carrier, entrywise regularity is free by type.
The carrier σ-algebra is the join of the pointwise (product) σ-algebra and the
σ-algebra generated by the linear entry integrals against bounded, measurable,
compactly supported probes.  These are statement-level copies of
`Homogenization/Probability/RegCoeffField.lean` and
`Homogenization/Probability/RegCoeffField/Sigma.lean`. -/

structure RegCoeffField (d : ℕ) where
  toFun : Vec d → Mat d
  entry_measurable : ∀ i j : Fin d, Measurable (fun x : Vec d => toFun x i j)
  entry_locInt : ∀ i j : Fin d,
    MeasureTheory.LocallyIntegrable (fun x : Vec d => toFun x i j)
      MeasureTheory.volume

instance {d : ℕ} : CoeFun (RegCoeffField d) (fun _ => Vec d → Mat d) :=
  ⟨RegCoeffField.toFun⟩

structure IsProbeR {d : ℕ} (φ : Vec d → ℝ) : Prop where
  measurable : Measurable φ
  bounded : ∃ C : ℝ, ∀ x, |φ x| ≤ C
  hasCompactSupport : HasCompactSupport φ

noncomputable def entryTestR {d : ℕ} (i j : Fin d) (φ : Vec d → ℝ)
    (a : RegCoeffField d) : ℝ :=
  ∫ x, a.toFun x i j * φ x ∂MeasureTheory.volume

def pointwiseSigmaR (d : ℕ) : MeasurableSpace (RegCoeffField d) :=
  MeasurableSpace.comap RegCoeffField.toFun (pointwiseCoeffFieldMeasurableSpace d)

def entryTestSigmaR (d : ℕ) : MeasurableSpace (RegCoeffField d) :=
  MeasurableSpace.generateFrom
    {s | ∃ (i j : Fin d) (φ : Vec d → ℝ), IsProbeR φ ∧
      ∃ t : Set ℝ, MeasurableSet t ∧ s = entryTestR i j φ ⁻¹' t}

instance instMeasurableSpaceRegCoeffField (d : ℕ) :
    MeasurableSpace (RegCoeffField d) :=
  pointwiseSigmaR d ⊔ entryTestSigmaR d

/-- A coefficient law on the carrier (mirrors `Book.Ch04.CoeffLaw`). -/
abbrev CoeffLaw (d : ℕ) := Measure (RegCoeffField d)

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

/-- The triadic cube centered at the origin with integer scale `m`. -/
def triadicOriginCube (d : ℕ) (m : ℤ) : TriadicCube d :=
  { scale := m
    index := 0 }

noncomputable def volumeAverage {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ) : ℝ :=
  (MeasureTheory.volume U).toReal⁻¹ * ∫ x in U, f x ∂MeasureTheory.volume

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

namespace PolynomialScale

/-! ## Block formalism, `Mu`, coarse/annealed matrices, and the contrast
selector (statement-level copies of
`Homogenization/Ambient/{Basic,BlockMatrix}.lean`,
`Homogenization/CoarseGraining/BlockFormalism/{Structures,Properties}.lean`,
`Homogenization/CoarseGraining/Definitions.lean`,
`Homogenization/Book/Ch04/AnnealedDefinitions.lean`, and
`Homogenization/Book/Ch05/Definitions.lean`). -/

/-! ### Block vectors and block matrices -/

abbrev BlockVec (d : ℕ) := Vec d × Vec d

abbrev BlockCoord (d : ℕ) := Sum (Fin d) (Fin d)

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

noncomputable def skewPart {d : ℕ} (A : Mat d) : Mat d :=
  fun i j => (A i j - A j i) / 2

def blockBasis {d : ℕ} : BlockCoord d → BlockVec d
  | Sum.inl i => (Pi.single i 1, 0)
  | Sum.inr i => (0, Pi.single i 1)

/-! ### L² membership and the potential/solenoidal trace predicates -/

noncomputable abbrev MemVectorL2 {d : ℕ} (U : Set (Vec d))
    (f : Vec d → Vec d) : Prop :=
  MemLp f 2 (volumeMeasureOn U)

def IsPotentialZeroTraceOn {d : ℕ} (U : Set (Vec d)) (f : Vec d → Vec d) : Prop :=
  ∃ u : H10Function U, u.toH1Function.grad = f

noncomputable def IsSolenoidalZeroNormalTraceOn {d : ℕ} (U : Set (Vec d))
    (g : Vec d → Vec d) : Prop :=
  ∀ φ : H1Function U,
    ∫ x in U, vecDot (g x) (φ.grad x) ∂MeasureTheory.volume = 0

/-! ### Block states, the doubled coefficient, and the energy density -/

structure BlockState (d : ℕ) where
  potential : Vec d → Vec d
  flux : Vec d → Vec d

def BlockState.eval {d : ℕ} (X : BlockState d) (x : Vec d) : BlockVec d :=
  (X.potential x, X.flux x)

noncomputable def blockMatrixOfCoeff {d : ℕ} (A : Mat d) : BlockMat d :=
  let s := symmPart A
  let k := skewPart A
  let sInv := s⁻¹
  { upperLeft := s + (matTranspose k) * sInv * k
    upperRight := -((matTranspose k) * sInv)
    lowerLeft := -(sInv * k)
    lowerRight := sInv }

noncomputable def blockCoeffField {d : ℕ} (a : CoeffField d) : Vec d → BlockMat d :=
  fun x => blockMatrixOfCoeff (a x)

def IsBlockMuAdmissible {d : ℕ} (U : Set (Vec d)) (P : BlockVec d)
    (X : BlockState d) : Prop :=
  MemVectorL2 U (fun x => X.potential x - P.1) ∧
    IsPotentialZeroTraceOn U (fun x => X.potential x - P.1) ∧
      MemVectorL2 U (fun x => X.flux x - P.2) ∧
        IsSolenoidalZeroNormalTraceOn U (fun x => X.flux x - P.2)

noncomputable def blockEnergyDensity {d : ℕ} (a : CoeffField d)
    (X : BlockState d) (x : Vec d) : ℝ :=
  (1 / 2 : ℝ) * blockVecDot (X.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x))

/-! ### The coarse-graining variational quantity `Mu` -/

noncomputable def muValueSet {d : ℕ} (U : Set (Vec d)) (P : BlockVec d)
    (a : CoeffField d) : Set ℝ :=
  { m | ∃ X : BlockState d,
      IsBlockMuAdmissible U P X ∧ m = volumeAverage U (blockEnergyDensity a X) }

noncomputable def Mu {d : ℕ} (U : Set (Vec d)) (P : BlockVec d)
    (a : CoeffField d) : ℝ :=
  sInf (muValueSet U P a)

/-! ### The coarse block matrix (polarization of `Mu`) -/

noncomputable def coarseBlockEntry {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (α β : BlockCoord d) : ℝ :=
  if _h : α = β then
    2 * Mu U (blockBasis α) a
  else
    Mu U (blockBasis α + blockBasis β) a - Mu U (blockBasis α) a - Mu U (blockBasis β) a

noncomputable def coarseBlockMatrix {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) :
    BlockMat d :=
  { upperLeft := fun i j => coarseBlockEntry U a (Sum.inl i) (Sum.inl j)
    upperRight := fun i j => coarseBlockEntry U a (Sum.inl i) (Sum.inr j)
    lowerLeft := fun i j => coarseBlockEntry U a (Sum.inr i) (Sum.inl j)
    lowerRight := fun i j => coarseBlockEntry U a (Sum.inr i) (Sum.inr j) }

/-! ### Annealed coarse matrices at scale -/

noncomputable def annealedBlockMatrix {d : ℕ} (P : CoeffLaw d)
    (U : Set (Vec d)) : BlockMat d :=
  { upperLeft := fun i j => ∫ a, (coarseBlockMatrix U a.toFun).upperLeft i j ∂P
    upperRight := fun i j => ∫ a, (coarseBlockMatrix U a.toFun).upperRight i j ∂P
    lowerLeft := fun i j => ∫ a, (coarseBlockMatrix U a.toFun).lowerLeft i j ∂P
    lowerRight := fun i j => ∫ a, (coarseBlockMatrix U a.toFun).lowerRight i j ∂P }

noncomputable def annealedSigmaStarInv {d : ℕ} (P : CoeffLaw d)
    (U : Set (Vec d)) : Mat d :=
  (annealedBlockMatrix P U).lowerRight

noncomputable def annealedSigmaStar {d : ℕ} (P : CoeffLaw d)
    (U : Set (Vec d)) : Mat d :=
  (annealedSigmaStarInv P U)⁻¹

noncomputable def annealedSigmaStarInvKappaMean {d : ℕ}
    (P : CoeffLaw d) (U : Set (Vec d)) : Mat d :=
  -((annealedBlockMatrix P U).lowerLeft)

noncomputable def annealedKappa {d : ℕ} (P : CoeffLaw d)
    (U : Set (Vec d)) : Mat d :=
  annealedSigmaStar P U * annealedSigmaStarInvKappaMean P U

noncomputable def annealedB {d : ℕ} (P : CoeffLaw d)
    (U : Set (Vec d)) : Mat d :=
  (annealedBlockMatrix P U).upperLeft

noncomputable def annealedSigma {d : ℕ} (P : CoeffLaw d)
    (U : Set (Vec d)) : Mat d :=
  annealedB P U
    - matTranspose (annealedKappa P U) * annealedSigmaStarInv P U * annealedKappa P U

noncomputable def annealedSigmaAtScale {d : ℕ}
    (P : CoeffLaw d) (n : ℤ) : Mat d :=
  annealedSigma P (cubeSet (triadicOriginCube d n))

noncomputable def annealedSigmaStarAtScale {d : ℕ}
    (P : CoeffLaw d) (n : ℤ) : Mat d :=
  annealedSigmaStar P (cubeSet (triadicOriginCube d n))

/-! ### The total scalar contrast selector

The repository's `Book.Ch05.thetaAtScale hP hStruct n` selects, via
`Classical.choice`/`Classical.choose` on the scalarization witnesses built from
the structural law, the scalars `barSigma`, `barSigmaStar` with
`annealedSigmaAtScale P n = barSigma • 1` and
`annealedSigmaStarAtScale P n = barSigmaStar • 1`, and returns
`barSigma * barSigmaStar⁻¹`.  Both records are `Prop`s and are consumed only
through `Classical.choice` on `Prop`-valued nonemptiness, so by proof
irrelevance the value depends on `(P, n)` alone.  Since scalar matrices are
determined by their `(0,0)` entry (`NeZero d`), the Mathlib-only mirror is the
*total* function below; under the structural hypotheses the Solution bridges it
to the repository selector. -/

noncomputable def thetaAtScale {d : ℕ} [NeZero d] (P : CoeffLaw d) (n : ℤ) : ℝ :=
  annealedSigmaAtScale P n 0 0 * (annealedSigmaStarAtScale P n 0 0)⁻¹

/-! ### The `Θ`-ellipticity class (quadratic-form form ONLY, per directive) -/

def ThetaEllipticLaw {d : ℕ} (Θ : ℝ) (P : CoeffLaw d) : Prop :=
  ∀ᵐ a ∂P, ∀ᵐ x ∂(MeasureTheory.volume : Measure (Vec d)),
    IsEllipticMatrix 1 Θ (a.toFun x)

end PolynomialScale

/-! ## Bernoulli checkerboard specialization -/

namespace RandomCheckerboard

section

attribute [local instance] Classical.propDecidable

abbrev Lattice (d : ℕ) :=
  Fin d → ℤ

abbrev Sample (d : ℕ) :=
  Lattice d → Bool

def openUnitCell {d : ℕ} (z : Lattice d) : Set (Vec d) :=
  {x | ∀ i : Fin d, |x i - (z i : ℝ)| < (1 / 2 : ℝ)}

def coinConductance (lam Lam : ℝ) (b : Bool) : ℝ :=
  if b then lam else Lam

def scalarAt {d : ℕ} (lam Lam : ℝ) (ω : Sample d) (x : Vec d) : ℝ :=
  if h : ∃ z : Lattice d, x ∈ openUnitCell z then
    coinConductance lam Lam (ω (Classical.choose h))
  else
    lam

def coeffField {d : ℕ} (lam Lam : ℝ) (ω : Sample d) : CoeffField d :=
  fun x => scalarMatrix (d := d) (scalarAt lam Lam ω x)

theorem measurableSet_openUnitCell {d : ℕ} (z : Lattice d) :
    MeasurableSet (openUnitCell z : Set (Vec d)) := by
  classical
  have hopen : IsOpen (openUnitCell z : Set (Vec d)) := by
    unfold openUnitCell
    have hset :
        {x : Vec d | ∀ i : Fin d, |x i - (z i : ℝ)| < (1 / 2 : ℝ)} =
          ⋂ i : Fin d, {x : Vec d | |x i - (z i : ℝ)| < (1 / 2 : ℝ)} := by
      ext x
      simp
    rw [hset]
    refine isOpen_iInter_of_finite fun i : Fin d => ?_
    have hleft : Continuous fun x : Vec d => |x i - (z i : ℝ)| :=
      ((continuous_apply i).sub continuous_const).abs
    have hright : Continuous fun _ : Vec d => (1 / 2 : ℝ) :=
      continuous_const
    exact isOpen_lt hleft hright
  exact hopen.measurableSet

theorem openUnitCell_unique {d : ℕ} {x : Vec d} {z w : Lattice d}
    (hz : x ∈ openUnitCell z) (hw : x ∈ openUnitCell w) :
    z = w := by
  funext i
  by_contra hne
  have hzw_int : (1 : ℤ) ≤ |z i - w i| :=
    Int.one_le_abs (sub_ne_zero.mpr hne)
  have hzw : (1 : ℝ) ≤ |(z i : ℝ) - (w i : ℝ)| := by
    rw [← Int.cast_sub, ← Int.cast_abs]
    exact_mod_cast hzw_int
  have hz_i := hz i
  have hw_i := hw i
  have hsplit :
      (z i : ℝ) - (w i : ℝ) =
        - (x i - (z i : ℝ)) + (x i - (w i : ℝ)) := by ring
  have htriangle :
      |(z i : ℝ) - (w i : ℝ)| <
        (1 / 2 : ℝ) + (1 / 2 : ℝ) := by
    calc
      |(z i : ℝ) - (w i : ℝ)|
          = |- (x i - (z i : ℝ)) + (x i - (w i : ℝ))| := by rw [hsplit]
      _ ≤ |-(x i - (z i : ℝ))| + |x i - (w i : ℝ)| := abs_add_le _ _
      _ = |x i - (z i : ℝ)| + |x i - (w i : ℝ)| := by rw [abs_neg]
      _ < (1 / 2 : ℝ) + (1 / 2 : ℝ) := add_lt_add hz_i hw_i
  norm_num at htriangle
  linarith

theorem scalarAt_of_mem_openUnitCell {d : ℕ} {lam Lam : ℝ}
    {ω : Sample d} {x : Vec d} {z : Lattice d}
    (hz : x ∈ openUnitCell z) :
    scalarAt lam Lam ω x = coinConductance lam Lam (ω z) := by
  classical
  have h : ∃ w : Lattice d, x ∈ openUnitCell w := ⟨z, hz⟩
  rw [scalarAt, dif_pos h]
  congr 1
  exact congrArg ω (openUnitCell_unique (Classical.choose_spec h) hz)

theorem scalarAt_of_not_mem_any_openUnitCell {d : ℕ} {lam Lam : ℝ}
    {ω : Sample d} {x : Vec d}
    (hx : ¬ ∃ z : Lattice d, x ∈ openUnitCell z) :
    scalarAt lam Lam ω x = lam := by
  classical
  rw [scalarAt, dif_neg hx]

/-- The region where the checkerboard scalar takes the upper value `Lam`. -/
def upperConductanceRegion {d : ℕ} (ω : Sample d) : Set (Vec d) :=
  ⋃ z : {z : Lattice d // ω z = false}, openUnitCell z.1

theorem measurableSet_upperConductanceRegion {d : ℕ} (ω : Sample d) :
    MeasurableSet (upperConductanceRegion ω : Set (Vec d)) := by
  classical
  unfold upperConductanceRegion
  exact MeasurableSet.iUnion fun z => measurableSet_openUnitCell z.1

theorem scalarAt_eq_if_upperConductanceRegion {d : ℕ} {lam Lam : ℝ}
    {ω : Sample d} {x : Vec d} :
    scalarAt lam Lam ω x =
      if x ∈ upperConductanceRegion ω then Lam else lam := by
  classical
  by_cases hxUpper : x ∈ upperConductanceRegion ω
  · rcases Set.mem_iUnion.mp hxUpper with ⟨z, hxz⟩
    have hcell : x ∈ openUnitCell z.1 := hxz
    have hz : ω z.1 = false := z.2
    simp [scalarAt_of_mem_openUnitCell (lam := lam) (Lam := Lam) (ω := ω) hcell,
      coinConductance, hz, hxUpper]
  · by_cases hx : ∃ z : Lattice d, x ∈ openUnitCell z
    · let z : Lattice d := Classical.choose hx
      have hzcell : x ∈ openUnitCell z := Classical.choose_spec hx
      have hztrue : ω z = true := by
        cases hωz : ω z
        · exact False.elim (hxUpper (Set.mem_iUnion.2 ⟨⟨z, hωz⟩, hzcell⟩))
        · rfl
      simp [scalarAt_of_mem_openUnitCell (lam := lam) (Lam := Lam) (ω := ω) hzcell,
        coinConductance, hztrue, hxUpper]
    · simp [scalarAt_of_not_mem_any_openUnitCell (lam := lam) (Lam := Lam) (ω := ω) hx,
        hxUpper]

theorem measurable_scalarAt_spatial {d : ℕ} {lam Lam : ℝ} (ω : Sample d) :
    Measurable (fun x : Vec d => scalarAt lam Lam ω x) := by
  classical
  have hpiece :
      Measurable
        ((upperConductanceRegion ω).piecewise
          (fun _ : Vec d => Lam) (fun _ : Vec d => lam)) :=
    Measurable.piecewise (measurableSet_upperConductanceRegion ω)
      measurable_const measurable_const
  convert hpiece using 1
  funext x
  simp [Set.piecewise, scalarAt_eq_if_upperConductanceRegion]

theorem scalarAt_eq_lam_or_Lam {d : ℕ} {lam Lam : ℝ} (ω : Sample d) (x : Vec d) :
    scalarAt lam Lam ω x = lam ∨ scalarAt lam Lam ω x = Lam := by
  rw [scalarAt_eq_if_upperConductanceRegion]
  by_cases hx : x ∈ upperConductanceRegion ω <;> simp [hx]

theorem abs_scalarAt_le {d : ℕ} {lam Lam : ℝ} (ω : Sample d) (x : Vec d) :
    |scalarAt lam Lam ω x| ≤ max |lam| |Lam| := by
  rcases scalarAt_eq_lam_or_Lam (lam := lam) (Lam := Lam) ω x with h | h
  · rw [h]; exact le_max_left _ _
  · rw [h]; exact le_max_right _ _

/-- A bounded measurable scalar field is locally integrable. -/
theorem locallyIntegrable_of_bounded_measurable {d : ℕ} {f : Vec d → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    MeasureTheory.LocallyIntegrable f MeasureTheory.volume := by
  rw [MeasureTheory.locallyIntegrable_iff]
  intro k hk
  refine MeasureTheory.Measure.integrableOn_of_bounded (hk.measure_lt_top).ne
    hf.aestronglyMeasurable (M := C) ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using hC x

/-- The checkerboard realization as a carrier element (mirrors
`checkerRegField`). -/
noncomputable def checkerRegField {d : ℕ} (lam Lam : ℝ) (ω : Sample d) :
    RegCoeffField d where
  toFun := coeffField lam Lam ω
  entry_measurable := fun i j => by
    by_cases hij : i = j
    · subst j
      simpa [coeffField, scalarMatrix] using
        measurable_scalarAt_spatial (lam := lam) (Lam := Lam) ω
    · simp [coeffField, scalarMatrix, hij]
  entry_locInt := fun i j => by
    by_cases hij : i = j
    · subst j
      have hmeas : Measurable (fun x : Vec d => coeffField lam Lam ω x i i) := by
        simpa [coeffField, scalarMatrix] using
          measurable_scalarAt_spatial (lam := lam) (Lam := Lam) ω
      refine locallyIntegrable_of_bounded_measurable hmeas
        (C := max |lam| |Lam|) fun x => ?_
      simpa [coeffField, scalarMatrix] using
        abs_scalarAt_le (lam := lam) (Lam := Lam) ω x
    · have hzero : (fun x : Vec d => coeffField lam Lam ω x i j)
          = fun _ : Vec d => (0 : ℝ) := by
        funext x
        simp [coeffField, scalarMatrix, hij]
      rw [hzero]
      exact MeasureTheory.locallyIntegrable_const (0 : ℝ)

def coinMeasure (p : ℝ≥0) (hp : p ≤ 1) : Measure Bool :=
  (PMF.bernoulli p hp).toMeasure

def sampleMeasure (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : Measure (Sample d) :=
  Measure.infinitePi (fun _ : Lattice d => coinMeasure p hp)

noncomputable def law (d : ℕ) (lam Lam : ℝ) (p : ℝ≥0) (hp : p ≤ 1) : CoeffLaw d :=
  Measure.map (checkerRegField lam Lam) (sampleMeasure d p hp)

end

end RandomCheckerboard

namespace CheckerboardScale

open PolynomialScale

/-- Mirror of the Bernoulli-checkerboard instantiation of
`Homogenization.homogenizationScale_polynomial_of_unitRange`
(`Homogenization/HighContrast/Scale/Final.lean` applied via
`Homogenization/Examples/RandomCheckerboard/CarrierLaw.lean`).  The dimension
restriction `3 ≤ d` (i.e. `d > 2`) is explicit; the capstone's ellipticity
parameter is instantiated at `Θ = Lam` — the checkerboard realizations lie in
the quadratic-form ellipticity class `IsEllipticMatrix 1 Lam` — so the
polynomial entry-scale bound reads `3^{N₀} ≤ (2 + Lam)^Ctriadic`, an explicit
algebraic dependence on the contrast. -/
theorem randomCheckerboard_homogenizationScale
    {d : ℕ} [NeZero d] (hd : 3 ≤ d) :
    ∃ Cscale Ctriadic alpha : ℝ, 0 < Cscale ∧ 0 < Ctriadic ∧ 0 < alpha ∧
      ∀ {lam Lam : ℝ} (_h1 : 1 ≤ lam) (_hle : lam ≤ Lam) (p : ℝ≥0) (hp : p ≤ 1),
        ∃ N0 : ℕ,
          (∀ n : ℕ,
            thetaAtScale (RandomCheckerboard.law d lam Lam p hp) ((N0 + n : ℕ) : ℤ) - 1 ≤
              (3 : ℝ) ^ (-alpha * (n : ℝ))) ∧
          (N0 : ℝ) ≤ Cscale * Real.log (2 + Lam) ∧
          (3 : ℝ) ^ ((N0 : ℕ) : ℝ) ≤ (2 + Lam) ^ Ctriadic := by
  sorry

end CheckerboardScale

end

end StatementAudit
end Homogenization
