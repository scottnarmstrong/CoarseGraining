import Mathlib

/-!
# Homogenization scale for the Bernoulli checkerboard

This is a Mathlib-only comparator challenge for the checkerboard instantiation
of the unconditional homogenization-scale theorem.

The mathematical content is the following.  In every dimension `d ≥ 3` there
are dimensional constants `Cscale, Ctriadic, alpha > 0` such that for all
conductances `1 ≤ lam ≤ Lam` and every coin parameter `p ≤ 1` the Bernoulli
checkerboard law — the law of the random field which equals `lam` times the
identity on the unit cells whose independent coin came up heads and `Lam` times
the identity on the remaining cells — admits an entry scale `N0` with

* geometric decay of the scalar contrast above `N0`, namely
  `theta_(N0 + n) - 1 ≤ 3 ^ (-alpha * n)` for every `n : ℕ`;
* a logarithmic entry scale, `N0 ≤ Cscale * log (2 + Lam)`; and
* a polynomial physical entry scale, `3 ^ N0 ≤ (2 + Lam) ^ Ctriadic`.

The scalar contrast `theta_n = thetaAtScale P n` is the `(0,0)`-entry ratio of
the two annealed coarse conductivity matrices on the triadic origin cube of
sidelength `3 ^ n`.  Those matrices are obtained by polarization from the
coarse-graining variational quantity `Mu`, an infimum of averaged block
energies over admissible potential/flux block states.  Under the structural
hypotheses both annealed matrices are scalar multiples of the identity, so this
entry ratio is the scalar contrast.

The bounds are unconditional in `lam`, `Lam` and `p`.  Every hypothesis of the
general theorem — that the law is a probability law of honest coefficient
fields which is stationary under integer translations, unit-range dependent,
invariant under signed coordinate changes and adjoints, and almost surely
pointwise in the quadratic-form ellipticity class with parameters `(1, Lam)`,
that is the general theorem at `Θ = Lam` — is discharged by the checkerboard
construction and therefore does not appear below.  The triadic bound
`3 ^ N0 ≤ (2 + Lam) ^ Ctriadic` exhibits the physical entry scale as an
explicit algebraic function of the contrast.

Only definitions needed to read that assertion occur below.  In particular:

* no ellipticity class and no structural-law predicate is defined, because the
  statement mentions none;
* the cube scale index is specialized to the nonnegative scales the statement
  uses; and
* the checkerboard construction is displayed in full — coin space, product
  measure, field assembly and pushforward — since it *is* the law being
  described.

The sole intentional `sorry` is the proof of the final theorem.
-/

namespace Homogenization
namespace StatementAudit

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

/-! ## 1. Euclidean vectors and matrices -/

abbrev Vec (d : ℕ) := Fin d → ℝ
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ
abbrev RawCoeffField (d : ℕ) := Vec d → Mat d

instance instMeasurableSpaceMat (d : ℕ) : MeasurableSpace (Mat d) := by
  exact @MeasurableSpace.pi (Fin d) (fun _ => Fin d → ℝ)
    (fun _ => @MeasurableSpace.pi (Fin d) (fun _ => ℝ)
      (fun _ => (RCLike.measurableSpace : MeasurableSpace ℝ)))

def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i

def matVecMul {d : ℕ} (A : Mat d) (x : Vec d) : Vec d :=
  fun i => ∑ j, A i j * x j

abbrev scalarMatrix {d : ℕ} (sigma : ℝ) : Mat d :=
  sigma • (1 : Mat d)

noncomputable def symmPart {d : ℕ} (A : Mat d) : Mat d :=
  fun i j => (A i j + A j i) / 2

noncomputable def skewPart {d : ℕ} (A : Mat d) : Mat d :=
  fun i j => (A i j - A j i) / 2

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

def pointwiseFieldSigma (d : ℕ) : MeasurableSpace (RawCoeffField d) := by
  exact @MeasurableSpace.pi (Vec d) (fun _ => Mat d)
    (fun _ => instMeasurableSpaceMat d)

def probeFieldSigma (d : ℕ) : MeasurableSpace (RawCoeffField d) :=
  MeasurableSpace.generateFrom
    {s | ∃ (i j : Fin d) (φ : Vec d → ℝ), IsProbe φ ∧
      ∃ t : Set ℝ, MeasurableSet t ∧ s = entryTest i j φ ⁻¹' t}

/-- The observable σ-algebra on raw fields: point evaluations together with all
compactly supported bounded entry integrals.

The bare function type `RawCoeffField d` deliberately carries no global
`MeasurableSpace` instance — Mathlib's product instance would also apply to it,
and the meaning of the law below must not depend on which instance wins. -/
def observableFieldSigma (d : ℕ) : MeasurableSpace (RawCoeffField d) :=
  pointwiseFieldSigma d ⊔ probeFieldSigma d

instance instMeasurableSpaceCoefficientField (d : ℕ) :
    MeasurableSpace (CoefficientField d) :=
  MeasurableSpace.comap CoefficientField.toFun (observableFieldSigma d)

abbrev CoefficientLaw (d : ℕ) := Measure (CoefficientField d)

/-- A raw field whose entries are measurable and uniformly bounded is an honest
coefficient field. -/
def CoefficientField.ofBounded {d : ℕ} (a : RawCoeffField d) (C : ℝ)
    (hmeas : ∀ i j : Fin d, Measurable fun x => a x i j)
    (hbdd : ∀ (i j : Fin d) (x : Vec d), |a x i j| ≤ C) :
    CoefficientField d where
  toFun := a
  entry_measurable := hmeas
  entry_locallyIntegrable := fun i j => by
    rw [locallyIntegrable_iff]
    intro k hk
    refine Measure.integrableOn_of_bounded hk.measure_lt_top.ne
      (hmeas i j).aestronglyMeasurable (M := C) ?_
    filter_upwards with x
    simpa [Real.norm_eq_abs] using hbdd i j x

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

end TriadicCube

/-- The triadic cube centered at the origin with sidelength `3 ^ m`. -/
def originCube (d : ℕ) [NeZero d] (m : ℕ) : TriadicCube d :=
  { scale := (m : ℤ)
    index := 0 }

noncomputable def volumeAverage {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ) : ℝ :=
  (volume U).toReal⁻¹ * ∫ x in U, f x ∂volume

/-! ## 4. Weak `H¹` and `H¹₀` -/

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

def GradientMemL2On {d : ℕ} (U : Set (Vec d)) (Du : Vec d → Vec d) : Prop :=
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

/-! ## 5. The block formalism and the coarse-graining quantity `Mu` -/

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

def blockBasis {d : ℕ} : BlockCoord d → BlockVec d
  | Sum.inl i => (Pi.single i 1, 0)
  | Sum.inr i => (0, Pi.single i 1)

/-- The doubled coefficient matrix of `A`, in the potential/flux variables. -/
noncomputable def blockMatrixOfCoeff {d : ℕ} (A : Mat d) : BlockMat d :=
  let s := symmPart A
  let k := skewPart A
  let sInv := s⁻¹
  { upperLeft := s + k.transpose * sInv * k
    upperRight := -(k.transpose * sInv)
    lowerLeft := -(sInv * k)
    lowerRight := sInv }

abbrev MemVectorL2On {d : ℕ} (U : Set (Vec d)) (f : Vec d → Vec d) : Prop :=
  MemLp f 2 (volumeOn U)

/-- `f` is the gradient of an `H¹₀` function on `U`. -/
def IsPotentialZeroTraceOn {d : ℕ} (U : Set (Vec d)) (f : Vec d → Vec d) : Prop :=
  ∃ u : WeakH10 U, u.toWeakH1.grad = f

/-- `g` is divergence free on `U` with vanishing normal trace. -/
def IsSolenoidalZeroNormalTraceOn {d : ℕ} (U : Set (Vec d))
    (g : Vec d → Vec d) : Prop :=
  ∀ φ : WeakH1 U,
    ∫ x in U, vecDot (g x) (φ.grad x) ∂volume = 0

/-- A candidate pair of a potential field and a flux field. -/
structure BlockState (d : ℕ) where
  potential : Vec d → Vec d
  flux : Vec d → Vec d

def BlockState.eval {d : ℕ} (X : BlockState d) (x : Vec d) : BlockVec d :=
  (X.potential x, X.flux x)

/-- `X` is admissible for the block boundary datum `P` on `U`. -/
def IsBlockMuAdmissible {d : ℕ} (U : Set (Vec d)) (P : BlockVec d)
    (X : BlockState d) : Prop :=
  MemVectorL2On U (fun x => X.potential x - P.1) ∧
    IsPotentialZeroTraceOn U (fun x => X.potential x - P.1) ∧
      MemVectorL2On U (fun x => X.flux x - P.2) ∧
        IsSolenoidalZeroNormalTraceOn U (fun x => X.flux x - P.2)

noncomputable def blockEnergyDensity {d : ℕ} (a : RawCoeffField d)
    (X : BlockState d) (x : Vec d) : ℝ :=
  (1 / 2 : ℝ) *
    blockVecDot (X.eval x) (blockMatVecMul (blockMatrixOfCoeff (a x)) (X.eval x))

noncomputable def muValueSet {d : ℕ} (U : Set (Vec d)) (P : BlockVec d)
    (a : RawCoeffField d) : Set ℝ :=
  {m | ∃ X : BlockState d,
    IsBlockMuAdmissible U P X ∧ m = volumeAverage U (blockEnergyDensity a X)}

/-- The coarse-graining variational quantity: the least averaged block energy
among admissible block states. -/
noncomputable def Mu {d : ℕ} (U : Set (Vec d)) (P : BlockVec d)
    (a : RawCoeffField d) : ℝ :=
  sInf (muValueSet U P a)

/-! ## 6. Annealed coarse matrices and the scalar contrast -/

/-- Polarization of the quadratic form `P ↦ Mu U P a`. -/
noncomputable def coarseBlockEntry {d : ℕ} (U : Set (Vec d))
    (a : RawCoeffField d) (α β : BlockCoord d) : ℝ :=
  if _h : α = β then
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

/-- The entrywise `P`-average of the coarse block matrix on `U`. -/
noncomputable def annealedBlockMatrix {d : ℕ} (P : CoefficientLaw d)
    (U : Set (Vec d)) : BlockMat d :=
  { upperLeft := fun i j => ∫ a, (coarseBlockMatrix U a.toFun).upperLeft i j ∂P
    upperRight := fun i j => ∫ a, (coarseBlockMatrix U a.toFun).upperRight i j ∂P
    lowerLeft := fun i j => ∫ a, (coarseBlockMatrix U a.toFun).lowerLeft i j ∂P
    lowerRight := fun i j => ∫ a, (coarseBlockMatrix U a.toFun).lowerRight i j ∂P }

/-- The inverse dual conductivity `(σ*)⁻¹`: the lower-right annealed block. -/
noncomputable def annealedSigmaStarInv {d : ℕ} (P : CoefficientLaw d)
    (U : Set (Vec d)) : Mat d :=
  (annealedBlockMatrix P U).lowerRight

/-- The annealed dual conductivity `σ*`. -/
noncomputable def annealedSigmaStar {d : ℕ} (P : CoefficientLaw d)
    (U : Set (Vec d)) : Mat d :=
  (annealedSigmaStarInv P U)⁻¹

/-- The product `(σ*)⁻¹ κ`: minus the lower-left annealed block. -/
noncomputable def annealedSigmaStarInvKappa {d : ℕ} (P : CoefficientLaw d)
    (U : Set (Vec d)) : Mat d :=
  -((annealedBlockMatrix P U).lowerLeft)

/-- The annealed skew coupling `κ = σ* ((σ*)⁻¹ κ)`. -/
noncomputable def annealedKappa {d : ℕ} (P : CoefficientLaw d)
    (U : Set (Vec d)) : Mat d :=
  annealedSigmaStar P U * annealedSigmaStarInvKappa P U

/-- The annealed conductivity `σ = b - κᵀ (σ*)⁻¹ κ`, where `b` is the
upper-left annealed block. -/
noncomputable def annealedSigma {d : ℕ} (P : CoefficientLaw d)
    (U : Set (Vec d)) : Mat d :=
  (annealedBlockMatrix P U).upperLeft -
    (annealedKappa P U).transpose * annealedSigmaStarInv P U * annealedKappa P U

noncomputable def annealedSigmaAtScale {d : ℕ} [NeZero d]
    (P : CoefficientLaw d) (n : ℕ) : Mat d :=
  annealedSigma P (originCube d n).set

noncomputable def annealedSigmaStarAtScale {d : ℕ} [NeZero d]
    (P : CoefficientLaw d) (n : ℕ) : Mat d :=
  annealedSigmaStar P (originCube d n).set

/-- The scalar contrast at scale `n`.

The repository selector chooses, through the scalarization witnesses supplied
by the structural law, scalars `barSigma`, `barSigmaStar` with
`annealedSigmaAtScale P n = barSigma • 1` and
`annealedSigmaStarAtScale P n = barSigmaStar • 1`, and returns
`barSigma * barSigmaStar⁻¹`.  Both witness records are `Prop`s consumed only
through `Classical.choice`, so by proof irrelevance the value depends on
`(P, n)` alone; and a scalar matrix is determined by its `(0,0)` entry.  The
Mathlib-only mirror is therefore the total function below. -/
noncomputable def thetaAtScale {d : ℕ} [NeZero d] (P : CoefficientLaw d)
    (n : ℕ) : ℝ :=
  annealedSigmaAtScale P n 0 0 * (annealedSigmaStarAtScale P n 0 0)⁻¹

/-! ## 7. The Bernoulli checkerboard law -/

namespace RandomCheckerboard

section

attribute [local instance] Classical.propDecidable

/-- The cells of the checkerboard are indexed by the integer lattice. -/
abbrev Lattice (d : ℕ) := Fin d → ℤ

/-- One independent coin per cell. -/
abbrev Sample (d : ℕ) := Lattice d → Bool

/-- The open unit cell centered at the lattice point `z`. -/
def openUnitCell {d : ℕ} (z : Lattice d) : Set (Vec d) :=
  {x | ∀ i : Fin d, |x i - (z i : ℝ)| < 1 / 2}

/-- Heads gives the low conductance `lam`, tails the high conductance `Lam`. -/
def coinConductance (lam Lam : ℝ) (b : Bool) : ℝ :=
  if b then lam else Lam

/-- The checkerboard scalar at `x`: the conductance of the cell containing `x`,
and `lam` on the (null) set of points lying in no open cell. -/
def scalarAt {d : ℕ} (lam Lam : ℝ) (ω : Sample d) (x : Vec d) : ℝ :=
  if h : ∃ z : Lattice d, x ∈ openUnitCell z then
    coinConductance lam Lam (ω (Classical.choose h))
  else
    lam

/-- The region where the checkerboard scalar takes the high value `Lam`. -/
def upperConductanceRegion {d : ℕ} (ω : Sample d) : Set (Vec d) :=
  ⋃ z : {z : Lattice d // ω z = false}, openUnitCell z.1

theorem isOpen_openUnitCell {d : ℕ} (z : Lattice d) :
    IsOpen (openUnitCell z : Set (Vec d)) := by
  have hset : (openUnitCell z : Set (Vec d)) =
      ⋂ i : Fin d, {x : Vec d | |x i - (z i : ℝ)| < 1 / 2} := by
    ext x; simp [openUnitCell]
  rw [hset]
  refine isOpen_iInter_of_finite fun i => ?_
  exact isOpen_lt (((continuous_apply i).sub continuous_const).abs) continuous_const

/-- Distinct lattice points have disjoint open cells. -/
theorem openUnitCell_unique {d : ℕ} {x : Vec d} {z w : Lattice d}
    (hz : x ∈ openUnitCell z) (hw : x ∈ openUnitCell w) :
    z = w := by
  funext i
  have h1 : |x i - (z i : ℝ)| < 1 / 2 := hz i
  have h2 : |x i - (w i : ℝ)| < 1 / 2 := hw i
  have key : |(z i : ℝ) - (w i : ℝ)| < 1 :=
    calc |(z i : ℝ) - (w i : ℝ)|
        ≤ |(z i : ℝ) - x i| + |x i - (w i : ℝ)| := abs_sub_le _ _ _
      _ = |x i - (z i : ℝ)| + |x i - (w i : ℝ)| := by rw [abs_sub_comm]
      _ < 1 / 2 + 1 / 2 := add_lt_add h1 h2
      _ = 1 := by norm_num
  obtain ⟨hlo, hhi⟩ := abs_lt.mp key
  have hlo' : (-1 : ℤ) < z i - w i := by
    have : ((-1 : ℤ) : ℝ) < ((z i - w i : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hhi' : (z i - w i : ℤ) < 1 := by
    have : ((z i - w i : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  omega

theorem scalarAt_eq_ite {d : ℕ} (lam Lam : ℝ) (ω : Sample d) (x : Vec d) :
    scalarAt lam Lam ω x =
      if x ∈ upperConductanceRegion ω then Lam else lam := by
  classical
  by_cases hx : ∃ z : Lattice d, x ∈ openUnitCell z
  · rw [scalarAt, dif_pos hx]
    set z := Classical.choose hx with hzdef
    have hz : x ∈ openUnitCell z := Classical.choose_spec hx
    have hmem : x ∈ upperConductanceRegion ω ↔ ω z = false := by
      constructor
      · intro hmem
        obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hmem
        have hwz : (w : Lattice d) = z := openUnitCell_unique hw hz
        rw [← hwz]
        exact w.2
      · intro hfalse
        exact Set.mem_iUnion.2 ⟨⟨z, hfalse⟩, hz⟩
    by_cases hupper : x ∈ upperConductanceRegion ω
    · rw [if_pos hupper]
      simp [coinConductance, hmem.1 hupper]
    · rw [if_neg hupper]
      have htrue : ω z = true := by
        cases hωz : ω z
        · exact absurd (hmem.2 hωz) hupper
        · rfl
      simp [coinConductance, htrue]
  · have hnot : x ∉ upperConductanceRegion ω := by
      intro hc
      obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hc
      exact hx ⟨w.1, hw⟩
    rw [scalarAt, dif_neg hx, if_neg hnot]

theorem measurable_scalarAt {d : ℕ} (lam Lam : ℝ) (ω : Sample d) :
    Measurable (scalarAt lam Lam ω) := by
  classical
  have hU : MeasurableSet (upperConductanceRegion ω : Set (Vec d)) :=
    MeasurableSet.iUnion fun z => (isOpen_openUnitCell z.1).measurableSet
  have hpiece : Measurable
      ((upperConductanceRegion ω).piecewise
        (fun _ : Vec d => Lam) (fun _ : Vec d => lam)) :=
    Measurable.piecewise hU measurable_const measurable_const
  convert hpiece using 1
  funext x
  simp [Set.piecewise, scalarAt_eq_ite]

theorem abs_scalarAt_le {d : ℕ} (lam Lam : ℝ) (ω : Sample d) (x : Vec d) :
    |scalarAt lam Lam ω x| ≤ max |lam| |Lam| := by
  classical
  rw [scalarAt_eq_ite]
  by_cases hx : x ∈ upperConductanceRegion ω
  · rw [if_pos hx]; exact le_max_right _ _
  · rw [if_neg hx]; exact le_max_left _ _

/-- The checkerboard field of the sample `ω`: the scalar `scalarAt` times the
identity matrix. -/
def rawField {d : ℕ} (lam Lam : ℝ) (ω : Sample d) : RawCoeffField d :=
  fun x => scalarMatrix (d := d) (scalarAt lam Lam ω x)

/-- The checkerboard field as an honest coefficient field. -/
noncomputable def realization {d : ℕ} (lam Lam : ℝ) (ω : Sample d) :
    CoefficientField d :=
  CoefficientField.ofBounded (rawField lam Lam ω) (max |lam| |Lam|)
    (fun i j => (measurable_scalarAt lam Lam ω).mul_const ((1 : Mat d) i j))
    (fun i j x => by
      have hentry : rawField lam Lam ω x i j =
          scalarAt lam Lam ω x * (1 : Mat d) i j := rfl
      by_cases hij : i = j
      · subst hij
        rw [hentry, Matrix.one_apply_eq, mul_one]
        exact abs_scalarAt_le lam Lam ω x
      · rw [hentry, Matrix.one_apply_ne hij, mul_zero, abs_zero]
        exact le_trans (abs_nonneg lam) (le_max_left _ _))

/-- One coin: heads with probability `p`. -/
def coinMeasure (p : ℝ≥0) (hp : p ≤ 1) : Measure Bool :=
  (PMF.bernoulli p hp).toMeasure

/-- Independent coins, one per cell. -/
def sampleMeasure (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : Measure (Sample d) :=
  Measure.infinitePi fun _ : Lattice d => coinMeasure p hp

/-- The Bernoulli checkerboard law: the pushforward of the coin measure along
the checkerboard field assembly. -/
noncomputable def law (d : ℕ) (lam Lam : ℝ) (p : ℝ≥0) (hp : p ≤ 1) :
    CoefficientLaw d :=
  Measure.map (realization lam Lam) (sampleMeasure d p hp)

end

end RandomCheckerboard

/-! ## 8. The theorem -/

namespace CheckerboardScale

/-- **Homogenization scale for the Bernoulli checkerboard.**  In dimension
`d ≥ 3` there are dimensional constants `Cscale, Ctriadic, alpha > 0` such that
for all conductances `1 ≤ lam ≤ Lam` and every coin parameter `p ≤ 1` the
checkerboard law has an entry scale `N0` above which the scalar contrast decays
geometrically, with `N0` logarithmic and `3 ^ N0` polynomial in the contrast.

Mirrors the checkerboard instantiation of
`Homogenization.homogenizationScale_polynomial_of_unitRange`. -/
theorem randomCheckerboard_homogenizationScale
    {d : ℕ} [NeZero d] (hd : 3 ≤ d) :
    ∃ Cscale Ctriadic alpha : ℝ, 0 < Cscale ∧ 0 < Ctriadic ∧ 0 < alpha ∧
      ∀ {lam Lam : ℝ}, 1 ≤ lam → lam ≤ Lam → ∀ (p : ℝ≥0) (hp : p ≤ 1),
        ∃ N0 : ℕ,
          (∀ n : ℕ,
            thetaAtScale (RandomCheckerboard.law d lam Lam p hp) (N0 + n) - 1 ≤
              (3 : ℝ) ^ (-alpha * (n : ℝ))) ∧
          (N0 : ℝ) ≤ Cscale * Real.log (2 + Lam) ∧
          (3 : ℝ) ^ (N0 : ℝ) ≤ (2 + Lam) ^ Ctriadic := by
  sorry

end CheckerboardScale

end

end StatementAudit
end Homogenization
