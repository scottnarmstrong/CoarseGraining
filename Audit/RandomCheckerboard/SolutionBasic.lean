import Mathlib

/-!
# Statement-level audit vocabulary (random Bernoulli checkerboard)

This Mathlib-only file holds the statement vocabulary of the comparator
challenge `Audit/RandomCheckerboard/Challenge.lean`: the ambient vectors and
matrices, the honest coefficient-field carrier with its observable σ-algebra,
the triadic rescaling, cubes and normalized averages, weak `H¹` solutions, the
fixed `H^{3/4}` / `H^{-3/4}` quantities, the error and data sizes, and the
Bernoulli checkerboard law together with its flat `Setup`.

Every declaration below is a **verbatim** copy of the corresponding
declaration of `Challenge.lean`; only the file header (imports and this
docstring) differs, and the final theorem is omitted.  Byte-identity of these
bodies is what makes the theorem statement in `Solution.lean` match the
challenge statement.  It is split out of `Solution.lean` to keep each file
within the repository line budget; `Solution.lean` imports it and adds the
private bridges to the repository theorem together with the audited theorem
itself.
-/

namespace Homogenization
namespace StatementAudit

open MeasureTheory
open scoped BigOperators ENNReal NNReal

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
def pointwiseFieldSigma (d : ℕ) : MeasurableSpace (RawCoeffField d) := by
  exact @MeasurableSpace.pi (Vec d) (fun _ => Mat d)
    (fun _ => instMeasurableSpaceMat d)

set_option warn.classDefReducibility false in
def probeFieldSigma (d : ℕ) : MeasurableSpace (RawCoeffField d) :=
  MeasurableSpace.generateFrom
    {s | ∃ (i j : Fin d) (φ : Vec d → ℝ), IsProbe φ ∧
      ∃ t : Set ℝ, MeasurableSet t ∧ s = entryTest i j φ ⁻¹' t}

set_option warn.classDefReducibility false in
/-- The observable σ-algebra on raw fields: point evaluations together with all
compactly supported bounded entry integrals.

This is deliberately *not* registered as an instance.  The bare function type
`RawCoeffField d` also carries Mathlib's product σ-algebra, and the meaning of
the law below must not depend on which instance wins; the σ-algebra actually
used is pinned by the pullback on the next declaration. -/
def observableFieldSigma (d : ℕ) : MeasurableSpace (RawCoeffField d) :=
  pointwiseFieldSigma d ⊔ probeFieldSigma d

instance instMeasurableSpaceCoefficientField (d : ℕ) :
    MeasurableSpace (CoefficientField d) :=
  MeasurableSpace.comap CoefficientField.toFun (observableFieldSigma d)

abbrev CoefficientLaw (d : ℕ) := Measure (CoefficientField d)

/-! ### The triadic rescaling

The law audited below is the law of the checkerboard field after one triadic
rescaling, so the rescaling has to act on the carrier.  This is the only
carrier-preservation argument the challenge exposes. -/

/-- Local integrability is preserved by precomposition with a homeomorphism
which rescales Lebesgue measure by a finite nonzero factor. -/
theorem locallyIntegrable_comp_homeomorph_of_map_smul {d : ℕ} {f : Vec d → ℝ}
    (hf : LocallyIntegrable f volume) (e : Vec d ≃ₜ Vec d) {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    (hmap : Measure.map e volume = c • volume) :
    LocallyIntegrable (fun x => f (e x)) volume := by
  have hcv : LocallyIntegrable f (c • (volume : Measure (Vec d))) := by
    intro x
    obtain ⟨U, hU, hint⟩ := hf x
    refine ⟨U, hU, ?_⟩
    rw [IntegrableOn, Measure.restrict_smul]
    exact (integrable_smul_measure hc0 hctop).2 hint
  have hmapInt : LocallyIntegrable f (Measure.map e volume) := by
    rw [hmap]; exact hcv
  exact (locallyIntegrable_map_homeomorph e).mp hmapInt

/-- The triadic rescaling `a ↦ a (3 ^ k • ·)` of a coefficient field. -/
noncomputable def rescale {d : ℕ} (k : ℕ) (a : CoefficientField d) :
    CoefficientField d where
  toFun := fun x => a.toFun (((3 : ℝ) ^ k) • x)
  entry_measurable := fun i j =>
    (a.entry_measurable i j).comp (measurable_id.const_smul ((3 : ℝ) ^ k))
  entry_locallyIntegrable := fun i j =>
    locallyIntegrable_comp_homeomorph_of_map_smul (a.entry_locallyIntegrable i j)
      (Homeomorph.smulOfNeZero ((3 : ℝ) ^ k) (pow_ne_zero k (by norm_num)))
      (c := ENNReal.ofReal |(((3 : ℝ) ^ k) ^ Module.finrank ℝ (Vec d))⁻¹|)
      (by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le, abs_pos]
        exact inv_ne_zero (pow_ne_zero _ (pow_ne_zero k (by norm_num))))
      ENNReal.ofReal_ne_top
      (Measure.map_addHaar_smul volume (pow_ne_zero k (by norm_num)))

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

/-- Every triadic cube carries some ellipticity bounds almost everywhere.  This
is the qualitative regularity hypothesis under which the realization `a` is
compared with the homogenized medium. -/
def LocallyUniformlyElliptic {d : ℕ} (a : CoefficientField d) : Prop :=
  ∀ Q : TriadicCube d,
    ∃ lam Lam : ℝ,
      0 < lam ∧ lam ≤ Lam ∧
        ∀ᵐ x ∂volumeOn Q.interior, IsEllipticMatrix lam Lam (a x)

/-! ## 4. Weak `H¹` solutions -/

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

/-! ## 5. The fixed `H^{3/4}` and `H^{-3/4}` quantities -/

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

/-! ## 6. Error and data size -/

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

/-! ## 7. The Bernoulli checkerboard law -/

namespace RandomCheckerboard

attribute [local instance] Classical.propDecidable

/-- The lattice of unit cells. -/
abbrev Lattice (d : ℕ) := Fin d → ℤ

/-- One coin per unit cell; `true` selects the low conductance `lam`. -/
abbrev Sample (d : ℕ) := Lattice d → Bool

/-- The open unit cell centered at the lattice point `z`. -/
def openUnitCell {d : ℕ} (z : Lattice d) : Set (Vec d) :=
  {x | ∀ i : Fin d, |x i - (z i : ℝ)| < (1 / 2 : ℝ)}

theorem measurableSet_openUnitCell {d : ℕ} (z : Lattice d) :
    MeasurableSet (openUnitCell z) := by
  have hopen : IsOpen (openUnitCell z : Set (Vec d)) := by
    have hset :
        openUnitCell z =
          ⋂ i : Fin d, {x : Vec d | |x i - (z i : ℝ)| < (1 / 2 : ℝ)} := by
      ext x
      simp [openUnitCell]
    rw [hset]
    refine isOpen_iInter_of_finite fun i : Fin d => ?_
    exact isOpen_lt (((continuous_apply i).sub continuous_const).abs) continuous_const
  exact hopen.measurableSet

/-- The union of the open cells whose coin came up `false`.  The checkerboard
conductance equals `Lam` there and `lam` everywhere else. -/
def highConductanceRegion {d : ℕ} (ω : Sample d) : Set (Vec d) :=
  ⋃ z ∈ {z : Lattice d | ω z = false}, openUnitCell z

theorem measurableSet_highConductanceRegion {d : ℕ} (ω : Sample d) :
    MeasurableSet (highConductanceRegion ω) :=
  MeasurableSet.biUnion (Set.to_countable _)
    fun z _ => measurableSet_openUnitCell z

/-- The two-valued checkerboard conductance. -/
def conductance {d : ℕ} (lam Lam : ℝ) (ω : Sample d) (x : Vec d) : ℝ :=
  if x ∈ highConductanceRegion ω then Lam else lam

theorem measurable_conductance {d : ℕ} (lam Lam : ℝ) (ω : Sample d) :
    Measurable (conductance lam Lam ω) :=
  Measurable.ite (measurableSet_highConductanceRegion ω)
    measurable_const measurable_const

theorem abs_conductance_le {d : ℕ} (lam Lam : ℝ) (ω : Sample d) (x : Vec d) :
    |conductance lam Lam ω x| ≤ max |lam| |Lam| := by
  by_cases hx : x ∈ highConductanceRegion ω <;> simp [conductance, hx]

/-- A bounded measurable scalar field is locally integrable. -/
theorem locallyIntegrable_of_bounded {d : ℕ} {f : Vec d → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  refine Measure.integrableOn_of_bounded (hk.measure_lt_top).ne
    hf.aestronglyMeasurable (M := C) ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using hC x

/-- The checkerboard realization attached to a coin sample: the two-valued
conductance times the identity matrix. -/
noncomputable def checkerboardField {d : ℕ} (lam Lam : ℝ) (ω : Sample d) :
    CoefficientField d where
  toFun := fun x => scalarMatrix (conductance lam Lam ω x)
  entry_measurable := fun i j => by
    by_cases hij : i = j
    · subst hij
      simpa [scalarMatrix] using measurable_conductance lam Lam ω
    · simp [scalarMatrix, hij]
  entry_locallyIntegrable := fun i j => by
    by_cases hij : i = j
    · subst hij
      refine locallyIntegrable_of_bounded ?_ (C := max |lam| |Lam|) ?_
      · simpa [scalarMatrix] using measurable_conductance lam Lam ω
      · intro x
        simpa [scalarMatrix] using abs_conductance_le lam Lam ω x
    · have hzero :
          (fun x : Vec d => (scalarMatrix (conductance lam Lam ω x) : Mat d) i j)
            = fun _ : Vec d => (0 : ℝ) := by
        funext x
        simp [scalarMatrix, hij]
      rw [hzero]
      exact locallyIntegrable_const (0 : ℝ)

/-- A single Bernoulli(`p`) coin. -/
def coinMeasure (p : ℝ≥0) (hp : p ≤ 1) : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false ⟨(p : ℝ), NNReal.coe_nonneg p, by exact_mod_cast hp⟩

/-- Independent Bernoulli(`p`) coins, one per unit cell. -/
def coinSampleMeasure (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : Measure (Sample d) :=
  Measure.infinitePi fun _ : Lattice d => coinMeasure p hp

/-- All data describing the random checkerboard.  The structure is flat so that
a reader sees the complete list of parameters and hypotheses in one place. -/
structure Setup (d : ℕ) [NeZero d] where
  two_le_dim : 2 ≤ d
  lam : ℝ
  Lam : ℝ
  lam_pos : 0 < lam
  lam_le_Lam : lam ≤ Lam
  /-- Probability that a cell receives the low conductance `lam`. -/
  bias : ℝ≥0
  bias_le_one : bias ≤ 1

namespace Setup

variable {d : ℕ} [NeZero d] (S : Setup d)

/-- The law of the unrescaled Bernoulli checkerboard field. -/
noncomputable def checkerboardLaw : CoefficientLaw d :=
  Measure.map (checkerboardField S.lam S.Lam)
    (coinSampleMeasure d S.bias S.bias_le_one)

/-- The audited law: the checkerboard law pushed forward by one triadic
rescaling `a ↦ a (3 • ·)`. -/
noncomputable def P : CoefficientLaw d :=
  Measure.map (rescale 1) S.checkerboardLaw

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

end RandomCheckerboard

end

end StatementAudit
end Homogenization
