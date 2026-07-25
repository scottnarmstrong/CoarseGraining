import Mathlib

/-!
# Mathlib-only challenge: the polynomial homogenization-scale capstone

This file is the comparator challenge surface for the unconditional
homogenization-scale capstone
`Homogenization.homogenizationScale_polynomial_of_unitRange`
(`Homogenization/HighContrast/Scale/Final.lean`).

It imports only Mathlib.  The theorem asserts: for every dimension `d > 2`
(the explicit hypothesis `hd : 3 ≤ d`) there are dimensional constants
`Cscale, Ctriadic, alpha > 0` such that every `Θ`-elliptic (`Θ ≥ 1`)
stationary, unit-range, isotropic, adjoint-invariant probability law on the
regular-fields carrier satisfies the homogenization-scale contrast decay:

* the scalar contrast decays geometrically from an entry scale `N₀`,
  `θ_{N₀+n} - 1 ≤ 3^{-alpha·n}`;
* the entry scale is logarithmic in the ellipticity ratio,
  `N₀ ≤ Cscale · log(2 + Θ)`; and
* the physical entry scale is polynomial, `3^{N₀} ≤ (2 + Θ)^{Ctriadic}`.

Ellipticity enters only through the quadratic-form class
`IsEllipticMatrix 1 Θ`: coercivity `∀ ξ, |ξ|² ≤ ξ · A ξ` together with the
inverse quadratic-form bound `∀ ξ, Θ⁻¹ |ξ|² ≤ ξ · A⁻¹ ξ`.  The coefficient
fields are general (non-symmetric) matrices; no symmetric-ordering phrasing
appears anywhere.

The scalar contrast `thetaAtScale P n` is defined here as the `(0,0)`-entry
ratio of the annealed conductivity matrices
`annealedSigmaAtScale P n · (annealedSigmaStarAtScale P n)⁻¹`, built by
polarization from the coarse-graining variational quantity `Mu` (an infimum
of averaged block energies over admissible potential/flux block states).
Under the structural hypotheses both annealed matrices are scalar multiples
of the identity, so this entry ratio agrees with the repository's scalar
contrast selector.

The definitions below are statement-level copies of the objects needed to
state this capstone.  The main source correspondences are:

* ambient fields and ellipticity: `Homogenization/Ambient/CoefficientField.lean`
  and `Homogenization/CoarseGraining/ThetaEllipticity.lean`;
* the regular-fields carrier `RegCoeffField` and its σ-algebra:
  `Homogenization/Probability/RegCoeffField.lean` and
  `Homogenization/Probability/RegCoeffField/Sigma.lean`;
* carrier endomorphisms and the restriction σ-algebra:
  `Homogenization/Probability/RegCoeffField/{Endomorphisms,Restriction}.lean`;
* coefficient laws and law hypotheses: `Homogenization/Book/Ch04/*`;
* cubes: `Homogenization/Geometry/TriadicCube.lean`;
* Sobolev objects: `Homogenization/Sobolev/*`;
* block formalism and `Mu`: `Homogenization/Ambient/{Basic,BlockMatrix}.lean`,
  `Homogenization/CoarseGraining/BlockFormalism/{Structures,Properties}.lean`,
  and `Homogenization/CoarseGraining/Definitions.lean`;
* annealed coarse matrices and the contrast:
  `Homogenization/Book/Ch04/AnnealedDefinitions.lean` and
  `Homogenization/Book/Ch05/Definitions.lean`;
* the public theorem surface: `Homogenization/HighContrast/Scale/Final.lean`.

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

/-! ## Signed permutations and carrier endomorphisms

Statement-level copies of the carrier endomorphisms of
`Homogenization/Probability/RegCoeffField/Endomorphisms.lean` (translation,
signed-permutation rotation, adjoint, restriction), together with the
signed-permutation matrix algebra needed to define them.  Each map preserves
the carrier: entrywise Borel measurability and local integrability are stable
under the corresponding change of variables. -/

def IsSignedPermutationMatrix {d : ℕ} (R : Mat d) : Prop :=
  ∃ sigma : Equiv.Perm (Fin d), ∃ signs : Fin d → ℝ,
    (∀ i, signs i = 1 ∨ signs i = -1) ∧
      ∀ i j, R i j = if i = sigma j then signs j else 0

theorem matVecMul_one {d : ℕ} (x : Vec d) :
    matVecMul (1 : Mat d) x = x := by
  ext i
  unfold matVecMul
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hij : i ≠ j := fun h => hji h.symm
    simp [hij]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem matVecMul_mul {d : ℕ} (A B : Mat d) (x : Vec d) :
    matVecMul A (matVecMul B x) = matVecMul (A * B) x := by
  change A.mulVec (B.mulVec x) = (A * B).mulVec x
  exact Matrix.mulVec_mulVec x A B

theorem IsSignedPermutationMatrix.transpose_mul_self {d : ℕ} {R : Mat d}
    (hR : IsSignedPermutationMatrix R) :
    matTranspose R * R = 1 := by
  classical
  rcases hR with ⟨σ, s, hs, hR⟩
  ext i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.mul_apply]
    calc
      ∑ k, matTranspose R i k * R k i =
          matTranspose R i (σ i) * R (σ i) i := by
        refine Finset.sum_eq_single (a := σ i)
          (f := fun k : Fin d => matTranspose R i k * R k i) ?_ ?_
        · intro k _ hk
          change R k i * R k i = 0
          rw [hR k i]
          simp [hk]
        · intro hnot
          exact (hnot (Finset.mem_univ _)).elim
      _ = s i * s i := by
        change R (σ i) i * R (σ i) i = s i * s i
        rw [hR (σ i) i]
        simp
      _ = 1 := by
        rcases hs i with hsi | hsi <;> simp [hsi]
      _ = (1 : Mat d) i i := by simp
  · rw [Matrix.mul_apply]
    calc
      ∑ k, matTranspose R i k * R k j = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [matTranspose, Matrix.transpose_apply, hR k i, hR k j]
        have hσij : σ i ≠ σ j := fun h => hij (σ.injective h)
        by_cases hki : k = σ i
        · have hkj : k ≠ σ j := by
            intro h
            apply hij
            exact σ.injective (hki.symm.trans h)
          simp [hki, hσij]
        · simp [hki]
      _ = (1 : Mat d) i j := by simp [hij]

theorem IsSignedPermutationMatrix.mul_transpose_self {d : ℕ} {R : Mat d}
    (hR : IsSignedPermutationMatrix R) :
    R * matTranspose R = 1 := by
  classical
  rcases hR with ⟨σ, s, hs, hR⟩
  ext i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.mul_apply]
    calc
      ∑ k, R i k * matTranspose R k i =
          R i (σ.symm i) * matTranspose R (σ.symm i) i := by
        refine Finset.sum_eq_single (a := σ.symm i)
          (f := fun k : Fin d => R i k * matTranspose R k i) ?_ ?_
        · intro k _ hk
          change R i k * R i k = 0
          rw [hR i k]
          have hik : i ≠ σ k := by
            intro h
            apply hk
            have hsymm : σ.symm i = k := by
              rw [h]
              simp
            exact hsymm.symm
          rw [if_neg hik]
          simp
        · intro hnot
          exact (hnot (Finset.mem_univ _)).elim
      _ = s (σ.symm i) * s (σ.symm i) := by
        change R i (σ.symm i) * R i (σ.symm i) =
          s (σ.symm i) * s (σ.symm i)
        rw [hR i (σ.symm i)]
        have hi : i = σ (σ.symm i) := by simp
        rw [if_pos hi]
      _ = 1 := by
        rcases hs (σ.symm i) with hsi | hsi <;> simp [hsi]
      _ = (1 : Mat d) i i := by simp
  · rw [Matrix.mul_apply]
    calc
      ∑ k, R i k * matTranspose R k j = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [matTranspose, Matrix.transpose_apply, hR i k, hR j k]
        by_cases hik : i = σ k
        · have hjk : j ≠ σ k := by
            intro h
            exact hij (hik.trans h.symm)
          simp [hik, hjk]
        · simp [hik]
      _ = (1 : Mat d) i j := by simp [hij]

theorem IsSignedPermutationMatrix.det_ne_zero {d : ℕ} {R : Mat d}
    (hR : IsSignedPermutationMatrix R) :
    Matrix.det R ≠ 0 := by
  have hdet := congrArg Matrix.det hR.transpose_mul_self
  have hprod : Matrix.det R * Matrix.det R = 1 := by
    simpa [matTranspose, Matrix.det_mul, Matrix.det_transpose] using hdet
  intro hzero
  simp [hzero] at hprod

theorem IsSignedPermutationMatrix.abs_det_eq_one {d : ℕ} {R : Mat d}
    (hR : IsSignedPermutationMatrix R) :
    |Matrix.det R| = 1 := by
  have hdet := congrArg Matrix.det hR.transpose_mul_self
  have hsquare : Matrix.det R * Matrix.det R = 1 := by
    simpa [matTranspose, Matrix.det_mul, Matrix.det_transpose] using hdet
  have hnonneg : 0 ≤ |Matrix.det R| := abs_nonneg _
  have habs_square : |Matrix.det R| * |Matrix.det R| = 1 := by
    rw [← abs_mul, hsquare, abs_one]
  nlinarith

theorem continuous_matVecMul {d : ℕ} (R : Mat d) :
    Continuous (fun x : Vec d => matVecMul R x) := by
  change Continuous fun x : Fin d → ℝ => fun i => ∑ j, R i j * x j
  exact continuous_pi fun i =>
    continuous_finset_sum Finset.univ fun j _ => continuous_const.mul (continuous_apply j)

/-- A signed permutation acts as a homeomorphism of the base space. -/
noncomputable def matVecMulHomeomorph {d : ℕ} (R : Mat d)
    (hR : IsSignedPermutationMatrix R) : Vec d ≃ₜ Vec d where
  toEquiv :=
    { toFun := matVecMul R
      invFun := matVecMul (matTranspose R)
      left_inv := fun x => by
        rw [matVecMul_mul, hR.transpose_mul_self, matVecMul_one]
      right_inv := fun x => by
        rw [matVecMul_mul, hR.mul_transpose_self, matVecMul_one] }
  continuous_toFun := continuous_matVecMul R
  continuous_invFun := continuous_matVecMul (matTranspose R)

/-- The signed-permutation action preserves Lebesgue measure. -/
theorem measurePreserving_matVecMul {d : ℕ} (R : Mat d)
    (hR : IsSignedPermutationMatrix R) :
    MeasureTheory.MeasurePreserving (fun x : Vec d => matVecMul R x)
      MeasureTheory.volume MeasureTheory.volume := by
  refine ⟨(continuous_matVecMul R).measurable, ?_⟩
  have hscale : ENNReal.ofReal |(Matrix.det R)⁻¹| = 1 := by
    rw [abs_inv, hR.abs_det_eq_one]
    norm_num
  change Measure.map (Matrix.toLin' R) MeasureTheory.volume = MeasureTheory.volume
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hR.det_ne_zero, hscale, one_smul]

/-- Local-integrability transport under a measure-preserving homeomorphism. -/
theorem locallyIntegrable_comp_homeomorph_of_measurePreserving {d : ℕ}
    {f : Vec d → ℝ}
    (hf : MeasureTheory.LocallyIntegrable f MeasureTheory.volume)
    (e : Vec d ≃ₜ Vec d)
    (hmp : MeasureTheory.MeasurePreserving e MeasureTheory.volume MeasureTheory.volume) :
    MeasureTheory.LocallyIntegrable (fun x => f (e x)) MeasureTheory.volume := by
  have hmapInt : MeasureTheory.LocallyIntegrable f
      (Measure.map e MeasureTheory.volume) := by
    rw [hmp.map_eq]; exact hf
  exact (MeasureTheory.locallyIntegrable_map_homeomorph e).mp hmapInt

/-- Spatial translation is a carrier endomorphism (mirrors `translateReg`). -/
noncomputable def translateReg {d : ℕ} (z : Vec d) (a : RegCoeffField d) :
    RegCoeffField d where
  toFun := fun x => a.toFun (x + z)
  entry_measurable := fun i j =>
    (a.entry_measurable i j).comp (measurable_id.add measurable_const)
  entry_locInt := fun i j =>
    locallyIntegrable_comp_homeomorph_of_measurePreserving (a.entry_locInt i j)
      (Homeomorph.addRight z) (by
        simpa [Homeomorph.coe_addRight] using
          MeasureTheory.measurePreserving_add_right
            (MeasureTheory.volume : Measure (Vec d)) z)

/-- The conjugation collapse for a signed permutation:
`(Rᵀ M R)_{ij} = s_i s_j M_{σ i, σ j}`. -/
theorem matTranspose_mul_mul_apply {d : ℕ} {R : Mat d} {σ : Equiv.Perm (Fin d)}
    {s : Fin d → ℝ}
    (hRdef : ∀ i j, R i j = if i = σ j then s j else 0) (M : Mat d) (i j : Fin d) :
    (matTranspose R * M * R) i j = s i * s j * M (σ i) (σ j) := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ j)]
  · rw [hRdef (σ j) j, if_pos rfl, Matrix.mul_apply, Finset.sum_eq_single (σ i)]
    · rw [matTranspose, Matrix.transpose_apply, hRdef (σ i) i, if_pos rfl]
      ring
    · intro l _ hl
      rw [matTranspose, Matrix.transpose_apply, hRdef l i, if_neg hl, zero_mul]
    · intro hnot
      exact absurd (Finset.mem_univ (σ i)) hnot
  · intro k _ hk
    rw [hRdef k j, if_neg hk, mul_zero]
  · intro hnot
    exact absurd (Finset.mem_univ (σ j)) hnot

/-- Signed-permutation rotation is a carrier endomorphism (mirrors
`rotateReg`). -/
noncomputable def rotateReg {d : ℕ} (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (a : RegCoeffField d) : RegCoeffField d where
  toFun := fun x => (matTranspose R) * (a.toFun (matVecMul R x)) * R
  entry_measurable := fun i j => by
    obtain ⟨σ, s, _hs, hRdef⟩ := id hR
    have hcollapse :
        (fun x => (matTranspose R * a.toFun (matVecMul R x) * R) i j)
          = fun x => s i * s j * a.toFun (matVecMul R x) (σ i) (σ j) :=
      funext fun x => matTranspose_mul_mul_apply hRdef _ i j
    rw [hcollapse]
    exact (((a.entry_measurable (σ i) (σ j)).comp
      (continuous_matVecMul R).measurable).const_mul _)
  entry_locInt := fun i j => by
    obtain ⟨σ, s, _hs, hRdef⟩ := id hR
    have hcollapse :
        (fun x => (matTranspose R * a.toFun (matVecMul R x) * R) i j)
          = fun x => s i * s j * a.toFun (matVecMul R x) (σ i) (σ j) :=
      funext fun x => matTranspose_mul_mul_apply hRdef _ i j
    rw [hcollapse]
    have hg : MeasureTheory.LocallyIntegrable
        (fun x => a.toFun (matVecMul R x) (σ i) (σ j)) MeasureTheory.volume :=
      locallyIntegrable_comp_homeomorph_of_measurePreserving
        (a.entry_locInt (σ i) (σ j))
        (matVecMulHomeomorph R hR) (measurePreserving_matVecMul R hR)
    simpa [smul_eq_mul] using hg.smul (s i * s j)

/-- The adjoint (entrywise transpose) is a carrier endomorphism (mirrors
`adjointReg`). -/
def adjointReg {d : ℕ} (a : RegCoeffField d) : RegCoeffField d where
  toFun := fun x => (a.toFun x).transpose
  entry_measurable := fun i j => by
    simpa [Matrix.transpose_apply] using a.entry_measurable j i
  entry_locInt := fun i j => by
    simpa [Matrix.transpose_apply] using a.entry_locInt j i

/-- Restriction of a carrier field to a measurable set (mirrors
`restrictReg`). -/
noncomputable def restrictReg {d : ℕ} (U : Set (Vec d)) (hU : MeasurableSet U)
    (a : RegCoeffField d) : RegCoeffField d where
  toFun := Set.indicator U a.toFun
  entry_measurable := fun i j => by
    have hEq : (fun x => Set.indicator U a.toFun x i j)
        = Set.indicator U (fun x => a.toFun x i j) := by
      funext x
      by_cases hx : x ∈ U
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rw [hEq]
    exact (a.entry_measurable i j).indicator hU
  entry_locInt := fun i j => by
    have hEq : (fun x => Set.indicator U a.toFun x i j)
        = Set.indicator U (fun x => a.toFun x i j) := by
      funext x
      by_cases hx : x ∈ U
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rw [hEq, MeasureTheory.locallyIntegrable_iff]
    intro K hK
    exact ((a.entry_locInt i j).integrableOn_isCompact hK).indicator hU

/-- The restriction σ-algebra on the carrier (mirrors `RestrictionSigmaR`):
the comap of the canonical carrier σ-algebra along `restrictReg U hU`. -/
def RestrictionSigmaR {d : ℕ} (U : Set (Vec d)) (hU : MeasurableSet U) :
    MeasurableSpace (RegCoeffField d) :=
  MeasurableSpace.comap (restrictReg U hU) inferInstance

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

/-- Stationarity of a carrier law: invariance under every integer translation
(mirrors `IsStationaryR`). -/
def IsStationary {d : ℕ} (P : CoeffLaw d) : Prop :=
  ∀ z : Fin d → ℤ, Measure.map (translateReg (intVecToRealVec z)) P = P

def AreUnitSeparated {d : ℕ} (U V : Set (Vec d)) : Prop :=
  ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V → 1 ≤ dist x y

/-- Unit-range dependence of a carrier law: independence of the restriction
σ-algebras of unit-separated measurable sets (mirrors
`IsUnitRangeDependentR`; the `MeasurableSet` side-conditions make
`RestrictionSigmaR` well defined). -/
def IsUnitRangeDependent {d : ℕ} (P : CoeffLaw d) : Prop :=
  ∀ (U V : Set (Vec d)) (hU : MeasurableSet U) (hV : MeasurableSet V),
    AreUnitSeparated U V →
      ProbabilityTheory.Indep (RestrictionSigmaR U hU) (RestrictionSigmaR V hV) P

/-- Isotropy of a carrier law: invariance under every signed-permutation
rotation (mirrors `IsIsotropicInLawR`). -/
def IsIsotropicInLaw {d : ℕ} (P : CoeffLaw d) : Prop :=
  ∀ (R : Mat d) (hR : IsSignedPermutationMatrix R),
    Measure.map (rotateReg R hR) P = P

/-- Adjoint invariance of a carrier law (mirrors
`IsAdjointInvariantInLawR`). -/
def IsAdjointInvariantInLaw {d : ℕ} (P : CoeffLaw d) : Prop :=
  Measure.map adjointReg P = P

def IsAEEllipticFieldOn {d : ℕ} (lam Lam : ℝ) (U : Set (Vec d))
    (a : CoeffField d) : Prop :=
  MeasurableSet U ∧
    (∀ i j : Fin d,
      AEStronglyMeasurable
        (fun x : Vec d => restrictCoeffField U a x i j) (volumeMeasureOn U)) ∧
      ∀ᵐ x ∂ volumeMeasureOn U, IsEllipticMatrix lam Lam (a x)

/-- Spatial a.e. ellipticity of a carrier field, evaluated on the honest
sample (mirrors `Book.Ch04.AEEllipticOn`). -/
def AEEllipticOn {d : ℕ} (lam Lam : ℝ) (U : Set (Vec d))
    (a : RegCoeffField d) : Prop :=
  IsAEEllipticFieldOn lam Lam U a.toFun

def AELocallyUniformlyEllipticField {d : ℕ} (a : RegCoeffField d) : Prop :=
  ∀ Q : TriadicCube d,
    ∃ lam Lam : ℝ,
      0 < lam ∧ lam ≤ Lam ∧
        AEEllipticOn lam Lam (openCubeSet Q) a

def AELocallyUniformlyEllipticLaw {d : ℕ} (P : CoeffLaw d) : Prop :=
  ∀ᵐ a ∂P, AELocallyUniformlyEllipticField a

/-- The Chapter 4 law carrier (mirrors `Book.Ch04.LawCarrier`).  On the
honest-fields carrier the former measurability fields are law-independent free
theorems, so the carrier consists of the probability instance and the a.s.
local uniform ellipticity support alone. -/
structure LawCarrier {d : ℕ} (P : CoeffLaw d) : Prop where
  isProbability : IsProbabilityMeasure P
  ae_locally_uniformly_elliptic : AELocallyUniformlyEllipticLaw P

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
        AEEllipticOn lam Lam (openCubeSet Q) a


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

/-! ### The audited theorem -/

/-- Mirror of `Homogenization.homogenizationScale_polynomial_of_unitRange`
(`Homogenization/HighContrast/Scale/Final.lean`).  The dimension restriction
`3 ≤ d` (i.e. `d > 2`) is explicit; ellipticity enters only through the
quadratic-form class `IsEllipticMatrix 1 Θ`. -/
theorem homogenizationScale_polynomial_of_unitRange
    {d : ℕ} [NeZero d] (hd : 3 ≤ d) :
    ∃ Cscale Ctriadic alpha : ℝ, 0 < Cscale ∧ 0 < Ctriadic ∧ 0 < alpha ∧
      ∀ {Θ : ℝ} (_hΘ : 1 ≤ Θ) {P : CoeffLaw d} [IsProbabilityMeasure P]
        (_hP : LawCarrier P) (_hStruct : StructuralLaw P)
        (_hLaw : ThetaEllipticLaw Θ P),
      ∃ N0 : ℕ,
        (∀ n : ℕ,
          thetaAtScale P ((N0 + n : ℕ) : ℤ) - 1 ≤
            (3 : ℝ) ^ (-alpha * (n : ℝ))) ∧
        (N0 : ℝ) ≤ Cscale * Real.log (2 + Θ) ∧
        (3 : ℝ) ^ ((N0 : ℕ) : ℝ) ≤ (2 + Θ) ^ Ctriadic := by
  sorry

end PolynomialScale

end

end StatementAudit
end Homogenization
