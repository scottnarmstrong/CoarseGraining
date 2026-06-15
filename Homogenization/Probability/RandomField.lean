import Homogenization.Ambient.CoefficientField
import Homogenization.Geometry.Translation
import Homogenization.Probability.Scalarization
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.Algebra.Support

namespace Homogenization

instance instMeasurableSpaceVec (d : ℕ) : MeasurableSpace (Vec d) := by
  change MeasurableSpace (Fin d → ℝ)
  infer_instance

instance instMeasurableSpaceMat (d : ℕ) : MeasurableSpace (Mat d) := by
  change MeasurableSpace (Fin d → Fin d → ℝ)
  infer_instance

instance instMeasurableSpaceCoeffField (d : ℕ) : MeasurableSpace (CoeffField d) := by
  change MeasurableSpace (Vec d → Mat d)
  infer_instance

def IsLocallyUniformlyElliptic {d : ℕ} (a : CoeffField d) : Prop :=
  ∀ R : ℝ, 1 ≤ R →
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      IsEllipticFieldOn ε ε⁻¹ (Metric.closedBall (0 : Vec d) R) a

noncomputable def localTestObservable {d : ℕ} (e e' : Vec d) (φ : Vec d → ℝ)
    (a : CoeffField d) : ℝ :=
  ∫ x, (vecDot e' (matVecMul (a x) e) * φ x) ∂MeasureTheory.volume

def LocalSigma {d : ℕ} (U : Set (Vec d)) : MeasurableSpace (CoeffField d) :=
  MeasurableSpace.generateFrom
    { s |
        ∃ e e' : Vec d, ∃ φ : Vec d → ℝ, ∃ t : Set ℝ,
          ContDiff ℝ (⊤ : ℕ∞) φ ∧
            HasCompactSupport φ ∧
            tsupport φ ⊆ U ∧
            MeasurableSet t ∧
            s = localTestObservable e e' φ ⁻¹' t }

def intVecToRealVec {d : ℕ} (z : Fin d → ℤ) : Vec d :=
  fun i => (z i : ℝ)

def translateByInt {d : ℕ} (z : Fin d → ℤ) : CoeffField d → CoeffField d :=
  translateCoeffField (intVecToRealVec z)

def IsStationary {d : ℕ} (P : MeasureTheory.Measure (CoeffField d)) : Prop :=
  ∀ z : Fin d → ℤ, MeasureTheory.Measure.map (translateByInt z) P = P

def AreUnitSeparated {d : ℕ} (U V : Set (Vec d)) : Prop :=
  ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V → 1 ≤ dist x y

def IsUnitRangeDependent {d : ℕ} (P : MeasureTheory.Measure (CoeffField d)) : Prop :=
  ∀ U V : Set (Vec d), AreUnitSeparated U V →
    ProbabilityTheory.Indep (LocalSigma U) (LocalSigma V) P

def IsSignedPermutationMatrix {d : ℕ} (R : Mat d) : Prop :=
  ∃ σ : Equiv.Perm (Fin d), ∃ s : Fin d → ℝ,
    (∀ i, s i = 1 ∨ s i = -1) ∧
      ∀ i j, R i j = if i = σ j then s j else 0

def rotateCoeffField {d : ℕ} (R : Mat d) (a : CoeffField d) : CoeffField d :=
  fun x => (matTranspose R) * (a (matVecMul R x)) * R

def adjointCoeffField {d : ℕ} (a : CoeffField d) : CoeffField d :=
  fun x => matTranspose (a x)

theorem measurable_rotateCoeffField {d : ℕ} (R : Mat d) :
    Measurable (rotateCoeffField (d := d) R) := by
  rw [measurable_pi_iff]
  intro x
  rw [measurable_pi_iff]
  intro i
  rw [measurable_pi_iff]
  intro j
  let f : Fin d → CoeffField d → ℝ :=
    fun l a => ∑ k ∈ Finset.univ, (matTranspose R) i k * (a (matVecMul R x) k l * R l j)
  have hf : ∀ l ∈ Finset.univ, Measurable (f l) := by
    intro l hl
    refine Finset.measurable_sum (s := Finset.univ)
      (f := fun k => fun a : CoeffField d =>
        (matTranspose R) i k * (a (matVecMul R x) k l * R l j)) ?_
    intro k hk
    have hEval : Measurable (fun a : CoeffField d => a (matVecMul R x) k l) := by
      have hEvalMat : Measurable (fun a : CoeffField d => a (matVecMul R x)) :=
        measurable_pi_apply (matVecMul R x)
      have hEvalRow : Measurable (fun a : CoeffField d => (a (matVecMul R x)) k) :=
        Measurable.eval hEvalMat
      exact Measurable.eval hEvalRow
    exact measurable_const.mul (hEval.mul measurable_const)
  simpa [rotateCoeffField, f, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    using (Finset.measurable_sum (s := Finset.univ) (f := f) hf)

theorem measurable_adjointCoeffField {d : ℕ} :
    Measurable (adjointCoeffField (d := d)) := by
  rw [measurable_pi_iff]
  intro x
  rw [measurable_pi_iff]
  intro i
  rw [measurable_pi_iff]
  intro j
  change Measurable (fun a : CoeffField d => matTranspose (a x) i j)
  have hEvalMat : Measurable (fun a : CoeffField d => a x) := measurable_pi_apply x
  have hEvalRow : Measurable (fun a : CoeffField d => (a x) j) := Measurable.eval hEvalMat
  simpa [adjointCoeffField, matTranspose] using
    (Measurable.eval hEvalRow)

def IsIsotropicInLaw {d : ℕ} (P : MeasureTheory.Measure (CoeffField d)) : Prop :=
  ∀ R : Mat d, IsSignedPermutationMatrix R →
    MeasureTheory.Measure.map (rotateCoeffField R) P = P

def IsAdjointInvariantInLaw {d : ℕ} (P : MeasureTheory.Measure (CoeffField d)) : Prop :=
  MeasureTheory.Measure.map adjointCoeffField P = P

theorem integral_comp_eq_of_map_eq {α : Type*} [MeasurableSpace α]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : MeasureTheory.Measure α} {f : α → α} (hf : Measurable f)
    (hmap : MeasureTheory.Measure.map f P = P) (g : α → E)
    (hg : MeasureTheory.AEStronglyMeasurable g P) :
    ∫ a, g (f a) ∂P = ∫ a, g a ∂P := by
  have hgm : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.Measure.map f P) := by
    simpa [hmap] using hg
  rw [← MeasureTheory.integral_map hf.aemeasurable hgm, hmap]

theorem isSignedPermutationMatrix_signFlipMatrix {d : ℕ} (i : Fin d) :
    IsSignedPermutationMatrix (signFlipMatrix i) := by
  refine ⟨Equiv.refl _, fun j => if j = i then (-1 : ℝ) else 1, ?_, ?_⟩
  · intro j
    by_cases h : j = i <;> simp [h]
  · intro r c
    by_cases h : r = c
    · subst c
      by_cases hi : r = i <;> simp [signFlipMatrix, hi]
    · simp [signFlipMatrix, h]

theorem isSignedPermutationMatrix_swap {d : ℕ} (i j : Fin d) :
    IsSignedPermutationMatrix (Matrix.swap ℝ i j) := by
  refine ⟨Equiv.swap i j, fun _ => (1 : ℝ), ?_, ?_⟩
  · intro k
    exact Or.inl rfl
  · intro r c
    by_cases h : r = Equiv.swap i j c
    · have h' : c = Equiv.swap i j r := by
        simpa using congrArg (Equiv.swap i j) h.symm
      rw [if_pos h]
      subst h'
      simp [Matrix.swap]
    · have hSwap : (Equiv.swap i j) r ≠ c := by
        intro hrc
        apply h
        simpa using (congrArg (Equiv.swap i j) hrc.symm).symm
      rw [if_neg h]
      simp [Matrix.swap, hSwap]

theorem IsIsotropicInLaw.map_rotateCoeffField_signFlipMatrix {d : ℕ}
    {P : MeasureTheory.Measure (CoeffField d)} (hP : IsIsotropicInLaw P) (i : Fin d) :
    MeasureTheory.Measure.map (rotateCoeffField (signFlipMatrix i)) P = P :=
  hP _ (isSignedPermutationMatrix_signFlipMatrix i)

theorem IsIsotropicInLaw.map_rotateCoeffField_swap {d : ℕ}
    {P : MeasureTheory.Measure (CoeffField d)} (hP : IsIsotropicInLaw P)
    (i j : Fin d) :
    MeasureTheory.Measure.map (rotateCoeffField (Matrix.swap ℝ i j)) P = P :=
  hP _ (isSignedPermutationMatrix_swap i j)

theorem integral_comp_rotateCoeffField_eq_of_isIsotropicInLaw {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : MeasureTheory.Measure (CoeffField d)} (hP : IsIsotropicInLaw P)
    {R : Mat d} (hR : IsSignedPermutationMatrix R) (f : CoeffField d → E)
    (hf : MeasureTheory.AEStronglyMeasurable f P) :
    ∫ a, f (rotateCoeffField R a) ∂P = ∫ a, f a ∂P :=
  integral_comp_eq_of_map_eq (measurable_rotateCoeffField R) (hP R hR) f hf

theorem integrable_comp_rotateCoeffField_of_isIsotropicInLaw {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : MeasureTheory.Measure (CoeffField d)} (hP : IsIsotropicInLaw P)
    {R : Mat d} (hR : IsSignedPermutationMatrix R) (f : CoeffField d → E)
    (hf : MeasureTheory.Integrable f P) :
    MeasureTheory.Integrable (fun a => f (rotateCoeffField R a)) P := by
  have hfMap : MeasureTheory.Integrable f (MeasureTheory.Measure.map (rotateCoeffField R) P) := by
    simpa [hP R hR] using hf
  exact hfMap.comp_measurable (measurable_rotateCoeffField R)

theorem integral_comp_adjointCoeffField_eq_of_isAdjointInvariantInLaw {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : MeasureTheory.Measure (CoeffField d)} (hP : IsAdjointInvariantInLaw P)
    (f : CoeffField d → E) (hf : MeasureTheory.AEStronglyMeasurable f P) :
    ∫ a, f (adjointCoeffField a) ∂P = ∫ a, f a ∂P :=
  integral_comp_eq_of_map_eq measurable_adjointCoeffField hP f hf

theorem integrable_comp_adjointCoeffField_of_isAdjointInvariantInLaw {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : MeasureTheory.Measure (CoeffField d)} (hP : IsAdjointInvariantInLaw P)
    (f : CoeffField d → E) (hf : MeasureTheory.Integrable f P) :
    MeasureTheory.Integrable (fun a => f (adjointCoeffField a)) P := by
  have hfMap : MeasureTheory.Integrable f (MeasureTheory.Measure.map adjointCoeffField P) := by
    exact hP.symm ▸ hf
  exact hfMap.comp_measurable measurable_adjointCoeffField

def IsLocalObservable {β : Type*} {d : ℕ} (U : Set (Vec d)) (X : CoeffField d → β) : Prop :=
  ∀ ⦃a₁ a₂ : CoeffField d⦄, (∀ x ∈ U, a₁ x = a₂ x) → X a₁ = X a₂

def IsTranslationCovariant {β : Type*} {d : ℕ}
    (X : Set (Vec d) → CoeffField d → β) : Prop :=
  ∀ (U : Set (Vec d)) (z : Fin d → ℤ) (a : CoeffField d),
    X (translateSet (intVecToRealVec z) U) a = X U (translateByInt z a)

end Homogenization
