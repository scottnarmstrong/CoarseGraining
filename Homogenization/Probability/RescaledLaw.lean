import Homogenization.Probability.IndependentSums.WeakOrlicz
import Homogenization.Probability.LocalObservable
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open scoped Pointwise

namespace Homogenization

/-!
Triadically rescaled coefficient laws and random scale parameters.

The Chapter 4 probability layer is mostly law-centric: coefficient fields are
sampled from a measure on `CoeffField d`.  This module adds the basic transport
API for passing from a law to its triadically rescaled law and records the
lightweight random-scale package used by later quenched-scale arguments.
-/

/-- Dilate a vector by the triadic factor `3^n`. -/
noncomputable def triadicDilateVec {d : ℕ} (n : ℕ) (x : Vec d) : Vec d :=
  fun i => (3 : ℝ) ^ n * x i

/-- The image of a set under triadic dilation by `3^n`. -/
noncomputable def triadicDilateSet {d : ℕ} (n : ℕ) (U : Set (Vec d)) : Set (Vec d) :=
  {x | ∃ y ∈ U, x = triadicDilateVec n y}

/-- The integer shift in the original variables corresponding to an integer
shift after triadic rescaling. -/
def triadicScaleIntShift {d : ℕ} (n : ℕ) (z : Fin d → ℤ) : Fin d → ℤ :=
  fun i => ((3 ^ n : ℕ) : ℤ) * z i

/-- Rescale a coefficient field by the triadic factor `3^n`.

The rescaled field is `x ↦ a(3^n x)`.  Thus integer translations of the
rescaled field correspond to translations of the original field by integer
vectors multiplied by `3^n`. -/
noncomputable def rescaleCoeffField {d : ℕ} (n : ℕ) (a : CoeffField d) : CoeffField d :=
  fun x => a (triadicDilateVec n x)

@[simp] theorem triadicDilateVec_zero {d : ℕ} (x : Vec d) :
    triadicDilateVec (d := d) 0 x = x := by
  funext i
  simp [triadicDilateVec]

@[simp] theorem triadicDilateVec_mem_triadicDilateSet {d : ℕ} (n : ℕ)
    {U : Set (Vec d)} {x : Vec d} (hx : x ∈ U) :
    triadicDilateVec n x ∈ triadicDilateSet n U :=
  ⟨x, hx, rfl⟩

/-- Triadic dilation sends bounded subsets of the ambient space to bounded subsets. -/
theorem isBounded_triadicDilateSet {d : ℕ} (n : ℕ) {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) :
    Bornology.IsBounded (triadicDilateSet n U) := by
  have hcont : Continuous (triadicDilateVec (d := d) n) := by
    change Continuous fun x : Fin d → ℝ => fun i => (3 : ℝ) ^ n * x i
    exact continuous_pi fun i => continuous_const.mul (continuous_apply i)
  simpa [triadicDilateSet, Set.image, eq_comm] using
    isBounded_image_of_continuous_vec hcont hU

@[simp] theorem rescaleCoeffField_zero {d : ℕ} (a : CoeffField d) :
    rescaleCoeffField 0 a = a := by
  funext x i j
  simp [rescaleCoeffField]

theorem rescaleCoeffField_add {d : ℕ} (m n : ℕ) (a : CoeffField d) :
    rescaleCoeffField (m + n) a =
      rescaleCoeffField n (rescaleCoeffField m a) := by
  funext x i j
  have hvec :
      triadicDilateVec (m + n) x = triadicDilateVec m (triadicDilateVec n x) := by
    funext k
    simp [triadicDilateVec, pow_add]
    ring
  simp [rescaleCoeffField, hvec]

theorem localTestObservable_rescaleCoeffField_eq_const_mul
    {d : ℕ} (k : ℕ) (e e' : Vec d) (φ : Vec d → ℝ) (a : CoeffField d) :
    localTestObservable e e' φ (rescaleCoeffField k a) =
      (((3 : ℝ) ^ k) ^ d)⁻¹ *
        localTestObservable e e'
          (fun y : Vec d => φ (((3 : ℝ) ^ k)⁻¹ • y)) a := by
  let r : ℝ := (3 : ℝ) ^ k
  have hr : 0 < r := by positivity
  let f : Vec d → ℝ := fun y => vecDot e' (matVecMul (a y) e) * φ (r⁻¹ • y)
  have hcv :
      ∫ x in (Set.univ : Set (Vec d)), f (r • x) ∂MeasureTheory.volume =
        (r ^ d)⁻¹ • ∫ y in r • (Set.univ : Set (Vec d)), f y ∂MeasureTheory.volume := by
    simpa [Vec] using
      (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
        (μ := MeasureTheory.volume) (f := f) (s := Set.univ) hr)
  have huniv : r • (Set.univ : Set (Vec d)) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      refine ⟨r⁻¹ • y, trivial, ?_⟩
      ext i
      simp [Pi.smul_apply, smul_eq_mul, hr.ne']
  have htriadic : ∀ x : Vec d, triadicDilateVec k x = r • x := by
    intro x
    ext i
    simp [triadicDilateVec, r, Pi.smul_apply, smul_eq_mul]
  unfold localTestObservable
  calc
    ∫ x, (vecDot e' (matVecMul (rescaleCoeffField k a x) e) * φ x) ∂MeasureTheory.volume
        = ∫ x, f (r • x) ∂MeasureTheory.volume := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          have hrx : r⁻¹ • (r • x) = x := by
            ext i
            simp [Pi.smul_apply, smul_eq_mul, hr.ne']
          simp [f, rescaleCoeffField, htriadic x, hrx]
    _ = ∫ x in (Set.univ : Set (Vec d)), f (r • x) ∂MeasureTheory.volume := by
          simp
    _ = (r ^ d)⁻¹ • ∫ y in r • (Set.univ : Set (Vec d)), f y ∂MeasureTheory.volume :=
          hcv
    _ = (r ^ d)⁻¹ *
          ∫ y, (vecDot e' (matVecMul (a y) e) *
            φ (((3 : ℝ) ^ k)⁻¹ • y)) ∂MeasureTheory.volume := by
          simp [f, r, huniv]

theorem localFiniteTestObservable_rescaleCoeffField_eq {d : ℕ} {ι : Type}
    (n : ℕ) (I : Finset ι) (e e' : ι → Vec d) (φ : ι → Vec d → ℝ)
    (a : CoeffField d) :
    localFiniteTestObservable I e e' φ (rescaleCoeffField n a) =
      localFiniteTestObservable I e e'
        (fun k y => (((3 : ℝ) ^ n) ^ d)⁻¹ * φ k (((3 : ℝ) ^ n)⁻¹ • y)) a := by
  let r : ℝ := (3 : ℝ) ^ n
  have hr : 0 < r := by positivity
  let c : ℝ := (r ^ d)⁻¹
  let f : Vec d → ℝ := fun y =>
    ∑ k ∈ I, vecDot (e' k) (matVecMul (a y) (e k)) * φ k (r⁻¹ • y)
  have hcv :
      ∫ x in (Set.univ : Set (Vec d)), f (r • x) ∂MeasureTheory.volume =
        (r ^ d)⁻¹ • ∫ y in r • (Set.univ : Set (Vec d)), f y ∂MeasureTheory.volume := by
    simpa [Vec] using
      (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
        (μ := MeasureTheory.volume) (f := f) (s := Set.univ) hr)
  have huniv : r • (Set.univ : Set (Vec d)) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      refine ⟨r⁻¹ • y, trivial, ?_⟩
      ext i
      simp [Pi.smul_apply, smul_eq_mul, hr.ne']
  have htriadic : ∀ x : Vec d, triadicDilateVec n x = r • x := by
    intro x
    ext i
    simp [triadicDilateVec, r, Pi.smul_apply, smul_eq_mul]
  unfold localFiniteTestObservable
  calc
    ∫ x, (∑ k ∈ I, vecDot (e' k) (matVecMul (rescaleCoeffField n a x) (e k)) *
        φ k x) ∂MeasureTheory.volume
        = ∫ x, f (r • x) ∂MeasureTheory.volume := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          have hrx : r⁻¹ • (r • x) = x := by
            ext i
            simp [Pi.smul_apply, smul_eq_mul, hr.ne']
          simp [f, rescaleCoeffField, htriadic x, hrx]
    _ = ∫ x in (Set.univ : Set (Vec d)), f (r • x) ∂MeasureTheory.volume := by
          simp
    _ = (r ^ d)⁻¹ • ∫ y in r • (Set.univ : Set (Vec d)), f y ∂MeasureTheory.volume :=
          hcv
    _ = c * ∫ y, f y ∂MeasureTheory.volume := by
          simp [c, huniv]
    _ = ∫ y, c * f y ∂MeasureTheory.volume := by
          exact (MeasureTheory.integral_const_mul c f).symm
    _ = ∫ y, (∑ k ∈ I, vecDot (e' k) (matVecMul (a y) (e k)) *
        ((((3 : ℝ) ^ n) ^ d)⁻¹ * φ k (((3 : ℝ) ^ n)⁻¹ • y)))
        ∂MeasureTheory.volume := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with y
          simp [f, c, r, Finset.mul_sum]
          ring_nf

theorem measurable_rescaleCoeffField {d : ℕ} (n : ℕ) :
    Measurable (rescaleCoeffField (d := d) n) := by
  refine measurable_coeffField_to_ambient ?_ (fun V hV => ?_)
  · refine measurable_pi_iff.2 fun x => measurable_pi_iff.2 fun i =>
      measurable_pi_iff.2 fun j => ?_
    exact measurable_coeffField_entry (d := d) (triadicDilateVec n x) i j
  · refine measurable_localSigma_of_local (T := rescaleCoeffField n) ?_ V hV
    intro W hW
    refine ⟨triadicDilateSet n W, ?_, ?_⟩
    · exact isBounded_triadicDilateSet n hW
    intro a b hab x hxW
    simp [rescaleCoeffField, hab (triadicDilateVec n x)
      (triadicDilateVec_mem_triadicDilateSet n hxW)]

theorem translateByInt_rescaleCoeffField_eq_rescaleCoeffField_translateByInt
    {d : ℕ} (n : ℕ) (z : Fin d → ℤ) (a : CoeffField d) :
    translateByInt z (rescaleCoeffField n a) =
      rescaleCoeffField n (translateByInt (triadicScaleIntShift n z) a) := by
  funext x i j
  have hvec :
      triadicDilateVec n (x + intVecToRealVec z) =
        triadicDilateVec n x + intVecToRealVec (triadicScaleIntShift n z) := by
    funext k
    simp [triadicDilateVec, triadicScaleIntShift, intVecToRealVec]
    ring
  change a (triadicDilateVec n (x + intVecToRealVec z)) i j =
    a (triadicDilateVec n x + intVecToRealVec (triadicScaleIntShift n z)) i j
  rw [hvec]

/-- The law obtained by triadically rescaling coefficient fields by `3^n`. -/
noncomputable def rescaledLaw {d : ℕ} (P : MeasureTheory.Measure (CoeffField d)) (n : ℕ) :
    MeasureTheory.Measure (CoeffField d) :=
  MeasureTheory.Measure.map (rescaleCoeffField n) P

@[simp] theorem rescaledLaw_zero {d : ℕ} (P : MeasureTheory.Measure (CoeffField d)) :
    rescaledLaw P 0 = P := by
  have h : rescaleCoeffField (d := d) 0 = id := by
    funext a
    simp
  simp [rescaledLaw, h]

theorem map_rescaledLaw_eq {β : Type*} [MeasurableSpace β] {d : ℕ}
    (P : MeasureTheory.Measure (CoeffField d)) (n : ℕ)
    (f : CoeffField d → β) (hf : Measurable f) :
    MeasureTheory.Measure.map f (rescaledLaw P n) =
      MeasureTheory.Measure.map (fun a => f (rescaleCoeffField n a)) P := by
  simpa [rescaledLaw, Function.comp] using
    (MeasureTheory.Measure.map_map hf (measurable_rescaleCoeffField (d := d) n) (μ := P))

theorem IsStationary.isStationary_rescaledLaw {d : ℕ} {P : MeasureTheory.Measure (CoeffField d)}
    (hP : IsStationary P) (n : ℕ) :
    IsStationary (rescaledLaw P n) := by
  intro z
  calc
    MeasureTheory.Measure.map (translateByInt z) (rescaledLaw P n)
        = MeasureTheory.Measure.map
            (fun a => translateByInt z (rescaleCoeffField n a)) P := by
          exact map_rescaledLaw_eq P n (translateByInt z) (measurable_translateByInt z)
    _ = MeasureTheory.Measure.map
            (fun a => rescaleCoeffField n (translateByInt (triadicScaleIntShift n z) a)) P := by
          congr 1
          funext a
          exact translateByInt_rescaleCoeffField_eq_rescaleCoeffField_translateByInt n z a
    _ =
        MeasureTheory.Measure.map (rescaleCoeffField n)
          (MeasureTheory.Measure.map (translateByInt (triadicScaleIntShift n z)) P) := by
          symm
          simpa [Function.comp] using
            (MeasureTheory.Measure.map_map
              (measurable_rescaleCoeffField (d := d) n)
              (measurable_translateByInt (d := d) (triadicScaleIntShift n z)) (μ := P))
    _ = rescaledLaw P n := by
          rw [hP (triadicScaleIntShift n z)]
          rfl

theorem isLocalObservable_comp_rescaleCoeffField {β : Type*} {d : ℕ}
    {U : Set (Vec d)} {X : CoeffField d → β} (n : ℕ)
    (hX : IsLocalObservable U X) :
    IsLocalObservable (triadicDilateSet n U) (fun a => X (rescaleCoeffField n a)) := by
  intro a₁ a₂ hagree
  apply hX
  intro x hx
  funext i j
  exact congrFun (congrFun (hagree (triadicDilateVec n x)
    (triadicDilateVec_mem_triadicDilateSet n hx)) i) j

namespace MeasurableLocalObservable

variable {β : Type*} [MeasurableSpace β] {d : ℕ} {U : Set (Vec d)}

/-- Pull a local observable back along triadic coefficient-field rescaling. -/
noncomputable def rescale (X : MeasurableLocalObservable d U β) (n : ℕ) :
    MeasurableLocalObservable d (triadicDilateSet n U) β where
  toFun := fun a => X (rescaleCoeffField n a)
  measurable_toFun := X.measurable.comp (measurable_rescaleCoeffField n)
  isLocal_toFun := isLocalObservable_comp_rescaleCoeffField n X.isLocal

@[simp] theorem rescale_apply (X : MeasurableLocalObservable d U β) (n : ℕ)
    (a : CoeffField d) :
    X.rescale n a = X (rescaleCoeffField n a) :=
  rfl

theorem law_rescale_eq_map_rescaledLaw
    (X : MeasurableLocalObservable d U β)
    (P : MeasureTheory.Measure (CoeffField d)) (n : ℕ) :
    MeasureTheory.Measure.map X (rescaledLaw P n) =
      MeasureTheory.Measure.map (X.rescale n) P :=
  map_rescaledLaw_eq P n X X.measurable

end MeasurableLocalObservable

namespace RandomCoeffField

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- Rescale a sample-space-valued random coefficient field. -/
noncomputable def rescale (A : RandomCoeffField Ω d) (n : ℕ) : RandomCoeffField Ω d where
  toFun := fun ω => rescaleCoeffField n (A ω)
  measurable_toFun := (measurable_rescaleCoeffField n).comp A.measurable

@[simp] theorem rescale_apply (A : RandomCoeffField Ω d) (n : ℕ) (ω : Ω) :
    A.rescale n ω = rescaleCoeffField n (A ω) :=
  rfl

theorem law_rescale (A : RandomCoeffField Ω d) (μ : MeasureTheory.Measure Ω) (n : ℕ) :
    (A.rescale n).law μ = rescaledLaw (A.law μ) n := by
  symm
  simpa [RandomCoeffField.law, RandomCoeffField.rescale, rescaledLaw, Function.comp] using
    (MeasureTheory.Measure.map_map
      (measurable_rescaleCoeffField (d := d) n) A.measurable (μ := μ))

end RandomCoeffField

/-- A measurable random integer scale parameter.  Later quenched arguments use
this as the formal home for random minimal scales. -/
structure RandomScaleParameter (Ω : Type*) [MeasurableSpace Ω] where
  /-- The random scale exponent. -/
  toFun : Ω → ℕ
  /-- Measurability of the scale exponent. -/
  measurable_toFun : Measurable toFun

namespace RandomScaleParameter

variable {Ω : Type*} [MeasurableSpace Ω]

instance : CoeFun (RandomScaleParameter Ω) (fun _ => Ω → ℕ) := ⟨toFun⟩

theorem measurable (X : RandomScaleParameter Ω) : Measurable X :=
  X.measurable_toFun

/-- A deterministic scale parameter, viewed as a random scale. -/
def const (n : ℕ) : RandomScaleParameter Ω where
  toFun := fun _ => n
  measurable_toFun := measurable_const

@[simp] theorem const_apply (n : ℕ) (ω : Ω) :
    (const n : RandomScaleParameter Ω) ω = n :=
  rfl

/-- Interpret a random scale exponent as a real-valued random variable. -/
noncomputable def toReal (X : RandomScaleParameter Ω) : Ω → ℝ :=
  fun ω => (X ω : ℝ)

/-- Stretched-exponential tail control for a random scale parameter. -/
def HasGammaTail (μ : MeasureTheory.Measure Ω) (X : RandomScaleParameter Ω)
    (σ A : ℝ) : Prop :=
  IndependentSums.IsBigO μ (IndependentSums.gammaSigma σ) X.toReal A

/-- A random scale controls a family of good-scale predicates above the random
threshold. -/
def ControlsAbove (μ : MeasureTheory.Measure Ω) (X : RandomScaleParameter Ω)
    (Good : ℕ → Ω → Prop) : Prop :=
  ∀ᵐ ω ∂μ, ∀ n, X ω ≤ n → Good n ω

theorem controlsAbove_of_forall {μ : MeasureTheory.Measure Ω}
    {X : RandomScaleParameter Ω} {Good : ℕ → Ω → Prop}
    (hGood : ∀ ω n, X ω ≤ n → Good n ω) :
    ControlsAbove μ X Good :=
  Filter.Eventually.of_forall fun ω n hn => hGood ω n hn

theorem ControlsAbove.mono {μ : MeasureTheory.Measure Ω}
    {X : RandomScaleParameter Ω} {Good Better : ℕ → Ω → Prop}
    (hX : ControlsAbove μ X Good)
    (hmono : ∀ᵐ ω ∂μ, ∀ n, Good n ω → Better n ω) :
    ControlsAbove μ X Better := by
  filter_upwards [hX, hmono] with ω hGood hBetter n hn
  exact hBetter n (hGood n hn)

end RandomScaleParameter

end Homogenization
