import Homogenization.Ambient.CoefficientField
import Homogenization.Geometry.Translation
import Homogenization.Probability.Scalarization
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Bounded

namespace Homogenization

instance instMeasurableSpaceVec (d : ℕ) : MeasurableSpace (Vec d) := by
  change MeasurableSpace (Fin d → ℝ)
  infer_instance

instance instMeasurableSpaceMat (d : ℕ) : MeasurableSpace (Mat d) := by
  change MeasurableSpace (Fin d → Fin d → ℝ)
  infer_instance

def IsLocallyUniformlyElliptic {d : ℕ} (a : CoeffField d) : Prop :=
  ∀ R : ℝ, 1 ≤ R →
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      IsEllipticFieldOn ε ε⁻¹ (Metric.closedBall (0 : Vec d) R) a

noncomputable def localTestObservable {d : ℕ} (e e' : Vec d) (φ : Vec d → ℝ)
    (a : CoeffField d) : ℝ :=
  ∫ x, (vecDot e' (matVecMul (a x) e) * φ x) ∂MeasureTheory.volume

/-- A finite local test observable, with the finite sum kept inside the
integral.  This avoids using additivity of the Bochner integral for arbitrary
coefficient fields. -/
noncomputable def localFiniteTestObservable {d : ℕ} {ι : Type} (s : Finset ι)
    (e e' : ι → Vec d) (φ : ι → Vec d → ℝ) (a : CoeffField d) : ℝ :=
  ∫ x, (∑ k ∈ s, vecDot (e' k) (matVecMul (a x) (e k)) * φ k x)
    ∂MeasureTheory.volume

/-- Two coefficient fields agree on all points of an observation set. -/
def LocalAgreementOn {d : ℕ} (U : Set (Vec d)) (a b : CoeffField d) : Prop :=
  ∀ x, x ∈ U → a x = b x

/-- A coefficient-field event is determined by the values of the field on `U`. -/
def IsLocalEvent {d : ℕ} (U : Set (Vec d)) (s : Set (CoeffField d)) : Prop :=
  ∀ ⦃a b : CoeffField d⦄, LocalAgreementOn U a b → (a ∈ s ↔ b ∈ s)

def LocalSigma {d : ℕ} (U : Set (Vec d)) : MeasurableSpace (CoeffField d) :=
  MeasurableSpace.generateFrom {s | IsLocalEvent U s}

/-- The pointwise (product) σ-algebra on coefficient fields: the smallest σ-algebra
making every coordinate evaluation `a ↦ a x` measurable. -/
def pointwiseCoeffFieldMeasurableSpace (d : ℕ) : MeasurableSpace (CoeffField d) :=
  MeasurableSpace.pi

/-- The bounded-local σ-algebra on coefficient fields: local events over
bounded observation sets.  This deliberately excludes unbounded regions such as
`Set.univ`; including `LocalSigma Set.univ` would make the ambient coefficient
space discrete and would rule out genuine infinite-product random fields. -/
def boundedLocalCoeffFieldMeasurableSpace (d : ℕ) : MeasurableSpace (CoeffField d) :=
  ⨆ U : {U : Set (Vec d) // Bornology.IsBounded U}, LocalSigma U.1

/-- The ambient σ-algebra on coefficient fields: the pointwise σ-algebra joined
with bounded local coefficient-field information.  This keeps every coordinate
evaluation measurable while making the bounded local events used by compact
tests and triadic cubes measurable. -/
instance instMeasurableSpaceCoeffField (d : ℕ) : MeasurableSpace (CoeffField d) :=
  pointwiseCoeffFieldMeasurableSpace d ⊔ boundedLocalCoeffFieldMeasurableSpace d

/-- The sigma-algebra on coefficient space induced by restricting the field to
the deterministic set `U`. This is the measurable local sigma algebra used for
unit-range dependence of genuine random fields. -/
def RestrictionSigma {d : ℕ} (U : Set (Vec d)) : MeasurableSpace (CoeffField d) :=
  MeasurableSpace.comap (restrictCoeffField U) inferInstance

theorem pointwise_le_coeffField (d : ℕ) :
    pointwiseCoeffFieldMeasurableSpace d ≤ instMeasurableSpaceCoeffField d :=
  le_sup_left

/-- The ambient→bounded-local bridge: every local event over a bounded
observation set is ambient-measurable. -/
theorem localSigma_le_coeffField_of_isBounded {d : ℕ} {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) :
    LocalSigma U ≤ instMeasurableSpaceCoeffField d :=
  le_trans
    (le_iSup (fun U : {U : Set (Vec d) // Bornology.IsBounded U} =>
      LocalSigma U.1) ⟨U, hU⟩)
    le_sup_right

/-- Coordinate evaluation is ambient-measurable (it factors through the pointwise
σ-algebra). -/
theorem measurable_coeffField_eval {d : ℕ} (y : Vec d) :
    Measurable (fun a : CoeffField d => a y) :=
  (measurable_pi_apply y).mono (pointwise_le_coeffField d) le_rfl

/-- A self-map of coefficient fields is ambient-measurable if it is measurable
into the pointwise σ-algebra and into every local sigma algebra. -/
theorem measurable_coeffField_to_ambient {d : ℕ} {f : CoeffField d → CoeffField d}
    (hpt : @Measurable _ _ (instMeasurableSpaceCoeffField d)
      (pointwiseCoeffFieldMeasurableSpace d) f)
    (hloc : ∀ U : Set (Vec d), Bornology.IsBounded U →
      @Measurable _ _ (instMeasurableSpaceCoeffField d) (LocalSigma U) f) :
    Measurable f := by
  rw [measurable_iff_comap_le]
  show (pointwiseCoeffFieldMeasurableSpace d ⊔ boundedLocalCoeffFieldMeasurableSpace d).comap f
      ≤ instMeasurableSpaceCoeffField d
  rw [MeasurableSpace.comap_sup, boundedLocalCoeffFieldMeasurableSpace,
    MeasurableSpace.comap_iSup]
  exact sup_le hpt.comap_le (iSup_le fun U => (hloc U.1 U.2).comap_le)

/-- A map from an arbitrary measurable space into coefficient fields is
ambient-measurable if it is pointwise-measurable and measurable into every
bounded local sigma algebra. -/
theorem measurable_to_coeffField_ambient {α : Type*} [mα : MeasurableSpace α] {d : ℕ}
    {f : α → CoeffField d}
    (hpt : @Measurable _ _ mα (pointwiseCoeffFieldMeasurableSpace d) f)
    (hloc : ∀ U : Set (Vec d), Bornology.IsBounded U →
      @Measurable _ _ mα (LocalSigma U) f) :
    Measurable f := by
  rw [measurable_iff_comap_le]
  show (pointwiseCoeffFieldMeasurableSpace d ⊔ boundedLocalCoeffFieldMeasurableSpace d).comap f
      ≤ mα
  rw [MeasurableSpace.comap_sup, boundedLocalCoeffFieldMeasurableSpace,
    MeasurableSpace.comap_iSup]
  exact sup_le hpt.comap_le (iSup_le fun U => (hloc U.1 U.2).comap_le)

theorem localTestObservable_eq_localFiniteTestObservable {d : ℕ}
    (e e' : Vec d) (φ : Vec d → ℝ) :
    localTestObservable e e' φ =
      localFiniteTestObservable ({()} : Finset Unit) (fun _ => e) (fun _ => e')
        (fun _ => φ) := by
  funext a
  simp [localTestObservable, localFiniteTestObservable]

/-- A finite test observable is measurable for the local sigma algebra on any
set containing the supports of all scalar probes in the finite sum. -/
theorem measurable_localFiniteTestObservable_localSigma {d : ℕ} {U : Set (Vec d)}
    {ι : Type} {I : Finset ι} {e e' : ι → Vec d} {φ : ι → Vec d → ℝ}
    (hφ_support : ∀ k ∈ I, Function.support (φ k) ⊆ U) :
    @Measurable (CoeffField d) ℝ (LocalSigma U) (borel ℝ)
      (localFiniteTestObservable I e e' φ) := by
  intro t _ht
  refine MeasurableSpace.measurableSet_generateFrom ?_
  intro a b hab
  simp only [Set.mem_preimage]
  have hEq :
      localFiniteTestObservable I e e' φ a =
        localFiniteTestObservable I e e' φ b := by
    unfold localFiniteTestObservable
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    by_cases hxU : x ∈ U
    · simp [hab x hxU]
    · have hzero : ∀ k ∈ I, φ k x = 0 := by
        intro k hk
        by_contra hkx
        exact hxU (hφ_support k hk (by simpa [Function.support] using hkx))
      apply Finset.sum_congr rfl
      intro k hk
      rw [hzero k hk]
      ring
  rw [hEq]

theorem LocalAgreementOn.mono {d : ℕ} {U V : Set (Vec d)} {a b : CoeffField d}
    (hUV : U ⊆ V) (h : LocalAgreementOn V a b) :
    LocalAgreementOn U a b :=
  fun x hx => h x (hUV hx)

theorem isBounded_image_of_continuous_vec {d : ℕ}
    {f : Vec d → Vec d} (hf : Continuous f) {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) :
    Bornology.IsBounded (f '' U) := by
  have hcompact : IsCompact (closure U) := hU.isCompact_closure
  exact (hcompact.image hf).isBounded.subset (Set.image_mono subset_closure)

/-- A self-map `T` of coefficient fields is measurable into `LocalSigma U` when
its values on `U` are determined by the input field on some source region. -/
theorem measurable_localSigma_of_local {d : ℕ} {T : CoeffField d → CoeffField d}
    (h : ∀ U : Set (Vec d), Bornology.IsBounded U →
      ∃ V : Set (Vec d), Bornology.IsBounded V ∧
      ∀ ⦃a b : CoeffField d⦄, LocalAgreementOn V a b →
        LocalAgreementOn U (T a) (T b))
    (U : Set (Vec d)) (hU : Bornology.IsBounded U) :
    @Measurable _ _ (instMeasurableSpaceCoeffField d) (LocalSigma U) T := by
  refine measurable_generateFrom fun s hs => ?_
  rcases h U hU with ⟨V, hV_bdd, hV⟩
  have hpre : @MeasurableSet (CoeffField d) (LocalSigma V) (T ⁻¹' s) :=
    MeasurableSpace.measurableSet_generateFrom
      (by
        intro a b hab
        exact hs (hV hab))
  exact localSigma_le_coeffField_of_isBounded hV_bdd _ hpre

/-- `localTestObservable e e' φ` is `LocalSigma U`-measurable when `tsupport φ ⊆ U`. -/
theorem measurable_localTestObservable_localSigma {d : ℕ} {U : Set (Vec d)}
    (e e' : Vec d) {φ : Vec d → ℝ} (_hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ)
    (_hφ_compact : HasCompactSupport φ) (hφ_support : tsupport φ ⊆ U) :
    @Measurable (CoeffField d) ℝ (LocalSigma U) (borel ℝ) (localTestObservable e e' φ) := by
  rw [localTestObservable_eq_localFiniteTestObservable]
  refine measurable_localFiniteTestObservable_localSigma ?_
  intro k hk x hx
  exact hφ_support (subset_tsupport φ hx)

/-- The generator set `localTestObservable e e' φ ⁻¹' t` is `LocalSigma U`-measurable. -/
theorem preimage_localTestObservable_mem_localSigma {d : ℕ} {U : Set (Vec d)}
    (e e' : Vec d) {φ : Vec d → ℝ} (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_support : tsupport φ ⊆ U)
    {t : Set ℝ} (ht : MeasurableSet t) :
    @MeasurableSet (CoeffField d) (LocalSigma U) (localTestObservable e e' φ ⁻¹' t) :=
  measurable_localTestObservable_localSigma e e' hφ_cont hφ_compact hφ_support ht

/-- `localTestObservable e e' φ` is ambient-measurable. -/
theorem measurable_localTestObservable {d : ℕ}
    (e e' : Vec d) {φ : Vec d → ℝ} (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) :
    Measurable (localTestObservable (d := d) e e' φ) :=
  (measurable_localTestObservable_localSigma (U := tsupport φ) e e' hφ_cont hφ_compact
    subset_rfl).mono
    (localSigma_le_coeffField_of_isBounded hφ_compact.isCompact.isBounded) le_rfl

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
    ProbabilityTheory.Indep (RestrictionSigma U) (RestrictionSigma V) P

def IsSignedPermutationMatrix {d : ℕ} (R : Mat d) : Prop :=
  ∃ σ : Equiv.Perm (Fin d), ∃ s : Fin d → ℝ,
    (∀ i, s i = 1 ∨ s i = -1) ∧
      ∀ i j, R i j = if i = σ j then s j else 0

private theorem matVecMul_one {d : ℕ} (x : Vec d) :
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

theorem IsSignedPermutationMatrix.transpose {d : ℕ} {R : Mat d}
    (hR : IsSignedPermutationMatrix R) :
    IsSignedPermutationMatrix (matTranspose R) := by
  classical
  rcases hR with ⟨σ, s, hs, hRdef⟩
  refine ⟨σ.symm, fun i => s (σ.symm i), ?_, ?_⟩
  · intro i
    exact hs (σ.symm i)
  · intro i j
    rw [matTranspose, Matrix.transpose_apply, hRdef j i]
    by_cases h : i = σ.symm j
    · subst i
      simp
    · have hji : j ≠ σ i := by
        intro hji
        apply h
        rw [hji]
        simp
      rw [if_neg hji, if_neg h]

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

private theorem continuous_matVecMul {d : ℕ} (R : Mat d) :
    Continuous (fun x : Vec d => matVecMul R x) := by
  change Continuous fun x : Fin d → ℝ => fun i => ∑ j, R i j * x j
  exact continuous_pi fun i =>
    continuous_finset_sum Finset.univ fun j _ => continuous_const.mul (continuous_apply j)

private theorem measurable_matVecMul {d : ℕ} (R : Mat d) :
    Measurable (fun x : Vec d => matVecMul R x) :=
  (continuous_matVecMul R).measurable

private noncomputable def signedPermutationHomeomorph {d : ℕ} (R : Mat d)
    (hR : IsSignedPermutationMatrix R) : Vec d ≃ₜ Vec d where
  toEquiv :=
    { toFun := matVecMul R
      invFun := matVecMul (matTranspose R)
      left_inv := by
        intro x
        rw [matVecMul_mul, hR.transpose_mul_self, matVecMul_one]
      right_inv := by
        intro x
        rw [matVecMul_mul, hR.mul_transpose_self, matVecMul_one] }
  continuous_toFun := continuous_matVecMul R
  continuous_invFun := continuous_matVecMul (matTranspose R)

private theorem measurePreserving_matVecMul_signedPermutation {d : ℕ} {R : Mat d}
    (hR : IsSignedPermutationMatrix R) :
    MeasureTheory.MeasurePreserving (fun x : Vec d => matVecMul R x)
      MeasureTheory.volume MeasureTheory.volume := by
  refine ⟨measurable_matVecMul R, ?_⟩
  have hscale :
      ENNReal.ofReal |(Matrix.det R)⁻¹| = 1 := by
    rw [abs_inv, hR.abs_det_eq_one]
    norm_num
  change MeasureTheory.Measure.map (Matrix.toLin' R) MeasureTheory.volume = MeasureTheory.volume
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hR.det_ne_zero, hscale, one_smul]

def rotateCoeffField {d : ℕ} (R : Mat d) (a : CoeffField d) : CoeffField d :=
  fun x => (matTranspose R) * (a (matVecMul R x)) * R

def adjointCoeffField {d : ℕ} (a : CoeffField d) : CoeffField d :=
  fun x => matTranspose (a x)

private theorem localTestObservable_rotateCoeffField_signedPermutation {d : ℕ}
    {R : Mat d} (hR : IsSignedPermutationMatrix R) (e e' : Vec d) (φ : Vec d → ℝ)
    (a : CoeffField d) :
    localTestObservable e e' φ (rotateCoeffField R a) =
      localTestObservable (matVecMul R e) (matVecMul R e')
        (fun y : Vec d => φ (matVecMul (matTranspose R) y)) a := by
  let g : Vec d → ℝ := fun y =>
    vecDot (matVecMul R e') (matVecMul (a y) (matVecMul R e)) *
      φ (matVecMul (matTranspose R) y)
  have hcv := (measurePreserving_matVecMul_signedPermutation hR).integral_comp
    (signedPermutationHomeomorph R hR).measurableEmbedding g
  have hleft :
      (∫ x, (vecDot e' (matVecMul (rotateCoeffField R a x) e) * φ x)
        ∂MeasureTheory.volume) =
        ∫ x, g (matVecMul R x) ∂MeasureTheory.volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    have hback : matVecMul (matTranspose R) (matVecMul R x) = x := by
      rw [matVecMul_mul, hR.transpose_mul_self, matVecMul_one]
    have halg :
        vecDot e' (matVecMul ((matTranspose R) * (a (matVecMul R x)) * R) e) =
          vecDot (matVecMul R e') (matVecMul (a (matVecMul R x)) (matVecMul R e)) := by
      calc
        vecDot e' (matVecMul ((matTranspose R) * (a (matVecMul R x)) * R) e)
            = vecDot e'
                (matVecMul ((matTranspose R) * (a (matVecMul R x))) (matVecMul R e)) := by
              rw [← matVecMul_mul]
        _ = vecDot e'
                (matVecMul (matTranspose R)
                  (matVecMul (a (matVecMul R x)) (matVecMul R e))) := by
              rw [← matVecMul_mul]
        _ = vecDot (matVecMul R e')
                (matVecMul (a (matVecMul R x)) (matVecMul R e)) := by
              rw [vecDot_matVecMul_transpose]
    simp [g, rotateCoeffField, hback, halg]
  unfold localTestObservable
  calc
    ∫ x, (vecDot e' (matVecMul (rotateCoeffField R a x) e) * φ x)
        ∂MeasureTheory.volume
        = ∫ x, g (matVecMul R x) ∂MeasureTheory.volume := hleft
    _ = ∫ y, g y ∂MeasureTheory.volume := hcv
    _ = ∫ y, (vecDot (matVecMul R e') (matVecMul (a y) (matVecMul R e)) *
        φ (matVecMul (matTranspose R) y)) ∂MeasureTheory.volume := rfl

private theorem localFiniteTestObservable_rotateCoeffField_signedPermutation {d : ℕ}
    {ι : Type} {R : Mat d} (hR : IsSignedPermutationMatrix R) (I : Finset ι)
    (e e' : ι → Vec d) (φ : ι → Vec d → ℝ) (a : CoeffField d) :
    localFiniteTestObservable I e e' φ (rotateCoeffField R a) =
      localFiniteTestObservable I
        (fun k => matVecMul R (e k))
        (fun k => matVecMul R (e' k))
        (fun k y => φ k (matVecMul (matTranspose R) y)) a := by
  let g : Vec d → ℝ := fun y =>
    ∑ k ∈ I,
      vecDot (matVecMul R (e' k)) (matVecMul (a y) (matVecMul R (e k))) *
        φ k (matVecMul (matTranspose R) y)
  have hcv := (measurePreserving_matVecMul_signedPermutation hR).integral_comp
    (signedPermutationHomeomorph R hR).measurableEmbedding g
  have hleft :
      (∫ x, (∑ k ∈ I,
          vecDot (e' k) (matVecMul (rotateCoeffField R a x) (e k)) * φ k x)
        ∂MeasureTheory.volume) =
        ∫ x, g (matVecMul R x) ∂MeasureTheory.volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    have hback : matVecMul (matTranspose R) (matVecMul R x) = x := by
      rw [matVecMul_mul, hR.transpose_mul_self, matVecMul_one]
    have hterm : ∀ k : ι,
        vecDot (e' k)
            (matVecMul ((matTranspose R) * (a (matVecMul R x)) * R) (e k)) =
          vecDot (matVecMul R (e' k))
            (matVecMul (a (matVecMul R x)) (matVecMul R (e k))) := by
      intro k
      calc
        vecDot (e' k)
            (matVecMul ((matTranspose R) * (a (matVecMul R x)) * R) (e k))
            = vecDot (e' k)
                (matVecMul ((matTranspose R) * (a (matVecMul R x)))
                  (matVecMul R (e k))) := by
              rw [← matVecMul_mul]
        _ = vecDot (e' k)
                (matVecMul (matTranspose R)
                  (matVecMul (a (matVecMul R x)) (matVecMul R (e k)))) := by
              rw [← matVecMul_mul]
        _ = vecDot (matVecMul R (e' k))
                (matVecMul (a (matVecMul R x)) (matVecMul R (e k))) := by
              rw [vecDot_matVecMul_transpose]
    simp [g, rotateCoeffField, hback, hterm]
  unfold localFiniteTestObservable
  calc
    ∫ x, (∑ k ∈ I, vecDot (e' k) (matVecMul (rotateCoeffField R a x) (e k)) * φ k x)
        ∂MeasureTheory.volume
        = ∫ x, g (matVecMul R x) ∂MeasureTheory.volume := hleft
    _ = ∫ y, g y ∂MeasureTheory.volume := hcv
    _ = ∫ y, (∑ k ∈ I,
          vecDot (matVecMul R (e' k)) (matVecMul (a y) (matVecMul R (e k))) *
            φ k (matVecMul (matTranspose R) y)) ∂MeasureTheory.volume := rfl

theorem measurable_rotateCoeffField {d : ℕ} (R : Mat d)
    (hR : IsSignedPermutationMatrix R) :
    Measurable (rotateCoeffField (d := d) R) := by
  refine measurable_coeffField_to_ambient ?_ ?_
  · -- into the pointwise σ-algebra: each coordinate is a (matrix-algebra) combination
    -- of evaluations of `a` at `R x`.
    refine measurable_pi_iff.2 fun x => measurable_pi_iff.2 fun i =>
      measurable_pi_iff.2 fun j => ?_
    let f : Fin d → CoeffField d → ℝ :=
      fun l a => ∑ k ∈ Finset.univ, (matTranspose R) i k * (a (matVecMul R x) k l * R l j)
    have hf : ∀ l ∈ Finset.univ, Measurable (f l) := by
      intro l hl
      refine Finset.measurable_sum (s := Finset.univ)
        (f := fun k => fun a : CoeffField d =>
          (matTranspose R) i k * (a (matVecMul R x) k l * R l j)) ?_
      intro k hk
      have hEval : Measurable (fun a : CoeffField d => a (matVecMul R x) k l) :=
        ((measurable_coeffField_eval (matVecMul R x)).eval).eval
      exact measurable_const.mul (hEval.mul measurable_const)
    simpa [rotateCoeffField, f, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      using (Finset.measurable_sum (s := Finset.univ) (f := f) hf)
  · -- into each `LocalSigma U`: values on `U` depend only on the input field
    -- on the signed-permutation image of `U`.
    intro U hU
    refine measurable_localSigma_of_local (T := rotateCoeffField R) ?_ U hU
    intro V hV
    refine ⟨{y : Vec d | matVecMul (matTranspose R) y ∈ V}, ?_, ?_⟩
    · have himage :
          Bornology.IsBounded ((fun x : Vec d => matVecMul R x) '' V) :=
        isBounded_image_of_continuous_vec (continuous_matVecMul R) hV
      refine himage.subset ?_
      intro y hy
      refine ⟨matVecMul (matTranspose R) y, hy, ?_⟩
      change matVecMul R (matVecMul (matTranspose R) y) = y
      rw [matVecMul_mul, hR.mul_transpose_self, matVecMul_one]
    intro a b hab x hx
    have hback : matVecMul (matTranspose R) (matVecMul R x) = x := by
      rw [matVecMul_mul, hR.transpose_mul_self, matVecMul_one]
    have hpoint : a (matVecMul R x) = b (matVecMul R x) := by
      exact hab (matVecMul R x) (by simpa [hback] using hx)
    simp [rotateCoeffField, hpoint]

/-- The adjoint pulls a local test back to the test with `e, e'` swapped (same
test function, same region). -/
theorem localTestObservable_adjoint {d : ℕ} (e e' : Vec d) (φ : Vec d → ℝ)
    (a : CoeffField d) :
    localTestObservable e e' φ (adjointCoeffField a) = localTestObservable e' e φ a := by
  unfold localTestObservable
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [adjointCoeffField]
  rw [vecDot_matVecMul_transpose, vecDot_comm]

theorem localFiniteTestObservable_adjoint {d : ℕ} {ι : Type} (I : Finset ι)
    (e e' : ι → Vec d) (φ : ι → Vec d → ℝ) (a : CoeffField d) :
    localFiniteTestObservable I e e' φ (adjointCoeffField a) =
      localFiniteTestObservable I e' e φ a := by
  unfold localFiniteTestObservable
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  apply Finset.sum_congr rfl
  intro k _hk
  congr 1
  simp only [adjointCoeffField]
  rw [vecDot_matVecMul_transpose, vecDot_comm]

theorem measurable_adjointCoeffField {d : ℕ} :
    Measurable (adjointCoeffField (d := d)) := by
  refine measurable_coeffField_to_ambient ?_ ?_
  · -- into the pointwise σ-algebra: each coordinate is an evaluation
    refine measurable_pi_iff.2 fun x => measurable_pi_iff.2 fun i =>
      measurable_pi_iff.2 fun j => ?_
    have hx : Measurable (fun a : CoeffField d => a x) := measurable_coeffField_eval x
    simpa [adjointCoeffField, matTranspose] using hx.eval.eval
  · -- into each `LocalSigma U`: adjoint is pointwise in the same spatial variable.
    intro U hU
    refine measurable_localSigma_of_local (T := adjointCoeffField) ?_ U hU
    intro V hV
    refine ⟨V, hV, ?_⟩
    intro a b hab x hx
    simp [adjointCoeffField, hab x hx]

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
  integral_comp_eq_of_map_eq (measurable_rotateCoeffField R hR) (hP R hR) f hf

theorem integrable_comp_rotateCoeffField_of_isIsotropicInLaw {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : MeasureTheory.Measure (CoeffField d)} (hP : IsIsotropicInLaw P)
    {R : Mat d} (hR : IsSignedPermutationMatrix R) (f : CoeffField d → E)
    (hf : MeasureTheory.Integrable f P) :
    MeasureTheory.Integrable (fun a => f (rotateCoeffField R a)) P := by
  have hfMap : MeasureTheory.Integrable f (MeasureTheory.Measure.map (rotateCoeffField R) P) := by
    simpa [hP R hR] using hf
  exact hfMap.comp_measurable (measurable_rotateCoeffField R hR)

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
