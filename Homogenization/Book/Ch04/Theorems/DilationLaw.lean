import Homogenization.Book.Ch04.Theorems.WidetildeTheta
import Homogenization.Book.Ch04.Theorems.Scalarization
import Homogenization.Book.Ch04.Theorems.Expectations
import Homogenization.Book.Ch02.Theorems.Dilation
import Homogenization.Probability.RescaledLaw

namespace Homogenization
namespace Book
namespace Ch04

open MeasureTheory
open scoped Pointwise

noncomputable section

/-!
# Dilation of Chapter 4 laws

This file starts the law-facing dilation API used in Section 5.5.  The
normalized law is the push-forward of the original coefficient law by the
triadic pullback which sends scale `k` in the original coordinates to scale
zero in normalized coordinates.
-/

/-- Scale-normalize a coefficient law by pulling coefficient fields back under
the triadic dilation `x ↦ 3^k x`. -/
noncomputable def scaleNormalizedLaw {d : ℕ} (k : ℕ) (P : CoeffLaw d) :
    CoeffLaw d :=
  Measure.map (Ch02.dilateCoeffField (-(k : ℤ))) P

/-- The existing probability-layer rescaling is the same map as the Ch2
dilation by the negative natural scale. -/
theorem rescaleCoeffField_eq_dilateCoeffField_neg_nat {d : ℕ} (k : ℕ) :
    rescaleCoeffField (d := d) k = Ch02.dilateCoeffField (-(k : ℤ)) := by
  funext a x i j
  have hvec : Ch02.undilateVec (-(k : ℤ)) x = triadicDilateVec k x := by
    ext r
    simp [Ch02.undilateVec, Ch02.triadicDilationFactor, triadicDilateVec,
      smul_eq_mul, zpow_neg]
  simp [rescaleCoeffField, Ch02.dilateCoeffField, hvec]

/-- `scaleNormalizedLaw` agrees with the pre-existing probability-layer
`rescaledLaw`. -/
theorem scaleNormalizedLaw_eq_rescaledLaw {d : ℕ} (k : ℕ) (P : CoeffLaw d) :
    scaleNormalizedLaw k P = rescaledLaw P k := by
  rw [scaleNormalizedLaw, rescaledLaw, ← rescaleCoeffField_eq_dilateCoeffField_neg_nat k]

/-- Measurability of the coefficient-field map defining `scaleNormalizedLaw`. -/
theorem measurable_dilateCoeffField_neg_nat {d : ℕ} (k : ℕ) :
    Measurable (Ch02.dilateCoeffField (d := d) (-(k : ℤ))) := by
  rw [← rescaleCoeffField_eq_dilateCoeffField_neg_nat k]
  exact measurable_rescaleCoeffField k

/-- A scale-normalized probability law is again a probability law. -/
theorem isProbabilityMeasure_scaleNormalizedLaw {d : ℕ} (k : ℕ) (P : CoeffLaw d)
    [IsProbabilityMeasure P] :
    IsProbabilityMeasure (scaleNormalizedLaw k P) := by
  rw [scaleNormalizedLaw_eq_rescaledLaw]
  exact Measure.isProbabilityMeasure_map (measurable_rescaleCoeffField (d := d) k).aemeasurable

/-- Bochner integral under a scale-normalized law. -/
theorem integral_scaleNormalizedLaw {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] {P : CoeffLaw d} (k : ℕ)
    (X : CoeffField d → E)
    (hX : AEStronglyMeasurable X (scaleNormalizedLaw k P)) :
    ∫ a, X a ∂scaleNormalizedLaw k P =
      ∫ a, X (Ch02.dilateCoeffField (-(k : ℤ)) a) ∂P := by
  rw [scaleNormalizedLaw]
  exact MeasureTheory.integral_map
    (measurable_dilateCoeffField_neg_nat (d := d) k).aemeasurable hX

/-- Integrability under a scale-normalized law is integrability after
composing with the defining dilation. -/
theorem integrable_scaleNormalizedLaw_iff {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] {P : CoeffLaw d} (k : ℕ)
    {X : CoeffField d → E}
    (hX : AEStronglyMeasurable X (scaleNormalizedLaw k P)) :
    Integrable X (scaleNormalizedLaw k P) ↔
      Integrable (fun a => X (Ch02.dilateCoeffField (-(k : ℤ)) a)) P := by
  simpa [scaleNormalizedLaw, Function.comp] using
    (integrable_map_measure
      (μ := P) (f := Ch02.dilateCoeffField (d := d) (-(k : ℤ))) (g := X)
      hX (measurable_dilateCoeffField_neg_nat (d := d) k).aemeasurable)

/-- Pullback by triadic coefficient-field rescaling sends local information on
`U` to local information on the dilated set. -/
theorem measurable_rescaleCoeffField_localSigma {d : ℕ}
    (k : ℕ) (U : Set (Vec d)) :
    @Measurable (CoeffField d) (CoeffField d)
      (localSigma (triadicDilateSet k U)) (localSigma U)
      (rescaleCoeffField k) := by
  show @Measurable (CoeffField d) (CoeffField d)
    (Homogenization.LocalSigma (triadicDilateSet k U)) (Homogenization.LocalSigma U)
    (rescaleCoeffField k)
  refine @measurable_generateFrom (CoeffField d) (CoeffField d)
    (Homogenization.LocalSigma (triadicDilateSet k U))
    {s | IsLocalEvent U s} (rescaleCoeffField k) ?_
  intro s hs
  have hpre : @MeasurableSet (CoeffField d)
      (Homogenization.LocalSigma (triadicDilateSet k U))
      ((rescaleCoeffField k) ⁻¹' s) :=
    MeasurableSpace.measurableSet_generateFrom
      (by
        intro a b hab
        exact hs (by
        intro x hx
        exact hab (triadicDilateVec k x) (triadicDilateVec_mem_triadicDilateSet k hx)))
  exact hpre

private theorem isLocalObservable_restrictCoeffField {d : ℕ}
    (U : Set (Vec d)) :
    IsLocalObservable U (restrictCoeffField (d := d) U) := by
  intro a b hab
  exact restrictCoeffField_eq_of_forall_mem_eq hab

/-- Pullback by triadic coefficient-field rescaling sends restriction-local
information on `U` to restriction-local information on the dilated set. -/
theorem measurable_rescaleCoeffField_restrictionSigma {d : ℕ}
    (k : ℕ) (U : Set (Vec d)) :
    @Measurable (CoeffField d) (CoeffField d)
      (RestrictionSigma (triadicDilateSet k U)) (RestrictionSigma U)
      (rescaleCoeffField k) := by
  rw [measurable_iff_comap_le, RestrictionSigma, MeasurableSpace.comap_comp]
  change MeasurableSpace.comap
      (fun a : CoeffField d => restrictCoeffField U (rescaleCoeffField k a))
      (instMeasurableSpaceCoeffField d) ≤ RestrictionSigma (triadicDilateSet k U)
  have hmeas :
      @Measurable (CoeffField d) (CoeffField d)
        (RestrictionSigma (triadicDilateSet k U)) (instMeasurableSpaceCoeffField d)
        (fun a => restrictCoeffField U (rescaleCoeffField k a)) := by
    exact measurable_of_isLocalObservable_restrictionSigma
      ((measurable_restrictCoeffField (d := d) U).comp
        (measurable_rescaleCoeffField (d := d) k))
      (isLocalObservable_comp_rescaleCoeffField (d := d) (U := U) k
        (isLocalObservable_restrictCoeffField (d := d) U))
  exact hmeas.comap_le

private theorem localTestObservable_dilateCoeffField_int_eq_const_mul
    {d : ℕ} (n : ℤ) (e e' : Vec d) (φ : Vec d → ℝ) (a : CoeffField d) :
    localTestObservable e e' φ (Ch02.dilateCoeffField n a) =
      (((Ch02.triadicDilationFactor n)⁻¹) ^ d)⁻¹ *
        localTestObservable e e'
          (fun y : Vec d => φ (((Ch02.triadicDilationFactor n)⁻¹)⁻¹ • y)) a := by
  let q : ℝ := (Ch02.triadicDilationFactor n)⁻¹
  have hq : 0 < q := inv_pos.mpr (Ch02.triadicDilationFactor_pos n)
  let f : Vec d → ℝ := fun y => vecDot e' (matVecMul (a y) e) * φ (q⁻¹ • y)
  have hcv := Ch01.setIntegral_comp_smul_of_pos
    (d := d) (E := ℝ) (r := q) hq Set.univ f
  have huniv : q • (Set.univ : Set (Vec d)) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      refine ⟨q⁻¹ • y, trivial, ?_⟩
      ext i
      simp [Pi.smul_apply, smul_eq_mul, hq.ne']
  have hundilate : ∀ x : Vec d, Ch02.undilateVec n x = q • x := by
    intro x
    ext i
    simp [Ch02.undilateVec, q, Pi.smul_apply, smul_eq_mul]
  unfold localTestObservable
  calc
    ∫ x, (vecDot e' (matVecMul (Ch02.dilateCoeffField n a x) e) * φ x) ∂volume
        = ∫ x, f (q • x) ∂volume := by
          apply integral_congr_ae
          filter_upwards with x
          have hqx : q⁻¹ • (q • x) = x := by
            ext i
            simp [Pi.smul_apply, smul_eq_mul, hq.ne']
          simp [f, Ch02.dilateCoeffField, hundilate x, hqx]
    _ = ∫ x in (Set.univ : Set (Vec d)), f (q • x) ∂volume := by simp
    _ = (q ^ d)⁻¹ • ∫ y in q • (Set.univ : Set (Vec d)), f y ∂volume := hcv
    _ = (q ^ d)⁻¹ *
          ∫ y, (vecDot e' (matVecMul (a y) e) *
            φ (((Ch02.triadicDilationFactor n)⁻¹)⁻¹ • y)) ∂volume := by
          simp [f, q, huniv]

private theorem localFiniteTestObservable_dilateCoeffField_int_eq {d : ℕ} {ι : Type}
    (n : ℤ) (I : Finset ι) (e e' : ι → Vec d) (φ : ι → Vec d → ℝ)
    (a : CoeffField d) :
    localFiniteTestObservable I e e' φ (Ch02.dilateCoeffField n a) =
      localFiniteTestObservable I e e'
        (fun k y => (((Ch02.triadicDilationFactor n)⁻¹) ^ d)⁻¹ *
          φ k (((Ch02.triadicDilationFactor n)⁻¹)⁻¹ • y)) a := by
  let q : ℝ := (Ch02.triadicDilationFactor n)⁻¹
  have hq : 0 < q := inv_pos.mpr (Ch02.triadicDilationFactor_pos n)
  let c : ℝ := (q ^ d)⁻¹
  let f : Vec d → ℝ := fun y =>
    ∑ k ∈ I, vecDot (e' k) (matVecMul (a y) (e k)) * φ k (q⁻¹ • y)
  have hcv := Ch01.setIntegral_comp_smul_of_pos
    (d := d) (E := ℝ) (r := q) hq Set.univ f
  have huniv : q • (Set.univ : Set (Vec d)) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      refine ⟨q⁻¹ • y, trivial, ?_⟩
      ext i
      simp [Pi.smul_apply, smul_eq_mul, hq.ne']
  have hundilate : ∀ x : Vec d, Ch02.undilateVec n x = q • x := by
    intro x
    ext i
    simp [Ch02.undilateVec, q, Pi.smul_apply, smul_eq_mul]
  unfold localFiniteTestObservable
  calc
    ∫ x, (∑ k ∈ I,
        vecDot (e' k) (matVecMul (Ch02.dilateCoeffField n a x) (e k)) * φ k x) ∂volume
        = ∫ x, f (q • x) ∂volume := by
          apply integral_congr_ae
          filter_upwards with x
          have hqx : q⁻¹ • (q • x) = x := by
            ext i
            simp [Pi.smul_apply, smul_eq_mul, hq.ne']
          simp [f, Ch02.dilateCoeffField, hundilate x, hqx]
    _ = ∫ x in (Set.univ : Set (Vec d)), f (q • x) ∂volume := by simp
    _ = (q ^ d)⁻¹ • ∫ y in q • (Set.univ : Set (Vec d)), f y ∂volume := hcv
    _ = c * ∫ y, f y ∂volume := by simp [c, huniv]
    _ = ∫ y, c * f y ∂volume := by
          exact (integral_const_mul c f).symm
    _ = ∫ y, (∑ k ∈ I, vecDot (e' k) (matVecMul (a y) (e k)) *
        ((((Ch02.triadicDilationFactor n)⁻¹) ^ d)⁻¹ *
          φ k (((Ch02.triadicDilationFactor n)⁻¹)⁻¹ • y))) ∂volume := by
          apply integral_congr_ae
          filter_upwards with y
          simp [f, c, q, Finset.mul_sum]
          ring_nf

private theorem measurable_dilateCoeffField_int {d : ℕ} (n : ℤ) :
    Measurable (Ch02.dilateCoeffField (d := d) n) := by
  refine measurable_coeffField_to_ambient ?_ (fun V hV => ?_)
  · refine measurable_pi_iff.2 fun x => measurable_pi_iff.2 fun i =>
      measurable_pi_iff.2 fun j => ?_
    exact measurable_coeffField_entry (d := d) (Ch02.undilateVec n x) i j
  · refine measurable_localSigma_of_local (T := Ch02.dilateCoeffField n) ?_ V hV
    intro W hW
    refine ⟨{y : Vec d | ∃ x ∈ W, y = Ch02.undilateVec n x}, ?_, ?_⟩
    · have hcont : Continuous (Ch02.undilateVec (d := d) n) := by
        change Continuous fun x : Fin d → ℝ =>
          fun i => (Ch02.triadicDilationFactor n)⁻¹ * x i
        exact continuous_pi fun i => continuous_const.mul (continuous_apply i)
      simpa [Set.image, eq_comm] using
        isBounded_image_of_continuous_vec hcont hW
    intro a b hab x hxW
    have hx_pre : Ch02.undilateVec n x ∈
        {y : Vec d | ∃ x ∈ W, y = Ch02.undilateVec n x} :=
      ⟨x, hxW, rfl⟩
    simp [Ch02.dilateCoeffField, hab (Ch02.undilateVec n x) hx_pre]

private noncomputable def rescaleCoeffFieldMeasurableEquiv {d : ℕ} (k : ℕ) :
    CoeffField d ≃ᵐ CoeffField d where
  toEquiv :=
    { toFun := rescaleCoeffField k
      invFun := Ch02.dilateCoeffField (k : ℤ)
      left_inv := by
        intro a
        funext x i j
        have hvec : triadicDilateVec k (Ch02.undilateVec (k : ℤ) x) = x := by
          ext l
          simp [triadicDilateVec, Ch02.undilateVec, Ch02.triadicDilationFactor,
            Pi.smul_apply, smul_eq_mul]
        simp [rescaleCoeffField, Ch02.dilateCoeffField, hvec]
      right_inv := by
        intro a
        funext x i j
        have hvec : Ch02.undilateVec (k : ℤ) (triadicDilateVec k x) = x := by
          ext l
          simp [triadicDilateVec, Ch02.undilateVec, Ch02.triadicDilationFactor,
            Pi.smul_apply, smul_eq_mul]
        simp [rescaleCoeffField, Ch02.dilateCoeffField, hvec] }
  measurable_toFun := measurable_rescaleCoeffField k
  measurable_invFun := measurable_dilateCoeffField_int (d := d) (k : ℤ)

private theorem nullMeasurableSet_map_of_preimage_measurableEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} (e : α ≃ᵐ β) {s : Set β}
    (hs : NullMeasurableSet (e ⁻¹' s) μ) :
    NullMeasurableSet s (Measure.map e μ) := by
  rcases hs with ⟨t, ht, hst⟩
  refine ⟨e '' t, e.measurableEmbedding.measurableSet_image' ht, ?_⟩
  rw [Filter.EventuallyEq, e.measurableEmbedding.ae_map_iff]
  filter_upwards [hst] with a ha
  apply propext
  constructor
  · intro hs_ea
    exact ⟨a, ha.mp hs_ea, rfl⟩
  · rintro ⟨b, hb, hbeq⟩
    have hb_eq : b = a := e.injective hbeq
    subst hb_eq
    exact ha.mpr hb

namespace LocalObservableLawCarrier

/-- Local-test null-measurability is preserved by triadic scale-normalization. -/
theorem scaleNormalized {d : ℕ} {P : CoeffLaw d}
    (hP : LocalObservableLawCarrier P) (k : ℕ) :
    LocalObservableLawCarrier (scaleNormalizedLaw k P) := by
  constructor
  intro U hU s hs
  let e := rescaleCoeffFieldMeasurableEquiv (d := d) k
  have hpre_meas :
      @MeasurableSet (CoeffField d) (localSigma (triadicDilateSet k U))
        ((rescaleCoeffField k) ⁻¹' s) := by
    exact hs.preimage (measurable_rescaleCoeffField_localSigma k U)
  have hpre_null : NullMeasurableSet ((rescaleCoeffField k) ⁻¹' s) P :=
    hP.nullMeasurable_localSigma (triadicDilateSet k U)
      (isBounded_triadicDilateSet k hU) _ hpre_meas
  have hmap : NullMeasurableSet s (Measure.map (rescaleCoeffField k) P) := by
    simpa [e] using
      nullMeasurableSet_map_of_preimage_measurableEquiv (μ := P) e (s := s) hpre_null
  simpa [scaleNormalizedLaw_eq_rescaledLaw, rescaledLaw] using hmap

end LocalObservableLawCarrier

private theorem indep_map_measurableEquiv
    {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    {μ : Measure α} (e : α ≃ᵐ β) {m1 m2 : MeasurableSpace β}
    (h : @ProbabilityTheory.Indep α
      (MeasurableSpace.comap (fun x : α => e x) m1)
      (MeasurableSpace.comap (fun x : α => e x) m2) mα μ) :
    @ProbabilityTheory.Indep β m1 m2 mβ
      (@Measure.map α β mα mβ (fun x : α => e x) μ) := by
  refine (ProbabilityTheory.Indep_iff
    (m₁ := m1) (m₂ := m2) (_mΩ := mβ)
    (μ := (@Measure.map α β mα mβ (fun x : α => e x) μ))).2 ?_
  intro s t hs ht
  have hemb : @MeasurableEmbedding α β mα mβ (fun x : α => e x) := by
    exact @MeasurableEquiv.measurableEmbedding α β mα mβ e
  have h_ind := (ProbabilityTheory.Indep_iff
    (m₁ := MeasurableSpace.comap (fun x : α => e x) m1)
    (m₂ := MeasurableSpace.comap (fun x : α => e x) m2)
    (_mΩ := mα) (μ := μ)).1 h
  have hspre : @MeasurableSet α
      (MeasurableSpace.comap (fun x : α => e x) m1)
      ((fun x : α => e x) ⁻¹' s) := by
    exact ⟨s, hs, rfl⟩
  have htpre : @MeasurableSet α
      (MeasurableSpace.comap (fun x : α => e x) m2)
      ((fun x : α => e x) ⁻¹' t) := by
    exact ⟨t, ht, rfl⟩
  have hst := h_ind ((fun x : α => e x) ⁻¹' s)
    ((fun x : α => e x) ⁻¹' t) hspre htpre
  have hmap_inter :
      (@Measure.map α β mα mβ (fun x : α => e x) μ) (s ∩ t) =
        μ ((fun x : α => e x) ⁻¹' (s ∩ t)) := by
    exact @MeasurableEmbedding.map_apply α β mα mβ
      (fun x : α => e x) hemb μ (s ∩ t)
  have hmap_s :
      (@Measure.map α β mα mβ (fun x : α => e x) μ) s =
        μ ((fun x : α => e x) ⁻¹' s) := by
    exact @MeasurableEmbedding.map_apply α β mα mβ
      (fun x : α => e x) hemb μ s
  have hmap_t :
      (@Measure.map α β mα mβ (fun x : α => e x) μ) t =
        μ ((fun x : α => e x) ⁻¹' t) := by
    exact @MeasurableEmbedding.map_apply α β mα mβ
      (fun x : α => e x) hemb μ t
  calc
    (@Measure.map α β mα mβ (fun x : α => e x) μ) (s ∩ t)
        = μ ((fun x : α => e x) ⁻¹' (s ∩ t)) := hmap_inter
    _ = μ (((fun x : α => e x) ⁻¹' s) ∩
          ((fun x : α => e x) ⁻¹' t)) := by rfl
    _ = μ ((fun x : α => e x) ⁻¹' s) *
          μ ((fun x : α => e x) ⁻¹' t) := hst
    _ = (@Measure.map α β mα mβ (fun x : α => e x) μ) s *
          (@Measure.map α β mα mβ (fun x : α => e x) μ) t := by
          rw [hmap_s, hmap_t]

private theorem dist_triadicDilateVec {d : ℕ} (k : ℕ) (x y : Vec d) :
    dist (triadicDilateVec k x) (triadicDilateVec k y) =
      ((3 : ℝ) ^ k) * dist x y := by
  let r : ℝ := (3 : ℝ) ^ k
  have hr : 0 ≤ r := by positivity
  have hsub : triadicDilateVec k x - triadicDilateVec k y = r • (x - y) := by
    ext i
    simp only [triadicDilateVec, r, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [dist_eq_norm, dist_eq_norm, hsub, norm_smul_of_nonneg hr]

private theorem AreUnitSeparated.triadicDilateSet {d : ℕ} {U V : Set (Vec d)}
    (hUV : AreUnitSeparated U V) (k : ℕ) :
    AreUnitSeparated (triadicDilateSet k U) (triadicDilateSet k V) := by
  intro x y hx hy
  rcases hx with ⟨x0, hx0, rfl⟩
  rcases hy with ⟨y0, hy0, rfl⟩
  rw [dist_triadicDilateVec]
  have hsep : 1 ≤ dist x0 y0 := hUV hx0 hy0
  have hscale : 1 ≤ ((3 : ℝ) ^ k) := by
    exact (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3) : 1 ≤ (3 : ℝ) ^ k)
  have hmul : (1 : ℝ) * 1 ≤ ((3 : ℝ) ^ k) * dist x0 y0 := by
    exact mul_le_mul hscale hsep zero_le_one (by positivity)
  simpa using hmul

namespace UnitRangeDependentLaw

/-- Unit-range dependence is preserved by triadic scale-normalization. -/
theorem scaleNormalized {d : ℕ} {P : CoeffLaw d}
    (hP : UnitRangeDependentLaw P) (k : ℕ) :
    UnitRangeDependentLaw (scaleNormalizedLaw k P) := by
  intro U V hUV
  let e := rescaleCoeffFieldMeasurableEquiv (d := d) k
  have hIndepDilated : ProbabilityTheory.Indep
      (RestrictionSigma (triadicDilateSet k U))
      (RestrictionSigma (triadicDilateSet k V)) P :=
    hP (triadicDilateSet k U) (triadicDilateSet k V)
      (AreUnitSeparated.triadicDilateSet hUV k)
  have hU_le : MeasurableSpace.comap
      (fun a : CoeffField d => rescaleCoeffField k a) (RestrictionSigma U) ≤
        RestrictionSigma (triadicDilateSet k U) := by
    exact (measurable_rescaleCoeffField_restrictionSigma (d := d) k U).comap_le
  have hV_le : MeasurableSpace.comap
      (fun a : CoeffField d => rescaleCoeffField k a) (RestrictionSigma V) ≤
        RestrictionSigma (triadicDilateSet k V) := by
    exact (measurable_rescaleCoeffField_restrictionSigma (d := d) k V).comap_le
  have hComap : ProbabilityTheory.Indep
      (MeasurableSpace.comap
        (fun a : CoeffField d => rescaleCoeffField k a) (RestrictionSigma U))
      (MeasurableSpace.comap
        (fun a : CoeffField d => rescaleCoeffField k a) (RestrictionSigma V)) P :=
    ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left hIndepDilated hU_le) hV_le
  have hmap := indep_map_measurableEquiv (μ := P) e
    (m1 := RestrictionSigma U) (m2 := RestrictionSigma V) hComap
  simpa [scaleNormalizedLaw_eq_rescaledLaw, rescaledLaw, e] using hmap

end UnitRangeDependentLaw

private theorem dilatedCoeffFamily_coeffOn_ae_eq_rescaleCoeffField
    {d : ℕ} {a : CoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (k : ℕ) (Q : TriadicCube d) :
    ((Ch02.TriadicCoeffFamily.dilate (-(k : ℤ))
        (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)).coeffOn Q).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet Q)]
        rescaleCoeffField k a := by
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let Qsrc : TriadicCube d := Ch02.dilateCube (k : ℤ) Q
  have htarget : Ch02.dilateCube (-(k : ℤ)) Qsrc = Q := by
    simpa [Qsrc] using Ch02.dilateCube_neg_dilateCube (k : ℤ) Q
  have hD :=
    Ch02.TriadicCoeffFamily.isDilation_dilate (-(k : ℤ)) F Qsrc
  have hcoeff' :
      ((Ch02.TriadicCoeffFamily.dilate (-(k : ℤ)) F).coeffOn
          (Ch02.dilateCube (-(k : ℤ)) Qsrc)).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet Q)]
          Ch02.dilateCoeffField (-(k : ℤ)) a := by
    simpa [F, Qsrc, htarget] using hD.coeff_ae_eq
  have hcast := hcoeff'
  rw [htarget] at hcast
  simpa [F, rescaleCoeffField_eq_dilateCoeffField_neg_nat k] using hcast

namespace AELocallyUniformlyEllipticField

/-- Locally a.e.-uniform ellipticity is preserved by triadic rescaling of the
ambient coefficient field. -/
theorem of_rescaleCoeffField {d : ℕ} {a : CoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (k : ℕ) :
    AELocallyUniformlyEllipticField (Homogenization.rescaleCoeffField k a) := by
  intro Q
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let B : Ch02.TriadicCoeffFamily d := Ch02.TriadicCoeffFamily.dilate (-(k : ℤ)) F
  let bQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := B.coeffOn Q
  have hcoeff :
      bQ.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet Q)]
        Homogenization.rescaleCoeffField k a := by
    simpa [bQ, B] using dilatedCoeffFamily_coeffOn_ae_eq_rescaleCoeffField ha k Q
  refine ⟨bQ.lam, bQ.Lam, bQ.lam_pos, bQ.lam_le_Lam, ?_⟩
  refine ⟨measurableSet_openCubeSet Q, ?_, ?_⟩
  · intro i j
    refine (bQ.aeStronglyMeasurable i j).congr ?_
    filter_upwards [hcoeff] with x hx
    by_cases hxQ : x ∈ openCubeSet Q
    · simp [restrictCoeffField, hxQ, hx]
    · simp [restrictCoeffField, hxQ]
  · filter_upwards [bQ.aeElliptic, hcoeff] with x hxEll hx
    simpa [hx] using hxEll

end AELocallyUniformlyEllipticField

namespace AELocallyUniformlyEllipticLaw

/-- A locally a.e.-uniformly elliptic law remains so after triadic
scale-normalization. -/
theorem scaleNormalized {d : ℕ} {P : CoeffLaw d}
    (hP : AELocallyUniformlyEllipticLaw P) (k : ℕ) :
    AELocallyUniformlyEllipticLaw (scaleNormalizedLaw k P) := by
  rw [scaleNormalizedLaw_eq_rescaledLaw, rescaledLaw]
  exact ((rescaleCoeffFieldMeasurableEquiv (d := d) k).measurableEmbedding.ae_map_iff).2 <| by
    filter_upwards [hP] with a ha
    exact ha.of_rescaleCoeffField k

end AELocallyUniformlyEllipticLaw

namespace LawCarrier

/-- The Chapter 4 law carrier is preserved by triadic scale-normalization. -/
theorem scaleNormalized {d : ℕ} {P : CoeffLaw d}
    (hP : LawCarrier P) (k : ℕ) :
    LawCarrier (scaleNormalizedLaw k P) where
  isProbability := by
    letI : IsProbabilityMeasure P := hP.isProbability
    exact isProbabilityMeasure_scaleNormalizedLaw k P
  ae_locally_uniformly_elliptic :=
    hP.ae_locally_uniformly_elliptic.scaleNormalized k
  local_observable_measurable :=
    hP.local_observable_measurable.scaleNormalized k
  aee_quantitative_slice_measurable :=
    hP.aee_quantitative_slice_measurable

end LawCarrier

theorem triadicCoeffFamily_rescaleCoeffField_aeeq_dilate
    {d : ℕ} {a : CoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (k : ℕ) :
    Ch02.TriadicCoeffFamily.AEEq
      (triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (rescaleCoeffField k a) (ha.of_rescaleCoeffField k))
      (Ch02.TriadicCoeffFamily.dilate (-(k : ℤ))
        (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)) := by
  intro Q
  change
    rescaleCoeffField k a
      =ᵐ[volumeMeasureOn (Ch02.cubeDomain Q : Set (Vec d))]
        ((Ch02.TriadicCoeffFamily.dilate (-(k : ℤ))
          (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)).coeffOn Q).toCoeffField
  simpa [Ch02.cubeDomain_coe] using
    (dilatedCoeffFamily_coeffOn_ae_eq_rescaleCoeffField ha k Q).symm

theorem LambdaSqCoeffField_rescaleCoeffField_of_aelocallyUniformlyElliptic
    {d : ℕ} [NeZero d] {a : CoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (k : ℕ)
    (Q : TriadicCube d) (s : ℝ) (q : Ch02.MultiscaleExponent) :
    LambdaSqCoeffField Q s q (rescaleCoeffField k a) =
      LambdaSqCoeffField (Ch02.dilateCube (k : ℤ) Q) s q a := by
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let G : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField
      (rescaleCoeffField k a) (ha.of_rescaleCoeffField k)
  let B : Ch02.TriadicCoeffFamily d := Ch02.TriadicCoeffFamily.dilate (-(k : ℤ)) F
  let Qsrc : TriadicCube d := Ch02.dilateCube (k : ℤ) Q
  have htarget : Ch02.dilateCube (-(k : ℤ)) Qsrc = Q := by
    simpa [Qsrc] using Ch02.dilateCube_neg_dilateCube (k : ℤ) Q
  have hGB : Ch02.TriadicCoeffFamily.AEEq G B := by
    simpa [G, B, F] using triadicCoeffFamily_rescaleCoeffField_aeeq_dilate ha k
  have hAEEq := Ch02.LambdaSq_eq_ofAEEq hGB Q s q
  have hdilate :=
    Ch02.LambdaSq_dilate
      (Ch02.TriadicCoeffFamily.isDilation_dilate (-(k : ℤ)) F) Qsrc s q
  calc
    LambdaSqCoeffField Q s q (rescaleCoeffField k a)
        = Ch02.LambdaSq Q s q G := by
          simp [LambdaSqCoeffField, G, ha.of_rescaleCoeffField k]
    _ = Ch02.LambdaSq Q s q B := hAEEq
    _ = Ch02.LambdaSq Qsrc s q F := by
          simpa [Qsrc, htarget, B] using hdilate
    _ = LambdaSqCoeffField Qsrc s q a := by
          simp [LambdaSqCoeffField, F, ha]

theorem lambdaSqCoeffField_rescaleCoeffField_of_aelocallyUniformlyElliptic
    {d : ℕ} [NeZero d] {a : CoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (k : ℕ)
    (Q : TriadicCube d) (s : ℝ) (q : Ch02.MultiscaleExponent) :
    lambdaSqCoeffField Q s q (rescaleCoeffField k a) =
      lambdaSqCoeffField (Ch02.dilateCube (k : ℤ) Q) s q a := by
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let G : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField
      (rescaleCoeffField k a) (ha.of_rescaleCoeffField k)
  let B : Ch02.TriadicCoeffFamily d := Ch02.TriadicCoeffFamily.dilate (-(k : ℤ)) F
  let Qsrc : TriadicCube d := Ch02.dilateCube (k : ℤ) Q
  have htarget : Ch02.dilateCube (-(k : ℤ)) Qsrc = Q := by
    simpa [Qsrc] using Ch02.dilateCube_neg_dilateCube (k : ℤ) Q
  have hGB : Ch02.TriadicCoeffFamily.AEEq G B := by
    simpa [G, B, F] using triadicCoeffFamily_rescaleCoeffField_aeeq_dilate ha k
  have hAEEq := Ch02.lambdaSq_eq_ofAEEq hGB Q s q
  have hdilate :=
    Ch02.lambdaSq_dilate
      (Ch02.TriadicCoeffFamily.isDilation_dilate (-(k : ℤ)) F) Qsrc s q
  calc
    lambdaSqCoeffField Q s q (rescaleCoeffField k a)
        = Ch02.lambdaSq Q s q G := by
          simp [lambdaSqCoeffField, G, ha.of_rescaleCoeffField k]
    _ = Ch02.lambdaSq Q s q B := hAEEq
    _ = Ch02.lambdaSq Qsrc s q F := by
          simpa [Qsrc, htarget, B] using hdilate
    _ = lambdaSqCoeffField Qsrc s q a := by
          simp [lambdaSqCoeffField, F, ha]

@[simp] theorem dilateCube_originCube_nat {d : ℕ} (k m : ℕ) :
    Ch02.dilateCube (k : ℤ) (originCube d (m : ℤ)) =
      originCube d ((k + m : ℕ) : ℤ) := by
  simp [Ch02.dilateCube, originCube, add_comm]

theorem LambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
    {d : ℕ} [NeZero d] {a : CoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (k m : ℕ)
    (s : ℝ) (q : Ch02.MultiscaleExponent) :
    LambdaSqCoeffField (originCube d (m : ℤ)) s q (rescaleCoeffField k a) =
      LambdaSqCoeffField (originCube d ((k + m : ℕ) : ℤ)) s q a := by
  simpa using
    LambdaSqCoeffField_rescaleCoeffField_of_aelocallyUniformlyElliptic
      ha k (originCube d (m : ℤ)) s q

theorem lambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
    {d : ℕ} [NeZero d] {a : CoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (k m : ℕ)
    (s : ℝ) (q : Ch02.MultiscaleExponent) :
    lambdaSqCoeffField (originCube d (m : ℤ)) s q (rescaleCoeffField k a) =
      lambdaSqCoeffField (originCube d ((k + m : ℕ) : ℤ)) s q a := by
  simpa using
    lambdaSqCoeffField_rescaleCoeffField_of_aelocallyUniformlyElliptic
      ha k (originCube d (m : ℤ)) s q

/-- The ambient coarse block matrix rescales by shifting the origin-cube
scale. -/
theorem coarseBlockMatrix_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
    {d : ℕ} [NeZero d] {a : CoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (k m : ℕ) :
    coarseBlockMatrix (cubeSet (originCube d (m : ℤ))) (rescaleCoeffField k a) =
      coarseBlockMatrix (cubeSet (originCube d ((k + m : ℕ) : ℤ))) a := by
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let G : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField
      (rescaleCoeffField k a) (ha.of_rescaleCoeffField k)
  let B : Ch02.TriadicCoeffFamily d := Ch02.TriadicCoeffFamily.dilate (-(k : ℤ)) F
  let Q : TriadicCube d := originCube d (m : ℤ)
  let Qsrc : TriadicCube d := Ch02.dilateCube (k : ℤ) Q
  have htarget : Ch02.dilateCube (-(k : ℤ)) Qsrc = Q := by
    simpa [Qsrc] using Ch02.dilateCube_neg_dilateCube (k : ℤ) Q
  have hGB : Ch02.TriadicCoeffFamily.AEEq G B := by
    simpa [G, B, F] using triadicCoeffFamily_rescaleCoeffField_aeeq_dilate ha k
  have hAEEq := Ch02.coarseBlockMatrix_eq_ofAEEq (hGB Q)
  have hdilate :=
    Ch02.coarseBlockMatrix_dilate
      (Ch02.TriadicCoeffFamily.isDilation_dilate (-(k : ℤ)) F Qsrc)
  have hdilate' :
      Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (B.coeffOn Q) =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Qsrc) (F.coeffOn Qsrc) := by
    rw [htarget] at hdilate
    simpa [B] using hdilate
  calc
    coarseBlockMatrix (cubeSet (originCube d (m : ℤ))) (rescaleCoeffField k a)
        = Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (G.coeffOn Q) := by
          simpa [Q, G] using
            LawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
              (ha.of_rescaleCoeffField k) Q
    _ = Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (B.coeffOn Q) := hAEEq
    _ = Ch02.coarseBlockMatrix (Ch02.cubeDomain Qsrc) (F.coeffOn Qsrc) := hdilate'
    _ = coarseBlockMatrix (cubeSet Qsrc) a :=
          (LawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
            ha Qsrc).symm
    _ = coarseBlockMatrix (cubeSet (originCube d ((k + m : ℕ) : ℤ))) a := by
          simp [Qsrc, Q]
/-- Scalar response observables rescale by shifting the origin-cube scale. -/
theorem responseJObservableCubeSet_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
    {d : ℕ} [NeZero d] {a : CoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (k m : ℕ) (p q : Vec d) :
    responseJObservableCubeSet (originCube d (m : ℤ)) p q (rescaleCoeffField k a) =
      responseJObservableCubeSet (originCube d ((k + m : ℕ) : ℤ)) p q a := by
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let G : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField
      (rescaleCoeffField k a) (ha.of_rescaleCoeffField k)
  let B : Ch02.TriadicCoeffFamily d := Ch02.TriadicCoeffFamily.dilate (-(k : ℤ)) F
  let Q : TriadicCube d := originCube d (m : ℤ)
  let Qsrc : TriadicCube d := Ch02.dilateCube (k : ℤ) Q
  have htarget : Ch02.dilateCube (-(k : ℤ)) Qsrc = Q := by
    simpa [Qsrc] using Ch02.dilateCube_neg_dilateCube (k : ℤ) Q
  have hGB : Ch02.TriadicCoeffFamily.AEEq G B := by
    simpa [G, B, F] using triadicCoeffFamily_rescaleCoeffField_aeeq_dilate ha k
  have hAEEq : Ch02.responseJ (Ch02.cubeDomain Q) (G.coeffOn Q) p q =
      Ch02.responseJ (Ch02.cubeDomain Q) (B.coeffOn Q) p q :=
    Ch02.responseJ_eq_ofAEEq (hGB Q) p q
  have hdilate :=
    Ch02.responseJ_dilate
      (Ch02.TriadicCoeffFamily.isDilation_dilate (-(k : ℤ)) F Qsrc) p q
  have hdilate' :
      Ch02.responseJ (Ch02.cubeDomain Q) (B.coeffOn Q) p q =
        Ch02.responseJ (Ch02.cubeDomain Qsrc) (F.coeffOn Qsrc) p q := by
    rw [htarget] at hdilate
    simpa [B] using hdilate
  calc
    responseJObservableCubeSet (originCube d (m : ℤ)) p q (rescaleCoeffField k a)
        = Ch02.responseJ (Ch02.cubeDomain Q) (G.coeffOn Q) p q := by
          symm
          calc
            Ch02.responseJ (Ch02.cubeDomain Q) (G.coeffOn Q) p q =
                ResponseJ (openCubeSet Q) p q (rescaleCoeffField k a) := by
                  simpa [G, Q, triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
                    coeffOnOfAEEllipticOn_toCoeffField, Ch02.cubeDomain_coe] using
                    Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ
                      (Ch02.cubeDomain Q) (G.coeffOn Q) p q
            _ = responseJObservableCubeSet (originCube d (m : ℤ)) p q
                  (rescaleCoeffField k a) := by
                  rw [← responseJ_cubeSet_eq_openCubeSet_of_triadicCube Q p q
                    (rescaleCoeffField k a)]
                  rfl
    _ = Ch02.responseJ (Ch02.cubeDomain Q) (B.coeffOn Q) p q := hAEEq
    _ = Ch02.responseJ (Ch02.cubeDomain Qsrc) (F.coeffOn Qsrc) p q := hdilate'
    _ = responseJObservableCubeSet Qsrc p q a := by
          calc
            Ch02.responseJ (Ch02.cubeDomain Qsrc) (F.coeffOn Qsrc) p q =
                ResponseJ (openCubeSet Qsrc) p q a := by
                  simpa [F, Qsrc, triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
                    coeffOnOfAEEllipticOn_toCoeffField, Ch02.cubeDomain_coe] using
                    Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ
                      (Ch02.cubeDomain Qsrc) (F.coeffOn Qsrc) p q
            _ = responseJObservableCubeSet Qsrc p q a := by
                  rw [← responseJ_cubeSet_eq_openCubeSet_of_triadicCube Qsrc p q a]
                  rfl
    _ = responseJObservableCubeSet (originCube d ((k + m : ℕ) : ℤ)) p q a := by
          simp [Qsrc, Q]

/-- Scalar response observables under the dilation defining `scaleNormalizedLaw`. -/
theorem responseJObservableCubeSet_originCube_dilateCoeffField_neg_nat_of_aelocallyUniformlyElliptic
    {d : ℕ} [NeZero d] {a : CoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (k m : ℕ) (p q : Vec d) :
    responseJObservableCubeSet (originCube d (m : ℤ)) p q
        (Ch02.dilateCoeffField (-(k : ℤ)) a) =
      responseJObservableCubeSet (originCube d ((k + m : ℕ) : ℤ)) p q a := by
  rw [← rescaleCoeffField_eq_dilateCoeffField_neg_nat]
  exact responseJObservableCubeSet_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
    ha k m p q
/-- Upper multiscale ellipticity moments shift under scale-normalization of the
law. -/
theorem LambdaMomentAtScale_scaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (k m : ℕ) {s : ℝ} (hs : 0 < s) (ξ : ℕ) :
    LambdaMomentAtScale (scaleNormalizedLaw k P) (m : ℤ) s ξ =
      LambdaMomentAtScale P ((k + m : ℕ) : ℤ) s ξ := by
  unfold LambdaMomentAtScale annealedMomentRoot
  rw [integral_scaleNormalizedLaw]
  · apply congrArg (fun x : ℝ => x ^ (1 / (ξ : ℝ)))
    apply integral_congr_ae
    filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
    rw [← rescaleCoeffField_eq_dilateCoeffField_neg_nat k]
    rw [LambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
      ha k m s (.finite 1)]
  · exact ((hP.scaleNormalized k).aemeasurable_LambdaSqCoeffField_finite_one
      (originCube d (m : ℤ)) hs).pow_const ξ |>.aestronglyMeasurable

/-- Lower inverse multiscale ellipticity moments shift under
scale-normalization of the law. -/
theorem lambdaInvMomentAtScale_scaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (k m : ℕ) {s : ℝ} (hs : 0 < s) (ξ : ℕ) :
    lambdaInvMomentAtScale (scaleNormalizedLaw k P) (m : ℤ) s ξ =
      lambdaInvMomentAtScale P ((k + m : ℕ) : ℤ) s ξ := by
  unfold lambdaInvMomentAtScale annealedMomentRoot
  rw [integral_scaleNormalizedLaw]
  · apply congrArg (fun x : ℝ => x ^ (1 / (ξ : ℝ)))
    apply integral_congr_ae
    filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
    rw [← rescaleCoeffField_eq_dilateCoeffField_neg_nat k]
    rw [lambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
      ha k m s (.finite 1)]
  · exact ((hP.scaleNormalized k).aemeasurable_lambdaSqCoeffField_finite_one_inv
      (originCube d (m : ℤ)) hs).pow_const ξ |>.aestronglyMeasurable

/-- The enhanced ellipticity moment contrast shifts under scale-normalization
of the law. -/
theorem widetildeThetaAtScale_scaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (k m : ℕ) {sUpper sLower : ℝ} (hsUpper : 0 < sUpper)
    (hsLower : 0 < sLower) (ξ : ℕ) :
    widetildeThetaAtScale (scaleNormalizedLaw k P) (m : ℤ) sUpper sLower ξ =
      widetildeThetaAtScale P ((k + m : ℕ) : ℤ) sUpper sLower ξ := by
  simp [widetildeThetaAtScale,
    LambdaMomentAtScale_scaleNormalizedLaw hP k m hsUpper ξ,
    lambdaInvMomentAtScale_scaleNormalizedLaw hP k m hsLower ξ]

private theorem smul_one_mat_eq_scalar_eq {d : ℕ} [NeZero d] {r s : ℝ}
    (h : r • (1 : Mat d) = s • (1 : Mat d)) : r = s := by
  classical
  let i : Fin d := Classical.choice (Fin.pos_iff_nonempty.mp (NeZero.pos d))
  have hentry := congrArg (fun M : Mat d => M i i) h
  simpa [Pi.smul_apply, Matrix.one_apply, i] using hentry

/-- The annealed full coarse block matrix shifts under scale-normalization of
the law. -/
theorem annealedBlockMatrixAtScale_scaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (k m : ℕ) :
    annealedBlockMatrixAtScale (scaleNormalizedLaw k P) (m : ℤ) =
      annealedBlockMatrixAtScale P ((k + m : ℕ) : ℤ) := by
  unfold annealedBlockMatrixAtScale annealedBlockMatrix
  rw [BlockMat.mk.injEq]
  constructor
  · ext i j
    rw [integral_scaleNormalizedLaw]
    · apply integral_congr_ae
      filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
      rw [← rescaleCoeffField_eq_dilateCoeffField_neg_nat k]
      rw [coarseBlockMatrix_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic ha k m]
    · exact ((hP.scaleNormalized k).aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet
        (originCube d (m : ℤ)) i j).aestronglyMeasurable
  constructor
  · ext i j
    rw [integral_scaleNormalizedLaw]
    · apply integral_congr_ae
      filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
      rw [← rescaleCoeffField_eq_dilateCoeffField_neg_nat k]
      rw [coarseBlockMatrix_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic ha k m]
    · exact ((hP.scaleNormalized k).aemeasurable_coarseBlockMatrix_upperRight_apply_cubeSet
        (originCube d (m : ℤ)) i j).aestronglyMeasurable
  constructor
  · ext i j
    rw [integral_scaleNormalizedLaw]
    · apply integral_congr_ae
      filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
      rw [← rescaleCoeffField_eq_dilateCoeffField_neg_nat k]
      rw [coarseBlockMatrix_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic ha k m]
    · exact ((hP.scaleNormalized k).aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet
        (originCube d (m : ℤ)) i j).aestronglyMeasurable
  · ext i j
    rw [integral_scaleNormalizedLaw]
    · apply integral_congr_ae
      filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
      rw [← rescaleCoeffField_eq_dilateCoeffField_neg_nat k]
      rw [coarseBlockMatrix_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic ha k m]
    · exact ((hP.scaleNormalized k).aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet
        (originCube d (m : ℤ)) i j).aestronglyMeasurable

/-- The annealed upper-left scalar block shifts under scale-normalization of
the law. -/
theorem annealedBAtScale_scaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (k m : ℕ) :
    annealedBAtScale (scaleNormalizedLaw k P) (m : ℤ) =
      annealedBAtScale P ((k + m : ℕ) : ℤ) := by
  simpa [annealedBAtScale, annealedB, annealedBlockMatrixAtScale] using
    congrArg BlockMat.upperLeft (annealedBlockMatrixAtScale_scaleNormalizedLaw hP k m)

/-- The annealed inverse-star scalar block shifts under scale-normalization of
the law. -/
theorem annealedSigmaStarInvAtScale_scaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (k m : ℕ) :
    annealedSigmaStarInvAtScale (scaleNormalizedLaw k P) (m : ℤ) =
      annealedSigmaStarInvAtScale P ((k + m : ℕ) : ℤ) := by
  simpa [annealedSigmaStarInvAtScale, annealedSigmaStarInv, annealedBlockMatrixAtScale] using
    congrArg BlockMat.lowerRight (annealedBlockMatrixAtScale_scaleNormalizedLaw hP k m)

namespace StationaryLaw

/-- Stationarity is preserved by triadic scale-normalization. -/
theorem scaleNormalized {d : ℕ} {P : CoeffLaw d}
    (hP : StationaryLaw P) (k : ℕ) :
    StationaryLaw (scaleNormalizedLaw k P) := by
  simpa [scaleNormalizedLaw_eq_rescaledLaw] using
    IsStationary.isStationary_rescaledLaw hP k

end StationaryLaw

namespace IsotropicLaw

private theorem rotateCoeffField_rescaleCoeffField {d : ℕ} (R : Mat d) (k : ℕ)
    (a : CoeffField d) :
    rotateCoeffField R (rescaleCoeffField k a) =
      rescaleCoeffField k (rotateCoeffField R a) := by
  funext x i j
  have hvec :
      matVecMul R (triadicDilateVec k x) =
        triadicDilateVec k (matVecMul R x) := by
    simpa [triadicDilateVec] using
      (matVecMul_smul R ((3 : ℝ) ^ k) x)
  simp [rotateCoeffField, rescaleCoeffField, hvec]

/-- Isotropy under signed permutations is preserved by triadic
scale-normalization. -/
theorem scaleNormalized {d : ℕ} {P : CoeffLaw d}
    (hP : IsotropicLaw P) (k : ℕ) :
    IsotropicLaw (scaleNormalizedLaw k P) := by
  intro R hR
  rw [scaleNormalizedLaw_eq_rescaledLaw]
  calc
    Measure.map (rotateCoeffField R) (rescaledLaw P k)
        = Measure.map
            (fun a : CoeffField d => rotateCoeffField R (rescaleCoeffField k a)) P := by
          exact map_rescaledLaw_eq P k (rotateCoeffField R) (measurable_rotateCoeffField R hR)
    _ = Measure.map
            (fun a : CoeffField d => rescaleCoeffField k (rotateCoeffField R a)) P := by
          apply congrArg (fun f => Measure.map f P)
          funext a
          exact rotateCoeffField_rescaleCoeffField R k a
    _ = Measure.map (rescaleCoeffField k) (Measure.map (rotateCoeffField R) P) := by
          symm
          simpa [Function.comp] using
            (Measure.map_map
              (measurable_rescaleCoeffField (d := d) k)
              (measurable_rotateCoeffField (d := d) R hR) (μ := P))
    _ = rescaledLaw P k := by
          rw [hP R hR]
          rfl

end IsotropicLaw

namespace AdjointInvariantLaw

private theorem adjointCoeffField_rescaleCoeffField {d : ℕ} (k : ℕ)
    (a : CoeffField d) :
    adjointCoeffField (rescaleCoeffField k a) =
      rescaleCoeffField k (adjointCoeffField a) := by
  funext x i j
  simp [adjointCoeffField, rescaleCoeffField, matTranspose]

/-- Adjoint invariance is preserved by triadic scale-normalization. -/
theorem scaleNormalized {d : ℕ} {P : CoeffLaw d}
    (hP : AdjointInvariantLaw P) (k : ℕ) :
    AdjointInvariantLaw (scaleNormalizedLaw k P) := by
  rw [scaleNormalizedLaw_eq_rescaledLaw]
  calc
    Measure.map adjointCoeffField (rescaledLaw P k)
        = Measure.map
            (fun a : CoeffField d => adjointCoeffField (rescaleCoeffField k a)) P := by
          exact map_rescaledLaw_eq P k adjointCoeffField measurable_adjointCoeffField
    _ = Measure.map
            (fun a : CoeffField d => rescaleCoeffField k (adjointCoeffField a)) P := by
          apply congrArg (fun f => Measure.map f P)
          funext a
          exact adjointCoeffField_rescaleCoeffField k a
    _ = Measure.map (rescaleCoeffField k) (Measure.map adjointCoeffField P) := by
          symm
          simpa [Function.comp] using
            (Measure.map_map
              (measurable_rescaleCoeffField (d := d) k)
              (measurable_adjointCoeffField (d := d)) (μ := P))
    _ = rescaledLaw P k := by
          rw [hP]
          rfl

end AdjointInvariantLaw

namespace StructuralLaw

/-- The full structural law package is preserved by triadic scale-normalization. -/
theorem scaleNormalized {d : ℕ} {P : CoeffLaw d}
    (hP : StructuralLaw P) (k : ℕ) :
    StructuralLaw (scaleNormalizedLaw k P) where
  stationary := hP.stationary.scaleNormalized k
  unit_range := hP.unit_range.scaleNormalized k
  isotropic := hP.isotropic.scaleNormalized k
  adjoint_invariant := hP.adjoint_invariant.scaleNormalized k

end StructuralLaw

namespace LawCarrier

/-- The primitive upper-left structural scalar shifts under
scale-normalization. -/
theorem barBAtScale_scaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hStruct : StructuralLaw P) (k m : ℕ) :
    (hP.scaleNormalized k).barBAtScale (hStruct.scaleNormalized k) (m : ℤ) =
      hP.barBAtScale hStruct ((k + m : ℕ) : ℤ) := by
  apply smul_one_mat_eq_scalar_eq (d := d)
  calc
    (hP.scaleNormalized k).barBAtScale (hStruct.scaleNormalized k) (m : ℤ) • (1 : Mat d)
        = annealedBAtScale (scaleNormalizedLaw k P) (m : ℤ) :=
          ((hP.scaleNormalized k).annealedBAtScale_eq_barBAtScale
            (hStruct.scaleNormalized k) (m : ℤ)).symm
    _ = annealedBAtScale P ((k + m : ℕ) : ℤ) :=
          annealedBAtScale_scaleNormalizedLaw hP k m
    _ = hP.barBAtScale hStruct ((k + m : ℕ) : ℤ) • (1 : Mat d) :=
          hP.annealedBAtScale_eq_barBAtScale hStruct ((k + m : ℕ) : ℤ)

/-- The primitive inverse-star structural scalar shifts under
scale-normalization. -/
theorem barSigmaStarInvAtScale_scaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hStruct : StructuralLaw P) (k m : ℕ) :
    (hP.scaleNormalized k).barSigmaStarInvAtScale
        (hStruct.scaleNormalized k) (m : ℤ) =
      hP.barSigmaStarInvAtScale hStruct ((k + m : ℕ) : ℤ) := by
  apply smul_one_mat_eq_scalar_eq (d := d)
  calc
    (hP.scaleNormalized k).barSigmaStarInvAtScale
          (hStruct.scaleNormalized k) (m : ℤ) • (1 : Mat d)
        = annealedSigmaStarInvAtScale (scaleNormalizedLaw k P) (m : ℤ) :=
          ((hP.scaleNormalized k).annealedSigmaStarInvAtScale_eq_barSigmaStarInvAtScale
            (hStruct.scaleNormalized k) (m : ℤ)).symm
    _ = annealedSigmaStarInvAtScale P ((k + m : ℕ) : ℤ) :=
          annealedSigmaStarInvAtScale_scaleNormalizedLaw hP k m
    _ = hP.barSigmaStarInvAtScale hStruct ((k + m : ℕ) : ℤ) • (1 : Mat d) :=
          hP.annealedSigmaStarInvAtScale_eq_barSigmaStarInvAtScale hStruct
            ((k + m : ℕ) : ℤ)

/-- The structural-law scalar `\bar\sigma` shifts under scale-normalization. -/
theorem barSigmaAtScale_scaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hStruct : StructuralLaw P) (k m : ℕ) :
    (hP.scaleNormalized k).barSigmaAtScale (hStruct.scaleNormalized k) (m : ℤ) =
      hP.barSigmaAtScale hStruct ((k + m : ℕ) : ℤ) := by
  calc
    (hP.scaleNormalized k).barSigmaAtScale (hStruct.scaleNormalized k) (m : ℤ)
        = (hP.scaleNormalized k).barBAtScale (hStruct.scaleNormalized k) (m : ℤ) :=
          (hP.scaleNormalized k).barSigmaAtScale_eq_barBAtScale
            (hStruct.scaleNormalized k) (m : ℤ)
    _ = hP.barBAtScale hStruct ((k + m : ℕ) : ℤ) :=
          hP.barBAtScale_scaleNormalizedLaw hStruct k m
    _ = hP.barSigmaAtScale hStruct ((k + m : ℕ) : ℤ) :=
          (hP.barSigmaAtScale_eq_barBAtScale hStruct ((k + m : ℕ) : ℤ)).symm

/-- The structural-law scalar `\bar\sigma_*` shifts under scale-normalization. -/
theorem barSigmaStarAtScale_scaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hStruct : StructuralLaw P) (k m : ℕ) :
    (hP.scaleNormalized k).barSigmaStarAtScale
        (hStruct.scaleNormalized k) (m : ℤ) =
      hP.barSigmaStarAtScale hStruct ((k + m : ℕ) : ℤ) := by
  calc
    (hP.scaleNormalized k).barSigmaStarAtScale (hStruct.scaleNormalized k) (m : ℤ)
        = ((hP.scaleNormalized k).barSigmaStarInvAtScale
            (hStruct.scaleNormalized k) (m : ℤ))⁻¹ :=
          (hP.scaleNormalized k).barSigmaStarAtScale_eq_inv_barSigmaStarInvAtScale
            (hStruct.scaleNormalized k) (m : ℤ)
    _ = (hP.barSigmaStarInvAtScale hStruct ((k + m : ℕ) : ℤ))⁻¹ := by
          rw [hP.barSigmaStarInvAtScale_scaleNormalizedLaw hStruct k m]
    _ = hP.barSigmaStarAtScale hStruct ((k + m : ℕ) : ℤ) :=
          (hP.barSigmaStarAtScale_eq_inv_barSigmaStarInvAtScale hStruct
            ((k + m : ℕ) : ℤ)).symm

/-- The structural-law contrast `\Theta` shifts under scale-normalization. -/
theorem thetaAtScale_scaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : CoeffLaw d} (hP : LawCarrier P)
    (hStruct : StructuralLaw P) (k m : ℕ) :
    (hP.scaleNormalized k).thetaAtScale (hStruct.scaleNormalized k) (m : ℤ) =
      hP.thetaAtScale hStruct ((k + m : ℕ) : ℤ) := by
  simp [LawCarrier.thetaAtScale,
    hP.barSigmaAtScale_scaleNormalizedLaw hStruct k m,
    hP.barSigmaStarAtScale_scaleNormalizedLaw hStruct k m]

end LawCarrier

end

end Ch04
end Book
end Homogenization
