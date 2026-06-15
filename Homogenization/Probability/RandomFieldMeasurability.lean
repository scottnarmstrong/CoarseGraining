import Homogenization.Geometry.CubeColoring
import Homogenization.Geometry.ScaleColoring
import Homogenization.Probability.RandomField

namespace Homogenization

/-!
Foundational measurability lemmas for coefficient fields viewed as the sample
space of the probability layer.

This file stays deliberately law-centric: the primitive random object remains a
measure on `CoeffField d`. The role of the present API is to expose the basic
measurable coefficient-field transforms and the `LocalSigma` measurability of
the generator observables used to define locality in law.
-/

theorem measurable_coeffField_eval {d : ℕ} (x : Vec d) :
    Measurable (fun a : CoeffField d => a x) :=
  measurable_pi_apply x

theorem measurable_coeffField_entry {d : ℕ} (x : Vec d) (i j : Fin d) :
    Measurable (fun a : CoeffField d => a x i j) := by
  have hMat : Measurable (fun a : CoeffField d => a x) :=
    measurable_coeffField_eval (d := d) x
  have hRow : Measurable (fun a : CoeffField d => (a x) i) := Measurable.eval hMat
  exact Measurable.eval hRow

theorem measurable_restrictCoeffField {d : ℕ} (U : Set (Vec d)) :
    Measurable (restrictCoeffField (d := d) U) := by
  classical
  rw [measurable_pi_iff]
  intro x
  rw [measurable_pi_iff]
  intro i
  rw [measurable_pi_iff]
  intro j
  by_cases hx : x ∈ U
  · simpa [restrictCoeffField, hx] using measurable_coeffField_entry (d := d) x i j
  · simp [restrictCoeffField, hx]

/-- The sigma-algebra on coefficient space induced by restricting the field to
the deterministic set `U`. This is the sigma-algebra that matches the current
pointwise notion of locality `IsLocalObservable U`. -/
def RestrictionSigma {d : ℕ} (U : Set (Vec d)) : MeasurableSpace (CoeffField d) :=
  MeasurableSpace.comap (restrictCoeffField U) inferInstance

theorem measurable_restrictCoeffField_restrictionSigma {d : ℕ} (U : Set (Vec d)) :
    @Measurable (CoeffField d) (CoeffField d) (RestrictionSigma U) _ (restrictCoeffField U) :=
  comap_measurable (restrictCoeffField U)

theorem restrictCoeffField_comp_restrictCoeffField_of_subset {d : ℕ}
    {U V : Set (Vec d)} (hUV : U ⊆ V) :
    restrictCoeffField U ∘ restrictCoeffField V = restrictCoeffField U := by
  funext a x
  by_cases hx : x ∈ U
  · have hxV : x ∈ V := hUV hx
    simp [Function.comp, restrictCoeffField, hx, hxV]
  · simp [Function.comp, restrictCoeffField, hx]

theorem measurable_restrictCoeffField_restrictionSigma_of_subset {d : ℕ}
    {U V : Set (Vec d)} (hUV : U ⊆ V) :
    @Measurable (CoeffField d) (CoeffField d) (RestrictionSigma V) _
      (restrictCoeffField U) := by
  simpa [restrictCoeffField_comp_restrictCoeffField_of_subset hUV, Function.comp] using
    (measurable_restrictCoeffField U).comp
      (measurable_restrictCoeffField_restrictionSigma (d := d) V)

theorem RestrictionSigma_mono {d : ℕ} {U V : Set (Vec d)} (hUV : U ⊆ V) :
    RestrictionSigma U ≤ RestrictionSigma V := by
  simpa [RestrictionSigma] using
    (measurable_iff_comap_le.mp
      (measurable_restrictCoeffField_restrictionSigma_of_subset (d := d) hUV))

theorem measurable_translateCoeffField {d : ℕ} (z : Vec d) :
    Measurable (translateCoeffField (d := d) z) := by
  rw [measurable_pi_iff]
  intro x
  rw [measurable_pi_iff]
  intro i
  rw [measurable_pi_iff]
  intro j
  simpa [translateCoeffField] using
    measurable_coeffField_entry (d := d) (fun k => x k + z k) i j

theorem measurable_translateByInt {d : ℕ} (z : Fin d → ℤ) :
    Measurable (translateByInt (d := d) z) := by
  simpa [translateByInt] using
    measurable_translateCoeffField (d := d) (intVecToRealVec z)

theorem measurable_symmCoeffField {d : ℕ} :
    Measurable (symmCoeffField (d := d)) := by
  rw [measurable_pi_iff]
  intro x
  rw [measurable_pi_iff]
  intro i
  rw [measurable_pi_iff]
  intro j
  have hij : Measurable (fun a : CoeffField d => a x i j) :=
    measurable_coeffField_entry (d := d) x i j
  have hji : Measurable (fun a : CoeffField d => a x j i) :=
    measurable_coeffField_entry (d := d) x j i
  simpa [symmCoeffField, symmPart_eq_smul_add_transpose, matTranspose] using
    (measurable_const.mul (hij.add hji))

theorem measurable_skewCoeffField {d : ℕ} :
    Measurable (skewCoeffField (d := d)) := by
  rw [measurable_pi_iff]
  intro x
  rw [measurable_pi_iff]
  intro i
  rw [measurable_pi_iff]
  intro j
  have hij : Measurable (fun a : CoeffField d => a x i j) :=
    measurable_coeffField_entry (d := d) x i j
  have hji : Measurable (fun a : CoeffField d => a x j i) :=
    measurable_coeffField_entry (d := d) x j i
  simpa [skewCoeffField, skewPart_eq_smul_sub_transpose, matTranspose] using
    (measurable_const.mul (hij.sub hji))

theorem IsStationary.map_translateByInt {d : ℕ}
    {P : MeasureTheory.Measure (CoeffField d)} (hP : IsStationary P) (z : Fin d → ℤ) :
    MeasureTheory.Measure.map (translateByInt z) P = P :=
  hP z

theorem integral_comp_translateByInt_eq_of_isStationary {d : ℕ}
    {P : MeasureTheory.Measure (CoeffField d)} (hP : IsStationary P)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (z : Fin d → ℤ) (f : CoeffField d → E)
    (hf : MeasureTheory.AEStronglyMeasurable f P) :
    ∫ a, f (translateByInt z a) ∂P = ∫ a, f a ∂P :=
  integral_comp_eq_of_map_eq (measurable_translateByInt z) (hP z) f hf

theorem preimage_localTestObservable_mem_localSigma {d : ℕ} {U : Set (Vec d)}
    (e e' : Vec d) {φ : Vec d → ℝ} (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_support : tsupport φ ⊆ U)
    {t : Set ℝ} (ht : MeasurableSet t) :
    @MeasurableSet (CoeffField d) (LocalSigma U) (localTestObservable e e' φ ⁻¹' t) := by
  show
    @MeasurableSet (CoeffField d)
      (MeasurableSpace.generateFrom
        { s |
            ∃ e e' : Vec d, ∃ φ : Vec d → ℝ, ∃ t : Set ℝ,
              ContDiff ℝ (⊤ : ℕ∞) φ ∧
                HasCompactSupport φ ∧
                tsupport φ ⊆ U ∧
                MeasurableSet t ∧
                s = localTestObservable e e' φ ⁻¹' t })
      (localTestObservable e e' φ ⁻¹' t)
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨e, e', φ, t, hφ_cont, hφ_compact, hφ_support, ht, rfl⟩

theorem measurable_localTestObservable_localSigma {d : ℕ} {U : Set (Vec d)}
    (e e' : Vec d) {φ : Vec d → ℝ} (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_support : tsupport φ ⊆ U) :
    @Measurable (CoeffField d) ℝ (LocalSigma U) (borel ℝ)
      (localTestObservable e e' φ) := by
  intro t ht
  exact preimage_localTestObservable_mem_localSigma
    (U := U) e e' hφ_cont hφ_compact hφ_support ht

theorem localTestObservable_eq_of_ae_eq {d : ℕ} {a b : CoeffField d}
    (h : a =ᵐ[MeasureTheory.volume] b) (e e' : Vec d) (φ : Vec d → ℝ) :
    localTestObservable e e' φ a = localTestObservable e e' φ b := by
  unfold localTestObservable
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h] with x hx
  simp [hx]

theorem mem_iff_of_measurableSet_localSigma_of_forall_localTestObservable_eq {d : ℕ}
    {U : Set (Vec d)} {s : Set (CoeffField d)}
    (hs : @MeasurableSet (CoeffField d) (LocalSigma U) s) {a b : CoeffField d}
    (hobs : ∀ (e e' : Vec d) (φ : Vec d → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ →
      tsupport φ ⊆ U →
      localTestObservable e e' φ a = localTestObservable e e' φ b) :
    a ∈ s ↔ b ∈ s := by
  let C : Set (Set (CoeffField d)) :=
    { s |
        ∃ e e' : Vec d, ∃ φ : Vec d → ℝ, ∃ t : Set ℝ,
          ContDiff ℝ (⊤ : ℕ∞) φ ∧
            HasCompactSupport φ ∧
            tsupport φ ⊆ U ∧
            MeasurableSet t ∧
            s = localTestObservable e e' φ ⁻¹' t }
  have hC : ∀ t ∈ C, a ∈ t ↔ b ∈ t := by
    intro t ht
    rcases ht with ⟨e, e', φ, q, hφ_cont, hφ_compact, hφ_support, _hq, rfl⟩
    simp only [Set.mem_preimage]
    rw [hobs e e' φ hφ_cont hφ_compact hφ_support]
  have hsC : @MeasurableSet (CoeffField d) (MeasurableSpace.generateFrom C) s := by
    simpa [LocalSigma, C] using hs
  exact (MeasurableSpace.forall_generateFrom_mem_iff_mem_iff (S := C) (x := a) (y := b)).2
    hC s hsC

theorem mem_iff_of_measurableSet_localSigma_of_ae_eq {d : ℕ} {U : Set (Vec d)}
    {s : Set (CoeffField d)} (hs : @MeasurableSet (CoeffField d) (LocalSigma U) s)
    {a b : CoeffField d} (h : a =ᵐ[MeasureTheory.volume] b) :
    a ∈ s ↔ b ∈ s :=
  mem_iff_of_measurableSet_localSigma_of_forall_localTestObservable_eq hs
    (fun e e' φ _ _ _ => localTestObservable_eq_of_ae_eq h e e' φ)

/-- A sample-space-valued coefficient field is locally measurable on `U` if it
is measurable with codomain `LocalSigma U`. -/
def IsLocalSigmaMeasurableOn {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (A : Ω → CoeffField d) (U : Set (Vec d)) : Prop :=
  @Measurable Ω (CoeffField d) _ (LocalSigma U) A

/-- A sample-space-valued coefficient field is restriction-measurable on `U` if
it is measurable with codomain `RestrictionSigma U`. -/
def IsRestrictionSigmaMeasurableOn {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (A : Ω → CoeffField d) (U : Set (Vec d)) : Prop :=
  @Measurable Ω (CoeffField d) _ (RestrictionSigma U) A

/-- Unit-range dependence formulated for the restriction sigma-algebras induced
by `restrictCoeffField`. This is the dependence notion naturally matched to
the current pointwise-local observable interface. -/
def IsRestrictionUnitRangeDependent {d : ℕ}
    (P : MeasureTheory.Measure (CoeffField d)) : Prop :=
  ∀ U V : Set (Vec d), AreUnitSeparated U V →
    ProbabilityTheory.Indep (RestrictionSigma U) (RestrictionSigma V) P

theorem AreUnitSeparated.symm {d : ℕ} {U V : Set (Vec d)}
    (hUV : AreUnitSeparated U V) :
    AreUnitSeparated V U := by
  intro x y hx hy
  simpa [dist_comm] using hUV hy hx

theorem areUnitSeparated_cubeSet_of_ne_of_mem_descendantsAtScaleColorClass {d : ℕ}
    {Q R S : TriadicCube d} {k : ℤ} {c : CubeColor d} (hk : 0 ≤ k)
    (hR : R ∈ descendantsAtScaleColorClass Q k c)
    (hS : S ∈ descendantsAtScaleColorClass Q k c) (hneq : R ≠ S) :
    AreUnitSeparated (cubeSet R) (cubeSet S) := by
  intro x y hx hy
  exact one_le_dist_of_ne_of_mem_descendantsAtScaleColorClass hk hR hS hneq hx hy

theorem pairwise_areUnitSeparated_cubeSet_descendantsAtScaleColorClass {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (hk : 0 ≤ k) (c : CubeColor d) :
    (descendantsAtScaleColorClass Q k c : Set (TriadicCube d)).Pairwise
      (fun R S => AreUnitSeparated (cubeSet R) (cubeSet S)) := by
  intro R hR S hS hneq
  exact areUnitSeparated_cubeSet_of_ne_of_mem_descendantsAtScaleColorClass hk hR hS hneq

theorem pairwise_areUnitSeparated_cubeSet_subtype_descendantsAtScaleColorClass {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (hk : 0 ≤ k) (c : CubeColor d) :
    Pairwise
      (fun R S : {R : TriadicCube d // R ∈ descendantsAtScaleColorClass Q k c} =>
        AreUnitSeparated (cubeSet R.1) (cubeSet S.1)) := by
  intro R S hRS
  exact areUnitSeparated_cubeSet_of_ne_of_mem_descendantsAtScaleColorClass hk R.2 S.2
    (by
      intro h
      apply hRS
      exact Subtype.ext h)

theorem areUnitSeparated_cubeSet_of_ne_of_mem_descendantsAtScaleScaleColorClass {d : ℕ}
    {Q R S : TriadicCube d} {k : ℤ} {c : ScaleColor d k}
    (hR : R ∈ descendantsAtScaleScaleColorClass Q k c)
    (hS : S ∈ descendantsAtScaleScaleColorClass Q k c) (hneq : R ≠ S) :
    AreUnitSeparated (cubeSet R) (cubeSet S) := by
  intro x y hx hy
  exact one_le_dist_of_ne_of_mem_descendantsAtScaleScaleColorClass hR hS hneq hx hy

theorem pairwise_areUnitSeparated_cubeSet_descendantsAtScaleScaleColorClass {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (c : ScaleColor d k) :
    (descendantsAtScaleScaleColorClass Q k c : Set (TriadicCube d)).Pairwise
      (fun R S => AreUnitSeparated (cubeSet R) (cubeSet S)) := by
  intro R hR S hS hneq
  exact areUnitSeparated_cubeSet_of_ne_of_mem_descendantsAtScaleScaleColorClass hR hS hneq

theorem pairwise_areUnitSeparated_cubeSet_subtype_descendantsAtScaleScaleColorClass {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (c : ScaleColor d k) :
    Pairwise
      (fun R S : {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c} =>
        AreUnitSeparated (cubeSet R.1) (cubeSet S.1)) := by
  intro R S hRS
  exact areUnitSeparated_cubeSet_of_ne_of_mem_descendantsAtScaleScaleColorClass R.2 S.2
    (by
      intro h
      apply hRS
      exact Subtype.ext h)

theorem areUnitSeparated_biUnion_right {d : ℕ} {ι : Type*} [DecidableEq ι] {U : Set (Vec d)}
    {V : ι → Set (Vec d)} {s : Finset ι}
    (h : ∀ i ∈ s, AreUnitSeparated U (V i)) :
    AreUnitSeparated U (⋃ i ∈ s, V i) := by
  intro x y hx hy
  simp only [Set.mem_iUnion] at hy
  rcases hy with ⟨i, hi, hyi⟩
  exact h i hi hx hyi

theorem measurableSet_biInter_restrictionSigma_biUnion {d : ℕ} {ι : Type*}
    [DecidableEq ι] {U : ι → Set (Vec d)} {f : ι → Set (CoeffField d)}
    {s : Finset ι}
    (hf : ∀ i ∈ s, @MeasurableSet (CoeffField d) (RestrictionSigma (U i)) (f i)) :
    @MeasurableSet (CoeffField d) (RestrictionSigma (⋃ i ∈ s, U i)) (⋂ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      have hsubset_i : U i ⊆ ⋃ j ∈ insert i s, U j := by
        intro x hx
        simp [hx]
      have hi_meas :
          @MeasurableSet (CoeffField d) (RestrictionSigma (⋃ j ∈ insert i s, U j)) (f i) := by
        exact (RestrictionSigma_mono (d := d) hsubset_i) (f i) (hf i (by simp))
      have hsubset_s : (⋃ j ∈ s, U j) ⊆ ⋃ j ∈ insert i s, U j := by
        intro x hx
        simp [hx]
      have hs_meas :
          @MeasurableSet (CoeffField d) (RestrictionSigma (⋃ j ∈ insert i s, U j))
            (⋂ j ∈ s, f j) := by
        exact (RestrictionSigma_mono (d := d) hsubset_s) (⋂ j ∈ s, f j)
          (ih (fun j hj => hf j (by simp [hj])))
      simpa [Finset.set_biInter_insert, hi] using hi_meas.inter hs_meas

theorem iIndep_restrictionSigma_of_isRestrictionUnitRangeDependent {d : ℕ} {ι : Type*}
    [DecidableEq ι] {P : MeasureTheory.Measure (CoeffField d)}
    [MeasureTheory.IsProbabilityMeasure P] {U : ι → Set (Vec d)}
    (hP : IsRestrictionUnitRangeDependent P)
    (hsep : Pairwise fun i j => AreUnitSeparated (U i) (U j)) :
    ProbabilityTheory.iIndep (fun i => RestrictionSigma (U i)) P := by
  rw [ProbabilityTheory.iIndep_iff]
  intro s f hf
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      have hsep_union : AreUnitSeparated (U i) (⋃ j ∈ s, U j) := by
        refine areUnitSeparated_biUnion_right (U := U i) (V := U) ?_
        intro j hj
        exact hsep (by
          intro hij
          exact hi (hij ▸ hj))
      have hs_meas :
          @MeasurableSet (CoeffField d) (RestrictionSigma (⋃ j ∈ s, U j)) (⋂ j ∈ s, f j) :=
        measurableSet_biInter_restrictionSigma_biUnion (U := U)
          (f := f) (s := s) fun j hj => hf j (by simp [hj])
      have h_inter :
          P (f i ∩ ⋂ j ∈ s, f j) = P (f i) * P (⋂ j ∈ s, f j) := by
        exact (ProbabilityTheory.Indep_iff
          (RestrictionSigma (U i)) (RestrictionSigma (⋃ j ∈ s, U j)) P).1
            (hP (U i) (⋃ j ∈ s, U j) hsep_union)
            (f i) (⋂ j ∈ s, f j) (hf i (by simp)) hs_meas
      calc
        P (⋂ j ∈ insert i s, f j) = P (f i ∩ ⋂ j ∈ s, f j) := by
          simp
        _ = P (f i) * P (⋂ j ∈ s, f j) := h_inter
        _ = P (f i) * ∏ j ∈ s, P (f j) := by rw [ih (fun j hj => hf j (by simp [hj]))]
        _ = ∏ j ∈ insert i s, P (f j) := by simp [Finset.prod_insert, hi]

theorem iIndep_restrictionSigma_descendantsAtScaleColorClass_of_isRestrictionUnitRangeDependent
    {d : ℕ} {Q : TriadicCube d} {k : ℤ} (hk : 0 ≤ k) {c : CubeColor d}
    {P : MeasureTheory.Measure (CoeffField d)} [MeasureTheory.IsProbabilityMeasure P]
    (hP : IsRestrictionUnitRangeDependent P) :
    ProbabilityTheory.iIndep
      (fun R : {R : TriadicCube d // R ∈ descendantsAtScaleColorClass Q k c} =>
        RestrictionSigma (cubeSet R.1)) P := by
  let I : Type := {R : TriadicCube d // R ∈ descendantsAtScaleColorClass Q k c}
  let U : I → Set (Vec d) := fun R => cubeSet R.1
  have hsep : Pairwise fun R S : I => AreUnitSeparated (U R) (U S) := by
    simpa [I, U] using
      pairwise_areUnitSeparated_cubeSet_subtype_descendantsAtScaleColorClass (Q := Q) hk c
  simpa [I, U] using
    (iIndep_restrictionSigma_of_isRestrictionUnitRangeDependent
      (d := d) (ι := I) (U := U) hP hsep)

theorem iIndep_restrictionSigma_descendantsAtScaleScaleColorClass_of_isRestrictionUnitRangeDependent
    {d : ℕ} {Q : TriadicCube d} {k : ℤ} {c : ScaleColor d k}
    {P : MeasureTheory.Measure (CoeffField d)} [MeasureTheory.IsProbabilityMeasure P]
    (hP : IsRestrictionUnitRangeDependent P) :
    ProbabilityTheory.iIndep
      (fun R : {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c} =>
        RestrictionSigma (cubeSet R.1)) P := by
  let I : Type := {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c}
  let U : I → Set (Vec d) := fun R => cubeSet R.1
  have hsep : Pairwise fun R S : I => AreUnitSeparated (U R) (U S) := by
    simpa [I, U] using
      pairwise_areUnitSeparated_cubeSet_subtype_descendantsAtScaleScaleColorClass (Q := Q) c
  simpa [I, U] using
    (iIndep_restrictionSigma_of_isRestrictionUnitRangeDependent
      (d := d) (ι := I) (U := U) hP hsep)

theorem IsLocalSigmaMeasurableOn.measurable_localTestObservable
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {A : Ω → CoeffField d} {U : Set (Vec d)}
    (hA : IsLocalSigmaMeasurableOn A U)
    (e e' : Vec d) {φ : Vec d → ℝ} (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_support : tsupport φ ⊆ U) :
    Measurable fun ω => localTestObservable e e' φ (A ω) := by
  exact
    (measurable_localTestObservable_localSigma (U := U) e e' hφ_cont hφ_compact hφ_support).comp
      hA

end Homogenization
