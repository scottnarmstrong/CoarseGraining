import Homogenization.Book.Ch04.Observable
import Homogenization.Geometry.ScaleColoring

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Independence and coloring lemmas

Direct theorem surface for Lemma
`l.independence.separated.local.observables.stationary.random.fields` and Lemma
`l.coloring.triadic.partition.stationary.random.fields`.
-/

noncomputable section

open MeasureTheory

/-- Monotonicity of the public local-test sigma algebra. -/
theorem localSigma_mono {d : ℕ} {U V : Set (Vec d)} (hUV : U ⊆ V) :
    localSigma U ≤ localSigma V := by
  change Homogenization.LocalSigma U ≤ Homogenization.LocalSigma V
  dsimp [Homogenization.LocalSigma]
  refine MeasurableSpace.generateFrom_le ?_
  rintro s ⟨e, e', φ, t, hφ_cont, hφ_compact, hφ_support, ht, rfl⟩
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨e, e', φ, t, hφ_cont, hφ_compact, Set.Subset.trans hφ_support hUV, ht, rfl⟩

/-- Separation from each member of a finite family implies separation from the
union of that family. -/
theorem areUnitSeparated_biUnion_right {d : ℕ} {ι : Type*} {U : Set (Vec d)}
    {V : ι → Set (Vec d)} {s : Finset ι}
    (h : ∀ i ∈ s, AreUnitSeparated U (V i)) :
    AreUnitSeparated U (⋃ i ∈ s, V i) := by
  intro x y hx hy
  simp only [Set.mem_iUnion] at hy
  rcases hy with ⟨i, hi, hyi⟩
  exact h i hi hx hyi

/-- Events measurable with respect to finitely many public local-test sigma
algebras are measurable with respect to the local-test sigma algebra on the
union of the observation sets. -/
theorem measurableSet_biInter_localSigma_biUnion {d : ℕ} {ι : Type*}
    {U : ι → Set (Vec d)} {f : ι → Set (CoeffField d)}
    {s : Finset ι}
    (hf : ∀ i ∈ s, @MeasurableSet (CoeffField d) (localSigma (U i)) (f i)) :
    @MeasurableSet (CoeffField d) (localSigma (⋃ i ∈ s, U i)) (⋂ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      have hsubset_i : U i ⊆ ⋃ j ∈ insert i s, U j := by
        intro x hx
        simp [hx]
      have hi_meas :
          @MeasurableSet (CoeffField d) (localSigma (⋃ j ∈ insert i s, U j)) (f i) := by
        exact (localSigma_mono (d := d) hsubset_i) (f i) (hf i (by simp))
      have hsubset_s : (⋃ j ∈ s, U j) ⊆ ⋃ j ∈ insert i s, U j := by
        intro x hx
        simp [hx]
      have hs_meas :
          @MeasurableSet (CoeffField d) (localSigma (⋃ j ∈ insert i s, U j))
            (⋂ j ∈ s, f j) := by
        exact (localSigma_mono (d := d) hsubset_s) (⋂ j ∈ s, f j)
          (ih (fun j hj => hf j (by simp [hj])))
      simpa [Finset.set_biInter_insert, hi] using hi_meas.inter hs_meas

/-- Unit-range dependence gives independence of any pairwise separated finite
family of public local-test sigma algebras. -/
theorem iIndep_localSigma_of_unitRangeDependentLaw {d : ℕ} {ι : Type*}
    {P : CoeffLaw d} [IsProbabilityMeasure P] {U : ι → Set (Vec d)}
    (hP : UnitRangeDependentLaw P)
    (hsep : Pairwise fun i j => AreUnitSeparated (U i) (U j)) :
    ProbabilityTheory.iIndep (fun i => localSigma (U i)) P := by
  classical
  rw [ProbabilityTheory.iIndep_iff]
  intro s f hf
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
          @MeasurableSet (CoeffField d) (localSigma (⋃ j ∈ s, U j)) (⋂ j ∈ s, f j) :=
        measurableSet_biInter_localSigma_biUnion (U := U)
          (f := f) (s := s) fun j hj => hf j (by simp [hj])
      have h_inter :
          P (f i ∩ ⋂ j ∈ s, f j) = P (f i) * P (⋂ j ∈ s, f j) := by
        exact (ProbabilityTheory.Indep_iff
          (localSigma (U i)) (localSigma (⋃ j ∈ s, U j)) P).1
            (hP (U i) (⋃ j ∈ s, U j) hsep_union)
            (f i) (⋂ j ∈ s, f j) (hf i (by simp)) hs_meas
      calc
        P (⋂ j ∈ insert i s, f j) = P (f i ∩ ⋂ j ∈ s, f j) := by
          simp
        _ = P (f i) * P (⋂ j ∈ s, f j) := h_inter
        _ = P (f i) * ∏ j ∈ s, P (f j) := by rw [ih (fun j hj => hf j (by simp [hj]))]
        _ = ∏ j ∈ insert i s, P (f j) := by simp [Finset.prod_insert, hi]

/-- Public local random variables indexed by pairwise separated observation
sets are independent under unit-range dependence. -/
theorem iIndepFun_of_unitRangeDependentLaw_of_pairwise_separated {d : ℕ}
    {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {P : CoeffLaw d} [IsProbabilityMeasure P]
    {U : ι → Set (Vec d)} {X : ∀ i, CoeffField d → β i}
    (hP : UnitRangeDependentLaw P)
    (hX : ∀ i, IsLocalRandomVariable (U i) (X i))
    (hsep : Pairwise fun i j => AreUnitSeparated (U i) (U j)) :
    ProbabilityTheory.iIndepFun X P := by
  classical
  rw [ProbabilityTheory.iIndepFun_iff_iIndep]
  rw [ProbabilityTheory.iIndep_iff]
  intro s f hf
  exact (ProbabilityTheory.iIndep_iff (fun i => localSigma (U i)) P).1
    (iIndep_localSigma_of_unitRangeDependentLaw (P := P) hP hsep) s
    (fun i hi => (Measurable.comap_le (hX i)) (f i) (hf i hi))

/-- A single scale-color class of descendant cube observables is an independent
family under the public unit-range dependence assumption. -/
theorem iIndepFun_descendantsAtScaleScaleColorClass_of_unitRangeDependentLaw
    {d : ℕ} {Q : TriadicCube d} {k : ℤ} {c : ScaleColor d k}
    {P : CoeffLaw d} [IsProbabilityMeasure P]
    {β : {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c} → Type*}
    [∀ R, MeasurableSpace (β R)]
    {X : ∀ R, CoeffField d → β R}
    (hP : UnitRangeDependentLaw P)
    (hX : ∀ R, IsLocalRandomVariable (cubeSet R.1) (X R)) :
    ProbabilityTheory.iIndepFun X P := by
  classical
  let I : Type := {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c}
  let U : I → Set (Vec d) := fun R => cubeSet R.1
  have hXU : ∀ R : I, IsLocalRandomVariable (U R) (X R) := by
    intro R
    simpa [I, U] using hX R
  have hsep : Pairwise fun R S : I => AreUnitSeparated (U R) (U S) := by
    intro R S hRS x y hx hy
    exact one_le_dist_of_ne_of_mem_descendantsAtScaleScaleColorClass
      (hR := R.2) (hS := S.2)
      (hneq := by
        intro h
        apply hRS
        exact Subtype.ext h)
      hx hy
  simpa [I, U] using
    (iIndepFun_of_unitRangeDependentLaw_of_pairwise_separated
      (d := d) (ι := I) (β := β) (P := P) (U := U) (X := X) hP hXU hsep)

end

end Ch04
end Book
end Homogenization
