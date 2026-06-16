import Homogenization.Book.Ch04.Measurability
import Homogenization.Book.Ch04.Theorems.CoarseObservables
import Homogenization.Book.Ch02.Theorems.SolutionIntegrability
import Homogenization.Book.Ch04.Internal.AEESliceAssembly.MuFamily

import Homogenization.Book.Ch04.Theorems.CanonicalSolutions.AverageIdentities

namespace Homogenization
namespace Book
namespace Ch04

open scoped ENNReal
open MeasureTheory


namespace LawCarrier

private theorem aemeasurable_vecNormSq_sub_const
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {d : ℕ} {F : α → Vec d} (hF : AEMeasurable F μ) (v : Vec d) :
    AEMeasurable (fun a : α => vecNormSq (F a - v)) μ := by
  have hcoord : ∀ i : Fin d, AEMeasurable (fun a : α => F a i - v i) μ := by
    intro i
    exact ((aemeasurable_pi_iff.mp hF) i).sub aemeasurable_const
  simpa [vecNormSq, vecDot] using
    (Finset.univ.aemeasurable_fun_sum
      (μ := μ)
      (f := fun i a => (F a i - v i) * (F a i - v i))
      (fun i _hi => (hcoord i).mul (hcoord i)))

private theorem measurable_canonicalMuHilbertMinimizerCubeSet_localSigma
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (P0 : BlockVec d) :
    @Measurable (CoeffField d) (HilbertBlockL2 (cubeSet Q))
      (localSigma (cubeSet Q)) (borel (HilbertBlockL2 (cubeSet Q)))
      (canonicalMuHilbertMinimizerCubeSet Q P0) := by
  classical
  let U : Set (Vec d) := cubeSet Q
  letI : MeasurableSpace (CoeffField d) := localSigma U
  letI : MeasurableSpace (HilbertBlockL2 U) := borel _
  haveI : BorelSpace (HilbertBlockL2 U) := ⟨rfl⟩
  let slice : ℕ → Set (CoeffField d) :=
    fun k => {a : CoeffField d | AEEQuantitativeEllipticSlice U k a}
  let firstSlice : ℕ → Set (CoeffField d) :=
    fun k => slice k ∩ ⋂ j ∈ Finset.range k, (slice j)ᶜ
  let S : Set (CoeffField d) := ⋃ k : ℕ, firstSlice k
  let cover : Option ℕ → Set (CoeffField d)
    | none => Sᶜ
    | some k => firstSlice k
  let piece : (i : Option ℕ) → cover i → HilbertBlockL2 U
    | none, _ => 0
    | some k, a => by
        let ak :
            {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} :=
          ⟨a.1, by simpa [U] using a.2.1⟩
        exact ((canonicalAEEMuOperatorSystemData Q k ak).toMuHilbertRealization).minimizerMap P0
  have hslice_meas : ∀ k : ℕ, MeasurableSet (slice k) := by
    intro k
    simpa [slice, U] using
      hP.measurableSet_aeeQuantitativeEllipticSlice_cubeSet Q k
  have hfirst_meas : ∀ k : ℕ, MeasurableSet (firstSlice k) := by
    intro k
    have hprev :
        MeasurableSet (⋂ j ∈ Finset.range k, (slice j)ᶜ) :=
      (Finset.range k).measurableSet_biInter fun j _hj => (hslice_meas j).compl
    exact (hslice_meas k).inter hprev
  have hcover_meas : ∀ i : Option ℕ, MeasurableSet (cover i) := by
    intro i
    cases i with
    | none => exact (MeasurableSet.iUnion hfirst_meas).compl
    | some k => exact hfirst_meas k
  have hfirst_unique :
      ∀ {i j : ℕ} {a : CoeffField d}, a ∈ firstSlice i → a ∈ firstSlice j → i = j := by
    intro i j a hi hj
    by_cases hij : i = j
    · exact hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hnot : a ∉ slice i := by
        have hcompl : a ∈ (slice i)ᶜ := by
          simpa using
            (Set.mem_iInter.mp
              (Set.mem_iInter.mp hj.2 i)
              (by simpa using hlt))
        simpa using hcompl
      exact False.elim (hnot hi.1)
    · have hnot : a ∉ slice j := by
        have hcompl : a ∈ (slice j)ᶜ := by
          simpa using
            (Set.mem_iInter.mp
              (Set.mem_iInter.mp hi.2 j)
              (by simpa using hgt))
        simpa using hcompl
      exact False.elim (hnot hj.1)
  have hagree :
      ∀ (i j : Option ℕ) (a : CoeffField d)
        (hai : a ∈ cover i) (haj : a ∈ cover j),
        piece i ⟨a, hai⟩ = piece j ⟨a, haj⟩ := by
    intro i j a hai haj
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some k =>
            exfalso
            have haS : a ∈ S := Set.mem_iUnion.mpr ⟨k, by simpa [cover] using haj⟩
            have hnotS : a ∉ S := by simpa [cover] using hai
            exact hnotS haS
    | some i =>
        cases j with
        | none =>
            exfalso
            have haS : a ∈ S := Set.mem_iUnion.mpr ⟨i, by simpa [cover] using hai⟩
            have hnotS : a ∉ S := by simpa [cover] using haj
            exact hnotS haS
        | some j =>
            have hij : i = j := hfirst_unique (by simpa [cover] using hai) (by simpa [cover] using haj)
            subst j
            rfl
  have hcover : ⋃ i : Option ℕ, cover i = Set.univ := by
    ext a
    constructor
    · intro _ha
      exact Set.mem_univ a
    · intro _ha
      by_cases haS : a ∈ S
      · rcases Set.mem_iUnion.mp haS with ⟨k, hak⟩
        exact Set.mem_iUnion.mpr ⟨some k, by simpa [cover] using hak⟩
      · exact Set.mem_iUnion.mpr ⟨none, by simpa [cover] using haS⟩
  have hpiece_meas : ∀ i : Option ℕ, Measurable (piece i) := by
    intro i
    cases i with
    | none => exact measurable_const
    | some k =>
        let sliceSubtype :=
          {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
        letI : MeasurableSpace sliceSubtype :=
          AEEQuantitativeEllipticSlice.localMeasurableSpace U k
        let toSlice : cover (some k) → sliceSubtype :=
          fun a => ⟨a.1, a.2.1⟩
        have htoSlice :
            @Measurable (cover (some k)) sliceSubtype
              (inferInstance : MeasurableSpace (cover (some k)))
              (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) toSlice := by
          apply Measurable.of_comap_le
          unfold AEEQuantitativeEllipticSlice.localMeasurableSpace
          rw [MeasurableSpace.comap_comp]
          rw [show Subtype.val ∘ toSlice = Subtype.val by
            funext a
            rfl]
          exact
            (measurable_subtype_coe :
              @Measurable (cover (some k)) (CoeffField d)
                (inferInstance : MeasurableSpace (cover (some k))) (localSigma U)
                Subtype.val).comap_le
        have hslice : StronglyMeasurable
            (fun a : sliceSubtype =>
              ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).minimizerMap P0) := by
          simpa [sliceSubtype, U] using
            Homogenization.stronglyMeasurable_canonicalAEEMuHilbertMinimizer_aeeQuantitativeSlice_cubeSet
              (Q := Q) (k := k) P0
        change Measurable (fun a : cover (some k) =>
          ((canonicalAEEMuOperatorSystemData Q k (toSlice a)).toMuHilbertRealization).minimizerMap P0)
        exact hslice.measurable.comp htoSlice
  have hLift : Measurable (Set.liftCover cover piece hagree hcover) :=
    measurable_liftCover cover hcover_meas piece hpiece_meas hagree hcover
  have hEq :
      Set.liftCover cover piece hagree hcover =
        canonicalMuHilbertMinimizerCubeSet Q P0 := by
    funext a
    by_cases ha : ∃ k : ℕ, AEEQuantitativeEllipticSlice U k a
    · let k : ℕ := Nat.find ha
      have hafirst : a ∈ firstSlice k := by
        refine ⟨?_, ?_⟩
        · simpa [slice, k] using Nat.find_spec ha
        · refine Set.mem_iInter.mpr ?_
          intro j
          refine Set.mem_iInter.mpr ?_
          intro hj
          have hjlt : j < k := by simpa [k] using hj
          have hnot : ¬ AEEQuantitativeEllipticSlice U j a := by
            intro hja
            exact (not_lt_of_ge (Nat.find_min' ha hja)) (by simpa [k] using hjlt)
          simpa [slice] using hnot
      rw [Set.liftCover_of_mem
        (S := cover) (f := piece) (hf := hagree) (hS := hcover) (i := some k)
        (by simpa [cover] using hafirst)]
      simp [canonicalMuHilbertMinimizerCubeSet, U, ha, k, piece, cover]
    · have ha_notS : a ∉ S := by
        intro haS
        rcases Set.mem_iUnion.mp haS with ⟨k, hafirst⟩
        exact ha ⟨k, hafirst.1⟩
      rw [Set.liftCover_of_mem
        (S := cover) (f := piece) (hf := hagree) (hS := hcover) (i := none)
        (by simpa [cover] using ha_notS)]
      simp [canonicalMuHilbertMinimizerCubeSet, U, ha, piece, cover]
  simpa [hEq, U] using hLift

private theorem measurable_canonicalMuHilbertEnergyBilinFixedCubeSet_localSigma
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (P0 : BlockVec d)
    (Y : BlockState d) (hY : MemBlockL2 (cubeSet Q) Y.eval) :
    @Measurable (CoeffField d) ℝ
      (localSigma (cubeSet Q)) (borel ℝ)
      (canonicalMuHilbertEnergyBilinFixedCubeSet Q P0 Y hY) := by
  classical
  let U : Set (Vec d) := cubeSet Q
  letI : MeasurableSpace (CoeffField d) := localSigma U
  let slice : ℕ → Set (CoeffField d) :=
    fun k => {a : CoeffField d | AEEQuantitativeEllipticSlice U k a}
  let firstSlice : ℕ → Set (CoeffField d) :=
    fun k => slice k ∩ ⋂ j ∈ Finset.range k, (slice j)ᶜ
  let S : Set (CoeffField d) := ⋃ k : ℕ, firstSlice k
  let cover : Option ℕ → Set (CoeffField d)
    | none => Sᶜ
    | some k => firstSlice k
  let piece : (i : Option ℕ) → cover i → ℝ
    | none, _ => 0
    | some k, a => by
        let ak :
            {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} :=
          ⟨a.1, by simpa [U] using a.2.1⟩
        exact
          ((canonicalAEEMuOperatorSystemData Q k ak).toMuHilbertRealization).energyBilin
            (toHilbertBlockL2OfBlockField (U := cubeSet Q) hY)
            (((canonicalAEEMuOperatorSystemData Q k ak).toMuHilbertRealization).minimizerMap P0)
  have hslice_meas : ∀ k : ℕ, MeasurableSet (slice k) := by
    intro k
    simpa [slice, U] using
      hP.measurableSet_aeeQuantitativeEllipticSlice_cubeSet Q k
  have hfirst_meas : ∀ k : ℕ, MeasurableSet (firstSlice k) := by
    intro k
    have hprev :
        MeasurableSet (⋂ j ∈ Finset.range k, (slice j)ᶜ) :=
      (Finset.range k).measurableSet_biInter fun j _hj => (hslice_meas j).compl
    exact (hslice_meas k).inter hprev
  have hcover_meas : ∀ i : Option ℕ, MeasurableSet (cover i) := by
    intro i
    cases i with
    | none => exact (MeasurableSet.iUnion hfirst_meas).compl
    | some k => exact hfirst_meas k
  have hfirst_unique :
      ∀ {i j : ℕ} {a : CoeffField d}, a ∈ firstSlice i → a ∈ firstSlice j → i = j := by
    intro i j a hi hj
    by_cases hij : i = j
    · exact hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hnot : a ∉ slice i := by
        have hcompl : a ∈ (slice i)ᶜ := by
          simpa using
            (Set.mem_iInter.mp
              (Set.mem_iInter.mp hj.2 i)
              (by simpa using hlt))
        simpa using hcompl
      exact False.elim (hnot hi.1)
    · have hnot : a ∉ slice j := by
        have hcompl : a ∈ (slice j)ᶜ := by
          simpa using
            (Set.mem_iInter.mp
              (Set.mem_iInter.mp hi.2 j)
              (by simpa using hgt))
        simpa using hcompl
      exact False.elim (hnot hj.1)
  have hagree :
      ∀ (i j : Option ℕ) (a : CoeffField d)
        (hai : a ∈ cover i) (haj : a ∈ cover j),
        piece i ⟨a, hai⟩ = piece j ⟨a, haj⟩ := by
    intro i j a hai haj
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some k =>
            exfalso
            have haS : a ∈ S := Set.mem_iUnion.mpr ⟨k, by simpa [cover] using haj⟩
            have hnotS : a ∉ S := by simpa [cover] using hai
            exact hnotS haS
    | some i =>
        cases j with
        | none =>
            exfalso
            have haS : a ∈ S := Set.mem_iUnion.mpr ⟨i, by simpa [cover] using hai⟩
            have hnotS : a ∉ S := by simpa [cover] using haj
            exact hnotS haS
        | some j =>
            have hij : i = j := hfirst_unique (by simpa [cover] using hai) (by simpa [cover] using haj)
            subst j
            rfl
  have hcover : ⋃ i : Option ℕ, cover i = Set.univ := by
    ext a
    constructor
    · intro _ha
      exact Set.mem_univ a
    · intro _ha
      by_cases haS : a ∈ S
      · rcases Set.mem_iUnion.mp haS with ⟨k, hak⟩
        exact Set.mem_iUnion.mpr ⟨some k, by simpa [cover] using hak⟩
      · exact Set.mem_iUnion.mpr ⟨none, by simpa [cover] using haS⟩
  have hpiece_meas : ∀ i : Option ℕ, Measurable (piece i) := by
    intro i
    cases i with
    | none => exact measurable_const
    | some k =>
        let sliceSubtype :=
          {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
        letI : MeasurableSpace sliceSubtype :=
          AEEQuantitativeEllipticSlice.localMeasurableSpace U k
        let toSlice : cover (some k) → sliceSubtype :=
          fun a => ⟨a.1, a.2.1⟩
        have htoSlice :
            @Measurable (cover (some k)) sliceSubtype
              (inferInstance : MeasurableSpace (cover (some k)))
              (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) toSlice := by
          apply Measurable.of_comap_le
          unfold AEEQuantitativeEllipticSlice.localMeasurableSpace
          rw [MeasurableSpace.comap_comp]
          rw [show Subtype.val ∘ toSlice = Subtype.val by
            funext a
            rfl]
          exact
            (measurable_subtype_coe :
              @Measurable (cover (some k)) (CoeffField d)
                (inferInstance : MeasurableSpace (cover (some k))) (localSigma U)
                Subtype.val).comap_le
        have hslice : Measurable
            (fun a : sliceSubtype =>
              ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyBilin
                (toHilbertBlockL2OfBlockField (U := cubeSet Q) hY)
                (((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).minimizerMap P0)) := by
          simpa [sliceSubtype, U] using
            Homogenization.measurable_energyBilin_fixed_canonicalAEEMuHilbertMinimizer_aeeQuantitativeSlice_cubeSet
              (Q := Q) (k := k) P0 Y hY
        change Measurable (fun a : cover (some k) =>
          ((canonicalAEEMuOperatorSystemData Q k (toSlice a)).toMuHilbertRealization).energyBilin
            (toHilbertBlockL2OfBlockField (U := cubeSet Q) hY)
            (((canonicalAEEMuOperatorSystemData Q k (toSlice a)).toMuHilbertRealization).minimizerMap P0))
        exact hslice.comp htoSlice
  have hLift : Measurable (Set.liftCover cover piece hagree hcover) :=
    measurable_liftCover cover hcover_meas piece hpiece_meas hagree hcover
  have hEq :
      Set.liftCover cover piece hagree hcover =
        canonicalMuHilbertEnergyBilinFixedCubeSet Q P0 Y hY := by
    funext a
    by_cases ha : ∃ k : ℕ, AEEQuantitativeEllipticSlice U k a
    · let k : ℕ := Nat.find ha
      have hafirst : a ∈ firstSlice k := by
        refine ⟨?_, ?_⟩
        · simpa [slice, k] using Nat.find_spec ha
        · refine Set.mem_iInter.mpr ?_
          intro j
          refine Set.mem_iInter.mpr ?_
          intro hj
          have hjlt : j < k := by simpa [k] using hj
          have hnot : ¬ AEEQuantitativeEllipticSlice U j a := by
            intro hja
            exact (not_lt_of_ge (Nat.find_min' ha hja)) (by simpa [k] using hjlt)
          simpa [slice] using hnot
      rw [Set.liftCover_of_mem
        (S := cover) (f := piece) (hf := hagree) (hS := hcover) (i := some k)
        (by simpa [cover] using hafirst)]
      simp [canonicalMuHilbertEnergyBilinFixedCubeSet, U, ha, k, piece, cover]
    · have ha_notS : a ∉ S := by
        intro haS
        rcases Set.mem_iUnion.mp haS with ⟨k, hafirst⟩
        exact ha ⟨k, hafirst.1⟩
      rw [Set.liftCover_of_mem
        (S := cover) (f := piece) (hf := hagree) (hS := hcover) (i := none)
        (by simpa [cover] using ha_notS)]
      simp [canonicalMuHilbertEnergyBilinFixedCubeSet, U, ha, piece, cover]
  simpa [hEq, U] using hLift

/-- Public Ch4 law-facing measurability of the selected canonical doubled-`Mu`
Hilbert minimizer on a deterministic cube. -/
theorem aestronglyMeasurable_canonicalMuHilbertMinimizer_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (P0 : BlockVec d) :
    AEStronglyMeasurable (canonicalMuHilbertMinimizerCubeSet Q P0) P := by
  classical
  let U : Set (Vec d) := cubeSet Q
  letI : MeasurableSpace (HilbertBlockL2 U) := borel _
  haveI : BorelSpace (HilbertBlockL2 U) := ⟨rfl⟩
  let f : CoeffField d → HilbertBlockL2 U :=
    canonicalMuHilbertMinimizerCubeSet Q P0
  have hLocalMeas :
      @Measurable (CoeffField d) (HilbertBlockL2 U)
        (localSigma U) (borel (HilbertBlockL2 U)) f := by
    simpa [f, U] using measurable_canonicalMuHilbertMinimizerCubeSet_localSigma hP Q P0
  have hNull : NullMeasurable f P := by
    intro s hs
    exact hP.local_observable_measurable.nullMeasurable_localSigma U
      (by simpa [U] using isBounded_cubeSet Q) (f ⁻¹' s) (hLocalMeas hs)
  let sliceRange : ℕ → Set (HilbertBlockL2 U) := fun k =>
    Set.range fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} =>
      ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).minimizerMap P0
  let sepSet : Set (HilbertBlockL2 U) :=
    ({0} : Set (HilbertBlockL2 U)) ∪ ⋃ k : ℕ, sliceRange k
  have hSep : TopologicalSpace.IsSeparable sepSet := by
    have hSlices : TopologicalSpace.IsSeparable (⋃ k : ℕ, sliceRange k) := by
      refine .iUnion ?_
      intro k
      let sliceSubtype :=
        {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
      letI : MeasurableSpace sliceSubtype :=
        AEEQuantitativeEllipticSlice.localMeasurableSpace U k
      have hslice : StronglyMeasurable
          (fun a : sliceSubtype =>
            ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).minimizerMap P0) := by
        simpa [U] using
          Homogenization.stronglyMeasurable_canonicalAEEMuHilbertMinimizer_aeeQuantitativeSlice_cubeSet
            (Q := Q) (k := k) P0
      simpa [sliceRange] using hslice.isSeparable_range
    exact (Set.finite_singleton (0 : HilbertBlockL2 U)).isSeparable.union hSlices
  have hMemSep : ∀ᵐ a ∂P, f a ∈ sepSet := by
    refine Filter.Eventually.of_forall ?_
    intro a
    by_cases ha : ∃ k : ℕ, AEEQuantitativeEllipticSlice U k a
    · let k : ℕ := Nat.find ha
      have hslice : AEEQuantitativeEllipticSlice U k a := by
        simpa [k] using Nat.find_spec ha
      right
      exact Set.mem_iUnion.mpr
        ⟨k, ⟨⟨a, hslice⟩, by simp [f, canonicalMuHilbertMinimizerCubeSet, U, ha, k]⟩⟩
    · left
      simp [f, canonicalMuHilbertMinimizerCubeSet, U, ha]
  exact (aestronglyMeasurable_iff_nullMeasurable_separable).2
    ⟨hNull, ⟨sepSet, hSep, hMemSep⟩⟩

/-- Law-facing strong measurability of the potential component of the selected
doubled-`Mu` Hilbert minimizer. -/
theorem aestronglyMeasurable_canonicalMuHilbertPotential_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (P0 : BlockVec d) :
    AEStronglyMeasurable (canonicalMuHilbertPotentialCubeSet Q P0) P := by
  have hmin := hP.aestronglyMeasurable_canonicalMuHilbertMinimizer_cubeSet Q P0
  simpa [canonicalMuHilbertPotentialCubeSet] using
    (hilbertBlockL2PotentialCLM (d := d) (U := cubeSet Q)).continuous.comp_aestronglyMeasurable hmin

/-- Law-facing strong measurability of the flux component of the selected
doubled-`Mu` Hilbert minimizer. -/
theorem aestronglyMeasurable_canonicalMuHilbertFlux_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (P0 : BlockVec d) :
    AEStronglyMeasurable (canonicalMuHilbertFluxCubeSet Q P0) P := by
  have hmin := hP.aestronglyMeasurable_canonicalMuHilbertMinimizer_cubeSet Q P0
  simpa [canonicalMuHilbertFluxCubeSet] using
    (hilbertBlockL2FluxCLM (d := d) (U := cubeSet Q)).continuous.comp_aestronglyMeasurable hmin

/-- Law-facing a.e.-measurability of the potential component of the selected
doubled-`Mu` Hilbert minimizer. -/
theorem aemeasurable_canonicalMuHilbertPotential_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (P0 : BlockVec d) :
    AEMeasurable (canonicalMuHilbertPotentialCubeSet Q P0) P :=
  (hP.aestronglyMeasurable_canonicalMuHilbertPotential_cubeSet Q P0).aemeasurable

/-- Law-facing a.e.-measurability of the flux component of the selected
doubled-`Mu` Hilbert minimizer. -/
theorem aemeasurable_canonicalMuHilbertFlux_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (P0 : BlockVec d) :
    AEMeasurable (canonicalMuHilbertFluxCubeSet Q P0) P :=
  (hP.aestronglyMeasurable_canonicalMuHilbertFlux_cubeSet Q P0).aemeasurable

/-- Law-facing strong measurability of the selected doubled-`Mu` potential field. -/
theorem aestronglyMeasurable_canonicalDoubledMuResponsePotentialField_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (p q : Vec d) :
    AEStronglyMeasurable (canonicalDoubledMuResponsePotentialFieldCubeSet Q p q) P := by
  simpa [canonicalDoubledMuResponsePotentialFieldCubeSet] using
    hP.aestronglyMeasurable_canonicalMuHilbertPotential_cubeSet Q (-p, q)

/-- Law-facing strong measurability of the selected doubled-`Mu` flux field. -/
theorem aestronglyMeasurable_canonicalDoubledMuResponseFluxField_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (p q : Vec d) :
    AEStronglyMeasurable (canonicalDoubledMuResponseFluxFieldCubeSet Q p q) P := by
  simpa [canonicalDoubledMuResponseFluxFieldCubeSet] using
    hP.aestronglyMeasurable_canonicalMuHilbertFlux_cubeSet Q (-p, q)

/-- Law-facing a.e.-measurability of the selected doubled-`Mu` potential field. -/
theorem aemeasurable_canonicalDoubledMuResponsePotentialField_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (p q : Vec d) :
    AEMeasurable (canonicalDoubledMuResponsePotentialFieldCubeSet Q p q) P :=
  (hP.aestronglyMeasurable_canonicalDoubledMuResponsePotentialField_cubeSet Q p q).aemeasurable

/-- Law-facing a.e.-measurability of the selected doubled-`Mu` flux field. -/
theorem aemeasurable_canonicalDoubledMuResponseFluxField_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (p q : Vec d) :
    AEMeasurable (canonicalDoubledMuResponseFluxFieldCubeSet Q p q) P :=
  (hP.aestronglyMeasurable_canonicalDoubledMuResponseFluxField_cubeSet Q p q).aemeasurable

/-- Law-facing measurability of selected doubled-`Mu` potential averages over a
deterministic subcube. -/
theorem aemeasurable_canonicalDoubledMuResponsePotentialFieldAverage_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q R : TriadicCube d) (p q : Vec d) :
    AEMeasurable (canonicalDoubledMuResponsePotentialFieldAverageCubeSet Q R p q) P := by
  rw [aemeasurable_pi_iff]
  intro i
  let ℓ : HilbertVectorL2 (cubeSet Q) →L[ℝ] ℝ :=
    (cubeVolume R)⁻¹ •
      hilbertVectorL2CoordSetIntegralCLM (U := cubeSet Q)
        (cubeSet R) (measurableSet_cubeSet R) i
  have hfield := hP.aestronglyMeasurable_canonicalDoubledMuResponsePotentialField_cubeSet Q p q
  have hℓ : AEMeasurable (fun a : CoeffField d => ℓ (canonicalDoubledMuResponsePotentialFieldCubeSet Q p q a)) P :=
    (ℓ.continuous.comp_aestronglyMeasurable hfield).aemeasurable
  simpa [canonicalDoubledMuResponsePotentialFieldAverageCubeSet, ℓ, smul_eq_mul] using hℓ

/-- Law-facing measurability of selected doubled-`Mu` flux averages over a
deterministic subcube. -/
theorem aemeasurable_canonicalDoubledMuResponseFluxFieldAverage_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q R : TriadicCube d) (p q : Vec d) :
    AEMeasurable (canonicalDoubledMuResponseFluxFieldAverageCubeSet Q R p q) P := by
  rw [aemeasurable_pi_iff]
  intro i
  let ℓ : HilbertVectorL2 (cubeSet Q) →L[ℝ] ℝ :=
    (cubeVolume R)⁻¹ •
      hilbertVectorL2CoordSetIntegralCLM (U := cubeSet Q)
        (cubeSet R) (measurableSet_cubeSet R) i
  have hfield := hP.aestronglyMeasurable_canonicalDoubledMuResponseFluxField_cubeSet Q p q
  have hℓ : AEMeasurable (fun a : CoeffField d => ℓ (canonicalDoubledMuResponseFluxFieldCubeSet Q p q a)) P :=
    (ℓ.continuous.comp_aestronglyMeasurable hfield).aemeasurable
  simpa [canonicalDoubledMuResponseFluxFieldAverageCubeSet, ℓ, smul_eq_mul] using hℓ

/-- Law-facing measurability of finite descendant averages of selected
response-gradient averages. -/
theorem aemeasurable_descendantsAverageCanonicalDoubledMuResponsePotentialFieldAverage_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    AEMeasurable
      (descendantsAverageCanonicalDoubledMuResponsePotentialFieldAverageCubeSet Q j p q) P := by
  rw [aemeasurable_pi_iff]
  intro i
  exact
    aemeasurable_descendantsAverage
      (P := P) (Q := Q) (j := j)
      (F := fun R a => canonicalDoubledMuResponsePotentialFieldAverageCubeSet Q R p q a i)
      (fun R _hR =>
        (aemeasurable_pi_iff.mp
          (hP.aemeasurable_canonicalDoubledMuResponsePotentialFieldAverage_cubeSet Q R p q)) i)

/-- Law-facing measurability of finite descendant averages of selected
response-flux averages. -/
theorem aemeasurable_descendantsAverageCanonicalDoubledMuResponseFluxFieldAverage_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    AEMeasurable
      (descendantsAverageCanonicalDoubledMuResponseFluxFieldAverageCubeSet Q j p q) P := by
  rw [aemeasurable_pi_iff]
  intro i
  exact
    aemeasurable_descendantsAverage
      (P := P) (Q := Q) (j := j)
      (F := fun R a => canonicalDoubledMuResponseFluxFieldAverageCubeSet Q R p q a i)
      (fun R _hR =>
        (aemeasurable_pi_iff.mp
          (hP.aemeasurable_canonicalDoubledMuResponseFluxFieldAverage_cubeSet Q R p q)) i)

/-- Law-facing measurability of finite-depth selected response-gradient weak
norms. -/
theorem aemeasurable_canonicalDoubledMuResponsePotentialWeakNormPartial_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (p q p0 : Vec d) :
    AEMeasurable (canonicalDoubledMuResponsePotentialWeakNormPartialCubeSet Q s N p q p0) P := by
  unfold canonicalDoubledMuResponsePotentialWeakNormPartialCubeSet
  exact
    Finset.aemeasurable_fun_sum (Finset.range (N + 1)) fun j _hj =>
      (aemeasurable_const.mul <|
        (aemeasurable_descendantsAverage
          (P := P) (Q := Q) (j := j)
          (F := fun R a =>
            vecNormSq (canonicalDoubledMuResponsePotentialFieldAverageCubeSet Q R p q a - p0))
          (fun R _hR =>
            aemeasurable_vecNormSq_sub_const
              (hP.aemeasurable_canonicalDoubledMuResponsePotentialFieldAverage_cubeSet Q R p q) p0)).sqrt)

/-- Law-facing measurability of finite-depth selected response-flux weak
norms. -/
theorem aemeasurable_canonicalDoubledMuResponseFluxWeakNormPartial_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (t : ℝ) (N : ℕ) (p q q0 : Vec d) :
    AEMeasurable (canonicalDoubledMuResponseFluxWeakNormPartialCubeSet Q t N p q q0) P := by
  unfold canonicalDoubledMuResponseFluxWeakNormPartialCubeSet
  exact
    Finset.aemeasurable_fun_sum (Finset.range (N + 1)) fun j _hj =>
      (aemeasurable_const.mul <|
        (aemeasurable_descendantsAverage
          (P := P) (Q := Q) (j := j)
          (F := fun R a =>
            vecNormSq (canonicalDoubledMuResponseFluxFieldAverageCubeSet Q R p q a - q0))
          (fun R _hR =>
            aemeasurable_vecNormSq_sub_const
              (hP.aemeasurable_canonicalDoubledMuResponseFluxFieldAverage_cubeSet Q R p q) q0)).sqrt)

/-- Law-facing measurability of the selected doubled-`Mu` potential weak norm. -/
theorem aemeasurable_canonicalDoubledMuResponsePotentialWeakNorm_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (s : ℝ) (p q p0 : Vec d) :
    AEMeasurable (canonicalDoubledMuResponsePotentialWeakNormCubeSet Q s p q p0) P := by
  simpa [canonicalDoubledMuResponsePotentialWeakNormCubeSet] using
    (AEMeasurable.iSup fun N =>
      hP.aemeasurable_canonicalDoubledMuResponsePotentialWeakNormPartial_cubeSet Q s N p q p0)

/-- Law-facing measurability of the selected doubled-`Mu` flux weak norm. -/
theorem aemeasurable_canonicalDoubledMuResponseFluxWeakNorm_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (t : ℝ) (p q q0 : Vec d) :
    AEMeasurable (canonicalDoubledMuResponseFluxWeakNormCubeSet Q t p q q0) P := by
  simpa [canonicalDoubledMuResponseFluxWeakNormCubeSet] using
    (AEMeasurable.iSup fun N =>
      hP.aemeasurable_canonicalDoubledMuResponseFluxWeakNormPartial_cubeSet Q t N p q q0)

/-- Law-facing measurability of a fixed-test Hilbert energy pairing against
the selected canonical doubled-`Mu` minimizer. This is the public Ch4 source for
raw scalar-response operator-image averages. -/
theorem aemeasurable_canonicalMuHilbertEnergyBilinFixed_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (P0 : BlockVec d)
    (Y : BlockState d) (hY : MemBlockL2 (cubeSet Q) Y.eval) :
    AEMeasurable (canonicalMuHilbertEnergyBilinFixedCubeSet Q P0 Y hY) P := by
  refine NullMeasurable.aemeasurable ?_
  intro s hs
  have hLocal :
      @Measurable (CoeffField d) ℝ
        (localSigma (cubeSet Q)) (borel ℝ)
        (canonicalMuHilbertEnergyBilinFixedCubeSet Q P0 Y hY) :=
    measurable_canonicalMuHilbertEnergyBilinFixedCubeSet_localSigma hP Q P0 Y hY
  exact hP.local_observable_measurable.nullMeasurable_localSigma
    (cubeSet Q)
    (isBounded_cubeSet Q)
    ((canonicalMuHilbertEnergyBilinFixedCubeSet Q P0 Y hY) ⁻¹' s)
    (hLocal hs)

/-- Law-facing measurability of the upper coefficient-operator image averages
of the selected doubled-`Mu` response minimizer. -/
theorem aemeasurable_canonicalDoubledMuResponseUpperImageAverage_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q R : TriadicCube d) (p q : Vec d) :
    AEMeasurable (canonicalDoubledMuResponseUpperImageAverageCubeSet Q R p q) P := by
  rw [aemeasurable_pi_iff]
  intro i
  have hpair :=
    hP.aemeasurable_canonicalMuHilbertEnergyBilinFixed_cubeSet Q (-p, q)
      (canonicalUpperImageIndicatorTestStateCubeSet R i)
      (canonicalUpperImageIndicatorTestStateCubeSet_memBlockL2 Q R i)
  simpa [canonicalDoubledMuResponseUpperImageAverageCubeSet, mul_assoc] using
    hpair.const_mul (cubeVolume Q * (cubeVolume R)⁻¹)

/-- Law-facing measurability of the lower coefficient-operator image averages
of the selected doubled-`Mu` response minimizer. -/
theorem aemeasurable_canonicalDoubledMuResponseLowerImageAverage_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q R : TriadicCube d) (p q : Vec d) :
    AEMeasurable (canonicalDoubledMuResponseLowerImageAverageCubeSet Q R p q) P := by
  rw [aemeasurable_pi_iff]
  intro i
  have hpair :=
    hP.aemeasurable_canonicalMuHilbertEnergyBilinFixed_cubeSet Q (-p, q)
      (canonicalLowerImageIndicatorTestStateCubeSet R i)
      (canonicalLowerImageIndicatorTestStateCubeSet_memBlockL2 Q R i)
  simpa [canonicalDoubledMuResponseLowerImageAverageCubeSet, mul_assoc] using
    hpair.const_mul (cubeVolume Q * (cubeVolume R)⁻¹)

/-- Law-facing measurability of raw scalar response-gradient averages
`avg_R grad v_m`. -/
theorem aemeasurable_canonicalScalarResponseGradientAverage_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q R : TriadicCube d) (p q : Vec d) :
    AEMeasurable (canonicalScalarResponseGradientAverageCubeSet Q R p q) P := by
  rw [aemeasurable_pi_iff]
  intro i
  have hPot :=
    (aemeasurable_pi_iff.mp
      (hP.aemeasurable_canonicalDoubledMuResponsePotentialFieldAverage_cubeSet Q R p q)) i
  have hLower :=
    (aemeasurable_pi_iff.mp
      (hP.aemeasurable_canonicalDoubledMuResponseLowerImageAverage_cubeSet Q R p q)) i
  simpa [canonicalScalarResponseGradientAverageCubeSet, Pi.add_apply] using hPot.add hLower

/-- Law-facing measurability of raw scalar response-flux averages
`avg_R a grad v_m`. -/
theorem aemeasurable_canonicalScalarResponseFluxAverage_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q R : TriadicCube d) (p q : Vec d) :
    AEMeasurable (canonicalScalarResponseFluxAverageCubeSet Q R p q) P := by
  rw [aemeasurable_pi_iff]
  intro i
  have hFlux :=
    (aemeasurable_pi_iff.mp
      (hP.aemeasurable_canonicalDoubledMuResponseFluxFieldAverage_cubeSet Q R p q)) i
  have hUpper :=
    (aemeasurable_pi_iff.mp
      (hP.aemeasurable_canonicalDoubledMuResponseUpperImageAverage_cubeSet Q R p q)) i
  simpa [canonicalScalarResponseFluxAverageCubeSet, Pi.add_apply] using hFlux.add hUpper

/-- Law-facing measurability of finite-depth raw scalar response-gradient weak
norms. -/
theorem aemeasurable_canonicalScalarResponseGradientWeakNormPartial_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (p q p0 : Vec d) :
    AEMeasurable (canonicalScalarResponseGradientWeakNormPartialCubeSet Q s N p q p0) P := by
  unfold canonicalScalarResponseGradientWeakNormPartialCubeSet
  exact
    Finset.aemeasurable_fun_sum (Finset.range (N + 1)) fun j _hj =>
      (aemeasurable_const.mul <|
        (aemeasurable_descendantsAverage
          (P := P) (Q := Q) (j := j)
          (F := fun R a =>
            vecNormSq (canonicalScalarResponseGradientAverageCubeSet Q R p q a - p0))
          (fun R _hR =>
            aemeasurable_vecNormSq_sub_const
              (hP.aemeasurable_canonicalScalarResponseGradientAverage_cubeSet Q R p q) p0)).sqrt)

/-- Law-facing measurability of finite-depth raw scalar response-flux weak
norms. -/
theorem aemeasurable_canonicalScalarResponseFluxWeakNormPartial_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (t : ℝ) (N : ℕ) (p q q0 : Vec d) :
    AEMeasurable (canonicalScalarResponseFluxWeakNormPartialCubeSet Q t N p q q0) P := by
  unfold canonicalScalarResponseFluxWeakNormPartialCubeSet
  exact
    Finset.aemeasurable_fun_sum (Finset.range (N + 1)) fun j _hj =>
      (aemeasurable_const.mul <|
        (aemeasurable_descendantsAverage
          (P := P) (Q := Q) (j := j)
          (F := fun R a =>
            vecNormSq (canonicalScalarResponseFluxAverageCubeSet Q R p q a - q0))
          (fun R _hR =>
            aemeasurable_vecNormSq_sub_const
              (hP.aemeasurable_canonicalScalarResponseFluxAverage_cubeSet Q R p q) q0)).sqrt)

/-- Law-facing measurability of the full raw scalar response-gradient weak
norm. -/
theorem aemeasurable_canonicalScalarResponseGradientWeakNorm_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (s : ℝ) (p q p0 : Vec d) :
    AEMeasurable (canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0) P := by
  simpa [canonicalScalarResponseGradientWeakNormCubeSet] using
    (AEMeasurable.iSup fun N =>
      hP.aemeasurable_canonicalScalarResponseGradientWeakNormPartial_cubeSet Q s N p q p0)

/-- Law-facing measurability of the full raw scalar response-flux weak norm. -/
theorem aemeasurable_canonicalScalarResponseFluxWeakNorm_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (t : ℝ) (p q q0 : Vec d) :
    AEMeasurable (canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0) P := by
  simpa [canonicalScalarResponseFluxWeakNormCubeSet] using
    (AEMeasurable.iSup fun N =>
      hP.aemeasurable_canonicalScalarResponseFluxWeakNormPartial_cubeSet Q t N p q q0)

/-- Law-facing strong measurability of the full raw scalar response-gradient
weak norm. -/
theorem aestronglyMeasurable_canonicalScalarResponseGradientWeakNorm_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (s : ℝ) (p q p0 : Vec d) :
    AEStronglyMeasurable (canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0) P :=
  (hP.aemeasurable_canonicalScalarResponseGradientWeakNorm_cubeSet Q s p q p0).aestronglyMeasurable

/-- Law-facing strong measurability of the full raw scalar response-flux weak
norm. -/
theorem aestronglyMeasurable_canonicalScalarResponseFluxWeakNorm_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (t : ℝ) (p q q0 : Vec d) :
    AEStronglyMeasurable (canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0) P :=
  (hP.aemeasurable_canonicalScalarResponseFluxWeakNorm_cubeSet Q t p q q0).aestronglyMeasurable

end LawCarrier

end Ch04
end Book
end Homogenization
