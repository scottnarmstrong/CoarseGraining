import Homogenization.Probability.Source.Coarse.Semantics
import Homogenization.Probability.Source.Coarse.RegIntegralAdapter
import Homogenization.Probability.Source.Coarse.Laws
import Homogenization.Probability.RegCoeffField.Laws
import Homogenization.Examples.RandomCheckerboard.SourceLaw
import Homogenization.Examples.RandomCheckerboard.AKLLaw

/-!
# Semantic regressions for source measurability and locality

The coarse source and its regular realizations use the same pointwise
representatives, but distinct measurable structures and laws.  In particular,
there is no canonical measurable `Measure.map` transport from the coarse
integral sigma algebra to the pointwise regular carrier.  Nor is there a
generic P2 implication between the two lanes: their separation metrics differ.
-/

namespace Audit.MeasurabilityLocality.SemanticRegression

open MeasureTheory ProbabilityTheory
open Homogenization
open scoped ENNReal NNReal

noncomputable section

/-- The integral-local coarse sigma algebra sees no singleton information. -/
theorem coarse_localSigma_singleton_eq_bot {d : ℕ} (x : Vec d) [NeZero d] :
    Source.Coarse.localSigma ({x} : Set (Vec d)) (MeasurableSet.singleton x) = ⊥ :=
  Source.Coarse.localSigma_singleton_eq_bot x

/-- Point entries remain observable in the regular restriction sigma algebra. -/
theorem regular_point_entry_measurable_from_singleton_restriction
    {d : ℕ} (x : Vec d) (i j : Fin d) :
    @Measurable (RegCoeffField d) ℝ
      (RestrictionSigmaR ({x} : Set (Vec d)) (MeasurableSet.singleton x)) _
      (fun a : RegCoeffField d => a x i j) :=
  measurable_apply_entry_restrictionSigmaR_of_mem (MeasurableSet.singleton x) (by simp) i j

private def pointZero : Vec 1 := fun _ => 0
private def pointTwo : Vec 1 := fun _ => 2

private def exceptionalPoints : Set (Vec 1) := {pointZero, pointTwo}

private def scalarOne : Mat 1 := scalarMatrix 1
private def scalarTwo : Mat 1 := scalarMatrix 2

private theorem isElliptic_scalarOne : IsEllipticMatrix (1 / 2 : ℝ) 2 scalarOne := by
  exact (isEllipticMatrix_scalarMatrix (d := 1) (by norm_num : (0 : ℝ) < 1)).mono
    (by norm_num) (by norm_num) (by norm_num)

private theorem isElliptic_scalarTwo : IsEllipticMatrix (1 / 2 : ℝ) 2 scalarTwo := by
  exact (isEllipticMatrix_scalarMatrix (d := 1) (by norm_num : (0 : ℝ) < 2)).mono
    (by norm_num) (by norm_num) (by norm_num)

private theorem measurableSet_exceptionalPoints : MeasurableSet exceptionalPoints := by
  simp [exceptionalPoints]

private def a0 : Source.Coarse.Carrier 1 where
  val := fun _ => scalarOne
  property := by
    constructor
    · intro i j
      exact measurable_const
    · intro R hR
      exact ⟨1 / 2, by norm_num, by norm_num, fun _ _ => by
        convert isElliptic_scalarOne using 1
        all_goals norm_num⟩

private noncomputable def a1 : Source.Coarse.Carrier 1 :=
  letI : DecidablePred (fun x : Vec 1 => x ∈ exceptionalPoints) := Classical.decPred _
  { val := fun x => if x ∈ exceptionalPoints then scalarTwo else scalarOne
    property := by
      constructor
      · intro i j
        have hEntry :
            (fun x : Vec 1 => (fun x =>
              if x ∈ exceptionalPoints then scalarTwo else scalarOne) x i j) =
              fun x => if x ∈ exceptionalPoints then scalarTwo i j else scalarOne i j := by
          funext x
          by_cases hx : x ∈ exceptionalPoints <;> simp [hx]
        rw [hEntry]
        exact measurable_const.ite measurableSet_exceptionalPoints measurable_const
      · intro R hR
        exact ⟨1 / 2, by norm_num, by norm_num, fun x _ => by
          change IsEllipticMatrix (1 / 2 : ℝ) (1 / 2 : ℝ)⁻¹
            (if x ∈ exceptionalPoints then scalarTwo else scalarOne)
          by_cases hx : x ∈ exceptionalPoints
          · rw [if_pos hx]
            convert isElliptic_scalarTwo using 1
            all_goals norm_num
          · rw [if_neg hx]
            convert isElliptic_scalarOne using 1
            all_goals norm_num⟩ }

private theorem volume_exceptionalPoints : volume exceptionalPoints = 0 := by
  apply measure_mono_null ?_ (measure_union_null (measure_singleton pointZero)
    (measure_singleton pointTwo))
  intro x hx
  simpa [exceptionalPoints, or_comm] using hx

private theorem a0_ae_eq_a1 : (a0 : CoeffField 1) =ᵐ[volume] (a1 : CoeffField 1) := by
  have houtside : ∀ᵐ x ∂volume, x ∉ exceptionalPoints := by
    refine (ae_iff).2 ?_
    simpa only [not_not] using volume_exceptionalPoints
  filter_upwards [houtside] with x hx
  simp [a0, a1, hx]

private theorem a0_ne_a1 : a0 ≠ a1 := by
  intro h
  have hentry := congrArg (fun a : Source.Coarse.Carrier 1 => a pointZero 0 0) h
  norm_num [a0, a1, exceptionalPoints, pointZero, pointTwo, scalarOne, scalarTwo] at hentry

private theorem bilinearTest_a0_eq_a1 (e e' : Vec 1) (φ : Vec 1 → ℝ) :
    Source.Coarse.bilinearTest e e' φ a0 = Source.Coarse.bilinearTest e e' φ a1 := by
  unfold Source.Coarse.bilinearTest
  apply integral_congr_ae
  filter_upwards [a0_ae_eq_a1] with x hx
  simp [hx]

/-- Integral-global coarse events cannot distinguish the two representatives. -/
private theorem coarse_global_event_a0_mem_iff_a1_mem (s : Set (Source.Coarse.Carrier 1))
    (hs : MeasurableSet s) : a0 ∈ s ↔ a1 ∈ s := by
  let C : Set (Set (Source.Coarse.Carrier 1)) :=
    {s | ∃ (e e' : Vec 1) (φ : Vec 1 → ℝ), Source.Coarse.SmoothCompactProbe φ ∧
      ∃ t : Set ℝ, MeasurableSet t ∧
        s = Source.Coarse.bilinearTest e e' φ ⁻¹' t}
  have hC : ∀ t ∈ C, a0 ∈ t ↔ a1 ∈ t := by
    rintro t ⟨e, e', φ, _hφ, q, _hq, rfl⟩
    simp only [Set.mem_preimage]
    rw [bilinearTest_a0_eq_a1]
  have hsGlobal : @MeasurableSet (Source.Coarse.Carrier 1) (Source.Coarse.globalSigma 1) s := hs
  have hsC : @MeasurableSet (Source.Coarse.Carrier 1)
      (MeasurableSpace.generateFrom C) s := by
    simpa [Source.Coarse.globalSigma, Source.Coarse.localSigma, C] using hsGlobal
  exact (MeasurableSpace.forall_generateFrom_mem_iff_mem_iff (S := C) (x := a0) (y := a1)).2
    hC s hsC

private def coarseTwoAtomLaw : Measure (Source.Coarse.Carrier 1) :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac a0 + (1 / 2 : ℝ≥0∞) • Measure.dirac a1

/-- The syntactic two-atom coarse law is a Dirac law on the integral global sigma algebra. -/
private theorem coarse_two_atom_law_eq_dirac : coarseTwoAtomLaw = Measure.dirac a0 := by
  ext s hs
  by_cases h0 : a0 ∈ s
  · have h1 : a1 ∈ s := (coarse_global_event_a0_mem_iff_a1_mem s hs).mp h0
    simpa [coarseTwoAtomLaw, Measure.dirac_apply' _ hs, h0, h1] using ENNReal.inv_two_add_inv_two
  · have h1 : a1 ∉ s := fun ha1 => h0 ((coarse_global_event_a0_mem_iff_a1_mem s hs).mpr ha1)
    simp [coarseTwoAtomLaw, Measure.dirac_apply' _ hs, h0, h1]

/-- The coarse two-atom law is a probability law, despite its syntactic two atoms. -/
private theorem coarse_two_atom_law_isProbabilityMeasure : IsProbabilityMeasure coarseTwoAtomLaw := by
  rw [coarse_two_atom_law_eq_dirac]
  infer_instance

/-- The coarse two-atom law satisfies coarse P2 directly through its integral-global Dirac form. -/
private theorem coarse_two_atom_law_isUnitRangeDependent :
    Source.Coarse.IsUnitRangeDependent coarseTwoAtomLaw := by
  intro U V hU hV _hsep
  rw [coarse_two_atom_law_eq_dirac]
  rw [Indep_iff]
  intro s t hs ht
  have hsAmbient : MeasurableSet s :=
    Source.Coarse.localSigma_mono hU MeasurableSet.univ (Set.subset_univ _) s hs
  have htAmbient : MeasurableSet t :=
    Source.Coarse.localSigma_mono hV MeasurableSet.univ (Set.subset_univ _) t ht
  rw [Measure.dirac_apply' a0 (hsAmbient.inter htAmbient),
    Measure.dirac_apply' a0 hsAmbient, Measure.dirac_apply' a0 htAmbient]
  by_cases has : a0 ∈ s <;> by_cases hat : a0 ∈ t <;> simp [has, hat]

private def regularA0 : RegCoeffField 1 := Source.Coarse.coarseToRegular a0
private def regularA1 : RegCoeffField 1 := Source.Coarse.coarseToRegular a1

private def regularTwoAtomLaw : RegCoeffLaw 1 :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac regularA0 + (1 / 2 : ℝ≥0∞) • Measure.dirac regularA1

private theorem regularTwoAtomLaw_isProbabilityMeasure :
    IsProbabilityMeasure regularTwoAtomLaw := by
  constructor
  simp [regularTwoAtomLaw, ENNReal.inv_two_add_inv_two]

private def pointEntryEvent (x : Vec 1) : Set (RegCoeffField 1) :=
  {a | a x 0 0 = 1}

private theorem pointEntryEvent_measurable_restriction (x : Vec 1) :
    @MeasurableSet (RegCoeffField 1)
      (RestrictionSigmaR ({x} : Set (Vec 1)) (MeasurableSet.singleton x))
      (pointEntryEvent x) := by
  change @MeasurableSet (RegCoeffField 1)
    (RestrictionSigmaR ({x} : Set (Vec 1)) (MeasurableSet.singleton x))
    ((fun a : RegCoeffField 1 => a x 0 0) ⁻¹' {1})
  exact (regular_point_entry_measurable_from_singleton_restriction x 0 0)
    (MeasurableSet.singleton 1)

private theorem pointEntryEvent_measurable (x : Vec 1) :
    MeasurableSet (pointEntryEvent x) := by
  exact restrictionSigmaR_le ({x} : Set (Vec 1)) (MeasurableSet.singleton x)
    (pointEntryEvent x) (pointEntryEvent_measurable_restriction x)

private theorem regularA0_mem_pointEntryEvent (x : Vec 1) : regularA0 ∈ pointEntryEvent x := by
  norm_num [regularA0, pointEntryEvent, a0, scalarOne]

private theorem regularA1_not_mem_pointEntryEvent_of_mem_exceptionalPoints {x : Vec 1}
    (hx : x ∈ exceptionalPoints) : regularA1 ∉ pointEntryEvent x := by
  norm_num [regularA1, pointEntryEvent, a1, scalarTwo, hx]

private theorem regularTwoAtomLaw_pointZero_measure :
    regularTwoAtomLaw (pointEntryEvent pointZero) = 1 / 2 := by
  have h0 := regularA0_mem_pointEntryEvent pointZero
  have h1 := regularA1_not_mem_pointEntryEvent_of_mem_exceptionalPoints (x := pointZero) (by
    simp [exceptionalPoints])
  simp [regularTwoAtomLaw, Measure.dirac_apply' _ (pointEntryEvent_measurable pointZero), h0, h1]

private theorem regularTwoAtomLaw_pointTwo_measure :
    regularTwoAtomLaw (pointEntryEvent pointTwo) = 1 / 2 := by
  have h0 := regularA0_mem_pointEntryEvent pointTwo
  have h1 := regularA1_not_mem_pointEntryEvent_of_mem_exceptionalPoints (x := pointTwo) (by
    simp [exceptionalPoints])
  simp [regularTwoAtomLaw, Measure.dirac_apply' _ (pointEntryEvent_measurable pointTwo), h0, h1]

private theorem regularTwoAtomLaw_point_inter_measure :
    regularTwoAtomLaw (pointEntryEvent pointZero ∩ pointEntryEvent pointTwo) = 1 / 2 := by
  have h0 : regularA0 ∈ pointEntryEvent pointZero ∩ pointEntryEvent pointTwo :=
    ⟨regularA0_mem_pointEntryEvent pointZero, regularA0_mem_pointEntryEvent pointTwo⟩
  have h1 : regularA1 ∉ pointEntryEvent pointZero ∩ pointEntryEvent pointTwo := by
    intro h
    exact (regularA1_not_mem_pointEntryEvent_of_mem_exceptionalPoints (x := pointZero) (by
      simp [exceptionalPoints])) h.1
  have hmeas := (pointEntryEvent_measurable pointZero).inter (pointEntryEvent_measurable pointTwo)
  simp [regularTwoAtomLaw, Measure.dirac_apply' _ hmeas, h0, h1]

private theorem pointZero_pointTwo_areUnitSeparated :
    AreUnitSeparated ({pointZero} : Set (Vec 1)) {pointTwo} := by
  intro x y hx hy
  rcases Set.mem_singleton_iff.mp hx with rfl
  rcases Set.mem_singleton_iff.mp hy with rfl
  norm_num [pointZero, pointTwo, dist_eq_norm, Pi.norm_def]

/-- The canonical regular two-atom law fails restriction P2: its two singleton
restriction events expose one shared fair latent atom. -/
private theorem regular_two_atom_law_not_isRestrictionUnitRangeDependentR :
    ¬ IsRestrictionUnitRangeDependentR regularTwoAtomLaw := by
  intro h
  have hind := h ({pointZero} : Set (Vec 1)) {pointTwo}
    (MeasurableSet.singleton pointZero) (MeasurableSet.singleton pointTwo)
    pointZero_pointTwo_areUnitSeparated
  have hfactor := (Indep_iff _ _ regularTwoAtomLaw).1 hind
    (pointEntryEvent pointZero) (pointEntryEvent pointTwo)
    (pointEntryEvent_measurable_restriction pointZero)
    (pointEntryEvent_measurable_restriction pointTwo)
  rw [regularTwoAtomLaw_point_inter_measure, regularTwoAtomLaw_pointZero_measure,
    regularTwoAtomLaw_pointTwo_measure] at hfactor
  have hreal := congrArg ENNReal.toReal hfactor
  norm_num at hreal

/-- The total pointwise realization is not measurable from the coarse integral
global sigma algebra to the canonical regular carrier sigma algebra. -/
theorem coarseToRegular_not_measurable_global_to_regular :
    ¬ Measurable (Source.Coarse.coarseToRegular (d := 1)) := by
  intro hmeas
  have hpre : MeasurableSet
      ((Source.Coarse.coarseToRegular (d := 1)) ⁻¹' pointEntryEvent pointZero) :=
    hmeas (pointEntryEvent_measurable pointZero)
  have hindist := coarse_global_event_a0_mem_iff_a1_mem _ hpre
  have h0 : a0 ∈ (Source.Coarse.coarseToRegular (d := 1)) ⁻¹' pointEntryEvent pointZero :=
    regularA0_mem_pointEntryEvent pointZero
  have h1 : a1 ∉ (Source.Coarse.coarseToRegular (d := 1)) ⁻¹' pointEntryEvent pointZero :=
    regularA1_not_mem_pointEntryEvent_of_mem_exceptionalPoints (x := pointZero) (by
      simp [exceptionalPoints])
  exact h1 (hindist.mp h0)

private theorem ambient_supNorm_le_euclideanNorm {d : ℕ} (z : Vec d) :
    ‖z‖ ≤ euclideanNorm z := by
  rw [euclideanNorm_eq_norm_ofVec]
  rw [EuclideanSpace.norm_eq]
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro i
  apply (Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).2
  exact Finset.single_le_sum (s := Finset.univ) (f := fun i : Fin d => ‖z i‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

/-- The AKL sup distance is bounded by the explicit ambient Euclidean distance. -/
theorem akl_supDist_le_euclideanDist {d : ℕ} (x y : Vec d) :
    Source.AKL.supDist x y ≤ euclideanDist x y :=
  ambient_supNorm_le_euclideanNorm (x - y)

private def metricPointZero : Vec 2 := fun _ => 0
private def metricPointFourFifths : Vec 2 := ![3 / 5, 4 / 5]

private def metricRegionZero : Source.AKL.BorelRegion 2 :=
  ⟨{metricPointZero}, MeasurableSet.singleton metricPointZero⟩

private def metricRegionFourFifths : Source.AKL.BorelRegion 2 :=
  ⟨{metricPointFourFifths}, MeasurableSet.singleton metricPointFourFifths⟩

/-- In dimension two, Euclidean unit separation does not imply AKL sup-metric
unit separation. -/
theorem euclidean_unit_separated_not_akl_unit_separated :
    Source.Coarse.EuclideanUnitSeparated ({metricPointZero} : Set (Vec 2))
      {metricPointFourFifths} ∧
    ¬ Source.AKL.unitSeparated metricRegionZero metricRegionFourFifths := by
  constructor
  · intro x y hx hy
    rcases Set.mem_singleton_iff.mp hx with rfl
    rcases Set.mem_singleton_iff.mp hy with rfl
    norm_num [euclideanDist, euclideanNorm, metricPointZero, metricPointFourFifths,
      vecNormSq, vecDot,
      Matrix.vecHead, Matrix.vecTail]
  · intro h
    have hsep := h (x := metricPointZero) (y := metricPointFourFifths)
      (by simp [metricRegionZero]) (by simp [metricRegionFourFifths])
    norm_num [Source.AKL.supDist, metricPointZero, metricPointFourFifths, Pi.norm_def,
      Matrix.vecHead, Matrix.vecTail] at hsep
    rcases hsep with hsep | hsep
    · have hlt : (3 : ℝ) / 5 < 1 := by norm_num
      exact (not_le_of_gt hlt) hsep
    · have hlt : (4 : ℝ) / 5 < 1 := by norm_num
      exact (not_le_of_gt hlt) hsep

/-- Smoke check: the refined checkerboard inhabits the coarse Euclidean P2 lane. -/
example {d : ℕ} {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (p : ℝ≥0) (hp : p ≤ 1) :
    Source.Coarse.IsUnitRangeDependent
      (Homogenization.Examples.RandomCheckerboard.Source.law d lam Lam hlam hle p hp) :=
  Homogenization.Examples.RandomCheckerboard.Source.unitRangeDependent_law hlam hle p hp

/-- Smoke check: the ordinary checkerboard inhabits the AKL sup-metric P2 lane. -/
example {d : ℕ} {Θ : ℝ} (hΘ : 1 ≤ Θ) (p : ℝ≥0) (hp : p ≤ 1) :
    Source.AKL.UnitRangeDependent
      (Homogenization.Examples.RandomCheckerboard.AKL.law d Θ hΘ p hp) :=
  Homogenization.Examples.RandomCheckerboard.AKL.unitRangeDependent_law hΘ p hp

end

end Audit.MeasurabilityLocality.SemanticRegression
