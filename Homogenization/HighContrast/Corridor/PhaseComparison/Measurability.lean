import Homogenization.HighContrast.Corridor.Geometry
import Homogenization.CoarseGraining.CoarseBounds.LawObservable
import Homogenization.CoarseGraining.ThetaEllipticity
import Homogenization.Probability.RandomFieldMeasurability

/-!
# Per-phase measurability of the corridor observable

The coarse observable is only
a.e.-measurable under a `LawCarrier` (the C3 wrap
`aestronglyMeasurable_coarseBlockQuadratic_cubeSet`), so `comp_measurable`
cannot be applied against `L` directly.  Instead:

1. `corridorField ℓ σ` is *genuinely* `Measurable` (`measurable_corridorField`) —
   the corridor indicator is a fixed spatial set, so each ambient entry is a
   `by_cases` between a constant and a coordinate evaluation.
2. The pushforward `L.map (corridorField ℓ σ)` is again a `LawCarrier`
   (`lawCarrier_map_corridorField`): probability is preserved by measurability,
   and a.e. local uniform ellipticity is preserved by the pointwise corridor
   modification (`aeLocallyUniformlyEllipticField_corridorField`); the a.e.
   pushforward uses `MeasureTheory.ae_map_iff`, whose measurable-set side
   condition is `measurableSet_aeLocallyUniformlyEllipticField` (the countable
   `⋂_Q ⋃_k` of the AEE quantitative-slice sets).
3. The C3 wrap on the pushforward pulls back along the measurable corridor map
   via `AEStronglyMeasurable.comp_measurable` (`aestronglyMeasurable_phaseObservable`).
-/

open Homogenization
open Homogenization.Book.Ch04 (CoeffLaw LawCarrier AELocallyUniformlyEllipticField
  AELocallyUniformlyEllipticLaw lawCarrier_of_aeLocallyUniformlyElliptic)
open MeasureTheory

namespace Homogenization

variable {d : ℕ}

/-! ## The corridor set is open, hence measurable -/

/-- The corridor set is open: it is a countable union over `(i, n)` of the open
slabs `{x | |x i − σ i − n·ℓ| < 1}`. -/
theorem isOpen_corridorSet (ℓ : ℝ) (σ : Vec d) : IsOpen (corridorSet ℓ σ) := by
  have hset : corridorSet ℓ σ
      = ⋃ i : Fin d, ⋃ n : ℤ, {x : Vec d | |x i - σ i - n * ℓ| < 1} := by
    ext x
    simp only [mem_corridorSet, Set.mem_iUnion, Set.mem_setOf_eq]
  rw [hset]
  refine isOpen_iUnion fun i => isOpen_iUnion fun n => ?_
  have hcont : Continuous (fun x : Vec d => |x i - σ i - n * ℓ|) :=
    (((continuous_apply i).sub continuous_const).sub continuous_const).abs
  exact isOpen_lt hcont continuous_const

/-- The corridor set is measurable. -/
theorem measurableSet_corridorSet (ℓ : ℝ) (σ : Vec d) :
    MeasurableSet (corridorSet ℓ σ) :=
  (isOpen_corridorSet ℓ σ).measurableSet

/-! ## M1.1 — genuine measurability of the corridor self-map -/

/-- The corridor self-map `corridorField ℓ σ : CoeffField d → CoeffField d` is
genuinely `Measurable`.  No measurability of `corridorSet` is needed here: the
corridor indicator is a fixed set in the spatial variable `x`, so each ambient
entry `a ↦ corridorField ℓ σ a x i j` is a `by_cases` between the constant
`(1 : Mat d) i j` and the measurable evaluation `a ↦ a x i j`, and the map is
local (it depends on `a` only pointwise). -/
theorem measurable_corridorField (ℓ : ℝ) (σ : Vec d) :
    Measurable (corridorField ℓ σ : CoeffField d → CoeffField d) := by
  classical
  refine measurable_coeffField_to_ambient ?_ (fun U hU => ?_)
  · refine measurable_pi_iff.2 fun x => measurable_pi_iff.2 fun i =>
      measurable_pi_iff.2 fun j => ?_
    by_cases hx : x ∈ corridorSet ℓ σ
    · simp only [corridorField_apply_of_mem hx]
      exact measurable_const
    · simp only [corridorField_apply_of_not_mem hx]
      exact measurable_coeffField_entry (d := d) x i j
  · refine measurable_localSigma_of_local (T := corridorField ℓ σ) ?_ U hU
    intro W hW
    refine ⟨W, hW, ?_⟩
    intro a b hab x hxW
    by_cases hx : x ∈ corridorSet ℓ σ
    · rw [corridorField_apply_of_mem hx, corridorField_apply_of_mem hx]
    · rw [corridorField_apply_of_not_mem hx, corridorField_apply_of_not_mem hx, hab x hxW]

/-! ## M1.2 — ellipticity transport through the corridor -/

/-- The corridor modification preserves a.e. local uniform ellipticity.  On the
corridor set the field is the identity, elliptic with any constants
`lam'' ≤ 1 ≤ Lam''`; off it the field is unchanged.  On each triadic cube, with
original constants `(lam, Lam)`, the modified field is a.e.
`(min lam 1, max Lam 1)`-elliptic; its spatial a.e.-strong measurability is the
piecewise combination of the original coordinate map and a constant, gated by
the measurable `corridorSet`. -/
theorem aeLocallyUniformlyEllipticField_corridorField {ℓ : ℝ} {σ : Vec d}
    {a : CoeffField d} (ha : AELocallyUniformlyEllipticField a) :
    AELocallyUniformlyEllipticField (corridorField ℓ σ a) := by
  classical
  intro Q
  obtain ⟨lam, Lam, hlam, hle, hAOn⟩ := ha Q
  set U : Set (Vec d) := openCubeSet Q with hUdef
  refine ⟨min lam 1, max Lam 1, lt_min hlam one_pos, ?_, ?_, ?_, ?_⟩
  · exact le_trans (min_le_left lam 1) (le_trans hle (le_max_left Lam 1))
  · exact hAOn.measurableSet
  · -- spatial a.e.-strong measurability (piecewise)
    intro i j
    have hEq :
        (fun x => restrictCoeffField U (corridorField ℓ σ a) x i j)
          = (corridorSet ℓ σ).piecewise
              (fun x => restrictCoeffField U (fun _ => (1 : Mat d)) x i j)
              (fun x => restrictCoeffField U a x i j) := by
      funext x
      by_cases hxU : x ∈ U <;> by_cases hxS : x ∈ corridorSet ℓ σ <;>
        simp [Set.piecewise, restrictCoeffField, corridorField, hxU, hxS]
    rw [hEq]
    refine AEStronglyMeasurable.piecewise (measurableSet_corridorSet ℓ σ) ?_ ?_
    · have hb1 :
          (fun x : Vec d => restrictCoeffField U (fun _ => (1 : Mat d)) x i j)
            = U.indicator (fun _ => (1 : Mat d) i j) := by
        funext x; by_cases hxU : x ∈ U <;> simp [restrictCoeffField, hxU]
      rw [hb1]
      exact (measurable_const.indicator hAOn.measurableSet).aestronglyMeasurable.restrict
    · exact (hAOn.aestronglyMeasurable_restrictCoeffField_apply i j).restrict
  · -- pointwise ellipticity a.e.
    have hminpos : (0 : ℝ) < min lam 1 := lt_min hlam one_pos
    filter_upwards [hAOn.ae_isEllipticMatrix] with x hx
    by_cases hxS : x ∈ corridorSet ℓ σ
    · rw [corridorField_apply_of_mem hxS]
      exact (isEllipticMatrix_one (le_max_right Lam 1)).mono hminpos
        (min_le_right lam 1) le_rfl
    · rw [corridorField_apply_of_not_mem hxS]
      exact hx.mono hminpos (min_le_left lam 1) (le_max_left Lam 1)

/-! ## M1.3 — measurability of the local-uniform-ellipticity support -/

/-- The set of locally a.e.-uniformly elliptic coefficient fields is measurable:
it equals the countable `⋂_Q ⋃_k` of the AEE quantitative-slice sets
(`AELocallyUniformlyEllipticField.exists_aeeQuantitativeEllipticSlice_cubeSet`
forward; the definition `AEEQuantitativeEllipticSlice = IsAEEllipticFieldOn (k+1)⁻¹ (k+1)`
plus `IsAEEllipticFieldOn.mono` to the open core backward), each slice set being
ambient-measurable via `AEEQuantitativeEllipticSlice.measurableSet_localSigma`. -/
theorem measurableSet_aeLocallyUniformlyEllipticField :
    MeasurableSet {b : CoeffField d | AELocallyUniformlyEllipticField b} := by
  classical
  have hEq : {b : CoeffField d | AELocallyUniformlyEllipticField b}
      = ⋂ Q : TriadicCube d, ⋃ k : ℕ,
          {b : CoeffField d | AEEQuantitativeEllipticSlice (cubeSet Q) k b} := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro hb Q
      exact hb.exists_aeeQuantitativeEllipticSlice_cubeSet Q
    · intro hb Q
      obtain ⟨k, hk⟩ := hb Q
      have hkpos : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
      have h1le : (1 : ℝ) ≤ (k : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (k : ℝ) := by positivity
        linarith
      have hle : ((k : ℝ) + 1)⁻¹ ≤ (k : ℝ) + 1 :=
        le_trans ((inv_le_one₀ (by positivity)).2 h1le) h1le
      refine ⟨((k : ℝ) + 1)⁻¹, (k : ℝ) + 1, hkpos, hle, ?_⟩
      have hslice : IsAEEllipticFieldOn ((k : ℝ) + 1)⁻¹ ((k : ℝ) + 1) (cubeSet Q) b := hk
      exact hslice.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  rw [hEq]
  refine MeasurableSet.iInter fun Q => MeasurableSet.iUnion fun k => ?_
  exact localSigma_le_coeffField_of_isBounded (isBounded_cubeSet Q) _
    (AEEQuantitativeEllipticSlice.measurableSet_localSigma (cubeSet Q) k)

/-! ## M1.4 — pushforward `LawCarrier` transport -/

/-- The pushforward of a `LawCarrier` law along the corridor map is again a
`LawCarrier` law. -/
theorem lawCarrier_map_corridorField {L : CoeffLaw d} (hP : LawCarrier L)
    (ℓ : ℝ) (σ : Vec d) :
    LawCarrier (L.map (corridorField ℓ σ)) := by
  have hT : Measurable (corridorField ℓ σ) := measurable_corridorField ℓ σ
  haveI : IsProbabilityMeasure L := hP.isProbability
  haveI : IsProbabilityMeasure (L.map (corridorField ℓ σ)) :=
    L.isProbabilityMeasure_map hT.aemeasurable
  refine lawCarrier_of_aeLocallyUniformlyElliptic ?_
  rw [AELocallyUniformlyEllipticLaw,
    ae_map_iff hT.aemeasurable measurableSet_aeLocallyUniformlyEllipticField]
  filter_upwards [hP.ae_locally_uniformly_elliptic] with a ha
  exact aeLocallyUniformlyEllipticField_corridorField ha

/-! ## M1 — the per-phase measurability theorem -/

/-- **M1 (per-phase measurability).**  For a fixed grid phase `σ`, the coarse
observable at the corridor-modified coefficient is a.e.-strongly-measurable under
any `LawCarrier` law. -/
theorem aestronglyMeasurable_phaseObservable [NeZero d] {L : CoeffLaw d}
    (hP : LawCarrier L) (m : ℤ) (ℓ : ℝ) (σ : Vec d) (P : BlockVec d) :
    AEStronglyMeasurable
      (fun a =>
        blockVecDot P
          (blockMatVecMul
            (coarseBlockMatrix (cubeSet (originCube d m)) (corridorField ℓ σ a)) P)) L := by
  have hT : Measurable (corridorField ℓ σ) := measurable_corridorField ℓ σ
  have hPush : LawCarrier (L.map (corridorField ℓ σ)) := lawCarrier_map_corridorField hP ℓ σ
  have hG :
      AEStronglyMeasurable
        (fun b =>
          blockVecDot P
            (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) b) P))
        (L.map (corridorField ℓ σ)) :=
    aestronglyMeasurable_coarseBlockQuadratic_cubeSet hPush m P
  exact hG.comp_measurable hT

end Homogenization
