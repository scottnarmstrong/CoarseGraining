import Homogenization.Probability.RegCoeffField.Endomorphisms

/-!
# The restriction σ-algebra on the carrier

The restriction σ-algebra `RestrictionSigmaR U hU` is the σ-algebra of carrier
events determined by the values of the field on the measurable set `U`: the comap
of the canonical carrier σ-algebra along the restriction endomorphism
`restrictReg U hU`.  It is the measurable local σ-algebra used for the unit-range
dependence of carrier laws (see `Laws.lean`).

`RestrictionSigmaR` is coarser than the canonical carrier σ-algebra, and monotone
under set inclusion (with the `MeasurableSet` discipline that both restriction
maps be well defined, matching the D7-approved coarsening interface).  The
separation predicate `AreUnitSeparated` is the raw-set predicate of
`Homogenization.Probability.RandomField`, reused unchanged.

Reference: the paper (Armstrong–Kuusi–Loher, in prep).
-/

namespace Homogenization

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The restriction σ-algebra on the carrier: the comap of the canonical carrier
σ-algebra along the restriction endomorphism `restrictReg U hU`. -/
def RestrictionSigmaR (U : Set (Vec d)) (hU : MeasurableSet U) :
    MeasurableSpace (RegCoeffField d) :=
  MeasurableSpace.comap (restrictReg U hU) inferInstance

/-- The restriction endomorphism is measurable from the restriction σ-algebra. -/
theorem measurable_restrictReg_restrictionSigmaR (U : Set (Vec d)) (hU : MeasurableSet U) :
    @Measurable _ _ (RestrictionSigmaR U hU) _ (restrictReg U hU) :=
  measurable_iff_comap_le.mpr le_rfl

/-- The restriction σ-algebra is coarser than the canonical carrier σ-algebra. -/
theorem restrictionSigmaR_le (U : Set (Vec d)) (hU : MeasurableSet U) :
    RestrictionSigmaR U hU ≤ instMeasurableSpaceRegCoeffField d :=
  measurable_iff_comap_le.mp (measurable_restrictReg U hU)

/-- Composition identity for nested restrictions: restricting to `V` and then to
`U ⊆ V` is the same as restricting to `U`. -/
theorem restrictReg_comp_restrictReg_of_subset {U V : Set (Vec d)}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hUV : U ⊆ V) :
    restrictReg U hU ∘ restrictReg V hV = restrictReg U hU := by
  funext a
  apply RegCoeffField.ext
  intro x
  by_cases hx : x ∈ U
  · have hxV : x ∈ V := hUV hx
    simp only [Function.comp_apply, restrictReg_apply,
      Set.indicator_of_mem hx, Set.indicator_of_mem hxV]
  · simp only [Function.comp_apply, restrictReg_apply,
      Set.indicator_of_notMem hx]

/-- The `U`-restriction endomorphism is measurable from the coarser `V`-restriction
σ-algebra when `U ⊆ V`. -/
theorem measurable_restrictReg_restrictionSigmaR_of_subset {U V : Set (Vec d)}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hUV : U ⊆ V) :
    @Measurable _ _ (RestrictionSigmaR V hV) _ (restrictReg U hU) := by
  simpa [restrictReg_comp_restrictReg_of_subset hU hV hUV, Function.comp] using
    (measurable_restrictReg U hU).comp (measurable_restrictReg_restrictionSigmaR V hV)

/-- **Monotonicity of the restriction σ-algebra under set inclusion.** -/
theorem RestrictionSigmaR_mono {U V : Set (Vec d)} (hU : MeasurableSet U)
    (hV : MeasurableSet V) (hUV : U ⊆ V) :
    RestrictionSigmaR U hU ≤ RestrictionSigmaR V hV := by
  simpa [RestrictionSigmaR] using
    measurable_iff_comap_le.mp
      (measurable_restrictReg_restrictionSigmaR_of_subset hU hV hUV)

end

end Homogenization
