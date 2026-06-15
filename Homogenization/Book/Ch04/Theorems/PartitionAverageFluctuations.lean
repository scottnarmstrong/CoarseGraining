import Homogenization.Book.Ch04.Theorems.DescendantAverages
import Homogenization.Book.Ch04.Theorems.StationaryExpectations

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Public partition-average fluctuation theorems

This file connects the public descendant-average concentration estimates to
the centered origin-cube formulation used in the notes.  The proof uses the
existing stationarity lemmas internally, but the theorem statements are phrased
only in terms of the public Chapter 4 law and local-random-variable notions.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

private theorem isBigO_gammaSigma_iff_of_map_eq_map
    {d : ℕ} {P : CoeffLaw d} {σ A : ℝ}
    {f g : CoeffField d → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hmap : Measure.map f P = Measure.map g P) :
    IsBigO P (gammaSigma σ) f A ↔ IsBigO P (gammaSigma σ) g A := by
  rw [isBigO_gammaSigma_iff, isBigO_gammaSigma_iff]
  constructor
  · intro h t ht
    let s : Set ℝ := {x | A * t < |x|}
    have hs : MeasurableSet s := by
      dsimp [s]
      exact measurableSet_lt measurable_const continuous_abs.measurable
    have hmass := congrArg (fun μ : Measure ℝ => μ s) hmap
    have hmass_real := congrArg ENNReal.toReal hmass
    have hfg :
        P.real (absTailEvent f (A * t)) = P.real (absTailEvent g (A * t)) := by
      simpa [s, absTailEvent, Measure.map_apply hf hs, Measure.map_apply hg hs]
        using hmass_real
    rw [← hfg]
    exact h ht
  · intro h t ht
    let s : Set ℝ := {x | A * t < |x|}
    have hs : MeasurableSet s := by
      dsimp [s]
      exact measurableSet_lt measurable_const continuous_abs.measurable
    have hmass := congrArg (fun μ : Measure ℝ => μ s) hmap
    have hmass_real := congrArg ENNReal.toReal hmass
    have hgf :
        P.real (absTailEvent g (A * t)) = P.real (absTailEvent f (A * t)) := by
      simpa [s, absTailEvent, Measure.map_apply hf hs, Measure.map_apply hg hs]
        using hmass_real.symm
    rw [← hgf]
    exact h ht

private theorem isBigO_psiSigma_iff_of_map_eq_map
    {d : ℕ} {P : CoeffLaw d} {σ A : ℝ}
    {f g : CoeffField d → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hmap : Measure.map f P = Measure.map g P) :
    IsBigO P (psiSigma σ) f A ↔ IsBigO P (psiSigma σ) g A := by
  rw [isBigO_psiSigma_iff, isBigO_psiSigma_iff]
  constructor
  · intro h t ht
    let s : Set ℝ := {x | A * t < |x|}
    have hs : MeasurableSet s := by
      dsimp [s]
      exact measurableSet_lt measurable_const continuous_abs.measurable
    have hmass := congrArg (fun μ : Measure ℝ => μ s) hmap
    have hmass_real := congrArg ENNReal.toReal hmass
    have hfg :
        P.real (absTailEvent f (A * t)) = P.real (absTailEvent g (A * t)) := by
      simpa [s, absTailEvent, Measure.map_apply hf hs, Measure.map_apply hg hs]
        using hmass_real
    rw [← hfg]
    exact h ht
  · intro h t ht
    let s : Set ℝ := {x | A * t < |x|}
    have hs : MeasurableSet s := by
      dsimp [s]
      exact measurableSet_lt measurable_const continuous_abs.measurable
    have hmass := congrArg (fun μ : Measure ℝ => μ s) hmap
    have hmass_real := congrArg ENNReal.toReal hmass
    have hgf :
        P.real (absTailEvent g (A * t)) = P.real (absTailEvent f (A * t)) := by
      simpa [s, absTailEvent, Measure.map_apply hf hs, Measure.map_apply hg hs]
        using hmass_real.symm
    rw [← hgf]
    exact h ht

private theorem centered_descendant_map_eq_origin {d : ℕ} {n m : ℤ}
    {P : CoeffLaw d} [IsProbabilityMeasure P]
    (hn : 0 ≤ n) (hnm : n ≤ m) (hPstat : StationaryLaw P)
    (X : Set (Vec d) → CoeffField d → ℝ)
    (hX0_meas : Measurable (X (cubeSet (originCube d n))))
    (hX_cov : IsTranslationCovariant X)
    (R : TriadicCube d) (hR : R ∈ descendantsAtScale (originCube d m) n) :
    let μ0 : ℝ := ∫ a, X (cubeSet (originCube d n)) a ∂P
    Measure.map (fun a => X (cubeSet R) a - μ0) P =
      Measure.map (fun a => X (cubeSet (originCube d n)) a - μ0) P := by
  intro μ0
  let Y : Set (Vec d) → CoeffField d → ℝ := fun U a => X U a - μ0
  have hY_cov : IsTranslationCovariant Y := by
    intro U z a
    simpa [Y] using congrArg (fun x : ℝ => x - μ0) (hX_cov U z a)
  have hY0_meas : Measurable (Y (cubeSet (originCube d n))) := by
    simpa [Y] using hX0_meas.sub measurable_const
  have hshift :=
    cubeSet_eq_translateSet_originCube_of_mem_descendantsAtScale_originCube
      (d := d) hn hnm hR
  calc
    Measure.map (fun a => X (cubeSet R) a - μ0) P =
        Measure.map (Y (cubeSet R)) P := by
          rfl
    _ = Measure.map
          (Y
            (translateSet (intVecToRealVec (scaleTranslationShift n R))
              (cubeSet (originCube d n)))) P := by
          rw [hshift]
    _ = Measure.map (Y (cubeSet (originCube d n))) P := by
          exact map_eq_map_translateByInt_of_isTranslationCovariant
            (P := P) hPstat (U := cubeSet (originCube d n)) hY0_meas hY_cov
            (scaleTranslationShift n R)
    _ = Measure.map (fun a => X (cubeSet (originCube d n)) a - μ0) P := by
          rfl

/-- Stationarity identifies the expectation of the uncentered descendant
partition average with the expectation on the origin cube at the descendant
scale. -/
theorem integral_descendantAverage_eq_integral_originCube_of_stationary
    {d : ℕ} {n m : ℤ} {P : CoeffLaw d} [IsProbabilityMeasure P]
    (hn : 0 ≤ n) (hnm : n ≤ m)
    (hPstat : StationaryLaw P)
    (X : Set (Vec d) → CoeffField d → ℝ)
    (hX0_meas : Measurable (X (cubeSet (originCube d n))))
    (hX_desc_int :
      ∀ R ∈ descendantsAtScale (originCube d m) n, Integrable (X (cubeSet R)) P)
    (hX_cov : IsTranslationCovariant X) :
    ∫ a, descendantAverage n m X a ∂P =
      ∫ a, X (cubeSet (originCube d n)) a ∂P := by
  let s := descendantsAtScale (originCube d m) n
  let μ0 : ℝ := ∫ a, X (cubeSet (originCube d n)) a ∂P
  have hs_nonempty : s.Nonempty := by
    simpa [s] using descendantsAtScale_nonempty (originCube d m) hnm
  have hs_card_ne_zero : ((s.card : ℝ)) ≠ 0 := by
    exact_mod_cast hs_nonempty.card_ne_zero
  have hterm : ∀ R ∈ s, ∫ a, X (cubeSet R) a ∂P = μ0 := by
    intro R hR
    have hshift :=
      cubeSet_eq_translateSet_originCube_of_mem_descendantsAtScale_originCube
        (d := d) hn hnm (by simpa [s] using hR)
    calc
      ∫ a, X (cubeSet R) a ∂P
          = ∫ a,
              X
                (translateSet (intVecToRealVec (scaleTranslationShift n R))
                  (cubeSet (originCube d n))) a ∂P := by
              rw [hshift]
      _ = ∫ a, X (cubeSet (originCube d n)) a ∂P := by
            exact integral_eq_of_isTranslationCovariant_of_isStationary
              (P := P) hPstat (U := cubeSet (originCube d n)) hX0_meas hX_cov
              (scaleTranslationShift n R)
      _ = μ0 := by
            rfl
  calc
    ∫ a, descendantAverage n m X a ∂P
        = ∫ a, ((s.card : ℝ)⁻¹ * ∑ R ∈ s, X (cubeSet R) a) ∂P := by
            simp [descendantAverage, s]
    _ = (s.card : ℝ)⁻¹ * ∫ a, ∑ R ∈ s, X (cubeSet R) a ∂P := by
            rw [integral_const_mul]
    _ = (s.card : ℝ)⁻¹ * ∑ R ∈ s, ∫ a, X (cubeSet R) a ∂P := by
          rw [integral_finset_sum s]
          intro R hR
          exact hX_desc_int R (by simpa [s] using hR)
    _ = (s.card : ℝ)⁻¹ * ∑ _R ∈ s, μ0 := by
          refine congrArg (fun t : ℝ => ((s.card : ℝ)⁻¹) * t) ?_
          refine Finset.sum_congr rfl ?_
          intro R hR
          exact hterm R hR
    _ = μ0 := by
          rw [Finset.sum_const]
          simp [nsmul_eq_mul, hs_card_ne_zero]
    _ = ∫ a, X (cubeSet (originCube d n)) a ∂P := by
          rfl

/-- The centered descendant partition average has mean zero under stationarity. -/
theorem integral_centeredDescendantAverage_eq_zero_of_stationary
    {d : ℕ} {n m : ℤ} {P : CoeffLaw d} [IsProbabilityMeasure P]
    (hn : 0 ≤ n) (hnm : n ≤ m)
    (hPstat : StationaryLaw P)
    (X : Set (Vec d) → CoeffField d → ℝ)
    (hX0_meas : Measurable (X (cubeSet (originCube d n))))
    (hX_desc_int :
      ∀ R ∈ descendantsAtScale (originCube d m) n, Integrable (X (cubeSet R)) P)
    (hX_cov : IsTranslationCovariant X) :
    ∫ a, centeredDescendantAverage P n m X a ∂P = 0 := by
  let s := descendantsAtScale (originCube d m) n
  let μ0 : ℝ := ∫ a, X (cubeSet (originCube d n)) a ∂P
  have hs_nonempty : s.Nonempty := by
    simpa [s] using descendantsAtScale_nonempty (originCube d m) hnm
  have hs_card_ne_zero : ((s.card : ℝ)) ≠ 0 := by
    exact_mod_cast hs_nonempty.card_ne_zero
  have havg :=
    integral_descendantAverage_eq_integral_originCube_of_stationary
      (P := P) hn hnm hPstat X hX0_meas hX_desc_int hX_cov
  have hsum_int :
      Integrable (fun a => ∑ R ∈ s, X (cubeSet R) a) P := by
    refine integrable_finset_sum _ ?_
    intro R hR
    exact hX_desc_int R (by simpa [s] using hR)
  have hdesc_int : Integrable (descendantAverage n m X) P := by
    have hdesc_eq :
        descendantAverage n m X =
          fun a => ((s.card : ℝ)⁻¹ * ∑ R ∈ s, X (cubeSet R) a) := by
      funext a
      simp [descendantAverage, s]
    rw [hdesc_eq]
    exact hsum_int.const_mul ((s.card : ℝ)⁻¹)
  have hcenter_eq :
      centeredDescendantAverage P n m X =
        fun a => descendantAverage n m X a - μ0 := by
    funext a
    rw [centeredDescendantAverage, descendantAverage]
    change
      ((s.card : ℝ)⁻¹ * ∑ R ∈ s, (X (cubeSet R) a - μ0)) =
        ((s.card : ℝ)⁻¹ * ∑ R ∈ s, X (cubeSet R) a) - μ0
    rw [Finset.sum_sub_distrib, Finset.sum_const]
    simp [nsmul_eq_mul, μ0]
    field_simp [hs_card_ne_zero]
  calc
    ∫ a, centeredDescendantAverage P n m X a ∂P
        = ∫ a, descendantAverage n m X a - μ0 ∂P := by
            rw [hcenter_eq]
    _ = ∫ a, descendantAverage n m X a ∂P - ∫ _a, μ0 ∂P := by
          exact integral_sub hdesc_int (integrable_const μ0)
    _ = μ0 - μ0 := by
          rw [havg]
          simp [μ0]
    _ = 0 := by
          ring

/-- Centered `Gamma_sigma` fluctuation bound for public centered descendant
averages of a translation-covariant cube observable. -/
theorem isBigO_gammaSigma_centeredDescendantAverage_of_unitRangeDependentLaw
    {d : ℕ} {n m : ℤ} {P : CoeffLaw d} [IsProbabilityMeasure P]
    {σ K : ℝ}
    (hn : 0 ≤ n) (hnm : n ≤ m)
    (hPstat : StationaryLaw P) (hPdep : UnitRangeDependentLaw P)
    (X : Set (Vec d) → CoeffField d → ℝ)
    (hX_local :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        IsLocalRandomVariable (cubeSet R) (X (cubeSet R)))
    (hX_cov : IsTranslationCovariant X)
    (hX0_meas : Measurable (X (cubeSet (originCube d n))))
    (hX_desc_meas :
      ∀ R ∈ descendantsAtScale (originCube d m) n, Measurable (X (cubeSet R)))
    (hσ₀ : 0 < σ) (hσ₂ : σ ≤ 2) (hK : 0 < K)
    (hX0 : IsBigO P (gammaSigma σ) (centeredOriginObservable P n X) K) :
    IsBigO P (gammaSigma σ) (centeredDescendantAverage P n m X)
      (gammaSigmaDescendantsAtScaleConst d n σ *
        partitionCardinalityScale (d := d) n m * K) := by
  let μ0 : ℝ := ∫ a, X (cubeSet (originCube d n)) a ∂P
  let Z : TriadicCube d → CoeffField d → ℝ := fun R a => X (cubeSet R) a - μ0
  have hZ_local :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        IsLocalRandomVariable (cubeSet R) (Z R) := by
    intro R hR
    simpa [Z] using (hX_local R hR).sub measurable_const
  have hZ_meas :
      ∀ R ∈ descendantsAtScale (originCube d m) n, Measurable (Z R) := by
    intro R hR
    simpa [Z] using (hX_desc_meas R hR).sub measurable_const
  have hZ_tail :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        IsBigO P (gammaSigma σ) (Z R) K := by
    intro R hR
    have hmap :=
      centered_descendant_map_eq_origin
        (P := P) hn hnm hPstat X hX0_meas hX_cov R hR
    have hZR_meas : Measurable (Z R) := hZ_meas R hR
    have hZ0_meas :
        Measurable (fun a => X (cubeSet (originCube d n)) a - μ0) :=
      hX0_meas.sub measurable_const
    have horigin :
        IsBigO P (gammaSigma σ) (fun a => X (cubeSet (originCube d n)) a - μ0) K := by
      simpa [centeredOriginObservable, μ0] using hX0
    have htail :=
      (isBigO_gammaSigma_iff_of_map_eq_map
        (P := P) (σ := σ) (A := K) hZR_meas hZ0_meas (by simpa [Z] using hmap)).2
        horigin
    simpa [Z] using htail
  have hZ0_int : Integrable (Z (originCube d n)) P := by
    have hZ0_meas : Measurable (Z (originCube d n)) := by
      simpa [Z] using hX0_meas.sub measurable_const
    have hZ0_mom :=
      hasGammaMomentGrowthWith_of_isBigO_gammaSigma
        (μ := P) (X := Z (originCube d n)) (K := K) (σ := σ)
        hσ₀ hK hZ0_meas.aemeasurable (by
          simpa [Z, centeredOriginObservable, μ0] using hX0)
    have hZ0_abs_int : Integrable (fun a => |Z (originCube d n) a|) P := by
      simpa using
        (IndependentSums.gammaMomentGrowth_natCast_bound
          (μ := P) (X := Z (originCube d n)) (σ := σ)
          (M := gammaMomentConst σ * K) (n := 1) (by norm_num) hZ0_mom).1
    have hZ0_norm_int : Integrable (fun a => ‖Z (originCube d n) a‖) P := by
      simpa [Real.norm_eq_abs] using hZ0_abs_int
    exact
      (integrable_norm_iff hZ0_meas.aemeasurable.aestronglyMeasurable).1 hZ0_norm_int
  have hX0_int : Integrable (X (cubeSet (originCube d n))) P := by
    have hX0_eq :
        (fun a => X (cubeSet (originCube d n)) a) =
          fun a => Z (originCube d n) a + μ0 := by
      funext a
      simp [Z, μ0]
    simpa [hX0_eq] using hZ0_int.add (integrable_const μ0)
  have hZ0_mean : ∫ a, Z (originCube d n) a ∂P = 0 := by
    calc
      ∫ a, Z (originCube d n) a ∂P =
          ∫ a, X (cubeSet (originCube d n)) a ∂P - ∫ _a, μ0 ∂P := by
            simpa [Z] using integral_sub hX0_int (integrable_const μ0)
      _ = μ0 - μ0 := by
            simp [μ0]
      _ = 0 := by
            ring
  have hZ_mean :
      ∀ R ∈ descendantsAtScale (originCube d m) n, ∫ a, Z R a ∂P = 0 := by
    intro R hR
    have hshift :=
      cubeSet_eq_translateSet_originCube_of_mem_descendantsAtScale_originCube
        (d := d) hn hnm hR
    have hZ_cov : IsTranslationCovariant (fun U a => X U a - μ0) := by
      intro U z a
      simpa using congrArg (fun x : ℝ => x - μ0) (hX_cov U z a)
    have hZ0_meas' : Measurable ((fun U a => X U a - μ0) (cubeSet (originCube d n))) := by
      simpa using hX0_meas.sub measurable_const
    have hint :
        ∫ a, Z R a ∂P = ∫ a, Z (originCube d n) a ∂P := by
      calc
        ∫ a, Z R a ∂P =
            ∫ a,
              (fun U a => X U a - μ0)
                (translateSet (intVecToRealVec (scaleTranslationShift n R))
                  (cubeSet (originCube d n))) a ∂P := by
              change
                ∫ a, (fun U a => X U a - μ0) (cubeSet R) a ∂P =
                  ∫ a,
                    (fun U a => X U a - μ0)
                      (translateSet (intVecToRealVec (scaleTranslationShift n R))
                        (cubeSet (originCube d n))) a ∂P
              rw [hshift]
        _ = ∫ a, (fun U a => X U a - μ0) (cubeSet (originCube d n)) a ∂P := by
              exact integral_eq_of_isTranslationCovariant_of_isStationary
                (P := P) hPstat (U := cubeSet (originCube d n)) hZ0_meas' hZ_cov
                (scaleTranslationShift n R)
        _ = ∫ a, Z (originCube d n) a ∂P := by
              rfl
    exact hint.trans hZ0_mean
  have havg :=
    isBigO_gammaSigma_descendantAverage_of_unitRangeDependentLaw
      (Q := originCube d m) (k := n) (P := P)
      hnm hPdep hσ₀ hσ₂ hK Z hZ_local hZ_meas hZ_tail hZ_mean
  have havg_fun_eq :
      (fun a => ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtScale (originCube d m) n, Z R a) =
        centeredDescendantAverage P n m X := by
    funext a
    simp [centeredDescendantAverage, Z, μ0]
  simpa [havg_fun_eq, partitionCardinalityScale,
    div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using havg

/-- Centered `Psi_sigma` fluctuation bound for public centered descendant
averages of a translation-covariant cube observable. -/
theorem isBigO_psiSigma_centeredDescendantAverage_of_unitRangeDependentLaw
    {d : ℕ} {n m : ℤ} {P : CoeffLaw d} [IsProbabilityMeasure P]
    {σ K : ℝ}
    (hn : 0 ≤ n) (hnm : n ≤ m)
    (hPstat : StationaryLaw P) (hPdep : UnitRangeDependentLaw P)
    (X : Set (Vec d) → CoeffField d → ℝ)
    (hX_local :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        IsLocalRandomVariable (cubeSet R) (X (cubeSet R)))
    (hX_cov : IsTranslationCovariant X)
    (hX0_meas : Measurable (X (cubeSet (originCube d n))))
    (hX0_int : Integrable (X (cubeSet (originCube d n))) P)
    (hX_desc_meas :
      ∀ R ∈ descendantsAtScale (originCube d m) n, Measurable (X (cubeSet R)))
    (hX_desc_int :
      ∀ R ∈ descendantsAtScale (originCube d m) n, Integrable (X (cubeSet R)) P)
    (hσ : 1 ≤ σ) (hK : 0 < K)
    (hX0 : IsBigO P (psiSigma σ) (centeredOriginObservable P n X) K) :
    IsBigO P (psiSigma σ) (centeredDescendantAverage P n m X)
      (psiSigmaDescendantsAtScaleConst d n σ *
        partitionCardinalityScale (d := d) n m * K) := by
  let μ0 : ℝ := ∫ a, X (cubeSet (originCube d n)) a ∂P
  let Z : TriadicCube d → CoeffField d → ℝ := fun R a => X (cubeSet R) a - μ0
  have hZ_local :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        IsLocalRandomVariable (cubeSet R) (Z R) := by
    intro R hR
    simpa [Z] using (hX_local R hR).sub measurable_const
  have hZ_meas :
      ∀ R ∈ descendantsAtScale (originCube d m) n, Measurable (Z R) := by
    intro R hR
    simpa [Z] using (hX_desc_meas R hR).sub measurable_const
  have hZ_int :
      ∀ R ∈ descendantsAtScale (originCube d m) n, Integrable (Z R) P := by
    intro R hR
    simpa [Z] using (hX_desc_int R hR).sub (integrable_const μ0)
  have hZ_tail :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        IsBigO P (psiSigma σ) (Z R) K := by
    intro R hR
    have hmap :=
      centered_descendant_map_eq_origin
        (P := P) hn hnm hPstat X hX0_meas hX_cov R hR
    have hZR_meas : Measurable (Z R) := hZ_meas R hR
    have hZ0_meas :
        Measurable (fun a => X (cubeSet (originCube d n)) a - μ0) :=
      hX0_meas.sub measurable_const
    have horigin :
        IsBigO P (psiSigma σ) (fun a => X (cubeSet (originCube d n)) a - μ0) K := by
      simpa [centeredOriginObservable, μ0] using hX0
    have htail :=
      (isBigO_psiSigma_iff_of_map_eq_map
        (P := P) (σ := σ) (A := K) hZR_meas hZ0_meas (by simpa [Z] using hmap)).2
        horigin
    simpa [Z] using htail
  have hZ0_mean : ∫ a, Z (originCube d n) a ∂P = 0 := by
    calc
      ∫ a, Z (originCube d n) a ∂P =
          ∫ a, X (cubeSet (originCube d n)) a ∂P - ∫ _a, μ0 ∂P := by
            simpa [Z] using integral_sub hX0_int (integrable_const μ0)
      _ = μ0 - μ0 := by
            simp [μ0]
      _ = 0 := by
            ring
  have hZ_mean :
      ∀ R ∈ descendantsAtScale (originCube d m) n, ∫ a, Z R a ∂P = 0 := by
    intro R hR
    have hshift :=
      cubeSet_eq_translateSet_originCube_of_mem_descendantsAtScale_originCube
        (d := d) hn hnm hR
    have hZ_cov : IsTranslationCovariant (fun U a => X U a - μ0) := by
      intro U z a
      simpa using congrArg (fun x : ℝ => x - μ0) (hX_cov U z a)
    have hZ0_meas' : Measurable ((fun U a => X U a - μ0) (cubeSet (originCube d n))) := by
      simpa using hX0_meas.sub measurable_const
    have hint :
        ∫ a, Z R a ∂P = ∫ a, Z (originCube d n) a ∂P := by
      calc
        ∫ a, Z R a ∂P =
            ∫ a,
              (fun U a => X U a - μ0)
                (translateSet (intVecToRealVec (scaleTranslationShift n R))
                  (cubeSet (originCube d n))) a ∂P := by
              change
                ∫ a, (fun U a => X U a - μ0) (cubeSet R) a ∂P =
                  ∫ a,
                    (fun U a => X U a - μ0)
                      (translateSet (intVecToRealVec (scaleTranslationShift n R))
                        (cubeSet (originCube d n))) a ∂P
              rw [hshift]
        _ = ∫ a, (fun U a => X U a - μ0) (cubeSet (originCube d n)) a ∂P := by
              exact integral_eq_of_isTranslationCovariant_of_isStationary
                (P := P) hPstat (U := cubeSet (originCube d n)) hZ0_meas' hZ_cov
                (scaleTranslationShift n R)
        _ = ∫ a, Z (originCube d n) a ∂P := by
              rfl
    exact hint.trans hZ0_mean
  have havg :=
    isBigO_psiSigma_descendantAverage_of_unitRangeDependentLaw
      (Q := originCube d m) (k := n) (P := P)
      hnm hPdep hσ hK Z hZ_local hZ_meas hZ_int hZ_tail hZ_mean
  have havg_fun_eq :
      (fun a => ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtScale (originCube d m) n, Z R a) =
        centeredDescendantAverage P n m X := by
    funext a
    simp [centeredDescendantAverage, Z, μ0]
  simpa [havg_fun_eq, partitionCardinalityScale,
    div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using havg

end

end Ch04
end Book
end Homogenization
