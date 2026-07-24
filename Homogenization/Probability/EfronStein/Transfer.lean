import Homogenization.Probability.EfronStein.Fin
import Homogenization.Probability.LocalObservable
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Efron–Stein transfer to coefficient-field laws

This file transfers the abstract product-space Efron–Stein inequality
(`Homogenization.efronStein_pi`) to a *single* unit-range-dependent probability
measure `P` on the ambient coefficient field `CoeffField d`, resampled through a
family of restriction maps.

Fix a `Fintype ι` and a family of pairwise `AreUnitSeparated` regions
`C : ι → Set (Vec d)`.  Writing `R a i := restrictCoeffField (C i) a` for the
joint restriction map, the family `(fun a => restrictCoeffField (C i) a)_i` is
independent under a unit-range-dependent `P`, so the pushforward `P.map R`
factors as the product measure `Measure.pi (fun i => P.map (restrictCoeffField
(C i)))`.  Efron–Stein on that product, transported back through the map
identity, yields the variance bound for a bounded measurable observable `G` of
the restricted fields.

The single resampling coordinate is `restrictCoeffField (C i) a'`: an
independent copy of `P` re-drawn only on `C i`.
-/

open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Homogenization

variable {d : ℕ}

/-- The restriction map `restrictCoeffField U`, bundled as a measurable local
observable on `U` valued in `CoeffField d` (the identity observable on the
`U`-restricted field).  This is the family fed to the independence bridge in
the Efron–Stein transfer. -/
noncomputable def restrictObservable (U : Set (Vec d)) :
    MeasurableLocalObservable d U (CoeffField d) where
  toFun := restrictCoeffField U
  measurable_toFun := measurable_restrictCoeffField U
  isLocal_toFun := by
    intro a b hab
    funext x
    by_cases hx : x ∈ U
    · simp [restrictCoeffField_apply_of_mem hx, hab x hx]
    · simp [restrictCoeffField_apply_of_not_mem hx]

@[simp] theorem restrictObservable_apply (U : Set (Vec d)) (a : CoeffField d) :
    restrictObservable U a = restrictCoeffField U a := rfl

/-- **Efron–Stein transfer.**  For a finite family of pairwise `AreUnitSeparated`
regions `C i`, a unit-range-dependent probability measure `P` on `CoeffField d`,
and a bounded measurable observable `G` of the jointly restricted fields
`R a = fun i => restrictCoeffField (C i) a`, the variance of `G ∘ R` is
controlled by the sum of single-region resampling energies, each an independent
copy of `P` re-drawn only on `C i`. -/
theorem efronStein_transfer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : ι → Set (Vec d)}
    (hsep : Pairwise fun i j => AreUnitSeparated (C i) (C j))
    {P : MeasureTheory.Measure (CoeffField d)} [MeasureTheory.IsProbabilityMeasure P]
    (hP : IsUnitRangeDependent P)
    {G : (ι → CoeffField d) → ℝ} (hG : Measurable G) {M : ℝ} (hMG : ∀ x, |G x| ≤ M)
    (R : CoeffField d → (ι → CoeffField d))
    (hRdef : R = fun a i => restrictCoeffField (C i) a) :
    Var[G ∘ R; P]
      ≤ (1 / 2) * ∑ i, ∫ a, ∫ a',
          (G (Function.update (R a) i (restrictCoeffField (C i) a')) - G (R a)) ^ 2 ∂P ∂P := by
  classical
  -- Restriction observables and the resampled per-region laws.
  set X : ∀ i, MeasurableLocalObservable d (C i) (CoeffField d) :=
    fun i => restrictObservable (C i) with hX
  set μ : ι → MeasureTheory.Measure (CoeffField d) :=
    fun i => MeasureTheory.Measure.map (restrictCoeffField (C i)) P with hμ
  haveI hμprob : ∀ i, MeasureTheory.IsProbabilityMeasure (μ i) := fun i =>
    MeasureTheory.Measure.isProbabilityMeasure_map
      (measurable_restrictCoeffField (C i)).aemeasurable
  -- Measurability of the joint restriction map.
  have hRmeas : Measurable R := by
    rw [hRdef]; exact measurable_pi_iff.2 (fun i => measurable_restrictCoeffField (C i))
  -- Independence (independence bridge) and the product-measure factorisation `P.map R = pi μ`.
  have hf : ∀ i, AEMeasurable (fun a => X i a) P :=
    fun i => (X i).measurable.aemeasurable
  have hindep :
      ProbabilityTheory.iIndepFun (fun i => (X i : CoeffField d → CoeffField d)) P :=
    MeasurableLocalObservable.iIndepFun_of_isRestrictionUnitRangeDependent hP hsep X
  have hmap : MeasureTheory.Measure.map R P = MeasureTheory.Measure.pi μ := by
    have h := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map hf).1 hindep
    rw [hRdef]; exact h
  -- Left-hand side: `Var[G ∘ R; P] = Var[G; pi μ]`.
  have hLHS : Var[G ∘ R; P] = Var[G; MeasureTheory.Measure.pi μ] := by
    rw [← ProbabilityTheory.variance_map (X := G) hG.aemeasurable hRmeas.aemeasurable, hmap]
  -- Right-hand side: each resampling term pulled back to a double `P`-integral.
  have hRHS : ∀ i,
      (∫ x, ∫ y, (G (Function.update x i y) - G x) ^ 2 ∂(μ i) ∂(MeasureTheory.Measure.pi μ))
        = ∫ a, ∫ a',
            (G (Function.update (R a) i (restrictCoeffField (C i) a')) - G (R a)) ^ 2 ∂P ∂P := by
    intro i
    -- Inner integral: resample the `i`-th coordinate from `P` through `restrict (C i)`.
    have hinner : ∀ x : ι → CoeffField d,
        (∫ y, (G (Function.update x i y) - G x) ^ 2 ∂(μ i))
          = ∫ a', (G (Function.update x i (restrictCoeffField (C i) a')) - G x) ^ 2 ∂P := by
      intro x
      have hg : Measurable
          (fun y : CoeffField d => (G (Function.update x i y) - G x) ^ 2) :=
        ((hG.comp (measurable_update x)).sub measurable_const).pow measurable_const
      simp only [hμ]
      rw [MeasureTheory.integral_map (measurable_restrictCoeffField (C i)).aemeasurable
        hg.aestronglyMeasurable]
    simp_rw [hinner]
    -- Outer integral: pull the free field `x` back to `R a` under `P`.
    have hjoint : Measurable
        (fun p : (ι → CoeffField d) × CoeffField d =>
          (G (Function.update p.1 i (restrictCoeffField (C i) p.2)) - G p.1) ^ 2) := by
      have hupd : Measurable
          (fun p : (ι → CoeffField d) × CoeffField d =>
            Function.update p.1 i (restrictCoeffField (C i) p.2)) :=
        (measurable_update' (a := i)).comp
          (measurable_fst.prodMk
            ((measurable_restrictCoeffField (C i)).comp measurable_snd))
      exact ((hG.comp hupd).sub (hG.comp measurable_fst)).pow measurable_const
    have houter : MeasureTheory.StronglyMeasurable
        (fun x : ι → CoeffField d =>
          ∫ a', (G (Function.update x i (restrictCoeffField (C i) a')) - G x) ^ 2 ∂P) :=
      hjoint.stronglyMeasurable.integral_prod_right'
    rw [← hmap, MeasureTheory.integral_map hRmeas.aemeasurable houter.aestronglyMeasurable]
  -- Assemble.
  rw [hLHS]
  refine le_trans (Homogenization.efronStein_pi μ hG (M := M) hMG) ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact le_of_eq (Finset.sum_congr rfl (fun i _ => hRHS i))

end Homogenization
