import Homogenization.Sobolev.Foundations.MeanZero

namespace Homogenization

/-!
# Integral identities for convex-domain Poincare

This file collects the first measure-theoretic identities behind the future
convex-domain mean-zero Poincare proof. At this stage we only need the basic
algebra that rewrites `u x - average_U u` as the normalized average of the
differences `u x - u y`.
-/

theorem sub_integralAverage_eq_volumeAverage_sub
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {u : Vec d → ℝ} (hu : MeasureTheory.IntegrableOn u U) (x : Vec d)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    u x - integralAverage U u =
      (MeasureTheory.volume U).toReal⁻¹ *
        ∫ y in U, (u x - u y) ∂MeasureTheory.volume := by
  have hμ_ne : (MeasureTheory.volume U).toReal ≠ 0 := by
    linarith
  have hconstInt : MeasureTheory.IntegrableOn (fun _ : Vec d => u x) U := by
    simp [MeasureTheory.IntegrableOn]
  have hconst :
      ∫ y in U, (u x : ℝ) ∂MeasureTheory.volume =
        (MeasureTheory.volume U).toReal * u x := by
    rw [MeasureTheory.integral_const, smul_eq_mul]
    have hμ₁ :
        (MeasureTheory.volume.restrict U).real Set.univ = MeasureTheory.volume.real U := by
      exact MeasureTheory.measureReal_restrict_apply_univ (μ := MeasureTheory.volume) U
    have hμ₂ : MeasureTheory.volume.real U = (MeasureTheory.volume U).toReal := rfl
    rw [hμ₁, hμ₂]
  let I : ℝ := ∫ y in U, u y ∂MeasureTheory.volume
  have hscale :
      u x - (MeasureTheory.volume U).toReal⁻¹ * I =
        (MeasureTheory.volume U).toReal⁻¹ *
          ((MeasureTheory.volume U).toReal * u x - I) := by
    field_simp [hμ_ne]
  calc
    u x - integralAverage U u
        = u x - (MeasureTheory.volume U).toReal⁻¹ * I := by
              simp [I, integralAverage]
    _ = (MeasureTheory.volume U).toReal⁻¹ *
          ((MeasureTheory.volume U).toReal * u x -
            I) := hscale
    _ = (MeasureTheory.volume U).toReal⁻¹ *
          ((∫ y in U, u x ∂MeasureTheory.volume) - I) := by
            rw [← hconst]
    _ = (MeasureTheory.volume U).toReal⁻¹ *
          ∫ y in U, (u x - u y) ∂MeasureTheory.volume := by
            change (MeasureTheory.volume U).toReal⁻¹ *
                ((∫ y in U, u x ∂MeasureTheory.volume) -
                  ∫ y in U, u y ∂MeasureTheory.volume) =
              (MeasureTheory.volume U).toReal⁻¹ *
                ∫ y in U, (u x - u y) ∂MeasureTheory.volume
            rw [MeasureTheory.integral_sub hconstInt.integrable hu.integrable]

theorem norm_sub_integralAverage_le_volumeAverage_integral_norm_sub
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {u : Vec d → ℝ} (hu : MeasureTheory.IntegrableOn u U) (x : Vec d)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    ‖u x - integralAverage U u‖ ≤
      (MeasureTheory.volume U).toReal⁻¹ *
        ∫ y in U, ‖u x - u y‖ ∂MeasureTheory.volume := by
  have hμinv_nonneg : 0 ≤ (MeasureTheory.volume U).toReal⁻¹ := by
    positivity
  calc
    ‖u x - integralAverage U u‖
        = ‖(MeasureTheory.volume U).toReal⁻¹ *
            ∫ y in U, (u x - u y) ∂MeasureTheory.volume‖ := by
              rw [sub_integralAverage_eq_volumeAverage_sub hu x hvol]
    _ = (MeasureTheory.volume U).toReal⁻¹ *
          ‖∫ y in U, (u x - u y) ∂MeasureTheory.volume‖ := by
            rw [norm_mul, Real.norm_of_nonneg hμinv_nonneg]
    _ ≤ (MeasureTheory.volume U).toReal⁻¹ *
          ∫ y in U, ‖u x - u y‖ ∂MeasureTheory.volume := by
            gcongr
            exact MeasureTheory.norm_integral_le_integral_norm (fun y => u x - u y)

end Homogenization
