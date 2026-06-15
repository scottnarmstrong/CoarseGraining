import Homogenization.Sobolev.Foundations.DifferenceQuotient

namespace Homogenization

noncomputable section

/-!
# Summation by parts for weak interior difference quotients

This file keeps the measure-theoretic finite-difference integration by parts
separate from `DifferenceQuotient.lean`, which is already close to the project
file-size cap.  The key point is that the identity below assumes only the
integrability needed to expand the Lebesgue integrals, so it can be used with
an `H¹` representative rather than a smooth compactly supported function.
-/

/-- Whole-space finite-difference summation by parts under explicit
integrability hypotheses.

This is the weak-solution version of
`integral_euclideanForwardDifferenceQuotient_mul_eq_neg_integral_mul_euclideanBackwardDifferenceQuotient`:
the left factor need not be smooth or compactly supported. -/
theorem integral_euclideanForwardDifferenceQuotient_mul_eq_neg_integral_mul_euclideanBackwardDifferenceQuotient_of_integrable
    {d : ℕ} {u v : Vec d → ℝ} (h : ℝ) (i : Fin d)
    (hshiftInt :
      MeasureTheory.Integrable
        (fun x : Vec d => u (euclideanCoordShift h i x) * v x)
        MeasureTheory.volume)
    (huvInt :
      MeasureTheory.Integrable (fun x : Vec d => u x * v x)
        MeasureTheory.volume)
    (hbackShiftInt :
      MeasureTheory.Integrable
        (fun x : Vec d => u x * v (euclideanCoordShift (-h) i x))
        MeasureTheory.volume) :
    ∫ x, euclideanForwardDifferenceQuotient h i u x * v x ∂MeasureTheory.volume =
      -∫ x, u x * euclideanBackwardDifferenceQuotient h i v x
          ∂MeasureTheory.volume := by
  have hchange :=
    integral_comp_euclideanCoordShift_mul_eq_integral_mul_comp_euclideanCoordShift_neg
      h i u v
  have hpointLeft :
      (fun x : Vec d => euclideanForwardDifferenceQuotient h i u x * v x) =
        fun x : Vec d =>
          (u (euclideanCoordShift h i x) * v x - u x * v x) * h⁻¹ := by
    funext x
    simp [euclideanForwardDifferenceQuotient, div_eq_mul_inv]
    ring
  have hpointRight :
      (fun x : Vec d => u x * euclideanBackwardDifferenceQuotient h i v x) =
        fun x : Vec d =>
          (u x * v x - u x * v (euclideanCoordShift (-h) i x)) * h⁻¹ := by
    funext x
    simp [euclideanBackwardDifferenceQuotient, div_eq_mul_inv]
    ring
  calc
    ∫ x, euclideanForwardDifferenceQuotient h i u x * v x ∂MeasureTheory.volume
        = ∫ x, (u (euclideanCoordShift h i x) * v x - u x * v x) * h⁻¹
            ∂MeasureTheory.volume := by
          rw [hpointLeft]
    _ = (∫ x, u (euclideanCoordShift h i x) * v x - u x * v x
            ∂MeasureTheory.volume) * h⁻¹ := by
          rw [MeasureTheory.integral_mul_const]
    _ = ((∫ x, u (euclideanCoordShift h i x) * v x ∂MeasureTheory.volume) -
            (∫ x, u x * v x ∂MeasureTheory.volume)) * h⁻¹ := by
          rw [MeasureTheory.integral_sub hshiftInt huvInt]
    _ = ((∫ x, u x * v (euclideanCoordShift (-h) i x) ∂MeasureTheory.volume) -
            (∫ x, u x * v x ∂MeasureTheory.volume)) * h⁻¹ := by
          rw [hchange]
    _ = -(((∫ x, u x * v x ∂MeasureTheory.volume) -
            (∫ x, u x * v (euclideanCoordShift (-h) i x) ∂MeasureTheory.volume)) * h⁻¹) := by
          ring
    _ = -((∫ x, u x * v x - u x * v (euclideanCoordShift (-h) i x)
            ∂MeasureTheory.volume) * h⁻¹) := by
          rw [MeasureTheory.integral_sub huvInt hbackShiftInt]
    _ = -∫ x, (u x * v x - u x * v (euclideanCoordShift (-h) i x)) * h⁻¹
            ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_mul_const]
    _ = -∫ x, u x * euclideanBackwardDifferenceQuotient h i v x
            ∂MeasureTheory.volume := by
          rw [hpointRight]

end

end Homogenization
