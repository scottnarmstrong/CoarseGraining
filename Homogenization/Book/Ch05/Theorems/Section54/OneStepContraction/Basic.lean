import Homogenization.Book.Ch05.Theorems.Section54.GoodScale
import Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace OneStepContraction

noncomputable section

/-!
# Basic definitions for the one-step contraction

This file contains only the scalar abbreviations used by the Section 5.4
one-step contraction proof.  The theorem-facing statement remains in the final
assembly file.
-/

/-- The internal manuscript choice `epsilon = delta^(1/4)`. -/
noncomputable def oneStepContractionEpsilon (delta : ℝ) : ℝ :=
  Real.rpow delta (1 / 4 : ℝ)

/-- The scalar coefficient combination multiplying the additivity-defect sum
in the Section 5.3 coarse-fluctuation estimate. -/
noncomputable def oneStepScalarWeightAtScale
    {d : ℕ} [NeZero d] {P : Ch04.CoeffLaw d}
    (hP : Ch04.LawCarrier P) (hStruct : Ch04.StructuralLaw P) (m : ℕ) : ℝ :=
  sigmaHatAtScale hP hStruct (m : ℤ) *
      (hP.barSigmaStarAtScale hStruct 0)⁻¹ +
    (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ *
      hP.barSigmaAtScale hStruct 0

/-- The one-step scalar weight is the sum of the two good-scale scalar
comparisons used in the manuscript proof. -/
theorem oneStepScalarWeightAtScale_eq
    {d : ℕ} [NeZero d] {P : Ch04.CoeffLaw d}
    (hP : Ch04.LawCarrier P) (hStruct : Ch04.StructuralLaw P) (m : ℕ) :
    oneStepScalarWeightAtScale hP hStruct m =
      sigmaHatAtScale hP hStruct (m : ℤ) *
          (hP.barSigmaStarAtScale hStruct 0)⁻¹ +
        (sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ *
          hP.barSigmaAtScale hStruct 0 := by
  rfl

end

end OneStepContraction
end Section54
end Ch05
end Book
end Homogenization

