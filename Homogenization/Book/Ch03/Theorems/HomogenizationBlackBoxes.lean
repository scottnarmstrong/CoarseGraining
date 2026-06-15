import Homogenization.Book.Ch03.Theorems.Duality
import Homogenization.Book.Ch03.Theorems.GeneralCoarseGrainingL2TwoExponent

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Section 3.3: Deterministic homogenization black boxes

This file bundles the public contract packages for all currently written
theorems in Chapter 3.3.
-/

/-- Public aggregate package for the proved two-exponent replacement route.

This is the downstream-facing Ch3.3 surface when the comparison left-hand side
is measured at exponent `s`, but the flux-defect/Besov input is consumed at an
independent exponent `t < s / 2` with the explicit note-facing singular factor
in the public RHS. -/
structure HomogenizationBlackBoxesTheory (d : ℕ) [NeZero d] : Prop where
  fluxDefectDuality : FluxDefectDualityTheory d
  generalCoarseGrainingL2TwoExponent : GeneralCoarseGrainingL2TwoExponentTheory d

private theorem homogenizationBlackBoxesTheory_of_components
    {d : ℕ} [NeZero d]
    (fluxDefectDuality : FluxDefectDualityTheory d)
    (generalCoarseGrainingL2TwoExponent : GeneralCoarseGrainingL2TwoExponentTheory d) :
    HomogenizationBlackBoxesTheory d where
  fluxDefectDuality := fluxDefectDuality
  generalCoarseGrainingL2TwoExponent := generalCoarseGrainingL2TwoExponent

/-- Public Chapter 3.3 two-exponent black-box package with all currently
formalized analytic inputs discharged. -/
theorem homogenizationBlackBoxesTheory
    (d : ℕ) [NeZero d] :
  HomogenizationBlackBoxesTheory d :=
  homogenizationBlackBoxesTheory_of_components
    (fluxDefectDualityTheory d)
    (generalCoarseGrainingL2TwoExponentTheory d)

end Ch03
end Book
end Homogenization
