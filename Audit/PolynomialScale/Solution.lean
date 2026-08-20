import Mathlib
import Homogenization.HighContrast.Scale.Final
import Audit.PolynomialScale.SolutionBridge

attribute [-instance] Homogenization.instMeasurableSpaceVec
attribute [-instance] Homogenization.instMeasurableSpaceMat
attribute [-instance] Homogenization.instMeasurableSpaceCoeffField

/-!
# Solution for the polynomial homogenization-scale challenge

This file is the comparator solution surface for the unconditional
homogenization-scale capstone
`Homogenization.homogenizationScale_polynomial_of_unitRange`
(`Homogenization/HighContrast/Scale/Final.lean`).

The corresponding challenge imports only Mathlib.  This solution imports the
repository theorem, together with the bridge layer of
`Audit.PolynomialScale.SolutionBridge` — which in turn imports the Mathlib-only
statement vocabulary `Audit.PolynomialScale.SolutionBasic` — and proves the
same `StatementAudit.PolynomialScale` theorem surface, with a statement
byte-identical to the challenge's.

The vocabulary is kept in its own repository-free module on purpose: the
comparator compares the full dependency closure of the audited theorem
constant by constant against the Mathlib-only challenge, so the vocabulary
must elaborate in exactly the challenge's environment.

All the work is in `SolutionBridge.lean`:

* `toRepoLawCarrier` rebuilds the repository law-carrier witness that the
  redesigned challenge no longer hypothesizes;
* `toRepoStructuralLaw` converts the four `LawInvariantUnder` symmetries of the
  challenge into the repository's pushforward invariances, through the
  measurability of the carrier endomorphisms and the obligation-B transport
  `map_eq_iff_lawInvariantUnder`;
* `toRepoThetaEllipticLaw` transports the a.s. `Θ`-ellipticity event;
* `thetaAtScale_toRepo` identifies the repository's `Classical.choice`-based
  contrast selector with the audit's total `(0,0)`-entry ratio.

The audited theorem carries the explicit dimension restriction `hd : 3 ≤ d`
(`d > 2`), and its ellipticity hypothesis enters only through the
quadratic-form class `IsEllipticMatrix 1 Θ` (coercivity together with the
inverse quadratic-form bound); the coefficient fields are general
(non-symmetric) matrices.
-/

namespace Homogenization
namespace StatementAudit

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace PolynomialScale

/-! ## The theorem -/

/-- Polynomial homogenization scale for high-contrast media.  The dimension
restriction `3 ≤ d` (that is, `d > 2`) is explicit, and the constants are
chosen before the medium, hence depend only on `d`. -/
theorem homogenizationScale_polynomial_of_unitRange
    {d : ℕ} [NeZero d] (hd : 3 ≤ d) :
    ∃ Cscale Ctriadic alpha : ℝ,
      0 < Cscale ∧ 0 < Ctriadic ∧ 0 < alpha ∧
      ∀ S : Setup d,
        ∃ N0 : ℕ,
          (∀ n : ℕ,
            thetaAtScale S.P ((N0 + n : ℕ) : ℤ) - 1 ≤
              (3 : ℝ) ^ (-alpha * (n : ℝ))) ∧
          (N0 : ℝ) ≤ Cscale * Real.log (2 + S.Θ) ∧
          (3 : ℝ) ^ (N0 : ℝ) ≤ (2 + S.Θ) ^ Ctriadic := by
  obtain ⟨Cscale, Ctriadic, alpha, hCs, hCt, halpha, hmain⟩ :=
    _root_.Homogenization.homogenizationScale_polynomial_of_unitRange (d := d) hd
  refine ⟨Cscale, Ctriadic, alpha, hCs, hCt, halpha, ?_⟩
  intro S
  haveI := S.isProbability
  haveI : IsProbabilityMeasure (Measure.map (toRepoReg (d := d)) S.P) :=
    isProbabilityMeasure_map_toRepoReg S.P
  have hP' := toRepoLawCarrier S
  have hStruct' := toRepoStructuralLaw S
  have hLaw' := toRepoThetaEllipticLaw S
  obtain ⟨N0, hdecay, hlog, htriadic⟩ := hmain S.one_le_theta hP' hStruct' hLaw'
  refine ⟨N0, ?_, hlog, htriadic⟩
  intro n
  have h := hdecay n
  rwa [thetaAtScale_toRepo S.P hP' hStruct'] at h

end PolynomialScale

end

end StatementAudit
end Homogenization
