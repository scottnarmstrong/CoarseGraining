import Homogenization.Examples.Periodic.DiracBridge

/-!
# Periodic deterministic comparison corollary

**Proves.** `periodicGeneral_comparison` — the public uniformly elliptic quenched
comparison estimate, specialized to the Dirac law concentrated at an *arbitrary*
periodic, isotropic, adjoint-invariant, uniformly elliptic deterministic
coefficient field, via the `periodicSetup` constructor in `DiracBridge`.

**Comparator.** `Audit/PeriodicGeneral` checks a Mathlib-only restatement of this
theorem against the proof below.  See `Audit/README.md` for the comparator map.

**Progression.** abstract theorem (`Audit/QuenchedComparison`) → *general periodic
(this file)* → explicit field (`PeriodicConcreteComparison`, `Audit/PeriodicConcrete`)
→ classical data (`PeriodicSmoothComparison`, `Audit/PeriodicSmooth`).
-/

namespace Homogenization
namespace Examples
namespace Periodic

open MeasureTheory
open scoped ENNReal

noncomputable section

/--
Fixed-exponent quenched homogenization comparison for a deterministic periodic
coefficient field.  The constants are chosen before the periodic field and its
ellipticity bounds; the stochastic setup is the Dirac law produced by
`periodicSetup`.
-/
theorem periodicGeneral_comparison {d : ℕ} [NeZero d] :
    ∃ C alpha Cscale : ℝ,
      0 < C ∧ 0 < alpha ∧ 0 < Cscale ∧
      ∀ (two_le_dim : 2 ≤ d) (a₀ : CoeffField d) (lam Lam : ℝ)
        (hper : IsPeriodicCoeffField a₀)
        (hiso : IsIsotropicCoeffField a₀)
        (hadj : IsAdjointInvariantCoeffField a₀)
        (hlam : 0 < lam) (hle : lam ≤ Lam)
        (hell : ∀ Q : TriadicCube d,
          Book.Ch04.AEEllipticOn lam Lam (openCubeSet Q) a₀),
        let S : Book.MainResults.Setup d :=
          periodicSetup two_le_dim a₀ lam Lam hper hiso hadj hlam hle hell
        ∃ sigmaBar : ℝ,
          0 < sigmaBar ∧
          ∃ X : CoeffField d → ℝ,
            S.IsMinimalScale X Cscale ∧
            ∀ᵐ aω ∂S.P,
              ∀ (ha : Book.Ch04.AELocallyUniformlyEllipticField aω)
                {m : ℕ} {g : Vec d → Vec d}
                (pair : S.ComparisonPair aω ha m g),
                X aω ≤ (3 : ℝ) ^ m →
                Book.Ch03.ForceSobolevRegularity
                  (Book.MainResults.originCube d m) Book.MainResults.fixedComparisonS g →
                S.comparisonDefect Book.MainResults.fixedComparisonS pair ≤
                  C * ((3 : ℝ) ^ m / X aω) ^ (-alpha) *
                    S.comparisonData Book.MainResults.fixedComparisonS pair := by
  obtain ⟨C, alpha, Cscale, hC, halpha, hCscale, hmain⟩ :=
    Book.MainResults.homogenizationComparison_uniformEllipticity (d := d)
  refine ⟨C, alpha, Cscale, hC, halpha, hCscale, ?_⟩
  intro two_le_dim a₀ lam Lam hper hiso hadj hlam hle hell
  let S : Book.MainResults.Setup d :=
    periodicSetup two_le_dim a₀ lam Lam hper hiso hadj hlam hle hell
  exact hmain S

end

end Periodic
end Examples
end Homogenization
