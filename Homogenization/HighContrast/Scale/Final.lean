import Homogenization.HighContrast.Scale.CapstoneUniform
import Homogenization.HighContrast.Scale.Pathwise
import Homogenization.HighContrast.Scale.RecordsFinal

/-!
# The unconditional homogenization-scale capstone

`homogenizationScale_polynomial_of_unitRange` is the public headline of the
homogenization-scale track: for every dimension `d ≥ 3` there are dimensional
constants `Cscale, Ctriadic, α > 0` such that *every* `Θ`-elliptic probability
law satisfies the homogenization-scale contrast decay, with the entry scale
`N₀ = O(log(2 + Θ))` uniformly.

Every hypothesis of the earlier capstones
(`thetaEllipticLaw_implies_homogenizationScale_uniform`, `…_implies_…`,
`…'`) — the high-contrast exponent record `hc`, the parameter record `params`,
the localization / small-contrast input `loc`, the quantitative
coarse-grained ellipticity witness `hP4`, and the pathwise fluctuation input
`hpath` — is discharged here:

* `params := canonicalParams d`, `hc := hcOfParams params`,
  `loc := locOfParams params` (`RecordsFinal.lean`);
* `hP4 := qcgeOfThetaEllipticLaw …` built from the `Θ`-elliptic law;
* `hpath := pathwise_fluctuation_bound …` (`Pathwise.lean`).
-/

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch04 (CoeffLaw LawCarrier StructuralLaw)
open Homogenization.Book.Ch05 (QuantitativeCoarseGrainedEllipticity thetaAtScale)

namespace Homogenization

/-- **The unconditional homogenization-scale capstone.**

For every `d ≥ 3` there are dimensional constants `Cscale, Ctriadic, α > 0`
such that every `Θ`-elliptic probability law (`Θ ≥ 1`) satisfies:

* the contrast decays geometrically from an entry scale `N₀`,
  `θ_{N₀+n} - 1 ≤ 3^{-α n}`;
* the entry scale is logarithmic in the ellipticity ratio,
  `N₀ ≤ Cscale · log(2 + Θ)`; and
* the physical entry scale is polynomial, `3^{N₀} ≤ (2 + Θ)^{Ctriadic}`.

The scale/triadic constants and the decay exponent are chosen **before** `Θ`,
so this is a genuine `Θ`-growth statement (`N₀ = O(log(2 + Θ))` uniformly). -/
theorem homogenizationScale_polynomial_of_unitRange {d : ℕ} [NeZero d] (hd : 3 ≤ d) :
    ∃ Cscale Ctriadic alpha : ℝ, 0 < Cscale ∧ 0 < Ctriadic ∧ 0 < alpha ∧
      ∀ {Θ : ℝ} (_hΘ : 1 ≤ Θ) {P : CoeffLaw d} [IsProbabilityMeasure P]
        (hP : LawCarrier P) (hStruct : StructuralLaw P)
        (_hLaw : Homogenization.ThetaEllipticLaw Θ P),
      ∃ N0 : ℕ,
        (∀ n : ℕ,
          thetaAtScale hP hStruct ((N0 + n : ℕ) : ℤ) - 1 ≤
            (3 : ℝ) ^ (-alpha * (n : ℝ))) ∧
        (N0 : ℝ) ≤ Cscale * Real.log (2 + Θ) ∧
        (3 : ℝ) ^ ((N0 : ℕ) : ℝ) ≤ (2 + Θ) ^ Ctriadic := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨Cscale, Ctriadic, alpha, hCs, hCt, ha, hmain⟩ :=
    thetaEllipticLaw_implies_homogenizationScale_uniform hd
      (hcOfParams (canonicalParams d hd2)) (canonicalParams d hd2)
      (locOfParams (canonicalParams d hd2)) rfl
  refine ⟨Cscale, Ctriadic, alpha, hCs, hCt, ha, ?_⟩
  intro Θ hΘ P _ hP hStruct hLaw
  exact hmain hΘ hP hStruct hLaw (qcgeOfThetaEllipticLaw hd2 hΘ hP hLaw)
    (qcgeOfThetaEllipticLaw_params hd2 hΘ hP hLaw)
    (fun {_j} {_Q} hQ => pathwise_fluctuation_bound hΘ hP hStruct hLaw hQ)

end Homogenization
