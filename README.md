# CoarseGraining

A machine-checked **Lean 4** formalization of the manuscript
*Coarse-Graining Theory for Elliptic Equations* (Scott Armstrong and Tuomo
Kuusi), built on [`mathlib`](https://github.com/leanprover-community/mathlib4).

[![CI](https://github.com/scottnarmstrong/CoarseGraining/actions/workflows/build.yml/badge.svg)](https://github.com/scottnarmstrong/CoarseGraining/actions/workflows/build.yml)

## What this is

This repository formalizes the coarse-graining theory of divergence-form
elliptic equations and quantitative stochastic homogenization developed in the
manuscript above. It builds the function-space, deterministic, probabilistic,
and homogenization-scale machinery up to the quenched minimal-scale theorem of
Chapter 5. Its main result formalizes a central theorem of Scott Armstrong and
Tuomo Kuusi, *Renormalization Group and Elliptic Homogenization in High Contrast*,
Inventiones Mathematicae **242** (2025), 895–1086,
[doi:10.1007/s00222-025-01370-9](https://doi.org/10.1007/s00222-025-01370-9);
carrying out that formalization was the principal aim of the project.

- **1,200 Lean source files, ~449,000 lines.**
- **No `sorry`** anywhere in the development.
- **No custom `axiom`.** The public theorems reduce to `mathlib`'s three
  standard foundational axioms — `propext`, `Classical.choice`, `Quot.sound` —
  verified by [`Homogenization/Meta/AxiomsAudit.lean`](Homogenization/Meta/AxiomsAudit.lean).
- Pinned to Lean `v4.26.0` and `mathlib` `v4.26.0`.

## Scope and faithfulness

**Every theorem stated in the manuscript is formalized in Lean.** In a few places
the formalized statement is less general than the manuscript statement or carries
an additional hypothesis; each such case is flagged in a footnote in the
manuscript and recorded, theorem by theorem, in the manuscript-to-Lean map
[`CORRESPONDENCE.md`](CORRESPONDENCE.md).

## The manuscript

The compiled manuscript is included as [`doc/coarse-graining.pdf`](doc/coarse-graining.pdf).
It is a **draft, still in preparation**, and was itself written largely with the
aid of GPT-5.5 under close supervision of the authors. The LaTeX source is not part of this repository.

## Main result

The main theorem is exposed, for the **uniformly elliptic** special case, in
[`Homogenization/Book/MainResults.lean`](Homogenization/Book/MainResults.lean).
It is proved with no `sorry` and no custom axiom (it depends only on Lean's
three standard foundations). The Lean development assumes the coefficient law is
**isotropic**, a hypothesis not required in the published paper cited above.

Throughout, the coefficient field is a stationary, unit-range, isotropic random
field that is uniformly elliptic: almost surely `λI ≤ a ≤ ΛI`.

**Quenched homogenization above the minimal scale** —
`homogenizationComparison_uniformEllipticity`. There exist constants `C, α > 0`,
depending only on the dimension `d`, and a random minimal scale `𝒳 ≥ 1` — with
stretched-exponential (`Γ_d`) tails of size `exp(C·log²(2+θ̂))` — such that, almost
surely, on every triadic cube `□ₘ` with `𝒳 ≤ 3ᵐ`, the heterogeneous solution `u` of
`−∇·a∇u = ∇·g` and the homogenized solution `v` of `−∇·ā∇v = ∇·g` (same force `∇·g`,
shared boundary data, `u − v ∈ H¹₀`) satisfy, for every force `g ∈ H^{3/4}`,

> `3^(−(3/4)m)·( ‖ā(∇u−∇v)‖_{H^{−3/4}} + ‖a∇u−ā∇v‖_{H^{−3/4}} )`
> `  ≤  C·(3ᵐ/𝒳)^(−α)·( √σ̄·‖σ^{1/2}∇u‖_{L²} + 3^{(3/4)m}·[g]_{H^{3/4}} )`.

(Here `Hˢ = B^s_{2,2}` is the fractional Sobolev space, and the positive seminorm
`[g]_{H^{3/4}}` is taken componentwise.)

This specializes the general (non-uniform) theorems
`homogenization_quenched_minimal_scale` and
`homogenization_quenched_homogenization_comparison` in
[`Homogenization/Book/Ch05/Theorems/Public.lean`](Homogenization/Book/Ch05/Theorems/Public.lean).

## Verified against a Mathlib-only statement

So that the central claim can be checked without trusting the ~449k-line
development, the quenched comparison theorem is **independently verified by
[`leanprover/comparator`](https://github.com/leanprover/comparator)**. It is
restated using **only Mathlib** — no project definitions — in
[`Audit/Challenge.lean`](Audit/Challenge.lean), and
[`Audit/Solution.lean`](Audit/Solution.lean) proves that exact statement from the
library. The comparator confirms the two have identical elaborated types and that
the proof reduces to the three standard axioms; running it prints
`Your solution is okay!` (see [`Audit/README.md`](Audit/README.md)).

The verified statement is `Homogenization.StatementAudit.homogenizationComparison_uniformEllipticity`,
with the Sobolev exponent fixed to `s = 3/4`. The constants `C, α, Cscale` are
chosen **before** the law and depend only on the dimension:

```lean
theorem homogenizationComparison_uniformEllipticity
    {d : ℕ} [NeZero d] :
    ∃ C alpha Cscale : ℝ,
      0 < C ∧ 0 < alpha ∧ 0 < Cscale ∧
      ∀ S : Setup d,
        ∃ sigmaBar : ℝ,
          0 < sigmaBar ∧
          ∃ X : CoeffField d → ℝ,
            S.IsMinimalScale X Cscale ∧
            ∀ᵐ a ∂S.P,
              ∀ (ha : AELocallyUniformlyEllipticField a)
                {m : ℕ} {g : Vec d → Vec d}
                (pair : ComparisonPair sigmaBar a ha m g),
                X a ≤ (3 : ℝ) ^ m →
                ForceSobolevRegularity (originCube d m) fixedComparisonS g →
                comparisonDefect sigmaBar fixedComparisonS pair ≤
                  C * ((3 : ℝ) ^ m / X a) ^ (-alpha) *
                    comparisonData sigmaBar fixedComparisonS pair
```

`Setup`, `ComparisonPair`, `comparisonDefect`, `comparisonData`, `IsMinimalScale`,
`ForceSobolevRegularity`, and `originCube` are all defined from Mathlib primitives
in the challenge file itself; `comparisonDefect`/`comparisonData` are the
negative-Sobolev defect and data norm of the **Main result** section above. The
project-wide disclosure (scope, models, cost, review status, statement map)
follows the [`formalization.yaml`](formalization.yaml) standard.

## Building

The project uses [`elan`](https://github.com/leanprover/elan) (the Lean
toolchain manager) and Lake. The toolchain is pinned in
[`lean-toolchain`](lean-toolchain), so `elan` installs the right Lean version
automatically.

```bash
# from the repository root
lake exe cache get   # download prebuilt mathlib oleans (avoids a multi-hour mathlib build)
lake build           # compile the project
```

`lake exe cache get` requires the committed [`lake-manifest.json`](lake-manifest.json),
which pins the exact dependency revisions.

On an 8-core / 32 GB machine, with Mathlib supplied by `lake exe cache get`, the
project itself elaborates in about 26 minutes (4,120 build jobs). Continuous
integration rebuilds the entire tree on every push; the live pass/fail status and
GitHub's own measured build time for each run are shown in the
[Actions tab](https://github.com/scottnarmstrong/CoarseGraining/actions) and in the
badge at the top of this file.

To use the library, `import Homogenization` (the root module
[`Homogenization.lean`](Homogenization.lean)) pulls in the whole development; the
public results are in `import Homogenization.Book.MainResults`.

## Repository layout

```
Homogenization/
  Ambient/         basic Hilbert-space and coefficient-field infrastructure
  Geometry/        triadic cubes, partitions, domains
  Multiscale/      cube averages and projections
  Besov/           Besov spaces, duality, Poincaré inequalities
  Sobolev/         H¹ / W^{1,p} theory, Hodge decomposition
  PDE/             weak solutions, Dirichlet problems
  Probability/     stationary fields, concentration, independence
  Deterministic/   coarse Caccioppoli / Poincaré, deterministic homogenization
  CoarseGraining/  block formalism, response identities, μ-operators
  Multiscale/, Renormalization/, ...
  Book/            chapter-by-chapter theorem surfaces (Ch02–Ch05)
  Meta/            AxiomsAudit.lean
Homogenization.lean   the root module (imports the whole library)
doc/coarse-graining.pdf
```

## How this was built

The Lean code in this repository was written entirely by GPT-5.5 and Claude
Opus 4.6–4.8, under the close supervision of the authors. The models, tooling,
cost, and review status are disclosed in full in
[`formalization.yaml`](formalization.yaml), following the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
standard.

## Authors and citation

The manuscript is by **Scott Armstrong** and **Tuomo Kuusi**. If you use this
formalization, please cite it using the metadata in [`CITATION.cff`](CITATION.cff).

## Acknowledgements

Scott Armstrong and Tuomo Kuusi were supported by the European Research Council
(ERC) under the European Union's Horizon Europe research and innovation
programme, grant agreement No. 101200828.

This formalization is built on [Lean 4](https://lean-lang.org) and
[Mathlib](https://github.com/leanprover-community/mathlib4); the comparator audit
in [`Audit/`](Audit/) uses [`leanprover/comparator`](https://github.com/leanprover/comparator).

## License

The Lean code in this repository is licensed under the **Apache License 2.0**
(see [`LICENSE`](LICENSE)). The manuscript PDF in `doc/` is © the authors, all
rights reserved, and is not covered by the Apache license.
