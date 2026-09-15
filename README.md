# CoarseGraining

A machine-checked **Lean 4** formalization of the manuscript
*Coarse-Graining Theory for Elliptic Equations* (Scott Armstrong and Tuomo
Kuusi), built on [`mathlib`](https://github.com/leanprover-community/mathlib4).

[![CI](https://github.com/scottnarmstrong/CoarseGraining/actions/workflows/build.yml/badge.svg)](https://github.com/scottnarmstrong/CoarseGraining/actions/workflows/build.yml)
[![Comparator audit](https://github.com/scottnarmstrong/CoarseGraining/actions/workflows/comparator.yml/badge.svg)](https://github.com/scottnarmstrong/CoarseGraining/actions/workflows/comparator.yml)

## What this is

This repository formalizes the coarse-graining theory of divergence-form
elliptic equations and quantitative stochastic homogenization developed in the
manuscript above. It builds the function-space, deterministic, probabilistic,
and homogenization-scale machinery up to the quenched minimal-scale theorem of
Chapter 5. Its public main result formalizes a uniformly elliptic, isotropic
specialization of the quenched comparison estimate in Scott Armstrong and
Tuomo Kuusi, *Renormalization Group and Elliptic Homogenization in High Contrast*,
Inventiones Mathematicae **242** (2025), 895–1086,
[doi:10.1007/s00222-025-01370-9](https://doi.org/10.1007/s00222-025-01370-9);
carrying out that formalization was the principal aim of the project. The
supporting analytic library also includes finite-exponent cube
Calderón–Zygmund estimates, finite-exponent Sobolev and fractional-Sobolev
infrastructure, and a finite-exponent local coarse-graining theorem.

- **1,606 Lean source files, 569,567 lines** (including the comparator audit
  surface; the production library is 1,589 files and 559,987 lines).
- **No `sorry`** anywhere in the library. (Each Mathlib-only comparator
  challenge in `Audit/` contains its single intentional statement-level
  `sorry`, filled by the corresponding solution file.)
- **No custom `axiom`.** The public theorems reduce to `mathlib`'s three
  standard foundational axioms — `propext`, `Classical.choice`, `Quot.sound` —
  verified by [`Homogenization/Meta/AxiomsAudit.lean`](Homogenization/Meta/AxiomsAudit.lean).
- Pinned to Lean `v4.33.0` and `mathlib` `v4.33.0`.

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
field, uniformly elliptic in the quadratic-form sense: almost surely, at almost
every point the (in general non-symmetric) matrix `a` satisfies the coercivity
bound `λ|ξ|² ≤ ξ·aξ` for every direction `ξ`, together with the inverse-side
bound `Λ⁻¹|ξ|² ≤ ξ·a⁻¹ξ` (equivalently, `|aη|² ≤ Λ·(η·aη)` for every `η`).

**Quenched homogenization above the minimal scale** —
`homogenizationComparison_uniformEllipticity`. There exist constants `C, α > 0`,
depending only on the dimension `d`, and a random minimal scale `𝒳 ≥ 1` — with
stretched-exponential (`Γ_d`) tails of size `exp(C·log²(2+θ̂))`, where `θ̂` is the
coarse-grained ellipticity constant of the law (see the next paragraph) — such that, almost
surely, on every origin cube `□ₘ` of side `3ᵐ` with `𝒳 ≤ 3ᵐ`, the heterogeneous solution `u` of
`−∇·a∇u = ∇·g` and the homogenized solution `v` of `−∇·ā∇v = ∇·g` (same force `∇·g`,
shared boundary data, `u − v ∈ H¹₀`) satisfy, for every force `g ∈ H^{3/4}`,

> `3^(−(3/4)m)·( ‖ā(∇u−∇v)‖_{H^{−3/4}} + ‖a∇u−ā∇v‖_{H^{−3/4}} )`
> `  ≤  C·(3ᵐ/𝒳)^(−α)·( √σ̄·‖σ^{1/2}∇u‖_{L²} + 3^{(3/4)m}·[g]_{H^{3/4}} )`.

Here the general Comparator uses the classical fractional Sobolev dual:
scalar tests have norm `[φ]_{H^{3/4}} + L^(−3/4)·‖φ‖_{L²}`, with normalized
L² measure and the Euclidean Gagliardo seminorm on a cube of side `L`.
The negative vector norm is the sum of the scalar component dual norms.
The force seminorm is also componentwise, using the equivalent sup-distance
Gagliardo normalization. The solution proves the comparison with the internal
dual-Besov quantity and absorbs its dimensional constant into `C`.

This specializes the general theorems
`homogenization_quenched_minimal_scale` and
`homogenization_quenched_homogenization_comparison` in
[`Homogenization/Book/Ch05/Theorems/Public.lean`](Homogenization/Book/Ch05/Theorems/Public.lean),
which require **no uniform ellipticity at all**. There, the law is assumed only
to be **coarse-grained elliptic**: the unit-scale coarse ellipticity observable
— the coarse-grained upper bound plus the reciprocal of the coarse-grained
lower bound, both defined through quadratic forms of the coarse-grained
matrices — has a stretched-exponential (`Γ_σ`) tail of size `θ̂` (the
manuscript's `Θ̂₀`; hypothesis `(P5)`). Under this assumption alone the random
minimal scale `𝒳` exists and satisfies the same stretched-exponential tail
bound with constant `exp(Cscale·log²(2+θ̂))`, with all constants chosen before
the law.

## Verified against a Mathlib-only statement

So that the central claims can be checked without trusting the ~570k-line
development, they are **independently verified by
[`leanprover/comparator`](https://github.com/leanprover/comparator)**. Each is
restated using **only Mathlib** — no project definitions — in a
`Challenge.lean`, and a `Solution.lean` proves that exact statement from the
library; the comparator confirms the two have identical elaborated types and
that the proof reduces to the three standard axioms, printing
`Your solution is okay!` (see [`Audit/README.md`](Audit/README.md)).

Five comparators are checked for the quenched comparison estimate — the
general statement in
[`Audit/QuenchedComparison/`](Audit/QuenchedComparison/) and four
specializations (three periodic laws and the random checkerboard).

The general quenched-comparison statement, as verified, is
`Homogenization.StatementAudit.homogenizationComparison_uniformEllipticity`,
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
          ∃ X : CoefficientField d → ℝ,
            S.IsMinimalScale X Cscale ∧
            ∀ᵐ a ∂S.P,
              ∀ {m : ℕ} {g : Vec d → Vec d}
                (pair : ComparisonPair sigmaBar a (originCube d m) g),
                X a ≤ (3 : ℝ) ^ m →
                ForceInH34 (originCube d m) g →
                comparisonDefect pair ≤
                  C * ((3 : ℝ) ^ m / X a) ^ (-alpha) * comparisonData pair
```

`Setup`, `CoefficientField`, `TriadicCube`, `ComparisonPair`, `comparisonDefect`,
`comparisonData`, `IsMinimalScale`, `ForceInH34`, and `originCube` are all defined
from Mathlib primitives in the challenge file itself; `comparisonDefect`/`comparisonData`
are the negative-Sobolev defect and data norm of the **Main result** section above.
Uniform ellipticity is carried by the almost-sure `uniformlyElliptic` field of
`Setup`, so it is not a separate hypothesis of the theorem. The
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
project itself elaborates in roughly half an hour (4,842 build jobs for the
default `Homogenization` target, which globs every module under
`Homogenization/`; `lake build Audit` additionally elaborates the comparator
surface and its semantic regression). Continuous
integration rebuilds the entire tree on every push; the live pass/fail status and
GitHub's own measured build time for each run are shown in the
[Actions tab](https://github.com/scottnarmstrong/CoarseGraining/actions) and in the
badges at the top of this file. A second workflow,
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml), re-runs
the full comparator sweep described below on every push, checking each of the
five pairs with both the Lean kernel and the independent `nanoda` kernel.

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
  Sobolev/         H¹ / W^{1,p}, fractional Sobolev, cube CZ, Hodge decomposition
  PDE/             weak solutions, Dirichlet problems
  Probability/     regular coefficient fields, stationarity, concentration, independence
  Deterministic/   coarse Caccioppoli / Poincaré, deterministic homogenization
  CoarseGraining/  block formalism, response identities, μ-operators
  HighContrast/    background material retained for downstream projects
  Renormalization/ renormalization-group iteration
  Internal/        internal support material
  Book/            chapter-by-chapter theorem surfaces (Ch01–Ch05)
  Meta/            AxiomsAudit.lean
  Examples/        instantiated laws (random checkerboard, periodic media)
Homogenization.lean   the root module (imports the whole library)
Audit/                Mathlib-only comparator challenges and solutions
doc/coarse-graining.pdf
```

## How this was built

The original Lean code in this repository was written by GPT-5.5 and Claude
Opus 4.6–4.8, under the close supervision of the authors. Subsequent updates,
including the finite-exponent analytic developments, were written by Claude
Fable 5 under the same supervision. The models, tooling, cost, and review
status are disclosed in full in
[`formalization.yaml`](formalization.yaml), following the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
standard.

## Authors and citation

The Lean development is by **Scott Armstrong** and **Tuomo Kuusi**. If you use this
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
