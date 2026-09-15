# Audit Comparator Surface

This directory contains Mathlib-only comparator challenges for the public-facing
quenched homogenization comparison theorem and four corollaries of it — three
deterministic periodic specializations and one random Bernoulli checkerboard.
Each comparator lives in its own subdirectory:

| Directory | Checked theorem |
| --- | --- |
| `QuenchedComparison/` | `Homogenization.StatementAudit.homogenizationComparison_uniformEllipticity` |
| `PeriodicGeneral/` | `Homogenization.StatementAudit.PeriodicGeneral.periodicGeneral_comparison` |
| `PeriodicConcrete/` | `Homogenization.StatementAudit.PeriodicConcrete.periodicConcrete_comparison` |
| `PeriodicSmooth/` | `Homogenization.StatementAudit.PeriodicSmooth.periodicSmooth_comparison` |
| `RandomCheckerboard/` | `Homogenization.StatementAudit.RandomCheckerboard.randomCheckerboard_quenchedComparison` |

`MeasurabilityLocality/SemanticRegression.lean` is an additional project-level
regression module, not a sixth comparator.  It checks that the integral-local
coarse measurable structure and the pointwise regular measurable structure
remain semantically distinct, including the corresponding locality notions.

The five comparators check the quenched comparison estimate described
below.

Each `Challenge.lean` imports only `Mathlib` and ends with one `sorry`, the
theorem proof being checked.  Each `Solution.lean` imports the repository theorem
surface and proves the same statement (where the statement vocabulary is large,
it is split into a `SolutionBasic.lean` imported by `Solution.lean`, keeping
every file within the repository line budget).  The comparator configurations
permit only:

```json
["propext", "Quot.sound", "Classical.choice"]
```

and set `enable_nanoda: false`: the baseline check uses the comparator's
builtin Lean kernel replay and needs only three tools (comparator,
`lean4export`, `landrun`).  The independent `nanoda` kernel is an optional
additional check — the CI workflow runs it on every commit (see below), and it
can be enabled locally by flipping the flag or via `COMPARATOR_NANODA`.

## What Is Checked

The five comparison-estimate comparators check the same *quenched
homogenization comparison estimate*, each for a different coefficient law.  In
every case the theorem has the shape

```lean
∃ C alpha Cscale : ℝ, 0 < C ∧ 0 < alpha ∧ 0 < Cscale ∧
  ∀ <law parameters>,
    ∃ sigmaBar : ℝ, 0 < sigmaBar ∧
      ∃ X : CoefficientField d → ℝ, <X is a minimal scale> ∧
        ∀ᵐ a ∂<law>, ∀ <solution data> <forcing g>,
          X a ≤ 3 ^ m → ForceInH34 (originCube d m) g →
            comparisonDefect ≤ C * (3 ^ m / X a) ^ (-alpha) * comparisonData
```

Following the 2026-08-19 readability redesign, every law is a measure on the
honest-fields carrier `CoefficientField d` (entrywise Borel-measurable,
locally integrable coefficient fields), whose σ-algebra is the pullback along
`toFun` of the observable σ-algebra on raw fields (point evaluations joined
with compactly supported bounded entry integrals); the bare function type
`RawCoeffField d` deliberately carries no global `MeasurableSpace` instance.
The minimal scale `X` is a function on the carrier, its stretched-exponential
tail is stated directly, structural hypotheses are stated as equality of
observable raw-field distributions (`LawInvariantUnder` via `rawLawAfter`,
which pins the σ-algebra in its type) under integer translations,
signed-coordinate permutations (`SignedPermutation` data), and adjoints, and
unit-range dependence uses the restriction σ-algebras `restrictionSigma U` of
measurable sets.  All hypotheses on a law are collected in one flat `Setup`
structure; measurability clauses that are free theorems on the carrier are
gone from the statement surface.

and asserts: there are universal constants `C, alpha, Cscale > 0` (chosen before
the law) such that the law has a homogenized scalar `sigmaBar > 0` and a random
*minimal scale* `X` (a positive field with a `Cscale`-controlled
stretched-exponential tail) for which, almost surely in the field `a` and for
every cube scale `3 ^ m ≥ X a` and forcing `g` with componentwise `H^s`
regularity (`s = comparisonS = 3 / 4`),

> `comparisonDefect ≤ C · (3 ^ m / X a) ^ (-alpha) · comparisonData`.

Here `comparisonDefect` is the scale-normalized negative-Sobolev (`H^{-s}`) size
of the homogenization error — the distance between the heterogeneous solution `u`
of `∇·(a ∇u) = ∇·g` and the homogenized solution `v` of
`∇·(sigmaBar·I ∇v) = ∇·g` — and `comparisonData` is the natural energy data (a
`√sigmaBar`-weighted `H¹` energy of `u` plus the scale-normalized `H^s` seminorm
of `g`).  So: above the minimal scale, the heterogeneous and homogenized
solutions agree at an algebraic rate in (cube sidelength `3 ^ m`) / (minimal
scale `X a`).  An auxiliary exponent `t = 1 / 8` (`4 t < s < 1`) is used
internally and appears in no statement.

The general `QuenchedComparison` uses the classical fractional dual norm:
its scalar tests have Euclidean Gagliardo seminorm plus the scale-weighted
normalized L² norm, with no boundary or mean-zero restriction. The vector
quantity sums the scalar component duals. Its solution proves domination by
the internal partition dual with a dimensional constant. The four specialized
comparators retain that internal dual-Besov quantity. Their laws and solution
data are:

| Comparator | Coefficient law | Solution data |
| --- | --- | --- |
| `QuenchedComparison` | **any** `Setup d`: an arbitrary stationary, unit-range, isotropic, adjoint-invariant, uniformly elliptic random law | weak `ComparisonPair` |
| `PeriodicGeneral` | Dirac point mass at an **arbitrary** deterministic field `a₀` that is periodic, isotropic, adjoint-invariant, and uniformly elliptic (`0 < lam ≤ Lam`), supplied as explicit hypotheses | weak `ComparisonPair` |
| `PeriodicConcrete` | Dirac point mass at the **explicit** field `a(x) = m(x) • I`, `m(x) = d + 2 + ∑ i, cos (2 π xᵢ)` (ellipticity `lam = 2`, `Lam = 2 d + 2` proved internally) | weak `ComparisonPair` |
| `PeriodicSmooth` | the same explicit field `a(x) = m(x) • I` | **classical**: smooth `u, v` solving the divergence-form equations pointwise |
| `RandomCheckerboard` | a genuinely **random** Bernoulli checkerboard law | weak `ComparisonPair` |

- **`QuenchedComparison`** is the root theorem: the bound holds for *every*
  `Setup d`, with `C, alpha, Cscale` uniform over all laws and ellipticity
  bounds.  The other four feed a specific law into it.
- **`PeriodicGeneral`** takes the law to be the Dirac mass at an arbitrary
  deterministic periodic field `a₀`; the periodicity, signed-coordinate
  invariance, adjoint-invariance, and ellipticity requirements are pointwise
  field identities collected in the flat `Setup` structure.
- **`PeriodicConcrete`** pins `a₀` to the explicit cosine field, whose
  ellipticity bounds `2 ≤ m(x) ≤ 2 d + 2` are discharged inside the proof, so the
  only remaining hypothesis is `2 ≤ d`.
- **`PeriodicSmooth`** states the same concrete estimate in fully *classical*
  terms: `u`, `v` are smooth (`ContDiff`) scalar fields solving
  `∇·(a ∇u) = ∇·g` and `∇·(sigmaBar·I ∇v) = ∇·g` pointwise, with `u − v` vanishing
  on the cube faces.  The weak `H¹` comparison datum the public theorem consumes
  is *constructed* from this classical data by integration by parts, so no
  weak-solution object is assumed; its defect and data are written with the
  classical gradient (`classicalComparisonDefect` / `classicalComparisonData`).
- **`RandomCheckerboard`** supplies an explicit *random* (non-deterministic) example.
  The field is a Bernoulli checkerboard — each unit lattice cell independently
  gets scalar conductance `lam` or `Lam` with probability `p` — a genuinely
  random, stationary, finite-range, uniformly elliptic law, and the estimate
  holds quenched (`∀ᵐ` in the field).  The statement is phrased for the unit
  triadic rescaling of the law, which preserves all constants.

## Definition Provenance

The challenge definitions are statement-level copies of the repository
definitions needed to state the theorem surfaces.

| Challenge declaration | Repository source |
| --- | --- |
| `Vec`, `Mat`, `RawCoeffField`, matrix/vector operations | `Homogenization/Ambient/*` |
| `CoefficientField`, probes, `entryTest`, `observableFieldSigma`, the carrier σ-algebra | `Homogenization/Probability/RegCoeffField.lean` and `Homogenization/Probability/RegCoeffField/Sigma.lean` |
| raw-field transformations, `rawLawAfter`/`LawInvariantUnder`, `restrictionSigma` (the carrier-endomorphism machinery itself now lives in the solutions) | `Homogenization/Probability/RegCoeffField/{Endomorphisms,Restriction}.lean` |
| `TriadicCube`, `cubeSet`, `openCubeSet`, descendants, cube measures | `Homogenization/Geometry/*` and `Homogenization/Book/Ch02` |
| coefficient laws and law hypotheses | `Homogenization/Book/Ch04/*` |
| weak solution pairs and comparison quantities | `Homogenization/Book/MainResults.lean` and `Homogenization/Book/Ch05/Theorems/Section57/*` |
| positive Sobolev force regularity | `Homogenization/Book/Ch03/Theorems/SobolevPublic.lean` |
| classical fractional dual in `QuenchedComparison` | `Homogenization/Sobolev/Fractional/ClassicalDualComparison.lean` |
| internal dual-Besov quantity in the specialized comparators | `Homogenization/Besov/Negative.lean` and `Homogenization/Book/Ch03/Theorems/SobolevPublic.lean` |
| block formalism and the variational quantity `Mu` | `Homogenization/Ambient/{Basic,BlockMatrix}.lean`, `Homogenization/CoarseGraining/BlockFormalism/{Structures,Properties}.lean`, and `Homogenization/CoarseGraining/Definitions.lean` |
| annealed coarse matrices and the scalar contrast | `Homogenization/Book/Ch04/AnnealedDefinitions.lean` and `Homogenization/Book/Ch05/Definitions.lean` |
| periodic Dirac bridge and examples | `Homogenization/Examples/Periodic/*` |
| random Bernoulli checkerboard law and setup | `Homogenization/Examples/RandomCheckerboard/Basic.lean` and `Homogenization/Examples/RandomCheckerboard/CarrierLaw.lean` |

The annealed convergence theorem is proved in
`Homogenization/Book/MainResults.lean`, but it is not currently represented by a
Mathlib-only comparator challenge.

## Reproducing The Checks

Build every challenge and solution:

```bash
lake build \
  Audit.QuenchedComparison.Challenge Audit.QuenchedComparison.Solution \
  Audit.PeriodicGeneral.Challenge Audit.PeriodicGeneral.Solution \
  Audit.PeriodicConcrete.Challenge Audit.PeriodicConcrete.Solution \
  Audit.PeriodicSmooth.Challenge Audit.PeriodicSmooth.Solution \
  Audit.RandomCheckerboard.Challenge Audit.RandomCheckerboard.Solution

lake build Audit.MeasurabilityLocality.SemanticRegression
```

The five challenge modules each emit their one documented theorem-body
`sorry` warning.  Those are the only expected warnings: the solutions,
semantic regression, and production library must emit no linter or other
compiler warnings.

Run the five comparators:

```bash
lake env comparator Audit/QuenchedComparison/comparator.json
lake env comparator Audit/PeriodicGeneral/comparator.json
lake env comparator Audit/PeriodicConcrete/comparator.json
lake env comparator Audit/PeriodicSmooth/comparator.json
lake env comparator Audit/RandomCheckerboard/comparator.json
```

Point the comparator at the tools via `PATH` or the environment variables
`COMPARATOR_LANDRUN` and `COMPARATOR_LEAN4EXPORT`.  Expected final output for
each run:

```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

Any other outcome falls into one of two very different classes.  **Audit
verdicts** are the comparator's own messages: `Const does not match between
challenge and target …`, an axiom-check complaint, or `… kernel rejected the
solution` — these mean the check genuinely failed.  **Setup problems** are
everything else: `unknown olean version` or import errors from `lean4export`
(its build must use the toolchain in `./lean-toolchain`, byte for byte),
`GLIBC`/spawn errors from `landrun` (build it from source), missing binaries,
or `lake` errors from a missing Mathlib cache (`lake exe cache get` first).
A setup problem says nothing about the mathematics; the reference environment
is the CI workflow.

Optionally, each solution can additionally be checked with the independent
`nanoda` kernel (a from-scratch Rust implementation of the Lean 4 kernel):
set `"enable_nanoda": true` in a comparator config and have `nanoda_bin` in
`PATH` (or set `COMPARATOR_NANODA`).  Two extra lines then precede the
verdict: `Running nanoda kernel on solution` / `nanoda kernel accepts the
solution`.  All five pairs pass this two-kernel variant (verified
2026-09-13).

The GitHub Actions workflow `.github/workflows/comparator.yml` runs the sweep
on every push to `main` — all five pairs, with the nanoda check enabled on
its own working copy of the configs, so the committed baseline stays
three-tool while CI always exercises the stronger two-kernel variant — and
uploads the per-pair logs as an artifact.

## Comparator Tools Used

The successful local runs (2026-09-13, all five pairs, both kernels) used:

| Tool | Version |
| --- | --- |
| Lean / Mathlib | `v4.33.0` |
| comparator | commit `575674928e239f5bc452aab72d1dd7b0f1326494` (built on its own pinned toolchain; it is version-agnostic toward this project since it orchestrates `lake`/`lean4export` subprocesses) |
| lean4export | tag `v4.33.0` (commit `15f6055e299ad5b89345e533cc2192f4cc00f659`) — must be built on the SAME toolchain as this repository, since it loads the project's oleans |
| landrun | `0.1.18` (commit `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`), built from source with `CGO_ENABLED=0 go build ./cmd/landrun` (Go >= 1.24; the release binaries require glibc 2.38) |
| nanoda (optional; CI enables it) | `nanoda_lib` 0.4.15 (commit `6ae1f0cd962f081f6c423454c5da729d841236a7`), `cargo build --release` (recent Rust; the binary is `target/release/nanoda_bin`) |

If a comparator binary was built against a different Lean version, point it at a
matching `lean4export` binary for this repository's pinned toolchain before
running the commands above.

### Maintenance invariant

Each pair's statement-vocabulary module (`SolutionBasic.lean`) must import
`Mathlib` and nothing else.  A repository import there changes instance
elaboration inside the vocabulary copy (the repository's private head-class
instance caches leak through oleans), which fails the comparator's
constant-by-constant closure comparison while every other check — `lake
build`, `#print axioms`, byte-diffs, `pp.all` statement printing — still
passes.  Repository imports and `attribute [-instance]` erasures belong in
`Solution.lean` (or a dedicated bridge module) only.  After any solution-side
edit or toolchain bump, re-run the comparator; the proxy checks are not
sufficient.
