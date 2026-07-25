# Audit Comparator Surface

This directory contains Mathlib-only comparator challenges for the public-facing
quenched homogenization comparison theorem and four corollaries of it — three
deterministic periodic specializations and one random Bernoulli checkerboard —
together with the polynomial homogenization-scale capstone and its
Bernoulli-checkerboard instantiation.
Each comparator lives in its own subdirectory:

| Directory | Checked theorem |
| --- | --- |
| `QuenchedComparison/` | `Homogenization.StatementAudit.homogenizationComparison_uniformEllipticity` |
| `PeriodicGeneral/` | `Homogenization.StatementAudit.PeriodicGeneral.periodicGeneral_comparison` |
| `PeriodicConcrete/` | `Homogenization.StatementAudit.PeriodicConcrete.periodicConcrete_comparison` |
| `PeriodicSmooth/` | `Homogenization.StatementAudit.PeriodicSmooth.periodicSmooth_comparison` |
| `RandomCheckerboard/` | `Homogenization.StatementAudit.RandomCheckerboard.randomCheckerboard_quenchedComparison` |
| `PolynomialScale/` | `Homogenization.StatementAudit.PolynomialScale.homogenizationScale_polynomial_of_unitRange` |
| `CheckerboardScale/` | `Homogenization.StatementAudit.CheckerboardScale.randomCheckerboard_homogenizationScale` |

The first five comparators check the quenched comparison estimate described
below.  `PolynomialScale/` checks the unconditional homogenization-scale
capstone: under the explicit dimension restriction `d > 2` (the hypothesis
`hd : 3 ≤ d`), every `Θ`-elliptic (`Θ ≥ 1`, in the quadratic-form ellipticity
class `IsEllipticMatrix 1 Θ`: coercivity `∀ ξ, |ξ|² ≤ ξ · a ξ` together with
the inverse quadratic-form bound `∀ ξ, Θ⁻¹ |ξ|² ≤ ξ · a⁻¹ ξ`; the fields are
general non-symmetric matrices) stationary, unit-range, isotropic,
adjoint-invariant probability law has geometrically decaying scalar contrast,
`θ_{N₀+n} - 1 ≤ 3^{-alpha·n}`, from an entry scale `N₀ ≤ Cscale · log(2 + Θ)`
with `3^{N₀} ≤ (2 + Θ)^{Ctriadic}`, where `Cscale, Ctriadic, alpha > 0` are
dimensional constants chosen before the law.  The scalar contrast
`thetaAtScale P n` is mirrored as the `(0, 0)`-entry ratio of the annealed
coarse matrices built by polarization from the variational quantity `Mu`.

`CheckerboardScale/` checks the Bernoulli-checkerboard instantiation of the
same capstone: under the explicit dimension restriction `d > 2` (the
hypothesis `hd : 3 ≤ d`), for every `1 ≤ lam ≤ Lam` and every coin parameter
`p ≤ 1`, the Bernoulli checkerboard law with conductances `lam`, `Lam` — a
genuinely random stationary law whose realizations lie pointwise in the
quadratic-form ellipticity class `IsEllipticMatrix 1 Lam` (coercivity
`∀ ξ, |ξ|² ≤ ξ · a ξ` together with the inverse quadratic-form bound
`∀ ξ, Lam⁻¹ |ξ|² ≤ ξ · a⁻¹ ξ`; the class is stated for general non-symmetric
matrices) — satisfies the same contrast decay
`θ_{N₀+n} - 1 ≤ 3^{-alpha·n}` from an entry scale
`N₀ ≤ Cscale · log(2 + Lam)` with `3^{N₀} ≤ (2 + Lam)^{Ctriadic}`.  The
capstone's ellipticity parameter is instantiated at `Θ = Lam`, and all of its
law hypotheses — the probability instance, the law carrier, the structural
law, and the `Θ`-ellipticity class membership — are discharged by the
checkerboard construction, so none of them appears in the statement: the
triadic bound `3^{N₀} ≤ (2 + Lam)^{Ctriadic}` exhibits the physical entry
scale as an explicit algebraic (polynomial) function of the contrast `Lam`,
concretely instantiated on a random law.

Each `Challenge.lean` imports only `Mathlib` and ends with one `sorry`, the
theorem proof being checked.  Each `Solution.lean` imports the repository theorem
surface and proves the same statement (where the statement vocabulary is large,
it is split into a `SolutionBasic.lean` imported by `Solution.lean`, keeping
every file within the repository line budget).  The comparator configurations
permit only:

```json
["propext", "Quot.sound", "Classical.choice"]
```

and set `enable_nanoda: false`.

## What Is Checked

The five comparison-estimate comparators check the same *quenched
homogenization comparison estimate*, each for a different coefficient law.  In
every case the theorem has the shape

```lean
∃ C alpha Cscale : ℝ, 0 < C ∧ 0 < alpha ∧ 0 < Cscale ∧
  ∀ <law parameters>,
    ∃ sigmaBar : ℝ, 0 < sigmaBar ∧
      ∃ X : RegCoeffField d → ℝ, <X is a minimal scale> ∧
        ∀ᵐ a ∂<law>, ∀ <solution data> <forcing g>,
          X a ≤ 3 ^ m → ForceSobolevRegularity (originCube d m) (3/4) g →
            comparisonDefect ≤ C * (3 ^ m / X a) ^ (-alpha) * comparisonData
```

Following the carrier redesign, every law is a measure on the local mirror of
the *regular-fields carrier* `RegCoeffField d` (entrywise Borel-measurable,
locally integrable coefficient fields, carrying the join of the pointwise and
entry-test σ-algebras), the minimal scale `X` is a function on the carrier, and
the structural hypotheses use the carrier endomorphisms
(`translateReg`/`rotateReg`/`adjointReg`) and the restriction σ-algebras
`RestrictionSigmaR U hU` of measurable sets.  The audit `LawCarrier` consists
of the probability instance and the a.s. local-uniform-ellipticity support
alone: the former local-observable and slice measurability fields are
law-independent free theorems on the carrier and are gone from the statement
surface.

and asserts: there are universal constants `C, alpha, Cscale > 0` (chosen before
the law) such that the law has a homogenized scalar `sigmaBar > 0` and a random
*minimal scale* `X` (a positive field with a `Cscale`-controlled
stretched-exponential tail) for which, almost surely in the field `a` and for
every cube scale `3 ^ m ≥ X a` and forcing `g` with componentwise `H^s`
regularity (`s = fixedComparisonS = 3 / 4`),

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

The five comparison-estimate comparators differ only in the law and in how the
solution pair is presented:

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
  deterministic periodic field `a₀`; the periodicity, isotropy,
  adjoint-invariance, and ellipticity requirements are the explicit hypotheses
  `_hper`, `_hiso`, `_hadj`, `_hlam`, `_hle`, `_hell`.
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
- **`RandomCheckerboard`** is the only *random* (non-deterministic) comparator.
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
| `Vec`, `Mat`, `CoeffField`, matrix/vector operations | `Homogenization/Ambient/*` |
| `RegCoeffField`, probes, `entryTestR`, the carrier σ-algebra | `Homogenization/Probability/RegCoeffField.lean` and `Homogenization/Probability/RegCoeffField/Sigma.lean` |
| carrier endomorphisms and `RestrictionSigmaR` | `Homogenization/Probability/RegCoeffField/{Endomorphisms,Restriction}.lean` |
| `TriadicCube`, `cubeSet`, `openCubeSet`, descendants, cube measures | `Homogenization/Geometry/*` and `Homogenization/Book/Ch02` |
| coefficient laws and law hypotheses | `Homogenization/Book/Ch04/*` |
| weak solution pairs and comparison quantities | `Homogenization/Book/MainResults.lean` and `Homogenization/Book/Ch05/Theorems/Section57/*` |
| positive Sobolev force regularity | `Homogenization/Book/Ch03/Theorems/SobolevPublic.lean` |
| negative Sobolev/dual norm representative | `Homogenization/Besov/Negative.lean` and `Homogenization/Book/Ch03/Theorems/SobolevPublic.lean` |
| block formalism and the variational quantity `Mu` | `Homogenization/Ambient/{Basic,BlockMatrix}.lean`, `Homogenization/CoarseGraining/BlockFormalism/{Structures,Properties}.lean`, and `Homogenization/CoarseGraining/Definitions.lean` |
| annealed coarse matrices and the scalar contrast | `Homogenization/Book/Ch04/AnnealedDefinitions.lean` and `Homogenization/Book/Ch05/Definitions.lean` |
| the homogenization-scale theorem surface | `Homogenization/HighContrast/Scale/Final.lean` |
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
  Audit.RandomCheckerboard.Challenge Audit.RandomCheckerboard.Solution \
  Audit.PolynomialScale.Challenge Audit.PolynomialScale.Solution \
  Audit.CheckerboardScale.Challenge Audit.CheckerboardScale.Solution
```

Run the seven comparators:

```bash
lake env comparator Audit/QuenchedComparison/comparator.json
lake env comparator Audit/PeriodicGeneral/comparator.json
lake env comparator Audit/PeriodicConcrete/comparator.json
lake env comparator Audit/PeriodicSmooth/comparator.json
lake env comparator Audit/RandomCheckerboard/comparator.json
lake env comparator Audit/PolynomialScale/comparator.json
lake env comparator Audit/CheckerboardScale/comparator.json
```

Expected final output for each run:

```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

## Comparator Tools Used

The successful local runs used:

| Tool | Version |
| --- | --- |
| Lean / Mathlib | `v4.26.0` |
| comparator | commit `5fb6e55e87cc2308e29e0916a3cb39522dbfebfd` |
| lean4export | commit `3e1cdfe206ec3f54bae4a548d814ce9b2c1bb43d` |
| landrun | `0.1.15` |

If a comparator binary was built against a different Lean version, point it at a
matching `lean4export` binary for this repository's pinned toolchain before
running the commands above.
