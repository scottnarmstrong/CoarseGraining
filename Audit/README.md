# Audit Comparator Surface

This directory contains the Mathlib-only comparator challenge for the
public-facing quenched homogenization comparison theorem.

## What Is Checked

`Audit/Challenge.lean` imports only `Mathlib` and states:

```lean
Homogenization.StatementAudit.homogenizationComparison_uniformEllipticity
```

The matching proof is in `Audit/Solution.lean`.  The comparator configuration is
`Audit/comparator.json`.

The checked theorem is the uniformly elliptic, fixed-exponent corollary of the
quenched comparison theorem.  The public exponents are fixed to
`t = 1 / 8` and `s = 3 / 4`.  The constants are bound as

```lean
∃ C alpha Cscale : ℝ, 0 < C ∧ 0 < alpha ∧ 0 < Cscale ∧
  ∀ S : Setup d, ...
```

so `C`, `alpha`, and `Cscale` do not depend on the law, the ellipticity bounds,
the realization, `m`, `g`, the solution pair, or exponent variables.

The repository theorem with the same public scope is:

```lean
Homogenization.Book.MainResults.homogenizationComparison_uniformEllipticity
```

The variable-exponent corollary
`Homogenization.Book.MainResults.homogenizationComparison_uniformEllipticity_variableExponents`
is not the public comparator target because its constants are selected after
`S`, `t`, and `s`.

## Scope And Caveats

The challenge states an existential positive scalar `sigmaBar`.  The solution
chooses the repository scalar
`Homogenization.Book.Ch05.Section57.barSigmaLimit`; the challenge does not expose
the internal construction of this scalar.

The positive force hypothesis is stated as `H^s` using the project's
Gagliardo/Sobolev representative.  The negative comparison norm is formalized
through the project's dual `B^{-s}_{2,2}`/`H^{-s}` representative.

The theorem quantifies `{d : ℕ} [NeZero d]`, while `Setup d` contains
`two_le_dim : 2 ≤ d`.  For dimensions below two the theorem is vacuous because
there is no `Setup d`.

The annealed convergence theorem is proved in
`Homogenization/Book/MainResults.lean`, but it is not currently represented by a
Mathlib-only comparator challenge.

## Definition Provenance

The challenge definitions are statement-level copies of the repository
definitions needed to state the theorem.

| Challenge declaration | Repository source |
| --- | --- |
| `Vec`, `Mat`, `CoeffField`, matrix/vector operations | `Homogenization/Ambient/CoefficientField.lean` |
| `TriadicCube`, `cubeSet`, `openCubeSet`, descendants, cube measures | `Homogenization/Geometry/*` and `Homogenization/Book/Ch02` |
| `CoeffLaw`, `LocalSigma`, stationarity, unit range, isotropy, adjoint invariance | `Homogenization/Book/Ch04/Law.lean` |
| `UniformEllipticityBounds` | `Homogenization/Book/Ch05/Theorems/Section57/UniformEllipticityBridge.lean` |
| `H1Function`, `H10Function`, weak equations | `Homogenization/Sobolev/*`, `Homogenization/PDE/*`, and `Homogenization/Book/Ch03` |
| positive Sobolev force regularity | `Homogenization/Book/Ch03/Theorems/SobolevPublic.lean` |
| negative Sobolev/dual norm representative | `Homogenization/Besov/Negative.lean` and `Homogenization/Book/Ch03/Theorems/SobolevPublic.lean` |
| `ComparisonPair`, `comparisonDefect`, `comparisonData` | `Homogenization/Book/MainResults.lean` and `Homogenization/Book/Ch05/Theorems/Section57/HomogenizationAssembly.lean` |
| `Setup.IsMinimalScale` | `Homogenization/Book/MainResults.lean` |

`Audit/Solution.lean` contains bridge lemmas showing that the copied challenge
definitions align with the repository definitions used by
`Homogenization.Book.MainResults.homogenizationComparison_uniformEllipticity`.

## Reproducing The Check

Lean version:

```bash
cat lean-toolchain
# leanprover/lean4:v4.26.0
```

Build the challenge and solution:

```bash
lake build Audit.Challenge Audit.Solution
```

Run the comparator on the config:

```bash
lake env comparator Audit/comparator.json
```

Expected final output:

```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

### Toolchain compatibility (read this before running)

The upstream `leanprover/comparator` distribution currently ships a **newer**
Lean toolchain than this project's pinned `v4.26.0`.  Its bundled `lean4export`
will reject this project's `.olean` files with an `incompatible header` error
*before any judgement is made*.  This is purely an exporter-version mismatch —
the comparator's own (newer) Lean kernel replays a `v4.26.0` export without
trouble.

To reproduce the check, point the comparator at a `lean4export` built for
`v4.26.0`:

```bash
COMPARATOR_LEAN4EXPORT=/path/to/lean4export-v4.26.0 \
  lake env comparator Audit/comparator.json
```

If your environment also lacks the default sandbox (e.g. no
`systemd-run --user` / user D-Bus), set `COMPARATOR_LANDRUN` to a `landrun`
binary or to the comparator's `scripts/fake-landrun.sh` dev shim.  The sandbox
affects isolation only, not the accept/reject decision.  Run with verified
versions below for a byte-for-byte reproduction.

## Comparator Tools Used

The successful local run used:

| Tool | Version |
| --- | --- |
| Lean / Mathlib | `v4.26.0` |
| comparator | commit `5fb6e55e87cc2308e29e0916a3cb39522dbfebfd` |
| lean4export | commit `3e1cdfe206ec3f54bae4a548d814ce9b2c1bb43d` |
| landrun | `0.1.15` |

`Audit/comparator.json` permits only:

```json
["propext", "Quot.sound", "Classical.choice"]
```

and has `enable_nanoda: false`.
