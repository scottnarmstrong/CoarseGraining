# Correspondence: manuscript ↔ Lean

This document maps **every numbered statement** in the manuscript *Coarse-Graining
Theory for Elliptic Equations* (included as
[`doc/coarse-graining.pdf`](doc/coarse-graining.pdf)) to its Lean declaration and
file, so a reader of the manuscript can locate where each result is proved.

**Conventions.**
- Lean names are given relative to the `Homogenization` namespace root; file
  paths are relative to the repository root.
- **Status**: `proved` — formalized as stated; `partial` — formalized in a
  restricted form (e.g. a single exponent / regime), flagged by a manuscript
  footnote; `not-formalized` — absent from the Lean development (and, where
  applicable, removed from the compiled manuscript).
- Chapter 0 is notation; it introduces no numbered statements.
- Several manuscript lemmas are packaged as a single Lean "`…Theory`" record
  whose conjuncts correspond to the manuscript's displayed claims; in those cases
  the Lean column names the package.
- The two main results — `t.annealed.convergence` and
  `t.quenched.homogenization.comparison` — are additionally exposed in a uniformly
  elliptic specialization in
  [`Homogenization/Book/MainResults.lean`](Homogenization/Book/MainResults.lean),
  and the comparison theorem is comparator-checked (see [`Audit/`](Audit/)).

**Summary.** Across Chapters 1–5 there are ~100 numbered statement environments.
The large majority are `proved`; the `partial` and `not-formalized` entries
coincide exactly with the manuscript footnotes and with the divergences recorded
in [`formalization.yaml`](formalization.yaml). The only genuinely unformalized
*results* are a fractional Poincaré–Sobolev / Morrey proposition (which is removed
from the compiled manuscript) and two interpretive remarks; the remaining
`not-formalized`/`partial` entries are restricted exponent ranges or unused
definitional vocabulary.

---

## Chapter 1 — Function spaces

All declarations are in namespace `Homogenization.Book.Ch01`; files under
`Homogenization/Book/Ch01/`.

| Manuscript label | Statement (short) | Lean declaration | File | Status |
|---|---|---|---|---|
| `e.normalized.Lp.function.spaces` | Normalized average and `‖·‖_{L̲^p(U)}` | `normalizedAverage`, `normalizedLpNorm` | `Definitions.lean` | proved |
| `e.normalized.W1p.function.spaces` | Normalized Sobolev norm/seminorm | `normalizedW1pNorm`, `normalizedW1pSeminorm` | `Definitions.lean` | proved |
| `e.negative.Sobolev.norms.function.spaces` | Dual negative Sobolev seminorms `W̲^{-1,p'}` | `dualNegativeBesovSeminorm`/`dualNegativeBesovNorm` (Besov-level analogue only) | `Definitions.lean` | partial |
| `e.holder.norms.function.spaces` | Hölder seminorm `[·]_{C^{0,α}}` | — | — | not-formalized |
| `e.potential.solenoidal.spaces.function.spaces` | Potential/solenoidal spaces | `PotentialFieldOn`, `PotentialZeroTraceFieldOn`, `SolenoidalFieldOn`, `SolenoidalZeroNormalTraceFieldOn` | `Definitions.lean` | proved |
| `e.positive.Besov.def.function.spaces` | Positive-order triadic Besov seminorm/norm | `positiveBesovPartialNorm`, `positiveBesovNormTop`, `positiveBesovNormTwo`, `positiveBesovVectorNormTop` | `Definitions.lean` | proved |
| `e.negative.Besov.dual.def.function.spaces` | Dual negative-order Besov seminorms | `dualNegativeBesovSeminorm`, `dualNegativeBesovNorm` | `Definitions.lean` | proved |
| `e.negative.Besov.def.function.spaces` | Concrete circ negative-order Besov seminorm | `circNegativeBesovNorm`, `circNegativeBesovPartialNorm` | `Definitions.lean` | proved |
| `l.circ.dominates.dual.Besov.function.spaces` | Circ seminorm dominates dual negative Besov | `circDominatesMeanZeroDualBesov`, `circDominatesFullDualBesov` | `Theorems/CircDomination.lean` | proved |
| `l.dual.to.circ.Besov.loss.function.spaces` | Reverse comparison after exponent loss | `cubeBesovNegativeVectorSeminormTwo_le_halfDual_fiftyFive_inv_sq` | `Theorems/DualToCircLoss/FiniteLoss.lean` | partial |
| `l.Wsp.vs.Bspp.function.spaces` | Fractional Sobolev seminorm ≃ `B̲^s_{p,p}` | `fractionalSobolevVsBesovSeminorms` | `Theorems/FractionalSobolevVsBesov.lean` | proved |
| `p.fractional.Sobolev.and.Morrey.function.spaces` | Fractional Poincaré–Sobolev & Morrey | — (inside `\iffalse` block) | — | not-formalized |
| `p.CZ.cubes.function.spaces` | Calderón–Zygmund `W^{2,q}` (Dirichlet & Neumann) | `cubeNeumannW22Regularity`, `cubeDirichletH2RegularityExact`, … | `Theorems/CubeNeumannCZ.lean`, `Theorems/CubeDirichletH2.lean` | partial |
| `l.constant.coefficient.Dirichlet.Besov.function.spaces` | Fractional Dirichlet regularity, constant coeff | `constantCoefficientDirichletBesovFunctionSpaces` | `Theorems/CubeDirichletH2.lean` | proved |
| `l.Besov.positive.localize.function.spaces` | Localization of normalized positive Besov norm | `positiveBesovLocalize` | `Theorems/PositiveBesovLocalize.lean` | proved |
| `l.Besov.negative.localize.function.spaces` | Subadditivity of dual negative Besov norm | `negativeBesovLocalize`, `negativeBesovFullLocalize` | `Theorems/NegativeBesovLocalize.lean` | proved |
| `l.Besov.duality.function.spaces` | Cube-wise Besov pairing | `cubeBesovPairing_two_one_le_…`, `cubeBesovPairing_two_two_le_…` | `Theorems/BesovPairing.lean`, `Theorems/CircDomination.lean` | partial |
| `l.multiscale.Poincare.function.spaces` | Multiscale Poincaré from negative Besov control | `h1_fullVectorPoincare`, `h1_fluctuation_partialNormTop_two_le_…` | `Theorems/MultiscalePoincare.lean` | proved |
| `l.Besov.grad.to.function.function.spaces` | From ∇u to u in the Besov scale | `gradientToFunctionBesovScale_from_h1` | `Theorems/GradientToFunction.lean` | proved |
| `l.cutoff.product.Besov.function.spaces` | Cutoff/product estimate in positive Besov norm | `cutoffProductPositiveBesov_infinite_from_h1` | `Theorems/CutoffProduct.lean` | proved |
| `l.standard.radius.iteration.function.spaces` | Standard radius iteration | `standardRadiusIteration` | `Theorems/RadiusIteration.lean` | partial |

---

## Chapter 2 — Basic definitions

All "`…Theory`" packages are in namespace `Homogenization`; files under
`Homogenization/Book/Ch02/`.

| Manuscript label | Statement (short) | Lean declaration | File | Status |
|---|---|---|---|---|
| `l.response.functional.optimality.basic.definitions` | First variation / quadraticity of `J` | `responseFirstVariationTheory` | `Theorems/FirstVariation.lean` | proved |
| `l.basic.cg.identities.basic.definitions` | Basic variational identities | `responseBasicVariationalIdentitiesTheory` | `Theorems/BasicVariationalIdentities.lean` | proved |
| `l.symmetric.dirichlet.neumann.split.basic.definitions` | Symmetric `a`: Dirichlet/Neumann split | `responseSymmetricDirichletNeumannTheory` | `Theorems/SymmetricDirichletNeumann.lean` | proved |
| `l.cg.subadditivity.basic.definitions` | Subadditivity + scaling of `J` | `responseSubadditivityAndScalingTheory` | `Theorems/SubadditivityScaling.lean` | proved |
| `l.block.matrix.field.basic.definitions` | Block field factorization | `blockMatrixFieldAlgebraTheory` | `Theorems/BlockMatrixField.lean` | proved |
| `l.block.response.functional.basic.definitions` | Doubled response space `S(U;a)` | `doubledResponseTheory` | `Theorems/DoubledResponse.lean` | proved |
| `l.block.coarse.matrices.basic.definitions` | Coarse block matrices `A`, `A_*` | `blockCoarseMatrixTheory` | `Theorems/BlockCoarseMatrix.lean` | proved |
| `l.magic.identities.basic.definitions` | Adjoint formulas + "magic" identities (`σ_*≤σ`) | `responseMagicIdentitiesTheory` | `Theorems/MagicIdentities.lean` | proved |
| `l.cg.response.estimates.basic.definitions` | Linear-response & coarse-graining estimates | `responseCoarseGrainingEstimatesTheory` | `Theorems/CoarseGrainingEstimates.lean` | proved |
| `d.multiscale.ellipticity.basic.definitions` | Coarse-grained ellipticity constants `Λ_{s,q}`, `λ_{s,q}`, `Θ` | `LambdaSqFinite`, `lambdaSqFinite`, `LambdaSqInfinity`, `lambdaSqInfinity`, `ThetaRatio` | `Ch02/MultiscaleEllipticity.lean` | proved |
| `l.multiscale.ellipticity.basic.definitions` | Basic properties of ellipticity constants | `multiscaleEllipticityBasicTheory`, `…ChangeExponentTheory` | `Theorems/MultiscaleEllipticity/Public.lean` | proved |
| `d.multiscale.homogenization.error.basic.definitions` | Multiscale homogenization error `E` | `HomogenizationError` (+ `…Finite`, `…Infinity`, `…OnCube`) | `Theorems/HomogenizationError.lean` | proved |
| `l.multiscale.homogenization.error.basic.definitions` | Basic properties of `E` | `homogenizationErrorInfinityOneBasicTheory` (`(∞,1)` instance) | `Theorems/HomogenizationError/InfinityOne.lean` | partial |
| `l.mathcal.E.to.Lambdas.basic.definitions` | `E` controls coarse-grained ellipticity | (in the `(∞,1)` error chain) | `Theorems/HomogenizationError/EllipticityControl.lean` | partial |

---

## Chapter 3 — Deterministic theory

All declarations in namespace `Homogenization.Book.Ch03`; files under
`Homogenization/Book/Ch03/Theorems/`. **Every Chapter-3 statement is `proved`**
as an unconditional top-level theorem.

| Manuscript label | Statement (short) | Lean declaration | File | Status |
|---|---|---|---|---|
| `p.coarse.grained.Poincare.deterministic.theory` | Coarse-grained Poincaré | `coarsePoincareTheory` | `CoarsePoincare.lean` | proved |
| `p.coarse.grained.Caccioppoli.boundary.deterministic.theory` | Coarse Caccioppoli (boundary) | `coarseCaccioppoliTheory` (boundary conjunct) | `CoarseCaccioppoliDilationTransport.lean` | proved |
| `c.coarse.grained.Caccioppoli.interior.deterministic.theory` | Coarse Caccioppoli (interior) | `coarseCaccioppoliTheory` (interior conjunct) | `CoarseCaccioppoliDilationTransport.lean` | proved |
| `l.coarse.grained.flux.response.deterministic.theory` | Coarse-grained flux response | `coarseFluxResponseTheory` | `FluxResponse.lean` | proved |
| `p.coarse.grained.Poincare.RHS.deterministic.theory` | Coarse Poincaré with RHS | `coarsePoincareRHSTheory` (main conjunct) | `CoarsePoincareRHS.lean` | proved |
| `l.zero.Dirichlet.energy.RHS.deterministic.theory` | Zero-Dirichlet energy estimate | `coarsePoincareRHSTheory` (zero-Dirichlet conjunct) | `CoarsePoincareRHS.lean` | proved |
| `p.coarse.grained.Caccioppoli.RHS.deterministic.theory` | Coarse Caccioppoli with RHS | `coarseCaccioppoliRHSTheory` | `CoarseCaccioppoliRHS/Theory.lean` | proved |
| `p.weak.flux.RHS.deterministic.theory` | Weak flux estimate with RHS | `weakFluxRHSTheory` | `WeakFluxRHS.lean` | proved |
| `l.coarse.grained.flux.response.RHS.deterministic.theory` | Coarse flux response with RHS | `coarseFluxResponseRHSTheory` | `CoarseFluxResponseRHS.lean` | proved |
| `p.Dirichlet.energy.RHS.deterministic.theory` | Dirichlet energy with RHS | `energyConsequencesRHSTheory` (Dirichlet conjunct) | `EnergyRHS/Theory.lean` | proved |
| `p.Neumann.energy.RHS.deterministic.theory` | Mean-zero Neumann energy with RHS | `energyConsequencesRHSTheory` (Neumann conjunct) | `EnergyRHS/Theory.lean` | proved |
| `l.duality.from.flux.defect.deterministic.theory` | Duality: flux defect → solution comparison | `fluxDefectDualityTheory` | `Duality.lean` | proved |
| `p.general.coarse.graining.p2.deterministic.theory` | General `L²` coarse-graining (two-exponent) | `generalCoarseGrainingL2TwoExponentTheory` | `GeneralCoarseGrainingL2TwoExponent.lean` | proved |

---

## Chapter 4 — Stationary random fields and concentration

Probability declarations are in namespace `Homogenization.IndependentSums`;
homogenization-scale declarations in `Homogenization` / `Homogenization.Book.Ch04`.

| Manuscript label | Statement (short) | Lean declaration | File | Status |
|---|---|---|---|---|
| `a.stationarity.homogenization.scale` (P1) | Stationarity (ℤᵈ-translations) | `IsStationary` (alias `Ch04.StationaryLaw`) | `Probability/RandomField.lean` | proved |
| `a.unit.range.homogenization.scale` (P2) | Unit-range dependence | `IsUnitRangeDependent` (alias `Ch04.UnitRangeDependentLaw`) | `Probability/RandomField.lean` | proved |
| `a.isotropy.homogenization.scale` (P3) | Isotropy + adjoint symmetry | `IsIsotropicInLaw`, `IsAdjointInvariantInLaw` | `Probability/RandomField.lean` | partial |
| `l.scalarization.homogenization.scale` | Scalarization of annealed matrices | `Ch04.Internal.annealedScalarizationTheory_of_structuralLaw` (+ endpoints) | `Ch04/Theorems/Scalarization.lean` | proved |
| `l.local.block.observables.stationary.random.fields` | Locality of block observables | `exists_isLocalRandomVariable_ae_eq_coarseBlockMatrix_*` family | `Ch04/Theorems/CoarseObservables.lean`, `BlockResponseConcentration.lean` | partial |
| `l.local.derived.observables.stationary.random.fields` | Locality of derived (Mu, J) observables | `exists_isLocalRandomVariable_ae_eq_blockJObservable…`, `aemeasurable_*` family | `Ch04/Theorems/BlockResponseConcentration.lean`, `CoarseObservables.lean` | partial |
| `l.independence.separated.local.observables.stationary.random.fields` | Independence of separated local observables | `Ch04.iIndepFun_of_unitRangeDependentLaw_of_pairwise_separated` | `Ch04/Theorems/IndependenceDefinitions.lean` | proved |
| `l.coloring.triadic.partition.stationary.random.fields` | Coloring of a triadic partition | `Ch04.iIndepFun_descendantsAtScaleScaleColorClass_of_unitRangeDependentLaw` | `Ch04/Theorems/IndependenceDefinitions.lean` | partial |
| `d.big.O.Psi.stationary.random.fields` | `𝒪_Ψ` (weak-Orlicz) notation | `IndependentSums.IsBigO`/`IsBigOWith` (+ `AdmissiblePsi`) | `Probability/IndependentSums/WeakOrlicz.lean` | proved |
| `r.model.classes.stationary.random.fields` | Remark: model classes | — | — | not-formalized |
| `l.Psi.calculus.stationary.random.fields` | Calculus for admissible Ψ | `HasPsiGrowth`, `admissiblePsi_doubling`, `IsBigOWith.{of_le,mono_scale,const_mul,neg}`, … | `IndependentSums/PsiCalculus.lean`, `WeakOrlicz.lean` | proved |
| `l.moments.to.gamma.stationary.random.fields` | Moment growth → stretched-exp tails | `isBigO_gammaSigma_of_moment_growth` | `IndependentSums/GammaSigma/Basic.lean` | proved |
| `p.Gamma.sigma.calculus.stationary.random.fields` | Calculus of `𝒪_{Γ_σ}` | `isBigO_finset_sum_of_isBigO_gammaSigma`, … | `IndependentSums/GammaSigma/Operations.lean`, `Basic.lean` | proved |
| `r.Psi.sigma.growth.stationary.random.fields` | Remark: log-normal scale | — | — | not-formalized |
| `p.Rosenthal.stationary.random.fields` | Rosenthal's inequality | `integral_abs_centeredFinsetSum_pow_le_rosenthal` | `IndependentSums/Rosenthal/Endpoint.lean` | proved |
| `l.symmetrization.Rosenthal.stationary.random.fields` | Symmetrization reduction | `integral_abs_centeredFinsetSum_pow_le_integral_abs_symmetrizedFinsetSum_pow` | `IndependentSums/Rosenthal/Symmetrization.lean` | proved |
| `l.Bennett.stationary.random.fields` | Bennett inequality | `measureReal_absTailEvent_finset_sum_le_bennett_…` | `IndependentSums/Rosenthal/ScalarBennett.lean` | proved |
| `l.Bennett.beta.stationary.random.fields` | Properties of the Bennett function | `bennettBeta` (+ `monotoneOn_bennettBeta`, …) | `IndependentSums/Rosenthal/BennettFunction.lean` | proved |
| `c.Rosenthal.polynomial.corollaries.stationary.random.fields` | Polynomial-moment corollaries | `integral_abs_centeredFinsetSum_pow_rpow_inv_le_rosenthal_polynomial` | `IndependentSums/Rosenthal/Corollaries.lean` | proved |
| `p.Gamma.sigma.exp.regime.stationary.random.fields` | Concentration, exponential regime (σ≥1) | `isBigO_gammaSigma_finset_sum_…_of_one_lt` (+ σ=1 endpoint) | `IndependentSums/GammaSigmaExpRegime/FiniteSums.lean` | partial |
| `p.Psi.concentration.stationary.random.fields` | General concentration for indep. sums | `measureReal_upperTailEvent_finset_sum_le_…` | `IndependentSums/PsiConcentration/Concentration.lean` | partial |
| `c.Gamma.sigma.concentration.stationary.random.fields` | Concentration corollary, `Γ_σ` (σ<1) | `isBigO_gammaSigma_finset_sum_…_of_lt_one` | `IndependentSums/GammaSigmaConcentration/LargeRegime.lean` | partial |
| `l.Psi.sigma.admissibility.stationary.random.fields` | Log-normal admissibility | `admissiblePsi_psiSigma` | `IndependentSums/WeakOrlicz.lean` | proved |
| `c.Psi.sigma.concentration.stationary.random.fields` | Concentration corollary, `Ψ_σ` | `isBigO_psiSigma_finset_sum_…` | `IndependentSums/PsiSigma/Endpoint.lean` | proved |
| `p.local.partition.average.fluctuations.stationary.random.fields` | Fluctuation bounds for partition averages | `Ch04.isBigO_gammaSigma_centeredDescendantAverage_…`, `…psiSigma…` | `Ch04/Theorems/PartitionAverageFluctuations.lean` | proved |
| `c.low.moment.partition.average.fluctuations.stationary.random.fields` | Finite-moment fluctuation | `Ch04.integral_abs_centeredDescendantAverage_le_…` | `Ch04/Theorems/PartitionAverageMoments/Theory.lean` | proved |
| `c.J.partition.average.fluctuations.stationary.random.fields` | Fluctuations of partition averages of `J` | (subsumed by `l.concentration.of.J` + low-moment corollary) | — | not-formalized |
| `p.annealed.subadditivity.stationary.random.fields` | Annealed subadditivity of `J`/matrices | `Ch04.LawCarrier.blockMatLoewnerLE_annealedBlockMatrixAtScale` (+ consequences) | `Ch04/Theorems/AnnealedSubadditivity/LawCarrierAnnealedMatrix.lean` | proved |
| `c.annealed.matrices.monotone.stationary.random.fields` | Monotonicity of annealed matrices | `Ch04.scalar_chain_of_primitive_block_mono` (+ matrix forms) | `Ch04/Theorems/AnnealedSubadditivity/LawCarrierAnnealedMatrix.lean` | proved |
| `l.concentration.of.J` | Concentration of normalized block responses | `Ch04.concentration_of_blockJObservableCubeSetBlockVec` | `Ch04/Theorems/BlockResponseConcentration.lean` | proved |

---

## Chapter 5 — The homogenization scale

Declarations in namespace `Homogenization.Ch05` (sectioned `Section51`–`Section57`);
files under `Homogenization/Book/Ch05/Theorems/`. Main results re-exported in
`Homogenization/Book/MainResults.lean`. **Every Chapter-5 statement is `proved`.**

| Manuscript label | Statement (short) | Lean declaration | File | Status |
|---|---|---|---|---|
| `a.cg.ellipticity.homogenization.scale` (P4) | Quantitative coarse-grained ellipticity | `Ch05.QuantitativeCoarseGrainedEllipticity` | `Ch05/Definitions.lean` | proved |
| **`t.annealed.convergence`** | **Convergence of the annealed contrast** | `Ch05.Section51.annealedConvergence_homogenizationScale`; re-export `Book.annealedConvergence_uniformEllipticity` | `Section51/AnnealedConvergence.lean`; `MainResults.lean` | proved |
| `a.cg.ellipticity.Gamma.sigma` (P5) | Stretched-exponential (`Γ_σ`) unit-scale ellipticity | `Ch05.Section57.GammaSigmaCoarseGrainedEllipticity`/`…NoXi`/`GammaInfinity…` | `Section57/QuenchedGammaEllipticity.lean` | proved |
| **`t.quenched.homogenization.comparison`** | **Quenched homogenization above the minimal scale** | `Ch05.homogenization_quenched_homogenization_comparison`; re-export `Book.homogenizationComparison_uniformEllipticity` | `Theorems/Public.lean`; `MainResults.lean` | proved |
| `l.scalar.preliminaries.homogenization.scale` | Basic scalar consequences of subadditivity | `Ch05.Section52.scalarPreliminaries_homogenizationScale` | `Section52/ScalarPreliminaries.lean` | proved |
| `l.centered.responses.homogenization.scale` | Centered primal/adjoint responses | `Ch05.Section52.centeredResponses_homogenizationScale` | `Section52/CenteredResponses.lean` | proved |
| `l.multiscale.ellipticity.moments.homogenization.scale` | Moment bounds for ellipticity constants | `Ch05.Section52.LambdaPositiveExcessMomentAtScale_le_…`, `…lambdaInv…` | `Section52/MomentBounds.lean` | proved |
| `l.J.upper.bound.weak.norms.homogenization.scale` | `J` upper bound by weak norms | `Ch05.Section53.JUpperBoundWeakNorms_homogenizationScale` | `Section53/JUpperBoundWeakNorms.lean` | proved |
| `l.weak.norms.maximizer.homogenization.scale` | Weak-norm bounds for the maximizer | `Ch05.Section53.weakNormsMaximizer_homogenizationScale` | `Section53/WeakNormsMaximizer/AssemblyFinal.lean` | proved |
| `l.J.upper.bound.coarse.fluctuations.homogenization.scale` | Centered response ≤ coarse fluctuations | `Ch05.Section53.JUpperBoundCoarseFluctuations_homogenizationScale` | `Section53/JUpperBoundCoarseFluctuations/FinalRHS.lean` | proved |
| `l.pigeonhole.homogenization.scale` | Pigeonhole lemma | `Ch05.Section54.pigeonhole_homogenizationScale` | `Section54/Pigeonhole.lean` | proved |
| `l.good.scale.parameter.bounds.homogenization.scale` | Good-scale parameter bounds | `Ch05.Section54.goodScaleParameterBounds_homogenizationScale` | `Section54/GoodScale/Assembly.lean` | proved |
| `l.variance.bound.good.scale.homogenization.scale` | Variance bound at a near-stationary scale | `Ch05.Section54.varianceBoundGoodScale_homogenizationScale` | `Section54/VarianceBoundGoodScale.lean` | proved |
| `p.one.step.contraction.homogenization.scale` | One-step contraction of the annealed flow | `Ch05.Section54.oneStepContraction_homogenizationScale` | `Section54/OneStepContraction/Assembly.lean` | proved |
| `c.shifted.widetilde.Theta.bound.homogenization.scale` | Shifted localization of the contrast | `Ch05.Section55.shiftedWidetildeThetaAtScale_le_…` | `Section55/ShiftedWidetildeTheta.lean` | proved |
| `c.shifted.one.step.contraction.homogenization.scale` | Shifted one-step contraction | `Ch05.Section55.shiftedOneStepContraction_homogenizationScale` | `Section55/ShiftedOneStepContraction.lean` | proved |
| `l.one.step.annealed.improvement.homogenization.scale` | One improvement step | `Ch05.Section55.oneStepAnnealedImprovement_homogenizationScale` | `Section55/AnnealedImprovement.lean` | proved |
| `p.annealed.convergence.homogenization.scale` | Annealed perturbative entry & convergence | `Ch05.Section55.annealedPerturbativeEntry_homogenizationScale` | `Section55/AnnealedConvergence.lean` | proved |
| `l.small.contrast.Jbound` | Upper bound for `J` in small contrast | `Ch05.Section56.smallContrastJBound_homogenizationScale` | `Section56/SmallContrastJBound/Estimate.lean` | proved |
| `l.variance.estimate.quadratic` | Variance estimate with quadratic error | `Ch05.Section56.fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_…` | `Section56/VarianceEstimateQuadratic/NormalizedStatements.lean` | proved |
| `l.small.contrast.assembly` | Assembled small-contrast bound | `Ch05.Section56.smallContrastAssembly_homogenizationScale` | `Section56/SmallContrastAssembly/FinalAssembly.lean` | proved |
| `p.small.contrast.algebraic.decay.homogenization.scale` | Algebraic decay in small contrast | `Ch05.Section56.smallContrastAlgebraicDecay_homogenizationScale` | `Section56/SmallContrastAlgebraicDecay/Final.lean` | proved |
| `c.first.quenched.estimate` | First quenched estimate | `Ch05.Section57.firstQuenchedEstimate_limitNormalized` (+ variants) | `Section57/FirstQuenchedEstimate.lean` | proved |
| `t.homogenization.quenched` | Quenched minimal scale | `Ch05.homogenization_quenched_minimal_scale`; internal `Section57.exists_quenchedLocalizedEstimate_…` | `Theorems/Public.lean`; `Section57/HomogenizationQuenched.lean`, `UniformHomogenizationQuenched.lean` | proved |
| `c.quenched.mathcalE.above.minimal.scale` | Finite-`q` homogenization error above the scale | `Ch05.Section57.exists_homogenizationErrorOnOriginCube_…` | `Section57/HomogenizationErrorQuenched.lean` | proved |

---

## Notes on `partial` and `not-formalized` entries

These coincide with the manuscript footnotes and with `formalization.yaml`.

- **Ch. 1, `p.CZ.cubes` (partial):** the manuscript states `q∈(1,∞)`; Lean
  formalizes the `q=2` (`H²`/`W^{2,2}`) Dirichlet and Neumann estimates (both
  endpoints present).
- **Ch. 1, `l.Besov.duality` (partial):** Lean formalizes `p=2` (the `(2,1)` and
  `(2,2)` pairings), the only cases used downstream.
- **Ch. 1, `l.dual.to.circ.Besov.loss` (partial):** Lean formalizes the half-case
  `t=s/2` at `p=q=2`; the general-`t` and vector-`ℓ²` forms are not separate.
- **Ch. 1, `l.standard.radius.iteration` (partial):** Lean proves the normalized
  `[1/3,1]` form (used by the coarse Caccioppoli argument); the general interval
  follows by scaling.
- **Ch. 1, `e.negative.Sobolev.norms` (partial) / `e.holder.norms` (not-formalized):**
  these are definitional vocabulary (`W^{-1,p'}` Sobolev, Hölder seminorms) that no
  formalized result consumes; only the Besov-scale duals and the `q=2`/`s=1` cases
  are formalized.
- **Ch. 1, `p.fractional.Sobolev.and.Morrey` (not-formalized):** the only genuinely
  unformalized *result*; it lives inside the manuscript's `\iffalse…\fi` block and
  does not appear in the compiled PDF.
- **Ch. 2, homogenization-error properties (partial):** `E` is defined for the
  full `(p,q)∈{finite,∞}²` lattice, but its monotonicity / one-cube properties
  and the `E ⇒ Λ/λ` control are exposed only at the `(p=∞, q=1)` instance that
  Chapter 3 consumes.
- **Ch. 2 domains:** the deterministic domain interface is restricted to bounded
  open **convex** cubes rather than general Lipschitz domains (manuscript
  footnote).
- **Ch. 4, `a.isotropy` (P3) (partial):** isotropy is formalized for **signed
  permutation matrices** rather than the full rotation group.
- **Ch. 4, concentration props (partial):** the manuscript's full `Γ_σ`
  concentration is split by regime (σ≥1 exponential vs σ<1 heavy-tail), and some
  locality lemmas are realized as families of consequences rather than a single
  named theorem; the constants match the (updated) manuscript.
- **Ch. 4, two remarks + `c.J.partition.average.fluctuations` (not-formalized):**
  the two `\remark`s carry no Lean target; the `J`-specialized partition-average
  corollary's content is subsumed by `l.concentration.of.J` plus the general
  low-moment corollary.
- **Ch. 5 (`ξ` integer):** the moment exponent `ξ` in (P4)/(P5) is taken to be an
  integer `> 2d` (manuscript footnote); every Chapter-5 statement is otherwise
  `proved` as stated.
