module

public import Homogenization.CoarseGraining.BlockResponse.Perturbation.Integrand
public import Homogenization.CoarseGraining.BlockResponse.Perturbation.PairHalfScalar
public import Homogenization.CoarseGraining.BlockResponse.Perturbation.VolumeAverage
public import Homogenization.CoarseGraining.BlockResponse.Perturbation.BlockEnergyFirstVariation
public import Homogenization.CoarseGraining.BlockResponse.Perturbation.ResponseJMuAdjoint

/-!
# BlockResponse perturbation, first-variation, and witness identities
(aggregate re-export)

Previously a 2169-line monolithic module; now split along thematic
boundaries into the five files imported above. Shim for backward compatibility.
-/

@[expose] public section
