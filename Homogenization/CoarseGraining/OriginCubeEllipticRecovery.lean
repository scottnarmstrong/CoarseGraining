module

public import Homogenization.CoarseGraining.OriginCubeEllipticRecovery.Setup
public import Homogenization.CoarseGraining.OriginCubeEllipticRecovery.Existence
public import Homogenization.CoarseGraining.OriginCubeEllipticRecovery.QuadraticMu
public import Homogenization.CoarseGraining.OriginCubeEllipticRecovery.Translate
public import Homogenization.CoarseGraining.OriginCubeEllipticRecovery.MuGeVecDot
public import Homogenization.CoarseGraining.OriginCubeEllipticRecovery.DeterministicCoarseData
public import Homogenization.CoarseGraining.OriginCubeEllipticRecovery.Subadditivity

/-!
# Origin-cube elliptic recovery (aggregate re-export)

Previously a 2296-line monolithic module; now split along thematic boundaries
into the files imported above. This shim re-exports everything so
existing consumers keep working unchanged.
-/

@[expose] public section
