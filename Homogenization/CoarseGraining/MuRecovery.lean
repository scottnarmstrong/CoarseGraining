module

public import Homogenization.CoarseGraining.MuRecovery.Setup
public import Homogenization.CoarseGraining.MuRecovery.CorrectionSpaceBasic
public import Homogenization.CoarseGraining.MuRecovery.CorrectionSpaceSolenoidal
public import Homogenization.CoarseGraining.MuRecovery.CorrectionSpaceEnergy
public import Homogenization.CoarseGraining.MuRecovery.RecoveryPackages

/-!
# Mu recovery (aggregate re-export)

Previously a 2111-line monolithic module whose MuCorrectionSpaceRecoveryData
namespace alone spanned ~1560 lines; now split along namespace / theme
boundaries into the five files imported above. Shim for backward
compatibility.
-/

@[expose] public section
