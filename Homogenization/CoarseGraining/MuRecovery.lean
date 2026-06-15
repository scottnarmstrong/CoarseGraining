import Homogenization.CoarseGraining.MuRecovery.Setup
import Homogenization.CoarseGraining.MuRecovery.CorrectionSpaceBasic
import Homogenization.CoarseGraining.MuRecovery.CorrectionSpaceSolenoidal
import Homogenization.CoarseGraining.MuRecovery.CorrectionSpaceEnergy
import Homogenization.CoarseGraining.MuRecovery.RecoveryPackages

/-!
# Mu recovery (aggregate re-export)

Previously a 2111-line monolithic module whose MuCorrectionSpaceRecoveryData
namespace alone spanned ~1560 lines; now split along namespace / theme
boundaries into the five files imported above. Shim for backward
compatibility.
-/
