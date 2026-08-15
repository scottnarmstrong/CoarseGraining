import Homogenization.HighContrast.EntryScale.BadEventResponse
import Homogenization.HighContrast.EntryScale.FinalAssembly
import Homogenization.HighContrast.EntryScale.LowerEdgeComparison
import Homogenization.HighContrast.EntryScale.LowerEdgeKernel
import Homogenization.HighContrast.EntryScale.LocalTailTransport
import Homogenization.HighContrast.EntryScale.RawHighContrastEnergy
import Homogenization.HighContrast.EntryScale.RawHighContrastWeakNorm
import Homogenization.HighContrast.EntryScale.Section52Index
import Homogenization.HighContrast.EntryScale.VarianceUpgrade

/-!
# High-moment entry-scale assembly

Aggregator for the entry-scale (homogenization-scale) development following
the high-moment paper (Armstrong–Kuusi–Loher, to appear).
-/
