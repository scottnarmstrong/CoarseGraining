import Homogenization.HighContrast.Coupled.LocalEnergy
import Homogenization.HighContrast.Coupled.Stampacchia
import Homogenization.HighContrast.Corridor.Geometry
import Homogenization.HighContrast.Corridor.PhaseComparison
import Homogenization.HighContrast.Corridor.FixedPhase
import Homogenization.HighContrast.Corridor.FixedPhase.VarianceFinal
import Homogenization.HighContrast.Variance.BlockVarianceBound
import Homogenization.HighContrast.EntryScale
import Homogenization.HighContrast.EntryScale.EntryScale
import Homogenization.HighContrast.EntryScale.FinalAssembly.P4Uniform
import Homogenization.HighContrast.Scale.Final

/-!
# High-contrast homogenization — theory root

This is the theory root for the high-moment paper's formalization
(Armstrong–Kuusi–Loher, in preparation).  It aggregates the two analytic pillars
of the development:

* **Block-variance decay** (`t.block.variance`).  The coupled-corridor and
  Stampacchia machinery (`Coupled`, `Corridor`), the fixed-phase variance chain
  (`Corridor.FixedPhase`), and the final block-variance bound
  `Homogenization.integral_fullBlockNormalizedFluctuation_le`
  (`Variance.BlockVarianceBound`) establishing the second-moment envelope for the
  normalized full-block fluctuation.

* **Homogenization scale.**  The entry-scale assembly (`EntryScale`) together with
  the `Scale` bridge, which turns a `ThetaEllipticLaw` into a uniform
  homogenization-scale contrast decay.  The headline theorem is

  `Homogenization.homogenizationScale_polynomial_of_unitRange`
  (`Scale.Final`):

  for every dimension `d ≥ 3` there are dimensional constants
  `Cscale, Ctriadic, α > 0` such that every `Θ`-elliptic probability law
  (`Θ ≥ 1`) contracts its ellipticity contrast to `1` from an entry scale
  `N₀ = O(log(2 + Θ))`, with physical entry scale polynomial in `2 + Θ`.
-/
