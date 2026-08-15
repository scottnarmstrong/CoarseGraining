import Homogenization.HighContrast.Corridor.PhaseComparison.GridCoverage
import Homogenization.HighContrast.Corridor.PhaseComparison.Measurability
import Homogenization.HighContrast.Corridor.PhaseComparison.Stability
import Homogenization.HighContrast.Corridor.PhaseComparison.Averaging

/-!
# Phase comparison (Prop 4.4, discrete-grid variant): facade

Formalization of Proposition `p.phase.comparison` of the high-moment paper
(Armstrong–Kuusi–Loher, to appear), §4.4, with the continuum `σ`-average
over `[0, ℓ)^d` replaced by the finite uniform grid `gridPhase ℓ N j`,
`j : Fin d → Fin N`.

* `sum_indicator_gridPhase_corridor_le` — grid coverage count
  (`Corridor/PhaseComparison/GridCoverage`).
* `aestronglyMeasurable_phaseObservable` — per-phase a.e.-strong
  measurability (`Corridor/PhaseComparison/Measurability`).
* `abs_phaseObservable_sub_le` — per-phase stability
  (`Corridor/PhaseComparison/Stability`).
* `exists_gridPhase_meanSq_le` — grid averaging + choice
  (`Corridor/PhaseComparison/Averaging`).

This facade re-exposes the full API via the split modules.
-/

namespace Homogenization

end Homogenization
