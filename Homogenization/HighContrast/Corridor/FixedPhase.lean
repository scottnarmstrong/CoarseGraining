import Homogenization.HighContrast.Corridor.FixedPhase.Recombination
import Homogenization.HighContrast.Corridor.FixedPhase.EfronSteinAE
import Homogenization.HighContrast.Corridor.FixedPhase.Resample
import Homogenization.HighContrast.Corridor.FixedPhase.CorePatchEnergy
import Homogenization.HighContrast.Corridor.FixedPhase.MeasurableObservable
import Homogenization.HighContrast.Corridor.FixedPhase.ClampedObservable
import Homogenization.HighContrast.Corridor.FixedPhase.EfronSteinPhase

/-!
# Fixed-phase variance (Proposition 4.3), Efron–Stein preparation

Facade re-exporting the fixed-phase components:

* `FixedPhase.Recombination` — the `G`-factorization: reconstructing the
  fixed-phase observable from the independent per-core restrictions
  (`corePatch`, `phaseObservable_corePatch_restrict_eq`).
* `FixedPhase.EfronSteinAE` — the a.e.-measurable Efron–Stein transfer wrapper
  (`efronStein_transfer_ae`) and the update-resample pushforward
  (`map_update_prod_pi`).
* `FixedPhase.Resample` — the deterministic one-core resampling stability bound
  (`abs_phaseObservable_resample_sub_le`).
* `FixedPhase.CorePatchEnergy` — the per-core energy split and its product
  measurability (`phaseSplitEnergy`, `measurable_phaseSplitEnergy`).
* `FixedPhase.MeasurableObservable` — the product-measurable raw observable and
  its five-link a.e. identity (`rawPhaseObservable`, `rawPhaseObservable_restrict_eq_of_field`).
* `FixedPhase.ClampedObservable` — the globally bounded clamped observable
  (`clampedPhaseObservable`, `abs_clampedPhaseObservable_le`).
* `FixedPhase.EfronSteinPhase` — the Efron–Stein bound in the `patchCore` form
  (`efronStein_phaseObservable`).
-/
