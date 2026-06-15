import Homogenization.Book.Ch04.Internal.FixedCompetitorEnergyMeasurability.Measurability
import Homogenization.Book.Ch04.Internal.FixedCompetitorEnergyMeasurability.LipschitzBounds
import Homogenization.Book.Ch04.Internal.FixedCompetitorEnergyMeasurability.Integrals
import Homogenization.Book.Ch04.Internal.FixedCompetitorEnergyMeasurability.BlockEnergyAverage
import Homogenization.Book.Ch04.Internal.FixedCompetitorEnergyMeasurability.MuObservable

/-!
# Audit tag (Ch4 rebuild contract `CH04_REBUILD_SURFACE_2026-05-16.md`)

Pure-import umbrella for the five-file `FixedCompetitorEnergyMeasurability`
chain.

**Internal claim of the chain (read top-down):** lift `LocalSigma` scalar
atoms (`Measurability`) → fixed-coefficient Borel maps on `HilbertMat`
(`LipschitzBounds`) → quantitative-slice integral algebra (`Integrals`) →
measurable block-energy averages (`BlockEnergyAverage`) → measurability of
the `Mu` candidate as a coefficient-field functional (`MuObservable`).

**Consumed by:** `Internal/AEESliceAssembly/{BlockEnergyAverage,
MuFamily}.lean`, then `Theorems/Mu.lean :: aemeasurable_Mu_cubeSet`.

If a sixth file becomes necessary in this chain, that is the signal to
refactor rather than extend, per the rebuild contract.
-/
