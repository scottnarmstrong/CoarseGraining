import Homogenization.Book.Ch05.Definitions
import Homogenization.Book.Ch01.Theorems.CutoffProduct
import Homogenization.Book.Ch02.Theorems.BasicVariationalIdentities
import Homogenization.Book.Ch02.Theorems.HomogenizationError.ResponseBounds
import Homogenization.Book.Ch02.Theorems.MatrixPositivity
import Homogenization.Book.Ch02.Theorems.SolutionIntegrability
import Homogenization.Book.Ch02.Theorems.SubadditivityScaling
import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.H1Transport
import Homogenization.Book.Ch04.CoeffFamily
import Homogenization.Book.Ch04.Theorems.CanonicalSolutions
import Homogenization.Book.Ch04.Theorems.StationaryExpectations
import Homogenization.Deterministic.CoarseCaccioppoliCutoffProduct
import Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicScalarControls
import Homogenization.PDE.EnergyIdentities
import Homogenization.Probability.LocalEllipticitySlices.SymmetricL2
import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.QuantCutoffLowerH1
import Homogenization.Sobolev.PotentialSolenoidalL2Recovery

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53

/-!
# Section 5.3 common imports

Shared base context for the split Section 5.3 files.  The mathematical content
lives in the three manuscript-lemma modules and their proof subdirectories.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

end Section53
end Ch05
end Book
end Homogenization
