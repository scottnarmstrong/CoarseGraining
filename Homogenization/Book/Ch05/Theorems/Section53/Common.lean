module

public import Homogenization.Book.Ch05.Definitions
public import Homogenization.Book.Ch01.Theorems.CutoffProduct
public import Homogenization.Book.Ch02.Theorems.BasicVariationalIdentities
public import Homogenization.Book.Ch02.Theorems.HomogenizationError.ResponseBounds
public import Homogenization.Book.Ch02.Theorems.MatrixPositivity
public import Homogenization.Book.Ch02.Theorems.SolutionIntegrability
public import Homogenization.Book.Ch02.Theorems.SubadditivityScaling
public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.H1Transport
public import Homogenization.Book.Ch04.CoeffFamily
public import Homogenization.Book.Ch04.Theorems.CanonicalSolutions
public import Homogenization.Book.Ch04.Theorems.StationaryExpectations
public import Homogenization.Deterministic.CoarseCaccioppoliCutoffProduct
public import Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicScalarControls
public import Homogenization.PDE.EnergyIdentities
public import Homogenization.Probability.LocalEllipticitySlices.SymmetricL2
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.QuantCutoffLowerH1
public import Homogenization.Sobolev.PotentialSolenoidalL2Recovery

@[expose] public section

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
