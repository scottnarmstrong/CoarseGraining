module

public import Homogenization.Book.Ch02.Theorems.Existence
public import Homogenization.Book.Ch02.Theorems.SolutionIntegrability
public import Homogenization.Book.Ch02.Theorems.FirstVariation
public import Homogenization.Book.Ch02.Theorems.GradientUniqueness
public import Homogenization.Book.Ch02.Theorems.GradientLinearity
public import Homogenization.Book.Ch02.Theorems.Quadraticity
public import Homogenization.Book.Ch02.Theorems.MatrixExtraction
public import Homogenization.Book.Ch02.Theorems.MatrixExtractionProofs
public import Homogenization.Book.Ch02.Theorems.MatrixPositivity
public import Homogenization.Book.Ch02.Theorems.BasicVariationalIdentities
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import Homogenization.Book.Ch02.Theorems.SubadditivityScaling
public import Homogenization.Book.Ch02.Theorems.BlockMatrixField
public import Homogenization.Book.Ch02.Theorems.DoubledMu
public import Homogenization.Book.Ch02.Theorems.DoubledResponse
public import Homogenization.Book.Ch02.Theorems.BlockCoarseMatrix
public import Homogenization.Book.Ch02.Theorems.DeterministicIdentities
public import Homogenization.Book.Ch02.Theorems.MagicIdentities
public import Homogenization.Book.Ch02.Theorems.CoarseGrainingEstimates
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity
public import Homogenization.Book.Ch02.Theorems.HomogenizationError
public import Homogenization.Book.Ch02.Theorems.WrapAround
public import Homogenization.Book.Ch02.Theorems.Dilation

/-!
Public Chapter 2 theorem surface.

The `*Definitions.lean` files in this directory contain proposition-valued
theorem packages and their small accessor APIs.  The companion theorem files
import the internal proof bridges and prove those packages for the public
`Domain`/`CoeffOn` interface.
-/

@[expose] public section
