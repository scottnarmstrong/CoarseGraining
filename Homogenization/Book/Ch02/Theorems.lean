import Homogenization.Book.Ch02.Theorems.Existence
import Homogenization.Book.Ch02.Theorems.SolutionIntegrability
import Homogenization.Book.Ch02.Theorems.FirstVariation
import Homogenization.Book.Ch02.Theorems.GradientUniqueness
import Homogenization.Book.Ch02.Theorems.GradientLinearity
import Homogenization.Book.Ch02.Theorems.Quadraticity
import Homogenization.Book.Ch02.Theorems.MatrixExtraction
import Homogenization.Book.Ch02.Theorems.MatrixExtractionProofs
import Homogenization.Book.Ch02.Theorems.MatrixPositivity
import Homogenization.Book.Ch02.Theorems.BasicVariationalIdentities
import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
import Homogenization.Book.Ch02.Theorems.SubadditivityScaling
import Homogenization.Book.Ch02.Theorems.BlockMatrixField
import Homogenization.Book.Ch02.Theorems.DoubledMu
import Homogenization.Book.Ch02.Theorems.DoubledResponse
import Homogenization.Book.Ch02.Theorems.BlockCoarseMatrix
import Homogenization.Book.Ch02.Theorems.DeterministicIdentities
import Homogenization.Book.Ch02.Theorems.MagicIdentities
import Homogenization.Book.Ch02.Theorems.CoarseGrainingEstimates
import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity
import Homogenization.Book.Ch02.Theorems.HomogenizationError
import Homogenization.Book.Ch02.Theorems.WrapAround
import Homogenization.Book.Ch02.Theorems.Dilation

/-!
Public Chapter 2 theorem surface.

The `*Definitions.lean` files in this directory contain proposition-valued
theorem packages and their small accessor APIs.  The companion theorem files
import the internal proof bridges and prove those packages for the public
`Domain`/`CoeffOn` interface.
-/
