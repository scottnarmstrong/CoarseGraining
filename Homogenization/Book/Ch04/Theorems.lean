import Homogenization.Book.Ch04.Definitions
import Homogenization.Book.Ch04.Theorems.CanonicalAverages
import Homogenization.Book.Ch04.Theorems.CanonicalSolutions
import Homogenization.Book.Ch04.Theorems.ColorClassConcentration
import Homogenization.Book.Ch04.Theorems.CoarseObservables
import Homogenization.Book.Ch04.Theorems.Concentration
import Homogenization.Book.Ch04.Theorems.DescendantAverages
import Homogenization.Book.Ch04.Theorems.DilationLaw
import Homogenization.Book.Ch04.Theorems.Expectations
import Homogenization.Book.Ch04.Theorems.IndependenceDefinitions
import Homogenization.Book.Ch04.Theorems.LocalCoefficient
import Homogenization.Book.Ch04.Theorems.Mu
import Homogenization.Book.Ch04.Theorems.PartitionAverageFluctuations
import Homogenization.Book.Ch04.Theorems.PartitionAverageMoments
import Homogenization.Book.Ch04.Theorems.PartitionAverages
import Homogenization.Book.Ch04.Theorems.PartitionAveragesDefinitions
import Homogenization.Book.Ch04.Theorems.StationaryExpectations
import Homogenization.Book.Ch04.Theorems.BlockExpectations
import Homogenization.Book.Ch04.Theorems.BlockResponseConcentration
import Homogenization.Book.Ch04.Theorems.ScalarizationDefinitions
import Homogenization.Book.Ch04.Theorems.Scalarization
import Homogenization.Book.Ch04.Theorems.AnnealedSubadditivity
import Homogenization.Book.Ch04.Theorems.WidetildeTheta
import Homogenization.Book.Ch04.Theorems.MomentFactorBounds

/-!
# Chapter 4 theorem surface

This aggregate imports the curated public theorem endpoints for Chapter 4.

The public policy is direct theorem statements over `LawCarrier`,
`StructuralLaw`, local observables, and ordinary analytic hypotheses.  Callers
should not need route-specific wrapper structures.  Scalarization witnesses,
primitive route data, and proof-only bound packages remain in `Internal`
namespaces or private declarations.

The exported theorem families cover local coefficient observables, expectations,
independence and color-class concentration, partition-average fluctuations and
moments, scalarized annealed matrices, annealed subadditivity, moment-factor
comparisons, canonical averages, canonical solution measurability, and
scalar-response weak-norm measurability.
-/
