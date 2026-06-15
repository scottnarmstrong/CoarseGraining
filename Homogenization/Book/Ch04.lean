import Homogenization.Book.Ch04.Definitions
import Homogenization.Book.Ch04.Theorems

/-!
# Chapter 4

Chapter 4 exposes the probability-facing law, observable, annealed-object, and
theorem API used by later chapters.

The public surface is organized around `CoeffLaw`, `LawCarrier`, structural law
hypotheses, local observables, law-relative measurability promotion, the
dependent coefficient-family bridge, annealed response quantities, and direct
theorem endpoints for concentration, partition averages, scalarization,
subadditivity, moment bounds, canonical averages, and canonical scalar-response
measurability.

Route-specific witnesses and proof packages live under `Internal` namespaces or
inside private declarations.  Downstream chapters should consume the direct
`LawCarrier` and `StructuralLaw` endpoints exported here.
-/
