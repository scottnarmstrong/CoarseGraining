import Homogenization.Book.Ch05.Theorems.Public
import Homogenization.Book.MainResults
import Homogenization.HighContrast.Scale.Final

/-!
# Axiom audit

Machine-checked record of the axioms that the public headline theorems depend on.

This development contains no `sorry` and declares no custom `axiom`, so every
public theorem reduces to mathlib's three standard foundational axioms:
`propext`, `Classical.choice`, and `Quot.sound`.  Building this file prints
those dependencies for inspection (see CI logs).
-/

#print axioms Homogenization.Book.Ch05.homogenization_quenched_minimal_scale
#print axioms Homogenization.Book.Ch05.homogenization_quenched_homogenization_comparison

-- The uniformly-elliptic headline theorems exposed in `MainResults.lean`.
#print axioms Homogenization.Book.MainResults.annealedConvergence_uniformEllipticity
#print axioms Homogenization.Book.MainResults.homogenizationComparison_uniformEllipticity

-- The polynomial homogenization length scale theorem (d > 2, uniform
-- ellipticity), from Armstrong--Kuusi--Loher, *Homogenization at a polynomial
-- scale in high contrast* (to appear).
#print axioms Homogenization.homogenizationScale_polynomial_of_unitRange
