/-
Copyright (c) 2026. All rights reserved.
-/
import Homogenization.Probability.EfronStein.TwoPoint
import Homogenization.Probability.EfronStein.ProdDecomp
import Homogenization.Probability.EfronStein.Fin

/-!
# Efron–Stein inequality on finite products

Facade module gathering the bounded-observable Efron–Stein inequality on a finite
product probability space.  The public entry point is

* `Homogenization.efronStein_pi`: for a bounded measurable `F` on `∀ i, Ω i`
  with independent coordinates `μ i`,
  `Var[F; Measure.pi μ] ≤ ½ ∑ i, ∫ x ∫ y (F (update x i y) − F x)² dμᵢ dπ`.

Supporting public lemmas:

* `Homogenization.variance_eq_half_integral_sub_sq` — two-point variance identity;
* `Homogenization.variance_prod_eq` — two-factor (law-of-total-variance) split;
* `Homogenization.efronStein_fin` — the `Fin n` version proved by induction.
-/
