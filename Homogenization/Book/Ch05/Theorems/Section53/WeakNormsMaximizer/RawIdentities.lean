import Homogenization.Book.Ch05.Theorems.Section53.WeakNormsMaximizer.Basic
import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.CanonicalFields

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace WeakNormsMaximizer

/-!
# Raw identities for scalar-response weak norms

These deterministic identities connect the Ch4 scalar-response weak-norm
objects used by the first Section 5.3 lemma to the raw Chapter 2 canonical
maximizer fields used in the second lemma proof.
-/

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

theorem canonicalScalarResponseGradientWeakNormCubeSet_eq_raw
    {d : ℕ} [NeZero d] (a : CoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (s : ℝ) (p q p0 : Vec d) :
    Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a =
      cubeBesovNegativeVectorSeminorm Q s
        (JUpperBoundWeakNorms.canonicalMaximizerGradientDefectOnCube Q
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
          p q p0) := by
  unfold Ch04.canonicalScalarResponseGradientWeakNormCubeSet
    cubeBesovNegativeVectorSeminorm
  apply congrArg sSup
  ext x
  constructor
  · rintro ⟨N, rfl⟩
    exact ⟨N,
      JUpperBoundWeakNorms.cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerGradientDefectOnDependentFamily_eq_ch04
        a ha Q s N p q p0⟩
  · rintro ⟨N, rfl⟩
    exact ⟨N,
      (JUpperBoundWeakNorms.cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerGradientDefectOnDependentFamily_eq_ch04
        a ha Q s N p q p0).symm⟩

theorem canonicalScalarResponseFluxWeakNormCubeSet_eq_raw
    {d : ℕ} [NeZero d] (a : CoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (s : ℝ) (p q q0 : Vec d) :
    Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q s p q q0 a =
      cubeBesovNegativeVectorSeminorm Q s
        (JUpperBoundWeakNorms.canonicalMaximizerFluxDefectOnCube Q
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
          p q q0) := by
  unfold Ch04.canonicalScalarResponseFluxWeakNormCubeSet
    cubeBesovNegativeVectorSeminorm
  apply congrArg sSup
  ext x
  constructor
  · rintro ⟨N, rfl⟩
    exact ⟨N,
      JUpperBoundWeakNorms.cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerFluxDefectOnDependentFamily_eq_ch04
        a ha Q s N p q q0⟩
  · rintro ⟨N, rfl⟩
    exact ⟨N,
      (JUpperBoundWeakNorms.cubeBesovNegativeVectorPartialSeminorm_canonicalMaximizerFluxDefectOnDependentFamily_eq_ch04
        a ha Q s N p q q0).symm⟩

end

end WeakNormsMaximizer
end Section53
end Ch05
end Book
end Homogenization
