import Homogenization.Book.Ch01.Theorems.CircDomination
import Homogenization.Besov.Duality.CaccioppoliBridge

namespace Homogenization
namespace Book
namespace Ch01

open scoped ENNReal

noncomputable section

/-- Public `p=2`, `q=1` cube-wise Besov pairing bound with an arbitrary
uniform positive-test bound. -/
theorem cubeBesovPairing_two_one_le_circNorm_mul_testBound {d : ℕ}
    (Q : Cube d) (s : ℝ) (u g : Vec d → ℝ) {B : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 ≤ B)
    (hnorm : ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ B)
    (hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    |cubeBesovPairing Q u g| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) *
          circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u) * B :=
  Homogenization.abs_cubeBesovPairing_le_note_constant_mul_of_uniform_bound_two_one_of_nonneg
    Q s u g hs hu hB hnorm hmem

/-- Public `p=2`, `q=1` cube-wise Besov pairing bound in the full-dual
average-inclusive form. -/
theorem cubeBesovPairing_two_one_le_fullDualNoteRhs_mul_testBound {d : ℕ}
    (Q : Cube d) (s : ℝ) (u g : Vec d → ℝ) {B : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 ≤ B)
    (hnorm : ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g ≤ B)
    (hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    |cubeBesovPairing Q u g| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) *
          circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) u +
        cubeBesovScaleWeight s Q * ‖normalizedAverage Q u‖) * B :=
  Homogenization.abs_cubeBesovPairing_le_note_rhs_mul_of_uniform_bound_two_one_of_nonneg
    Q s u g hs hu hB hnorm hmem

/-- Public `p=2`, `q=2` cube-wise Besov pairing bound in the full-dual
average-inclusive form. -/
theorem cubeBesovPairing_two_two_le_fullDualNoteRhs_mul_testBound {d : ℕ}
    (Q : Cube d) (s : ℝ) (u g : Vec d → ℝ) {B : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 ≤ B)
    (hnorm : ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g ≤ B)
    (hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    |cubeBesovPairing Q u g| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) *
          circNegativeBesovNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u +
        cubeBesovScaleWeight s Q * ‖normalizedAverage Q u‖) * B :=
  Homogenization.abs_cubeBesovPairing_le_note_rhs_mul_of_uniform_bound_two_two_of_nonneg
    Q s u g hs hu hB hnorm hmem

end

end Ch01
end Book
end Homogenization
