import Homogenization.Book.Ch01.Definitions
import Homogenization.Besov.Duality.GlobalComparison

namespace Homogenization
namespace Book
namespace Ch01

open scoped ENNReal

noncomputable section

/-- Note-facing circ domination of the mean-zero dual negative Besov seminorm. -/
theorem circDominatesMeanZeroDualBesov {d : ℕ} (Q : Cube d)
    (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ)
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q) :
    dualNegativeBesovSeminorm Q s p q u ≤
      (3 : ℝ) ^ ((d : ℝ) + s) * circNegativeBesovNorm Q s p q u :=
  Homogenization.cubeBesovDualMeanZeroSeminorm_le_note_constant_mul_cubeBesovCircNorm
    Q s p q u hs hu hp hpTop hpConjTop hq

/-- Note-facing circ domination of the full dual negative Besov norm. -/
theorem circDominatesFullDualBesov {d : ℕ} (Q : Cube d)
    (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ)
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q) :
    dualNegativeBesovNorm Q s p q u ≤
      (3 : ℝ) ^ ((d : ℝ) + s) * circNegativeBesovNorm Q s p q u +
        cubeBesovScaleWeight s Q * ‖normalizedAverage Q u‖ :=
  Homogenization.cubeBesovDualFullNorm_le_note_rhs
    Q s p q u hs hu hp hpTop hpConjTop hq

/-- Cube-wise Besov pairing controlled by the concrete circ negative norm for
unit full-dual positive tests. -/
theorem cubeBesovPairing_le_circNorm_of_fullTest {d : ℕ} (Q : Cube d)
    (s : ℝ) (p q : ℝ≥0∞) (u g : Vec d → ℝ)
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q)
    (hg : CubeBesovDualFullTest Q s p q g) :
    |cubeBesovPairing Q u g| ≤
      (3 : ℝ) ^ ((d : ℝ) + s) * circNegativeBesovNorm Q s p q u := by
  have hBdd :
      BddAbove (cubeBesovCircNormValueSet Q s p q u) :=
    Homogenization.cubeBesovCircNormValueSet_bddAbove_of_memLp
      Q s p q u hs hu hp hpTop hq
  have hpair :
      |cubeBesovPairing Q u g| ≤
        max 1 ((3 : ℝ) ^ s) * circNegativeBesovNorm Q s p q u :=
    Homogenization.abs_cubeBesovPairing_le_max_mul_cubeBesovCircNorm_of_full_test
      Q s p q u g hBdd hu hp hpTop hpConjTop hq hg
  have hconst :
      max 1 ((3 : ℝ) ^ s) ≤ (3 : ℝ) ^ ((d : ℝ) + s) :=
    Homogenization.max_one_three_rpow_le_three_rpow_nat_add d s hs.le
  have hcirc_nonneg :
      0 ≤ circNegativeBesovNorm Q s p q u :=
    Homogenization.cubeBesovCircNorm_nonneg Q s p q u hBdd
  exact hpair.trans (mul_le_mul_of_nonneg_right hconst hcirc_nonneg)

end

end Ch01
end Book
end Homogenization
