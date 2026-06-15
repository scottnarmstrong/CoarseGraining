import Homogenization.Besov.Duality.CaccioppoliBridge

namespace Homogenization

open MeasureTheory.Measure
open scoped BigOperators ENNReal

theorem cubeAverage_vecDot_eq_sum_cubeBesovPairing {d : ℕ} (Q : TriadicCube d)
    (u g : Vec d → Vec d)
    (hInt :
      ∀ i : Fin d,
        MeasureTheory.Integrable (fun x => u x i * g x i) (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => vecDot (u x) (g x)) =
      ∑ i, cubeBesovPairing Q (fun x => u x i) (fun x => g x i) := by
  calc
    cubeAverage Q (fun x => vecDot (u x) (g x))
        = ∫ x, vecDot (u x) (g x) ∂ normalizedCubeMeasure Q := by
            rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    _ = ∫ x, ∑ i, u x i * g x i ∂ normalizedCubeMeasure Q := by
          simp [vecDot]
    _ = ∑ i, ∫ x, u x i * g x i ∂ normalizedCubeMeasure Q := by
          rw [MeasureTheory.integral_finset_sum]
          intro i hi
          exact hInt i
    _ = ∑ i, cubeBesovPairing Q (fun x => u x i) (fun x => g x i) := by
          simp [cubeBesovPairing, cubeAverage_eq_integral_normalizedCubeMeasure]

theorem abs_cubeAverage_vecDot_le_sum_abs_cubeBesovPairing {d : ℕ} (Q : TriadicCube d)
    (u g : Vec d → Vec d)
    (hInt :
      ∀ i : Fin d,
        MeasureTheory.Integrable (fun x => u x i * g x i) (normalizedCubeMeasure Q)) :
    |cubeAverage Q (fun x => vecDot (u x) (g x))| ≤
      ∑ i, |cubeBesovPairing Q (fun x => u x i) (fun x => g x i)| := by
  rw [cubeAverage_vecDot_eq_sum_cubeBesovPairing Q u g hInt]
  simpa using
    (Finset.abs_sum_le_sum_abs (s := Finset.univ)
      (f := fun i : Fin d => cubeBesovPairing Q (fun x => u x i) (fun x => g x i)))

theorem abs_cubeAverage_vecDot_le_sum_note_rhs_mul_of_uniform_component_bounds_two_one
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) (B : Fin d → ℝ)
    (hs : 0 < s)
    (hu : ∀ i, MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : ∀ i, 0 < B i)
    (hnorm :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => g x i) ≤ B i)
    (hmem :
      ∀ i, CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => g x i)) :
    |cubeAverage Q (fun x => vecDot (u x) (g x))| ≤
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) * B i) := by
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hInt :
      ∀ i : Fin d,
        MeasureTheory.Integrable (fun x => u x i * g x i) (normalizedCubeMeasure Q) := by
    intro i
    have hgfull :
        CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => (B i)⁻¹ * g x i) :=
      cubeBesovDualFullTest_two_one_of_uniform_bound Q s (fun x => g x i) (hB i) (hnorm i) (hmem i)
    have hgi_mem :
        MeasureTheory.MemLp (fun x => g x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
      have hscaled_mem : MeasureTheory.MemLp (fun x => (B i)⁻¹ * g x i) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) := by
        simpa [hpConj, Pi.smul_apply, smul_eq_mul] using hgfull.memLp
      have hconst : MeasureTheory.MemLp (fun x => B i * ((B i)⁻¹ * g x i)) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) := by
            simpa [Pi.smul_apply, smul_eq_mul] using hscaled_mem.const_smul (B i)
      convert hconst using 1
      funext x
      field_simp [hB i |>.ne']
    simpa [Pi.mul_apply, mul_comm] using (hu i).integrable_mul hgi_mem
  calc
    |cubeAverage Q (fun x => vecDot (u x) (g x))|
        ≤ ∑ i, |cubeBesovPairing Q (fun x => u x i) (fun x => g x i)| := by
            exact abs_cubeAverage_vecDot_le_sum_abs_cubeBesovPairing Q u g hInt
    _ ≤ ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) * B i) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact abs_cubeBesovPairing_le_note_rhs_mul_of_uniform_bound_two_one
            Q s (fun x => u x i) (fun x => g x i) hs (hu i) (hB i) (hnorm i) (hmem i)

theorem abs_cubeAverage_vecDot_le_sum_note_rhs_mul_of_uniform_component_bounds_two_one_of_nonneg
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) (B : Fin d → ℝ)
    (hs : 0 < s)
    (hu : ∀ i, MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : ∀ i, 0 ≤ B i)
    (hnorm :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => g x i) ≤ B i)
    (hmem :
      ∀ i, CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => g x i)) :
    |cubeAverage Q (fun x => vecDot (u x) (g x))| ≤
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) * B i) := by
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hInt :
      ∀ i : Fin d,
        MeasureTheory.Integrable (fun x => u x i * g x i) (normalizedCubeMeasure Q) := by
    intro i
    have hBi_pos : 0 < B i + 1 := add_pos_of_nonneg_of_pos (hB i) zero_lt_one
    have hnormBi :
        ∀ N : ℕ,
          cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
              (fun x => g x i) ≤
            B i + 1 := by
      intro N
      exact (hnorm i N).trans (le_add_of_nonneg_right zero_le_one)
    have hgfull :
        CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => (B i + 1)⁻¹ * g x i) :=
      cubeBesovDualFullTest_two_one_of_uniform_bound Q s (fun x => g x i)
        hBi_pos hnormBi (hmem i)
    have hgi_mem :
        MeasureTheory.MemLp (fun x => g x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
      have hscaled_mem :
          MeasureTheory.MemLp (fun x => (B i + 1)⁻¹ * g x i)
            (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
        simpa [hpConj, Pi.smul_apply, smul_eq_mul] using hgfull.memLp
      have hconst :
          MeasureTheory.MemLp (fun x => (B i + 1) * ((B i + 1)⁻¹ * g x i))
            (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
        simpa [Pi.smul_apply, smul_eq_mul] using hscaled_mem.const_smul (B i + 1)
      convert hconst using 1
      funext x
      field_simp [hBi_pos.ne']
    simpa [Pi.mul_apply, mul_comm] using (hu i).integrable_mul hgi_mem
  calc
    |cubeAverage Q (fun x => vecDot (u x) (g x))|
        ≤ ∑ i, |cubeBesovPairing Q (fun x => u x i) (fun x => g x i)| := by
            exact abs_cubeAverage_vecDot_le_sum_abs_cubeBesovPairing Q u g hInt
    _ ≤ ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) * B i) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact abs_cubeBesovPairing_le_note_rhs_mul_of_uniform_bound_two_one_of_nonneg
            Q s (fun x => u x i) (fun x => g x i) hs (hu i) (hB i) (hnorm i) (hmem i)

/-- Sharp vectorized two-one pairing bound without the redundant average tail
in the flux dual norm. -/
theorem abs_cubeAverage_vecDot_le_sum_note_constant_mul_of_uniform_component_bounds_two_one_of_nonneg
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) (B : Fin d → ℝ)
    (hs : 0 < s)
    (hu : ∀ i, MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : ∀ i, 0 ≤ B i)
    (hnorm :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => g x i) ≤ B i)
    (hmem :
      ∀ i, CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => g x i)) :
    |cubeAverage Q (fun x => vecDot (u x) (g x))| ≤
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i)) * B i) := by
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hInt :
      ∀ i : Fin d,
        MeasureTheory.Integrable (fun x => u x i * g x i) (normalizedCubeMeasure Q) := by
    intro i
    have hBi_pos : 0 < B i + 1 := add_pos_of_nonneg_of_pos (hB i) zero_lt_one
    have hnormBi :
        ∀ N : ℕ,
          cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
              (fun x => g x i) ≤
            B i + 1 := by
      intro N
      exact (hnorm i N).trans (le_add_of_nonneg_right zero_le_one)
    have hgfull :
        CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => (B i + 1)⁻¹ * g x i) :=
      cubeBesovDualFullTest_two_one_of_uniform_bound Q s (fun x => g x i)
        hBi_pos hnormBi (hmem i)
    have hgi_mem :
        MeasureTheory.MemLp (fun x => g x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
      have hscaled_mem :
          MeasureTheory.MemLp (fun x => (B i + 1)⁻¹ * g x i)
            (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
        simpa [hpConj, Pi.smul_apply, smul_eq_mul] using hgfull.memLp
      have hconst :
          MeasureTheory.MemLp (fun x => (B i + 1) * ((B i + 1)⁻¹ * g x i))
            (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
        simpa [Pi.smul_apply, smul_eq_mul] using hscaled_mem.const_smul (B i + 1)
      convert hconst using 1
      funext x
      field_simp [hBi_pos.ne']
    simpa [Pi.mul_apply, mul_comm] using (hu i).integrable_mul hgi_mem
  calc
    |cubeAverage Q (fun x => vecDot (u x) (g x))|
        ≤ ∑ i, |cubeBesovPairing Q (fun x => u x i) (fun x => g x i)| := by
            exact abs_cubeAverage_vecDot_le_sum_abs_cubeBesovPairing Q u g hInt
    _ ≤ ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i)) * B i) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact abs_cubeBesovPairing_le_note_constant_mul_of_uniform_bound_two_one_of_nonneg
            Q s (fun x => u x i) (fun x => g x i) hs (hu i) (hB i) (hnorm i) (hmem i)

theorem sum_abs_cubeBesovPairing_le_sum_dualFullNorm_mul_of_uniform_component_bounds_two_one
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) (B : Fin d → ℝ)
    (hs : 0 < s)
    (hu : ∀ i, MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : ∀ i, 0 < B i)
    (hnorm :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => g x i) ≤ B i)
    (hmem :
      ∀ i, CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => g x i)) :
    ∑ i, |cubeBesovPairing Q (fun x => u x i) (fun x => g x i)| ≤
      ∑ i, cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i) *
        B i := by
  refine Finset.sum_le_sum ?_
  intro i hi
  exact abs_cubeBesovPairing_le_mul_cubeBesovDualFullNorm_of_uniform_bound_two_one
    Q s (fun x => u x i) (fun x => g x i) hs (hu i) (hB i) (hnorm i) (hmem i)

theorem abs_cubeAverage_vecDot_le_sum_dualFullNorm_mul_of_uniform_component_bounds_two_one
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) (B : Fin d → ℝ)
    (hs : 0 < s)
    (hu : ∀ i, MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : ∀ i, 0 < B i)
    (hnorm :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => g x i) ≤ B i)
    (hmem :
      ∀ i, CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => g x i)) :
    |cubeAverage Q (fun x => vecDot (u x) (g x))| ≤
      ∑ i, cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i) *
        B i := by
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hInt :
      ∀ i : Fin d,
        MeasureTheory.Integrable (fun x => u x i * g x i) (normalizedCubeMeasure Q) := by
    intro i
    have hgfull :
        CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => (B i)⁻¹ * g x i) :=
      cubeBesovDualFullTest_two_one_of_uniform_bound Q s (fun x => g x i) (hB i)
        (hnorm i) (hmem i)
    have hgi_mem :
        MeasureTheory.MemLp (fun x => g x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
      have hscaled_mem : MeasureTheory.MemLp (fun x => (B i)⁻¹ * g x i) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) := by
        simpa [hpConj, Pi.smul_apply, smul_eq_mul] using hgfull.memLp
      have hconst : MeasureTheory.MemLp (fun x => B i * ((B i)⁻¹ * g x i)) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) := by
            simpa [Pi.smul_apply, smul_eq_mul] using hscaled_mem.const_smul (B i)
      convert hconst using 1
      funext x
      field_simp [hB i |>.ne']
    simpa [Pi.mul_apply, mul_comm] using (hu i).integrable_mul hgi_mem
  calc
    |cubeAverage Q (fun x => vecDot (u x) (g x))|
        ≤ ∑ i, |cubeBesovPairing Q (fun x => u x i) (fun x => g x i)| := by
            exact abs_cubeAverage_vecDot_le_sum_abs_cubeBesovPairing Q u g hInt
    _ ≤ ∑ i, cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => u x i) * B i := by
          exact
            sum_abs_cubeBesovPairing_le_sum_dualFullNorm_mul_of_uniform_component_bounds_two_one
              Q s u g B hs hu hB hnorm hmem

theorem sum_abs_cubeBesovPairing_le_sum_dualFullNorm_mul_sum_bounds_two_one
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) (B : Fin d → ℝ)
    (hs : 0 < s)
    (hu : ∀ i, MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : ∀ i, 0 < B i)
    (hnorm :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => g x i) ≤ B i)
    (hmem :
      ∀ i, CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => g x i))
    (hdualNonneg :
      ∀ i : Fin d,
        0 ≤ cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i)) :
    ∑ i, |cubeBesovPairing Q (fun x => u x i) (fun x => g x i)| ≤
      (∑ i, cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i)) *
        (∑ i, B i) := by
  have hcomponent :
      ∑ i, |cubeBesovPairing Q (fun x => u x i) (fun x => g x i)| ≤
        ∑ i, cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i) *
          B i :=
    sum_abs_cubeBesovPairing_le_sum_dualFullNorm_mul_of_uniform_component_bounds_two_one
      Q s u g B hs hu hB hnorm hmem
  calc
    ∑ i, |cubeBesovPairing Q (fun x => u x i) (fun x => g x i)|
        ≤ ∑ i, cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u x i) * B i := hcomponent
    _ ≤ ∑ i, cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u x i) * (∑ j, B j) := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          exact mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (fun j _hj => (hB j).le) (Finset.mem_univ i))
            (hdualNonneg i)
    _ = (∑ i, cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u x i)) * (∑ i, B i) := by
          rw [Finset.sum_mul]

theorem abs_cubeAverage_vecDot_le_sum_dualFullNorm_mul_sum_bounds_two_one
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) (B : Fin d → ℝ)
    (hs : 0 < s)
    (hu : ∀ i, MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : ∀ i, 0 < B i)
    (hnorm :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => g x i) ≤ B i)
    (hmem :
      ∀ i, CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => g x i))
    (hdualNonneg :
      ∀ i : Fin d,
        0 ≤ cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i)) :
    |cubeAverage Q (fun x => vecDot (u x) (g x))| ≤
      (∑ i, cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i)) *
        (∑ i, B i) := by
  have hcomponent :
      |cubeAverage Q (fun x => vecDot (u x) (g x))| ≤
        ∑ i, cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i) *
          B i :=
    abs_cubeAverage_vecDot_le_sum_dualFullNorm_mul_of_uniform_component_bounds_two_one
      Q s u g B hs hu hB hnorm hmem
  have hgroup :
      ∑ i, cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i) *
          B i ≤
        (∑ i, cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i)) *
          (∑ i, B i) := by
    calc
      ∑ i, cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u x i) *
          B i
          ≤ ∑ i, cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => u x i) * (∑ j, B j) := by
            refine Finset.sum_le_sum ?_
            intro i _hi
            exact mul_le_mul_of_nonneg_left
              (Finset.single_le_sum (fun j _hj => (hB j).le) (Finset.mem_univ i))
              (hdualNonneg i)
      _ = (∑ i, cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => u x i)) * (∑ i, B i) := by
            rw [Finset.sum_mul]
  exact hcomponent.trans hgroup

theorem abs_cubeAverage_vecDot_le_sum_note_rhs_mul_of_uniform_component_bounds_two_two
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) (B : Fin d → ℝ)
    (hs : 0 < s)
    (hu : ∀ i, MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : ∀ i, 0 < B i)
    (hnorm :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => g x i) ≤ B i)
    (hmem :
      ∀ i, CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => g x i)) :
    |cubeAverage Q (fun x => vecDot (u x) (g x))| ≤
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => u x i) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) * B i) := by
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hInt :
      ∀ i : Fin d,
        MeasureTheory.Integrable (fun x => u x i * g x i) (normalizedCubeMeasure Q) := by
    intro i
    have hgfull :
        CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => (B i)⁻¹ * g x i) :=
      cubeBesovDualFullTest_two_two_of_uniform_bound Q s (fun x => g x i) (hB i) (hnorm i) (hmem i)
    have hgi_mem :
        MeasureTheory.MemLp (fun x => g x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
      have hscaled_mem : MeasureTheory.MemLp (fun x => (B i)⁻¹ * g x i) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) := by
            simpa [hpConj, Pi.smul_apply, smul_eq_mul] using hgfull.memLp
      have hconst : MeasureTheory.MemLp (fun x => B i * ((B i)⁻¹ * g x i)) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) := by
            simpa [Pi.smul_apply, smul_eq_mul] using hscaled_mem.const_smul (B i)
      convert hconst using 1
      funext x
      field_simp [hB i |>.ne']
    simpa [Pi.mul_apply, mul_comm] using (hu i).integrable_mul hgi_mem
  calc
    |cubeAverage Q (fun x => vecDot (u x) (g x))|
        ≤ ∑ i, |cubeBesovPairing Q (fun x => u x i) (fun x => g x i)| := by
            exact abs_cubeAverage_vecDot_le_sum_abs_cubeBesovPairing Q u g hInt
    _ ≤ ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => u x i) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) * B i) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact abs_cubeBesovPairing_le_note_rhs_mul_of_uniform_bound_two_two
            Q s (fun x => u x i) (fun x => g x i) hs (hu i) (hB i) (hnorm i) (hmem i)

theorem abs_cubeAverage_vecDot_le_sum_note_rhs_mul_of_uniform_component_bounds_two_two_of_nonneg
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u g : Vec d → Vec d) (B : Fin d → ℝ)
    (hs : 0 < s)
    (hu : ∀ i, MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : ∀ i, 0 ≤ B i)
    (hnorm :
      ∀ i : Fin d, ∀ N : ℕ,
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => g x i) ≤ B i)
    (hmem :
      ∀ i, CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => g x i)) :
    |cubeAverage Q (fun x => vecDot (u x) (g x))| ≤
      ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => u x i) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) * B i) := by
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hInt :
      ∀ i : Fin d,
        MeasureTheory.Integrable (fun x => u x i * g x i) (normalizedCubeMeasure Q) := by
    intro i
    have hBi_pos : 0 < B i + 1 := add_pos_of_nonneg_of_pos (hB i) zero_lt_one
    have hnormBi :
        ∀ N : ℕ,
          cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
              (fun x => g x i) ≤
            B i + 1 := by
      intro N
      exact (hnorm i N).trans (le_add_of_nonneg_right zero_le_one)
    have hgfull :
        CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
          (fun x => (B i + 1)⁻¹ * g x i) :=
      cubeBesovDualFullTest_two_two_of_uniform_bound Q s (fun x => g x i)
        hBi_pos hnormBi (hmem i)
    have hgi_mem :
        MeasureTheory.MemLp (fun x => g x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
      have hscaled_mem :
          MeasureTheory.MemLp (fun x => (B i + 1)⁻¹ * g x i)
            (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
        simpa [hpConj, Pi.smul_apply, smul_eq_mul] using hgfull.memLp
      have hconst :
          MeasureTheory.MemLp (fun x => (B i + 1) * ((B i + 1)⁻¹ * g x i))
            (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
        simpa [Pi.smul_apply, smul_eq_mul] using hscaled_mem.const_smul (B i + 1)
      convert hconst using 1
      funext x
      field_simp [hBi_pos.ne']
    simpa [Pi.mul_apply, mul_comm] using (hu i).integrable_mul hgi_mem
  calc
    |cubeAverage Q (fun x => vecDot (u x) (g x))|
        ≤ ∑ i, |cubeBesovPairing Q (fun x => u x i) (fun x => g x i)| := by
            exact abs_cubeAverage_vecDot_le_sum_abs_cubeBesovPairing Q u g hInt
    _ ≤ ∑ i, (((3 : ℝ) ^ ((d : ℝ) + s) *
          cubeBesovCircNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => u x i) +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖) * B i) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact abs_cubeBesovPairing_le_note_rhs_mul_of_uniform_bound_two_two_of_nonneg
            Q s (fun x => u x i) (fun x => g x i) hs (hu i) (hB i) (hnorm i) (hmem i)

end Homogenization
