import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Homogenization.HighContrast.EntryScale.MomentConsequences
import Homogenization.HighContrast.EntryScale.Memory.P1

open scoped BigOperators

namespace Homogenization.HighContrast.EntryScale

variable {d : ℕ}

/--
Source label `l.det.memory`: for `j` in the grid block starting at
`m_{r-1}`, monotonicity and telescoping give
`F_j - F_i <= sum_{a=r}^i Delta_a`.
-/
theorem memoryGridContrast_sub_le_sum_memoryGridDrop_of_le_block_left
    {F : ℕ → ℝ} (hF : Antitone F) {Nstar L j r i : ℕ}
    (hr_pos : 1 ≤ r) (hri : r ≤ i)
    (hj_left : memoryGridScale Nstar L (r - 1) ≤ j) :
    F j - memoryGridContrast F Nstar L i ≤
      ∑ a ∈ Finset.Icc r i, memoryGridDrop F Nstar L a := by
  have hmono : F j ≤ memoryGridContrast F Nstar L (r - 1) := by
    dsimp [memoryGridContrast]
    exact hF hj_left
  have hsum :=
    memoryGridDrop_sum_Icc_eq_contrast_sub F Nstar L r i hr_pos hri
  calc
    F j - memoryGridContrast F Nstar L i ≤
        memoryGridContrast F Nstar L (r - 1) -
          memoryGridContrast F Nstar L i :=
      sub_le_sub_right hmono _
    _ = ∑ a ∈ Finset.Icc r i, memoryGridDrop F Nstar L a := by
      rw [← hsum]

/--
Source label `l.det.memory`: grid-block contrast drops, after insertion of
the factor `q^(i-r)`, are paid by the current memory.
-/
theorem memoryGridContrast_sub_mul_pow_le_inv_mul_memory_of_le_block_left
    {q H0 : ℝ} {F : ℕ → ℝ} {Nstar L j r i : ℕ}
    (hq_pos : 0 < q) (hq_le_one : q ≤ 1)
    (hH0_nonneg : 0 ≤ H0)
    (hF : Antitone F)
    (hr_pos : 1 ≤ r) (hri : r ≤ i)
    (hj_left : memoryGridScale Nstar L (r - 1) ≤ j) :
    q ^ (i - r) * (F j - memoryGridContrast F Nstar L i) ≤
      q⁻¹ * memory q H0 (memoryGridDrop F Nstar L) i := by
  have hcontrast :
      F j - memoryGridContrast F Nstar L i ≤
        ∑ a ∈ Finset.Icc r i, memoryGridDrop F Nstar L a :=
    memoryGridContrast_sub_le_sum_memoryGridDrop_of_le_block_left hF
      hr_pos hri hj_left
  have hpow_nonneg : 0 ≤ q ^ (i - r) :=
    pow_nonneg (le_of_lt hq_pos) _
  have hscaled :
      q ^ (i - r) * (F j - memoryGridContrast F Nstar L i) ≤
        q ^ (i - r) *
          (∑ a ∈ Finset.Icc r i, memoryGridDrop F Nstar L a) :=
    mul_le_mul_of_nonneg_left hcontrast hpow_nonneg
  have htail :
      q ^ (i - r) *
          (∑ a ∈ Finset.Icc r i, memoryGridDrop F Nstar L a) ≤
        q⁻¹ * memory q H0 (memoryGridDrop F Nstar L) i :=
    memoryGridDrop_tail_mul_pow_le_inv_mul_memory hq_pos hq_le_one
      hH0_nonneg hF hr_pos
  exact hscaled.trans htail

/--
Source label `l.det.memory`: for `j <= m_r`, the source decay weight is
bounded by the grid factor `q^(i-r)`.
-/
theorem memoryGridWeight_le_memoryDecay_pow_of_le_block_right
    {d : ℕ} (hc : HighContrastExponents d) {Nstar L j r i : ℕ}
    (hri : r ≤ i)
    (hj_right : j ≤ memoryGridScale Nstar L r) :
    (3 : ℝ) ^
        (-(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ))) ≤
      memoryDecay hc L ^ (i - r) := by
  have hscale_add :
      memoryGridScale Nstar L r + (i - r) * L =
        memoryGridScale Nstar L i := by
    dsimp [memoryGridScale]
    rw [Nat.add_assoc, ← Nat.add_mul, Nat.add_sub_of_le hri]
  have hsum_le :
      j + (i - r) * L ≤ memoryGridScale Nstar L i := by
    calc
      j + (i - r) * L ≤
          memoryGridScale Nstar L r + (i - r) * L :=
        Nat.add_le_add_right hj_right _
      _ = memoryGridScale Nstar L i := hscale_add
  have hgap_nat :
      (i - r) * L ≤ memoryGridScale Nstar L i - j := by
    omega
  have hgap_real :
      (((i - r) * L : ℕ) : ℝ) ≤
        ((memoryGridScale Nstar L i - j : ℕ) : ℝ) := by
    exact_mod_cast hgap_nat
  have hmul_le :
      hc.rhoM * (((i - r) * L : ℕ) : ℝ) ≤
        hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hgap_real (le_of_lt hc.rhoM_pos)
  have hexp_le :
      -(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ)) ≤
        -(hc.rhoM * (((i - r) * L : ℕ) : ℝ)) := by
    linarith
  -- `memoryDecay` now decays at `kappaH <= rhoM`, so its `(i-r)`-th power
  -- (the upper bound) is the larger factor `3^{-kappaH (i-r)L}`.
  have hcast_nonneg : (0 : ℝ) ≤ (((i - r) * L : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrate_le :
      hc.kappaH * (((i - r) * L : ℕ) : ℝ) ≤
        hc.rhoM * (((i - r) * L : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hc.kappaH_le_rhoM hcast_nonneg
  have hexp_le' :
      -(hc.rhoM * (((i - r) * L : ℕ) : ℝ)) ≤
        -(hc.kappaH * (((i - r) * L : ℕ) : ℝ)) := by
    linarith
  calc
    (3 : ℝ) ^
        (-(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ))) ≤
        (3 : ℝ) ^ (-(hc.rhoM * (((i - r) * L : ℕ) : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 3) hexp_le
    _ ≤ (3 : ℝ) ^ (-(hc.kappaH * (((i - r) * L : ℕ) : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 3) hexp_le'
    _ = memoryDecay hc L ^ (i - r) := by
      rw [← memoryDecay_pow_eq_grid_gap]

/--
Source label `l.det.memory`: on the pre-start range, the same source weight
is bounded termwise by the manuscript weighted grid-tail factors.
-/
theorem memoryGridWeight_mul_gridDrop_sum_le_weighted_gridDrop_sum_of_prestart
    (hc : HighContrastExponents d)
    {Nstar L i j : ℕ} {F : ℕ → ℝ}
    (hjNstar : j ≤ Nstar)
    (hF : Antitone F) :
    (3 : ℝ) ^
        (-(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ))) *
        (∑ a ∈ Finset.Icc 1 i, memoryGridDrop F Nstar L a) ≤
      ∑ a ∈ Finset.Icc 1 i,
        memoryDecay hc L ^ (i - a) * memoryGridDrop F Nstar L a := by
  let w : ℝ :=
    (3 : ℝ) ^
      (-(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ)))
  have hweight_i : w ≤ memoryDecay hc L ^ i := by
    exact memoryGridWeight_le_memoryDecay_pow_of_le_block_right
      (hc := hc) (Nstar := Nstar) (L := L) (j := j) (r := 0) (i := i)
      (Nat.zero_le i) (by simpa [memoryGridScale] using hjNstar)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro a ha
  have ha_bounds := Finset.mem_Icc.mp ha
  have hpow :
      memoryDecay hc L ^ i ≤ memoryDecay hc L ^ (i - a) := by
    exact pow_le_pow_of_le_one
      (le_of_lt (memoryDecay_pos hc L)) (memoryDecay_le_one hc L)
      (by omega : i - a ≤ i)
  have hweight_a : w ≤ memoryDecay hc L ^ (i - a) :=
    hweight_i.trans hpow
  have hdrop_nonneg : 0 ≤ memoryGridDrop F Nstar L a := by
    cases a with
    | zero => omega
    | succ a =>
        exact memoryGridDrop_succ_nonneg_of_antitone hF Nstar L a
  exact mul_le_mul_of_nonneg_right hweight_a hdrop_nonneg

/--
Source label `l.det.memory`: every pre-start source-weighted contrast drop is
paid by the current memory.
-/
theorem memoryGridContrast_weighted_sub_le_inv_mul_memory_of_prestart
    (hc : HighContrastExponents d)
    {N Nstar L i j : ℕ} {F : ℕ → ℝ}
    (hi : 1 ≤ i)
    (hNj : N ≤ j) (hjNstar : j ≤ Nstar)
    (hF : Antitone F) :
    (3 : ℝ) ^
        (-(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ))) *
        (F j - memoryGridContrast F Nstar L i) ≤
      (memoryDecay hc L)⁻¹ *
        memory (memoryDecay hc L)
          (initialMemory hc.rhoM N Nstar F)
          (memoryGridDrop F Nstar L) i := by
  let w : ℝ :=
    (3 : ℝ) ^
      (-(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ)))
  let preTail : ℝ :=
    ∑ ell ∈ Finset.Icc (j + 1) Nstar, (F (ell - 1) - F ell)
  let gridTail : ℝ :=
    ∑ a ∈ Finset.Icc 1 i, memoryGridDrop F Nstar L a
  let weightedGridTail : ℝ :=
    ∑ a ∈ Finset.Icc 1 i,
      memoryDecay hc L ^ (i - a) * memoryGridDrop F Nstar L a
  let H0 : ℝ := initialMemory hc.rhoM N Nstar F
  have hdecomp :
      F j - memoryGridContrast F Nstar L i = preTail + gridTail := by
    dsimp [preTail, gridTail]
    exact sub_memoryGridContrast_eq_prestartDrop_sum_add_gridDrop_sum F
      hjNstar hi
  have hpre :
      w * preTail ≤ memoryDecay hc L ^ i * H0 := by
    dsimp [w, preTail, H0]
    exact memoryGridWeight_mul_prestartDrop_sum_le_memoryDecay_pow_mul_initialMemory
      (hc := hc) (N := N) (Nstar := Nstar) (L := L) (i := i)
      (j := j) (F := F) hNj hF
  have hgrid :
      w * gridTail ≤ weightedGridTail := by
    dsimp [w, gridTail, weightedGridTail]
    exact memoryGridWeight_mul_gridDrop_sum_le_weighted_gridDrop_sum_of_prestart
      (hc := hc) (Nstar := Nstar) (L := L) (i := i)
      (j := j) (F := F) hjNstar hF
  have hH0_nonneg : 0 ≤ H0 := by
    dsimp [H0]
    exact initialMemory_nonneg_of_antitone hF
  have hscalar :
      memoryDecay hc L ^ i * H0 + weightedGridTail ≤
        (memoryDecay hc L)⁻¹ *
          memory (memoryDecay hc L) H0 (memoryGridDrop F Nstar L) i := by
    dsimp [weightedGridTail]
    exact memory_initial_pow_add_weighted_tail_le_inv_mul_memory
      (q := memoryDecay hc L) (H0 := H0)
      (delta := memoryGridDrop F Nstar L) (i := i)
      (memoryDecay_pos hc L) (memoryDecay_le_one hc L)
      hH0_nonneg hi
  calc
    (3 : ℝ) ^
        (-(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ))) *
        (F j - memoryGridContrast F Nstar L i)
        = w * (preTail + gridTail) := by
          rw [hdecomp]
    _ = w * preTail + w * gridTail := by ring
    _ ≤ memoryDecay hc L ^ i * H0 + weightedGridTail :=
      add_le_add hpre hgrid
    _ ≤ (memoryDecay hc L)⁻¹ *
          memory (memoryDecay hc L) H0 (memoryGridDrop F Nstar L) i :=
      hscalar

/--
Source label `l.det.memory`: on a post-start grid block
`j in [m_{r-1}, m_r]`, the source-weighted contrast drop is paid by the
current memory.
-/
theorem memoryGridContrast_weighted_sub_le_inv_mul_memory_of_mem_grid_block
    (hc : HighContrastExponents d)
    {H0 : ℝ} {F : ℕ → ℝ} {Nstar L j r i : ℕ}
    (hH0_nonneg : 0 ≤ H0)
    (hF : Antitone F)
    (hr_pos : 1 ≤ r) (hri : r ≤ i)
    (hj_left : memoryGridScale Nstar L (r - 1) ≤ j)
    (hj_right : j ≤ memoryGridScale Nstar L r) :
    (3 : ℝ) ^
        (-(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ))) *
        (F j - memoryGridContrast F Nstar L i) ≤
      (memoryDecay hc L)⁻¹ *
        memory (memoryDecay hc L) H0 (memoryGridDrop F Nstar L) i := by
  have hweight :
      (3 : ℝ) ^
          (-(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ))) ≤
        memoryDecay hc L ^ (i - r) :=
    memoryGridWeight_le_memoryDecay_pow_of_le_block_right hc hri hj_right
  have hj_i : j ≤ memoryGridScale Nstar L i :=
    hj_right.trans (memoryGridScale_le_of_le hri)
  have hcontrast_nonneg :
      0 ≤ F j - memoryGridContrast F Nstar L i := by
    have hmono : memoryGridContrast F Nstar L i ≤ F j := by
      dsimp [memoryGridContrast]
      exact hF hj_i
    linarith
  have hweight_scaled :
      (3 : ℝ) ^
          (-(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ))) *
          (F j - memoryGridContrast F Nstar L i) ≤
        memoryDecay hc L ^ (i - r) *
          (F j - memoryGridContrast F Nstar L i) :=
    mul_le_mul_of_nonneg_right hweight hcontrast_nonneg
  have hmemory :
      memoryDecay hc L ^ (i - r) *
          (F j - memoryGridContrast F Nstar L i) ≤
        (memoryDecay hc L)⁻¹ *
          memory (memoryDecay hc L) H0 (memoryGridDrop F Nstar L) i :=
    memoryGridContrast_sub_mul_pow_le_inv_mul_memory_of_le_block_left
      (q := memoryDecay hc L) (H0 := H0) (F := F)
      (Nstar := Nstar) (L := L) (j := j) (r := r) (i := i)
      (memoryDecay_pos hc L) (memoryDecay_le_one hc L)
      hH0_nonneg hF hr_pos hri hj_left
  exact hweight_scaled.trans hmemory

/--
Source label `l.det.memory`: every post-start scale `j <= m_i` lies in one
of the grid blocks `[m_{r-1}, m_r]`, `1 <= r <= i`.
-/
theorem exists_memoryGridBlock_of_poststart_le_gridScale
    {Nstar L i j : ℕ}
    (hi : 1 ≤ i)
    (hj_start : memoryGridScale Nstar L 0 ≤ j)
    (hj_end : j ≤ memoryGridScale Nstar L i) :
    ∃ r : ℕ,
      1 ≤ r ∧ r ≤ i ∧
        memoryGridScale Nstar L (r - 1) ≤ j ∧
          j ≤ memoryGridScale Nstar L r := by
  induction i generalizing j with
  | zero =>
      omega
  | succ i ih =>
      by_cases hi_zero : i = 0
      · subst i
        refine ⟨1, by omega, by omega, ?_, ?_⟩
        · simpa using hj_start
        · simpa using hj_end
      · have hi_pos : 1 ≤ i := by omega
        by_cases hj_mid : j ≤ memoryGridScale Nstar L i
        · obtain ⟨r, hr_pos, hri, hj_left, hj_right⟩ :=
            ih hi_pos hj_start hj_mid
          exact ⟨r, hr_pos, by omega, hj_left, hj_right⟩
        · refine ⟨i + 1, by omega, by omega, ?_, hj_end⟩
          have hleft : memoryGridScale Nstar L i ≤ j := by omega
          simpa using hleft

/--
Source label `l.det.memory`: every post-start source-weighted contrast drop is
paid by the current memory.
-/
theorem memoryGridContrast_weighted_sub_le_inv_mul_memory_of_poststart
    (hc : HighContrastExponents d)
    {H0 : ℝ} {F : ℕ → ℝ} {Nstar L j i : ℕ}
    (hi : 1 ≤ i)
    (hH0_nonneg : 0 ≤ H0)
    (hF : Antitone F)
    (hj_start : Nstar ≤ j)
    (hj_end : j ≤ memoryGridScale Nstar L i) :
    (3 : ℝ) ^
        (-(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ))) *
        (F j - memoryGridContrast F Nstar L i) ≤
      (memoryDecay hc L)⁻¹ *
        memory (memoryDecay hc L) H0 (memoryGridDrop F Nstar L) i := by
  have hj_start_grid : memoryGridScale Nstar L 0 ≤ j := by
    simpa [memoryGridScale] using hj_start
  obtain ⟨r, hr_pos, hri, hj_left, hj_right⟩ :=
    exists_memoryGridBlock_of_poststart_le_gridScale
      (Nstar := Nstar) (L := L) (i := i) (j := j)
      hi hj_start_grid hj_end
  exact
    memoryGridContrast_weighted_sub_le_inv_mul_memory_of_mem_grid_block
      (hc := hc) (H0 := H0) (F := F) (Nstar := Nstar) (L := L)
      (j := j) (r := r) (i := i)
      hH0_nonneg hF hr_pos hri hj_left hj_right

/--
Source label `l.det.memory`: every source scale `N <= j <= m_i`, including
pre-start scales, has weighted contrast drop paid by the current memory.
-/
theorem memoryGridContrast_weighted_sub_le_inv_mul_memory_of_mem_Icc
    (hc : HighContrastExponents d)
    {N Nstar L i j : ℕ} {F : ℕ → ℝ}
    (hi : 1 ≤ i)
    (hF : Antitone F)
    (hj : j ∈ Finset.Icc N (memoryGridScale Nstar L i)) :
    (3 : ℝ) ^
        (-(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ))) *
        (F j - memoryGridContrast F Nstar L i) ≤
      (memoryDecay hc L)⁻¹ *
        memory (memoryDecay hc L)
          (initialMemory hc.rhoM N Nstar F)
          (memoryGridDrop F Nstar L) i := by
  have hj_bounds := Finset.mem_Icc.mp hj
  by_cases hjNstar : j ≤ Nstar
  · exact
      memoryGridContrast_weighted_sub_le_inv_mul_memory_of_prestart
        (hc := hc) (N := N) (Nstar := Nstar) (L := L)
        (i := i) (j := j) (F := F)
        hi hj_bounds.1 hjNstar hF
  · have hNstarj : Nstar ≤ j := by omega
    have hH0_nonneg :
        0 ≤ initialMemory hc.rhoM N Nstar F :=
      initialMemory_nonneg_of_antitone hF
    exact
      memoryGridContrast_weighted_sub_le_inv_mul_memory_of_poststart
        (hc := hc) (H0 := initialMemory hc.rhoM N Nstar F)
        (F := F) (Nstar := Nstar) (L := L)
        (j := j) (i := i)
        hi hH0_nonneg hF hNstarj hj_bounds.2

/--
Source label `l.det.memory`: finite supremum form of the full
source-weighted contrast-drop bound over `N <= j <= m_i`.
-/
theorem memoryGridContrast_weighted_sup_le_inv_mul_memory
    (hc : HighContrastExponents d)
    {N Nstar L i : ℕ} {F : ℕ → ℝ}
    (hi : 1 ≤ i)
    (hNNstar : N ≤ Nstar)
    (hF : Antitone F) :
    (Finset.Icc N (memoryGridScale Nstar L i)).sup'
        ⟨N, Finset.mem_Icc.mpr
          ⟨le_rfl, by
            exact hNNstar.trans
              (by
                dsimp [memoryGridScale]
                exact Nat.le_add_right Nstar (i * L))⟩⟩
        (fun j =>
          (3 : ℝ) ^
            (-(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ))) *
            (F j - memoryGridContrast F Nstar L i)) ≤
      (memoryDecay hc L)⁻¹ *
        memory (memoryDecay hc L)
          (initialMemory hc.rhoM N Nstar F)
          (memoryGridDrop F Nstar L) i := by
  classical
  let S : Finset ℕ := Finset.Icc N (memoryGridScale Nstar L i)
  let phi : ℕ → ℝ := fun j =>
    (3 : ℝ) ^
      (-(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ))) *
      (F j - memoryGridContrast F Nstar L i)
  let hS : S.Nonempty :=
    ⟨N, by
      dsimp [S]
      exact Finset.mem_Icc.mpr
        ⟨le_rfl, hNNstar.trans
          (by
            dsimp [memoryGridScale]
            exact Nat.le_add_right Nstar (i * L))⟩⟩
  refine Finset.sup'_le (s := S) (f := phi) hS ?_
  intro j hj
  exact
    memoryGridContrast_weighted_sub_le_inv_mul_memory_of_mem_Icc
      (hc := hc) (N := N) (Nstar := Nstar) (L := L)
      (i := i) (j := j) (F := F)
      hi hF (by simpa [S] using hj)

/--
Source label `l.det.memory`: the full source-weighted contrast-drop supremum
for the concrete contrast excess sequence is paid by the memory variable.
-/
theorem contrastExcessAtScale_weighted_sup_le_inv_mul_memory_of_P4
    {d : ℕ} [NeZero d] (hc : HighContrastExponents d) {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {N Nstar L i : ℕ}
    (hi : 1 ≤ i)
    (hNNstar : N ≤ Nstar) :
    (Finset.Icc N (memoryGridScale Nstar L i)).sup'
        ⟨N, Finset.mem_Icc.mpr
          ⟨le_rfl, by
            exact hNNstar.trans
              (by
                dsimp [memoryGridScale]
                exact Nat.le_add_right Nstar (i * L))⟩⟩
        (fun j =>
          (3 : ℝ) ^
            (-(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ))) *
            (contrastExcessAtScale hP hStruct j -
              contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))) ≤
      (memoryDecay hc L)⁻¹ *
        memory (memoryDecay hc L)
          (initialMemory hc.rhoM N Nstar
            (fun n => contrastExcessAtScale hP hStruct n))
          (memoryGridDrop
            (fun n => contrastExcessAtScale hP hStruct n) Nstar L) i := by
  have hF := contrastExcessAtScale_antitone_of_P4 hP hStruct hP4
  simpa [memoryGridContrast] using
    memoryGridContrast_weighted_sup_le_inv_mul_memory
      (hc := hc) (N := N) (Nstar := Nstar) (L := L) (i := i)
      (F := fun n => contrastExcessAtScale hP hStruct n)
      hi hNNstar hF

/-- Source label `e.H.recursion`: nonnegative memory from nonnegative data. -/
theorem memory_nonneg {q H0 : ℝ} {delta : ℕ → ℝ}
    (hq_nonneg : 0 ≤ q)
    (hH0_nonneg : 0 ≤ H0)
    (hdelta_nonneg : ∀ i, 0 ≤ delta i) :
    ∀ i, 0 ≤ memory q H0 delta i := by
  intro i
  induction i with
  | zero => exact hH0_nonneg
  | succ i ih =>
      rw [memory_succ]
      exact add_nonneg (mul_nonneg hq_nonneg ih)
        (mul_nonneg hq_nonneg (hdelta_nonneg (i + 1)))

/--
Source label `e.det.memory`: if `e.drift.general` controls each deterministic
drift by a contrast drop and the weighted contrast-drop supremum is bounded by
the memory numerator, then the weighted deterministic-drift supremum has the
same memory numerator divided by `1 + F_m`.
-/
theorem weighted_drift_sup_le_memory_of_drift_bound
    {N m : ℕ} (hNm : N ≤ m) {rhoM F_m C_D C_H H : ℝ}
    {D F : ℕ → ℝ}
    (hden_pos : 0 < 1 + F_m)
    (hC_D_nonneg : 0 ≤ C_D)
    (hD :
      ∀ j ∈ Finset.Icc N m,
        D j ≤ C_D * (F j - F_m) / (1 + F_m))
    (hdrop :
      (Finset.Icc N m).sup'
          ⟨N, Finset.mem_Icc.mpr ⟨le_rfl, hNm⟩⟩
          (fun j =>
            (3 : ℝ) ^ (-(rhoM * ((m - j : ℕ) : ℝ))) * (F j - F_m)) ≤
        C_H * H) :
    (Finset.Icc N m).sup'
        ⟨N, Finset.mem_Icc.mpr ⟨le_rfl, hNm⟩⟩
        (fun j => (3 : ℝ) ^ (-(rhoM * ((m - j : ℕ) : ℝ))) * D j) ≤
      (C_D * C_H) * H / (1 + F_m) := by
  classical
  let S := Finset.Icc N m
  let w : ℕ → ℝ := fun j => (3 : ℝ) ^ (-(rhoM * ((m - j : ℕ) : ℝ)))
  have hS_nonempty : S.Nonempty :=
    ⟨N, Finset.mem_Icc.mpr ⟨le_rfl, hNm⟩⟩
  have hfactor_nonneg : 0 ≤ C_D / (1 + F_m) := by
    positivity
  refine Finset.sup'_le hS_nonempty _ ?_
  intro j hj
  have hw_nonneg : 0 ≤ w j :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hD_scaled :
      w j * D j ≤ w j * (C_D * (F j - F_m) / (1 + F_m)) :=
    mul_le_mul_of_nonneg_left (hD j (by simpa [S] using hj)) hw_nonneg
  have hdrop_j :
      w j * (F j - F_m) ≤
        S.sup' hS_nonempty (fun j => w j * (F j - F_m)) :=
    Finset.le_sup' (f := fun j => w j * (F j - F_m)) hj
  have hdrop_j_mem :
      w j * (F j - F_m) ≤ C_H * H :=
    hdrop_j.trans (by simpa [S, w] using hdrop)
  calc
    w j * D j ≤ w j * (C_D * (F j - F_m) / (1 + F_m)) := hD_scaled
    _ = (C_D / (1 + F_m)) * (w j * (F j - F_m)) := by ring
    _ ≤ (C_D / (1 + F_m)) * (C_H * H) :=
        mul_le_mul_of_nonneg_left hdrop_j_mem hfactor_nonneg
    _ = (C_D * C_H) * H / (1 + F_m) := by ring

/--
Source label `e.det.memory`: specialization of the weighted-sup bridge to the
actual deterministic drift `D_{j,m}` and contrast excesses in the entry-scale
development.
-/
theorem terminalAnnealedFullBlockDrift_weightedSup_le_memory_of_contrastDrop_sup
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {N m : ℕ} (hNm : N ≤ m) {rhoM C_H H : ℝ}
    (hdrop :
      (Finset.Icc N m).sup'
          ⟨N, Finset.mem_Icc.mpr ⟨le_rfl, hNm⟩⟩
          (fun j =>
            (3 : ℝ) ^ (-(rhoM * ((m - j : ℕ) : ℝ))) *
              (contrastExcessAtScale hP hStruct j -
                contrastExcessAtScale hP hStruct m)) ≤
        C_H * H) :
    (Finset.Icc N m).sup'
        ⟨N, Finset.mem_Icc.mpr ⟨le_rfl, hNm⟩⟩
        (fun j =>
          (3 : ℝ) ^ (-(rhoM * ((m - j : ℕ) : ℝ))) *
            terminalAnnealedFullBlockDriftAtScales hP hStruct j m) ≤
      C_H * H / (1 + contrastExcessAtScale hP hStruct m) := by
  have hF_nonneg :
      0 ≤ contrastExcessAtScale hP hStruct m :=
    contrastExcessAtScale_nonneg_of_P4 hP hStruct hP4 m
  have hden_pos :
      0 < 1 + contrastExcessAtScale hP hStruct m := by
    linarith
  have hbridge :=
    weighted_drift_sup_le_memory_of_drift_bound
      (N := N) (m := m) hNm
      (rhoM := rhoM)
      (F_m := contrastExcessAtScale hP hStruct m)
      (C_D := 1) (C_H := C_H) (H := H)
      (D := fun j => terminalAnnealedFullBlockDriftAtScales hP hStruct j m)
      (F := fun j => contrastExcessAtScale hP hStruct j)
      hden_pos (by norm_num : (0 : ℝ) ≤ 1) ?_ hdrop
  · simpa using hbridge
  · intro j hj
    have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
    simpa [one_mul] using
      terminalAnnealedFullBlockDriftAtScales_le_contrastExcess_drop_div_of_P4
        hP hStruct hP4 hjm

/--
Source label `e.det.memory`: concrete weighted deterministic-drift supremum
paid by the memory variable at the grid endpoint `m_i`.
-/
theorem terminalAnnealedFullBlockDrift_weightedSup_le_memory_of_P4
    {d : ℕ} [NeZero d] (hc : HighContrastExponents d) {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {N Nstar L i : ℕ}
    (hi : 1 ≤ i)
    (hNNstar : N ≤ Nstar) :
    (Finset.Icc N (memoryGridScale Nstar L i)).sup'
        ⟨N, Finset.mem_Icc.mpr
          ⟨le_rfl, by
            exact hNNstar.trans
              (by
                dsimp [memoryGridScale]
                exact Nat.le_add_right Nstar (i * L))⟩⟩
        (fun j =>
          (3 : ℝ) ^
              (-(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ))) *
            terminalAnnealedFullBlockDriftAtScales hP hStruct j
              (memoryGridScale Nstar L i)) ≤
      ((memoryDecay hc L)⁻¹ *
        memory (memoryDecay hc L)
          (initialMemory hc.rhoM N Nstar
            (fun n => contrastExcessAtScale hP hStruct n))
          (memoryGridDrop
            (fun n => contrastExcessAtScale hP hStruct n) Nstar L) i) /
        (1 + contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) := by
  have hNm :
      N ≤ memoryGridScale Nstar L i :=
    hNNstar.trans (by
      dsimp [memoryGridScale]
      exact Nat.le_add_right Nstar (i * L))
  let Hmem : ℝ :=
    (memoryDecay hc L)⁻¹ *
      memory (memoryDecay hc L)
        (initialMemory hc.rhoM N Nstar
          (fun n => contrastExcessAtScale hP hStruct n))
        (memoryGridDrop
          (fun n => contrastExcessAtScale hP hStruct n) Nstar L) i
  have hdrop :
      (Finset.Icc N (memoryGridScale Nstar L i)).sup'
          ⟨N, Finset.mem_Icc.mpr ⟨le_rfl, hNm⟩⟩
          (fun j =>
            (3 : ℝ) ^
                (-(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ))) *
              (contrastExcessAtScale hP hStruct j -
                contrastExcessAtScale hP hStruct
                  (memoryGridScale Nstar L i))) ≤
        1 * Hmem := by
    dsimp [Hmem]
    simpa [one_mul] using
      contrastExcessAtScale_weighted_sup_le_inv_mul_memory_of_P4
        (hc := hc) (hP := hP) (hStruct := hStruct) (hP4 := hP4)
        (N := N) (Nstar := Nstar) (L := L) (i := i)
        hi hNNstar
  have hbridge :=
    terminalAnnealedFullBlockDrift_weightedSup_le_memory_of_contrastDrop_sup
      (hP := hP) (hStruct := hStruct) (hP4 := hP4)
      (N := N) (m := memoryGridScale Nstar L i)
      hNm
      (rhoM := hc.rhoM) (C_H := 1) (H := Hmem)
      hdrop
  simpa [Hmem, one_mul] using hbridge

end Homogenization.HighContrast.EntryScale
