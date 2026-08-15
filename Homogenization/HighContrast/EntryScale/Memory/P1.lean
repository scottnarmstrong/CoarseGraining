import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Homogenization.HighContrast.EntryScale.MomentConsequences

open scoped BigOperators


/-!
# Deterministic memory machinery

Planned home for the memory variable and deterministic maximal drift estimate.
-/


namespace Homogenization.HighContrast.EntryScale

variable {d : ℕ}

/-- Source label `s.memory`: grid scale `m_i = N_* + i L`. -/
def memoryGridScale (Nstar L i : ℕ) : ℕ :=
  Nstar + i * L

/-- Source label `s.memory`: grid scales are monotone in the grid index. -/
theorem memoryGridScale_le_of_le {Nstar L r i : ℕ} (hri : r ≤ i) :
    memoryGridScale Nstar L r ≤ memoryGridScale Nstar L i :=
  Nat.add_le_add_left (Nat.mul_le_mul_right L hri) Nstar

/-- Source label `s.memory`: positive block length makes consecutive positive
grid indices strictly increase. -/
theorem memoryGridScale_lt_of_pos_L {Nstar L i : ℕ}
    (hi : 1 ≤ i) (hL : 0 < L) :
    memoryGridScale Nstar L (i - 1) < memoryGridScale Nstar L i := by
  have hpred : i - 1 < i := by omega
  dsimp [memoryGridScale]
  exact Nat.add_lt_add_left (mul_lt_mul_of_pos_right hpred hL) Nstar

/-- Source label `s.memory`: consecutive positive grid points are separated by
exactly one block length. -/
theorem memoryGridScale_sub_prev_eq {Nstar L i : ℕ} (hi : 1 ≤ i) :
    memoryGridScale Nstar L i - memoryGridScale Nstar L (i - 1) = L := by
  have hscale_eq :
      memoryGridScale Nstar L i =
        memoryGridScale Nstar L (i - 1) + L := by
    dsimp [memoryGridScale]
    have hi_eq : i = (i - 1) + 1 := by omega
    have hmul_eq : i * L = (i - 1) * L + L := by
      calc
        i * L = ((i - 1) + 1) * L :=
          congrArg (fun n : ℕ => n * L) hi_eq
        _ = (i - 1) * L + 1 * L := by rw [Nat.add_mul]
        _ = (i - 1) * L + L := by rw [one_mul]
    rw [hmul_eq]
    omega
  rw [hscale_eq]
  exact Nat.add_sub_cancel_left (memoryGridScale Nstar L (i - 1)) L

/-- Source label `s.memory`: grid contrast value `F_i = F_{m_i}`. -/
def memoryGridContrast (F : ℕ → ℝ) (Nstar L i : ℕ) : ℝ :=
  F (memoryGridScale Nstar L i)

/-- Source label `s.memory`: grid drop `Δ_i = F_{i-1} - F_i` for `i >= 1`. -/
def memoryGridDrop (F : ℕ → ℝ) (Nstar L : ℕ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => memoryGridContrast F Nstar L i - memoryGridContrast F Nstar L (i + 1)

@[simp]
theorem memoryGridDrop_zero (F : ℕ → ℝ) (Nstar L : ℕ) :
    memoryGridDrop F Nstar L 0 = 0 :=
  rfl

@[simp]
theorem memoryGridDrop_succ (F : ℕ → ℝ) (Nstar L i : ℕ) :
    memoryGridDrop F Nstar L (i + 1) =
      memoryGridContrast F Nstar L i - memoryGridContrast F Nstar L (i + 1) :=
  rfl

/-- Source label `s.memory`: at positive indices, the grid drop is
`F_{i-1} - F_i`. -/
theorem memoryGridDrop_eq_contrast_sub
    (F : ℕ → ℝ) (Nstar L i : ℕ) (hi : 1 ≤ i) :
    memoryGridDrop F Nstar L i =
      memoryGridContrast F Nstar L (i - 1) -
        memoryGridContrast F Nstar L i := by
  have hi_eq : i = (i - 1) + 1 := by omega
  conv_lhs => rw [hi_eq]
  rw [memoryGridDrop_succ]
  rw [hi_eq]
  have hpred : i - 1 + 1 - 1 = i - 1 := by omega
  have hsucc : i - 1 + 1 = i := by omega
  rw [hpred, hsucc]

/-- Source label `s.memory`: grid drops are nonnegative when contrast decreases. -/
theorem memoryGridDrop_succ_nonneg_of_antitone
    {F : ℕ → ℝ} (hF : Antitone F) (Nstar L i : ℕ) :
    0 ≤ memoryGridDrop F Nstar L (i + 1) := by
  dsimp [memoryGridDrop, memoryGridContrast, memoryGridScale]
  have hscale :
      Nstar + i * L ≤ Nstar + (i + 1) * L :=
    Nat.add_le_add_left (Nat.mul_le_mul_right L (Nat.le_succ i)) Nstar
  have hmono := hF hscale
  linarith

/-- Source label `s.memory`: memory decay factor `q = 3^{-kappa_H L}`, where
`kappa_H = min{rho_M, beta, beta_edge}` is the realized memory decay rate. -/
noncomputable def memoryDecay (hc : HighContrastExponents d) (L : ℕ) : ℝ :=
  (3 : ℝ) ^ (-(hc.kappaH * (L : ℝ)))

/-- Source label `s.memory`: the memory decay factor is positive. -/
theorem memoryDecay_pos (hc : HighContrastExponents d) (L : ℕ) :
    0 < memoryDecay hc L := by
  rw [memoryDecay]
  exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _

/-- Source label `s.memory`: the memory decay factor is at most one. -/
theorem memoryDecay_le_one (hc : HighContrastExponents d) (L : ℕ) :
    memoryDecay hc L ≤ 1 := by
  rw [memoryDecay]
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by norm_num : (1 : ℝ) ≤ 3)
    (by
      have hnonneg :
          0 ≤ hc.kappaH * (L : ℝ) :=
        mul_nonneg (le_of_lt hc.kappaH_pos) (Nat.cast_nonneg L)
      linarith)

/--
Source label `s.memory`: powers of `q = 3^{-kappa_H L}` agree with the
corresponding triadic scale gap.
-/
theorem memoryDecay_pow_eq_grid_gap (hc : HighContrastExponents d) (L n : ℕ) :
    memoryDecay hc L ^ n =
      (3 : ℝ) ^ (-(hc.kappaH * ((n * L : ℕ) : ℝ))) := by
  rw [memoryDecay]
  calc
    ((3 : ℝ) ^ (-(hc.kappaH * (L : ℝ)))) ^ n =
        (3 : ℝ) ^ (-(hc.kappaH * (L : ℝ)) * (n : ℝ)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    _ = (3 : ℝ) ^ (-(hc.kappaH * ((n * L : ℕ) : ℝ))) := by
      congr 1
      rw [Nat.cast_mul]
      ring

/-- Source label `s.memory`: the block decay is the corresponding power of
the one-step decay. -/
theorem memoryDecay_eq_one_pow (hc : HighContrastExponents d) (L : ℕ) :
    memoryDecay hc L = memoryDecay hc 1 ^ L := by
  rw [memoryDecay_pow_eq_grid_gap, memoryDecay]
  simp only [Nat.mul_one]

/-- Source label `s.memory`: one block of memory decay is strictly contracting. -/
theorem memoryDecay_one_lt_one (hc : HighContrastExponents d) :
    memoryDecay hc 1 < 1 := by
  rw [memoryDecay]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by norm_num : (1 : ℝ) < 3)
    (by
      simpa only [Nat.cast_one, mul_one] using
        neg_neg_of_pos hc.kappaH_pos)

/--
Source label `s.memory`: by taking the fixed memory block length large enough,
the decay factor `q = 3^{-rho_M L}` is below any positive scalar threshold.
-/
theorem exists_memoryDecay_le_of_pos
    (hc : HighContrastExponents d) {qMax : ℝ} (hqMax_pos : 0 < qMax) :
    ∃ L : ℕ, memoryDecay hc L ≤ qMax := by
  obtain ⟨L, hL⟩ :=
    exists_pow_lt_of_lt_one (x := qMax) (y := memoryDecay hc 1)
      hqMax_pos (memoryDecay_one_lt_one hc)
  refine ⟨L, ?_⟩
  rw [memoryDecay_eq_one_pow]
  exact le_of_lt hL

/-- Source label `s.memory`: the memory decay decreases as the block length grows. -/
theorem memoryDecay_antitone (hc : HighContrastExponents d) :
    Antitone (memoryDecay hc) := by
  intro L L' hLL'
  calc
    memoryDecay hc L' = memoryDecay hc 1 ^ L' :=
      memoryDecay_eq_one_pow hc L'
    _ ≤ memoryDecay hc 1 ^ L :=
      pow_le_pow_of_le_one
        (le_of_lt (memoryDecay_pos hc 1)) (memoryDecay_le_one hc 1) hLL'
    _ = memoryDecay hc L := (memoryDecay_eq_one_pow hc L).symm

/-- Source label `p.nodrop.CR`: response-side block decay `3^{-beta L}`. -/
noncomputable def noDropResponseDecay (hc : HighContrastExponents d) (L : ℕ) : ℝ :=
  (3 : ℝ) ^ (-(hc.beta * (L : ℝ)))

/-- Source label `p.nodrop.CR`: response-side block decay is positive. -/
theorem noDropResponseDecay_pos (hc : HighContrastExponents d) (L : ℕ) :
    0 < noDropResponseDecay hc L := by
  rw [noDropResponseDecay]
  exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _

/-- Source label `p.nodrop.CR`: response-side block decay is at most one. -/
theorem noDropResponseDecay_le_one (hc : HighContrastExponents d) (L : ℕ) :
    noDropResponseDecay hc L ≤ 1 := by
  rw [noDropResponseDecay]
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by norm_num : (1 : ℝ) ≤ 3)
    (by
      have hnonneg :
          0 ≤ hc.beta * (L : ℝ) :=
        mul_nonneg (le_of_lt hc.beta_pos) (Nat.cast_nonneg L)
      linarith)

/--
Source label `p.nodrop.CR`: powers of the response-side block decay agree with
the corresponding triadic scale gap.
-/
theorem noDropResponseDecay_pow_eq_grid_gap
    (hc : HighContrastExponents d) (L n : ℕ) :
    noDropResponseDecay hc L ^ n =
      (3 : ℝ) ^ (-(hc.beta * ((n * L : ℕ) : ℝ))) := by
  rw [noDropResponseDecay]
  calc
    ((3 : ℝ) ^ (-(hc.beta * (L : ℝ)))) ^ n =
        (3 : ℝ) ^ (-(hc.beta * (L : ℝ)) * (n : ℝ)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    _ = (3 : ℝ) ^ (-(hc.beta * ((n * L : ℕ) : ℝ))) := by
      congr 1
      rw [Nat.cast_mul]
      ring

/-- Source label `p.nodrop.CR`: the response-side block decay is the
corresponding power of the one-step response decay. -/
theorem noDropResponseDecay_eq_one_pow (hc : HighContrastExponents d) (L : ℕ) :
    noDropResponseDecay hc L = noDropResponseDecay hc 1 ^ L := by
  rw [noDropResponseDecay_pow_eq_grid_gap, noDropResponseDecay]
  simp only [Nat.mul_one]

/-- Source label `p.nodrop.CR`: one response-side block is strictly contracting. -/
theorem noDropResponseDecay_one_lt_one (hc : HighContrastExponents d) :
    noDropResponseDecay hc 1 < 1 := by
  rw [noDropResponseDecay]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by norm_num : (1 : ℝ) < 3)
    (by
      simpa only [Nat.cast_one, mul_one] using
        neg_neg_of_pos hc.beta_pos)

/--
Source label `p.nodrop.CR`: by taking the fixed response block length large
enough, the beta-decay factor `3^{-beta L}` is below any positive threshold.
-/
theorem exists_noDropResponseDecay_le_of_pos
    (hc : HighContrastExponents d) {x : ℝ} (hx_pos : 0 < x) :
    ∃ L : ℕ, noDropResponseDecay hc L ≤ x := by
  obtain ⟨L, hL⟩ :=
    exists_pow_lt_of_lt_one (x := x) (y := noDropResponseDecay hc 1)
      hx_pos (noDropResponseDecay_one_lt_one hc)
  refine ⟨L, ?_⟩
  rw [noDropResponseDecay_eq_one_pow]
  exact le_of_lt hL

/-- Source label `p.nodrop.CR`: the response-side beta decay decreases as the
block length grows. -/
theorem noDropResponseDecay_antitone (hc : HighContrastExponents d) :
    Antitone (noDropResponseDecay hc) := by
  intro L L' hLL'
  calc
    noDropResponseDecay hc L' = noDropResponseDecay hc 1 ^ L' :=
      noDropResponseDecay_eq_one_pow hc L'
    _ ≤ noDropResponseDecay hc 1 ^ L :=
      pow_le_pow_of_le_one
        (le_of_lt (noDropResponseDecay_pos hc 1))
        (noDropResponseDecay_le_one hc 1) hLL'
    _ = noDropResponseDecay hc L := (noDropResponseDecay_eq_one_pow hc L).symm

/--
Source labels `s.memory`, `p.nodrop.CR`, and `l.lyapunov`: one enlarged memory
block length can make both the response-side beta decay and the Lyapunov memory
decay smaller than prescribed positive thresholds.
-/
theorem exists_memoryDecay_and_noDropResponseDecay_le_of_pos
    (hc : HighContrastExponents d) {qMax x : ℝ}
    (hqMax_pos : 0 < qMax) (hx_pos : 0 < x) :
    ∃ L : ℕ, 0 < L ∧
      memoryDecay hc L ≤ qMax ∧ noDropResponseDecay hc L ≤ x := by
  obtain ⟨Lmem, hLmem⟩ := exists_memoryDecay_le_of_pos hc hqMax_pos
  obtain ⟨Lresp, hLresp⟩ := exists_noDropResponseDecay_le_of_pos hc hx_pos
  refine ⟨max 1 (max Lmem Lresp), ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 (max Lmem Lresp))
  · have hLmem_le : Lmem ≤ max 1 (max Lmem Lresp) :=
      (Nat.le_max_left Lmem Lresp).trans
        (Nat.le_max_right 1 (max Lmem Lresp))
    exact ((memoryDecay_antitone hc) hLmem_le).trans hLmem
  · have hLresp_le : Lresp ≤ max 1 (max Lmem Lresp) :=
      (Nat.le_max_right Lmem Lresp).trans
        (Nat.le_max_right 1 (max Lmem Lresp))
    exact ((noDropResponseDecay_antitone hc) hLresp_le).trans hLresp

/--
Source label `e.H0.memory`: pre-start deterministic memory between the
high-moment threshold `N` and the first grid point `N_*`.
-/
noncomputable def initialMemory (rhoM : ℝ) (N Nstar : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ ell ∈ Finset.Icc (N + 1) Nstar,
    (3 : ℝ) ^ (-(rhoM * ((Nstar - ell : ℕ) : ℝ))) *
      (F (ell - 1) - F ell)

/-- Source label `e.H0.memory`: the pre-start memory is nonnegative. -/
theorem initialMemory_nonneg_of_antitone
    {rhoM : ℝ} {N Nstar : ℕ} {F : ℕ → ℝ} (hF : Antitone F) :
    0 ≤ initialMemory rhoM N Nstar F := by
  rw [initialMemory]
  refine Finset.sum_nonneg ?_
  intro ell _
  have hweight_nonneg :
      0 ≤ (3 : ℝ) ^ (-(rhoM * ((Nstar - ell : ℕ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hdrop_nonneg : 0 ≤ F (ell - 1) - F ell := by
    have hmono := hF (Nat.sub_le ell 1)
    linarith
  exact mul_nonneg hweight_nonneg hdrop_nonneg

/-- Recursive deterministic memory variable.

Source labels: `e.H.memory` and `e.H.recursion`.  The closed-form sum in the
TeX note is equivalent to this recursion and will be connected later when the
pre-start buffer sum is formalized.
-/
def memory (q H0 : ℝ) (delta : ℕ → ℝ) : ℕ → ℝ
  | 0 => H0
  | i + 1 => q * memory q H0 delta i + q * delta (i + 1)

/-- Source label `e.H.recursion`: first recursive memory identity. -/
@[simp]
theorem memory_succ (q H0 : ℝ) (delta : ℕ → ℝ) (i : ℕ) :
    memory q H0 delta (i + 1) =
      q * memory q H0 delta i + q * delta (i + 1) :=
  rfl

/--
Source label `e.H.recursion`: the important `q⁻¹` identity
`q⁻¹ H_i = H_{i-1} + Δ_i`.
-/
theorem inv_mul_memory_succ (q H0 : ℝ) (delta : ℕ → ℝ) (i : ℕ)
    (hq : q ≠ 0) :
    q⁻¹ * memory q H0 delta (i + 1) =
      memory q H0 delta i + delta (i + 1) := by
  rw [memory_succ]
  field_simp [hq]

/--
Source label `e.H.recursion`: memory-grid form of
`H_i = q H_{i-1} + q Δ_i`, with
`Δ_i = F_{i-1} - F_i` for `i >= 1`.
-/
theorem memoryGrid_memory_step_eq
    (q H0 : ℝ) (F : ℕ → ℝ) (Nstar L i : ℕ) (hi : 1 ≤ i) :
    memory q H0 (memoryGridDrop F Nstar L) i =
      q * memory q H0 (memoryGridDrop F Nstar L) (i - 1) +
        q * (memoryGridContrast F Nstar L (i - 1) -
          memoryGridContrast F Nstar L i) := by
  have hi_eq : i = (i - 1) + 1 := by omega
  conv_lhs => rw [hi_eq]
  rw [memory_succ, memoryGridDrop_succ]
  rw [hi_eq]
  have hpred : i - 1 + 1 - 1 = i - 1 := by omega
  have hsucc : i - 1 + 1 = i := by omega
  rw [hpred, hsucc]

/--
Source label `e.H.memory`: one-based form of the closed memory sum, matching
the manuscript index `r = 1, ..., i`.
-/
theorem memory_eq_closed_form_one_based (q H0 : ℝ) (delta : ℕ → ℝ) :
    ∀ i : ℕ,
      memory q H0 delta i =
        q ^ i * H0 +
          ∑ a ∈ Finset.Icc 1 i, q ^ (i - a + 1) * delta a := by
  intro i
  induction i with
  | zero =>
      simp [memory]
  | succ i ih =>
      rw [memory_succ, ih]
      have hsum :
          q * (∑ a ∈ Finset.Icc 1 i, q ^ (i - a + 1) * delta a) =
            ∑ a ∈ Finset.Icc 1 i, q ^ (i + 1 - a + 1) * delta a := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro a ha
        have ha_bounds := Finset.mem_Icc.mp ha
        have hexp : i + 1 - a + 1 = i - a + 1 + 1 := by omega
        rw [hexp, pow_succ]
        ring
      have htop : i + 1 - (i + 1) + 1 = 1 := by omega
      calc
        q * (q ^ i * H0 + ∑ a ∈ Finset.Icc 1 i, q ^ (i - a + 1) * delta a) +
            q * delta (i + 1)
            = q ^ (i + 1) * H0 +
                q * (∑ a ∈ Finset.Icc 1 i, q ^ (i - a + 1) * delta a) +
                q * delta (i + 1) := by
              rw [pow_succ]
              ring
        _ = q ^ (i + 1) * H0 +
              (∑ a ∈ Finset.Icc 1 i, q ^ (i + 1 - a + 1) * delta a) +
              q * delta (i + 1) := by
              rw [hsum]
        _ = q ^ (i + 1) * H0 +
              ∑ a ∈ Finset.Icc 1 (i + 1), q ^ (i + 1 - a + 1) * delta a := by
              rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ i + 1)]
              rw [htop, pow_one]
              ring

private theorem finset_sum_le_sum_of_subset_nonneg
    {ι : Type*} [DecidableEq ι] {s t : Finset ι} {f : ι → ℝ}
    (hst : s ⊆ t) (hf_nonneg : ∀ x ∈ t, 0 ≤ f x) :
    ∑ x ∈ s, f x ≤ ∑ x ∈ t, f x := by
  have hsum := Finset.sum_sdiff hst (f := f)
  have hsdiff_nonneg : 0 ≤ ∑ x ∈ t \ s, f x := by
    refine Finset.sum_nonneg ?_
    intro x hx
    exact hf_nonneg x (Finset.sdiff_subset hx)
  linarith

/--
Source label `e.H0.memory`: any tail of the pre-start drop sum is bounded by
the full initial memory `H_0`.
-/
theorem initialMemory_tail_le_initialMemory
    {rhoM : ℝ} {N Nstar j : ℕ} {F : ℕ → ℝ}
    (hNj : N ≤ j) (hF : Antitone F) :
    ∑ ell ∈ Finset.Icc (j + 1) Nstar,
        (3 : ℝ) ^ (-(rhoM * ((Nstar - ell : ℕ) : ℝ))) *
          (F (ell - 1) - F ell) ≤
      initialMemory rhoM N Nstar F := by
  rw [initialMemory]
  refine finset_sum_le_sum_of_subset_nonneg ?_ ?_
  · intro ell hell
    have hell_bounds := Finset.mem_Icc.mp hell
    exact Finset.mem_Icc.mpr ⟨by omega, hell_bounds.2⟩
  · intro ell _hell
    have hweight_nonneg :
        0 ≤ (3 : ℝ) ^ (-(rhoM * ((Nstar - ell : ℕ) : ℝ))) :=
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
    have hdrop_nonneg : 0 ≤ F (ell - 1) - F ell := by
      have hmono := hF (Nat.sub_le ell 1)
      linarith
    exact mul_nonneg hweight_nonneg hdrop_nonneg

/--
Source label `e.H.memory`: the weighted one-based tail
`sum_{a=r}^i q^{i-a} Delta_a` is bounded by `q^{-1} H_i`.
-/
theorem memory_weighted_tail_sum_le_inv_mul_memory
    {q H0 : ℝ} {delta : ℕ → ℝ} {r i : ℕ}
    (hq_pos : 0 < q)
    (hH0_nonneg : 0 ≤ H0)
    (hdelta_nonneg : ∀ a, 0 ≤ delta a)
    (hr_pos : 1 ≤ r) :
    ∑ a ∈ Finset.Icc r i, q ^ (i - a) * delta a ≤
      q⁻¹ * memory q H0 delta i := by
  let tail : ℝ := ∑ a ∈ Finset.Icc r i, q ^ (i - a) * delta a
  have hq_tail :
      q * tail =
        ∑ a ∈ Finset.Icc r i, q ^ (i - a + 1) * delta a := by
    dsimp [tail]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro a ha
    rw [pow_succ]
    ring
  have htail_le_memory :
      ∑ a ∈ Finset.Icc r i, q ^ (i - a + 1) * delta a ≤
        memory q H0 delta i := by
    rw [memory_eq_closed_form_one_based q H0 delta i]
    have hsub : Finset.Icc r i ⊆ Finset.Icc 1 i := by
      intro a ha
      have ha_bounds := Finset.mem_Icc.mp ha
      exact Finset.mem_Icc.mpr ⟨le_trans hr_pos ha_bounds.1, ha_bounds.2⟩
    have hfull_nonneg :
        ∀ a ∈ Finset.Icc 1 i, 0 ≤ q ^ (i - a + 1) * delta a := by
      intro a _ha
      exact mul_nonneg (pow_nonneg (le_of_lt hq_pos) _) (hdelta_nonneg a)
    have hsubsum :
        ∑ a ∈ Finset.Icc r i, q ^ (i - a + 1) * delta a ≤
          ∑ a ∈ Finset.Icc 1 i, q ^ (i - a + 1) * delta a :=
      finset_sum_le_sum_of_subset_nonneg hsub hfull_nonneg
    have hinit_nonneg : 0 ≤ q ^ i * H0 :=
      mul_nonneg (pow_nonneg (le_of_lt hq_pos) _) hH0_nonneg
    linarith
  have hq_tail_le : q * tail ≤ memory q H0 delta i := by
    rw [hq_tail]
    exact htail_le_memory
  have hq_inv_nonneg : 0 ≤ q⁻¹ :=
    inv_nonneg.mpr (le_of_lt hq_pos)
  calc
    (∑ a ∈ Finset.Icc r i, q ^ (i - a) * delta a) = tail := rfl
    _ = q⁻¹ * (q * tail) := by
          field_simp [ne_of_gt hq_pos]
    _ ≤ q⁻¹ * memory q H0 delta i :=
          mul_le_mul_of_nonneg_left hq_tail_le hq_inv_nonneg

/--
Source label `l.det.memory`: the pre-start contribution
`q^i H_0` plus the post-start weighted grid tail is bounded by `q^{-1} H_i`.
-/
theorem memory_initial_pow_add_weighted_tail_le_inv_mul_memory
    {q H0 : ℝ} {delta : ℕ → ℝ} {i : ℕ}
    (hq_pos : 0 < q) (hq_le_one : q ≤ 1)
    (hH0_nonneg : 0 ≤ H0)
    (hi : 1 ≤ i) :
    q ^ i * H0 +
        ∑ a ∈ Finset.Icc 1 i, q ^ (i - a) * delta a ≤
      q⁻¹ * memory q H0 delta i := by
  have hq_nonneg : 0 ≤ q := le_of_lt hq_pos
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hmem := memory_eq_closed_form_one_based q H0 delta i
  have hinit_inv :
      q⁻¹ * (q ^ i * H0) = q ^ (i - 1) * H0 := by
    have hcancel : q⁻¹ * q = 1 := inv_mul_cancel₀ hq_ne
    have hpow_i : q ^ i = q ^ (i - 1) * q := by
      calc
        q ^ i = q ^ (i - 1 + 1) := by
          congr 1
          omega
        _ = q ^ (i - 1) * q := by
          rw [pow_succ]
    calc
      q⁻¹ * (q ^ i * H0) =
          q⁻¹ * (q ^ (i - 1) * q * H0) := by
            rw [hpow_i]
      _ = (q⁻¹ * q) * (q ^ (i - 1) * H0) := by ring
      _ = q ^ (i - 1) * H0 := by rw [hcancel, one_mul]
  have hsum_inv :
      q⁻¹ *
          (∑ a ∈ Finset.Icc 1 i, q ^ (i - a + 1) * delta a) =
        ∑ a ∈ Finset.Icc 1 i, q ^ (i - a) * delta a := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro a ha
    rw [pow_succ]
    field_simp [hq_ne]
  have hinit_le :
      q ^ i * H0 ≤ q ^ (i - 1) * H0 := by
    have hpow : q ^ i ≤ q ^ (i - 1) :=
      pow_le_pow_of_le_one hq_nonneg hq_le_one (by omega : i - 1 ≤ i)
    exact mul_le_mul_of_nonneg_right hpow hH0_nonneg
  calc
    q ^ i * H0 + ∑ a ∈ Finset.Icc 1 i, q ^ (i - a) * delta a
        ≤ q ^ (i - 1) * H0 +
            ∑ a ∈ Finset.Icc 1 i, q ^ (i - a) * delta a :=
          by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right hinit_le
                (∑ a ∈ Finset.Icc 1 i, q ^ (i - a) * delta a)
    _ = q⁻¹ * (q ^ i * H0) +
          q⁻¹ * (∑ a ∈ Finset.Icc 1 i, q ^ (i - a + 1) * delta a) := by
          rw [hinit_inv, hsum_inv]
    _ = q⁻¹ *
          (q ^ i * H0 +
            ∑ a ∈ Finset.Icc 1 i, q ^ (i - a + 1) * delta a) := by
          ring
    _ = q⁻¹ * memory q H0 delta i := by
          rw [hmem]

/--
Source label `l.det.memory`: if `0 < q <= 1`, the grid-block factor
`q^(i-r)` may be inserted into the unweighted tail and then absorbed by
`q^{-1} H_i`.
-/
theorem memory_unweighted_tail_mul_pow_le_inv_mul_memory
    {q H0 : ℝ} {delta : ℕ → ℝ} {r i : ℕ}
    (hq_pos : 0 < q) (hq_le_one : q ≤ 1)
    (hH0_nonneg : 0 ≤ H0)
    (hdelta_nonneg : ∀ a, 0 ≤ delta a)
    (hr_pos : 1 ≤ r) :
    q ^ (i - r) * (∑ a ∈ Finset.Icc r i, delta a) ≤
      q⁻¹ * memory q H0 delta i := by
  have hweighted :
      ∑ a ∈ Finset.Icc r i, q ^ (i - a) * delta a ≤
        q⁻¹ * memory q H0 delta i :=
    memory_weighted_tail_sum_le_inv_mul_memory hq_pos hH0_nonneg
      hdelta_nonneg hr_pos
  have hinsert :
      q ^ (i - r) * (∑ a ∈ Finset.Icc r i, delta a) ≤
        ∑ a ∈ Finset.Icc r i, q ^ (i - a) * delta a := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro a ha
    have ha_bounds := Finset.mem_Icc.mp ha
    have hexp : i - a ≤ i - r := by omega
    have hpow :
        q ^ (i - r) ≤ q ^ (i - a) :=
      pow_le_pow_of_le_one (le_of_lt hq_pos) hq_le_one hexp
    exact mul_le_mul_of_nonneg_right hpow (hdelta_nonneg a)
  exact hinsert.trans hweighted

/--
Source label `l.det.memory`: the previous scalar tail estimate applied to the
grid drops `Delta_a = F_{a-1} - F_a`.
-/
theorem memoryGridDrop_tail_mul_pow_le_inv_mul_memory
    {q H0 : ℝ} {F : ℕ → ℝ} {Nstar L r i : ℕ}
    (hq_pos : 0 < q) (hq_le_one : q ≤ 1)
    (hH0_nonneg : 0 ≤ H0)
    (hF : Antitone F)
    (hr_pos : 1 ≤ r) :
    q ^ (i - r) *
        (∑ a ∈ Finset.Icc r i, memoryGridDrop F Nstar L a) ≤
      q⁻¹ * memory q H0 (memoryGridDrop F Nstar L) i := by
  exact memory_unweighted_tail_mul_pow_le_inv_mul_memory hq_pos hq_le_one
    hH0_nonneg
    (fun a => by
      cases a with
      | zero => simp
      | succ a =>
          exact memoryGridDrop_succ_nonneg_of_antitone hF Nstar L a)
    hr_pos

/--
Source label `l.det.memory`: finite telescoping of the grid drops
`Delta_a = F_{a-1} - F_a`.
-/
theorem memoryGridDrop_sum_Icc_eq_contrast_sub
    (F : ℕ → ℝ) (Nstar L r i : ℕ)
    (hr_pos : 1 ≤ r) (hri : r ≤ i) :
    ∑ a ∈ Finset.Icc r i, memoryGridDrop F Nstar L a =
      memoryGridContrast F Nstar L (r - 1) -
        memoryGridContrast F Nstar L i := by
  induction i generalizing r with
  | zero =>
      omega
  | succ i ih =>
      by_cases hri' : r ≤ i
      · rw [Finset.sum_Icc_succ_top (by omega : r ≤ i + 1)]
        rw [ih r hr_pos hri']
        rw [memoryGridDrop_succ]
        ring
      · have hr_eq : r = i + 1 := by omega
        subst r
        rw [Finset.Icc_self, Finset.sum_singleton]
        rw [memoryGridDrop_succ]
        have hpred : i + 1 - 1 = i := by omega
        rw [hpred]

/--
Source label `l.det.memory`: finite telescoping of the ordinary pre-start
drops `F_{ell-1} - F_ell`.
-/
theorem prestartDrop_sum_Icc_eq_sub (F : ℕ → ℝ) {j Nstar : ℕ}
    (hj : j ≤ Nstar) :
    ∑ ell ∈ Finset.Icc (j + 1) Nstar, (F (ell - 1) - F ell) =
      F j - F Nstar := by
  induction Nstar generalizing j with
  | zero =>
      have hj_zero : j = 0 := by omega
      subst j
      simp
  | succ Nstar ih =>
      by_cases hjN : j ≤ Nstar
      · rw [Finset.sum_Icc_succ_top (by omega : j + 1 ≤ Nstar + 1)]
        rw [ih hjN]
        have hpred : Nstar + 1 - 1 = Nstar := by omega
        rw [hpred]
        ring
      · have hj_top : j = Nstar + 1 := by omega
        subst j
        simp

/--
Source label `e.H0.memory`: the pre-start memory is bounded by the starting
contrast when the contrast sequence is nonincreasing and nonnegative.
-/
theorem initialMemory_le_start_of_antitone_nonneg
    {rhoM : ℝ} (hrhoM_pos : 0 < rhoM) {N Nstar : ℕ} {F : ℕ → ℝ}
    (hNNstar : N ≤ Nstar)
    (hF_antitone : Antitone F)
    (hF_nonneg : ∀ n, 0 ≤ F n) :
    initialMemory rhoM N Nstar F ≤ F N := by
  have hweighted_le_unweighted :
      initialMemory rhoM N Nstar F ≤
        ∑ ell ∈ Finset.Icc (N + 1) Nstar, (F (ell - 1) - F ell) := by
    rw [initialMemory]
    refine Finset.sum_le_sum ?_
    intro ell hell
    have hdrop_nonneg : 0 ≤ F (ell - 1) - F ell := by
      have hmono := hF_antitone (Nat.sub_le ell 1)
      linarith
    have hweight_le_one :
        (3 : ℝ) ^ (-(rhoM * ((Nstar - ell : ℕ) : ℝ))) ≤ 1 := by
      exact Real.rpow_le_one_of_one_le_of_nonpos
        (by norm_num : (1 : ℝ) ≤ 3)
        (by
          have hmul_nonneg :
              0 ≤ rhoM * ((Nstar - ell : ℕ) : ℝ) :=
            mul_nonneg (le_of_lt hrhoM_pos) (Nat.cast_nonneg _)
          linarith)
    calc
      (3 : ℝ) ^ (-(rhoM * ((Nstar - ell : ℕ) : ℝ))) *
          (F (ell - 1) - F ell)
          ≤ 1 * (F (ell - 1) - F ell) :=
            mul_le_mul_of_nonneg_right hweight_le_one hdrop_nonneg
      _ = F (ell - 1) - F ell := by ring
  have htel :
      ∑ ell ∈ Finset.Icc (N + 1) Nstar, (F (ell - 1) - F ell) =
        F N - F Nstar :=
    prestartDrop_sum_Icc_eq_sub F hNNstar
  calc
    initialMemory rhoM N Nstar F
        ≤ ∑ ell ∈ Finset.Icc (N + 1) Nstar, (F (ell - 1) - F ell) :=
          hweighted_le_unweighted
    _ = F N - F Nstar := htel
    _ ≤ F N := by
          have hnonneg := hF_nonneg Nstar
          linarith

/--
Source label `e.H0.memory`: concrete initial memory bound by the corrected
initial contrast budget `T = widetildeTheta_0`.
-/
theorem initialMemory_contrastExcessAtScale_le_initialWidetildeTheta_of_P4
    {d : ℕ} [NeZero d] (hc : HighContrastExponents d) {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {N Nstar : ℕ}
    (hNNstar : N ≤ Nstar) :
    initialMemory hc.rhoM N Nstar
        (fun n => contrastExcessAtScale hP hStruct n) ≤
      Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 := by
  have hF_antitone :
      Antitone (fun n => contrastExcessAtScale hP hStruct n) :=
    contrastExcessAtScale_antitone_of_P4 hP hStruct hP4
  have hF_nonneg :
      ∀ n, 0 ≤ contrastExcessAtScale hP hStruct n := by
    intro n
    exact contrastExcessAtScale_nonneg_of_P4 hP hStruct hP4 n
  have hH_start :
      initialMemory hc.rhoM N Nstar
          (fun n => contrastExcessAtScale hP hStruct n) ≤
        contrastExcessAtScale hP hStruct N :=
    initialMemory_le_start_of_antitone_nonneg hc.rhoM_pos hNNstar
      hF_antitone hF_nonneg
  have htheta :
      Homogenization.Book.Ch05.thetaAtScale hP hStruct (N : ℤ) ≤
        Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 :=
    thetaAtScale_le_initialWidetildeTheta_of_P4 hP hStruct hP4 N
  have hF_le :
      contrastExcessAtScale hP hStruct N ≤
        Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 := by
    change Homogenization.Book.Ch05.thetaAtScale hP hStruct (N : ℤ) - 1 ≤
      Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4
    linarith
  exact hH_start.trans hF_le

/--
Source label `l.det.memory`: for `j <= N_*`, decompose `F_j - F_i` into the
pre-start drops plus all post-start grid drops.
-/
theorem sub_memoryGridContrast_eq_prestartDrop_sum_add_gridDrop_sum
    (F : ℕ → ℝ) {Nstar L j i : ℕ}
    (hj : j ≤ Nstar) (hi : 1 ≤ i) :
    F j - memoryGridContrast F Nstar L i =
      (∑ ell ∈ Finset.Icc (j + 1) Nstar, (F (ell - 1) - F ell)) +
        ∑ a ∈ Finset.Icc 1 i, memoryGridDrop F Nstar L a := by
  have hpre := prestartDrop_sum_Icc_eq_sub F hj
  have hgrid :=
    memoryGridDrop_sum_Icc_eq_contrast_sub F Nstar L 1 i
      (by omega : 1 ≤ 1) hi
  have hgrid' :
      ∑ a ∈ Finset.Icc 1 i, memoryGridDrop F Nstar L a =
        F Nstar - memoryGridContrast F Nstar L i := by
    simpa [memoryGridContrast, memoryGridScale] using hgrid
  calc
    F j - memoryGridContrast F Nstar L i =
        (F j - F Nstar) + (F Nstar - memoryGridContrast F Nstar L i) := by
          ring
    _ =
        (∑ ell ∈ Finset.Icc (j + 1) Nstar, (F (ell - 1) - F ell)) +
          ∑ a ∈ Finset.Icc 1 i, memoryGridDrop F Nstar L a := by
          rw [← hpre, ← hgrid']

/--
Source label `l.det.memory`: on the pre-start range, the source weight is
bounded termwise by `q^i` times the initial-memory weight.
-/
theorem memoryGridWeight_le_memoryDecay_pow_mul_initialWeight_of_prestart
    (hc : HighContrastExponents d) {Nstar L i j ell : ℕ}
    (hjell : j ≤ ell) (hell : ell ≤ Nstar) :
    (3 : ℝ) ^
        (-(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ))) ≤
      memoryDecay hc L ^ i *
        (3 : ℝ) ^ (-(hc.rhoM * ((Nstar - ell : ℕ) : ℝ))) := by
  have hgap_nat :
      i * L + (Nstar - ell) ≤ memoryGridScale Nstar L i - j := by
    dsimp [memoryGridScale]
    omega
  have hgap_real :
      ((i * L + (Nstar - ell) : ℕ) : ℝ) ≤
        ((memoryGridScale Nstar L i - j : ℕ) : ℝ) := by
    exact_mod_cast hgap_nat
  have hmul_le :
      hc.rhoM * ((i * L + (Nstar - ell) : ℕ) : ℝ) ≤
        hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hgap_real (le_of_lt hc.rhoM_pos)
  have hexp_le :
      -(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ)) ≤
        -(hc.rhoM * ((i * L + (Nstar - ell) : ℕ) : ℝ)) := by
    linarith
  -- `memoryDecay hc L ^ i = 3^{-kappaH i L}` decays at `kappaH <= rhoM`, so the
  -- product with the pre-start weight is the larger factor with the mixed
  -- exponent `kappaH i L + rhoM (Nstar - ell)`.
  have hprod :
      memoryDecay hc L ^ i *
          (3 : ℝ) ^ (-(hc.rhoM * ((Nstar - ell : ℕ) : ℝ))) =
        (3 : ℝ) ^
          (-(hc.kappaH * ((i * L : ℕ) : ℝ) +
            hc.rhoM * ((Nstar - ell : ℕ) : ℝ))) := by
    rw [memoryDecay_pow_eq_grid_gap]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hcast_iL_nonneg : (0 : ℝ) ≤ ((i * L : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrate_le :
      hc.kappaH * ((i * L : ℕ) : ℝ) ≤ hc.rhoM * ((i * L : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hc.kappaH_le_rhoM hcast_iL_nonneg
  have hexp_le' :
      -(hc.rhoM * ((i * L + (Nstar - ell) : ℕ) : ℝ)) ≤
        -(hc.kappaH * ((i * L : ℕ) : ℝ) +
          hc.rhoM * ((Nstar - ell : ℕ) : ℝ)) := by
    have hcast_split :
        ((i * L + (Nstar - ell) : ℕ) : ℝ) =
          ((i * L : ℕ) : ℝ) + ((Nstar - ell : ℕ) : ℝ) := by
      rw [Nat.cast_add]
    rw [hcast_split, mul_add]
    linarith
  calc
    (3 : ℝ) ^
        (-(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ))) ≤
      (3 : ℝ) ^
        (-(hc.rhoM * ((i * L + (Nstar - ell) : ℕ) : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 3) hexp_le
    _ ≤ (3 : ℝ) ^
        (-(hc.kappaH * ((i * L : ℕ) : ℝ) +
          hc.rhoM * ((Nstar - ell : ℕ) : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 3) hexp_le'
    _ = memoryDecay hc L ^ i *
        (3 : ℝ) ^ (-(hc.rhoM * ((Nstar - ell : ℕ) : ℝ))) := by
        rw [← hprod]

/--
Source label `l.det.memory`: the weighted ordinary pre-start drop tail is
bounded by `q^i H_0`.
-/
theorem memoryGridWeight_mul_prestartDrop_sum_le_memoryDecay_pow_mul_initialMemory
    (hc : HighContrastExponents d)
    {N Nstar L i j : ℕ} {F : ℕ → ℝ}
    (hNj : N ≤ j) (hF : Antitone F) :
    (3 : ℝ) ^
        (-(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ))) *
        (∑ ell ∈ Finset.Icc (j + 1) Nstar, (F (ell - 1) - F ell)) ≤
      memoryDecay hc L ^ i * initialMemory hc.rhoM N Nstar F := by
  let w : ℝ :=
    (3 : ℝ) ^
      (-(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ)))
  let tail : ℝ :=
    ∑ ell ∈ Finset.Icc (j + 1) Nstar,
      (3 : ℝ) ^ (-(hc.rhoM * ((Nstar - ell : ℕ) : ℝ))) *
        (F (ell - 1) - F ell)
  have hterm :
      ∀ ell ∈ Finset.Icc (j + 1) Nstar,
        w * (F (ell - 1) - F ell) ≤
          memoryDecay hc L ^ i *
            ((3 : ℝ) ^ (-(hc.rhoM * ((Nstar - ell : ℕ) : ℝ))) *
              (F (ell - 1) - F ell)) := by
    intro ell hell
    have hell_bounds := Finset.mem_Icc.mp hell
    have hweight :
        w ≤ memoryDecay hc L ^ i *
            (3 : ℝ) ^ (-(hc.rhoM * ((Nstar - ell : ℕ) : ℝ))) := by
      exact memoryGridWeight_le_memoryDecay_pow_mul_initialWeight_of_prestart
        (hc := hc) (Nstar := Nstar) (L := L) (i := i)
        (j := j) (ell := ell) (by omega) hell_bounds.2
    have hdrop_nonneg : 0 ≤ F (ell - 1) - F ell := by
      have hmono := hF (Nat.sub_le ell 1)
      linarith
    calc
      w * (F (ell - 1) - F ell) ≤
          (memoryDecay hc L ^ i *
            (3 : ℝ) ^ (-(hc.rhoM * ((Nstar - ell : ℕ) : ℝ)))) *
            (F (ell - 1) - F ell) :=
        mul_le_mul_of_nonneg_right hweight hdrop_nonneg
      _ = memoryDecay hc L ^ i *
            ((3 : ℝ) ^ (-(hc.rhoM * ((Nstar - ell : ℕ) : ℝ))) *
              (F (ell - 1) - F ell)) := by
        ring
  have hsum :
      w * (∑ ell ∈ Finset.Icc (j + 1) Nstar, (F (ell - 1) - F ell)) ≤
        memoryDecay hc L ^ i * tail := by
    dsimp [tail]
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have htail :
      tail ≤ initialMemory hc.rhoM N Nstar F := by
    dsimp [tail]
    exact initialMemory_tail_le_initialMemory hNj hF
  have hqpow_nonneg : 0 ≤ memoryDecay hc L ^ i :=
    pow_nonneg (le_of_lt (memoryDecay_pos hc L)) _
  calc
    (3 : ℝ) ^
        (-(hc.rhoM * ((memoryGridScale Nstar L i - j : ℕ) : ℝ))) *
        (∑ ell ∈ Finset.Icc (j + 1) Nstar, (F (ell - 1) - F ell))
        = w * (∑ ell ∈ Finset.Icc (j + 1) Nstar,
            (F (ell - 1) - F ell)) := rfl
    _ ≤ memoryDecay hc L ^ i * tail := hsum
    _ ≤ memoryDecay hc L ^ i * initialMemory hc.rhoM N Nstar F :=
      mul_le_mul_of_nonneg_left htail hqpow_nonneg

end Homogenization.HighContrast.EntryScale
