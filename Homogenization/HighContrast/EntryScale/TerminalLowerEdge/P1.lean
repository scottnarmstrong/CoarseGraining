import Homogenization.HighContrast.EntryScale.Section52Index
import Homogenization.HighContrast.EntryScale.BadMaximal.P2

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open scoped Matrix.Norms.Elementwise
open scoped ENNReal


/-!
# Terminal lower-edge bridge

Pointwise bridges from the terminal positive-excess source maximum toward the
lower-edge good/bad split used by the raw high-contrast energy estimate.
-/


namespace Homogenization.HighContrast.EntryScale

noncomputable section

/-- Real value of the terminal stochastic weak weight. -/
theorem terminalStochasticWeakWeight_toReal_eq
    {d : ℕ} (hc : HighContrastExponents d) (m j : ℕ)
    (R : Homogenization.TriadicCube d) :
    (terminalStochasticWeakWeight (d := d) hc m j R).toReal =
      (3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ)) := by
  dsimp [terminalStochasticWeakWeight]
  exact ENNReal.toReal_ofReal
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3)
      (-hc.rhoM * ((m - j : ℕ) : ℝ))).le

/-- The real inverse weak weight exactly cancels the real weak weight. -/
theorem terminalStochasticWeakWeight_inv_toReal_mul_toReal
    {d : ℕ} (hc : HighContrastExponents d) (m j : ℕ)
    (R : Homogenization.TriadicCube d) :
    ((terminalStochasticWeakWeight (d := d) hc m j R)⁻¹).toReal *
        (terminalStochasticWeakWeight (d := d) hc m j R).toReal = 1 := by
  rw [terminalStochasticWeakWeight_inv_toReal_eq,
    terminalStochasticWeakWeight_toReal_eq]
  calc
    (3 : ℝ) ^ (hc.rhoM * ((m - j : ℕ) : ℝ)) *
        (3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ)) =
      (3 : ℝ) ^
        (hc.rhoM * ((m - j : ℕ) : ℝ) +
          -hc.rhoM * ((m - j : ℕ) : ℝ)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    _ = 1 := by
        have hzero :
            hc.rhoM * ((m - j : ℕ) : ℝ) +
                -hc.rhoM * ((m - j : ℕ) : ℝ) = 0 := by ring
        rw [hzero]
        norm_num

/--
Convert an LIH Section 5.2 descendant at absolute scale `n` into the
`descendantsAtDepth` indexing used by the terminal source maximum.
-/
theorem section52LargeScaleSet_mem_descendantsAtScale_to_descendantsAtDepth
    {d m : ℕ} {n : ℤ} {R : Homogenization.TriadicCube d}
    (hn : n ∈ Homogenization.Book.Ch05.Section52.section52LargeScaleSet m)
    (hR :
      R ∈ Homogenization.descendantsAtScale
        (Homogenization.originCube d (m : ℤ)) n) :
    R ∈ Homogenization.descendantsAtDepth
      (Homogenization.originCube d (m : ℤ)) (m - Int.toNat n) := by
  rwa [descendantsAtScale_originCube_eq_descendantsAtDepth_of_mem_section52LargeScaleSet hn] at hR

/--
The scalar high-scale edge-weight loss before taking the crude fixed-window
supremum.  This keeps the Section 5.2 geometric weights attached to the
inverse weak stochastic weight, which is the algebraic form needed for the
manuscript/high-contrast no-growth bad-event route.
-/
theorem section52LargeScale_terminalPositiveExcess_edgeWeightLoss_le_weightedInvSum
    {d : ℕ} [NeZero d] (hc : HighContrastExponents d)
    {N m : ℕ} {sLower sUpper : ℝ}
    (hsLower : 0 < sLower) (hsUpper : 0 < sUpper) :
    let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let weightLossSup : {n : ℤ // n ∈ S} → ℝ := fun n =>
      let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa [Q, Homogenization.originCube] using section52LargeScaleSet_mem_le_m n.2)
      parents.sup' hparents
        (fun R =>
          ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n.1) R)⁻¹).toReal)
    let edgeWeightLoss : ℝ :=
      S.attach.sum fun n =>
        if N ≤ Int.toNat n.1 then
          (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 +
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1) *
            weightLossSup n
        else 0
    let invLoss : {n : ℤ // n ∈ S} → ℝ := fun n =>
      ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n.1) Q)⁻¹).toReal
    edgeWeightLoss ≤
      (S.attach.sum fun n =>
        Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 *
          invLoss n) +
      (S.attach.sum fun n =>
        Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1 *
          invLoss n) := by
  classical
  dsimp only
  let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let weightLossSup : {n : ℤ // n ∈ S} → ℝ := fun n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa [Q, Homogenization.originCube] using section52LargeScaleSet_mem_le_m n.2)
    parents.sup' hparents
      (fun R =>
        ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n.1) R)⁻¹).toReal)
  let edgeWeightLoss : ℝ :=
    S.attach.sum fun n =>
      if N ≤ Int.toNat n.1 then
        (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 +
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1) *
          weightLossSup n
      else 0
  let invLoss : {n : ℤ // n ∈ S} → ℝ := fun n =>
    ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n.1) Q)⁻¹).toReal
  have hinv_nonneg : ∀ n : {n : ℤ // n ∈ S}, 0 ≤ invLoss n := by
    intro n
    dsimp [invLoss]
    rw [terminalStochasticWeakWeight_inv_toReal_eq]
    positivity
  have hweightLossSup_le :
      ∀ n : {n : ℤ // n ∈ S}, weightLossSup n ≤ invLoss n := by
    intro n
    dsimp [weightLossSup, invLoss]
    refine Finset.sup'_le _ _ ?_
    intro R _hR
    simp [terminalStochasticWeakWeight]
  have hsum_le_total :
      edgeWeightLoss ≤
        S.attach.sum fun n =>
          (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 +
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1) *
            invLoss n := by
    dsimp [edgeWeightLoss]
    refine Finset.sum_le_sum ?_
    intro n _hn
    have hcoeff_nonneg :
        0 ≤
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 +
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1 := by
      exact add_nonneg
        (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight_nonneg
          m hsLower.le n.1)
        (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight_nonneg
          m hsUpper.le n.1)
    by_cases hNn : N ≤ Int.toNat n.1
    · simp [hNn]
      exact mul_le_mul_of_nonneg_left (hweightLossSup_le n) hcoeff_nonneg
    · simp [hNn, mul_nonneg hcoeff_nonneg (hinv_nonneg n)]
  have hsum_split :
      (S.attach.sum fun n =>
          (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 +
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1) *
            invLoss n) =
        (S.attach.sum fun n =>
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 *
            invLoss n) +
        (S.attach.sum fun n =>
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1 *
            invLoss n) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro n _hn
    ring
  exact hsum_le_total.trans_eq hsum_split

/--
Pointwise cancellation behind the no-growth edge-loss bound: the Section 5.2
weight with exponent `s`, multiplied by the terminal inverse stochastic weak
weight, is exactly the Section 5.2 weight with exponent `s - rhoM`, up to the
normalizing geometric-discount ratio.
-/
theorem section52LargeScaleWeight_mul_terminalStochasticWeakWeight_inv_toReal_eq_discountRatio_mul_gapWeight
    {d : ℕ} [NeZero d] (hc : HighContrastExponents d)
    {m : ℕ} {s : ℝ}
    (hgap : 0 < s - hc.rhoM)
    {n : ℤ}
    (hn : n ∈ Homogenization.Book.Ch05.Section52.section52LargeScaleSet m) :
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s m n *
        ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n)
          (Homogenization.originCube d (m : ℤ)))⁻¹).toReal =
      (Homogenization.geometricDiscount s 1 /
          Homogenization.geometricDiscount (s - hc.rhoM) 1) *
        Homogenization.Book.Ch05.Section52.section52LargeScaleWeight
          (s - hc.rhoM) m n := by
  let l : ℕ := Int.toNat ((m : ℤ) - n)
  have hsub : m - Int.toNat n = l := by
    have hsum :
        Int.toNat ((m : ℤ) - n) + Int.toNat n = m :=
      Homogenization.Book.Ch05.Section52.section52LargeScaleSet_toNat_sub_add_toNat hn
    dsimp [l]
    omega
  have hdisc_gap_pos :
      0 < Homogenization.geometricDiscount (s - hc.rhoM) 1 :=
    Homogenization.geometricDiscount_pos (by simpa using hgap)
  have hpow :
      Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
          Real.rpow (3 : ℝ) (hc.rhoM * (l : ℝ)) =
        Real.rpow (3 : ℝ) (-(s - hc.rhoM) * (l : ℝ)) := by
    calc
      Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
          Real.rpow (3 : ℝ) (hc.rhoM * (l : ℝ)) =
        Real.rpow (3 : ℝ) (-s * (l : ℝ) + hc.rhoM * (l : ℝ)) := by
          exact (Real.rpow_add (by norm_num : (0 : ℝ) < 3)
            (-s * (l : ℝ)) (hc.rhoM * (l : ℝ))).symm
      _ = Real.rpow (3 : ℝ) (-(s - hc.rhoM) * (l : ℝ)) := by
          congr 1
          ring
  calc
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s m n *
        ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n)
          (Homogenization.originCube d (m : ℤ)))⁻¹).toReal =
      Homogenization.geometricDiscount s 1 *
        (Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
          Real.rpow (3 : ℝ) (hc.rhoM * (l : ℝ))) := by
        rw [Homogenization.Book.Ch05.Section52.section52LargeScaleWeight,
          Homogenization.geometricWeight_one_eq,
          terminalStochasticWeakWeight_inv_toReal_eq, hsub]
        dsimp [l]
        ring
    _ =
      Homogenization.geometricDiscount s 1 *
        Real.rpow (3 : ℝ) (-(s - hc.rhoM) * (l : ℝ)) := by
        rw [hpow]
    _ =
      (Homogenization.geometricDiscount s 1 /
          Homogenization.geometricDiscount (s - hc.rhoM) 1) *
        Homogenization.Book.Ch05.Section52.section52LargeScaleWeight
          (s - hc.rhoM) m n := by
        rw [Homogenization.Book.Ch05.Section52.section52LargeScaleWeight,
          Homogenization.geometricWeight_one_eq]
        dsimp [l]
        field_simp [hdisc_gap_pos.ne']

/--
Uniform scalar bound for one Section 5.2 weighted inverse-loss sum.  The only
constant is the geometric-discount ratio associated with the exponent gap
`s - rhoM`.
-/
theorem section52LargeScale_terminalPositiveExcess_weightedInvSum_le_discountRatio
    {d : ℕ} [NeZero d] (hc : HighContrastExponents d)
    {m : ℕ} {s : ℝ}
    (hgap : 0 < s - hc.rhoM) :
    let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let invLoss : {n : ℤ // n ∈ S} → ℝ := fun n =>
      ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n.1) Q)⁻¹).toReal
    (S.attach.sum fun n =>
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s m n.1 *
        invLoss n) ≤
      Homogenization.geometricDiscount s 1 /
        Homogenization.geometricDiscount (s - hc.rhoM) 1 := by
  classical
  dsimp only
  let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let C : ℝ :=
    Homogenization.geometricDiscount s 1 /
      Homogenization.geometricDiscount (s - hc.rhoM) 1
  let invLoss : {n : ℤ // n ∈ S} → ℝ := fun n =>
    ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n.1) Q)⁻¹).toReal
  have hs : 0 < s := by
    linarith [hc.rhoM_pos, hgap]
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg
      (Homogenization.geometricDiscount_pos (by simpa using hs)).le
      (Homogenization.geometricDiscount_pos (by simpa using hgap)).le
  have hsum_eq :
      (S.attach.sum fun n =>
        Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s m n.1 *
          invLoss n) =
        C *
          (S.attach.sum fun n =>
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight
              (s - hc.rhoM) m n.1) := by
    calc
      (S.attach.sum fun n =>
        Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s m n.1 *
          invLoss n) =
        S.attach.sum fun n =>
          C *
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight
              (s - hc.rhoM) m n.1 := by
          refine Finset.sum_congr rfl ?_
          intro n _hn
          simpa [S, Q, C, invLoss] using
            section52LargeScaleWeight_mul_terminalStochasticWeakWeight_inv_toReal_eq_discountRatio_mul_gapWeight
              (d := d) hc (m := m) (s := s) hgap (n := n.1) n.2
      _ =
        C *
          (S.attach.sum fun n =>
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight
              (s - hc.rhoM) m n.1) := by
          rw [Finset.mul_sum]
  have hsum_gap :
      (S.attach.sum fun n =>
        Homogenization.Book.Ch05.Section52.section52LargeScaleWeight
          (s - hc.rhoM) m n.1) ≤ 1 := by
    rw [Finset.sum_attach]
    simpa [S] using
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight_sum_le_one
        hgap m
  calc
    (S.attach.sum fun n =>
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s m n.1 *
        invLoss n) =
        C *
          (S.attach.sum fun n =>
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight
              (s - hc.rhoM) m n.1) := hsum_eq
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hsum_gap hC_nonneg
    _ = Homogenization.geometricDiscount s 1 /
        Homogenization.geometricDiscount (s - hc.rhoM) 1 := by
        dsimp [C]
        ring

/--
No-growth scalar bound for the exact Section 5.2 `edgeWeightLoss`.  The crude
window factor `3^(rhoM * L)` is replaced by the two geometric-discount ratios
corresponding to the lower and upper Section 5.2 exponent gaps.
-/
theorem section52LargeScale_terminalPositiveExcess_edgeWeightLoss_le_discountRatio
    {d : ℕ} [NeZero d] (hc : HighContrastExponents d)
    {N m : ℕ} {sLower sUpper : ℝ}
    (hLowerGap : 0 < sLower - hc.rhoM)
    (hUpperGap : 0 < sUpper - hc.rhoM) :
    let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let weightLossSup : {n : ℤ // n ∈ S} → ℝ := fun n =>
      let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa [Q, Homogenization.originCube] using section52LargeScaleSet_mem_le_m n.2)
      parents.sup' hparents
        (fun R =>
          ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n.1) R)⁻¹).toReal)
    let edgeWeightLoss : ℝ :=
      S.attach.sum fun n =>
        if N ≤ Int.toNat n.1 then
          (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 +
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1) *
            weightLossSup n
        else 0
    edgeWeightLoss ≤
      Homogenization.geometricDiscount sLower 1 /
          Homogenization.geometricDiscount (sLower - hc.rhoM) 1 +
        Homogenization.geometricDiscount sUpper 1 /
          Homogenization.geometricDiscount (sUpper - hc.rhoM) 1 := by
  classical
  dsimp only
  let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let weightLossSup : {n : ℤ // n ∈ S} → ℝ := fun n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa [Q, Homogenization.originCube] using section52LargeScaleSet_mem_le_m n.2)
    parents.sup' hparents
      (fun R =>
        ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n.1) R)⁻¹).toReal)
  let edgeWeightLoss : ℝ :=
    S.attach.sum fun n =>
      if N ≤ Int.toNat n.1 then
        (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 +
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1) *
          weightLossSup n
      else 0
  let invLoss : {n : ℤ // n ∈ S} → ℝ := fun n =>
    ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n.1) Q)⁻¹).toReal
  have hsLower : 0 < sLower := by
    linarith [hc.rhoM_pos, hLowerGap]
  have hsUpper : 0 < sUpper := by
    linarith [hc.rhoM_pos, hUpperGap]
  have hbase :
      edgeWeightLoss ≤
        (S.attach.sum fun n =>
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 *
            invLoss n) +
        (S.attach.sum fun n =>
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1 *
            invLoss n) := by
    simpa [S, Q, weightLossSup, edgeWeightLoss, invLoss] using
      section52LargeScale_terminalPositiveExcess_edgeWeightLoss_le_weightedInvSum
        (d := d) hc (N := N) (m := m)
        (sLower := sLower) (sUpper := sUpper) hsLower hsUpper
  have hlower :
      (S.attach.sum fun n =>
        Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 *
          invLoss n) ≤
        Homogenization.geometricDiscount sLower 1 /
          Homogenization.geometricDiscount (sLower - hc.rhoM) 1 := by
    simpa [S, Q, invLoss] using
      section52LargeScale_terminalPositiveExcess_weightedInvSum_le_discountRatio
        (d := d) hc (m := m) (s := sLower) hLowerGap
  have hupper :
      (S.attach.sum fun n =>
        Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1 *
          invLoss n) ≤
        Homogenization.geometricDiscount sUpper 1 /
          Homogenization.geometricDiscount (sUpper - hc.rhoM) 1 := by
    simpa [S, Q, invLoss] using
      section52LargeScale_terminalPositiveExcess_weightedInvSum_le_discountRatio
        (d := d) hc (m := m) (s := sUpper) hUpperGap
  exact hbase.trans (add_le_add hlower hupper)

/--
Source label `l.weaknorms.moreproto`: scalar Section 5.2 replacement for the
exact high-scale edge-weight-loss coefficient with the P4 lower-edge exponents
`sLower + beta` and `sUpper + beta`.
-/
theorem section52LargeScale_terminalPositiveExcess_edgeWeightLoss_le_discountRatio_of_P4_beta
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {N m : ℕ}
    (hLowerGap :
      let β := section53CoarseFluctuationBeta hP4
      0 < (hP4.sLower + β) - hc.rhoM)
    (hUpperGap :
      let β := section53CoarseFluctuationBeta hP4
      0 < (hP4.sUpper + β) - hc.rhoM) :
    let β := section53CoarseFluctuationBeta hP4
    let s' := hP4.sLower + β
    let t' := hP4.sUpper + β
    let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let weightLossSup : {n : ℤ // n ∈ S} → ℝ := fun n =>
      let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa [Q, Homogenization.originCube] using
            Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
      parents.sup' hparents
        (fun R =>
          ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n.1) R)⁻¹).toReal)
    let edgeWeightLoss : ℝ :=
      S.attach.sum fun n =>
        if N ≤ Int.toNat n.1 then
          (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 +
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1) *
            weightLossSup n
        else 0
    edgeWeightLoss ≤
      Homogenization.geometricDiscount s' 1 /
          Homogenization.geometricDiscount (s' - hc.rhoM) 1 +
        Homogenization.geometricDiscount t' 1 /
          Homogenization.geometricDiscount (t' - hc.rhoM) 1 := by
  classical
  dsimp only at hLowerGap hUpperGap ⊢
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let weightLossSup : {n : ℤ // n ∈ S} → ℝ := fun n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa [Q, Homogenization.originCube] using
          Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
    parents.sup' hparents
      (fun R =>
        ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n.1) R)⁻¹).toReal)
  let edgeWeightLoss : ℝ :=
    S.attach.sum fun n =>
      if N ≤ Int.toNat n.1 then
        (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s' m n.1 +
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight t' m n.1) *
          weightLossSup n
      else 0
  simpa [β, s', t', S, Q, weightLossSup, edgeWeightLoss] using
    section52LargeScale_terminalPositiveExcess_edgeWeightLoss_le_discountRatio
      (d := d) hc (N := N) (m := m)
      (sLower := s') (sUpper := t') hLowerGap hUpperGap

/--
High-scale Section 5.2 descendant slot with the faithful sqrt-theta
first-power source-max split.  The source maximum is split as
`min(sourceMax, 1) + badEventTruncation(sourceMax)` at first power; no
split-envelope substitution, no squaring, and no deterministic response cap is
introduced.
-/
theorem section52LargeScale_terminalMatrixPositiveExcessWeight_mul_le_two_mul_sqrt_thetaAtScale_mul_sourceMax_min_one_add_badEventTruncation_mul_response
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {N m : ℕ}
    {n : ℤ}
    (hn : n ∈ Homogenization.Book.Ch05.Section52.section52LargeScaleSet m)
    (hN : N ≤ Int.toNat n)
    (a : Ω → Homogenization.RegCoeffField d) (ω : Ω)
    {R : Homogenization.TriadicCube d}
    (hR :
      R ∈ Homogenization.descendantsAtScale
        (Homogenization.originCube d (m : ℤ)) n)
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField (a ω))
    {J : ℝ} (hJ_nonneg : 0 ≤ J) :
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let j : ℕ := Int.toNat n
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let sourceMax := terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a
    let upperExcess : ℝ :=
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).upperLeft -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0
    let lowerExcess : ℝ :=
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).lowerRight -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0
    (terminalStochasticWeakWeight (d := d) hc m j R).toReal *
        (σ * lowerExcess + σ⁻¹ * upperExcess) * J ≤
      2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
        (min (sourceMax ω) 1 * J +
          badEventTruncation sourceMax ω * J) := by
  classical
  dsimp only
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let j : ℕ := Int.toNat n
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let upperExcess : ℝ :=
    max
      (Homogenization.Book.Ch02.matrixNorm
          (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).upperLeft -
        hP.barSigmaAtScale hStruct (m : ℤ))
      0
  let lowerExcess : ℝ :=
    max
      (Homogenization.Book.Ch02.matrixNorm
          (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).lowerRight -
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
      0
  let source : Ω → ℝ := terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a
  let Ttheta : ℝ := 2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))
  have hj : Int.toNat n ∈ Finset.Icc N m :=
    section52LargeScaleSet_toNat_mem_Icc hn hN
  have hR_depth :
      R ∈ Homogenization.descendantsAtDepth
        (Homogenization.originCube d (m : ℤ)) (m - Int.toNat n) :=
    section52LargeScaleSet_mem_descendantsAtScale_to_descendantsAtDepth hn hR
  have hslot :
      (terminalStochasticWeakWeight (d := d) hc m j R).toReal *
          (σ * lowerExcess + σ⁻¹ * upperExcess) ≤
        Ttheta * source ω := by
    have hweighted :=
      weighted_terminalMatrixPositiveExcessWeight_le_two_mul_sqrt_thetaAtScale_mul_terminalSpectralPositivePartSourceMax
        (hP := hP) (hStruct := hStruct) (hP4 := hP4) (hc := hc)
        (N := N) (m := m) (j := Int.toNat n)
        (Homogenization.originCube d (m : ℤ)) a ω
        (R := R) hj hR_depth ha
    simpa [Q, j, σ, upperExcess, lowerExcess, source, Ttheta] using hweighted
  have hsource_split :
      source ω * J ≤
        min (source ω) 1 * J + badEventTruncation source ω * J :=
    maximal_mul_le_min_one_mul_add_badEventTruncation_mul hJ_nonneg
  have hTtheta_nonneg : 0 ≤ Ttheta := by
    dsimp [Ttheta]
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  calc
    (terminalStochasticWeakWeight (d := d) hc m j R).toReal *
        (σ * lowerExcess + σ⁻¹ * upperExcess) * J
        ≤ (Ttheta * source ω) * J :=
          mul_le_mul_of_nonneg_right hslot hJ_nonneg
    _ = Ttheta * (source ω * J) := by ring
    _ ≤ Ttheta *
        (min (source ω) 1 * J + badEventTruncation source ω * J) :=
          mul_le_mul_of_nonneg_left hsource_split hTtheta_nonneg
    _ =
      2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
        (min (source ω) 1 * J + badEventTruncation source ω * J) := by
        rfl

/--
Unweighted Section 5.2 sqrt-theta descendant slot with the inverse
stochastic weak-weight loss and the first-power source-max split.
-/
theorem section52LargeScale_terminalMatrixPositiveExcessWeight_mul_le_weightLoss_mul_two_mul_sqrt_thetaAtScale_mul_sourceMax_min_one_add_badEventTruncation_mul_response
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {N m : ℕ}
    {n : ℤ}
    (hn : n ∈ Homogenization.Book.Ch05.Section52.section52LargeScaleSet m)
    (hN : N ≤ Int.toNat n)
    (a : Ω → Homogenization.RegCoeffField d) (ω : Ω)
    {R : Homogenization.TriadicCube d}
    (hR :
      R ∈ Homogenization.descendantsAtScale
        (Homogenization.originCube d (m : ℤ)) n)
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField (a ω))
    {c J : ℝ} (hc_nonneg : 0 ≤ c) (hJ_nonneg : 0 ≤ J) :
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let j : ℕ := Int.toNat n
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let sourceMax := terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a
    let upperExcess : ℝ :=
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).upperLeft -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0
    let lowerExcess : ℝ :=
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).lowerRight -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0
    c * (σ * lowerExcess + σ⁻¹ * upperExcess) * J ≤
      c * ((terminalStochasticWeakWeight (d := d) hc m j R)⁻¹).toReal *
        (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
          (min (sourceMax ω) 1 * J +
            badEventTruncation sourceMax ω * J)) := by
  classical
  dsimp only
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let j : ℕ := Int.toNat n
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let upperExcess : ℝ :=
    max
      (Homogenization.Book.Ch02.matrixNorm
          (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).upperLeft -
        hP.barSigmaAtScale hStruct (m : ℤ))
      0
  let lowerExcess : ℝ :=
    max
      (Homogenization.Book.Ch02.matrixNorm
          (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).lowerRight -
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
      0
  let source : Ω → ℝ := terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a
  let w : ℝ := (terminalStochasticWeakWeight (d := d) hc m j R).toReal
  let winv : ℝ := ((terminalStochasticWeakWeight (d := d) hc m j R)⁻¹).toReal
  let E : ℝ := σ * lowerExcess + σ⁻¹ * upperExcess
  let B : ℝ :=
    2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
      (min (source ω) 1 * J + badEventTruncation source ω * J)
  have hweighted : w * E * J ≤ B := by
    simpa [Q, j, σ, upperExcess, lowerExcess, source, w, E, B] using
      section52LargeScale_terminalMatrixPositiveExcessWeight_mul_le_two_mul_sqrt_thetaAtScale_mul_sourceMax_min_one_add_badEventTruncation_mul_response
        (hP := hP) (hStruct := hStruct) (hP4 := hP4) (hc := hc)
        (N := N) (m := m) (n := n) hn hN a ω
        (R := R) hR ha hJ_nonneg
  have hwinv_nonneg : 0 ≤ winv := by
    dsimp [winv]
    exact ENNReal.toReal_nonneg
  have hcancel : winv * w = 1 := by
    simpa [w, winv, j] using
      terminalStochasticWeakWeight_inv_toReal_mul_toReal (d := d) hc m j R
  have hinside : winv * (w * E * J) = E * J := by
    calc
      winv * (w * E * J) = (winv * w) * E * J := by ring
      _ = E * J := by
          rw [hcancel]
          ring
  calc
    c * E * J = c * (winv * (w * E * J)) := by
      rw [hinside]
      ring
    _ = c * winv * (w * E * J) := by ring
    _ ≤ c * winv * B :=
      mul_le_mul_of_nonneg_left hweighted (mul_nonneg hc_nonneg hwinv_nonneg)

/--
Lower Section 5.2 descendant supremum with the sqrt-theta first-power
source-max split.  The only loss is the supremum of the inverse stochastic
weak weight.
-/
theorem section52LargeScaleWeight_terminalLowerPositiveExcess_sup_mul_le_weightLossSup_mul_two_mul_sqrt_thetaAtScale_mul_sourceMax_min_one_add_badEventTruncation_mul_response
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {N m : ℕ} {s : ℝ}
    (hs : 0 ≤ s)
    {n : ℤ}
    (hn : n ∈ Homogenization.Book.Ch05.Section52.section52LargeScaleSet m)
    (hN : N ≤ Int.toNat n)
    (a : Ω → Homogenization.RegCoeffField d) (ω : Ω)
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField (a ω))
    {J : ℝ} (hJ_nonneg : 0 ≤ J) :
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let parents := Homogenization.descendantsAtScale Q n
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa [Q, Homogenization.originCube] using section52LargeScaleSet_mem_le_m hn)
    let j : ℕ := Int.toNat n
    let coeff : ℝ :=
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s m n
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let sourceMax := terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a
    let lowerExcess : Homogenization.TriadicCube d → ℝ := fun R =>
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).lowerRight -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0
    let lowerSup : ℝ := parents.sup' hparents lowerExcess
    let weightLossSup : ℝ :=
      parents.sup' hparents
        (fun R => ((terminalStochasticWeakWeight (d := d) hc m j R)⁻¹).toReal)
    coeff * (σ * lowerSup) * J ≤
      coeff * weightLossSup *
        (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
          (min (sourceMax ω) 1 * J +
            badEventTruncation sourceMax ω * J)) := by
  classical
  dsimp only
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let parents := Homogenization.descendantsAtScale Q n
  let hparents : parents.Nonempty :=
    Homogenization.descendantsAtScale_nonempty Q
      (by simpa [Q, Homogenization.originCube] using section52LargeScaleSet_mem_le_m hn)
  let j : ℕ := Int.toNat n
  let coeff : ℝ :=
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s m n
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let source : Ω → ℝ := terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a
  let lowerExcess : Homogenization.TriadicCube d → ℝ := fun R =>
    max
      (Homogenization.Book.Ch02.matrixNorm
          (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).lowerRight -
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
      0
  let upperExcess : Homogenization.TriadicCube d → ℝ := fun R =>
    max
      (Homogenization.Book.Ch02.matrixNorm
          (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).upperLeft -
        hP.barSigmaAtScale hStruct (m : ℤ))
      0
  let lowerSup : ℝ := parents.sup' hparents lowerExcess
  let weightLossSup : ℝ :=
    parents.sup' hparents
      (fun R => ((terminalStochasticWeakWeight (d := d) hc m j R)⁻¹).toReal)
  let B : ℝ :=
    2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
      (min (source ω) 1 * J + badEventTruncation source ω * J)
  have hcoeff_nonneg : 0 ≤ coeff := by
    dsimp [coeff]
    exact Homogenization.Book.Ch05.Section52.section52LargeScaleWeight_nonneg m hs n
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, Homogenization.Book.Ch05.sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hsource_nonneg : 0 ≤ source ω :=
    terminalSpectralPositivePartSourceMax_nonneg hP hStruct hc N m Q a ω
  have hmin_nonneg : 0 ≤ min (source ω) 1 :=
    le_min hsource_nonneg zero_le_one
  have hbad_nonneg : 0 ≤ badEventTruncation source ω :=
    badEventTruncation_nonneg hsource_nonneg
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (add_nonneg (mul_nonneg hmin_nonneg hJ_nonneg)
        (mul_nonneg hbad_nonneg hJ_nonneg))
  rcases Finset.exists_mem_eq_sup' hparents lowerExcess with
    ⟨R0, hR0, hR0_eq⟩
  have hupper_term_nonneg : 0 ≤ σ⁻¹ * upperExcess R0 :=
    mul_nonneg (inv_nonneg.mpr hσ_nonneg) (le_max_right _ _)
  have hpiece :
      coeff * (σ * lowerExcess R0) * J ≤
        coeff * (σ * lowerExcess R0 + σ⁻¹ * upperExcess R0) * J := by
    have hinner :
        σ * lowerExcess R0 ≤ σ * lowerExcess R0 + σ⁻¹ * upperExcess R0 := by
      linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hinner hcoeff_nonneg) hJ_nonneg
  have hslot :
      coeff * (σ * lowerExcess R0 + σ⁻¹ * upperExcess R0) * J ≤
        coeff * ((terminalStochasticWeakWeight (d := d) hc m j R0)⁻¹).toReal * B := by
    simpa [Q, j, σ, source, lowerExcess, upperExcess, B] using
      section52LargeScale_terminalMatrixPositiveExcessWeight_mul_le_weightLoss_mul_two_mul_sqrt_thetaAtScale_mul_sourceMax_min_one_add_badEventTruncation_mul_response
        (hP := hP) (hStruct := hStruct) (hP4 := hP4) (hc := hc)
        (N := N) (m := m) (n := n) hn hN a ω (R := R0) hR0 ha
        (c := coeff) hcoeff_nonneg hJ_nonneg
  have hwinv_le :
      ((terminalStochasticWeakWeight (d := d) hc m j R0)⁻¹).toReal ≤
        weightLossSup := by
    exact Finset.le_sup'
      (s := parents)
      (f := fun R =>
        ((terminalStochasticWeakWeight (d := d) hc m j R)⁻¹).toReal)
      hR0
  have hslot_to_sup :
      coeff * ((terminalStochasticWeakWeight (d := d) hc m j R0)⁻¹).toReal * B ≤
        coeff * weightLossSup * B := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hwinv_le hcoeff_nonneg) hB_nonneg
  calc
    coeff * (σ * lowerSup) * J
        = coeff * (σ * lowerExcess R0) * J := by
          rw [show lowerSup = lowerExcess R0 by simpa [lowerSup] using hR0_eq]
    _ ≤ coeff * (σ * lowerExcess R0 + σ⁻¹ * upperExcess R0) * J := hpiece
    _ ≤ coeff * ((terminalStochasticWeakWeight (d := d) hc m j R0)⁻¹).toReal * B :=
      hslot
    _ ≤ coeff * weightLossSup * B := hslot_to_sup

/--
Upper Section 5.2 descendant supremum with the sqrt-theta first-power
source-max split.
-/
theorem section52LargeScaleWeight_terminalUpperPositiveExcess_sup_mul_le_weightLossSup_mul_two_mul_sqrt_thetaAtScale_mul_sourceMax_min_one_add_badEventTruncation_mul_response
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {N m : ℕ} {s : ℝ}
    (hs : 0 ≤ s)
    {n : ℤ}
    (hn : n ∈ Homogenization.Book.Ch05.Section52.section52LargeScaleSet m)
    (hN : N ≤ Int.toNat n)
    (a : Ω → Homogenization.RegCoeffField d) (ω : Ω)
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField (a ω))
    {J : ℝ} (hJ_nonneg : 0 ≤ J) :
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let parents := Homogenization.descendantsAtScale Q n
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa [Q, Homogenization.originCube] using section52LargeScaleSet_mem_le_m hn)
    let j : ℕ := Int.toNat n
    let coeff : ℝ :=
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s m n
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let sourceMax := terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a
    let upperExcess : Homogenization.TriadicCube d → ℝ := fun R =>
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).upperLeft -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0
    let upperSup : ℝ := parents.sup' hparents upperExcess
    let weightLossSup : ℝ :=
      parents.sup' hparents
        (fun R => ((terminalStochasticWeakWeight (d := d) hc m j R)⁻¹).toReal)
    coeff * (σ⁻¹ * upperSup) * J ≤
      coeff * weightLossSup *
        (2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
          (min (sourceMax ω) 1 * J +
            badEventTruncation sourceMax ω * J)) := by
  classical
  dsimp only
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let parents := Homogenization.descendantsAtScale Q n
  let hparents : parents.Nonempty :=
    Homogenization.descendantsAtScale_nonempty Q
      (by simpa [Q, Homogenization.originCube] using section52LargeScaleSet_mem_le_m hn)
  let j : ℕ := Int.toNat n
  let coeff : ℝ :=
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s m n
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let source : Ω → ℝ := terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a
  let lowerExcess : Homogenization.TriadicCube d → ℝ := fun R =>
    max
      (Homogenization.Book.Ch02.matrixNorm
          (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).lowerRight -
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
      0
  let upperExcess : Homogenization.TriadicCube d → ℝ := fun R =>
    max
      (Homogenization.Book.Ch02.matrixNorm
          (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).upperLeft -
        hP.barSigmaAtScale hStruct (m : ℤ))
      0
  let upperSup : ℝ := parents.sup' hparents upperExcess
  let weightLossSup : ℝ :=
    parents.sup' hparents
      (fun R => ((terminalStochasticWeakWeight (d := d) hc m j R)⁻¹).toReal)
  let B : ℝ :=
    2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
      (min (source ω) 1 * J + badEventTruncation source ω * J)
  have hcoeff_nonneg : 0 ≤ coeff := by
    dsimp [coeff]
    exact Homogenization.Book.Ch05.Section52.section52LargeScaleWeight_nonneg m hs n
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, Homogenization.Book.Ch05.sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hsource_nonneg : 0 ≤ source ω :=
    terminalSpectralPositivePartSourceMax_nonneg hP hStruct hc N m Q a ω
  have hmin_nonneg : 0 ≤ min (source ω) 1 :=
    le_min hsource_nonneg zero_le_one
  have hbad_nonneg : 0 ≤ badEventTruncation source ω :=
    badEventTruncation_nonneg hsource_nonneg
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (add_nonneg (mul_nonneg hmin_nonneg hJ_nonneg)
        (mul_nonneg hbad_nonneg hJ_nonneg))
  rcases Finset.exists_mem_eq_sup' hparents upperExcess with
    ⟨R0, hR0, hR0_eq⟩
  have hlower_term_nonneg : 0 ≤ σ * lowerExcess R0 :=
    mul_nonneg hσ_nonneg (le_max_right _ _)
  have hpiece :
      coeff * (σ⁻¹ * upperExcess R0) * J ≤
        coeff * (σ * lowerExcess R0 + σ⁻¹ * upperExcess R0) * J := by
    have hinner :
        σ⁻¹ * upperExcess R0 ≤ σ * lowerExcess R0 + σ⁻¹ * upperExcess R0 := by
      linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hinner hcoeff_nonneg) hJ_nonneg
  have hslot :
      coeff * (σ * lowerExcess R0 + σ⁻¹ * upperExcess R0) * J ≤
        coeff * ((terminalStochasticWeakWeight (d := d) hc m j R0)⁻¹).toReal * B := by
    simpa [Q, j, σ, source, lowerExcess, upperExcess, B] using
      section52LargeScale_terminalMatrixPositiveExcessWeight_mul_le_weightLoss_mul_two_mul_sqrt_thetaAtScale_mul_sourceMax_min_one_add_badEventTruncation_mul_response
        (hP := hP) (hStruct := hStruct) (hP4 := hP4) (hc := hc)
        (N := N) (m := m) (n := n) hn hN a ω (R := R0) hR0 ha
        (c := coeff) hcoeff_nonneg hJ_nonneg
  have hwinv_le :
      ((terminalStochasticWeakWeight (d := d) hc m j R0)⁻¹).toReal ≤
        weightLossSup := by
    exact Finset.le_sup'
      (s := parents)
      (f := fun R =>
        ((terminalStochasticWeakWeight (d := d) hc m j R)⁻¹).toReal)
      hR0
  have hslot_to_sup :
      coeff * ((terminalStochasticWeakWeight (d := d) hc m j R0)⁻¹).toReal * B ≤
        coeff * weightLossSup * B := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hwinv_le hcoeff_nonneg) hB_nonneg
  calc
    coeff * (σ⁻¹ * upperSup) * J
        = coeff * (σ⁻¹ * upperExcess R0) * J := by
          rw [show upperSup = upperExcess R0 by simpa [upperSup] using hR0_eq]
    _ ≤ coeff * (σ * lowerExcess R0 + σ⁻¹ * upperExcess R0) * J := hpiece
    _ ≤ coeff * ((terminalStochasticWeakWeight (d := d) hc m j R0)⁻¹).toReal * B :=
      hslot
    _ ≤ coeff * weightLossSup * B := hslot_to_sup

end

end Homogenization.HighContrast.EntryScale
