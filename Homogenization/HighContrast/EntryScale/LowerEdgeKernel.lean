import Homogenization.HighContrast.EntryScale.LowerEdgeComparison
import Homogenization.HighContrast.EntryScale.MomentConsequences.P1

/-!
# Lower-edge hard-kernel split

This file isolates the current-baseline Section 5.2 large-scale sum split into
a finite low part and the high part already consumed by the high-moment
estimate.
-/

namespace Homogenization.HighContrast.EntryScale

noncomputable section

/--
Shifted normalized geometric weights have the exact tail mass
`3^{-s r}`.  This is the deterministic tail calculation used in the
low-window part of the corrected lower-edge coefficient proof.
-/
theorem tsum_geometricWeight_one_nat_add_eq_rpow {s : Real} (hs : 0 < s)
    (r : Nat) :
    tsum (fun n : Nat => Homogenization.geometricWeight s 1 (n + r)) =
      Real.rpow (3 : Real) (-s * (r : Real)) := by
  have hterm :
      ∀ n : Nat,
        Homogenization.geometricWeight s 1 (n + r) =
          Real.rpow (3 : Real) (-s * (r : Real)) *
            Homogenization.geometricWeight s 1 n := by
    intro n
    rw [Homogenization.geometricWeight_one_eq, Homogenization.geometricWeight_one_eq]
    have h3 : 0 < (3 : Real) := by norm_num
    have hpow :
        Real.rpow (3 : Real) (-s * ((n + r : Nat) : Real)) =
          Real.rpow (3 : Real) (-s * (r : Real)) *
            Real.rpow (3 : Real) (-s * (n : Real)) := by
      have hexp :
          -s * ((n + r : Nat) : Real) =
            -s * (r : Real) + -s * (n : Real) := by
        norm_num
        ring
      calc
        Real.rpow (3 : Real) (-s * ((n + r : Nat) : Real))
            = Real.rpow (3 : Real)
                (-s * (r : Real) + -s * (n : Real)) := by rw [hexp]
        _ = Real.rpow (3 : Real) (-s * (r : Real)) *
              Real.rpow (3 : Real) (-s * (n : Real)) := by
              simpa using
                (Real.rpow_add h3 (-s * (r : Real)) (-s * (n : Real)))
    rw [hpow]
    ring
  calc
    tsum (fun n : Nat => Homogenization.geometricWeight s 1 (n + r))
        = tsum (fun n : Nat =>
            Real.rpow (3 : Real) (-s * (r : Real)) *
              Homogenization.geometricWeight s 1 n) := by
          exact tsum_congr hterm
    _ = Real.rpow (3 : Real) (-s * (r : Real)) *
        tsum (fun n : Nat => Homogenization.geometricWeight s 1 n) := by
          rw [tsum_mul_left]
    _ = Real.rpow (3 : Real) (-s * (r : Real)) := by
          rw [Homogenization.tsum_geometricWeight_one_eq_one hs]
          ring

/--
Any finite collection of depths all lying past `r` has mass bounded by the
shifted geometric tail.  This is the finite-set form needed when the
Section 5.2 low window is rewritten from absolute scales to depths.
-/
theorem finset_geometricWeight_one_sum_le_tail_rpow {s : Real} (hs : 0 < s)
    {S : Finset Nat} {r : Nat} (hS : ∀ l ∈ S, r <= l) :
    (∑ l ∈ S, Homogenization.geometricWeight s 1 l) <=
      Real.rpow (3 : Real) (-s * (r : Real)) := by
  classical
  let imageS : Finset Nat := S.image fun l => l - r
  have hinj : Set.InjOn (fun l : Nat => l - r) (↑S : Set Nat) := by
    intro a ha b hb hsub
    have ha_ge : r <= a := hS a (by simpa using ha)
    have hb_ge : r <= b := hS b (by simpa using hb)
    have hadd := congrArg (fun x : Nat => x + r) hsub
    simpa [Nat.sub_add_cancel ha_ge, Nat.sub_add_cancel hb_ge] using hadd
  have hsum_image :
      (∑ l ∈ S, Homogenization.geometricWeight s 1 l) =
        ∑ u ∈ imageS, Homogenization.geometricWeight s 1 (u + r) := by
    dsimp [imageS]
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl ?_
      intro l hl
      have hl_ge : r <= l := hS l hl
      congr 1
      omega
    · exact hinj
  have hsummable :
      Summable (fun u : Nat => Homogenization.geometricWeight s 1 (u + r)) := by
    exact (summable_nat_add_iff r).2
      (Homogenization.summable_geometricWeight_one hs)
  have hfinite_le :
      (∑ u ∈ imageS, Homogenization.geometricWeight s 1 (u + r)) <=
        tsum (fun u : Nat => Homogenization.geometricWeight s 1 (u + r)) := by
    exact hsummable.sum_le_tsum imageS
      (fun u _hu =>
        Homogenization.geometricWeight_nonneg (u + r) (by simpa using hs.le))
  calc
    (∑ l ∈ S, Homogenization.geometricWeight s 1 l)
        = ∑ u ∈ imageS, Homogenization.geometricWeight s 1 (u + r) :=
          hsum_image
    _ <= tsum (fun u : Nat => Homogenization.geometricWeight s 1 (u + r)) :=
          hfinite_le
    _ = Real.rpow (3 : Real) (-s * (r : Real)) :=
          tsum_geometricWeight_one_nat_add_eq_rpow hs r

/--
The Section 5.2 low absolute scales carry only the geometric tail beginning at
depth `k - N`.  This is the scalar part of the corrected `ell < N` lower-edge
argument; stochastic/root bounds are handled separately.
-/
theorem section52LargeScaleSet_low_weight_sum_le_tail_rpow {s : Real}
    (hs : 0 < s) (N k : Nat) :
    (∑ n ∈ Homogenization.Book.Ch05.Section52.section52LargeScaleSet k,
        if N <= Int.toNat n then 0 else
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s k n) <=
      Real.rpow (3 : Real) (-s * ((k - N : Nat) : Real)) := by
  classical
  let LS := Homogenization.Book.Ch05.Section52.section52LargeScaleSet k
  by_cases hNk : N <= k
  · let F : Int -> Real := fun n => if N <= Int.toNat n then 0 else 1
    have hweighted :
        (∑ n ∈ LS,
            if N <= Int.toNat n then 0 else
              Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s k n) =
          ∑ n ∈ LS,
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s k n * F n := by
      refine Finset.sum_congr rfl ?_
      intro n _hn
      by_cases hN : N <= Int.toNat n
      · simp [F, hN]
      · simp [F, hN]
    have hreindex :
        (∑ n ∈ LS,
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s k n * F n) =
          ∑ l ∈ Finset.range k,
            Homogenization.geometricWeight s 1 l * F ((k : Int) - (l : Int)) := by
      simpa [LS] using
        Homogenization.Book.Ch05.Section52.section52LargeScaleSet_weighted_sum_eq_prefix_sum
          s k F
    let r : Nat := k - N
    let S : Finset Nat := (Finset.range k).filter fun l : Nat => r <= l
    have hterm :
        ∀ l ∈ Finset.range k,
          Homogenization.geometricWeight s 1 l * F ((k : Int) - (l : Int)) <=
            if r <= l then Homogenization.geometricWeight s 1 l else 0 := by
      intro l hl
      have hl_le : l <= k := Nat.le_of_lt (Finset.mem_range.mp hl)
      have htoNat : Int.toNat ((k : Int) - (l : Int)) = k - l := by omega
      by_cases hNlow : N <= Int.toNat ((k : Int) - (l : Int))
      · have hNlow_nat : N <= k - l := by
          simpa [htoNat] using hNlow
        have hzero : F ((k : Int) - (l : Int)) = 0 := by
          simp [F, htoNat, hNlow_nat]
        simp [hzero]
        by_cases hr : r <= l
        · simpa [hr] using
            Homogenization.geometricWeight_nonneg (s := s) (q := 1) l
              (by simpa using hs.le)
        · simp [hr]
      · have hnot_nat : ¬ N <= k - l := by
          intro h
          exact hNlow (by simpa [htoNat] using h)
        have hr : r <= l := by
          have hk_l_lt : k - l < N := by
            exact Nat.lt_of_not_ge hnot_nat
          dsimp [r]
          omega
        have hF : F ((k : Int) - (l : Int)) = 1 := by
          simp [F, htoNat, hnot_nat]
        simp [hF, hr]
    have hprefix_le :
        (∑ l ∈ Finset.range k,
            Homogenization.geometricWeight s 1 l * F ((k : Int) - (l : Int))) <=
          ∑ l ∈ Finset.range k,
            if r <= l then Homogenization.geometricWeight s 1 l else 0 :=
      Finset.sum_le_sum hterm
    have hfilter :
        (∑ l ∈ Finset.range k,
            if r <= l then Homogenization.geometricWeight s 1 l else 0) =
          ∑ l ∈ S, Homogenization.geometricWeight s 1 l := by
      dsimp [S]
      rw [Finset.sum_filter]
    have htail :
        (∑ l ∈ S, Homogenization.geometricWeight s 1 l) <=
          Real.rpow (3 : Real) (-s * (r : Real)) := by
      exact finset_geometricWeight_one_sum_le_tail_rpow hs
        (S := S) (r := r) (by
          intro l hl
          exact (Finset.mem_filter.mp hl).2)
    calc
      (∑ n ∈ LS,
          if N <= Int.toNat n then 0 else
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s k n)
          = ∑ n ∈ LS,
              Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s k n * F n :=
            hweighted
      _ = ∑ l ∈ Finset.range k,
            Homogenization.geometricWeight s 1 l * F ((k : Int) - (l : Int)) :=
            hreindex
      _ <= ∑ l ∈ Finset.range k,
            if r <= l then Homogenization.geometricWeight s 1 l else 0 :=
            hprefix_le
      _ = ∑ l ∈ S, Homogenization.geometricWeight s 1 l := hfilter
      _ <= Real.rpow (3 : Real) (-s * (r : Real)) := htail
      _ = Real.rpow (3 : Real) (-s * ((k - N : Nat) : Real)) := by rfl
  · have hterm :
        ∀ n ∈ LS,
          (if N <= Int.toNat n then 0 else
              Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s k n) <=
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s k n := by
      intro n _hn
      by_cases hN : N <= Int.toNat n
      · simp [hN, Homogenization.Book.Ch05.Section52.section52LargeScaleWeight_nonneg
          k (by nlinarith [hs]) n]
      · simp [hN]
    have hsum_le :
        (∑ n ∈ LS,
            if N <= Int.toNat n then 0 else
              Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s k n) <=
          ∑ n ∈ LS, Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s k n :=
      Finset.sum_le_sum hterm
    have htotal :
        (∑ n ∈ LS, Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s k n) <=
          1 := by
      simpa [LS] using
        Homogenization.Book.Ch05.Section52.section52LargeScaleWeight_sum_le_one hs k
    have hkN_zero : k - N = 0 := by omega
    calc
      (∑ n ∈ LS,
          if N <= Int.toNat n then 0 else
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s k n)
          <= ∑ n ∈ LS,
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s k n :=
            hsum_le
      _ <= 1 := htotal
      _ = Real.rpow (3 : Real) (-s * ((k - N : Nat) : Real)) := by
          simp [hkN_zero]

/--
Uniform exponent lower bound for the upper Section 5.2 weights.  The high
moment hypothesis bounds the P4 moment exponent from above, so `2d / Q` is a
law-independent positive lower bound for `sUpper`.
-/
theorem HighCenteredMomentParameters.uniformSection52Exponent_le_sUpper
    {d : Nat} [NeZero d] {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hparams : hP4.params = hm.p4Params) :
    (2 * (d : Real)) / hm.Q <= hP4.sUpper := by
  have hQ_pos : 0 < hm.Q := highCenteredMoment_Q_pos hm
  have hxi_pos : (0 : Real) < (hP4.xi : Real) := by
    exact_mod_cast hP4.xi_pos
  have hd_nonneg : 0 <= (d : Real) := by
    exact_mod_cast Nat.zero_le d
  have htwo_xi_le_Q : 2 * (hP4.xi : Real) <= hm.Q :=
    by simpa only [← hparams] using hm.two_mul_p4_xi_le_Q
  have hratio :
      (2 * (d : Real)) / hm.Q <= (d : Real) / (hP4.xi : Real) := by
    field_simp [hQ_pos.ne', hxi_pos.ne']
    nlinarith
  exact hratio.trans_lt hP4.dim_div_xi_lt_sUpper |>.le

/--
Uniform exponent lower bound for the lower/star Section 5.2 weights.  This is
the starred counterpart of
`HighCenteredMomentParameters.uniformSection52Exponent_le_sUpper`.
-/
theorem HighCenteredMomentParameters.uniformSection52Exponent_le_sLower
    {d : Nat} [NeZero d] {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hparams : hP4.params = hm.p4Params) :
    (2 * (d : Real)) / hm.Q <= hP4.sLower := by
  have hQ_pos : 0 < hm.Q := highCenteredMoment_Q_pos hm
  have hxi_pos : (0 : Real) < (hP4.xi : Real) := by
    exact_mod_cast hP4.xi_pos
  have hd_nonneg : 0 <= (d : Real) := by
    exact_mod_cast Nat.zero_le d
  have htwo_xi_le_Q : 2 * (hP4.xi : Real) <= hm.Q :=
    by simpa only [← hparams] using hm.two_mul_p4_xi_le_Q
  have hratio :
      (2 * (d : Real)) / hm.Q <= (d : Real) / (hP4.xi : Real) := by
    field_simp [hQ_pos.ne', hxi_pos.ne']
    nlinarith
  exact hratio.trans_lt hP4.dim_div_xi_lt_sLower |>.le

/--
If a fixed exponent `c` is below the Section 5.2 exponent `s`, the low absolute
scales carry at most the corresponding `c`-tail.  This is the uniform form used
with `c = 2d / Q`.
-/
theorem section52LargeScaleSet_low_weight_sum_le_uniform_tail_rpow
    {c s : Real} (hc : 0 < c) (hcs : c <= s) (N k : Nat) :
    (∑ n ∈ Homogenization.Book.Ch05.Section52.section52LargeScaleSet k,
        if N <= Int.toNat n then 0 else
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s k n) <=
      Real.rpow (3 : Real) (-c * ((k - N : Nat) : Real)) := by
  have hs : 0 < s := hc.trans_le hcs
  have hlow :=
    section52LargeScaleSet_low_weight_sum_le_tail_rpow hs N k
  have hgap_nonneg : 0 <= ((k - N : Nat) : Real) := by positivity
  have hexp :
      -s * ((k - N : Nat) : Real) <=
        -c * ((k - N : Nat) : Real) := by
    nlinarith
  have htail :
      Real.rpow (3 : Real) (-s * ((k - N : Nat) : Real)) <=
        Real.rpow (3 : Real) (-c * ((k - N : Nat) : Real)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) <= 3) hexp
  exact hlow.trans htail

/--
The upper lower-edge Section 5.2 exponent beats the triadic descendant count
at high moment order.  This is the exponent gap needed for the direct
manuscript-faithful weighted union bound.
-/
theorem HighCenteredMomentParameters.Q_mul_sUpper_gt_dim
    {d : Nat} [NeZero d] {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hparams : hP4.params = hm.p4Params) :
    (d : Real) < hm.Q * hP4.sUpper := by
  have hxi_pos : (0 : Real) < (hP4.xi : Real) := by
    exact_mod_cast hP4.xi_pos
  have hdim_div :
      (d : Real) / (hP4.xi : Real) < hP4.sUpper := by
    exact hP4.dim_div_xi_lt_sUpper
  have hdim_lt_xi_s : (d : Real) < (hP4.xi : Real) * hP4.sUpper := by
    have hmul := (div_lt_iff₀ hxi_pos).1 hdim_div
    nlinarith
  have hxi_nonneg : (0 : Real) <= (hP4.xi : Real) := hxi_pos.le
  have hxi_le_Q : (hP4.xi : Real) <= hm.Q := by
    have htwo_xi_le_Q : 2 * (hP4.xi : Real) <= hm.Q :=
      by simpa only [← hparams] using hm.two_mul_p4_xi_le_Q
    nlinarith
  have hmul_le : (hP4.xi : Real) * hP4.sUpper <= hm.Q * hP4.sUpper :=
    mul_le_mul_of_nonneg_right hxi_le_Q hP4.sUpper_pos.le
  exact hdim_lt_xi_s.trans_le hmul_le

/--
The lower lower-edge Section 5.2 exponent beats the triadic descendant count
at high moment order.  This is the lower endpoint counterpart of
`HighCenteredMomentParameters.Q_mul_sUpper_gt_dim`.
-/
theorem HighCenteredMomentParameters.Q_mul_sLower_gt_dim
    {d : Nat} [NeZero d] {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hparams : hP4.params = hm.p4Params) :
    (d : Real) < hm.Q * hP4.sLower := by
  have hxi_pos : (0 : Real) < (hP4.xi : Real) := by
    exact_mod_cast hP4.xi_pos
  have hdim_div :
      (d : Real) / (hP4.xi : Real) < hP4.sLower := by
    exact hP4.dim_div_xi_lt_sLower
  have hdim_lt_xi_s : (d : Real) < (hP4.xi : Real) * hP4.sLower := by
    have hmul := (div_lt_iff₀ hxi_pos).1 hdim_div
    nlinarith
  have hxi_nonneg : (0 : Real) <= (hP4.xi : Real) := hxi_pos.le
  have hxi_le_Q : (hP4.xi : Real) <= hm.Q := by
    have htwo_xi_le_Q : 2 * (hP4.xi : Real) <= hm.Q :=
      by simpa only [← hparams] using hm.two_mul_p4_xi_le_Q
    nlinarith
  have hmul_le : (hP4.xi : Real) * hP4.sLower <= hm.Q * hP4.sLower :=
    mul_le_mul_of_nonneg_right hxi_le_Q hP4.sLower_pos.le
  exact hdim_lt_xi_s.trans_le hmul_le

/--
The Section 5.3 beta decay still fits after the descendant-count
`d / Q` loss at the upper lower-edge endpoint.
-/
theorem HighCenteredMomentParameters.section53Beta_le_sUpper_sub_dim_div_Q
    {d : Nat} [NeZero d] {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hparams : hP4.params = hm.p4Params) :
    Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta
        hP4 <=
      hP4.sUpper - (d : Real) / hm.Q := by
  have hbeta_xi :
      Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta
          hP4 <=
        hP4.sUpper - (d : Real) / (hP4.xi : Real) := by
    exact
      Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta_le_sUpper_sub_dim_div_xi
        hP4
  have hxi_pos : (0 : Real) < (hP4.xi : Real) := by
    exact_mod_cast hP4.xi_pos
  have hxi_le_Q : (hP4.xi : Real) <= hm.Q := by
    have htwo_xi_le_Q : 2 * (hP4.xi : Real) <= hm.Q :=
      by simpa only [← hparams] using hm.two_mul_p4_xi_le_Q
    have hxi_nonneg : (0 : Real) <= (hP4.xi : Real) := hxi_pos.le
    nlinarith
  have hd_nonneg : (0 : Real) <= (d : Real) := by exact_mod_cast Nat.zero_le d
  have hdiv_le :
      (d : Real) / hm.Q <= (d : Real) / (hP4.xi : Real) := by
    exact div_le_div_of_nonneg_left hd_nonneg hxi_pos hxi_le_Q
  linarith

/--
The Section 5.3 beta decay still fits after the descendant-count
`d / Q` loss at the lower/star lower-edge endpoint.
-/
theorem HighCenteredMomentParameters.section53Beta_le_sLower_sub_dim_div_Q
    {d : Nat} [NeZero d] {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hparams : hP4.params = hm.p4Params) :
    Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta
        hP4 <=
      hP4.sLower - (d : Real) / hm.Q := by
  have hbeta_xi :
      Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta
          hP4 <=
        hP4.sLower - (d : Real) / (hP4.xi : Real) := by
    exact
      Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta_le_sLower_sub_dim_div_xi
        hP4
  have hxi_pos : (0 : Real) < (hP4.xi : Real) := by
    exact_mod_cast hP4.xi_pos
  have hxi_le_Q : (hP4.xi : Real) <= hm.Q := by
    have htwo_xi_le_Q : 2 * (hP4.xi : Real) <= hm.Q :=
      by simpa only [← hparams] using hm.two_mul_p4_xi_le_Q
    have hxi_nonneg : (0 : Real) <= (hP4.xi : Real) := hxi_pos.le
    nlinarith
  have hd_nonneg : (0 : Real) <= (d : Real) := by exact_mod_cast Nat.zero_le d
  have hdiv_le :
      (d : Real) / hm.Q <= (d : Real) / (hP4.xi : Real) := by
    exact div_le_div_of_nonneg_left hd_nonneg hxi_pos hxi_le_Q
  linarith

/--
Section 5.2 weights with exponent `s` are bounded by the raw beta-decay when
`beta <= s`.  This is the deterministic weight comparison in the lower-edge
source row; the geometric discount is at most one.
-/
theorem section52LargeScaleWeight_le_beta_decay_of_le
    {s beta : Real} (hbeta_le : beta <= s)
    {m j : Nat}
    (hj : (j : Int) ∈ Homogenization.Book.Ch05.Section52.section52LargeScaleSet m) :
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s m (j : Int) <=
      Real.rpow (3 : Real) (-beta * (((m - j : Nat) : Real))) := by
  have hj_le_int : (j : Int) <= (m : Int) :=
    Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m hj
  have hj_le : j <= m := by
    exact_mod_cast hj_le_int
  have hdepth :
      Int.toNat ((m : Int) - (j : Int)) = m - j := by
    omega
  have hdisc_le_one :
      Homogenization.geometricDiscount s 1 <= 1 :=
    Homogenization.Book.Ch05.Section52.geometricDiscount_one_le_one s
  have hpow_nonneg :
      0 <= Real.rpow (3 : Real) (-s * 1 * (((m - j : Nat) : Real))) :=
    Real.rpow_nonneg (by norm_num : (0 : Real) <= 3) _
  have hs_decay_le_beta_decay :
      Real.rpow (3 : Real) (-s * 1 * (((m - j : Nat) : Real))) <=
        Real.rpow (3 : Real) (-beta * (((m - j : Nat) : Real))) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) <= 3) ?_
    have hdepth_nonneg : 0 <= (((m - j : Nat) : Real)) := by positivity
    nlinarith
  calc
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s m (j : Int)
        =
      Homogenization.geometricDiscount s 1 *
        Real.rpow (3 : Real) (-s * 1 * (((m - j : Nat) : Real))) := by
          simp [Homogenization.Book.Ch05.Section52.section52LargeScaleWeight,
            Homogenization.geometricWeight, hdepth]
    _ <=
      1 * Real.rpow (3 : Real) (-s * 1 * (((m - j : Nat) : Real))) := by
          exact mul_le_mul_of_nonneg_right hdisc_le_one hpow_nonneg
    _ <=
      1 * Real.rpow (3 : Real) (-beta * (((m - j : Nat) : Real))) := by
          exact mul_le_mul_of_nonneg_left hs_decay_le_beta_decay
            (by norm_num : (0 : Real) <= 1)
    _ = Real.rpow (3 : Real) (-beta * (((m - j : Nat) : Real))) := by ring

/--
Section 5.2 weights still fit below beta decay after paying the
high-moment root of the triadic descendant count.  This is the scalar
exponent comparison behind the direct lower-edge high-window estimate:
the large-scale exponent `s` has a spare `d / Q` gap beyond beta.
-/
theorem section52LargeScaleWeight_mul_descendantCountRoot_le_beta_decay_of_le
    {d : Nat} {s beta Q : Real} (hQ_pos : 0 < Q)
    (hs_nonneg : 0 <= s)
    (hbeta_le : beta <= s - (d : Real) / Q)
    {m j : Nat}
    (hj : (j : Int) ∈ Homogenization.Book.Ch05.Section52.section52LargeScaleSet m) :
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s m (j : Int) *
        (((((3 ^ d) ^ (m - j) : Nat) : Real)) ^ ((1 : Real) / Q)) <=
      (3 : Real) ^ (-beta * (((m - j : Nat) : Real))) := by
  let gap : Real := ((m - j : Nat) : Real)
  have h3_pos : 0 < (3 : Real) := by norm_num
  have h3_nonneg : 0 <= (3 : Real) := le_of_lt h3_pos
  have hgap_nonneg : 0 <= gap := by
    dsimp [gap]
    positivity
  have hcount :
      (((3 ^ d) ^ (m - j) : Nat) : Real) =
        (3 : Real) ^ ((d : Real) * gap) := by
    rw [Nat.cast_pow, Nat.cast_pow]
    norm_num only [Nat.cast_ofNat]
    rw [← pow_mul, ← Real.rpow_natCast]
    congr 1
    simp [gap, Nat.cast_mul]
  have hcountRoot :
      (((((3 ^ d) ^ (m - j) : Nat) : Real)) ^ ((1 : Real) / Q)) =
        (3 : Real) ^ (((d : Real) / Q) * gap) := by
    rw [hcount]
    calc
      ((3 : Real) ^ ((d : Real) * gap)) ^ ((1 : Real) / Q)
          = (3 : Real) ^ (((d : Real) * gap) * ((1 : Real) / Q)) := by
            rw [← Real.rpow_mul h3_nonneg]
      _ = (3 : Real) ^ (((d : Real) / Q) * gap) := by
            congr 1
            field_simp [ne_of_gt hQ_pos]
  have hcountRoot_nonneg :
      0 <= (((((3 ^ d) ^ (m - j) : Nat) : Real)) ^ ((1 : Real) / Q)) := by
    rw [hcountRoot]
    exact Real.rpow_nonneg h3_nonneg _
  have hweight_le_s :
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s m (j : Int) <=
        (3 : Real) ^ (-s * gap) := by
    simpa [gap] using
      section52LargeScaleWeight_le_beta_decay_of_le (s := s) (beta := s)
        (le_refl s) (m := m) (j := j) hj
  have hweight_nonneg :
      0 <= Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s m (j : Int) :=
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight_nonneg
      m hs_nonneg (j : Int)
  calc
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s m (j : Int) *
        (((((3 ^ d) ^ (m - j) : Nat) : Real)) ^ ((1 : Real) / Q))
        <=
      (3 : Real) ^ (-s * gap) *
        (((((3 ^ d) ^ (m - j) : Nat) : Real)) ^ ((1 : Real) / Q)) := by
          exact mul_le_mul_of_nonneg_right hweight_le_s hcountRoot_nonneg
    _ =
      (3 : Real) ^ (-s * gap) *
        (3 : Real) ^ (((d : Real) / Q) * gap) := by
          rw [hcountRoot]
    _ =
      (3 : Real) ^ (-(s - (d : Real) / Q) * gap) := by
          rw [← Real.rpow_add h3_pos]
          congr 1
          ring
    _ <= (3 : Real) ^ (-beta * (((m - j : Nat) : Real))) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) <= 3) ?_
          dsimp [gap] at hgap_nonneg ⊢
          nlinarith

/--
Upper endpoint specialization of
`section52LargeScaleWeight_mul_descendantCountRoot_le_beta_decay_of_le`
with Section 5.3 beta.
-/
theorem HighCenteredMomentParameters.upper_section52LargeScaleWeight_mul_descendantCountRoot_le_section53BetaDecay
    {d : Nat} [NeZero d] {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hparams : hP4.params = hm.p4Params)
    {m j : Nat}
    (hj : (j : Int) ∈ Homogenization.Book.Ch05.Section52.section52LargeScaleSet m) :
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight hP4.sUpper m (j : Int) *
        (((((3 ^ d) ^ (m - j) : Nat) : Real)) ^ ((1 : Real) / hm.Q)) <=
      (3 : Real) ^
        (-
          Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta
            hP4 *
          (((m - j : Nat) : Real))) := by
  exact section52LargeScaleWeight_mul_descendantCountRoot_le_beta_decay_of_le
    (d := d) (s := hP4.sUpper)
    (beta :=
      Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta
        hP4)
    (Q := hm.Q) (highCenteredMoment_Q_pos hm) hP4.sUpper_nonneg
    (hm.section53Beta_le_sUpper_sub_dim_div_Q hP4 hparams) hj

/--
Lower/star endpoint specialization of
`section52LargeScaleWeight_mul_descendantCountRoot_le_beta_decay_of_le`
with Section 5.3 beta.
-/
theorem HighCenteredMomentParameters.lower_section52LargeScaleWeight_mul_descendantCountRoot_le_section53BetaDecay
    {d : Nat} [NeZero d] {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hparams : hP4.params = hm.p4Params)
    {m j : Nat}
    (hj : (j : Int) ∈ Homogenization.Book.Ch05.Section52.section52LargeScaleSet m) :
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight hP4.sLower m (j : Int) *
        (((((3 ^ d) ^ (m - j) : Nat) : Real)) ^ ((1 : Real) / hm.Q)) <=
      (3 : Real) ^
        (-
          Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta
            hP4 *
          (((m - j : Nat) : Real))) := by
  exact section52LargeScaleWeight_mul_descendantCountRoot_le_beta_decay_of_le
    (d := d) (s := hP4.sLower)
    (beta :=
      Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta
        hP4)
    (Q := hm.Q) (highCenteredMoment_Q_pos hm) hP4.sLower_nonneg
    (hm.section53Beta_le_sLower_sub_dim_div_Q hP4 hparams) hj

/--
Scalar root form of the direct `a.HM` descendant envelope.  The stochastic
high-moment decay is at most one after taking the `1 / Q` root, leaving only the
root of `C_Q` and the descendant-count root.
-/
theorem HighCenteredMomentParameters.count_mul_envelope_root_le_CQ_root_mul_countRoot
    {d : Nat} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) {N m j : Nat} :
    (((((3 ^ d) ^ (m - j) : Nat) : Real) *
        (hm.C_Q *
          (3 : Real) ^ (-(hm.Q * hm.gamma) * (((j - N : Nat) : Real))))) ^
      ((1 : Real) / hm.Q)) <=
      hm.C_Q ^ ((1 : Real) / hm.Q) *
        (((((3 ^ d) ^ (m - j) : Nat) : Real)) ^
          ((1 : Real) / hm.Q)) := by
  let p : Real := (1 : Real) / hm.Q
  let count : Real := (((3 ^ d) ^ (m - j) : Nat) : Real)
  let decay : Real :=
    (3 : Real) ^ (-(hm.Q * hm.gamma) * (((j - N : Nat) : Real)))
  have hQ_pos : 0 < hm.Q := highCenteredMoment_Q_pos hm
  have hp_nonneg : 0 <= p := by
    dsimp [p]
    exact div_nonneg (by norm_num) hQ_pos.le
  have hcount_nonneg : 0 <= count := by
    dsimp [count]
    positivity
  have hdecay_nonneg : 0 <= decay := by
    dsimp [decay]
    positivity
  have hCdecay_nonneg : 0 <= hm.C_Q * decay :=
    mul_nonneg hm.C_Q_nonneg hdecay_nonneg
  have hdecay_le_one : decay <= 1 := by
    dsimp [decay]
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by norm_num : (1 : Real) <= 3)
      (by
        have hgap_nonneg : 0 <= (((j - N : Nat) : Real)) := by
          positivity
        exact mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (mul_pos hQ_pos hm.gamma_pos).le) hgap_nonneg)
  have hdecay_root_le_one : decay ^ p <= 1 := by
    simpa using Real.rpow_le_one hdecay_nonneg hdecay_le_one hp_nonneg
  calc
    (((((3 ^ d) ^ (m - j) : Nat) : Real) *
        (hm.C_Q *
          (3 : Real) ^ (-(hm.Q * hm.gamma) * (((j - N : Nat) : Real))))) ^
      ((1 : Real) / hm.Q))
        = (count * (hm.C_Q * decay)) ^ p := by
          rfl
    _ = count ^ p * (hm.C_Q * decay) ^ p := by
          exact Real.mul_rpow hcount_nonneg hCdecay_nonneg
    _ = count ^ p * (hm.C_Q ^ p * decay ^ p) := by
          rw [Real.mul_rpow hm.C_Q_nonneg hdecay_nonneg]
    _ <= count ^ p * (hm.C_Q ^ p * 1) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hdecay_root_le_one
              (Real.rpow_nonneg hm.C_Q_nonneg p))
            (Real.rpow_nonneg hcount_nonneg p)
    _ = hm.C_Q ^ ((1 : Real) / hm.Q) *
        (((((3 ^ d) ^ (m - j) : Nat) : Real)) ^
          ((1 : Real) / hm.Q)) := by
          dsimp [p, count]
          ring_nf


/-- Low-index part of the grouped upper current-baseline Section 5.2 sum. -/
noncomputable def lowerEdgeCurrentUpperSection52LowLargeScalePositiveExcessSum
    {d : Nat} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (N k : Nat) (s : Real) :
    Homogenization.RegCoeffField d -> Real := fun a =>
  (Homogenization.Book.Ch05.Section52.section52LargeScaleSet k).attach.sum
    fun n =>
      if N <= Int.toNat n.1 then
        0
      else
        lowerEdgeCurrentUpperSection52LargeScalePositiveExcess
          hP hStruct k s n a

/-- Low-index part of the grouped lower/star current-baseline Section 5.2 sum. -/
noncomputable def lowerEdgeCurrentLowerSection52LowLargeScalePositiveExcessSum
    {d : Nat} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (N k : Nat) (s : Real) :
    Homogenization.RegCoeffField d -> Real := fun a =>
  (Homogenization.Book.Ch05.Section52.section52LargeScaleSet k).attach.sum
    fun n =>
      if N <= Int.toNat n.1 then
        0
      else
        lowerEdgeCurrentLowerSection52LargeScalePositiveExcess
          hP hStruct k s n a
