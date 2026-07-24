import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Homogenization.HighContrast.EntryScale.Inputs

/-!
# Variance-to-high-moment interpolation (`l.moment.variance.upgrade`)

Source: the high-moment paper (Armstrong–Kuusi–Loher, in preparation).

For a nonnegative observable bounded pathwise by `C_0 (2+T)^b` whose second
moment decays like `C_2 3^{-2 delta (j - N_2)}` from the entry scale
`N_2 = ceil(p_2 log_3 (2+T))`, the `Q`-th moment decays like
`C_Q 3^{-Q gamma_Q (j - N_Q)}` from the shifted entry scale
`N_Q = ceil(p_Q log_3 (2+T))`, where

* `p_Q = p_2 + b (Q-2) / (2 delta)`,
* `gamma_Q = 2 delta / Q`,
* `C_Q = 3^{2 delta} C_2 C_0^{Q-2}` is independent of `T`.

The pathwise bound absorbs the interpolation loss `(C_0 (2+T)^b)^{Q-2}` into
the entry-scale shift `N_Q - N_2`, up to the single ceiling discrepancy
`3^{2 delta}`.  This file provides the abstract lemma and the constructor
producing a `HighCenteredMomentEstimate` from a `VarianceBlockEstimate`; the
final-assembly corollary is in `VarianceUpgrade/P2.lean`.
-/

namespace Homogenization.HighContrast.EntryScale

/-- Parameters of the two-channel variance input in
`l.moment.variance.upgrade`: entry-scale coefficient `p2`, decay rate
`delta`, variance prefactor `C2`, and the pathwise-bound data `C0`, `b`
(with `b = 0` the plain uniformly bounded case). -/
structure VarianceMomentParameters where
  p2 : ℝ
  delta : ℝ
  C2 : ℝ
  C0 : ℝ
  b : ℝ
  p2_nonneg : 0 ≤ p2
  delta_pos : 0 < delta
  C2_nonneg : 0 ≤ C2
  C0_nonneg : 0 ≤ C0
  b_nonneg : 0 ≤ b

/-- The second-moment envelope `C_2 3^{-2 delta (j - N)}` of the variance
input, mirroring the shape of `highCenteredMomentEnvelope`. -/
noncomputable def varianceMomentEnvelope
    (vp : VarianceMomentParameters) (N j : ℕ) : ENNReal :=
  ENNReal.ofReal
    (vp.C2 * (3 : ℝ) ^ (-(2 * vp.delta) * ((j - N : ℕ) : ℝ)))

/-- The pathwise (ellipticity) bound `C_0 (2+T)^b` on the centered block
deviation.  In the uniformly elliptic case `b = 0` and the bound is a
constant. -/
noncomputable def variancePathwiseBound
    (vp : VarianceMomentParameters) (T : ℝ) : ENNReal :=
  ENNReal.ofReal (vp.C0 * (2 + T) ^ vp.b)

theorem variancePathwiseBound_ne_top
    (vp : VarianceMomentParameters) (T : ℝ) :
    variancePathwiseBound vp T ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- The scale-uniform variance input for the centered coarse block deviation:
almost-everywhere measurability, the pathwise ellipticity bound, and the
second-moment envelope, uniformly over triadic translates at every scale
`j ≥ N`.  This is the `Q = 2` counterpart of `HighCenteredMomentEstimate`,
augmented by the pathwise bound that powers the interpolation. -/
structure VarianceBlockEstimate
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (vp : VarianceMomentParameters) (μ : MeasureTheory.Measure Ω) (T : ℝ)
    (N : ℕ)
    (centeredBlockDeviation :
      ℕ → Homogenization.TriadicCube d → Ω → ENNReal) : Prop where
  aemeasurable :
    ∀ {j : ℕ}, N ≤ j → ∀ {Q : Homogenization.TriadicCube d},
      Q.scale = (j : ℤ) →
        AEMeasurable (fun ω => centeredBlockDeviation j Q ω) μ
  pathwise_le :
    ∀ {j : ℕ}, N ≤ j → ∀ {Q : Homogenization.TriadicCube d},
      Q.scale = (j : ℤ) →
        ∀ᵐ ω ∂ μ, centeredBlockDeviation j Q ω ≤ variancePathwiseBound vp T
  second_moment_le :
    ∀ {j : ℕ}, N ≤ j → ∀ {Q : Homogenization.TriadicCube d},
      Q.scale = (j : ℤ) →
        ∫⁻ ω, centeredBlockDeviation j Q ω ^ (2 : ℝ) ∂ μ ≤
          varianceMomentEnvelope vp N j

/-- The high-moment parameter pack produced by the interpolation
`l.moment.variance.upgrade`: the moment exponent `Q` and the structural
fields are inherited, while the entry-scale coefficient, the decay rate, and
the prefactor are replaced by the interpolated values
`p_Q = p_2 + b (Q-2)/(2 delta)`, `gamma_Q = 2 delta / Q`, and
`C_Q = 3^{2 delta} C_2 C_0^{Q-2}`. -/
noncomputable def HighCenteredMomentParameters.varianceUpgrade
    {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (vp : VarianceMomentParameters) :
    HighCenteredMomentParameters d hc where
  p_hm := vp.p2 + vp.b * (hm.Q - 2) / (2 * vp.delta)
  Q := hm.Q
  gamma := 2 * vp.delta / hm.Q
  C_Q := (3 : ℝ) ^ (2 * vp.delta) * vp.C2 * vp.C0 ^ (hm.Q - 2)
  holderExponentFloor := hm.holderExponentFloor
  p4Params := hm.p4Params
  p_hm_nonneg :=
    add_nonneg vp.p2_nonneg
      (div_nonneg
        (mul_nonneg vp.b_nonneg (by linarith [hm.two_le_Q]))
        (by linarith [vp.delta_pos]))
  two_le_Q := hm.two_le_Q
  gamma_pos :=
    div_pos (by linarith [vp.delta_pos])
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hm.two_le_Q)
  C_Q_nonneg :=
    mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
        vp.C2_nonneg)
      (Real.rpow_nonneg vp.C0_nonneg _)
  Q_mul_rhoM_gt := hm.Q_mul_rhoM_gt
  holderExponentFloor_nonneg := hm.holderExponentFloor_nonneg
  holderExponentFloor_lt_Q := hm.holderExponentFloor_lt_Q
  two_mul_p4_xi_le_Q := hm.two_mul_p4_xi_le_Q

@[simp] theorem varianceUpgrade_p_hm
    {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (vp : VarianceMomentParameters) :
    (hm.varianceUpgrade vp).p_hm =
      vp.p2 + vp.b * (hm.Q - 2) / (2 * vp.delta) := rfl

@[simp] theorem varianceUpgrade_Q
    {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (vp : VarianceMomentParameters) :
    (hm.varianceUpgrade vp).Q = hm.Q := rfl

@[simp] theorem varianceUpgrade_gamma
    {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (vp : VarianceMomentParameters) :
    (hm.varianceUpgrade vp).gamma = 2 * vp.delta / hm.Q := rfl

@[simp] theorem varianceUpgrade_C_Q
    {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (vp : VarianceMomentParameters) :
    (hm.varianceUpgrade vp).C_Q =
      (3 : ℝ) ^ (2 * vp.delta) * vp.C2 * vp.C0 ^ (hm.Q - 2) := rfl

@[simp] theorem varianceUpgrade_p4Params
    {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (vp : VarianceMomentParameters) :
    (hm.varianceUpgrade vp).p4Params = hm.p4Params := rfl

/-- The house envelope, restated with `^` notation for syntactic rewriting
against the lemmas in this file. -/
theorem highCenteredMomentEnvelope_eq
    {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) (N j : ℕ) :
    highCenteredMomentEnvelope hm N j =
      ENNReal.ofReal
        (hm.C_Q * (3 : ℝ) ^ (-(hm.Q * hm.gamma) * ((j - N : ℕ) : ℝ))) := rfl

/-- Abstract interpolation step (`(INT)` in the source note): a pathwise
bound and a second-moment bound give the `q`-th moment bound, with the
`q - 2` powers of the pathwise bound as interpolation constant.  No
measurability is needed. -/
theorem lintegral_rpow_le_rpow_sub_two_mul_of_ae_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {X : Ω → ENNReal} {B V : ENNReal} {q : ℝ}
    (hq : 2 ≤ q) (hB_ne_top : B ≠ ⊤)
    (hbound : ∀ᵐ ω ∂ μ, X ω ≤ B)
    (hsq : ∫⁻ ω, X ω ^ (2 : ℝ) ∂ μ ≤ V) :
    ∫⁻ ω, X ω ^ q ∂ μ ≤ B ^ (q - 2) * V := by
  have hq2 : (0 : ℝ) ≤ q - 2 := by linarith
  have hpt : ∀ᵐ ω ∂ μ, X ω ^ q ≤ B ^ (q - 2) * X ω ^ (2 : ℝ) := by
    filter_upwards [hbound] with ω hω
    have hsplit : X ω ^ q = X ω ^ (q - 2) * X ω ^ (2 : ℝ) := by
      have h :=
        ENNReal.rpow_add_of_nonneg (x := X ω) (q - 2) 2 hq2
          (by norm_num : (0 : ℝ) ≤ 2)
      have hq' : q - 2 + 2 = q := by ring
      rw [hq'] at h
      exact h
    rw [hsplit]
    exact mul_le_mul' (ENNReal.rpow_le_rpow hω hq2) le_rfl
  calc ∫⁻ ω, X ω ^ q ∂ μ
      ≤ ∫⁻ ω, B ^ (q - 2) * X ω ^ (2 : ℝ) ∂ μ :=
        MeasureTheory.lintegral_mono_ae hpt
    _ = B ^ (q - 2) * ∫⁻ ω, X ω ^ (2 : ℝ) ∂ μ :=
        MeasureTheory.lintegral_const_mul' _ _
          (ENNReal.rpow_ne_top_of_nonneg hq2 hB_ne_top)
    _ ≤ B ^ (q - 2) * V := mul_le_mul_right hsq _

/-- The interpolated entry scale dominates the variance entry scale. -/
theorem varianceUpgrade_ceil_le
    {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (vp : VarianceMomentParameters)
    {T : ℝ} (hT : 1 ≤ T) {N2 NQ : ℕ}
    (hN2 : N2 = Nat.ceil (vp.p2 * Real.logb 3 (2 + T)))
    (hNQ : NQ =
      Nat.ceil ((hm.varianceUpgrade vp).p_hm * Real.logb 3 (2 + T))) :
    N2 ≤ NQ := by
  have hL_nonneg : 0 ≤ Real.logb 3 (2 + T) :=
    Real.logb_nonneg (by norm_num : (1 : ℝ) < 3)
      (by linarith : (1 : ℝ) ≤ 2 + T)
  have hQe2 : (0 : ℝ) ≤ hm.Q - 2 := by linarith [hm.two_le_Q]
  have h2d_pos : (0 : ℝ) < 2 * vp.delta := by linarith [vp.delta_pos]
  have hp : vp.p2 ≤ (hm.varianceUpgrade vp).p_hm := by
    rw [varianceUpgrade_p_hm]
    exact le_add_of_nonneg_right
      (div_nonneg (mul_nonneg vp.b_nonneg hQe2) (le_of_lt h2d_pos))
  rw [hN2, hNQ]
  exact Nat.ceil_le_ceil (mul_le_mul_of_nonneg_right hp hL_nonneg)

/-- Real-arithmetic core of `(ABSORB)` + `(V2M)`: the interpolation loss
`(C_0 (2+T)^b)^{Q-2}` applied to the variance envelope entered at `N_2` is
dominated by the interpolated envelope entered at `N_Q`, with the
`T`-independent prefactor `3^{2 delta} C_2 C_0^{Q-2}`. -/
theorem varianceUpgrade_real_envelope_absorb
    (vp : VarianceMomentParameters) {Qe T : ℝ} (hQe : 2 ≤ Qe) (hT : 1 ≤ T)
    {N2 NQ j : ℕ}
    (hN2 : N2 = Nat.ceil (vp.p2 * Real.logb 3 (2 + T)))
    (hNQ : NQ =
      Nat.ceil
        ((vp.p2 + vp.b * (Qe - 2) / (2 * vp.delta)) *
          Real.logb 3 (2 + T)))
    (hj : NQ ≤ j) :
    (vp.C0 * (2 + T) ^ vp.b) ^ (Qe - 2) *
        (vp.C2 * (3 : ℝ) ^ (-(2 * vp.delta) * ((j - N2 : ℕ) : ℝ))) ≤
      ((3 : ℝ) ^ (2 * vp.delta) * vp.C2 * vp.C0 ^ (Qe - 2)) *
        (3 : ℝ) ^ (-(2 * vp.delta) * ((j - NQ : ℕ) : ℝ)) := by
  set L := Real.logb 3 (2 + T) with hL_def
  have hbase_pos : (0 : ℝ) < 2 + T := by linarith
  have h2T_nonneg : (0 : ℝ) ≤ 2 + T := le_of_lt hbase_pos
  have hL_nonneg : 0 ≤ L := by
    rw [hL_def]
    exact Real.logb_nonneg (by norm_num : (1 : ℝ) < 3)
      (by linarith : (1 : ℝ) ≤ 2 + T)
  have hQe2 : (0 : ℝ) ≤ Qe - 2 := by linarith
  have h2d_pos : (0 : ℝ) < 2 * vp.delta := by linarith [vp.delta_pos]
  have h2d_ne : (2 * vp.delta) ≠ 0 := ne_of_gt h2d_pos
  set D2 : ℝ := vp.b * (Qe - 2) / (2 * vp.delta) with hD2_def
  have hD2_nonneg : 0 ≤ D2 := by
    rw [hD2_def]
    exact div_nonneg (mul_nonneg vp.b_nonneg hQe2) (le_of_lt h2d_pos)
  have hD2_mul : D2 * (2 * vp.delta) = vp.b * (Qe - 2) := by
    rw [hD2_def]
    exact div_mul_cancel₀ _ h2d_ne
  -- entry-scale comparison and ceiling bounds
  have hN2NQ : N2 ≤ NQ := by
    rw [hN2, hNQ]
    exact Nat.ceil_le_ceil
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD2_nonneg)
        hL_nonneg)
  have hNQ_ge : (vp.p2 + D2) * L ≤ (NQ : ℝ) := by
    rw [hNQ]
    exact Nat.le_ceil _
  have hN2_lt : (N2 : ℝ) < vp.p2 * L + 1 := by
    rw [hN2]
    exact Nat.ceil_lt_add_one (mul_nonneg vp.p2_nonneg hL_nonneg)
  -- natural-subtraction bookkeeping, done once
  have hcast_NQN2 : ((NQ - N2 : ℕ) : ℝ) = (NQ : ℝ) - (N2 : ℝ) :=
    Nat.cast_sub hN2NQ
  have hsplit_nat : j - N2 = (j - NQ) + (NQ - N2) := by omega
  have hcast_split :
      ((j - N2 : ℕ) : ℝ) = ((j - NQ : ℕ) : ℝ) + ((NQ - N2 : ℕ) : ℝ) := by
    rw [hsplit_nat]
    push_cast
    ring
  -- the exponent absorption inequality
  have hexp_absorb :
      L * (vp.b * (Qe - 2)) +
          (-(2 * vp.delta) * ((NQ : ℝ) - (N2 : ℝ))) ≤
        2 * vp.delta := by
    have hexpand : (vp.p2 + D2) * L = vp.p2 * L + D2 * L := add_mul _ _ _
    have hD2L : D2 * L ≤ (NQ : ℝ) - vp.p2 * L := by
      linarith [hNQ_ge, hexpand]
    have hLb : L * (vp.b * (Qe - 2)) = (D2 * L) * (2 * vp.delta) := by
      rw [← hD2_mul]
      ring
    have hbound :
        (D2 * L) * (2 * vp.delta) ≤
          ((NQ : ℝ) - (N2 : ℝ) + 1) * (2 * vp.delta) :=
      mul_le_mul_of_nonneg_right (by linarith [hD2L, hN2_lt])
        (le_of_lt h2d_pos)
    have hexpand2 :
        ((NQ : ℝ) - (N2 : ℝ) + 1) * (2 * vp.delta) =
          (2 * vp.delta) * ((NQ : ℝ) - (N2 : ℝ)) + 2 * vp.delta := by
      ring
    linarith [hbound, hLb, hexpand2]
  -- convert the (2+T)-power to a 3-power
  have h3L : (3 : ℝ) ^ L = 2 + T := by
    rw [hL_def]
    exact Real.rpow_logb (by norm_num : (0 : ℝ) < 3)
      (by norm_num : (3 : ℝ) ≠ 1) hbase_pos
  have hP_eq :
      ((2 + T : ℝ) ^ vp.b) ^ (Qe - 2) =
        (3 : ℝ) ^ (L * (vp.b * (Qe - 2))) := by
    calc ((2 + T : ℝ) ^ vp.b) ^ (Qe - 2)
        = (2 + T : ℝ) ^ (vp.b * (Qe - 2)) :=
          (Real.rpow_mul h2T_nonneg _ _).symm
      _ = ((3 : ℝ) ^ L) ^ (vp.b * (Qe - 2)) := by rw [h3L]
      _ = (3 : ℝ) ^ (L * (vp.b * (Qe - 2))) :=
          (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _).symm
  have habsorb :
      ((2 + T : ℝ) ^ vp.b) ^ (Qe - 2) *
          (3 : ℝ) ^ (-(2 * vp.delta) * ((NQ - N2 : ℕ) : ℝ)) ≤
        (3 : ℝ) ^ (2 * vp.delta) := by
    rw [hP_eq, hcast_NQN2, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      hexp_absorb
  -- split the variance envelope across the entry-scale shift
  have hsplit_env :
      (3 : ℝ) ^ (-(2 * vp.delta) * ((j - N2 : ℕ) : ℝ)) =
        (3 : ℝ) ^ (-(2 * vp.delta) * ((j - NQ : ℕ) : ℝ)) *
          (3 : ℝ) ^ (-(2 * vp.delta) * ((NQ - N2 : ℕ) : ℝ)) := by
    rw [hcast_split, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  -- assemble
  have hC0Q_nonneg : 0 ≤ vp.C0 ^ (Qe - 2) :=
    Real.rpow_nonneg vp.C0_nonneg _
  have hEQ_nonneg :
      0 ≤ (3 : ℝ) ^ (-(2 * vp.delta) * ((j - NQ : ℕ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hfactor :
      (vp.C0 * (2 + T) ^ vp.b) ^ (Qe - 2) =
        vp.C0 ^ (Qe - 2) * ((2 + T) ^ vp.b) ^ (Qe - 2) :=
    Real.mul_rpow vp.C0_nonneg (Real.rpow_nonneg h2T_nonneg _)
  calc (vp.C0 * (2 + T) ^ vp.b) ^ (Qe - 2) *
        (vp.C2 * (3 : ℝ) ^ (-(2 * vp.delta) * ((j - N2 : ℕ) : ℝ)))
      = (vp.C2 * vp.C0 ^ (Qe - 2) *
          (3 : ℝ) ^ (-(2 * vp.delta) * ((j - NQ : ℕ) : ℝ))) *
          (((2 + T) ^ vp.b) ^ (Qe - 2) *
            (3 : ℝ) ^ (-(2 * vp.delta) * ((NQ - N2 : ℕ) : ℝ))) := by
        rw [hfactor, hsplit_env]
        ring
    _ ≤ (vp.C2 * vp.C0 ^ (Qe - 2) *
          (3 : ℝ) ^ (-(2 * vp.delta) * ((j - NQ : ℕ) : ℝ))) *
          (3 : ℝ) ^ (2 * vp.delta) := by
        exact mul_le_mul_of_nonneg_left habsorb
          (mul_nonneg (mul_nonneg vp.C2_nonneg hC0Q_nonneg) hEQ_nonneg)
    _ = ((3 : ℝ) ^ (2 * vp.delta) * vp.C2 * vp.C0 ^ (Qe - 2)) *
          (3 : ℝ) ^ (-(2 * vp.delta) * ((j - NQ : ℕ) : ℝ)) := by
        ring

/-- ENNReal form of the absorption step: the interpolation constant times the
variance envelope at entry scale `N_2` is dominated by the upgraded
high-moment envelope at entry scale `N_Q`. -/
theorem varianceUpgrade_envelope_absorb
    {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (vp : VarianceMomentParameters)
    {T : ℝ} (hT : 1 ≤ T) {N2 NQ j : ℕ}
    (hN2 : N2 = Nat.ceil (vp.p2 * Real.logb 3 (2 + T)))
    (hNQ : NQ =
      Nat.ceil ((hm.varianceUpgrade vp).p_hm * Real.logb 3 (2 + T)))
    (hj : NQ ≤ j) :
    variancePathwiseBound vp T ^ (hm.Q - 2) * varianceMomentEnvelope vp N2 j ≤
      highCenteredMomentEnvelope (hm.varianceUpgrade vp) NQ j := by
  have hbase_pos : (0 : ℝ) < 2 + T := by linarith
  have hCb_nonneg : (0 : ℝ) ≤ vp.C0 * (2 + T) ^ vp.b :=
    mul_nonneg vp.C0_nonneg (Real.rpow_nonneg (le_of_lt hbase_pos) _)
  have hQe2 : (0 : ℝ) ≤ hm.Q - 2 := by linarith [hm.two_le_Q]
  have hQ_ne : hm.Q ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hm.two_le_Q)
  have hQgamma :
      (hm.varianceUpgrade vp).Q * (hm.varianceUpgrade vp).gamma =
        2 * vp.delta := by
    rw [varianceUpgrade_Q, varianceUpgrade_gamma, mul_comm,
      div_mul_cancel₀ _ hQ_ne]
  have hNQ' :
      NQ =
        Nat.ceil
          ((vp.p2 + vp.b * (hm.Q - 2) / (2 * vp.delta)) *
            Real.logb 3 (2 + T)) := by
    rw [hNQ, varianceUpgrade_p_hm]
  have hreal :=
    varianceUpgrade_real_envelope_absorb vp hm.two_le_Q hT hN2 hNQ' hj
  calc variancePathwiseBound vp T ^ (hm.Q - 2) * varianceMomentEnvelope vp N2 j
      = ENNReal.ofReal
          ((vp.C0 * (2 + T) ^ vp.b) ^ (hm.Q - 2) *
            (vp.C2 * (3 : ℝ) ^ (-(2 * vp.delta) * ((j - N2 : ℕ) : ℝ)))) := by
        simp only [variancePathwiseBound, varianceMomentEnvelope]
        rw [ENNReal.ofReal_rpow_of_nonneg hCb_nonneg hQe2,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hCb_nonneg _)]
    _ ≤ ENNReal.ofReal
          (((3 : ℝ) ^ (2 * vp.delta) * vp.C2 * vp.C0 ^ (hm.Q - 2)) *
            (3 : ℝ) ^ (-(2 * vp.delta) * ((j - NQ : ℕ) : ℝ))) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = highCenteredMomentEnvelope (hm.varianceUpgrade vp) NQ j := by
        rw [highCenteredMomentEnvelope_eq, varianceUpgrade_C_Q, hQgamma]

/-- `l.moment.variance.upgrade` (`(V2M)`): a variance block estimate entered
at `N_2 = ceil(p_2 log_3 (2+T))` upgrades to the high centered-moment
estimate for the interpolated parameters, entered at
`N_Q = ceil(p_Q log_3 (2+T))`. -/
theorem HighCenteredMomentEstimate.of_varianceBlockEstimate
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (vp : VarianceMomentParameters)
    {μ : MeasureTheory.Measure Ω} {T : ℝ} (hT : 1 ≤ T) {N2 NQ : ℕ}
    {centeredBlockDeviation :
      ℕ → Homogenization.TriadicCube d → Ω → ENNReal}
    (hN2 : N2 = Nat.ceil (vp.p2 * Real.logb 3 (2 + T)))
    (hNQ : NQ =
      Nat.ceil ((hm.varianceUpgrade vp).p_hm * Real.logb 3 (2 + T)))
    (hVar : VarianceBlockEstimate vp μ T N2 centeredBlockDeviation) :
    HighCenteredMomentEstimate (hm.varianceUpgrade vp) μ NQ
      centeredBlockDeviation where
  measurable := by
    intro j hj Q hQ
    have hN2NQ : N2 ≤ NQ := varianceUpgrade_ceil_le hm vp hT hN2 hNQ
    exact (hVar.aemeasurable (le_trans hN2NQ hj) hQ).pow_const _
  moment_le := by
    intro j hj Q hQ
    have hN2NQ : N2 ≤ NQ := varianceUpgrade_ceil_le hm vp hT hN2 hNQ
    have hN2j : N2 ≤ j := le_trans hN2NQ hj
    have hmoment :
        ∫⁻ ω, centeredBlockDeviation j Q ω ^ (hm.varianceUpgrade vp).Q ∂ μ ≤
          variancePathwiseBound vp T ^ ((hm.varianceUpgrade vp).Q - 2) *
            varianceMomentEnvelope vp N2 j :=
      lintegral_rpow_le_rpow_sub_two_mul_of_ae_le
        (hq := by rw [varianceUpgrade_Q]; exact hm.two_le_Q)
        (variancePathwiseBound_ne_top vp T)
        (hVar.pathwise_le hN2j hQ)
        (hVar.second_moment_le hN2j hQ)
    refine le_trans hmoment ?_
    have habs := varianceUpgrade_envelope_absorb hm vp hT hN2 hNQ hj
    rw [varianceUpgrade_Q]
    exact habs

end Homogenization.HighContrast.EntryScale
