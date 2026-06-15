import Homogenization.Deterministic.CoarseFluxResponse.RHSConstantApexZeroDirichletWeakFluxScalarAdequacy

namespace Homogenization

noncomputable section

/-!
# Homogeneous response discharge for the zero-Dirichlet RHS apex

This leaf proves the scalar comparison that replaces the harmonic-response
energy of the remainder `w` by the manuscript's homogeneous split bound.  The
proof uses the zero-trace energy envelope for the correction field and keeps the
constant requirements explicit so the apex file can close them from its fixed
dimension scale.
-/

open scoped BigOperators ENNReal

namespace ZeroTraceDirichletCorrectorData

private theorem inv_geometricDiscount_one_le_five_inv {s : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) :
    (geometricDiscount s 1)⁻¹ ≤ 5 * s⁻¹ := by
  simpa [geometricDiscount] using
    inv_one_sub_rpow_three_neg_le_five_inv hs hs_le

private theorem homogenizationErrorOnCube_infinity_one_nonneg_local
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 := by
  rw [homogenizationErrorOnCube_infinity_one_eq_tsum]
  apply tsum_nonneg
  intro n
  exact mul_nonneg (geometricWeight_nonneg n (by simpa using hs))
    (scaleResponseAtScale_infinity_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a a0)

private theorem inv_sq_le_rpow_neg_five_halves {s : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) :
    (s⁻¹) ^ 2 ≤ Real.rpow s (-(5 / 2 : ℝ)) := by
  have hs_inv_ge_one : 1 ≤ s⁻¹ := (one_le_inv₀ hs).2 hs_le
  have hpow :
      Real.rpow (s⁻¹) (2 : ℝ) ≤ Real.rpow (s⁻¹) (5 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hs_inv_ge_one (by norm_num)
  have hleft : Real.rpow (s⁻¹) (2 : ℝ) = (s⁻¹) ^ 2 := by
    norm_num
  have hright :
      Real.rpow (s⁻¹) (5 / 2 : ℝ) = Real.rpow s (-(5 / 2 : ℝ)) := by
    exact (Real.rpow_neg_eq_inv_rpow s (5 / 2 : ℝ)).symm
  rw [hleft] at hpow
  rw [hright] at hpow
  exact hpow

private theorem sqrt_four_mul_matNorm_eq_two_mul_sqrt_matNorm
    {d : ℕ} (a0 : Mat d) :
    Real.sqrt ((4 : ℝ) * matNorm a0) = 2 * Real.sqrt (matNorm a0) := by
  have hmat : 0 ≤ matNorm a0 := matNorm_nonneg a0
  calc
    Real.sqrt ((4 : ℝ) * matNorm a0)
        = Real.sqrt ((2 : ℝ) ^ 2 * matNorm a0) := by norm_num
    _ = Real.sqrt ((2 : ℝ) ^ 2) * Real.sqrt (matNorm a0) := by
          rw [Real.sqrt_mul (sq_nonneg (2 : ℝ))]
    _ = 2 * Real.sqrt (matNorm a0) := by
          rw [Real.sqrt_sq_eq_abs]
          norm_num

private theorem sqrt_le_two_mul_add_sqrt_of_le_two_mul_add
    {X A B : ℝ}
    (hX_nonneg : 0 ≤ X) (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B)
    (hX : X ≤ 2 * A + 2 * B) :
    Real.sqrt X ≤ 2 * (Real.sqrt A + Real.sqrt B) := by
  have hrhs_nonneg : 0 ≤ 2 * (Real.sqrt A + Real.sqrt B) := by
    positivity
  refine Real.sqrt_le_of_le_sq hX_nonneg hrhs_nonneg ?_
  have hA_sq : (Real.sqrt A) ^ 2 = A := by
    rw [Real.sq_sqrt hA_nonneg]
  have hB_sq : (Real.sqrt B) ^ 2 = B := by
    rw [Real.sq_sqrt hB_nonneg]
  have hcross_nonneg : 0 ≤ Real.sqrt A * Real.sqrt B := by
    positivity
  nlinarith

private theorem cubeAverage_scalarVariationEnergyIntegrand_harmonic_le_two_mul_add
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    (w : AHarmonicFunction a (cubeSet Q)) {gradU : Vec d → Vec d}
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hgrad : ∀ x ∈ cubeSet Q,
      gradU x = w.toH1.grad x + ρ.toH10.toH1Function.grad x) :
    cubeAverage Q (scalarVariationEnergyIntegrand a w) ≤
      2 * cubeAverage Q (coefficientEnergyDensity a gradU) +
        2 * cubeAverage Q
          (coefficientEnergyDensity a
            (fun x => ρ.toH10.toH1Function.grad x)) := by
  let gradSum : Vec d → Vec d :=
    fun x => w.toH1.grad x + ρ.toH10.toH1Function.grad x
  have hgradSum_mem : MemVectorL2 (cubeSet Q) gradSum :=
    w.toH1.grad_memVectorL2.add ρ.toH10.toH1Function.grad_memVectorL2
  have hsplit :
      cubeAverage Q (coefficientEnergyDensity a (fun x => w.toH1.grad x)) ≤
        2 * cubeAverage Q (coefficientEnergyDensity a gradSum) +
          2 * cubeAverage Q
            (coefficientEnergyDensity a
              (fun x => ρ.toH10.toH1Function.grad x)) :=
    ρ.cubeAverage_coefficientEnergyDensity_harmonic_le_two_mul_add
      (u := gradSum) w hEll
      (by intro x hx; rfl) hgradSum_mem
  have hgradAvg :
      cubeAverage Q (coefficientEnergyDensity a gradSum) =
        cubeAverage Q (coefficientEnergyDensity a gradU) := by
    apply cubeAverage_eq_of_eq_on_cubeSet
    intro x hx
    simp [gradSum, coefficientEnergyDensity, hgrad x hx]
  calc
    cubeAverage Q (scalarVariationEnergyIntegrand a w)
        = cubeAverage Q (coefficientEnergyDensity a (fun x => w.toH1.grad x)) := by
          rfl
    _ ≤
        2 * cubeAverage Q (coefficientEnergyDensity a gradSum) +
          2 * cubeAverage Q
            (coefficientEnergyDensity a
              (fun x => ρ.toH10.toH1Function.grad x)) := hsplit
    _ =
        2 * cubeAverage Q (coefficientEnergyDensity a gradU) +
          2 * cubeAverage Q
            (coefficientEnergyDensity a
              (fun x => ρ.toH10.toH1Function.grad x)) := by
          rw [hgradAvg]

private theorem sqrt_correction_energy_le_display_scale
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    {s : ℝ} (g : Vec d → Vec d)
    (hs : 0 < s)
    (hG_nonneg : 0 ≤ cubeBesovPositiveVectorSeminormTwo Q s g)
    {Eρ : ℝ}
    (hEρ_nonneg : 0 ≤ Eρ)
    (hEρ :
      Eρ ≤ zeroTraceDirichletEnergyEnvelope Q a s g) :
    Real.sqrt Eρ ≤
      26 * s⁻¹ *
        Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) *
            cubeBesovPositiveVectorSeminormTwo Q s g := by
  let L : ℝ := (lambdaSq Q (s / 2) (.finite 2) a)⁻¹
  let N : ℝ := (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)
  let G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact inv_nonneg.mpr hlambda_nonneg
  have hN_nonneg : 0 ≤ N := by
    dsimp [N]
    exact mul_nonneg (by exact_mod_cast Nat.zero_le d)
      (mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
        (Real.sqrt_nonneg 2))
  have hG : 0 ≤ G := by
    dsimp [G]
    exact hG_nonneg
  have htarget_nonneg :
      0 ≤ 26 * s⁻¹ * Real.sqrt L * N * G := by
    positivity
  refine Real.sqrt_le_of_le_sq hEρ_nonneg htarget_nonneg ?_
  have henv :
      zeroTraceDirichletEnergyEnvelope Q a s g ≤
        650 * (s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2 := by
    simpa [L, N, G] using
      zeroTraceDirichletEnergyEnvelope_le_poincareDisplayedScale_noteConstants
        Q a g hs hG_nonneg
  have hcommon_nonneg :
      0 ≤ (s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2 := by
    positivity
  calc
    Eρ ≤ 650 * (s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2 := hEρ.trans henv
    _ = 650 * ((s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2) := by ring
    _ ≤ 676 * ((s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2) := by
          exact mul_le_mul_of_nonneg_right (by norm_num : (650 : ℝ) ≤ 676)
            hcommon_nonneg
    _ = (26 * s⁻¹ * Real.sqrt L * N * G) ^ 2 := by
          ring_nf
          rw [Real.sq_sqrt hL_nonneg]
          ring

theorem one_le_zeroTraceDirichletDisplayScale_expr
    {d : ℕ} [NeZero d] {s : ℝ} (hs : 0 < s) :
    1 ≤ (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2) := by
  have hd : 1 ≤ (d : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
  have hpow :
      1 ≤ (3 : ℝ) ^ ((d : ℝ) + s) := by
    exact Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 3)
      (add_nonneg (by exact_mod_cast Nat.zero_le d) hs.le)
  have hsqrttwo : 1 ≤ Real.sqrt 2 := by
    have h := Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 2)
    rw [Real.sqrt_one] at h
    exact h
  have hinner :
      1 ≤ (3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2 := by
    simpa [one_mul] using
      mul_le_mul hpow hsqrttwo (by norm_num : (0 : ℝ) ≤ 1)
        (le_trans (by norm_num : (0 : ℝ) ≤ 1) hpow)
  simpa [one_mul] using
    mul_le_mul hd hinner (by norm_num : (0 : ℝ) ≤ 1)
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) hd)

/--
Discharge of the homogeneous scalar comparison in the zero-Dirichlet RHS
route.  The two size assumptions on `C` are pure scalar constant checks; the
apex supplies them from `1000` times the displayed dimensional scale.
-/
theorem coarseFluxResponseQOneBound_le_const_mul_RHSHomogeneousSplitBound_of_zeroTraceDirichlet
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    (a0 : Mat d) (s : ℝ) (gradU : Vec d → Vec d)
    (w : AHarmonicFunction a (cubeSet Q))
    {lam Lam : ℝ} {C : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hgrad : ∀ x ∈ cubeSet Q,
      gradU x = w.toH1.grad x + ρ.toH10.toH1Function.grad x)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hC_energy : 20 ≤ C)
    (hC_response :
      520 * ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ≤ C) :
    coarseFluxResponseQOneBound Q a a0 s w ≤
      C * coarseFluxResponseRHSHomogeneousSplitBound Q a a0 s gradU g := by
  let gdInv : ℝ := (geometricDiscount s 1)⁻¹
  let H : ℝ := HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0
  let M : ℝ := Real.sqrt (matNorm a0)
  let A : ℝ := Real.sqrt (cubeAverage Q (coefficientEnergyDensity a gradU))
  let Linv : ℝ := (lambdaSq Q (s / 2) (.finite 2) a)⁻¹
  let L : ℝ := Real.sqrt Linv
  let N : ℝ := (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)
  let G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g
  let R : ℝ := 26 * s⁻¹ * L * N * G
  let Rp : ℝ := Real.rpow s (-(5 / 2 : ℝ))
  have hgd_nonneg : 0 ≤ gdInv := by
    dsimp [gdInv]
    exact inv_nonneg.mpr (le_of_lt (geometricDiscount_pos (by simpa using hs)))
  have hgd_le : gdInv ≤ 5 * s⁻¹ := by
    dsimp [gdInv]
    exact inv_geometricDiscount_one_le_five_inv hs hs_le
  have hH_nonneg : 0 ≤ H := by
    dsimp [H]
    exact homogenizationErrorOnCube_infinity_one_nonneg_local Q a a0 hs.le
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact Real.sqrt_nonneg _
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact Real.sqrt_nonneg _
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hLinv_nonneg : 0 ≤ Linv := by
    dsimp [Linv]
    exact inv_nonneg.mpr hlambda_nonneg
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact Real.sqrt_nonneg _
  have hN_nonneg : 0 ≤ N := by
    dsimp [N]
    exact mul_nonneg (by exact_mod_cast Nat.zero_le d)
      (mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
        (Real.sqrt_nonneg 2))
  have hG_nonneg : 0 ≤ G := by
    dsimp [G]
    exact cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove Q s g hGlobalBdd
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hRp_nonneg : 0 ≤ Rp := by
    dsimp [Rp]
    exact Real.rpow_nonneg hs.le _
  have hEgrad_nonneg :
      0 ≤ cubeAverage Q (coefficientEnergyDensity a gradU) :=
    cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
      Q a gradU hEll
  have hEρ_nonneg :
      0 ≤ cubeAverage Q
        (coefficientEnergyDensity a
          (fun x => ρ.toH10.toH1Function.grad x)) :=
    cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
      Q a (fun x => ρ.toH10.toH1Function.grad x) hEll
  have hAw_nonneg :
      0 ≤ cubeAverage Q (scalarVariationEnergyIntegrand a w) := by
    simpa [scalarVariationEnergyIntegrand, coefficientEnergyDensity] using
      cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        Q a (fun x => w.toH1.grad x) hEll
  have hρEnvelope :
      cubeAverage Q
          (coefficientEnergyDensity a
            (fun x => ρ.toH10.toH1Function.grad x)) ≤
        zeroTraceDirichletEnergyEnvelope Q a s g :=
    ρ.coefficientEnergy_average_le_zeroTraceDirichletEnergyEnvelope_noteConstants_expanded
      (s := s) (lam := lam) (Lam := Lam) hs hs_le hEll hg hGlobalBdd
  have hsqrtρ :
      Real.sqrt
          (cubeAverage Q
            (coefficientEnergyDensity a
              (fun x => ρ.toH10.toH1Function.grad x))) ≤ R := by
    simpa [Linv, L, N, G, R] using
      sqrt_correction_energy_le_display_scale Q a g hs hG_nonneg
        hEρ_nonneg hρEnvelope
  have hAw_split :
      cubeAverage Q (scalarVariationEnergyIntegrand a w) ≤
        2 * cubeAverage Q (coefficientEnergyDensity a gradU) +
          2 * cubeAverage Q
            (coefficientEnergyDensity a
              (fun x => ρ.toH10.toH1Function.grad x)) :=
    cubeAverage_scalarVariationEnergyIntegrand_harmonic_le_two_mul_add
      ρ w hEll hgrad
  have hsqrtsplit :
      Real.sqrt (cubeAverage Q (scalarVariationEnergyIntegrand a w)) ≤
        2 * (A + R) := by
    have hbase :=
      sqrt_le_two_mul_add_sqrt_of_le_two_mul_add hAw_nonneg
        hEgrad_nonneg hEρ_nonneg hAw_split
    calc
      Real.sqrt (cubeAverage Q (scalarVariationEnergyIntegrand a w))
          ≤ 2 * (A +
              Real.sqrt
                (cubeAverage Q
                  (coefficientEnergyDensity a
                    (fun x => ρ.toH10.toH1Function.grad x)))) := by
            simpa [A] using hbase
      _ ≤ 2 * (A + R) := by nlinarith
  have hscale : (s⁻¹) ^ 2 ≤ Rp := by
    dsimp [Rp]
    exact inv_sq_le_rpow_neg_five_halves hs hs_le
  have hcoeff_energy : 4 * gdInv ≤ C * s⁻¹ := by
    have hs_inv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
    nlinarith [hgd_le, hC_energy, hs_inv_nonneg]
  have hcoeff_response : 104 * gdInv * s⁻¹ * N ≤ C * Rp := by
    have hs_inv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
    have hfactor_nonneg : 0 ≤ 104 * s⁻¹ * N := by positivity
    have hgd_scaled :
        gdInv * (104 * s⁻¹ * N) ≤ (5 * s⁻¹) * (104 * s⁻¹ * N) :=
      mul_le_mul_of_nonneg_right hgd_le hfactor_nonneg
    have hscale_scaled :
        520 * (s⁻¹) ^ 2 * N ≤ 520 * Rp * N := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hscale (by norm_num : 0 ≤ (520 : ℝ)))
        hN_nonneg
    have hC_scaled :
        520 * N * Rp ≤ C * Rp :=
      mul_le_mul_of_nonneg_right hC_response hRp_nonneg
    calc
      104 * gdInv * s⁻¹ * N = gdInv * (104 * s⁻¹ * N) := by ring
      _ ≤ (5 * s⁻¹) * (104 * s⁻¹ * N) := hgd_scaled
      _ = 520 * (s⁻¹) ^ 2 * N := by ring
      _ ≤ 520 * Rp * N := hscale_scaled
      _ = 520 * N * Rp := by ring
      _ ≤ C * Rp := hC_scaled
  have henergyTerm :
      4 * gdInv * H * M * A ≤
        C * (s⁻¹ * M * H * A) := by
    have hcommon_nonneg : 0 ≤ M * H * A := by positivity
    have hscaled :=
      mul_le_mul_of_nonneg_right hcoeff_energy hcommon_nonneg
    calc
      4 * gdInv * H * M * A = (4 * gdInv) * (M * H * A) := by ring
      _ ≤ (C * s⁻¹) * (M * H * A) := hscaled
      _ = C * (s⁻¹ * M * H * A) := by ring
  have hresponseTerm :
      4 * gdInv * H * M * R ≤
        C * (Rp * M * L * H * G) := by
    have hcommon_nonneg : 0 ≤ M * L * H * G := by positivity
    have hscaled :=
      mul_le_mul_of_nonneg_right hcoeff_response hcommon_nonneg
    calc
      4 * gdInv * H * M * R =
          (104 * gdInv * s⁻¹ * N) * (M * L * H * G) := by
            dsimp [R]
            ring
      _ ≤ (C * Rp) * (M * L * H * G) := hscaled
      _ = C * (Rp * M * L * H * G) := by ring
  have hhom_split :
      gdInv * H * (2 * M) * (2 * (A + R)) ≤
        C * coarseFluxResponseRHSHomogeneousSplitBound Q a a0 s gradU g := by
    have henergy_eq :
        coarseFluxResponseRHSEnergyBound Q a a0 s gradU =
          s⁻¹ * M * H * A := by
      unfold coarseFluxResponseRHSEnergyBound
      dsimp [M, H, A]
    have hresponse_eq :
        coarseFluxResponseRHSResponseCorrectionBound Q a a0 s g =
          Rp * M * L * H * G := by
      unfold coarseFluxResponseRHSResponseCorrectionBound
      dsimp [Rp, M, L, Linv, H, G]
    calc
      gdInv * H * (2 * M) * (2 * (A + R))
          = 4 * gdInv * H * M * A + 4 * gdInv * H * M * R := by ring
      _ ≤ C * (s⁻¹ * M * H * A) +
            C * (Rp * M * L * H * G) :=
          add_le_add henergyTerm hresponseTerm
      _ = C *
            (coarseFluxResponseRHSEnergyBound Q a a0 s gradU +
              coarseFluxResponseRHSResponseCorrectionBound Q a a0 s g) := by
          rw [henergy_eq, hresponse_eq]
          ring
      _ = C * coarseFluxResponseRHSHomogeneousSplitBound Q a a0 s gradU g := by
          rfl
  have hprefix_nonneg : 0 ≤ gdInv * H * (2 * M) := by positivity
  calc
    coarseFluxResponseQOneBound Q a a0 s w
        = gdInv * H * (2 * M) *
            Real.sqrt (cubeAverage Q (scalarVariationEnergyIntegrand a w)) := by
          unfold coarseFluxResponseQOneBound
          dsimp [gdInv, H, M]
          rw [sqrt_four_mul_matNorm_eq_two_mul_sqrt_matNorm a0]
          ring
    _ ≤ gdInv * H * (2 * M) * (2 * (A + R)) :=
          mul_le_mul_of_nonneg_left hsqrtsplit hprefix_nonneg
    _ ≤ C * coarseFluxResponseRHSHomogeneousSplitBound Q a a0 s gradU g :=
          hhom_split

end ZeroTraceDirichletCorrectorData

end

end Homogenization
