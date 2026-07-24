import Homogenization.CoarseGraining.AdjointSymmetry.BasicAdjoint
import Homogenization.Book.Ch04.Theorems.CoarseObservables
import Homogenization.Book.Ch04.Theorems.DilationResponse
import Homogenization.HighContrast.EntryScale.ResponseFluctuation
import Homogenization.HighContrast.EntryScale.ResponseMoment.P1

open MeasureTheory
open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization.Book.Ch05.Section54.OneStepContraction
open scoped Matrix.Norms.Elementwise

namespace Homogenization.HighContrast.EntryScale

/--
Source label `e.J.moment.bound`: `L^2` version of the primal terminal-norm
response lift.  This is the exponent used by the high-moment stochastic
maximum after Lyapunov's inequality in the manuscript.
-/
theorem coarseFluctuationResponseMomentAtScale_le_two_sqrtTheta_terminalUncenteredMomentRoot_two
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Homogenization.Vec d)
    (he : Homogenization.Book.Ch02.vecNorm e = 1)
    (hTerminal_mem :
      MeasureTheory.MemLp
        (fun a : Homogenization.CoeffField d =>
          terminalUncenteredCoarseBlockNorm hP hStruct m
            (Homogenization.originCube d (k : ℤ)) a)
        (2 : ENNReal) P) :
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e ≤
      2 * Real.sqrt
          (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
        Homogenization.Book.Ch04.annealedMomentRoot P 2
          (fun a : Homogenization.CoeffField d =>
            terminalUncenteredCoarseBlockNorm hP hStruct m
              (Homogenization.originCube d (k : ℤ)) a) := by
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (k : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let ζ := section53CoarseFluctuationZeta hP4
  let θ := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
  let c := 2 * Real.sqrt θ
  let T : Homogenization.CoeffField d → ℝ :=
    fun a => terminalUncenteredCoarseBlockNorm hP hStruct m Q a
  let X : Homogenization.CoeffField d → ℝ :=
    fun a => Homogenization.Book.Ch04.responseJObservableCubeSet Q p_e q_e a
  let Y : Homogenization.CoeffField d → ℝ := fun a => c * T a
  have hζ_pos : 0 < ζ := by
    simpa [ζ] using section53CoarseFluctuationZeta_pos hP4
  have hζ_le_two : ζ ≤ (2 : ℝ) := by
    simpa [ζ] using section53CoarseFluctuationZeta_le_two hP4
  have hξ_one : 1 ≤ (2 : ℕ) := by norm_num
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hT_nonneg : ∀ a, 0 ≤ T a := by
    intro a
    dsimp [T, terminalUncenteredCoarseBlockNorm]
    exact fullBlockOperatorNorm_nonneg _
  have hY_nonneg : ∀ a, 0 ≤ Y a := fun a =>
    mul_nonneg hc_nonneg (hT_nonneg a)
  have hX_nonneg : ∀ a, 0 ≤ X a := by
    intro a
    dsimp [X]
    exact Homogenization.Book.Ch04.responseJObservableCubeSet_nonneg Q p_e q_e a
  have hX_meas : AEMeasurable X P := by
    simpa [X] using hP.aemeasurable_responseJObservableCubeSet Q p_e q_e
  have hY_mem : MeasureTheory.MemLp Y (2 : ENNReal) P := by
    simpa [Y, T, Q] using hTerminal_mem.const_mul c
  have hXY : X ≤ᵐ[P] Y := by
    simpa [X, Y, T, Q, p_e, q_e, θ, c] using
      responseJ_special_ae_le_two_sqrtTheta_terminalUncentered
        hP hStruct hP4 k m e he
  have hmoment :
      coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e ≤
        Homogenization.Book.Ch04.annealedMomentRoot P 2 Y := by
    simpa [coarseFluctuationResponseMomentAtScale, X, Y, ζ, Q, p_e, q_e] using
      responseMoment_realRpowMomentRoot_le_natAnnealedMomentRoot_of_ae_le
        (P := P) (ζ := ζ) (ξ := 2) (X := X) (Y := Y)
        hζ_pos hζ_le_two hξ_one hX_meas hX_nonneg hY_nonneg hY_mem hXY
  have hconst :
      Homogenization.Book.Ch04.annealedMomentRoot P 2 Y =
        c * Homogenization.Book.Ch04.annealedMomentRoot P 2 T := by
    simpa [Y, T, c] using
      Homogenization.Book.Ch05.Section52.section52_annealedMomentRoot_const_mul_of_nonneg
        (P := P) (ξ := 2) (c := c) (X := T) hξ_one hc_nonneg hT_nonneg
  calc
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
        ≤ Homogenization.Book.Ch04.annealedMomentRoot P 2 Y := hmoment
    _ = c * Homogenization.Book.Ch04.annealedMomentRoot P 2 T := hconst
    _ =
        2 * Real.sqrt
            (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
          Homogenization.Book.Ch04.annealedMomentRoot P 2
            (fun a : Homogenization.CoeffField d =>
              terminalUncenteredCoarseBlockNorm hP hStruct m
                (Homogenization.originCube d (k : ℤ)) a) := by
          rfl

private theorem responseMoment_fullBlockOperatorNorm_add_le {d : ℕ}
    (A B : Homogenization.FullBlockMat d) :
    fullBlockOperatorNorm (A + B) ≤
      fullBlockOperatorNorm A + fullBlockOperatorNorm B := by
  calc
    fullBlockOperatorNorm (A + B)
        = ‖Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
            (𝕜 := ℝ) (A + B)‖ := rfl
    _ = ‖Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
          (𝕜 := ℝ) A +
          Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
          (𝕜 := ℝ) B‖ := by
        rw [map_add]
    _ ≤ ‖Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
          (𝕜 := ℝ) A‖ +
          ‖Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
          (𝕜 := ℝ) B‖ :=
        norm_add_le _ _
    _ = fullBlockOperatorNorm A + fullBlockOperatorNorm B := rfl

private theorem responseMoment_fullBlockOperatorNorm_one_le {d : ℕ} :
    fullBlockOperatorNorm (1 : Homogenization.FullBlockMat d) ≤ 1 := by
  calc
    fullBlockOperatorNorm (1 : Homogenization.FullBlockMat d)
        = ‖Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d)
            (𝕜 := ℝ) (1 : Homogenization.FullBlockMat d)‖ := rfl
    _ = ‖(1 : EuclideanSpace ℝ (Homogenization.BlockCoord d) →L[ℝ]
          EuclideanSpace ℝ (Homogenization.BlockCoord d))‖ := by
          rw [map_one]
    _ ≤ 1 := ContinuousLinearMap.norm_id_le

private theorem responseMoment_scalarFullBlockNormalizer_self_annealed_eq_one
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) :
    scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
        Homogenization.toFullBlockMat
          (Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale
            hP hStruct (m : ℤ)) *
        scalarFullBlockNormalizerMatrixAtScale hP hStruct m =
      1 := by
  classical
  let b := hP.barSigmaAtScale hStruct (m : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
  have hb : 0 < b := by
    simpa [b] using
      Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
        hP hStruct hP4 m
  have hc : 0 < c := by
    simpa [c] using
      Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
        hP hStruct hP4 m
  ext α β
  by_cases hαβ : α = β
  · subst β
    cases α with
    | inl i =>
        simp [scalarFullBlockNormalizerMatrixAtScale,
          Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale,
          Homogenization.Book.Ch02.blockDiag, Homogenization.toFullBlockMat,
          Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag,
          Matrix.mul_apply, Matrix.diagonal]
        field_simp [ne_of_gt (Real.sqrt_pos.mpr (by simpa [b] using hb))]
        rw [Real.sq_sqrt (by simpa [b] using hb.le)]
    | inr i =>
        simp [scalarFullBlockNormalizerMatrixAtScale,
          Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale,
          Homogenization.Book.Ch02.blockDiag, Homogenization.toFullBlockMat,
          Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag,
          Matrix.mul_apply, Matrix.diagonal]
        field_simp [ne_of_gt (Real.sqrt_pos.mpr (by simpa [c] using hc))]
        rw [Real.sq_sqrt (by simpa [c] using hc.le)]
        field_simp [ne_of_gt (by simpa [c] using hc)]
  · cases α with
    | inl i =>
        cases β with
        | inl j =>
            have hij : i ≠ j := by
              intro hij
              exact hαβ (by subst j; rfl)
            simp [scalarFullBlockNormalizerMatrixAtScale,
              Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale,
              Homogenization.Book.Ch02.blockDiag, Homogenization.toFullBlockMat,
              Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag,
              Matrix.mul_apply, Matrix.diagonal, hij]
        | inr j =>
            simp [scalarFullBlockNormalizerMatrixAtScale,
              Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale,
              Homogenization.Book.Ch02.blockDiag, Homogenization.toFullBlockMat,
              Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag,
              Matrix.mul_apply, Matrix.diagonal]
    | inr i =>
        cases β with
        | inl j =>
            simp [scalarFullBlockNormalizerMatrixAtScale,
              Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale,
              Homogenization.Book.Ch02.blockDiag, Homogenization.toFullBlockMat,
              Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag,
              Matrix.mul_apply, Matrix.diagonal]
        | inr j =>
            have hij : i ≠ j := by
              intro hij
              exact hαβ (by subst j; rfl)
            simp [scalarFullBlockNormalizerMatrixAtScale,
              Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale,
              Homogenization.Book.Ch02.blockDiag, Homogenization.toFullBlockMat,
              Homogenization.Book.Ch04.scalarFullBlockInvSqrtDiag,
              Matrix.mul_apply, Matrix.diagonal, hij]

/--
Source label `e.J.moment.bound`: the uncentered terminal-normalized block norm
is bounded by the terminal-centered block deviation, the deterministic
annealed drift, and the normalized identity.  This is the deterministic split
behind the manuscript's `|Ahom_m^{-1/2} A(cu_k) Ahom_m^{-1/2}| + 1` response
bound.
-/
theorem terminalUncenteredCoarseBlockNorm_le_centered_add_drift_add_one
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.CoeffField d) :
    terminalUncenteredCoarseBlockNorm hP hStruct m Q a ≤
      (terminalCoarseBlockDeviation hP hStruct m (fun x => x) k Q a).toReal +
        terminalAnnealedFullBlockDriftAtScales hP hStruct k m + 1 := by
  let D := scalarFullBlockNormalizerMatrixAtScale hP hStruct m
  let A := Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube Q a
  let Ak :=
    Homogenization.toFullBlockMat
      (Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale
        hP hStruct (k : ℤ))
  let Am :=
    Homogenization.toFullBlockMat
      (Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale
        hP hStruct (m : ℤ))
  let C := D * scalarCenteredFullBlockMatrixAtScale hP hStruct k A * D
  let R := D * (Ak - Am) * D
  have hcenter_toReal :
      (terminalCoarseBlockDeviation hP hStruct m (fun x => x) k Q a).toReal =
        fullBlockOperatorNorm C := by
    unfold terminalCoarseBlockDeviation terminalCenteredFullBlockDeviation
      coarseFullBlockMatrixAtCubeProcess scalarCenteredFullBlockMatrixAtScale
    change (ENNReal.ofReal (fullBlockOperatorNorm C)).toReal =
      fullBlockOperatorNorm C
    exact ENNReal.toReal_ofReal (fullBlockOperatorNorm_nonneg C)
  have hdrift :
      terminalAnnealedFullBlockDriftAtScales hP hStruct k m =
        fullBlockOperatorNorm R := by
    rfl
  have hAm :
      D * Am * D = 1 := by
    simpa [D, Am] using
      responseMoment_scalarFullBlockNormalizer_self_annealed_eq_one
        hP hStruct hP4 m
  have hsplit :
      D * A * D = C + R + 1 := by
    have hsplit0 :
        D * A * D = C + R + D * Am * D := by
      dsimp [C, R, scalarCenteredFullBlockMatrixAtScale]
      noncomm_ring
    calc
      D * A * D = C + R + D * Am * D := hsplit0
      _ = C + R + 1 := by rw [hAm]
  have hnorm₁ :
      fullBlockOperatorNorm (C + R + 1) ≤
        fullBlockOperatorNorm (C + R) + fullBlockOperatorNorm (1 : Homogenization.FullBlockMat d) :=
    responseMoment_fullBlockOperatorNorm_add_le (C + R) 1
  have hnorm₂ :
      fullBlockOperatorNorm (C + R) ≤ fullBlockOperatorNorm C + fullBlockOperatorNorm R :=
    responseMoment_fullBlockOperatorNorm_add_le C R
  calc
    terminalUncenteredCoarseBlockNorm hP hStruct m Q a =
        fullBlockOperatorNorm (D * A * D) := rfl
    _ = fullBlockOperatorNorm (C + R + 1) := by rw [hsplit]
    _ ≤ fullBlockOperatorNorm (C + R) +
        fullBlockOperatorNorm (1 : Homogenization.FullBlockMat d) := hnorm₁
    _ ≤ (fullBlockOperatorNorm C + fullBlockOperatorNorm R) +
        fullBlockOperatorNorm (1 : Homogenization.FullBlockMat d) := by
          gcongr
    _ ≤ (terminalCoarseBlockDeviation hP hStruct m (fun x => x) k Q a).toReal +
        terminalAnnealedFullBlockDriftAtScales hP hStruct k m + 1 := by
          rw [hcenter_toReal, hdrift]
          gcongr
          exact responseMoment_fullBlockOperatorNorm_one_le

/--
Source labels `e.J.moment.bound`, `M_m^st`, and `l.S.and.J`: the terminal
centered deviation at the lower edge of the no-drop window is selected from
the stochastic terminal envelope, losing only the explicit inverse weak
weight.
-/
theorem terminalCoarseBlockDeviation_origin_toReal_le_inv_weight_mul_stochasticMax
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hc : HighContrastExponents d) {N k m : ℕ}
    (hNk : N ≤ k) (hkm : k ≤ m)
    (a : Homogenization.CoeffField d) :
    (terminalCoarseBlockDeviation hP hStruct m
        (fun x : Homogenization.CoeffField d => x) k
        (Homogenization.originCube d (k : ℤ)) a).toReal ≤
      ((terminalStochasticWeakWeight (d := d) hc m k
          (Homogenization.originCube d (k : ℤ)))⁻¹).toReal *
        terminalCoarseBlockStochasticMax hP hStruct hc N m
          (Homogenization.originCube d (m : ℤ))
          (fun x : Homogenization.CoeffField d => x) a := by
  classical
  let Qm : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let Rk : Homogenization.TriadicCube d := Homogenization.originCube d (k : ℤ)
  let weak : ℕ → Homogenization.TriadicCube d → ENNReal :=
    terminalStochasticWeakWeight (d := d) hc m
  let dev :=
    terminalCoarseBlockDeviation hP hStruct m
      (fun x : Homogenization.CoeffField d => x)
  let env :=
    terminalCoarseBlockStochasticEnvelope hP hStruct N m Qm weak
      (fun x : Homogenization.CoeffField d => x)
  have hkIcc : k ∈ Finset.Icc N m := Finset.mem_Icc.mpr ⟨hNk, hkm⟩
  have hRk : Rk ∈ Homogenization.descendantsAtDepth Qm (m - k) := by
    simpa only [Qm, Rk] using
      originCube_mem_descendantsAtDepth_originCube_of_le (d := d) hkm
  have hinner :
      weak k Rk * dev k Rk a ≤
        (Homogenization.descendantsAtDepth Qm (m - k)).sup
          (fun R => weak k R * dev k R a) := by
    exact Finset.le_sup
      (s := Homogenization.descendantsAtDepth Qm (m - k))
      (f := fun R => weak k R * dev k R a) hRk
  have hterm : weak k Rk * dev k Rk a ≤ env a := by
    have houter :
        (Homogenization.descendantsAtDepth Qm (m - k)).sup
            (fun R => weak k R * dev k R a) ≤
          env a := by
      dsimp [env, terminalCoarseBlockStochasticEnvelope]
      exact Finset.le_sup
        (s := Finset.Icc N m)
        (f := fun j =>
          (Homogenization.descendantsAtDepth Qm (m - j)).sup
            (fun R => weak j R * dev j R a))
        hkIcc
    exact hinner.trans houter
  have hweak_ne_zero : weak k Rk ≠ 0 := by
    dsimp [weak, terminalStochasticWeakWeight]
    exact ENNReal.ofReal_ne_zero_iff.mpr
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3)
        (-hc.rhoM * ((m - k : ℕ) : ℝ)))
  have hweak_ne_top : weak k Rk ≠ ⊤ := by
    dsimp [weak, terminalStochasticWeakWeight]
    exact ENNReal.ofReal_ne_top
  have hdev_le : dev k Rk a ≤ (weak k Rk)⁻¹ * env a := by
    calc
      dev k Rk a = (weak k Rk)⁻¹ * (weak k Rk * dev k Rk a) := by
        exact (ENNReal.inv_mul_cancel_left hweak_ne_zero hweak_ne_top).symm
      _ ≤ (weak k Rk)⁻¹ * env a := by
        exact mul_le_mul_right hterm (weak k Rk)⁻¹
  have hweak_bound : ∀ j ∈ Finset.Icc N m,
      ∀ R ∈ Homogenization.descendantsAtDepth Qm (m - j),
        weak j R ≤
          ENNReal.ofReal ((3 : ℝ) ^
            (-hc.rhoM * ((m - j : ℕ) : ℝ))) := by
    intro j _hj R _hR
    dsimp [weak, terminalStochasticWeakWeight]
    exact le_rfl
  have henv_ne_top : env a ≠ ⊤ := by
    simpa [env, weak, Qm] using
      terminalCoarseBlockStochasticEnvelope_ne_top_of_weak_le_terminal
        hP hStruct N m Qm weak
        (fun x : Homogenization.CoeffField d => x) hweak_bound a
  have hprod_ne_top : (weak k Rk)⁻¹ * env a ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hweak_ne_zero) henv_ne_top
  have htoReal :
      (dev k Rk a).toReal ≤ ((weak k Rk)⁻¹ * env a).toReal :=
    ENNReal.toReal_mono hprod_ne_top hdev_le
  calc
    (terminalCoarseBlockDeviation hP hStruct m
        (fun x : Homogenization.CoeffField d => x) k
        (Homogenization.originCube d (k : ℤ)) a).toReal =
        (dev k Rk a).toReal := by rfl
    _ ≤ ((weak k Rk)⁻¹ * env a).toReal := htoReal
    _ =
        ((terminalStochasticWeakWeight (d := d) hc m k
          (Homogenization.originCube d (k : ℤ)))⁻¹).toReal *
          terminalCoarseBlockStochasticMax hP hStruct hc N m
            (Homogenization.originCube d (m : ℤ))
            (fun x : Homogenization.CoeffField d => x) a := by
          simp [terminalCoarseBlockStochasticMax,
            terminalCoarseBlockStochasticMaxOfWeak, ENNReal.toReal_mul,
            weak, env, Qm, Rk]

/--
Source labels `e.J.moment.bound`, `M_m^st`, and `l.S.and.J`: pointwise
terminal-norm estimate after inserting both the stochastic high-moment
envelope and the deterministic no-drop drift bound.
-/
theorem terminalUncenteredCoarseBlockNorm_origin_le_stochasticMax_add_noDrop_drift_add_one
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {rho : ℝ} {N k m : ℕ}
    (hNk : N ≤ k) (hkm : k ≤ m)
    (hno :
      noDropWindow rho
        (contrastExcessAtScale hP hStruct k)
        (contrastExcessAtScale hP hStruct m))
    (a : Homogenization.CoeffField d) :
    terminalUncenteredCoarseBlockNorm hP hStruct m
        (Homogenization.originCube d (k : ℤ)) a ≤
      ((terminalStochasticWeakWeight (d := d) hc m k
          (Homogenization.originCube d (k : ℤ)))⁻¹).toReal *
        terminalCoarseBlockStochasticMax hP hStruct hc N m
          (Homogenization.originCube d (m : ℤ))
          (fun x : Homogenization.CoeffField d => x) a +
        rho * contrastExcessAtScale hP hStruct m /
          (1 + contrastExcessAtScale hP hStruct m) + 1 := by
  have hsplit :=
    terminalUncenteredCoarseBlockNorm_le_centered_add_drift_add_one
      hP hStruct hP4 k m (Homogenization.originCube d (k : ℤ)) a
  have hcenter :=
    terminalCoarseBlockDeviation_origin_toReal_le_inv_weight_mul_stochasticMax
      hP hStruct hc hNk hkm a
  have hdrift :=
    terminalAnnealedFullBlockDriftAtScales_le_noDrop_contrastExcess_of_P4
      hP hStruct hP4 hno (Nat.le_refl k) hkm
  calc
    terminalUncenteredCoarseBlockNorm hP hStruct m
        (Homogenization.originCube d (k : ℤ)) a ≤
        (terminalCoarseBlockDeviation hP hStruct m
          (fun x : Homogenization.CoeffField d => x) k
          (Homogenization.originCube d (k : ℤ)) a).toReal +
          terminalAnnealedFullBlockDriftAtScales hP hStruct k m + 1 := hsplit
    _ ≤
        ((terminalStochasticWeakWeight (d := d) hc m k
          (Homogenization.originCube d (k : ℤ)))⁻¹).toReal *
          terminalCoarseBlockStochasticMax hP hStruct hc N m
            (Homogenization.originCube d (m : ℤ))
            (fun x : Homogenization.CoeffField d => x) a +
          rho * contrastExcessAtScale hP hStruct m /
            (1 + contrastExcessAtScale hP hStruct m) + 1 := by
          nlinarith

/--
Source labels `e.J.moment.bound`, `M_m^st`, and `l.S.and.J`: the pointwise
stochastic-envelope/no-drop terminal norm estimate transfers the terminal
uncentered block norm into `L^2` once the stochastic maximum is in `L^2`.
-/
theorem terminalUncenteredCoarseBlockNorm_origin_memLp_two_of_stochasticMax
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {rho : ℝ} {N k m : ℕ}
    (hNk : N ≤ k) (hkm : k ≤ m)
    (hno :
      noDropWindow rho
        (contrastExcessAtScale hP hStruct k)
        (contrastExcessAtScale hP hStruct m))
    (hM_mem :
      MeasureTheory.MemLp
        (terminalCoarseBlockStochasticMax hP hStruct hc N m
          (Homogenization.originCube d (m : ℤ))
          (fun x : Homogenization.CoeffField d => x))
        (2 : ENNReal) P) :
    MeasureTheory.MemLp
      (fun a : Homogenization.CoeffField d =>
        terminalUncenteredCoarseBlockNorm hP hStruct m
          (Homogenization.originCube d (k : ℤ)) a)
      (2 : ENNReal) P := by
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  let T : Homogenization.CoeffField d → ℝ :=
    fun a =>
      terminalUncenteredCoarseBlockNorm hP hStruct m
        (Homogenization.originCube d (k : ℤ)) a
  let M : Homogenization.CoeffField d → ℝ :=
    terminalCoarseBlockStochasticMax hP hStruct hc N m
      (Homogenization.originCube d (m : ℤ))
      (fun x : Homogenization.CoeffField d => x)
  let c : ℝ :=
    ((terminalStochasticWeakWeight (d := d) hc m k
      (Homogenization.originCube d (k : ℤ)))⁻¹).toReal
  let A : ℝ :=
    rho * contrastExcessAtScale hP hStruct m /
      (1 + contrastExcessAtScale hP hStruct m) + 1
  have hT_meas : MeasureTheory.AEStronglyMeasurable T P := by
    simpa [T] using
      (aemeasurable_terminalUncenteredCoarseBlockNorm hP hStruct m
        (Homogenization.originCube d (k : ℤ))).aestronglyMeasurable
  have hR_mem : MeasureTheory.MemLp (fun a => c * M a + A) (2 : ENNReal) P := by
    have hcM_mem : MeasureTheory.MemLp (fun a => c * M a) (2 : ENNReal) P := by
      simpa [M, c] using hM_mem.const_mul c
    have hA_mem : MeasureTheory.MemLp (fun _ : Homogenization.CoeffField d => A)
        (2 : ENNReal) P :=
      MeasureTheory.memLp_const A
    simpa [Pi.add_apply] using hcM_mem.add hA_mem
  refine hR_mem.mono hT_meas ?_
  filter_upwards with a
  have hT_nonneg : 0 ≤ T a := by
    dsimp [T, terminalUncenteredCoarseBlockNorm]
    exact fullBlockOperatorNorm_nonneg _
  have hpoint : T a ≤ c * M a + A := by
    have hraw :=
      terminalUncenteredCoarseBlockNorm_origin_le_stochasticMax_add_noDrop_drift_add_one
        hP hStruct hP4 hc hNk hkm hno a
    dsimp [T, M, c, A]
    nlinarith
  have hR_nonneg : 0 ≤ c * M a + A := hT_nonneg.trans hpoint
  rw [Real.norm_of_nonneg hT_nonneg, Real.norm_of_nonneg hR_nonneg]
  exact hpoint

/--
Source labels `e.J.moment.bound`, `M_m^st`, and `l.S.and.J`: the terminal
uncentered norm has a concrete second-moment root bound by the stochastic
maximum and the deterministic no-drop drift term.  This is the moment version
of the source line bounding the normalized block response by the `L^Q`
hypothesis plus no-drop normalization.
-/
theorem terminalUncenteredCoarseBlockNorm_origin_annealedMomentRoot_two_le_stochasticMax_add_noDrop_drift
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {rho : ℝ} {N k m : ℕ}
    (hrho_nonneg : 0 ≤ rho)
    (hNk : N ≤ k) (hkm : k ≤ m)
    (hno :
      noDropWindow rho
        (contrastExcessAtScale hP hStruct k)
        (contrastExcessAtScale hP hStruct m))
    (hM_mem :
      MeasureTheory.MemLp
        (terminalCoarseBlockStochasticMax hP hStruct hc N m
          (Homogenization.originCube d (m : ℤ))
          (fun x : Homogenization.CoeffField d => x))
        (2 : ENNReal) P) :
    Homogenization.Book.Ch04.annealedMomentRoot P 2
        (fun a : Homogenization.CoeffField d =>
          terminalUncenteredCoarseBlockNorm hP hStruct m
            (Homogenization.originCube d (k : ℤ)) a) ≤
      rho * contrastExcessAtScale hP hStruct m /
          (1 + contrastExcessAtScale hP hStruct m) + 1 +
        ((terminalStochasticWeakWeight (d := d) hc m k
          (Homogenization.originCube d (k : ℤ)))⁻¹).toReal *
          Homogenization.Book.Ch04.annealedMomentRoot P 2
            (terminalCoarseBlockStochasticMax hP hStruct hc N m
              (Homogenization.originCube d (m : ℤ))
              (fun x : Homogenization.CoeffField d => x)) := by
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  let T : Homogenization.CoeffField d → ℝ :=
    fun a =>
      terminalUncenteredCoarseBlockNorm hP hStruct m
        (Homogenization.originCube d (k : ℤ)) a
  let M : Homogenization.CoeffField d → ℝ :=
    terminalCoarseBlockStochasticMax hP hStruct hc N m
      (Homogenization.originCube d (m : ℤ))
      (fun x : Homogenization.CoeffField d => x)
  let c : ℝ :=
    ((terminalStochasticWeakWeight (d := d) hc m k
      (Homogenization.originCube d (k : ℤ)))⁻¹).toReal
  let A : ℝ :=
    rho * contrastExcessAtScale hP hStruct m /
      (1 + contrastExcessAtScale hP hStruct m) + 1
  let E : Homogenization.CoeffField d → ℝ := fun a => c * M a
  have hF_nonneg : 0 ≤ contrastExcessAtScale hP hStruct m :=
    contrastExcessAtScale_nonneg_of_P4 hP hStruct hP4 m
  have hden_pos : 0 < 1 + contrastExcessAtScale hP hStruct m := by linarith
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    have hfrac_nonneg :
        0 ≤ rho * contrastExcessAtScale hP hStruct m /
          (1 + contrastExcessAtScale hP hStruct m) := by
      exact div_nonneg (mul_nonneg hrho_nonneg hF_nonneg) hden_pos.le
    linarith
  have hT_nonneg : ∀ a, 0 ≤ T a := by
    intro a
    dsimp [T, terminalUncenteredCoarseBlockNorm]
    exact fullBlockOperatorNorm_nonneg _
  have hM_nonneg : ∀ a, 0 ≤ M a := by
    intro a
    dsimp [M, terminalCoarseBlockStochasticMax, terminalCoarseBlockStochasticMaxOfWeak]
    exact ENNReal.toReal_nonneg
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact ENNReal.toReal_nonneg
  have hE_nonneg : ∀ a, 0 ≤ E a := fun a =>
    mul_nonneg hc_nonneg (hM_nonneg a)
  have hT_le : ∀ a, T a ≤ A + E a := by
    intro a
    have hpoint :=
      terminalUncenteredCoarseBlockNorm_origin_le_stochasticMax_add_noDrop_drift_add_one
        hP hStruct hP4 hc hNk hkm hno a
    dsimp [T, M, c, A, E]
    nlinarith
  have hT_meas : AEMeasurable T P := by
    simpa [T] using
      aemeasurable_terminalUncenteredCoarseBlockNorm hP hStruct m
        (Homogenization.originCube d (k : ℤ))
  have hE_meas : AEMeasurable E P := by
    exact hM_mem.aestronglyMeasurable.aemeasurable.const_mul c
  have hT_mem :
      MeasureTheory.MemLp T (2 : ENNReal) P := by
    simpa [T, M, c, A] using
      terminalUncenteredCoarseBlockNorm_origin_memLp_two_of_stochasticMax
        hP hStruct hP4 hc hNk hkm hno hM_mem
  have hE_mem : MeasureTheory.MemLp E (2 : ENNReal) P := by
    simpa [E, M, c] using hM_mem.const_mul c
  have hT_int : Integrable (fun a => |T a| ^ (2 : ℕ)) P := by
    have hint := hT_mem.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    simpa [Real.norm_eq_abs] using hint
  have hE_int : Integrable (fun a => |E a| ^ (2 : ℕ)) P := by
    have hint := hE_mem.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    simpa [Real.norm_eq_abs] using hint
  have hroot :=
    Homogenization.Book.Ch04.annealedMomentRoot_le_const_add_of_nonneg_le
      (P := P) (ξ := 2) (X := T) (E := E) (A := A)
      (by norm_num : 1 ≤ (2 : ℕ)) hA_nonneg hT_nonneg hE_nonneg
      hT_le hT_meas hE_meas hT_int hE_int
  have hE_root :
      Homogenization.Book.Ch04.annealedMomentRoot P 2 E =
        c *
          Homogenization.Book.Ch04.annealedMomentRoot P 2 M := by
    simpa [E, M, c] using
      Homogenization.Book.Ch05.Section52.section52_annealedMomentRoot_const_mul_of_nonneg
        (P := P) (ξ := 2) (c := c) (X := M)
        (by norm_num : 1 ≤ (2 : ℕ)) hc_nonneg hM_nonneg
  calc
    Homogenization.Book.Ch04.annealedMomentRoot P 2 T
        ≤ A + Homogenization.Book.Ch04.annealedMomentRoot P 2 E := hroot
    _ =
        A + c * Homogenization.Book.Ch04.annealedMomentRoot P 2 M := by
          rw [hE_root]
    _ =
        rho * contrastExcessAtScale hP hStruct m /
            (1 + contrastExcessAtScale hP hStruct m) + 1 +
          ((terminalStochasticWeakWeight (d := d) hc m k
            (Homogenization.originCube d (k : ℤ)))⁻¹).toReal *
            Homogenization.Book.Ch04.annealedMomentRoot P 2
              (terminalCoarseBlockStochasticMax hP hStruct hc N m
                (Homogenization.originCube d (m : ℤ))
                (fun x : Homogenization.CoeffField d => x)) := by
          rfl

/--
Source labels `M_m^st` and `e.J.moment.bound`: the inverse weak stochastic
weight at the lower edge has the expected real value `3^{rho_M(m-k)}`.
-/
theorem terminalStochasticWeakWeight_inv_toReal_eq
    {d : ℕ} (hc : HighContrastExponents d) (m k : ℕ)
    (R : Homogenization.TriadicCube d) :
    ((terminalStochasticWeakWeight (d := d) hc m k R)⁻¹).toReal =
      (3 : ℝ) ^ (hc.rhoM * ((m - k : ℕ) : ℝ)) := by
  let gap : ℝ := ((m - k : ℕ) : ℝ)
  let x : ℝ := (3 : ℝ) ^ (-hc.rhoM * gap)
  have hx_pos : 0 < x := by
    dsimp [x]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (-hc.rhoM * gap)
  have hreal : x⁻¹ = (3 : ℝ) ^ (hc.rhoM * gap) := by
    calc
      x⁻¹ = ((3 : ℝ) ^ (-hc.rhoM * gap))⁻¹ := by rfl
      _ = (3 : ℝ) ^ (-(-hc.rhoM * gap)) := by
            rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
      _ = (3 : ℝ) ^ (hc.rhoM * gap) := by
            congr 1
            ring
  calc
    ((terminalStochasticWeakWeight (d := d) hc m k R)⁻¹).toReal =
        ((ENNReal.ofReal x)⁻¹).toReal := by rfl
    _ = (ENNReal.ofReal x⁻¹).toReal := by
          rw [← ENNReal.ofReal_inv_of_pos hx_pos]
    _ = (3 : ℝ) ^ (hc.rhoM * ((m - k : ℕ) : ℝ)) := by
          rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hx_pos.le), hreal]

/--
Source labels `M_m^st` and `e.J.moment.bound`: on a fixed response window
`m-k <= L`, the inverse weak stochastic weight is bounded by the endpoint
loss.
-/
theorem terminalStochasticWeakWeight_inv_toReal_le_of_sub_le
    {d : ℕ} (hc : HighContrastExponents d) {k m L : ℕ}
    (hWindow : m - k ≤ L) (R : Homogenization.TriadicCube d) :
    ((terminalStochasticWeakWeight (d := d) hc m k R)⁻¹).toReal ≤
      (3 : ℝ) ^ (hc.rhoM * (L : ℝ)) := by
  have hgap_le_window_real : ((m - k : ℕ) : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast hWindow
  have hexp_le :
      hc.rhoM * ((m - k : ℕ) : ℝ) ≤ hc.rhoM * (L : ℝ) :=
    mul_le_mul_of_nonneg_left hgap_le_window_real (le_of_lt hc.rhoM_pos)
  rw [terminalStochasticWeakWeight_inv_toReal_eq]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp_le

/--
Source labels `e.J.moment.bound`, `M_m^st`, and `l.S.and.J`: fixed-window
form of the terminal uncentered norm moment estimate.  The no-drop drift is
absorbed into the constant `2`, and the only remaining random term is the
source stochastic maximum.
-/
theorem terminalUncenteredCoarseBlockNorm_origin_annealedMomentRoot_two_le_window_stochasticMax_add_two
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {rho : ℝ} {N k m L : ℕ}
    (hrho_nonneg : 0 ≤ rho) (hrho_le_one : rho ≤ 1)
    (hNk : N ≤ k) (hkm : k ≤ m) (hWindow : m - k ≤ L)
    (hno :
      noDropWindow rho
        (contrastExcessAtScale hP hStruct k)
        (contrastExcessAtScale hP hStruct m))
    (hM_mem :
      MeasureTheory.MemLp
        (terminalCoarseBlockStochasticMax hP hStruct hc N m
          (Homogenization.originCube d (m : ℤ))
          (fun x : Homogenization.CoeffField d => x))
        (2 : ENNReal) P) :
    Homogenization.Book.Ch04.annealedMomentRoot P 2
        (fun a : Homogenization.CoeffField d =>
          terminalUncenteredCoarseBlockNorm hP hStruct m
            (Homogenization.originCube d (k : ℤ)) a) ≤
      (3 : ℝ) ^ (hc.rhoM * (L : ℝ)) *
          Homogenization.Book.Ch04.annealedMomentRoot P 2
            (terminalCoarseBlockStochasticMax hP hStruct hc N m
              (Homogenization.originCube d (m : ℤ))
              (fun x : Homogenization.CoeffField d => x)) + 2 := by
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  let M : Homogenization.CoeffField d → ℝ :=
    terminalCoarseBlockStochasticMax hP hStruct hc N m
      (Homogenization.originCube d (m : ℤ))
      (fun x : Homogenization.CoeffField d => x)
  let c : ℝ :=
    ((terminalStochasticWeakWeight (d := d) hc m k
      (Homogenization.originCube d (k : ℤ)))⁻¹).toReal
  let Cw : ℝ := (3 : ℝ) ^ (hc.rhoM * (L : ℝ))
  let A : ℝ :=
    rho * contrastExcessAtScale hP hStruct m /
      (1 + contrastExcessAtScale hP hStruct m) + 1
  have hF_nonneg : 0 ≤ contrastExcessAtScale hP hStruct m :=
    contrastExcessAtScale_nonneg_of_P4 hP hStruct hP4 m
  have hden_pos : 0 < 1 + contrastExcessAtScale hP hStruct m := by linarith
  have hfrac_le_one :
      rho * contrastExcessAtScale hP hStruct m /
          (1 + contrastExcessAtScale hP hStruct m) ≤ 1 := by
    rw [div_le_iff₀ hden_pos]
    have hmul_le : rho * contrastExcessAtScale hP hStruct m ≤
        1 * contrastExcessAtScale hP hStruct m :=
      mul_le_mul_of_nonneg_right hrho_le_one hF_nonneg
    linarith
  have hA_le_two : A ≤ 2 := by
    dsimp [A]
    linarith
  have hc_le : c ≤ Cw := by
    simpa [c, Cw] using
      terminalStochasticWeakWeight_inv_toReal_le_of_sub_le
        (d := d) hc hWindow (Homogenization.originCube d (k : ℤ))
  have hM_nonneg : ∀ a, 0 ≤ M a := by
    intro a
    dsimp [M, terminalCoarseBlockStochasticMax, terminalCoarseBlockStochasticMaxOfWeak]
    exact ENNReal.toReal_nonneg
  have hM_root_nonneg :
      0 ≤ Homogenization.Book.Ch04.annealedMomentRoot P 2 M :=
    Homogenization.Book.Ch04.annealedMomentRoot_nonneg_of_nonneg P 2 hM_nonneg
  have hroot :=
    terminalUncenteredCoarseBlockNorm_origin_annealedMomentRoot_two_le_stochasticMax_add_noDrop_drift
      hP hStruct hP4 hc hrho_nonneg hNk hkm hno hM_mem
  calc
    Homogenization.Book.Ch04.annealedMomentRoot P 2
        (fun a : Homogenization.CoeffField d =>
          terminalUncenteredCoarseBlockNorm hP hStruct m
            (Homogenization.originCube d (k : ℤ)) a)
        ≤ A + c * Homogenization.Book.Ch04.annealedMomentRoot P 2 M := by
          simpa [A, c, M] using hroot
    _ ≤ 2 + Cw * Homogenization.Book.Ch04.annealedMomentRoot P 2 M := by
          exact add_le_add hA_le_two
            (mul_le_mul_of_nonneg_right hc_le hM_root_nonneg)
    _ =
        (3 : ℝ) ^ (hc.rhoM * (L : ℝ)) *
            Homogenization.Book.Ch04.annealedMomentRoot P 2
              (terminalCoarseBlockStochasticMax hP hStruct hc N m
                (Homogenization.originCube d (m : ℤ))
                (fun x : Homogenization.CoeffField d => x)) + 2 := by
          rw [add_comm]

/--
Source labels `M_m^st` and `e.J.moment.bound`: convert an `ENNReal`
second-moment estimate into the real `L^2` annealed moment root used by the
response estimate.
-/
theorem memLp_two_and_annealedMomentRoot_two_le_of_lintegral_enorm_sq_le
    {d : ℕ} {P : Homogenization.Book.Ch04.CoeffLaw d}
    [MeasureTheory.IsProbabilityMeasure P]
    {X : Homogenization.CoeffField d → ℝ} {η : ℝ}
    (hX_meas : MeasureTheory.AEStronglyMeasurable X P)
    (hX_nonneg : ∀ a, 0 ≤ X a) (hη_nonneg : 0 ≤ η)
    (hlin :
      ∫⁻ a, ‖X a‖ₑ ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal (η ^ 2)) :
    MeasureTheory.MemLp X (2 : ENNReal) P ∧
      Homogenization.Book.Ch04.annealedMomentRoot P 2 X ≤ η := by
  have hp_ne_zero : (2 : ENNReal) ≠ 0 := by norm_num
  have hp_ne_top : (2 : ENNReal) ≠ ⊤ := by simp
  have hlin_lt_top :
      ∫⁻ a, ‖X a‖ₑ ^ (2 : ℝ) ∂P < ⊤ :=
    lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  have hX_mem : MeasureTheory.MemLp X (2 : ENNReal) P := by
    refine ⟨hX_meas, ?_⟩
    rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      hp_ne_zero hp_ne_top]
    simpa using hlin_lt_top
  have hpow_eq :
      (ENNReal.ofReal (η ^ 2)) ^ ((1 : ℝ) / 2) = ENNReal.ofReal η := by
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg η)
      (by norm_num : 0 ≤ ((1 : ℝ) / 2))]
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_nonneg hη_nonneg]
  have hELp :
      MeasureTheory.eLpNorm X (2 : ENNReal) P ≤ ENNReal.ofReal η := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm hp_ne_zero hp_ne_top]
    have hpow_mono :=
      ENNReal.rpow_le_rpow hlin (by norm_num : 0 ≤ ((1 : ℝ) / 2))
    exact hpow_mono.trans_eq hpow_eq
  have hroot_toReal :
      (MeasureTheory.eLpNorm X (2 : ENNReal) P).toReal =
        Homogenization.Book.Ch04.annealedMomentRoot P 2 X := by
    calc
      (MeasureTheory.eLpNorm X (2 : ENNReal) P).toReal =
          (∫ a, ‖X a‖ ^ (2 : ℕ) ∂P) ^ (1 / (2 : ℝ)) := by
            exact Homogenization.Book.Ch04.toReal_eLpNorm_eq_integral_norm_pow_rpow_inv
              (μ := P) (f := X) (p := 2) (by norm_num) hX_mem
      _ = Homogenization.Book.Ch04.annealedMomentRoot P 2 X := by
            rw [Homogenization.Book.Ch04.annealedMomentRoot]
            congr 1
            exact integral_congr_ae
              (Filter.Eventually.of_forall fun a => by
                simp [Real.norm_of_nonneg (hX_nonneg a)])
  have hroot_le :
      Homogenization.Book.Ch04.annealedMomentRoot P 2 X ≤ η := by
    calc
      Homogenization.Book.Ch04.annealedMomentRoot P 2 X =
          (MeasureTheory.eLpNorm X (2 : ENNReal) P).toReal := hroot_toReal.symm
      _ ≤ (ENNReal.ofReal η).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hELp
      _ = η := ENNReal.toReal_ofReal hη_nonneg
  exact ⟨hX_mem, hroot_le⟩

/--
Source labels `M_m^st`, `a.HM`, and `e.J.moment.bound`: buffered high
centered moments imply an `L^2` annealed moment-root bound for the source
terminal stochastic maximum over the terminal origin cube.
-/
theorem exists_bufferExponent_terminalCoarseBlockStochasticMax_annealedMomentRoot_two_le_of_Nstar
    {d : ℕ} [NeZero d] {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) {η_M : ℝ} (hη_M : 0 < η_M) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {P : Homogenization.Book.Ch04.CoeffLaw d}
        (hP : Homogenization.Book.Ch04.LawCarrier P)
        (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
        {N m : ℕ},
          N + Nat.ceil
              (B * Real.logb 3
                (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) ≤
            m →
          HighCenteredMomentEstimate hm P N
            (intermediateCoarseBlockDeviation hP hStruct
              (fun x : Homogenization.CoeffField d => x)) →
          MeasureTheory.MemLp
            (terminalCoarseBlockStochasticMax hP hStruct hc N m
              (Homogenization.originCube d (m : ℤ))
              (fun x : Homogenization.CoeffField d => x))
            (2 : ENNReal) P ∧
          Homogenization.Book.Ch04.annealedMomentRoot P 2
            (terminalCoarseBlockStochasticMax hP hStruct hc N m
              (Homogenization.originCube d (m : ℤ))
              (fun x : Homogenization.CoeffField d => x)) ≤ η_M := by
  let η_sq : ℝ := η_M ^ 2
  let η_total : ℝ := 2 * η_sq
  let η_terminal : ℝ := η_sq ^ (hm.Q / 2)
  have hη_sq_pos : 0 < η_sq := by
    dsimp [η_sq]
    exact sq_pos_of_pos hη_M
  have hη_total_pos : 0 < η_total := by
    dsimp [η_total]
    positivity
  have hη_terminal_pos : 0 < η_terminal := by
    dsimp [η_terminal]
    exact Real.rpow_pos_of_pos hη_sq_pos (hm.Q / 2)
  obtain ⟨B, hB_one, hB⟩ :=
    exists_bufferExponent_lintegral_enorm_rpow_two_terminalCoarseBlockStochasticMax_le_of_Nstar
      hm hη_terminal_pos
  refine ⟨B, hB_one, ?_⟩
  intro P hP hStruct hP4 N m hNstar hHM
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  let M : Homogenization.CoeffField d → ℝ :=
    terminalCoarseBlockStochasticMax hP hStruct hc N m
      (Homogenization.originCube d (m : ℤ))
      (fun x : Homogenization.CoeffField d => x)
  have hQscale : (Homogenization.originCube d (m : ℤ)).scale = (m : ℤ) := by
    simp [Homogenization.originCube]
  have hM_meas :
      MeasureTheory.AEStronglyMeasurable M P := by
    simpa [M] using
      aestronglyMeasurable_terminalCoarseBlockStochasticMax_origin
        hP hStruct hP4 hc N m
  have hlin_raw :=
    hB hP hStruct hP4 P (Homogenization.originCube d (m : ℤ))
      hQscale hNstar (fun x : Homogenization.CoeffField d => x) hM_meas hHM
  have hbudget :
      (ENNReal.ofReal η_terminal) ^ ((2 : ℝ) / hm.Q) =
        ENNReal.ofReal η_sq := by
    have h :=
      ofReal_highCenteredMoment_halfBudget_rpow_eq
        (d := d) (hc := hc) hm hη_total_pos
    simpa [η_terminal, η_total, η_sq] using h
  have hlin :
      ∫⁻ a, ‖M a‖ₑ ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal (η_M ^ 2) := by
    exact hlin_raw.trans_eq (by simpa [η_sq] using hbudget)
  have hM_nonneg : ∀ a, 0 ≤ M a := by
    intro a
    dsimp [M, terminalCoarseBlockStochasticMax, terminalCoarseBlockStochasticMaxOfWeak]
    exact ENNReal.toReal_nonneg
  simpa [M] using
    memLp_two_and_annealedMomentRoot_two_le_of_lintegral_enorm_sq_le
      (P := P) (X := M) hM_meas hM_nonneg (le_of_lt hη_M) hlin

end Homogenization.HighContrast.EntryScale
