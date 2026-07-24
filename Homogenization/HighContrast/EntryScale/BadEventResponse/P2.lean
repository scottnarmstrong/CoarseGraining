import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Homogenization.HighContrast.EntryScale.TerminalLowerEdge
import Homogenization.HighContrast.EntryScale.BadEventResponse.P1

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open MeasureTheory

namespace Homogenization.HighContrast.EntryScale

noncomputable section

/--
Design item L-C integrability companion.  The capped source maximum pairs
integrably against the child response average: the cap lies in `L^xi` by
boundedness, the child average lies in the conjugate `L^zeta` by the
stationary descendants-average moment estimate, and the Hölder triple closes
integrability of the product.
-/
theorem integrable_min_terminalSourceMax_one_mul_childResponseAverage_special
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hstat : Homogenization.Book.Ch04.StationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {k m : ℕ}
    (hkm : k < m) (e : Homogenization.Vec d) :
    let Qm : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let childAvg := fun a : Homogenization.CoeffField d =>
      Homogenization.descendantsAverage Qm (m - k)
        (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
    let sourceMax :=
      terminalSpectralPositivePartSourceMax hP hStruct hc k m Qm
        (fun x : Homogenization.CoeffField d => x)
    MeasureTheory.Integrable
      (fun a : Homogenization.CoeffField d =>
        min (sourceMax a) 1 * childAvg a) P := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  dsimp only
  let ζ := section53CoarseFluctuationZeta hP4
  let ξr : ℝ := (hP4.xi : ℝ)
  let Qm : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let childAvg : Homogenization.CoeffField d → ℝ := fun a =>
    Homogenization.descendantsAverage Qm (m - k)
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
  let sourceMax : Homogenization.CoeffField d → ℝ :=
    terminalSpectralPositivePartSourceMax hP hStruct hc k m Qm
      (fun x : Homogenization.CoeffField d => x)
  have hζ_one : 1 ≤ ζ := (one_lt_section53CoarseFluctuationZeta hP4).le
  have hsrc_nonneg : ∀ a, 0 ≤ sourceMax a :=
    terminalSpectralPositivePartSourceMax_nonneg hP hStruct hc k m Qm
      (fun x : Homogenization.CoeffField d => x)
  have hsrc_asm : MeasureTheory.AEStronglyMeasurable sourceMax P := by
    simpa [sourceMax, Qm] using
      aestronglyMeasurable_terminalSpectralPositivePartSourceMax_origin
        hP hStruct hc k m
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by
    exact_mod_cast Nat.zero_le k
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by
    exact_mod_cast hkm.le
  have hdepth : Int.toNat ((m : ℤ) - (k : ℤ)) = m - k := by
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hkm_int)]
    exact (Nat.cast_sub hkm.le).symm
  have hChildMem :
      MeasureTheory.MemLp childAvg (ENNReal.ofReal ζ) P := by
    simpa [childAvg, Qm, p_e, q_e, ζ, hdepth] using
      memLp_zeta_descendantsAverage_responseJObservableCubeSet_originCube_from_P4_of_stationary
        hP hstat hStruct hP4 hk_nonneg hkm_int p_e q_e
  have hminSrc_mem :
      MeasureTheory.MemLp (fun a => min (sourceMax a) 1)
        (ENNReal.ofReal ξr) P :=
    memLp_min_one_of_aestronglyMeasurable hsrc_asm hsrc_nonneg _
  have hHolderXiZeta : ξr.HolderConjugate ζ :=
    holderConjugate_xi_section53CoarseFluctuationZeta hP4
  letI : ENNReal.HolderTriple (ENNReal.ofReal ξr) (ENNReal.ofReal ζ) 1 := by
    simpa using Real.HolderTriple.ennrealOfReal hHolderXiZeta
  have hmain := hminSrc_mem.integrable_mul hChildMem
  simpa [childAvg, sourceMax, Qm, p_e, q_e, Pi.mul_apply] using hmain
/--
Mixed-scale variant of design item L-D: the bad-event truncation of the
terminal source maximum over the FULL start window `[N, m]` is paired against
the child response average at the CURRENT window `(k, m)`.  Same Hölder
`(xi, zeta)` pairing; the `L^{2 xi}` envelope is the global polynomial root
plus the deterministic drift supremum, exactly as in L-D.
-/
theorem integral_badEventTruncation_terminalSourceMax_start_mul_childResponseAverage_le_responseMoment_mul_global_polynomialRoot_add_drift
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hstat : Homogenization.Book.Ch04.StationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d)
    (hm : HighCenteredMomentParameters d hc)
    (hparams : hP4.params = hm.p4Params) {N k m : ℕ}
    (hNk : N ≤ k) (hkm : k < m)
    (hHM :
      HighCenteredMomentEstimate hm P N
        (intermediateCoarseBlockDeviation hP hStruct
          (fun x : Homogenization.CoeffField d => x)))
    (e : Homogenization.Vec d) :
    let Qm : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let childAvg := fun a : Homogenization.CoeffField d =>
      Homogenization.descendantsAverage Qm (m - k)
        (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
    let sourceMax :=
      terminalSpectralPositivePartSourceMax hP hStruct hc N m Qm
        (fun x : Homogenization.CoeffField d => x)
    let globalDrift := terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)
    let polynomialBound : ENNReal :=
      ENNReal.ofReal
        (((2 +
          Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
          (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - N : ℕ) : ℝ)))))
    MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d =>
          badEventTruncation sourceMax a * childAvg a) P ∧
      ∫ a, badEventTruncation sourceMax a * childAvg a ∂P ≤
        coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e *
          ((polynomialBound ^ (1 / hm.Q)).toReal + globalDrift) := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  dsimp only
  let ζ := section53CoarseFluctuationZeta hP4
  let Qm : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let childAvg : Homogenization.CoeffField d → ℝ := fun a =>
    Homogenization.descendantsAverage Qm (m - k)
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
  let sourceMax : Homogenization.CoeffField d → ℝ :=
    terminalSpectralPositivePartSourceMax hP hStruct hc N m Qm
      (fun x : Homogenization.CoeffField d => x)
  let badTrunc : Homogenization.CoeffField d → ℝ := badEventTruncation sourceMax
  let globalDrift : ℝ := terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)
  let polynomialBound : ENNReal :=
    ENNReal.ofReal
      (((2 +
        Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
        (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
          (3 : ℝ) ^
            (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
              ((m - N : ℕ) : ℝ)))))
  let sourceBound : ENNReal :=
    polynomialBound ^ (1 / hm.Q) + ENNReal.ofReal globalDrift
  let responseMoment : ℝ :=
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  have hxi_pos : (0 : ℝ) < (hP4.xi : ℝ) := by
    exact_mod_cast hP4.xi_pos
  have hxi_one : 1 ≤ hP4.xi := Nat.succ_le_of_lt hP4.xi_pos
  have hsource_nonneg : ∀ a, 0 ≤ sourceMax a :=
    terminalSpectralPositivePartSourceMax_nonneg hP hStruct hc N m Qm
      (fun x : Homogenization.CoeffField d => x)
  have hbad_nonneg : ∀ a, 0 ≤ badTrunc a := fun a =>
    badEventTruncation_nonneg (hsource_nonneg a)
  have hchild_nonneg : ∀ a, 0 ≤ childAvg a := by
    intro a
    dsimp [childAvg]
    exact Homogenization.descendantsAverage_nonneg Qm (m - k)
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
      (fun R _hR =>
        Homogenization.Book.Ch04.responseJObservableCubeSet_nonneg R p_e q_e a)
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by
    exact_mod_cast Nat.zero_le k
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by
    exact_mod_cast hkm.le
  have hdepth : Int.toNat ((m : ℤ) - (k : ℤ)) = m - k := by
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hkm_int)]
    exact (Nat.cast_sub hkm.le).symm
  have hChildMem :
      MeasureTheory.MemLp childAvg (ENNReal.ofReal ζ) P := by
    simpa [childAvg, Qm, p_e, q_e, ζ, hdepth] using
      memLp_zeta_descendantsAverage_responseJObservableCubeSet_originCube_from_P4_of_stationary
        hP hstat hStruct hP4 hk_nonneg hkm_int p_e q_e
  have hSourceMem :
      MeasureTheory.MemLp sourceMax (ENNReal.ofReal hm.Q) P := by
    simpa [sourceMax, Qm] using
      memLp_terminalSpectralPositivePartSourceMax_origin_highMoment
        hP hStruct hP4 hm (hNk.trans hkm.le)
        (HighCenteredMomentEstimate.of_start_le (le_refl N) hHM)
  have hxi_le_Q : (hP4.xi : ℝ) ≤ hm.Q := by
    have h2 := highCenteredMoment_two_mul_p4_xi_le_Q hm hP4 hparams
    linarith
  have hBadMem :
      MeasureTheory.MemLp badTrunc (ENNReal.ofReal (hP4.xi : ℝ)) P := by
    refine
      (hSourceMem.mono_exponent (ENNReal.ofReal_le_ofReal hxi_le_Q)).of_le
        (aestronglyMeasurable_badEventTruncation hSourceMem.1) ?_
    filter_upwards with a
    have hle : badTrunc a ≤ sourceMax a :=
      badEventTruncation_le_self_of_nonneg (hsource_nonneg a)
    simpa [Real.norm_eq_abs, abs_of_nonneg (hbad_nonneg a),
      abs_of_nonneg (hsource_nonneg a)] using hle
  have hHolderXiZeta : (hP4.xi : ℝ).HolderConjugate ζ :=
    holderConjugate_xi_section53CoarseFluctuationZeta hP4
  letI : ENNReal.HolderTriple
      (ENNReal.ofReal (hP4.xi : ℝ)) (ENNReal.ofReal ζ) 1 := by
    simpa using Real.HolderTriple.ennrealOfReal hHolderXiZeta
  have hInt :
      MeasureTheory.Integrable
        (fun a : Homogenization.CoeffField d => badTrunc a * childAvg a) P := by
    simpa using hBadMem.integrable_mul hChildMem
  have hHolder :
      ∫ a, badTrunc a * childAvg a ∂P ≤
        (∫ a, badTrunc a ^ (hP4.xi : ℝ) ∂P) ^ (1 / (hP4.xi : ℝ)) *
          (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) :=
    MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hHolderXiZeta
      (Filter.Eventually.of_forall hbad_nonneg)
      (Filter.Eventually.of_forall hchild_nonneg) hBadMem hChildMem
  have hchildRoot_le :
      (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) ≤ responseMoment := by
    simpa [childAvg, Qm, ζ, p_e, q_e, responseMoment] using
      childResponseAverage_zetaRoot_le_responseMoment_of_stationary
        hP hstat hStruct hP4 hkm e
  have hchildRoot_nonneg :
      0 ≤ (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) :=
    Real.rpow_nonneg
      (MeasureTheory.integral_nonneg fun a =>
        Real.rpow_nonneg (hchild_nonneg a) _) _
  have hresponse_nonneg : 0 ≤ responseMoment := by
    simpa [responseMoment] using
      coarseFluctuationResponseMomentAtScale_nonneg hP hStruct hP4 k m e
  have hBadMemNat :
      MeasureTheory.MemLp badTrunc ((hP4.xi : ℕ) : ENNReal) P := by
    simpa [ENNReal.ofReal_natCast] using hBadMem
  have hbadRoot_eq :
      (∫ a, badTrunc a ^ (hP4.xi : ℝ) ∂P) ^ (1 / (hP4.xi : ℝ)) =
        (MeasureTheory.eLpNorm badTrunc ((hP4.xi : ℕ) : ENNReal) P).toReal := by
    have htoReal :=
      Homogenization.Book.Ch04.toReal_eLpNorm_eq_integral_norm_pow_rpow_inv
        (μ := P) (f := badTrunc) (p := hP4.xi) hxi_one hBadMemNat
    calc
      (∫ a, badTrunc a ^ (hP4.xi : ℝ) ∂P) ^ (1 / (hP4.xi : ℝ))
          = (∫ a, ‖badTrunc a‖ ^ hP4.xi ∂P) ^ (1 / (hP4.xi : ℝ)) := by
            congr 1
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with a
            rw [Real.norm_of_nonneg (hbad_nonneg a), Real.rpow_natCast]
      _ = (MeasureTheory.eLpNorm badTrunc ((hP4.xi : ℕ) : ENNReal) P).toReal :=
            htoReal.symm
  have hmono_eLp :
      MeasureTheory.eLpNorm badTrunc ((hP4.xi : ℕ) : ENNReal) P ≤
        MeasureTheory.eLpNorm badTrunc
          (ENNReal.ofReal (2 * (hP4.xi : ℝ))) P := by
    have hle : ((hP4.xi : ℕ) : ENNReal) ≤ ENNReal.ofReal (2 * (hP4.xi : ℝ)) := by
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    exact MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le hle hBadMem.1
  have hglobal_eLp :
      MeasureTheory.eLpNorm badTrunc
          (ENNReal.ofReal (2 * (hP4.xi : ℝ))) P ≤ sourceBound := by
    simpa [badTrunc, sourceBound, polynomialBound, sourceMax, Qm,
      globalDrift] using
      eLpNorm_badEventTruncation_terminalSourceMax_le_global_polynomial_add_drift_of_start_le
        hP hStruct hP4 hc hm hparams (le_refl N) (hNk.trans hkm.le) hHM
  have hQ_pos : 0 < hm.Q := highCenteredMoment_Q_pos hm
  have hpolyRoot_ne_top : polynomialBound ^ (1 / hm.Q) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg
      (one_div_nonneg.mpr hQ_pos.le) ENNReal.ofReal_ne_top
  have hsourceBound_ne_top : sourceBound ≠ ⊤ := by
    dsimp [sourceBound]
    exact ENNReal.add_ne_top.2 ⟨hpolyRoot_ne_top, ENNReal.ofReal_ne_top⟩
  have hdrift_nonneg : 0 ≤ globalDrift :=
    terminalBadMaximalDriftSup_nonneg hP hStruct hc (hNk.trans hkm.le)
  have hsourceBound_toReal :
      sourceBound.toReal = (polynomialBound ^ (1 / hm.Q)).toReal + globalDrift := by
    dsimp [sourceBound]
    rw [ENNReal.toReal_add hpolyRoot_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hdrift_nonneg]
  have hbadRoot_le :
      (∫ a, badTrunc a ^ (hP4.xi : ℝ) ∂P) ^ (1 / (hP4.xi : ℝ)) ≤
        (polynomialBound ^ (1 / hm.Q)).toReal + globalDrift := by
    rw [hbadRoot_eq, ← hsourceBound_toReal]
    exact ENNReal.toReal_mono hsourceBound_ne_top
      (hmono_eLp.trans hglobal_eLp)
  have hbound_nonneg :
      0 ≤ (polynomialBound ^ (1 / hm.Q)).toReal + globalDrift :=
    add_nonneg ENNReal.toReal_nonneg hdrift_nonneg
  constructor
  · simpa [badTrunc, sourceMax, childAvg, Qm, p_e, q_e] using hInt
  · calc
      ∫ a, badEventTruncation sourceMax a * childAvg a ∂P
          = ∫ a, badTrunc a * childAvg a ∂P := by rfl
      _ ≤ (∫ a, badTrunc a ^ (hP4.xi : ℝ) ∂P) ^ (1 / (hP4.xi : ℝ)) *
            (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) := hHolder
      _ ≤ ((polynomialBound ^ (1 / hm.Q)).toReal + globalDrift) *
            responseMoment :=
          mul_le_mul hbadRoot_le hchildRoot_le hchildRoot_nonneg hbound_nonneg
      _ = responseMoment *
            ((polynomialBound ^ (1 / hm.Q)).toReal + globalDrift) := by ring

/--
Mixed-scale variant of design item L-C: the capped terminal source maximum
over the FULL start window `[N, m]` is paired against the child response
average at the CURRENT window `(k, m)`.  The stochastic/subthreshold/drift
envelope split and the capped Hölder pairing are unchanged.
-/
theorem integral_min_terminalSourceMax_start_one_mul_childResponseAverage_le_stochasticRoot_add_min_drift_one_mul_responseMoment
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hstat : Homogenization.Book.Ch04.StationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {N k m : ℕ}
    (hNk : N ≤ k) (hkm : k < m)
    (M_sub : ℕ → Homogenization.CoeffField d → ℝ)
    (hMsub : AEMeasurable (M_sub m) P)
    (e : Homogenization.Vec d)
    {stochRoot : ℝ}
    (hfin :
      (∫⁻ ω, ‖terminalCoarseBlockStochasticMax hP hStruct hc N m
          (Homogenization.originCube d (m : ℤ))
          (fun x : Homogenization.CoeffField d => x) ω‖ₑ ^ (2 : ℝ) ∂P) +
        (∫⁻ ω, ‖M_sub m ω‖ₑ ^ (2 : ℝ) ∂P) ≠ ⊤)
    (hstochRoot :
      2 * (((∫⁻ ω, ‖terminalCoarseBlockStochasticMax hP hStruct hc N m
            (Homogenization.originCube d (m : ℤ))
            (fun x : Homogenization.CoeffField d => x) ω‖ₑ ^ (2 : ℝ) ∂P) +
          (∫⁻ ω, ‖M_sub m ω‖ₑ ^ (2 : ℝ) ∂P)).toReal ^ (1 / (hP4.xi : ℝ))) ≤
        stochRoot) :
    let Qm : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let childAvg := fun a : Homogenization.CoeffField d =>
      Homogenization.descendantsAverage Qm (m - k)
        (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
    let sourceMax :=
      terminalSpectralPositivePartSourceMax hP hStruct hc N m Qm
        (fun x : Homogenization.CoeffField d => x)
    ∫ a, min (sourceMax a) 1 * childAvg a ∂P ≤
      (stochRoot +
          min (terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)) 1) *
        coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  dsimp only
  let ζ := section53CoarseFluctuationZeta hP4
  let ξr : ℝ := (hP4.xi : ℝ)
  let Qm : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let childAvg : Homogenization.CoeffField d → ℝ := fun a =>
    Homogenization.descendantsAverage Qm (m - k)
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
  let sourceMax : Homogenization.CoeffField d → ℝ :=
    terminalSpectralPositivePartSourceMax hP hStruct hc N m Qm
      (fun x : Homogenization.CoeffField d => x)
  let S : Homogenization.CoeffField d → ℝ :=
    terminalCoarseBlockStochasticMax hP hStruct hc N m Qm
      (fun x : Homogenization.CoeffField d => x)
  let T : Homogenization.CoeffField d → ℝ := fun a => |M_sub m a|
  let D : ℝ := terminalBadMaximalDriftSup hP hStruct hc (hNk.trans hkm.le)
  let lintSum : ENNReal :=
    (∫⁻ ω, ‖S ω‖ₑ ^ (2 : ℝ) ∂P) + (∫⁻ ω, ‖M_sub m ω‖ₑ ^ (2 : ℝ) ∂P)
  let sumRoot : ℝ := lintSum.toReal ^ (1 / ξr)
  let responseMoment : ℝ :=
    coarseFluctuationResponseMomentAtScale hP hStruct hP4 k m e
  have hxi_two : (2 : ℝ) ≤ ξr := by
    show (2 : ℝ) ≤ (hP4.xi : ℝ)
    exact_mod_cast hP4.two_le_xi
  have hxi_pos : (0 : ℝ) < ξr := lt_of_lt_of_le two_pos hxi_two
  have hζ_one : 1 ≤ ζ := (one_lt_section53CoarseFluctuationZeta hP4).le
  have hS_nonneg : ∀ a, 0 ≤ S a :=
    terminalCoarseBlockStochasticMax_nonneg hP hStruct hc N m Qm
      (fun x : Homogenization.CoeffField d => x)
  have hT_nonneg : ∀ a, 0 ≤ T a := fun a => abs_nonneg _
  have hD_nonneg : 0 ≤ D :=
    terminalBadMaximalDriftSup_nonneg hP hStruct hc (hNk.trans hkm.le)
  have hsrc_nonneg : ∀ a, 0 ≤ sourceMax a :=
    terminalSpectralPositivePartSourceMax_nonneg hP hStruct hc N m Qm
      (fun x : Homogenization.CoeffField d => x)
  have hchild_nonneg : ∀ a, 0 ≤ childAvg a := by
    intro a
    dsimp [childAvg]
    exact Homogenization.descendantsAverage_nonneg Qm (m - k)
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
      (fun R _hR =>
        Homogenization.Book.Ch04.responseJObservableCubeSet_nonneg R p_e q_e a)
  have hS_asm : MeasureTheory.AEStronglyMeasurable S P := by
    simpa [S, Qm] using
      aestronglyMeasurable_terminalCoarseBlockStochasticMax_origin
        hP hStruct hP4 hc N m
  have hT_asm : MeasureTheory.AEStronglyMeasurable T P := by
    simpa [T, Real.norm_eq_abs] using hMsub.aestronglyMeasurable.norm
  have hsrc_asm : MeasureTheory.AEStronglyMeasurable sourceMax P := by
    simpa [sourceMax, Qm] using
      aestronglyMeasurable_terminalSpectralPositivePartSourceMax_origin
        hP hStruct hc N m
  -- membership of the child average and the capped observables
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by
    exact_mod_cast Nat.zero_le k
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by
    exact_mod_cast hkm.le
  have hdepth : Int.toNat ((m : ℤ) - (k : ℤ)) = m - k := by
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hkm_int)]
    exact (Nat.cast_sub hkm.le).symm
  have hChildMem :
      MeasureTheory.MemLp childAvg (ENNReal.ofReal ζ) P := by
    simpa [childAvg, Qm, p_e, q_e, ζ, hdepth] using
      memLp_zeta_descendantsAverage_responseJObservableCubeSet_originCube_from_P4_of_stationary
        hP hstat hStruct hP4 hk_nonneg hkm_int p_e q_e
  have hminS_mem :
      MeasureTheory.MemLp (fun a => min (S a) 1) (ENNReal.ofReal ξr) P :=
    memLp_min_one_of_aestronglyMeasurable hS_asm hS_nonneg _
  have hminT_mem :
      MeasureTheory.MemLp (fun a => min (T a) 1) (ENNReal.ofReal ξr) P :=
    memLp_min_one_of_aestronglyMeasurable hT_asm hT_nonneg _
  have hminSrc_mem :
      MeasureTheory.MemLp (fun a => min (sourceMax a) 1)
        (ENNReal.ofReal ξr) P :=
    memLp_min_one_of_aestronglyMeasurable hsrc_asm hsrc_nonneg _
  have hHolderXiZeta : ξr.HolderConjugate ζ :=
    holderConjugate_xi_section53CoarseFluctuationZeta hP4
  letI : ENNReal.HolderTriple (ENNReal.ofReal ξr) (ENNReal.ofReal ζ) 1 := by
    simpa using Real.HolderTriple.ennrealOfReal hHolderXiZeta
  have hChildInt : MeasureTheory.Integrable childAvg P :=
    hChildMem.integrable (ENNReal.one_le_ofReal.mpr hζ_one)
  have hIS :
      MeasureTheory.Integrable
        (fun a => min (S a) 1 * childAvg a) P := by
    simpa using hminS_mem.integrable_mul hChildMem
  have hIT :
      MeasureTheory.Integrable
        (fun a => min (T a) 1 * childAvg a) P := by
    simpa using hminT_mem.integrable_mul hChildMem
  have hID :
      MeasureTheory.Integrable
        (fun a => min D 1 * childAvg a) P :=
    hChildInt.const_mul (min D 1)
  have hILHS :
      MeasureTheory.Integrable
        (fun a => min (sourceMax a) 1 * childAvg a) P := by
    simpa using hminSrc_mem.integrable_mul hChildMem
  have hIST :
      MeasureTheory.Integrable
        (fun a => min (S a) 1 * childAvg a + min (T a) 1 * childAvg a) P := by
    simpa using hIS.add hIT
  -- pointwise envelope split
  have hsplit : ∀ a,
      min (sourceMax a) 1 ≤ min (S a) 1 + min (T a) 1 + min D 1 := by
    intro a
    have hstart :
        sourceMax a ≤
          terminalSpectralPositivePartSourceMax hP hStruct hc N m Qm
            (fun x : Homogenization.CoeffField d => x) a := by
      simpa [sourceMax, Qm] using
        terminalSpectralPositivePartSourceMax_le_of_start_le
          hP hStruct hc (le_refl N) Qm (fun x : Homogenization.CoeffField d => x) a
    have henv :
        terminalSpectralPositivePartSourceMax hP hStruct hc N m Qm
            (fun x : Homogenization.CoeffField d => x) a ≤
          S a + T a + D := by
      simpa [terminalBadMaximalSplitEnvelope, S, T, D, Qm] using
        terminalSpectralPositivePartSourceMax_le_terminalBadMaximalSplitEnvelope
          hP hStruct hc (hNk.trans hkm.le) Qm
          (fun x : Homogenization.CoeffField d => x) M_sub a
    have h1 : min (sourceMax a) 1 ≤ min (S a + T a + D) 1 :=
      min_le_min (hstart.trans henv) le_rfl
    have h2 : min (S a + T a + D) 1 ≤ min (S a + T a) 1 + min D 1 :=
      min_add_one_le_add_min_one
        (add_nonneg (hS_nonneg a) (hT_nonneg a)) hD_nonneg
    have h3 : min (S a + T a) 1 ≤ min (S a) 1 + min (T a) 1 :=
      min_add_one_le_add_min_one (hS_nonneg a) (hT_nonneg a)
    linarith
  have hpt :
      (fun a => min (sourceMax a) 1 * childAvg a) ≤
        fun a =>
          (min (S a) 1 * childAvg a + min (T a) 1 * childAvg a) +
            min D 1 * childAvg a := by
    intro a
    have := mul_le_mul_of_nonneg_right (hsplit a) (hchild_nonneg a)
    calc
      min (sourceMax a) 1 * childAvg a
          ≤ (min (S a) 1 + min (T a) 1 + min D 1) * childAvg a := this
      _ = (min (S a) 1 * childAvg a + min (T a) 1 * childAvg a) +
            min D 1 * childAvg a := by ring
  -- the three pieces
  have hzetaRoot_le :
      (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) ≤ responseMoment := by
    simpa [childAvg, Qm, ζ, p_e, q_e, responseMoment] using
      childResponseAverage_zetaRoot_le_responseMoment_of_stationary
        hP hstat hStruct hP4 hkm e
  have hzetaRoot_nonneg :
      0 ≤ (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) :=
    Real.rpow_nonneg
      (MeasureTheory.integral_nonneg fun a =>
        Real.rpow_nonneg (hchild_nonneg a) _) _
  have hresponse_nonneg : 0 ≤ responseMoment := by
    simpa [responseMoment] using
      coarseFluctuationResponseMomentAtScale_nonneg hP hStruct hP4 k m e
  have hsumRoot_nonneg : 0 ≤ sumRoot :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  -- stochastic piece
  have hS_pow_le : ∫ a, min (S a) 1 ^ ξr ∂P ≤ lintSum.toReal :=
    integral_min_one_rpow_le_lintegral_enorm_sq_toReal hS_asm hS_nonneg
      hxi_two le_self_add hfin
  have hS_root_le :
      (∫ a, min (S a) 1 ^ ξr ∂P) ^ (1 / ξr) ≤ sumRoot :=
    Real.rpow_le_rpow
      (MeasureTheory.integral_nonneg fun a =>
        Real.rpow_nonneg (le_min (hS_nonneg a) zero_le_one) _)
      hS_pow_le (one_div_nonneg.mpr hxi_pos.le)
  have hS_holder :
      ∫ a, min (S a) 1 * childAvg a ∂P ≤
        (∫ a, min (S a) 1 ^ ξr ∂P) ^ (1 / ξr) *
          (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) :=
    MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hHolderXiZeta
      (Filter.Eventually.of_forall fun a => le_min (hS_nonneg a) zero_le_one)
      (Filter.Eventually.of_forall hchild_nonneg) hminS_mem hChildMem
  have hS_piece :
      ∫ a, min (S a) 1 * childAvg a ∂P ≤ sumRoot * responseMoment :=
    hS_holder.trans
      (mul_le_mul hS_root_le hzetaRoot_le hzetaRoot_nonneg hsumRoot_nonneg)
  -- subthreshold piece
  have hT_lint :
      (∫⁻ ω, ‖T ω‖ₑ ^ (2 : ℝ) ∂P) ≤ lintSum := by
    have heq :
        (∫⁻ ω, ‖T ω‖ₑ ^ (2 : ℝ) ∂P) =
          ∫⁻ ω, ‖M_sub m ω‖ₑ ^ (2 : ℝ) ∂P := by
      refine MeasureTheory.lintegral_congr fun ω => ?_
      congr 1
      simp [T, Real.enorm_eq_ofReal_abs, abs_abs]
    rw [heq]
    exact le_add_self
  have hT_pow_le : ∫ a, min (T a) 1 ^ ξr ∂P ≤ lintSum.toReal :=
    integral_min_one_rpow_le_lintegral_enorm_sq_toReal hT_asm hT_nonneg
      hxi_two hT_lint hfin
  have hT_root_le :
      (∫ a, min (T a) 1 ^ ξr ∂P) ^ (1 / ξr) ≤ sumRoot :=
    Real.rpow_le_rpow
      (MeasureTheory.integral_nonneg fun a =>
        Real.rpow_nonneg (le_min (hT_nonneg a) zero_le_one) _)
      hT_pow_le (one_div_nonneg.mpr hxi_pos.le)
  have hT_holder :
      ∫ a, min (T a) 1 * childAvg a ∂P ≤
        (∫ a, min (T a) 1 ^ ξr ∂P) ^ (1 / ξr) *
          (∫ a, childAvg a ^ ζ ∂P) ^ (1 / ζ) :=
    MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hHolderXiZeta
      (Filter.Eventually.of_forall fun a => le_min (hT_nonneg a) zero_le_one)
      (Filter.Eventually.of_forall hchild_nonneg) hminT_mem hChildMem
  have hT_piece :
      ∫ a, min (T a) 1 * childAvg a ∂P ≤ sumRoot * responseMoment :=
    hT_holder.trans
      (mul_le_mul hT_root_le hzetaRoot_le hzetaRoot_nonneg hsumRoot_nonneg)
  -- drift piece
  have hchild_int_le : ∫ a, childAvg a ∂P ≤ responseMoment := by
    have hOneMem :
        MeasureTheory.MemLp (fun _ : Homogenization.CoeffField d => (1 : ℝ))
          (ENNReal.ofReal ξr) P :=
      MeasureTheory.memLp_const 1
    have hH1 :=
      MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hHolderXiZeta.symm
        (Filter.Eventually.of_forall hchild_nonneg)
        (Filter.Eventually.of_forall fun _ => zero_le_one) hChildMem hOneMem
    have hone_pow :
        (∫ _a, (1 : ℝ) ^ ξr ∂P) ^ (1 / ξr) = 1 := by
      simp [Real.one_rpow]
    rw [hone_pow, mul_one] at hH1
    simpa [mul_one] using hH1.trans hzetaRoot_le
  have hminD_nonneg : 0 ≤ min D 1 := le_min hD_nonneg zero_le_one
  have hD_piece :
      ∫ a, min D 1 * childAvg a ∂P ≤ min D 1 * responseMoment := by
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hchild_int_le hminD_nonneg
  -- assembly
  have hstochRoot' : 2 * sumRoot ≤ stochRoot := by
    simpa [sumRoot, lintSum, S, Qm] using hstochRoot
  calc
    ∫ a, min (sourceMax a) 1 * childAvg a ∂P
        ≤ ∫ a,
            (min (S a) 1 * childAvg a + min (T a) 1 * childAvg a) +
              min D 1 * childAvg a ∂P :=
          MeasureTheory.integral_mono hILHS (hIST.add hID) hpt
    _ = (∫ a, min (S a) 1 * childAvg a ∂P +
          ∫ a, min (T a) 1 * childAvg a ∂P) +
          ∫ a, min D 1 * childAvg a ∂P := by
        rw [MeasureTheory.integral_add hIST hID,
          MeasureTheory.integral_add hIS hIT]
    _ ≤ (sumRoot * responseMoment + sumRoot * responseMoment) +
          min D 1 * responseMoment :=
        add_le_add (add_le_add hS_piece hT_piece) hD_piece
    _ = (2 * sumRoot + min D 1) * responseMoment := by ring
    _ ≤ (stochRoot + min D 1) * responseMoment :=
        mul_le_mul_of_nonneg_right
          (add_le_add hstochRoot' le_rfl) hresponse_nonneg


/--
Mixed-scale variant of the L-C integrability companion: the capped source
maximum over the start window `[N, m]` pairs integrably against the child
response average at the current window `(k, m)`.
-/
theorem integrable_min_terminalSourceMax_start_one_mul_childResponseAverage_special
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hstat : Homogenization.Book.Ch04.StationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {N k m : ℕ}
    (_hNk : N ≤ k) (hkm : k < m) (e : Homogenization.Vec d) :
    let Qm : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let childAvg := fun a : Homogenization.CoeffField d =>
      Homogenization.descendantsAverage Qm (m - k)
        (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
    let sourceMax :=
      terminalSpectralPositivePartSourceMax hP hStruct hc N m Qm
        (fun x : Homogenization.CoeffField d => x)
    MeasureTheory.Integrable
      (fun a : Homogenization.CoeffField d =>
        min (sourceMax a) 1 * childAvg a) P := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  dsimp only
  let ζ := section53CoarseFluctuationZeta hP4
  let ξr : ℝ := (hP4.xi : ℝ)
  let Qm : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let childAvg : Homogenization.CoeffField d → ℝ := fun a =>
    Homogenization.descendantsAverage Qm (m - k)
      (fun R => Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a)
  let sourceMax : Homogenization.CoeffField d → ℝ :=
    terminalSpectralPositivePartSourceMax hP hStruct hc N m Qm
      (fun x : Homogenization.CoeffField d => x)
  have hζ_one : 1 ≤ ζ := (one_lt_section53CoarseFluctuationZeta hP4).le
  have hsrc_nonneg : ∀ a, 0 ≤ sourceMax a :=
    terminalSpectralPositivePartSourceMax_nonneg hP hStruct hc N m Qm
      (fun x : Homogenization.CoeffField d => x)
  have hsrc_asm : MeasureTheory.AEStronglyMeasurable sourceMax P := by
    simpa [sourceMax, Qm] using
      aestronglyMeasurable_terminalSpectralPositivePartSourceMax_origin
        hP hStruct hc N m
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by
    exact_mod_cast Nat.zero_le k
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by
    exact_mod_cast hkm.le
  have hdepth : Int.toNat ((m : ℤ) - (k : ℤ)) = m - k := by
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hkm_int)]
    exact (Nat.cast_sub hkm.le).symm
  have hChildMem :
      MeasureTheory.MemLp childAvg (ENNReal.ofReal ζ) P := by
    simpa [childAvg, Qm, p_e, q_e, ζ, hdepth] using
      memLp_zeta_descendantsAverage_responseJObservableCubeSet_originCube_from_P4_of_stationary
        hP hstat hStruct hP4 hk_nonneg hkm_int p_e q_e
  have hminSrc_mem :
      MeasureTheory.MemLp (fun a => min (sourceMax a) 1)
        (ENNReal.ofReal ξr) P :=
    memLp_min_one_of_aestronglyMeasurable hsrc_asm hsrc_nonneg _
  have hHolderXiZeta : ξr.HolderConjugate ζ :=
    holderConjugate_xi_section53CoarseFluctuationZeta hP4
  letI : ENNReal.HolderTriple (ENNReal.ofReal ξr) (ENNReal.ofReal ζ) 1 := by
    simpa using Real.HolderTriple.ennrealOfReal hHolderXiZeta
  have hmain := hminSrc_mem.integrable_mul hChildMem
  simpa [childAvg, sourceMax, Qm, p_e, q_e, Pi.mul_apply] using hmain

end

end Homogenization.HighContrast.EntryScale
