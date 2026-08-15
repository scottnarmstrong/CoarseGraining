import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Homogenization.HighContrast.EntryScale.Lyapunov
import Homogenization.HighContrast.EntryScale.EntryScale.P1

namespace Homogenization.HighContrast.EntryScale

/--
Source label `e.Nentry`: faithful source-facing logarithmic bound for the
entry scale `N_entry = m_I = N_* + I L`, using the displayed choices of
`N`, `N_*`, and `I`.
-/
theorem exists_entryScaleConstant_memoryGridScale_le_logb_of_choices
    {p_hm B C_A delta_sc lambda : ℝ} {L : ℕ}
    (hp_hm_nonneg : 0 ≤ p_hm)
    (hB_one : 1 ≤ B)
    (hC_A_pos : 0 < C_A)
    (hdelta_sc_pos : 0 < delta_sc)
    (hlambda_pos : 0 < lambda)
    (hlambda_lt_one : lambda < 1) :
    ∃ Centry : ℝ, 0 ≤ Centry ∧
      ∀ {T : ℝ} {N Nstar I : ℕ}, 1 ≤ T →
        N = Nat.ceil (p_hm * Real.logb 3 (2 + T)) →
        Nstar = N + Nat.ceil (B * Real.logb 3 (2 + T)) →
        I =
          Nat.ceil
            (Real.log (C_A * (2 + T) / delta_sc) / |Real.log lambda|) →
        (memoryGridScale Nstar L I : ℝ) ≤
          Centry * Real.logb 3 (2 + T) := by
  let c0 : ℝ := max 0 (Real.log (C_A / delta_sc) / Real.log 3)
  let D : ℝ := |Real.log lambda|
  let CI : ℝ := ((c0 + 1) * Real.log 3) / D + 1
  let CN : ℝ := p_hm + 1
  let Centry : ℝ := CN + B + 1 + (L : ℝ) * CI + 1
  have hlog_lambda_neg : Real.log lambda < 0 :=
    Real.log_neg hlambda_pos hlambda_lt_one
  have hD_pos : 0 < D := by
    dsimp [D]
    exact abs_pos.mpr (ne_of_lt hlog_lambda_neg)
  have hlog3_pos : 0 < Real.log 3 :=
    Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hc0_nonneg : 0 ≤ c0 := by
    dsimp [c0]
    exact le_max_left 0 (Real.log (C_A / delta_sc) / Real.log 3)
  have hCI_nonneg : 0 ≤ CI := by
    dsimp [CI, D, c0]
    have hnum_nonneg :
        0 ≤
          (max 0 (Real.log (C_A / delta_sc) / Real.log 3) + 1) *
            Real.log 3 :=
      mul_nonneg (by nlinarith) (le_of_lt hlog3_pos)
    have hdiv_nonneg :
        0 ≤
          ((max 0 (Real.log (C_A / delta_sc) / Real.log 3) + 1) *
              Real.log 3) /
            |Real.log lambda| :=
      div_nonneg hnum_nonneg (le_of_lt hD_pos)
    linarith
  have hCentry_nonneg : 0 ≤ Centry := by
    dsimp [Centry, CN]
    have hL_nonneg : 0 ≤ (L : ℝ) := by positivity
    nlinarith
  refine ⟨Centry, hCentry_nonneg, ?_⟩
  intro T N Nstar I hT hN_eq hNstar_eq hI_eq
  let Llog : ℝ := Real.logb 3 (2 + T)
  have hLlog_ge_one : 1 ≤ Llog := by
    dsimp [Llog]
    exact one_le_logb_three_two_add hT
  have hLlog_nonneg : 0 ≤ Llog := by linarith
  have hpL_nonneg : 0 ≤ p_hm * Llog :=
    mul_nonneg hp_hm_nonneg hLlog_nonneg
  have hN_log : (N : ℝ) ≤ CN * Llog := by
    have hceil_upper :
        (Nat.ceil (p_hm * Llog) : ℝ) ≤ p_hm * Llog + 1 :=
      le_of_lt (Nat.ceil_lt_add_one hpL_nonneg)
    calc
      (N : ℝ) = (Nat.ceil (p_hm * Llog) : ℝ) := by
          rw [hN_eq]
      _ ≤ p_hm * Llog + 1 := hceil_upper
      _ ≤ CN * Llog := by
          dsimp [CN]
          nlinarith
  have hB_nonneg : 0 ≤ B := by linarith
  have hNstar_le :
      Nstar ≤ N + Nat.ceil (B * Real.logb 3 (2 + T)) := by
    rw [hNstar_eq]
  have hI_log : (I : ℝ) ≤ CI * Llog := by
    dsimp [CI, c0, D, Llog]
    exact
      iteration_count_le_log_of_choices hT hC_A_pos hdelta_sc_pos
        hlambda_pos hlambda_lt_one hI_eq
  have hgrid :=
    memoryGridScale_le_log_of_base_buffer_iterations
      (N := N) (Nstar := Nstar) (I := I) (L := L)
      (CN := CN) (B := B) (CI := CI) (T := T)
      hT hB_nonneg (by simpa [Llog] using hN_log) hNstar_le
      (by simpa [Llog] using hI_log)
  simpa [Centry, Llog] using hgrid

/--
Source label `e.Nentry`: source-facing entry-scale theorem.  The hypotheses
include the actual displayed choices of `N`, `N_*`, and `I`; the conclusions
are exactly the two estimates in `e.Nentry`.
-/
theorem exists_entryScaleConstant_theta_entry_and_memoryGridScale_le_logb_of_choices
    {d : ℕ} [NeZero d] (hc : HighContrastExponents d) {p_hm B C_A delta_sc lambda : ℝ} {L : ℕ}
    (hp_hm_nonneg : 0 ≤ p_hm)
    (hB_one : 1 ≤ B)
    (hC_A_pos : 0 < C_A)
    (hdelta_sc_pos : 0 < delta_sc)
    (hlambda_pos : 0 < lambda)
    (hlambda_lt_one : lambda < 1) :
    ∃ Centry : ℝ, 0 ≤ Centry ∧
      ∀ {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
        (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
        (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
        (_hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
        {T : ℝ} {N Nstar I : ℕ} {A : ℝ},
          1 ≤ T →
          N = Nat.ceil (p_hm * Real.logb 3 (2 + T)) →
          Nstar = N + Nat.ceil (B * Real.logb 3 (2 + T)) →
          I =
            Nat.ceil
              (Real.log (C_A * (2 + T) / delta_sc) / |Real.log lambda|) →
          0 ≤ A →
          lyapunovValue A
              (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L 0))
              (memory (memoryDecay hc L)
                (initialMemory hc.rhoM N Nstar
                  (fun n => contrastExcessAtScale hP hStruct n))
                (memoryGridDrop
                  (fun n => contrastExcessAtScale hP hStruct n) Nstar L) 0) ≤
            C_A * T →
          (∀ i < I,
            delta_sc <
              contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i + 1)) →
            lyapunovValue A
                (contrastExcessAtScale hP hStruct
                  (memoryGridScale Nstar L (i + 1)))
                (memory (memoryDecay hc L)
                  (initialMemory hc.rhoM N Nstar
                    (fun n => contrastExcessAtScale hP hStruct n))
                  (memoryGridDrop
                    (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
                  (i + 1)) ≤
              lambda *
                lyapunovValue A
                  (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
                  (memory (memoryDecay hc L)
                    (initialMemory hc.rhoM N Nstar
                      (fun n => contrastExcessAtScale hP hStruct n))
                    (memoryGridDrop
                      (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
                    i)) →
            Homogenization.Book.Ch05.thetaAtScale hP hStruct
                (memoryGridScale Nstar L I : ℤ) ≤ 1 + delta_sc ∧
              (memoryGridScale Nstar L I : ℝ) ≤
                Centry * Real.logb 3 (2 + T) := by
  obtain ⟨Centry, hCentry_nonneg, hCentry_log⟩ :=
    exists_entryScaleConstant_memoryGridScale_le_logb_of_choices
      (p_hm := p_hm) (B := B) (C_A := C_A) (delta_sc := delta_sc)
      (lambda := lambda) (L := L)
      hp_hm_nonneg hB_one hC_A_pos hdelta_sc_pos hlambda_pos hlambda_lt_one
  refine ⟨Centry, hCentry_nonneg, ?_⟩
  intro P hP hStruct _hP4 T N Nstar I A hT hN_eq hNstar_eq hI_eq
    hA_nonneg hY0 hstep_if_above
  have hpow :
      lambda ^ I * (C_A * T) ≤ delta_sc :=
    contraction_power_mul_le_delta_of_iteration_choice
      hT hC_A_pos hdelta_sc_pos hlambda_pos hlambda_lt_one hI_eq
  have htheta :
      Homogenization.Book.Ch05.thetaAtScale hP hStruct
          (memoryGridScale Nstar L I : ℤ) ≤ 1 + delta_sc :=
    thetaAt_memoryGridScale_entry_le_one_add_of_contraction
      (hc := hc) hP hStruct _hP4
      (N := N) (Nstar := Nstar) (L := L) (I := I)
      (A := A) (lambda := lambda) (delta := delta_sc) (Y0Bound := C_A * T)
      hA_nonneg (le_of_lt hlambda_pos) hY0 hpow hstep_if_above
  have hlog :
      (memoryGridScale Nstar L I : ℝ) ≤
        Centry * Real.logb 3 (2 + T) :=
    hCentry_log hT hN_eq hNstar_eq hI_eq
  exact ⟨htheta, hlog⟩

/--
Source label `e.Nentry`: entry-scale theorem specialized to the corrected
initial budget `T = widetildeTheta_0`.  The initial `Y_0 <= C_A T` hypothesis
is discharged here; downstream only has to provide the per-step Lyapunov
contraction.
-/
theorem exists_entryScaleConstant_theta_entry_and_memoryGridScale_le_logb_of_choices_initial
    {d : ℕ} [NeZero d] (hc : HighContrastExponents d) {p_hm B C_A delta_sc lambda : ℝ} {L : ℕ}
    (hp_hm_nonneg : 0 ≤ p_hm)
    (hB_one : 1 ≤ B)
    (hC_A_pos : 0 < C_A)
    (hdelta_sc_pos : 0 < delta_sc)
    (hlambda_pos : 0 < lambda)
    (hlambda_lt_one : lambda < 1) :
    ∃ Centry : ℝ, 0 ≤ Centry ∧
      ∀ {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
        (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
        (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
        {N Nstar I : ℕ} {A : ℝ},
          N =
            Nat.ceil
              (p_hm * Real.logb 3
                (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) →
          Nstar =
            N + Nat.ceil
              (B * Real.logb 3
                (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) →
          I =
            Nat.ceil
              (Real.log
                  (C_A *
                    (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) /
                    delta_sc) /
                |Real.log lambda|) →
          N ≤ Nstar →
          0 ≤ A →
          1 + A ≤ C_A →
          (∀ i < I,
            delta_sc <
              contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i + 1)) →
            lyapunovValue A
                (contrastExcessAtScale hP hStruct
                  (memoryGridScale Nstar L (i + 1)))
                (memory (memoryDecay hc L)
                  (initialMemory hc.rhoM N Nstar
                    (fun n => contrastExcessAtScale hP hStruct n))
                  (memoryGridDrop
                    (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
                  (i + 1)) ≤
              lambda *
                lyapunovValue A
                  (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
                  (memory (memoryDecay hc L)
                    (initialMemory hc.rhoM N Nstar
                      (fun n => contrastExcessAtScale hP hStruct n))
                    (memoryGridDrop
                      (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
                    i)) →
            Homogenization.Book.Ch05.thetaAtScale hP hStruct
                (memoryGridScale Nstar L I : ℤ) ≤ 1 + delta_sc ∧
              (memoryGridScale Nstar L I : ℝ) ≤
                Centry * Real.logb 3
                  (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) := by
  obtain ⟨Centry, hCentry_nonneg, hentry⟩ :=
    exists_entryScaleConstant_theta_entry_and_memoryGridScale_le_logb_of_choices
      (hc := hc) (d := d) (p_hm := p_hm) (B := B) (C_A := C_A)
      (delta_sc := delta_sc) (lambda := lambda) (L := L)
      hp_hm_nonneg hB_one hC_A_pos hdelta_sc_pos hlambda_pos hlambda_lt_one
  refine ⟨Centry, hCentry_nonneg, ?_⟩
  intro P hP hStruct hP4 N Nstar I A hN_eq hNstar_eq hI_eq hNNstar
    hA_nonneg hC_A hstep_if_above
  let T : ℝ := Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4
  have hT_one : 1 ≤ T := by
    dsimp [T]
    exact one_le_initialWidetildeTheta_of_P4 hP hStruct hP4
  have hY0 :
      lyapunovValue A
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L 0))
          (memory (memoryDecay hc L)
            (initialMemory hc.rhoM N Nstar
              (fun n => contrastExcessAtScale hP hStruct n))
            (memoryGridDrop
              (fun n => contrastExcessAtScale hP hStruct n) Nstar L) 0) ≤
        C_A * T := by
    dsimp [T]
    exact
      initial_lyapunovValue_le_const_mul_initialWidetildeTheta_of_P4
        hc hP hStruct hP4 hNNstar hA_nonneg hC_A
  have hN_eq_T : N = Nat.ceil (p_hm * Real.logb 3 (2 + T)) := by
    simpa [T] using hN_eq
  have hNstar_eq_T : Nstar = N + Nat.ceil (B * Real.logb 3 (2 + T)) := by
    simpa [T] using hNstar_eq
  have hI_eq_T :
      I =
        Nat.ceil
          (Real.log (C_A * (2 + T) / delta_sc) / |Real.log lambda|) := by
    simpa [T] using hI_eq
  have hresult :=
    hentry hP hStruct hP4 hT_one hN_eq_T hNstar_eq_T hI_eq_T hA_nonneg
      hY0 hstep_if_above
  simpa [T] using hresult

/--
Source labels `e.Nentry`, `e.localization`, `e.final.decay`, and
`e.final.scale`: conditional final assembly from an entry scale with a
logarithmic bound.  The constants `C` and `alpha` are chosen before the law
`P`, matching the manuscript's uniformity claim.
-/
theorem exists_uniform_final_scale_decay_and_physical_scale_of_entry
    {d : ℕ} [NeZero d] (hc : HighContrastExponents d) (loc : LocalizationSmallContrastInput hc)
    {delta_sc Centry : ℝ}
    (hdelta_sc : delta_sc ≤ loc.delta0 / 2)
    (hCentry_nonneg : 0 ≤ Centry) :
    ∃ C alpha : ℝ, 0 < C ∧ 0 < alpha ∧
      ∀ {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
        (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
        (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P),
        hP4.params = hc.params →
        ∀ {Nentry : ℕ},
          Homogenization.Book.Ch05.thetaAtScale hP hStruct (Nentry : ℤ) ≤
              1 + delta_sc →
          (Nentry : ℝ) ≤
              Centry * Real.logb 3
                (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) →
            ∃ N0 : ℕ,
              (∀ n : ℕ,
                Homogenization.Book.Ch05.thetaAtScale hP hStruct
                    ((N0 + n : ℕ) : ℤ) ≤
                  1 + (3 : ℝ) ^ (-(alpha * (n : ℝ)))) ∧
              (N0 : ℝ) ≤
                C * Real.logb 3
                  (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ∧
              (3 : ℝ) ^ N0 ≤
                Real.rpow
                  (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) C := by
  have heta_pos : 0 < loc.delta0 / 2 := by linarith [loc.delta0_pos]
  obtain ⟨B, hB_one, hB⟩ :=
    exists_localizationShift_le_log_and_error
      loc.C_loc_nonneg loc.beta_loc_pos heta_pos
  obtain ⟨Rsc, hRsc⟩ :=
    exists_smallContrast_prefactor_shift loc.C_sc_pos loc.alpha0_pos
  let C : ℝ := Centry + 2 * B + (Rsc : ℝ) + 1
  let alpha : ℝ := loc.alpha0
  have hB_nonneg : 0 ≤ B := by linarith
  have hC_pos : 0 < C := by
    have hRsc_nonneg : 0 ≤ (Rsc : ℝ) := by positivity
    dsimp [C]
    nlinarith
  refine ⟨C, alpha, hC_pos, by simpa [alpha] using loc.alpha0_pos, ?_⟩
  intro P hP hStruct hP4 hcparams Nentry hentry hNentry_log
  let T : ℝ := Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4
  have hT_one : 1 ≤ T := by
    dsimp [T]
    exact one_le_initialWidetildeTheta_of_P4 hP hStruct hP4
  obtain ⟨R, hR_error, hR_log⟩ := hB (T := T) hT_one
  have hR_error_initial :
      loc.C_loc * (3 : ℝ) ^ (-(loc.beta_loc * (R : ℝ))) *
          Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 ≤
        loc.delta0 / 2 := by
    simpa [T] using hR_error
  let N0 : ℕ := (Nentry + R) + Rsc
  have hdecay :
      ∀ n : ℕ,
        Homogenization.Book.Ch05.thetaAtScale hP hStruct ((N0 + n : ℕ) : ℤ) ≤
          1 + (3 : ℝ) ^ (-(alpha * (n : ℝ))) := by
    intro n
    have h :=
      thetaAtScale_le_one_add_final_decay_of_entry_localization_shift
        (hc := hc) loc hP hStruct hP4 hcparams hentry hdelta_sc
        hR_error_initial hRsc n
    simpa [N0, alpha] using h
  have hNentry_log_T :
      (Nentry : ℝ) ≤ Centry * Real.logb 3 (2 + T) := by
    simpa [T] using hNentry_log
  have hN0_log_T :
      (N0 : ℝ) ≤ C * Real.logb 3 (2 + T) := by
    have hcomponent :=
      final_index_le_log_of_components
        (Nentry := Nentry) (R := R) (Rsc := Rsc)
        (Centry := Centry) (CR := 2 * B) (T := T)
        hT_one hNentry_log_T hR_log
    simpa [N0, C] using hcomponent
  have hN0_log :
      (N0 : ℝ) ≤
        C * Real.logb 3
          (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) := by
    simpa [T] using hN0_log_T
  have hphys_T :
      (3 : ℝ) ^ N0 ≤ Real.rpow (2 + T) C := by
    exact physical_scale_le_of_logb_bound
      (N := N0) (C := C) (T := T) (by linarith [hT_one]) hN0_log_T
  have hphys :
      (3 : ℝ) ^ N0 ≤
        Real.rpow
          (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) C := by
    simpa [T] using hphys_T
  exact ⟨N0, hdecay, hN0_log, hphys⟩

end Homogenization.HighContrast.EntryScale
