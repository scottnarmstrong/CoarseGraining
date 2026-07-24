import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Homogenization.HighContrast.EntryScale.Lyapunov.P1


/-!
# Entry scale and small-contrast handoff

The logarithmic entry-scale construction and the handoff to
the localization and small-contrast theorem.
-/


namespace Homogenization.HighContrast.EntryScale

/--
Source label `e.Nentry`: iterating a one-step contraction gives
`Y_n ≤ λ^n Y_0`.
-/
theorem iterated_contraction_le_pow {n : ℕ} {Y : ℕ → ℝ} {lambda : ℝ}
    (hlambda_nonneg : 0 ≤ lambda)
    (hstep : ∀ i < n, Y (i + 1) ≤ lambda * Y i) :
    Y n ≤ lambda ^ n * Y 0 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hprev : ∀ i < n, Y (i + 1) ≤ lambda * Y i := by
        intro i hi
        exact hstep i (Nat.lt_trans hi (Nat.lt_succ_self n))
      have hYn : Y n ≤ lambda ^ n * Y 0 := ih hprev
      have hlast : Y (n + 1) ≤ lambda * Y n := hstep n (Nat.lt_succ_self n)
      calc
        Y (n + 1) ≤ lambda * Y n := hlast
        _ ≤ lambda * (lambda ^ n * Y 0) :=
            mul_le_mul_of_nonneg_left hYn hlambda_nonneg
        _ = lambda ^ (n + 1) * Y 0 := by ring

/--
Source label `e.Nentry`: if contraction would force `Y_I ≤ δ`, then some
scale up to `I` has entered the small-contrast regime.
-/
theorem exists_entry_of_contraction {F Y : ℕ → ℝ} {lambda delta Y0Bound : ℝ}
    {I : ℕ}
    (hlambda_nonneg : 0 ≤ lambda)
    (hY0 : Y 0 ≤ Y0Bound)
    (hpow : lambda ^ I * Y0Bound ≤ delta)
    (hF_le_Y : ∀ i, F i ≤ Y i)
    (hstep_if_above :
      ∀ i < I, delta < F (i + 1) → Y (i + 1) ≤ lambda * Y i) :
    ∃ i, i ≤ I ∧ F i ≤ delta := by
  by_contra hnone
  push_neg at hnone
  have hstep : ∀ i < I, Y (i + 1) ≤ lambda * Y i := by
    intro i hi
    exact hstep_if_above i hi (hnone (i + 1) (Nat.succ_le_of_lt hi))
  have hYI : Y I ≤ lambda ^ I * Y 0 :=
    iterated_contraction_le_pow hlambda_nonneg hstep
  have hpowY0 : lambda ^ I * Y 0 ≤ lambda ^ I * Y0Bound := by
    have hpow_nonneg : 0 ≤ lambda ^ I := pow_nonneg hlambda_nonneg I
    exact mul_le_mul_of_nonneg_left hY0 hpow_nonneg
  have hFI_le_delta : F I ≤ delta :=
    le_trans (hF_le_Y I) (le_trans hYI (le_trans hpowY0 hpow))
  exact not_lt_of_ge hFI_le_delta (hnone I (le_refl I))

/--
Source label `e.Nentry`: if the contrast sequence is monotone decreasing, the
entry index found by the contraction argument can be pushed to the endpoint
`I`.
-/
theorem endpoint_entry_of_contraction {F Y : ℕ → ℝ} {lambda delta Y0Bound : ℝ}
    {I : ℕ}
    (hF_antitone : Antitone F)
    (hlambda_nonneg : 0 ≤ lambda)
    (hY0 : Y 0 ≤ Y0Bound)
    (hpow : lambda ^ I * Y0Bound ≤ delta)
    (hF_le_Y : ∀ i, F i ≤ Y i)
    (hstep_if_above :
      ∀ i < I, delta < F (i + 1) → Y (i + 1) ≤ lambda * Y i) :
    F I ≤ delta := by
  obtain ⟨i, hiI, hFi⟩ :=
    exists_entry_of_contraction hlambda_nonneg hY0 hpow hF_le_Y
      hstep_if_above
  exact (hF_antitone hiI).trans hFi

/--
Source labels `l.lyapunov` and `e.Nentry`: convert a one-based Lyapunov step
statement, natural for the memory-grid theorem, into the zero-based
`i < I -> i+1` contraction used by the entry-scale iteration.
-/
theorem lyapunov_step_if_above_of_one_based_step
    {F H : ℕ → ℝ} {A lambda delta_sc : ℝ} {I : ℕ}
    (hstep :
      ∀ j, 1 ≤ j →
        delta_sc ≤ F j →
        lyapunovValue A (F j) (H j) ≤
          lambda * lyapunovValue A (F (j - 1)) (H (j - 1))) :
    ∀ i < I, delta_sc < F (i + 1) →
      lyapunovValue A (F (i + 1)) (H (i + 1)) ≤
        lambda * lyapunovValue A (F i) (H i) := by
  intro i _hi hdelta_lt
  have hj : 1 ≤ i + 1 := Nat.succ_le_succ (Nat.zero_le i)
  have hdelta_le : delta_sc ≤ F (i + 1) := le_of_lt hdelta_lt
  have h := hstep (i + 1) hj hdelta_le
  have hpred : i + 1 - 1 = i := Nat.succ_sub_one i
  simpa [hpred] using h

/--
Source label `e.Nentry`: concrete memory-grid entry conclusion for the
contrast excess.  The contraction step is supplied only in the iteration
regime `delta < F_{i+1}`, matching the antecedent
`F_i > delta_sc` in `l.lyapunov`.
-/
theorem contrastExcessAt_memoryGridScale_entry_le_of_contraction
    {d : ℕ} [NeZero d] (hc : HighContrastExponents d) {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {N Nstar L I : ℕ} {A lambda delta Y0Bound : ℝ}
    (hA_nonneg : 0 ≤ A)
    (hlambda_nonneg : 0 ≤ lambda)
    (hY0 :
      lyapunovValue A
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L 0))
          (memory (memoryDecay hc L)
            (initialMemory hc.rhoM N Nstar
              (fun n => contrastExcessAtScale hP hStruct n))
            (memoryGridDrop
              (fun n => contrastExcessAtScale hP hStruct n) Nstar L) 0) ≤
        Y0Bound)
    (hpow : lambda ^ I * Y0Bound ≤ delta)
    (hstep_if_above :
      ∀ i < I,
        delta <
          contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i + 1)) →
        lyapunovValue A
            (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i + 1)))
            (memory (memoryDecay hc L)
              (initialMemory hc.rhoM N Nstar
                (fun n => contrastExcessAtScale hP hStruct n))
              (memoryGridDrop
                (fun n => contrastExcessAtScale hP hStruct n) Nstar L) (i + 1)) ≤
          lambda *
            lyapunovValue A
              (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
              (memory (memoryDecay hc L)
                (initialMemory hc.rhoM N Nstar
                  (fun n => contrastExcessAtScale hP hStruct n))
                (memoryGridDrop
                  (fun n => contrastExcessAtScale hP hStruct n) Nstar L) i)) :
    contrastExcessAtScale hP hStruct (memoryGridScale Nstar L I) ≤ delta := by
  let Fseq : ℕ → ℝ :=
    fun i => contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)
  let H0 : ℝ :=
    initialMemory hc.rhoM N Nstar
      (fun n => contrastExcessAtScale hP hStruct n)
  let Delta : ℕ → ℝ :=
    memoryGridDrop (fun n => contrastExcessAtScale hP hStruct n) Nstar L
  let Hseq : ℕ → ℝ := fun i => memory (memoryDecay hc L) H0 Delta i
  let Yseq : ℕ → ℝ := fun i => lyapunovValue A (Fseq i) (Hseq i)
  have hcontrast_antitone :
      Antitone (fun n => contrastExcessAtScale hP hStruct n) :=
    contrastExcessAtScale_antitone_of_P4 hP hStruct hP4
  have hFseq_antitone : Antitone Fseq := by
    intro i j hij
    dsimp [Fseq]
    exact hcontrast_antitone (memoryGridScale_le_of_le hij)
  have hH0_nonneg : 0 ≤ H0 := by
    dsimp [H0]
    exact initialMemory_nonneg_of_antitone hcontrast_antitone
  have hDelta_nonneg : ∀ i, 0 ≤ Delta i := by
    intro i
    cases i with
    | zero =>
        dsimp [Delta]
        simp
    | succ i =>
        dsimp [Delta]
        exact memoryGridDrop_succ_nonneg_of_antitone hcontrast_antitone Nstar L i
  have hF_le_Y : ∀ i, Fseq i ≤ Yseq i := by
    intro i
    have hH_nonneg : 0 ≤ Hseq i := by
      dsimp [Hseq]
      exact memory_nonneg (le_of_lt (memoryDecay_pos hc L)) hH0_nonneg
        hDelta_nonneg i
    have hAH_nonneg : 0 ≤ A * Hseq i := mul_nonneg hA_nonneg hH_nonneg
    dsimp [Yseq, lyapunovValue]
    linarith
  have hY0' : Yseq 0 ≤ Y0Bound := by
    simpa [Yseq, Hseq, H0, Delta, Fseq] using hY0
  have hstep' :
      ∀ i < I, delta < Fseq (i + 1) →
        Yseq (i + 1) ≤ lambda * Yseq i := by
    intro i hi hdelta
    simpa [Yseq, Hseq, H0, Delta, Fseq] using
      hstep_if_above i hi hdelta
  exact
    endpoint_entry_of_contraction (F := Fseq) (Y := Yseq)
      hFseq_antitone hlambda_nonneg hY0' hpow hF_le_Y hstep'

/--
Source label `e.Nentry`: rewriting the contrast-excess entry
`F_m <= delta` as the displayed small-contrast bound
`Theta_m <= 1 + delta`.
-/
theorem thetaAtScale_le_one_add_of_contrastExcessAtScale_le
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    {m : ℕ} {delta : ℝ}
    (hentry : contrastExcessAtScale hP hStruct m ≤ delta) :
    Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ) ≤ 1 + delta := by
  dsimp [contrastExcessAtScale] at hentry
  change Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ) - 1 ≤ delta at hentry
  linarith

/--
Source label `e.Nentry`: direct displayed small-contrast conclusion at the
memory-grid entry scale `m_I = N_* + I L`.
-/
theorem thetaAt_memoryGridScale_entry_le_one_add_of_contraction
    {d : ℕ} [NeZero d] (hc : HighContrastExponents d) {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {N Nstar L I : ℕ} {A lambda delta Y0Bound : ℝ}
    (hA_nonneg : 0 ≤ A)
    (hlambda_nonneg : 0 ≤ lambda)
    (hY0 :
      lyapunovValue A
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L 0))
          (memory (memoryDecay hc L)
            (initialMemory hc.rhoM N Nstar
              (fun n => contrastExcessAtScale hP hStruct n))
            (memoryGridDrop
              (fun n => contrastExcessAtScale hP hStruct n) Nstar L) 0) ≤
        Y0Bound)
    (hpow : lambda ^ I * Y0Bound ≤ delta)
    (hstep_if_above :
      ∀ i < I,
        delta <
          contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i + 1)) →
        lyapunovValue A
            (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i + 1)))
            (memory (memoryDecay hc L)
              (initialMemory hc.rhoM N Nstar
                (fun n => contrastExcessAtScale hP hStruct n))
              (memoryGridDrop
                (fun n => contrastExcessAtScale hP hStruct n) Nstar L) (i + 1)) ≤
          lambda *
            lyapunovValue A
              (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
              (memory (memoryDecay hc L)
                (initialMemory hc.rhoM N Nstar
                  (fun n => contrastExcessAtScale hP hStruct n))
                (memoryGridDrop
                  (fun n => contrastExcessAtScale hP hStruct n) Nstar L) i)) :
    Homogenization.Book.Ch05.thetaAtScale hP hStruct
        (memoryGridScale Nstar L I : ℤ) ≤ 1 + delta := by
  exact
    thetaAtScale_le_one_add_of_contrastExcessAtScale_le hP hStruct
      (contrastExcessAt_memoryGridScale_entry_le_of_contraction
        (hc := hc) hP hStruct hP4 hA_nonneg hlambda_nonneg hY0 hpow
        hstep_if_above)

/--
Source labels `e.Nentry` and `e.localization`: after entry at `N_entry`, a
localization shift `R` whose error is at most `delta0 / 2` puts the shifted
contrast below `delta0`.
-/
theorem shiftedWidetildeTheta_entry_shift_sub_one_le_delta0
    {d : ℕ} [NeZero d] (hc : HighContrastExponents d) (loc : LocalizationSmallContrastInput hc)
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hcparams : hP4.params = hc.params)
    {Nentry R : ℕ} {delta_sc : ℝ}
    (hentry :
      Homogenization.Book.Ch05.thetaAtScale hP hStruct (Nentry : ℤ) ≤
        1 + delta_sc)
    (hdelta_sc : delta_sc ≤ loc.delta0 / 2)
    (hR :
      loc.C_loc * (3 : ℝ) ^ (-(loc.beta_loc * (R : ℝ))) *
          Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 ≤
        loc.delta0 / 2) :
    Homogenization.Book.Ch05.Section55.shiftedWidetildeThetaAtScale P
        ((Nentry + R : ℕ) : ℤ) hP4 (2 * hc.beta) - 1 ≤ loc.delta0 := by
  have hloc :=
    loc.localization hP hStruct hP4 hcparams
      (k := Nentry) (n := Nentry + R) (Nat.le_add_right Nentry R)
  have hshift_le :
      Homogenization.Book.Ch05.Section55.shiftedWidetildeThetaAtScale P
          ((Nentry + R : ℕ) : ℤ) hP4 (2 * hc.beta) ≤
        Homogenization.Book.Ch05.thetaAtScale hP hStruct (Nentry : ℤ) +
          loc.C_loc * (3 : ℝ) ^ (-(loc.beta_loc * (R : ℝ))) *
            Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 := by
    have hdiff : Nentry + R - Nentry = R := Nat.add_sub_cancel_left Nentry R
    simpa [hdiff] using hloc.2
  linarith

/--
Source labels `e.localization`, `e.small.contrast`, and `e.final.decay`: entry
plus the localization shift gives the small-contrast decay from
`N_1 = N_entry + R`.
-/
theorem thetaAtScale_le_one_add_smallContrast_decay_of_entry_localization
    {d : ℕ} [NeZero d] (hc : HighContrastExponents d) (loc : LocalizationSmallContrastInput hc)
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hcparams : hP4.params = hc.params)
    {Nentry R : ℕ} {delta_sc : ℝ}
    (hentry :
      Homogenization.Book.Ch05.thetaAtScale hP hStruct (Nentry : ℤ) ≤
        1 + delta_sc)
    (hdelta_sc : delta_sc ≤ loc.delta0 / 2)
    (hR :
      loc.C_loc * (3 : ℝ) ^ (-(loc.beta_loc * (R : ℝ))) *
          Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 ≤
        loc.delta0 / 2) :
    ∀ n : ℕ,
      Homogenization.Book.Ch05.thetaAtScale hP hStruct
          (((Nentry + R) + n : ℕ) : ℤ) ≤
        1 + loc.C_sc * (3 : ℝ) ^ (-(loc.alpha0 * (n : ℝ))) := by
  have hsmall_input :
      Homogenization.Book.Ch05.Section55.shiftedWidetildeThetaAtScale P
          ((Nentry + R : ℕ) : ℤ) hP4 (2 * hc.beta) - 1 ≤ loc.delta0 :=
    shiftedWidetildeTheta_entry_shift_sub_one_le_delta0
      (hc := hc) loc hP hStruct hP4 hcparams hentry hdelta_sc hR
  have hsmall :=
    loc.small_contrast hP hStruct hP4 hcparams (N := Nentry + R) hsmall_input
  intro n
  have hn := hsmall n
  linarith

/--
Source label `e.final.decay`: a fixed post-entry shift absorbs the
small-contrast prefactor in a geometric decay estimate.
-/
theorem final_decay_after_shift {Theta : ℕ → ℝ} {N1 Rsc : ℕ} {Csc a : ℝ}
    (ha_nonneg : 0 ≤ a)
    (hshift : Csc * a ^ Rsc ≤ 1)
    (hdecay : ∀ n, Theta (N1 + n) ≤ 1 + Csc * a ^ n) :
    ∀ n, Theta (N1 + Rsc + n) ≤ 1 + a ^ n := by
  intro n
  have hbase : Theta (N1 + (Rsc + n)) ≤ 1 + Csc * a ^ (Rsc + n) :=
    hdecay (Rsc + n)
  have htail : Csc * a ^ (Rsc + n) ≤ a ^ n := by
    rw [pow_add]
    calc
      Csc * (a ^ Rsc * a ^ n)
          = (Csc * a ^ Rsc) * a ^ n := by ring
      _ ≤ 1 * a ^ n :=
          mul_le_mul_of_nonneg_right hshift (pow_nonneg ha_nonneg n)
      _ = a ^ n := by ring
  have htarget : Theta (N1 + Rsc + n) ≤ 1 + Csc * a ^ (Rsc + n) := by
    simpa [Nat.add_assoc] using hbase
  linarith

/--
Source label `e.final.decay`: a fixed small-contrast shift absorbs the
prefactor `C_sc`; this is the `R_sc = O(1)` choice in the note.
-/
theorem exists_smallContrast_prefactor_shift {Csc alpha0 : ℝ}
    (hCsc_pos : 0 < Csc) (halpha0_pos : 0 < alpha0) :
    ∃ Rsc : ℕ, Csc * ((3 : ℝ) ^ (-alpha0)) ^ Rsc ≤ 1 := by
  let a : ℝ := (3 : ℝ) ^ (-alpha0)
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have ha_lt_one : a < 1 := by
    dsimp [a]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : (1 : ℝ) < 3) (by linarith [halpha0_pos])
  obtain ⟨Rsc, hRsc⟩ :=
    exists_pow_lt_of_lt_one (x := Csc⁻¹) (y := a) (inv_pos.mpr hCsc_pos)
      ha_lt_one
  refine ⟨Rsc, ?_⟩
  have hmul : Csc * a ^ Rsc < Csc * Csc⁻¹ :=
    mul_lt_mul_of_pos_left hRsc hCsc_pos
  have hC : Csc * Csc⁻¹ = 1 := by
    field_simp [ne_of_gt hCsc_pos]
  rw [hC] at hmul
  simpa [a] using le_of_lt hmul

/--
Source labels `e.localization`, `e.small.contrast`, and `e.final.decay`:
entry plus localization gives final decay after a supplied fixed
small-contrast shift.
-/
theorem thetaAtScale_le_one_add_final_decay_of_entry_localization_shift
    {d : ℕ} [NeZero d] (hc : HighContrastExponents d) (loc : LocalizationSmallContrastInput hc)
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hcparams : hP4.params = hc.params)
    {Nentry R Rsc : ℕ} {delta_sc : ℝ}
    (hentry :
      Homogenization.Book.Ch05.thetaAtScale hP hStruct (Nentry : ℤ) ≤
        1 + delta_sc)
    (hdelta_sc : delta_sc ≤ loc.delta0 / 2)
    (hR :
      loc.C_loc * (3 : ℝ) ^ (-(loc.beta_loc * (R : ℝ))) *
          Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 ≤
        loc.delta0 / 2)
    (hRsc : loc.C_sc * ((3 : ℝ) ^ (-loc.alpha0)) ^ Rsc ≤ 1) :
    ∀ n : ℕ,
      Homogenization.Book.Ch05.thetaAtScale hP hStruct
          ((((Nentry + R) + Rsc) + n : ℕ) : ℤ) ≤
        1 + (3 : ℝ) ^ (-(loc.alpha0 * (n : ℝ))) := by
  let a : ℝ := (3 : ℝ) ^ (-loc.alpha0)
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hshift : loc.C_sc * a ^ Rsc ≤ 1 := by
    simpa [a] using hRsc
  have hdecay :
      ∀ n : ℕ,
        Homogenization.Book.Ch05.thetaAtScale hP hStruct
            (((Nentry + R) + n : ℕ) : ℤ) ≤ 1 + loc.C_sc * a ^ n := by
    intro n
    have hpre :=
      thetaAtScale_le_one_add_smallContrast_decay_of_entry_localization
        (hc := hc) loc hP hStruct hP4 hcparams hentry hdelta_sc hR n
    have hpow_eq : a ^ n = (3 : ℝ) ^ (-(loc.alpha0 * (n : ℝ))) := by
      dsimp [a]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))]
      congr 1
      ring
    simpa [hpow_eq] using hpre
  have hfinal :=
    final_decay_after_shift
      (Theta := fun m =>
        Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ))
      (N1 := Nentry + R) ha_nonneg hshift hdecay
  intro n
  have h := hfinal n
  have hpow_eq : a ^ n = (3 : ℝ) ^ (-(loc.alpha0 * (n : ℝ))) := by
    dsimp [a]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))]
    congr 1
    ring
  simpa [hpow_eq] using h

/--
Source label `e.final.scale`: logarithmic choice of the localization shift.
The returned constant is uniform in the initial contrast parameter `T`.
-/
theorem exists_localizationShift_le_log_and_error
    {C_loc beta_loc eta : ℝ}
    (hC_loc : 0 ≤ C_loc) (hbeta_loc_pos : 0 < beta_loc)
    (heta_pos : 0 < eta) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {T : ℝ}, 1 ≤ T →
        ∃ R : ℕ,
          C_loc * (3 : ℝ) ^ (-(beta_loc * (R : ℝ))) * T ≤ eta ∧
          (R : ℝ) ≤ 2 * B * Real.logb 3 (2 + T) := by
  obtain ⟨B, hB_one, hB⟩ :=
    exists_bufferExponent_for_polynomial_geometric_envelope_no_linear_le
      (C := C_loc) (A := 1) (c := beta_loc) (η := eta)
      hC_loc hbeta_loc_pos heta_pos
  refine ⟨B, hB_one, ?_⟩
  intro T hT
  let R : ℕ := Nat.ceil (B * Real.logb 3 (2 + T))
  have hlog_nonneg : 0 ≤ Real.logb 3 (2 + T) :=
    Real.logb_nonneg (by norm_num : (1 : ℝ) < 3) (by linarith : 1 ≤ 2 + T)
  have hlog_ge_one : 1 ≤ Real.logb 3 (2 + T) := by
    have hmono :
        Real.logb 3 3 ≤ Real.logb 3 (2 + T) :=
      Real.logb_le_logb_of_le
        (by norm_num : (1 : ℝ) < 3)
        (by norm_num : (0 : ℝ) < 3)
        (by linarith : (3 : ℝ) ≤ 2 + T)
    simpa [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 3)] using hmono
  have hB_nonneg : 0 ≤ B := by linarith
  have hx_nonneg : 0 ≤ B * Real.logb 3 (2 + T) :=
    mul_nonneg hB_nonneg hlog_nonneg
  have hbuf : B * Real.logb 3 (2 + T) ≤ (R : ℝ) := by
    dsimp [R]
    exact Nat.le_ceil _
  refine ⟨R, ?_, ?_⟩
  let decay : ℝ := (3 : ℝ) ^ (-(beta_loc * (R : ℝ)))
  have hdecay_nonneg : 0 ≤ decay := by
    dsimp [decay]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hbig :
      C_loc * (((2 + T : ℝ) ^ (1 : ℝ)) *
          (3 : ℝ) ^ (-beta_loc * (R : ℝ))) ≤ eta :=
    hB hT hbuf
  have hT_le : T ≤ (2 + T : ℝ) ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    linarith
  have hinner :
      T * decay ≤ ((2 + T : ℝ) ^ (1 : ℝ)) * decay :=
    mul_le_mul_of_nonneg_right hT_le hdecay_nonneg
  have htarget_le :
      C_loc * decay * T ≤
        C_loc * (((2 + T : ℝ) ^ (1 : ℝ)) * decay) := by
    calc
      C_loc * decay * T = C_loc * (T * decay) := by ring
      _ ≤ C_loc * (((2 + T : ℝ) ^ (1 : ℝ)) * decay) :=
          mul_le_mul_of_nonneg_left hinner hC_loc
  have hgoal : C_loc * decay * T ≤ eta :=
    htarget_le.trans (by simpa [decay, neg_mul] using hbig)
  simpa [decay, neg_mul] using hgoal
  have hceil_lt : (R : ℝ) < B * Real.logb 3 (2 + T) + 1 := by
    dsimp [R]
    exact Nat.ceil_lt_add_one hx_nonneg
  have hBlog_ge_one : 1 ≤ B * Real.logb 3 (2 + T) := by
    nlinarith
  linarith

/--
Source label `e.final.scale`: source-facing base-three logarithmic form of
the polynomial physical-scale estimate.
-/
theorem physical_scale_le_of_logb_bound {N : ℕ} {C T : ℝ}
    (hbase : 0 < 2 + T)
    (hlog : (N : ℝ) ≤ C * Real.logb 3 (2 + T)) :
    (3 : ℝ) ^ N ≤ Real.rpow (2 + T) C := by
  have htarget_log :
      (N : ℝ) ≤ Real.logb 3 (Real.rpow (2 + T) C) := by
    simpa [Real.logb_rpow_eq_mul_logb_of_pos hbase] using hlog
  have htarget :
      (3 : ℝ) ^ (N : ℝ) ≤ Real.rpow (2 + T) C := by
    exact
      (Real.le_logb_iff_rpow_le (b := 3) (x := (N : ℝ))
        (y := Real.rpow (2 + T) C)
        (by norm_num : (1 : ℝ) < 3)
        (Real.rpow_pos_of_pos hbase C)).mp htarget_log
  simpa [Real.rpow_natCast] using htarget

/--
Source label `e.final.scale`: for `T >= 1`, the source logarithm
`log_3(2+T)` is at least one.
-/
theorem one_le_logb_three_two_add {T : ℝ} (hT : 1 ≤ T) :
    1 ≤ Real.logb 3 (2 + T) := by
  have hmono :
      Real.logb 3 3 ≤ Real.logb 3 (2 + T) :=
    Real.logb_le_logb_of_le
      (by norm_num : (1 : ℝ) < 3)
      (by norm_num : (0 : ℝ) < 3)
      (by linarith : (3 : ℝ) ≤ 2 + T)
  simpa [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 3)] using hmono

/--
Source label `e.final.scale`: the entry scale, localization shift, and fixed
small-contrast shift have the same logarithmic size once each component does.
-/
theorem final_index_le_log_of_components
    {Nentry R Rsc : ℕ} {Centry CR T : ℝ}
    (hT : 1 ≤ T)
    (hNentry : (Nentry : ℝ) ≤ Centry * Real.logb 3 (2 + T))
    (hR : (R : ℝ) ≤ CR * Real.logb 3 (2 + T)) :
    (((Nentry + R) + Rsc : ℕ) : ℝ) ≤
      (Centry + CR + (Rsc : ℝ) + 1) * Real.logb 3 (2 + T) := by
  have hlog_ge_one : 1 ≤ Real.logb 3 (2 + T) :=
    one_le_logb_three_two_add hT
  have hlog_nonneg : 0 ≤ Real.logb 3 (2 + T) := by linarith
  have hRsc_log : (Rsc : ℝ) ≤ (Rsc : ℝ) * Real.logb 3 (2 + T) := by
    have hRsc_nonneg : 0 ≤ (Rsc : ℝ) := by positivity
    nlinarith
  have hsum :
      (Nentry : ℝ) + (R : ℝ) + (Rsc : ℝ) ≤
        Centry * Real.logb 3 (2 + T) +
          CR * Real.logb 3 (2 + T) +
            (Rsc : ℝ) * Real.logb 3 (2 + T) := by
    exact add_le_add (add_le_add hNentry hR) hRsc_log
  have hcoeff :
      Centry * Real.logb 3 (2 + T) +
          CR * Real.logb 3 (2 + T) +
            (Rsc : ℝ) * Real.logb 3 (2 + T) ≤
        (Centry + CR + (Rsc : ℝ) + 1) * Real.logb 3 (2 + T) := by
    nlinarith
  calc
    (((Nentry + R) + Rsc : ℕ) : ℝ)
        = (Nentry : ℝ) + (R : ℝ) + (Rsc : ℝ) := by norm_num [Nat.cast_add]
    _ ≤ Centry * Real.logb 3 (2 + T) +
          CR * Real.logb 3 (2 + T) +
            (Rsc : ℝ) * Real.logb 3 (2 + T) := hsum
    _ ≤ (Centry + CR + (Rsc : ℝ) + 1) * Real.logb 3 (2 + T) := hcoeff

/--
Source labels `e.Nentry` and `t.main`: the displayed choice
`N_* = N + ceil(B log_3(2+T))` supplies the buffer lower bound needed by the
Main high-moment estimates at every memory-grid step.
-/
theorem buffer_bound_le_memoryGridScale_of_nstar_eq
    {N Nstar L i : ℕ} {B T : ℝ}
    (hNstar :
      Nstar = N + Nat.ceil (B * Real.logb 3 (2 + T))) :
    N + Nat.ceil (B * Real.logb 3 (2 + T)) ≤ memoryGridScale Nstar L i := by
  dsimp [memoryGridScale]
  rw [hNstar]
  exact Nat.le_add_right (N + Nat.ceil (B * Real.logb 3 (2 + T))) (i * L)

/--
Source label `e.Nentry`: if the high-moment start scale `N` is logarithmic
and `N_*` is chosen by adding a logarithmic buffer, then `N_*` is logarithmic.
-/
theorem nstar_le_log_of_base_buffer
    {N Nstar : ℕ} {CN B T : ℝ}
    (hT : 1 ≤ T)
    (hB_nonneg : 0 ≤ B)
    (hN : (N : ℝ) ≤ CN * Real.logb 3 (2 + T))
    (hNstar : Nstar ≤ N + Nat.ceil (B * Real.logb 3 (2 + T))) :
    (Nstar : ℝ) ≤ (CN + B + 1) * Real.logb 3 (2 + T) := by
  let Llog : ℝ := Real.logb 3 (2 + T)
  have hlog_ge_one : 1 ≤ Llog := by
    dsimp [Llog]
    exact one_le_logb_three_two_add hT
  have hlog_nonneg : 0 ≤ Llog := by linarith
  have hBL_nonneg : 0 ≤ B * Llog := mul_nonneg hB_nonneg hlog_nonneg
  have hceil_le : (Nat.ceil (B * Llog) : ℝ) ≤ B * Llog + 1 :=
    le_of_lt (Nat.ceil_lt_add_one hBL_nonneg)
  have hNstar_real :
      (Nstar : ℝ) ≤ ((N + Nat.ceil (B * Llog) : ℕ) : ℝ) := by
    exact_mod_cast (by simpa [Llog] using hNstar)
  have hN_L : (N : ℝ) ≤ CN * Llog := by
    simpa [Llog] using hN
  calc
    (Nstar : ℝ)
        ≤ ((N + Nat.ceil (B * Llog) : ℕ) : ℝ) := hNstar_real
    _ = (N : ℝ) + Nat.ceil (B * Llog) := by norm_num [Nat.cast_add]
    _ ≤ CN * Llog + (B * Llog + 1) := add_le_add hN_L hceil_le
    _ ≤ (CN + B + 1) * Llog := by nlinarith

/--
Source label `e.Nentry`: if `N_*` and the iteration count `I` are
logarithmic, then the memory-grid entry scale `m_I = N_* + I L` is
logarithmic.
-/
theorem memoryGridScale_le_log_of_components
    {Nstar I L : ℕ} {CNstar CI T : ℝ}
    (hT : 1 ≤ T)
    (hNstar : (Nstar : ℝ) ≤ CNstar * Real.logb 3 (2 + T))
    (hI : (I : ℝ) ≤ CI * Real.logb 3 (2 + T)) :
    (memoryGridScale Nstar L I : ℝ) ≤
      (CNstar + (L : ℝ) * CI + 1) * Real.logb 3 (2 + T) := by
  let Llog : ℝ := Real.logb 3 (2 + T)
  have hlog_ge_one : 1 ≤ Llog := by
    dsimp [Llog]
    exact one_le_logb_three_two_add hT
  have hlog_nonneg : 0 ≤ Llog := by linarith
  have hI_L :
      (I : ℝ) * (L : ℝ) ≤ (CI * Llog) * (L : ℝ) :=
    mul_le_mul_of_nonneg_right (by simpa [Llog] using hI) (by positivity)
  calc
    (memoryGridScale Nstar L I : ℝ)
        = (Nstar : ℝ) + (I : ℝ) * (L : ℝ) := by
            simp [memoryGridScale, Nat.cast_add, Nat.cast_mul]
    _ ≤ CNstar * Llog + (CI * Llog) * (L : ℝ) :=
        add_le_add (by simpa [Llog] using hNstar) hI_L
    _ = (CNstar + (L : ℝ) * CI) * Llog := by ring
    _ ≤ (CNstar + (L : ℝ) * CI + 1) * Llog := by nlinarith

/--
Source label `e.Nentry`: combined bookkeeping for
`N_entry = m_I = N_* + I L` from the concrete buffered choice of `N_*` and a
logarithmic bound on the iteration count `I`.
-/
theorem memoryGridScale_le_log_of_base_buffer_iterations
    {N Nstar I L : ℕ} {CN B CI T : ℝ}
    (hT : 1 ≤ T)
    (hB_nonneg : 0 ≤ B)
    (hN : (N : ℝ) ≤ CN * Real.logb 3 (2 + T))
    (hNstar : Nstar ≤ N + Nat.ceil (B * Real.logb 3 (2 + T)))
    (hI : (I : ℝ) ≤ CI * Real.logb 3 (2 + T)) :
    (memoryGridScale Nstar L I : ℝ) ≤
      (CN + B + 1 + (L : ℝ) * CI + 1) * Real.logb 3 (2 + T) := by
  have hNstar_log :
      (Nstar : ℝ) ≤ (CN + B + 1) * Real.logb 3 (2 + T) :=
    nstar_le_log_of_base_buffer hT hB_nonneg hN hNstar
  have hgrid :=
    memoryGridScale_le_log_of_components
      (Nstar := Nstar) (I := I) (L := L)
      (CNstar := CN + B + 1) (CI := CI) (T := T)
      hT hNstar_log hI
  simpa [add_assoc] using hgrid

/--
Source label `e.Nentry`: the source initial Lyapunov value satisfies
`Y_0 <= C_A T` once `C_A` dominates the fixed Lyapunov weight.
-/
theorem initial_lyapunovValue_le_const_mul_initialWidetildeTheta_of_P4
    {d : ℕ} [NeZero d] (hc : HighContrastExponents d) {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {N Nstar L : ℕ} {A C_A : ℝ}
    (hNNstar : N ≤ Nstar)
    (hA_nonneg : 0 ≤ A)
    (hC_A : 1 + A ≤ C_A) :
    lyapunovValue A
        (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L 0))
        (memory (memoryDecay hc L)
          (initialMemory hc.rhoM N Nstar
            (fun n => contrastExcessAtScale hP hStruct n))
          (memoryGridDrop
            (fun n => contrastExcessAtScale hP hStruct n) Nstar L) 0) ≤
      C_A * Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 := by
  let T : ℝ := Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4
  have hT_one : 1 ≤ T := by
    dsimp [T]
    exact one_le_initialWidetildeTheta_of_P4 hP hStruct hP4
  have hT_nonneg : 0 ≤ T := le_trans zero_le_one hT_one
  have hF_le_T :
      contrastExcessAtScale hP hStruct (memoryGridScale Nstar L 0) ≤ T := by
    have htheta :
        Homogenization.Book.Ch05.thetaAtScale hP hStruct
            (memoryGridScale Nstar L 0 : ℤ) ≤ T := by
      dsimp [T]
      exact thetaAtScale_le_initialWidetildeTheta_of_P4 hP hStruct hP4
        (memoryGridScale Nstar L 0)
    change
      Homogenization.Book.Ch05.thetaAtScale hP hStruct
          (memoryGridScale Nstar L 0 : ℤ) - 1 ≤ T
    linarith
  have hH_le_T :
      initialMemory hc.rhoM N Nstar
          (fun n => contrastExcessAtScale hP hStruct n) ≤ T := by
    dsimp [T]
    exact initialMemory_contrastExcessAtScale_le_initialWidetildeTheta_of_P4
      hc hP hStruct hP4 hNNstar
  have hAH_le : A *
      memory (memoryDecay hc L)
        (initialMemory hc.rhoM N Nstar
          (fun n => contrastExcessAtScale hP hStruct n))
        (memoryGridDrop
          (fun n => contrastExcessAtScale hP hStruct n) Nstar L) 0 ≤
        A * T := by
    simpa [memory] using mul_le_mul_of_nonneg_left hH_le_T hA_nonneg
  calc
    lyapunovValue A
        (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L 0))
        (memory (memoryDecay hc L)
          (initialMemory hc.rhoM N Nstar
            (fun n => contrastExcessAtScale hP hStruct n))
          (memoryGridDrop
            (fun n => contrastExcessAtScale hP hStruct n) Nstar L) 0)
        = contrastExcessAtScale hP hStruct (memoryGridScale Nstar L 0) +
            A *
              memory (memoryDecay hc L)
                (initialMemory hc.rhoM N Nstar
                  (fun n => contrastExcessAtScale hP hStruct n))
                (memoryGridDrop
                  (fun n => contrastExcessAtScale hP hStruct n) Nstar L) 0 := rfl
    _ ≤ T + A * T := add_le_add hF_le_T hAH_le
    _ = (1 + A) * T := by ring
    _ ≤ C_A * T := mul_le_mul_of_nonneg_right hC_A hT_nonneg

/--
Source label `e.Nentry`: the displayed choice of `I` makes the contracted
initial bound small enough, using the source's harmless `2 + T` enlargement.
-/
theorem contraction_power_mul_le_delta_of_iteration_choice
    {C_A delta lambda T : ℝ} {I : ℕ}
    (hT : 1 ≤ T)
    (hC_A_pos : 0 < C_A)
    (hdelta_pos : 0 < delta)
    (hlambda_pos : 0 < lambda)
    (hlambda_lt_one : lambda < 1)
    (hI :
      I =
        Nat.ceil
          (Real.log (C_A * (2 + T) / delta) / |Real.log lambda|)) :
    lambda ^ I * (C_A * T) ≤ delta := by
  let arg : ℝ := C_A * (2 + T) / delta
  let x : ℝ := Real.log arg / |Real.log lambda|
  have harg_pos : 0 < arg := by
    dsimp [arg]
    exact div_pos (mul_pos hC_A_pos (by linarith : 0 < 2 + T)) hdelta_pos
  have hlog_lambda_neg : Real.log lambda < 0 :=
    Real.log_neg hlambda_pos hlambda_lt_one
  have hD_eq : |Real.log lambda| = -Real.log lambda := by
    exact abs_of_neg hlog_lambda_neg
  have hD_pos : 0 < |Real.log lambda| := by
    exact abs_pos.mpr (ne_of_lt hlog_lambda_neg)
  have hx_le_I : x ≤ (I : ℝ) := by
    rw [hI]
    dsimp [x, arg]
    exact Nat.le_ceil _
  have hpow_rpow :
      lambda ^ I ≤ lambda ^ x := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hlambda_pos (le_of_lt hlambda_lt_one)
      hx_le_I
  have hpow_arg_eq :
      lambda ^ x * arg = 1 := by
    have hx_exp : lambda ^ x = Real.exp (-Real.log arg) := by
      dsimp [x]
      rw [Real.rpow_def_of_pos hlambda_pos]
      congr 1
      rw [hD_eq]
      field_simp [ne_of_lt hlog_lambda_neg]
    calc
      lambda ^ x * arg
          = Real.exp (-Real.log arg) * arg := by rw [hx_exp]
      _ = arg⁻¹ * arg := by rw [Real.exp_neg, Real.exp_log harg_pos]
      _ = 1 := by field_simp [ne_of_gt harg_pos]
  have hpow_mul_arg : lambda ^ I * arg ≤ 1 := by
    have harg_nonneg : 0 ≤ arg := le_of_lt harg_pos
    calc
      lambda ^ I * arg ≤ lambda ^ x * arg :=
        mul_le_mul_of_nonneg_right hpow_rpow harg_nonneg
      _ = 1 := hpow_arg_eq
  have htarget_enlarged :
      lambda ^ I * (C_A * (2 + T)) ≤ delta := by
    have hdelta_nonneg : 0 ≤ delta := le_of_lt hdelta_pos
    have hmul := mul_le_mul_of_nonneg_right hpow_mul_arg hdelta_nonneg
    have harg_delta :
        arg * delta = C_A * (2 + T) := by
      dsimp [arg]
      field_simp [ne_of_gt hdelta_pos]
    calc
      lambda ^ I * (C_A * (2 + T))
          = (lambda ^ I * arg) * delta := by
            rw [← harg_delta]
            ring
      _ ≤ 1 * delta := hmul
      _ = delta := by ring
  have hT_le : C_A * T ≤ C_A * (2 + T) :=
    mul_le_mul_of_nonneg_left (by linarith : T ≤ 2 + T) (le_of_lt hC_A_pos)
  have hpow_nonneg : 0 ≤ lambda ^ I := pow_nonneg (le_of_lt hlambda_pos) I
  calc
    lambda ^ I * (C_A * T)
        ≤ lambda ^ I * (C_A * (2 + T)) :=
          mul_le_mul_of_nonneg_left hT_le hpow_nonneg
    _ ≤ delta := htarget_enlarged

/--
Source label `e.Nentry`: the displayed ceiling formula for the iteration
count `I` is logarithmic in the initial contrast budget.
-/
theorem iteration_count_le_log_of_choices
    {C_A delta_sc lambda T : ℝ} {I : ℕ}
    (hT : 1 ≤ T)
    (hC_A_pos : 0 < C_A)
    (hdelta_sc_pos : 0 < delta_sc)
    (hlambda_pos : 0 < lambda)
    (hlambda_lt_one : lambda < 1)
    (hI :
      I =
        Nat.ceil
          (Real.log (C_A * (2 + T) / delta_sc) / |Real.log lambda|)) :
    (I : ℝ) ≤
      (((max 0 (Real.log (C_A / delta_sc) / Real.log 3) + 1) *
            Real.log 3) / |Real.log lambda| + 1) *
        Real.logb 3 (2 + T) := by
  let Llog : ℝ := Real.logb 3 (2 + T)
  let c0 : ℝ := max 0 (Real.log (C_A / delta_sc) / Real.log 3)
  let D : ℝ := |Real.log lambda|
  let CI0 : ℝ := ((c0 + 1) * Real.log 3) / D
  have hlog_lambda_neg : Real.log lambda < 0 :=
    Real.log_neg hlambda_pos hlambda_lt_one
  have hD_pos : 0 < D := by
    dsimp [D]
    exact abs_pos.mpr (ne_of_lt hlog_lambda_neg)
  have hlog3_pos : 0 < Real.log 3 :=
    Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hbase_pos : 0 < 2 + T := by linarith
  have hratio_pos : 0 < C_A / delta_sc := div_pos hC_A_pos hdelta_sc_pos
  have hLlog_ge_one : 1 ≤ Llog := by
    dsimp [Llog]
    exact one_le_logb_three_two_add hT
  have hLlog_nonneg : 0 ≤ Llog := by linarith
  have hc0_nonneg : 0 ≤ c0 := by
    dsimp [c0]
    exact le_max_left 0 (Real.log (C_A / delta_sc) / Real.log 3)
  have hlog_ratio_le : Real.log (C_A / delta_sc) ≤ c0 * Real.log 3 := by
    have hdiv_le : Real.log (C_A / delta_sc) / Real.log 3 ≤ c0 := by
      dsimp [c0]
      exact le_max_right 0 (Real.log (C_A / delta_sc) / Real.log 3)
    have hmul :=
      mul_le_mul_of_nonneg_right hdiv_le (le_of_lt hlog3_pos)
    calc
      Real.log (C_A / delta_sc)
          = (Real.log (C_A / delta_sc) / Real.log 3) * Real.log 3 := by
              field_simp [ne_of_gt hlog3_pos]
      _ ≤ c0 * Real.log 3 := hmul
  have hlog_two_add :
      Real.log (2 + T) = Real.log 3 * Llog := by
    dsimp [Llog, Real.logb]
    field_simp [ne_of_gt hlog3_pos]
  have harg_eq :
      C_A * (2 + T) / delta_sc = (C_A / delta_sc) * (2 + T) := by
    field_simp [ne_of_gt hdelta_sc_pos]
  have hlog_arg :
      Real.log (C_A * (2 + T) / delta_sc) =
        Real.log (C_A / delta_sc) + Real.log (2 + T) := by
    rw [harg_eq]
    exact Real.log_mul (ne_of_gt hratio_pos) (ne_of_gt hbase_pos)
  have hnum_le :
      Real.log (C_A * (2 + T) / delta_sc) ≤
        (c0 + 1) * Real.log 3 * Llog := by
    calc
      Real.log (C_A * (2 + T) / delta_sc)
          = Real.log (C_A / delta_sc) + Real.log (2 + T) := hlog_arg
      _ ≤ c0 * Real.log 3 + Real.log 3 * Llog := by
          exact add_le_add hlog_ratio_le (le_of_eq hlog_two_add)
      _ ≤ (c0 + 1) * Real.log 3 * Llog := by
          have hc0_log_nonneg : 0 ≤ c0 * Real.log 3 :=
            mul_nonneg hc0_nonneg (le_of_lt hlog3_pos)
          have hc0_log_le :
              c0 * Real.log 3 ≤ c0 * Real.log 3 * Llog := by
            nlinarith
          calc
            c0 * Real.log 3 + Real.log 3 * Llog
                = Real.log 3 * Llog + c0 * Real.log 3 := by ring
            _ ≤ Real.log 3 * Llog + c0 * Real.log 3 * Llog :=
                  add_le_add_right hc0_log_le (Real.log 3 * Llog)
            _ = (c0 + 1) * Real.log 3 * Llog := by ring
  let x : ℝ := Real.log (C_A * (2 + T) / delta_sc) / D
  have hx_le : x ≤ CI0 * Llog := by
    dsimp [x, CI0]
    calc
      Real.log (C_A * (2 + T) / delta_sc) / D
          ≤ ((c0 + 1) * Real.log 3 * Llog) / D :=
            div_le_div_of_nonneg_right hnum_le (le_of_lt hD_pos)
      _ = (((c0 + 1) * Real.log 3) / D) * Llog := by ring
  have hCI0_nonneg : 0 ≤ CI0 := by
    dsimp [CI0]
    exact div_nonneg
      (mul_nonneg (by nlinarith) (le_of_lt hlog3_pos))
      (le_of_lt hD_pos)
  have hCI0L_nonneg : 0 ≤ CI0 * Llog :=
    mul_nonneg hCI0_nonneg hLlog_nonneg
  have hceil_mono : Nat.ceil x ≤ Nat.ceil (CI0 * Llog) :=
    Nat.ceil_mono hx_le
  have hI_cast_le : (I : ℝ) ≤ (Nat.ceil (CI0 * Llog) : ℝ) := by
    rw [hI]
    exact_mod_cast (by simpa [x, D] using hceil_mono)
  have hceil_upper :
      (Nat.ceil (CI0 * Llog) : ℝ) ≤ CI0 * Llog + 1 :=
    le_of_lt (Nat.ceil_lt_add_one hCI0L_nonneg)
  calc
    (I : ℝ) ≤ (Nat.ceil (CI0 * Llog) : ℝ) := hI_cast_le
    _ ≤ CI0 * Llog + 1 := hceil_upper
    _ ≤ (CI0 + 1) * Llog := by nlinarith

end Homogenization.HighContrast.EntryScale
