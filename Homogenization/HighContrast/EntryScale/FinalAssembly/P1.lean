import Mathlib.Tactic.Positivity
import Homogenization.HighContrast.EntryScale.ResponseFluctuation.P1

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization.Book.Ch05.Section54.OneStepContraction
open scoped Matrix.Norms.Elementwise


/-!
# Final assembly for the high-moment theorem

This file connects the fixed-order entry-scale API to the `Main.lean`
raw-energy scalar Lyapunov bridge.  The raw cutoff geometric tail is discharged
by the large block length chosen here.  The remaining high-contrast obligations
are the local lower-edge/tail scalar hypotheses; they are not hidden behind a
packaged intermediate proposition.
-/


namespace Homogenization.HighContrast.EntryScale

def unitCoordinateVector {d : ℕ} [NeZero d] : Homogenization.Vec d :=
  Pi.single (0 : Fin d) 1

theorem unitCoordinateVector_vecNorm {d : ℕ} [NeZero d] :
    Homogenization.Book.Ch02.vecNorm (unitCoordinateVector : Homogenization.Vec d) = 1 := by
  have hsq :
      Homogenization.Book.Ch02.vecNorm
          (unitCoordinateVector : Homogenization.Vec d) ^ (2 : ℕ) = 1 := by
    have hvecSq :
        Homogenization.vecNormSq (unitCoordinateVector : Homogenization.Vec d) = 1 := by
      rw [unitCoordinateVector, Homogenization.vecNormSq, Homogenization.vecDot,
        Finset.sum_eq_single (0 : Fin d)]
      · simp
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp
    simpa [hvecSq] using
      Homogenization.Book.Ch02.vecNorm_sq_eq_vecNormSq
        (unitCoordinateVector : Homogenization.Vec d)
  have hnonneg :
      0 ≤ Homogenization.Book.Ch02.vecNorm
        (unitCoordinateVector : Homogenization.Vec d) :=
    Homogenization.Book.Ch02.vecNorm_nonneg _
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact h
  · linarith

/--
Source labels `e.raw.CR.energy` and `e.final.scale`: canonical scalar size
large enough for the raw centered-response coefficient lower bounds at one
active memory-grid step.
-/
noncomputable def finalAssemblySourceStepBound
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (C_lin C_high : ℝ) : ℝ :=
  let β := section53CoarseFluctuationBeta hP4
  let K :=
    Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst
      d
  max 1
    (max (2 * (1 + (2 : ℝ) ^ d))
      (max C_lin
        (max (C_lin * 16 * (C_high * β⁻¹) + C_lin * 16 * K ^ 2)
          (max (C_lin * 16 * K ^ 2 * (5 * β⁻¹))
            (1 + C_lin * 16 * K ^ 2 + C_lin * 16 * K ^ 2)))))

/--
Source labels `l.S.and.J` and `e.tau.sum.absorb`: canonical fluctuation scalar
large enough for the half-threshold and geometric-weight absorptions.
-/
noncomputable def finalAssemblyFluctuationBound
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (delta_sc : ℝ) : ℝ :=
  max (2 * (1 + (delta_sc / 2)⁻¹) ^ 2)
    (2 * section53CoarseFluctuationWeightSumConstant hP4)

/-- Parameter-level version of the Section 5.3 geometric-weight constant. -/
noncomputable def section53CoarseFluctuationWeightSumConstantParams
    {d : ℕ}
    (params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d) :
    ℝ :=
  (1 - Real.rpow (3 : ℝ) (-(section53CoarseFluctuationBetaParams params)))⁻¹

/--
Parameter-level source-step bound.  This is used before a particular law `P`
has been introduced, so the final constants are uniform over all laws with the
fixed quantitative ellipticity parameters.
-/
noncomputable def finalAssemblySourceStepBoundParams
    {d : ℕ} [NeZero d]
    (params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    (C_lin C_high : ℝ) : ℝ :=
  let β := section53CoarseFluctuationBetaParams params
  let K :=
    Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst
      d
  max 1
    (max (2 * (1 + (2 : ℝ) ^ d))
      (max C_lin
        (max (C_lin * 16 * (C_high * β⁻¹) + C_lin * 16 * K ^ 2)
          (max (C_lin * 16 * K ^ 2 * (5 * β⁻¹))
            (1 + C_lin * 16 * K ^ 2 + C_lin * 16 * K ^ 2)))))

/-- Parameter-level fluctuation bound used for uniform final scalar budgets. -/
noncomputable def finalAssemblyFluctuationBoundParams
    {d : ℕ}
    (params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    (delta_sc : ℝ) : ℝ :=
  max (2 * (1 + (delta_sc / 2)⁻¹) ^ 2)
    (2 * section53CoarseFluctuationWeightSumConstantParams params)

/-- Final memory budget chosen from parameter-level raw constants. -/
noncomputable def finalAssemblyMemoryBudgetBoundParams
    {d : ℕ} [NeZero d]
    (params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    (C_lin C_high : ℝ) : ℝ :=
  max (0 : ℝ) (6 * finalAssemblySourceStepBoundParams params C_lin C_high)

/-- Final one-step error budget chosen from parameter-level raw constants. -/
noncomputable def finalAssemblyDeltaBudgetBoundParams
    {d : ℕ} [NeZero d]
    (params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    (delta_sc C_resp C_lin C_high : ℝ) : ℝ :=
  let C_step := finalAssemblySourceStepBoundParams params C_lin C_high
  let C_fluct := finalAssemblyFluctuationBoundParams params delta_sc
  max (0 : ℝ)
    (max (2 * (C_step * C_fluct))
      (max (C_step * (1 + C_resp) * ((1 + (delta_sc / 2)⁻¹) ^ 2))
        (max (12 * C_step)
          (max (6 * C_step * (1 + (delta_sc / 2)⁻¹))
            (C_step * 2 * Real.sqrt (delta_sc / 2)⁻¹)))))

theorem finalAssemblySourceStepBound_eq_params
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d}
    (hparams : hP4.params = params) (C_lin C_high : ℝ) :
    finalAssemblySourceStepBound hP4 C_lin C_high =
      finalAssemblySourceStepBoundParams params C_lin C_high := by
  have hβ :
      section53CoarseFluctuationBeta hP4 =
        section53CoarseFluctuationBetaParams params := by
    simpa [hparams] using
      (section53CoarseFluctuationBetaParams_eq_of_P4 hP4).symm
  simp [finalAssemblySourceStepBound, finalAssemblySourceStepBoundParams, hβ]

private theorem section53CoarseFluctuationWeightSumConstant_eq_params
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d}
    (hparams : hP4.params = params) :
    section53CoarseFluctuationWeightSumConstant hP4 =
      section53CoarseFluctuationWeightSumConstantParams params := by
  have hβ :
      section53CoarseFluctuationBeta hP4 =
        section53CoarseFluctuationBetaParams params := by
    simpa [hparams] using
      (section53CoarseFluctuationBetaParams_eq_of_P4 hP4).symm
  simp [section53CoarseFluctuationWeightSumConstant,
    section53CoarseFluctuationWeightSumConstantParams, hβ]

theorem finalAssemblyFluctuationBound_eq_params
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d}
    (hparams : hP4.params = params) (delta_sc : ℝ) :
    finalAssemblyFluctuationBound hP4 delta_sc =
      finalAssemblyFluctuationBoundParams params delta_sc := by
  have hCw := section53CoarseFluctuationWeightSumConstant_eq_params hP4 hparams
  simp [finalAssemblyFluctuationBound, finalAssemblyFluctuationBoundParams, hCw]

/--
Source labels `l.S.and.J`, `e.tau.sum.absorb`, `e.sqrt.tau.absorb`, and
`e.raw.CR.energy`: deterministic scalar bookkeeping for one active
memory-grid step.

This is not a high-contrast feed wrapper: it only chooses the six scalar
witnesses used by the one-step theorem and proves the corresponding real
inequalities from explicit budget bounds.
-/
theorem final_assembly_source_step_scalars
    {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {delta_sc C_delta C_memory C_resp C_lin C_high : ℝ}
    (hmemory_budget :
      6 * finalAssemblySourceStepBound hP4 C_lin C_high ≤ C_memory)
    (hfluct_budget :
      2 *
          (finalAssemblySourceStepBound hP4 C_lin C_high *
            finalAssemblyFluctuationBound hP4 delta_sc) ≤
        C_delta)
    (hresponse_budget :
      finalAssemblySourceStepBound hP4 C_lin C_high *
          (1 + C_resp) * ((1 + (delta_sc / 2)⁻¹) ^ 2) ≤
        C_delta)
    (hbad_budget :
      12 * finalAssemblySourceStepBound hP4 C_lin C_high ≤ C_delta)
    (hbad_threshold_budget :
      6 * finalAssemblySourceStepBound hP4 C_lin C_high *
          (1 + (delta_sc / 2)⁻¹) ≤
        C_delta)
    (hsqrt_budget :
      finalAssemblySourceStepBound hP4 C_lin C_high *
          2 * Real.sqrt (delta_sc / 2)⁻¹ ≤
        C_delta) :
    let C_step : ℝ := finalAssemblySourceStepBound hP4 C_lin C_high
    let C_norm : ℝ := 1
    let C_S : ℝ := C_delta / 2
    let C_bad : ℝ := C_delta / 2
    let C_fluct : ℝ := finalAssemblyFluctuationBound hP4 delta_sc
    let C_sqrt : ℝ := 2
    0 < C_step ∧
    0 < C_norm ∧
    0 ≤ C_sqrt ∧
    C_S ≤ C_delta ∧
    C_bad ≤ C_delta ∧
    C_S + C_bad ≤ C_delta ∧
    6 * C_step ≤ C_bad ∧
    6 * C_step ≤ C_memory ∧
    2 * (1 + (delta_sc / 2)⁻¹) ^ 2 ≤ C_fluct ∧
    2 * section53CoarseFluctuationWeightSumConstant hP4 ≤ C_fluct ∧
    C_step * C_fluct ≤ C_S ∧
    C_step * (1 + C_resp) * ((1 + (delta_sc / 2)⁻¹) ^ 2) ≤ C_delta ∧
    3 * C_step * (1 + (delta_sc / 2)⁻¹) ≤ C_bad ∧
    C_step * (2 * section53CoarseFluctuationWeightSumConstant hP4) ≤
      C_delta ∧
    C_step * C_sqrt * Real.sqrt (delta_sc / 2)⁻¹ ≤ C_delta ∧
    (2 : ℝ) ≤ C_sqrt ^ 2 ∧
    (let β := section53CoarseFluctuationBeta hP4
     let K :=
       Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst
        d
     2 * (1 + (2 : ℝ) ^ d) ≤ C_step ∧
     C_lin ≤ C_step ∧
     C_lin * 16 * (C_high * β⁻¹) + C_lin * 16 * K ^ 2 ≤ C_step ∧
     C_lin * 16 * K ^ 2 * (5 * β⁻¹) ≤ C_step ∧
     C_norm + C_lin * 16 * K ^ 2 + C_lin * 16 * K ^ 2 ≤ C_step) := by
  let C_step : ℝ := finalAssemblySourceStepBound hP4 C_lin C_high
  let C_norm : ℝ := 1
  let C_S : ℝ := C_delta / 2
  let C_bad : ℝ := C_delta / 2
  let C_fluct : ℝ := finalAssemblyFluctuationBound hP4 delta_sc
  let C_sqrt : ℝ := 2
  have hC_step_one : (1 : ℝ) ≤ C_step := by
    simp [C_step, finalAssemblySourceStepBound]
  have hC_step_pos : 0 < C_step := by
    linarith
  have hC_step_nonneg : 0 ≤ C_step := le_of_lt hC_step_pos
  have hC_norm_pos : 0 < C_norm := by
    norm_num [C_norm]
  have hC_sqrt_nonneg : 0 ≤ C_sqrt := by
    norm_num [C_sqrt]
  have hC_S_le : C_S ≤ C_delta := by
    dsimp [C_S]
    linarith
  have hC_bad_le : C_bad ≤ C_delta := by
    dsimp [C_bad]
    linarith
  have hC_split : C_S + C_bad ≤ C_delta := by
    dsimp [C_S, C_bad]
    linarith
  have hbad_absorb : 6 * C_step ≤ C_bad := by
    have hbad_budget' : 12 * C_step ≤ C_delta := by
      simpa [C_step] using hbad_budget
    dsimp [C_bad]
    linarith
  have hmemory : 6 * C_step ≤ C_memory := by
    simpa [C_step] using hmemory_budget
  have hfluct_threshold :
      2 * (1 + (delta_sc / 2)⁻¹) ^ 2 ≤ C_fluct := by
    simp [C_fluct, finalAssemblyFluctuationBound]
  have hfluct_weight :
      2 * section53CoarseFluctuationWeightSumConstant hP4 ≤ C_fluct := by
    simp [C_fluct, finalAssemblyFluctuationBound]
  have hstep_fluct_half : C_step * C_fluct ≤ C_delta / 2 := by
    have hfluct_budget' : 2 * (C_step * C_fluct) ≤ C_delta := by
      simpa [C_step, C_fluct] using hfluct_budget
    linarith
  have hstep_fluct_budget : C_step * C_fluct ≤ C_S := by
    dsimp [C_S]
    exact hstep_fluct_half
  have hresponse :
      C_step * (1 + C_resp) * ((1 + (delta_sc / 2)⁻¹) ^ 2) ≤
        C_delta := by
    simpa [C_step] using hresponse_budget
  have hbad_threshold : 3 * C_step * (1 + (delta_sc / 2)⁻¹) ≤ C_bad := by
    have hbad_threshold_budget' :
        6 * C_step * (1 + (delta_sc / 2)⁻¹) ≤ C_delta := by
      simpa [C_step] using hbad_threshold_budget
    dsimp [C_bad]
    linarith
  have hstep_fluct_delta : C_step * C_fluct ≤ C_delta := by
    exact hstep_fluct_half.trans (by linarith)
  have hweight_budget :
      C_step * (2 * section53CoarseFluctuationWeightSumConstant hP4) ≤
        C_delta := by
    have hmul :
        C_step * (2 * section53CoarseFluctuationWeightSumConstant hP4) ≤
          C_step * C_fluct :=
      mul_le_mul_of_nonneg_left hfluct_weight hC_step_nonneg
    exact hmul.trans hstep_fluct_delta
  have hsqrt :
      C_step * C_sqrt * Real.sqrt (delta_sc / 2)⁻¹ ≤ C_delta := by
    simpa [C_step, C_sqrt, mul_assoc] using hsqrt_budget
  have hC_sqrt_sq : (2 : ℝ) ≤ C_sqrt ^ 2 := by
    norm_num [C_sqrt]
  have hfirst_uniform : 2 * (1 + (2 : ℝ) ^ d) ≤ C_step := by
    simp [C_step, finalAssemblySourceStepBound]
  have hlin : C_lin ≤ C_step := by
    simp [C_step, finalAssemblySourceStepBound]
  have hhigh :
      (let β := section53CoarseFluctuationBeta hP4
       let K :=
         Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst
          d
       C_lin * 16 * (C_high * β⁻¹) + C_lin * 16 * K ^ 2 ≤ C_step) := by
    simp [C_step, finalAssemblySourceStepBound]
  have htau :
      (let β := section53CoarseFluctuationBeta hP4
       let K :=
         Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst
          d
       C_lin * 16 * K ^ 2 * (5 * β⁻¹) ≤ C_step) := by
    simp [C_step, finalAssemblySourceStepBound]
  have hlocal :
      (let K :=
         Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst
          d
       C_norm + C_lin * 16 * K ^ 2 + C_lin * 16 * K ^ 2 ≤ C_step) := by
    simp [C_step, C_norm, finalAssemblySourceStepBound]
  exact
    ⟨hC_step_pos, hC_norm_pos, hC_sqrt_nonneg, hC_S_le, hC_bad_le,
      hC_split, hbad_absorb, hmemory, hfluct_threshold, hfluct_weight,
      hstep_fluct_budget, hresponse, hbad_threshold, hweight_budget, hsqrt,
      hC_sqrt_sq, hfirst_uniform, hlin, hhigh, htau, hlocal⟩

end Homogenization.HighContrast.EntryScale
