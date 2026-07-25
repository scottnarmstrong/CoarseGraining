import Mathlib.Tactic.Linarith
import Homogenization.HighContrast.EntryScale.MaximalResponse
import Homogenization.HighContrast.EntryScale.Memory.P1

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open scoped Matrix.Norms.Elementwise


/-!
# No-drop centered-response estimate

Planned home for Proposition `p.nodrop.CR`, after the maximal-response,
high-moment, deterministic algebra, and memory phases are available.
-/


namespace Homogenization.HighContrast.EntryScale

/-- Right-hand side of the no-drop centered-response estimate
`e.nodrop.CR.memory`. -/
noncomputable def noDropResponseRHS
    (C_delta C_memory eps rhoSqrt rho etaS etaSt rhoSq decay F_i memoryTerm : ℝ) :
    ℝ :=
  C_delta *
      (rhoSqrt + eps + eps⁻¹ * (etaS + etaSt + rho + rhoSq) +
        eps⁻¹ * decay) * F_i +
    C_memory * eps⁻¹ * memoryTerm

/-- **Layer B: linear-memory response RHS.**

Right-hand side of the no-drop centered-response estimate carrying a *second*,
`H`-linear memory slot `+ C_edgeMem·eps⁻¹·linTerm` alongside the existing
quadratic drift slot `C_memory·eps⁻¹·quadTerm`.  This is
`noDropResponseRHS … quadTerm` plus the extra linear term. -/
noncomputable def noDropResponseRHSLinear
    (C_delta C_memory C_edgeMem eps rhoSqrt rho etaS etaSt rhoSq decay F_i
      quadTerm linTerm : ℝ) :
    ℝ :=
  noDropResponseRHS C_delta C_memory eps rhoSqrt rho etaS etaSt rhoSq decay F_i
      quadTerm +
    C_edgeMem * eps⁻¹ * linTerm

/-- **Layer B: linear-memory RHS unfolds to the base RHS plus a linear slot.** -/
theorem noDropResponseRHSLinear_eq
    (C_delta C_memory C_edgeMem eps rhoSqrt rho etaS etaSt rhoSq decay F_i
      quadTerm linTerm : ℝ) :
    noDropResponseRHSLinear C_delta C_memory C_edgeMem eps rhoSqrt rho etaS etaSt
        rhoSq decay F_i quadTerm linTerm =
      C_delta *
          (rhoSqrt + eps + eps⁻¹ * (etaS + etaSt + rho + rhoSq) +
            eps⁻¹ * decay) * F_i +
        C_memory * eps⁻¹ * quadTerm +
        C_edgeMem * eps⁻¹ * linTerm := by
  rw [noDropResponseRHSLinear, noDropResponseRHS]

/-- **Layer B: linearization of the linear-memory RHS.**

After the small parameters are chosen, the linear-memory no-drop RHS is bounded
by a small multiple `coeff` of `F_i` plus the quadratic memory term and the
linear (edge) memory term with their own coefficients. -/
theorem noDropResponseRHSLinear_le_linear_memory
    {C_delta C_memory C_edgeMem eps rhoSqrt rho etaS etaSt rhoSq decay F_i
      quadTerm linTerm coeff memoryCoeff edgeMemoryCoeff : ℝ}
    (hF_nonneg : 0 ≤ F_i)
    (hquad_nonneg : 0 ≤ quadTerm)
    (hlin_nonneg : 0 ≤ linTerm)
    (hcoeff :
      C_delta *
        (rhoSqrt + eps + eps⁻¹ * (etaS + etaSt + rho + rhoSq) +
          eps⁻¹ * decay) ≤ coeff)
    (hmemoryCoeff : C_memory * eps⁻¹ ≤ memoryCoeff)
    (hedgeMemoryCoeff : C_edgeMem * eps⁻¹ ≤ edgeMemoryCoeff) :
    noDropResponseRHSLinear C_delta C_memory C_edgeMem eps rhoSqrt rho etaS etaSt
        rhoSq decay F_i quadTerm linTerm ≤
      coeff * F_i + memoryCoeff * quadTerm + edgeMemoryCoeff * linTerm := by
  rw [noDropResponseRHSLinear_eq]
  have hbase :
      C_delta *
          (rhoSqrt + eps + eps⁻¹ * (etaS + etaSt + rho + rhoSq) +
            eps⁻¹ * decay) * F_i +
        C_memory * eps⁻¹ * quadTerm ≤
      coeff * F_i + memoryCoeff * quadTerm :=
    add_le_add
      (mul_le_mul_of_nonneg_right hcoeff hF_nonneg)
      (mul_le_mul_of_nonneg_right hmemoryCoeff hquad_nonneg)
  have hlin :
      C_edgeMem * eps⁻¹ * linTerm ≤ edgeMemoryCoeff * linTerm :=
    mul_le_mul_of_nonneg_right hedgeMemoryCoeff hlin_nonneg
  linarith

/-- **Layer B: response bound in linear-memory form.**

A centered response controlled by the linear-memory no-drop RHS is bounded by
the linear-memory form `coeff·F + memoryCoeff·quadTerm + edgeMemoryCoeff·linTerm`. -/
theorem response_le_linear_memory_of_noDropResponseRHSLinear
    {response C_delta C_memory C_edgeMem eps rhoSqrt rho etaS etaSt rhoSq decay
      F_i quadTerm linTerm coeff memoryCoeff edgeMemoryCoeff : ℝ}
    (hresponse :
      response ≤
        noDropResponseRHSLinear C_delta C_memory C_edgeMem eps rhoSqrt rho etaS
          etaSt rhoSq decay F_i quadTerm linTerm)
    (hF_nonneg : 0 ≤ F_i)
    (hquad_nonneg : 0 ≤ quadTerm)
    (hlin_nonneg : 0 ≤ linTerm)
    (hcoeff :
      C_delta *
        (rhoSqrt + eps + eps⁻¹ * (etaS + etaSt + rho + rhoSq) +
          eps⁻¹ * decay) ≤ coeff)
    (hmemoryCoeff : C_memory * eps⁻¹ ≤ memoryCoeff)
    (hedgeMemoryCoeff : C_edgeMem * eps⁻¹ ≤ edgeMemoryCoeff) :
    response ≤
      coeff * F_i + memoryCoeff * quadTerm + edgeMemoryCoeff * linTerm :=
  hresponse.trans
    (noDropResponseRHSLinear_le_linear_memory hF_nonneg hquad_nonneg hlin_nonneg
      hcoeff hmemoryCoeff hedgeMemoryCoeff)

/-- **Layer B: split-raw combiner with a second, linear (edge) memory slot.**

Source labels `p.HC.CR`, `p.nodrop.CR`, `e.det.memory`, and Layer A's
`e.edge.memory.residual`.  Identical to
`splitRawResponseRHS_le_noDropResponseRHS_of_split_rhoSq_budgets_lower_memory`,
but the lower-edge hypothesis `h_lower` now carries **two** memory terms — the
existing quadratic drift term `C_memory·eps⁻¹·memoryTerm` and the new
`H`-linear edge-memory term `C_edgeMem·eps⁻¹·linTerm` (Layer A's residual).
The produced value is `noDropResponseRHSLinear`, i.e. the base no-drop RHS with
the extra `+ C_edgeMem·eps⁻¹·linTerm` slot. -/
theorem splitRawResponseRHS_le_noDropResponseRHSLinear_of_split_rhoSq_budgets_lower_memory_linear
    {C C_raw_bad C_delta C_memory C_edgeMem C_S C_bad eps sqrtTerm F_i
      weakNormGood T_m S_term P_tau_sum lowerEdge badMaximal rhoSqrt rho etaS
      etaSt rhoSq decay memoryTerm linTerm : ℝ}
    (hC_nonneg : 0 ≤ C)
    (heps_inv_nonneg : 0 ≤ eps⁻¹)
    (hF_nonneg : 0 ≤ F_i)
    (hetaS_nonneg : 0 ≤ etaS)
    (hetaSt_nonneg : 0 ≤ etaSt)
    (hrhoSq_nonneg : 0 ≤ rhoSq)
    (hlin_nonneg : 0 ≤ linTerm)
    (hedgeMem_nonneg : 0 ≤ C_edgeMem)
    (hC_S : C_S ≤ C_delta)
    (hC_bad : C_bad ≤ C_delta)
    (hC_rhoSq : C_S + C_bad ≤ C_delta)
    (hweak :
      weakNormGood ≤
        weakNormContribution T_m S_term P_tau_sum lowerEdge 0)
    (h_sqrt : C * sqrtTerm ≤ C_delta * rhoSqrt * F_i)
    (h_eps : C * eps * F_i ≤ C_delta * eps * F_i)
    (h_S :
      C * eps⁻¹ * T_m * S_term ≤
        C_S * eps⁻¹ * etaS * F_i +
          C_S * eps⁻¹ * rhoSq * F_i)
    (h_tau :
      C * eps⁻¹ * P_tau_sum ≤ C_delta * eps⁻¹ * rho * F_i)
    (h_lower :
      C * eps⁻¹ * lowerEdge ≤
        C_delta * eps⁻¹ * decay * F_i +
          C_memory * eps⁻¹ * memoryTerm +
          C_edgeMem * eps⁻¹ * linTerm)
    (h_bad :
      C_raw_bad * eps⁻¹ * (T_m * badMaximal) ≤
        C_bad * eps⁻¹ * (etaSt + rhoSq) * F_i) :
    C * sqrtTerm + C * eps * F_i +
        C * eps⁻¹ * weakNormGood +
          C_raw_bad * eps⁻¹ * (T_m * badMaximal) ≤
      noDropResponseRHSLinear C_delta C_memory C_edgeMem eps rhoSqrt rho etaS
        etaSt rhoSq decay F_i memoryTerm linTerm := by
  have hfactor_nonneg : 0 ≤ C * eps⁻¹ :=
    mul_nonneg hC_nonneg heps_inv_nonneg
  have hedge_term_nonneg : 0 ≤ C_edgeMem * eps⁻¹ * linTerm :=
    mul_nonneg (mul_nonneg hedgeMem_nonneg heps_inv_nonneg) hlin_nonneg
  have hweak_scaled :
      C * eps⁻¹ * weakNormGood ≤
        C * eps⁻¹ *
          weakNormContribution T_m S_term P_tau_sum lowerEdge 0 :=
    mul_le_mul_of_nonneg_left hweak hfactor_nonneg
  have htail_etaS_nonneg : 0 ≤ eps⁻¹ * etaS * F_i :=
    mul_nonneg (mul_nonneg heps_inv_nonneg hetaS_nonneg) hF_nonneg
  have htail_etaSt_nonneg : 0 ≤ eps⁻¹ * etaSt * F_i :=
    mul_nonneg (mul_nonneg heps_inv_nonneg hetaSt_nonneg) hF_nonneg
  have htail_rhoSq_nonneg : 0 ≤ eps⁻¹ * rhoSq * F_i :=
    mul_nonneg (mul_nonneg heps_inv_nonneg hrhoSq_nonneg) hF_nonneg
  have hS_eta :
      C_S * eps⁻¹ * etaS * F_i ≤
        C_delta * eps⁻¹ * etaS * F_i := by
    calc
      C_S * eps⁻¹ * etaS * F_i = C_S * (eps⁻¹ * etaS * F_i) := by ring
      _ ≤ C_delta * (eps⁻¹ * etaS * F_i) :=
          mul_le_mul_of_nonneg_right hC_S htail_etaS_nonneg
      _ = C_delta * eps⁻¹ * etaS * F_i := by ring
  have hbad_eta :
      C_bad * eps⁻¹ * etaSt * F_i ≤
        C_delta * eps⁻¹ * etaSt * F_i := by
    calc
      C_bad * eps⁻¹ * etaSt * F_i = C_bad * (eps⁻¹ * etaSt * F_i) := by ring
      _ ≤ C_delta * (eps⁻¹ * etaSt * F_i) :=
          mul_le_mul_of_nonneg_right hC_bad htail_etaSt_nonneg
      _ = C_delta * eps⁻¹ * etaSt * F_i := by ring
  have hrhoSq :
      C_S * eps⁻¹ * rhoSq * F_i +
          C_bad * eps⁻¹ * rhoSq * F_i ≤
        C_delta * eps⁻¹ * rhoSq * F_i := by
    calc
      C_S * eps⁻¹ * rhoSq * F_i +
          C_bad * eps⁻¹ * rhoSq * F_i =
        (C_S + C_bad) * (eps⁻¹ * rhoSq * F_i) := by ring
      _ ≤ C_delta * (eps⁻¹ * rhoSq * F_i) :=
          mul_le_mul_of_nonneg_right hC_rhoSq htail_rhoSq_nonneg
      _ = C_delta * eps⁻¹ * rhoSq * F_i := by ring
  rw [weakNormContribution] at hweak_scaled
  rw [noDropResponseRHSLinear, noDropResponseRHS]
  nlinarith

/--
Source labels `p.HC.CR`, `p.nodrop.CR`, `e.det.memory`, and Layer A's
`e.edge.memory.residual`: primal no-drop response assembly for the split
child-average raw computation when the lower-edge slot carries **both** the
deterministic memory payment and Layer A's `H`-linear edge-memory residual.
The produced value is `noDropResponseRHSLinear`. -/
theorem expectedCenteredResponseJAtScale_le_noDropResponseRHSLinear_of_split_raw_highContrast_lower_memory_linear
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    {k m : ℤ} (e : Homogenization.Vec d)
    {C C_raw_bad C_delta C_memory C_edgeMem C_S C_bad eps F_i weakNormGood T_m
      S_term P_tau_sum lowerEdge badMaximal rhoSqrt rho etaS etaSt rhoSq
      decay memoryTerm linTerm : ℝ}
    (hC_nonneg : 0 ≤ C)
    (heps_pos : 0 < eps)
    (hF_nonneg : 0 ≤ F_i)
    (hetaS_nonneg : 0 ≤ etaS)
    (hetaSt_nonneg : 0 ≤ etaSt)
    (hrhoSq_nonneg : 0 ≤ rhoSq)
    (hlin_nonneg : 0 ≤ linTerm)
    (hedgeMem_nonneg : 0 ≤ C_edgeMem)
    (hC_S : C_S ≤ C_delta)
    (hC_bad : C_bad ≤ C_delta)
    (hC_rhoSq : C_S + C_bad ≤ C_delta)
    (hraw :
      Homogenization.Book.Ch05.expectedCenteredResponseJAtScale hP hStruct m
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct m e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct m e) ≤
        C * centeredResponseSqrtTermAtScale hP hStruct k m e +
        C * eps * F_i + C * eps⁻¹ * weakNormGood +
          C_raw_bad * eps⁻¹ * (T_m * badMaximal))
    (hweak :
      weakNormGood ≤ weakNormContribution T_m S_term P_tau_sum lowerEdge 0)
    (h_sqrt :
      C * centeredResponseSqrtTermAtScale hP hStruct k m e ≤
        C_delta * rhoSqrt * F_i)
    (h_eps : C * eps * F_i ≤ C_delta * eps * F_i)
    (h_S :
      C * eps⁻¹ * T_m * S_term ≤
        C_S * eps⁻¹ * etaS * F_i +
          C_S * eps⁻¹ * rhoSq * F_i)
    (h_tau :
      C * eps⁻¹ * P_tau_sum ≤ C_delta * eps⁻¹ * rho * F_i)
    (h_lower :
      C * eps⁻¹ * lowerEdge ≤
        C_delta * eps⁻¹ * decay * F_i +
          C_memory * eps⁻¹ * memoryTerm +
          C_edgeMem * eps⁻¹ * linTerm)
    (h_bad :
      C_raw_bad * eps⁻¹ * (T_m * badMaximal) ≤
        C_bad * eps⁻¹ * (etaSt + rhoSq) * F_i) :
    Homogenization.Book.Ch05.expectedCenteredResponseJAtScale hP hStruct m
        (Homogenization.Book.Ch05.specialPAtScale hP hStruct m e)
        (Homogenization.Book.Ch05.specialQAtScale hP hStruct m e) ≤
      noDropResponseRHSLinear C_delta C_memory C_edgeMem eps rhoSqrt rho etaS
        etaSt rhoSq decay F_i memoryTerm linTerm := by
  have hbudget :
      C * centeredResponseSqrtTermAtScale hP hStruct k m e +
          C * eps * F_i + C * eps⁻¹ * weakNormGood +
            C_raw_bad * eps⁻¹ * (T_m * badMaximal) ≤
        noDropResponseRHSLinear C_delta C_memory C_edgeMem eps rhoSqrt rho etaS
          etaSt rhoSq decay F_i memoryTerm linTerm :=
    splitRawResponseRHS_le_noDropResponseRHSLinear_of_split_rhoSq_budgets_lower_memory_linear
      (C_S := C_S) (C_bad := C_bad) hC_nonneg
      (inv_nonneg.mpr (le_of_lt heps_pos)) hF_nonneg hetaS_nonneg
      hetaSt_nonneg hrhoSq_nonneg hlin_nonneg hedgeMem_nonneg hC_S hC_bad
      hC_rhoSq hweak h_sqrt h_eps h_S h_tau h_lower h_bad
  exact hraw.trans hbudget

/--
Source labels `p.HC.CR`, `p.nodrop.CR`, `e.det.memory`, and Layer A's
`e.edge.memory.residual`: adjoint no-drop response assembly for the split
child-average raw computation when the lower-edge slot carries **both** the
deterministic memory payment and Layer A's `H`-linear edge-memory residual. -/
theorem expectedCenteredResponseJStarAtScale_le_noDropResponseRHSLinear_of_split_raw_highContrast_lower_memory_linear
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    {m : ℤ} (e : Homogenization.Vec d)
    {C C_raw_bad C_delta C_memory C_edgeMem C_S C_bad eps starSqrtTerm F_i
      weakNormGood T_m S_term P_tau_sum lowerEdge badMaximal rhoSqrt rho
      etaS etaSt rhoSq decay memoryTerm linTerm : ℝ}
    (hC_nonneg : 0 ≤ C)
    (heps_pos : 0 < eps)
    (hF_nonneg : 0 ≤ F_i)
    (hetaS_nonneg : 0 ≤ etaS)
    (hetaSt_nonneg : 0 ≤ etaSt)
    (hrhoSq_nonneg : 0 ≤ rhoSq)
    (hlin_nonneg : 0 ≤ linTerm)
    (hedgeMem_nonneg : 0 ≤ C_edgeMem)
    (hC_S : C_S ≤ C_delta)
    (hC_bad : C_bad ≤ C_delta)
    (hC_rhoSq : C_S + C_bad ≤ C_delta)
    (hraw :
      Homogenization.Book.Ch05.expectedCenteredResponseJStarAtScale hP hStruct m
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct m e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct m e) ≤
        C * starSqrtTerm + C * eps * F_i + C * eps⁻¹ * weakNormGood +
          C_raw_bad * eps⁻¹ * (T_m * badMaximal))
    (hweak :
      weakNormGood ≤ weakNormContribution T_m S_term P_tau_sum lowerEdge 0)
    (h_sqrt : C * starSqrtTerm ≤ C_delta * rhoSqrt * F_i)
    (h_eps : C * eps * F_i ≤ C_delta * eps * F_i)
    (h_S :
      C * eps⁻¹ * T_m * S_term ≤
        C_S * eps⁻¹ * etaS * F_i +
          C_S * eps⁻¹ * rhoSq * F_i)
    (h_tau :
      C * eps⁻¹ * P_tau_sum ≤ C_delta * eps⁻¹ * rho * F_i)
    (h_lower :
      C * eps⁻¹ * lowerEdge ≤
        C_delta * eps⁻¹ * decay * F_i +
          C_memory * eps⁻¹ * memoryTerm +
          C_edgeMem * eps⁻¹ * linTerm)
    (h_bad :
      C_raw_bad * eps⁻¹ * (T_m * badMaximal) ≤
        C_bad * eps⁻¹ * (etaSt + rhoSq) * F_i) :
    Homogenization.Book.Ch05.expectedCenteredResponseJStarAtScale hP hStruct m
        (Homogenization.Book.Ch05.specialPAtScale hP hStruct m e)
        (Homogenization.Book.Ch05.specialQAtScale hP hStruct m e) ≤
      noDropResponseRHSLinear C_delta C_memory C_edgeMem eps rhoSqrt rho etaS
        etaSt rhoSq decay F_i memoryTerm linTerm := by
  have hbudget :
      C * starSqrtTerm + C * eps * F_i + C * eps⁻¹ * weakNormGood +
          C_raw_bad * eps⁻¹ * (T_m * badMaximal) ≤
        noDropResponseRHSLinear C_delta C_memory C_edgeMem eps rhoSqrt rho etaS
          etaSt rhoSq decay F_i memoryTerm linTerm :=
    splitRawResponseRHS_le_noDropResponseRHSLinear_of_split_rhoSq_budgets_lower_memory_linear
      (C_S := C_S) (C_bad := C_bad) hC_nonneg
      (inv_nonneg.mpr (le_of_lt heps_pos)) hF_nonneg hetaS_nonneg
      hetaSt_nonneg hrhoSq_nonneg hlin_nonneg hedgeMem_nonneg hC_S hC_bad
      hC_rhoSq hweak h_sqrt h_eps h_S h_tau h_lower h_bad
  exact hraw.trans hbudget

/--
Source labels `l.union.bound`, `M_m^st`, and `M_m^{<N}`: memory-grid
specialization of the final stochastic maximal union bound.  The buffer
condition is kept explicit, matching the manuscript choice of `N_*` large
enough after the high-moment and subthreshold constants are fixed.
-/
theorem exists_bufferExponent_lintegral_terminalCoarseBlockStochasticMax_add_subthresholdMax_le_memoryGrid_of_Nstar
    {d : ℕ} [NeZero d] {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (sub : SubthresholdPolynomialMomentParameters)
    {etaSt : ℝ} (hetaSt_pos : 0 < etaSt) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {P : Homogenization.Book.Ch04.CoeffLaw d}
        (hP : Homogenization.Book.Ch04.LawCarrier P)
        (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
        {N Nstar L i : ℕ},
          N + Nat.ceil
              (B * Real.logb 3
                (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) ≤
            memoryGridScale Nstar L i →
          ∀ (M_sub : ℕ → Homogenization.RegCoeffField d → ℝ),
            HighCenteredMomentEstimate hm P N
              (intermediateCoarseBlockDeviation hP hStruct
                (fun x : Homogenization.RegCoeffField d => x)) →
            SubthresholdPolynomialMomentEstimate hc sub P
              (Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)
              N M_sub →
              ∫⁻ ω,
                  ‖terminalCoarseBlockStochasticMax hP hStruct hc N
                      (memoryGridScale Nstar L i)
                      (Homogenization.originCube d
                        ((memoryGridScale Nstar L i : ℕ) : ℤ))
                      (fun x : Homogenization.RegCoeffField d => x) ω‖ₑ ^
                    (2 : ℝ) ∂P +
                ∫⁻ ω, ‖M_sub (memoryGridScale Nstar L i) ω‖ₑ ^
                  (2 : ℝ) ∂P ≤ ENNReal.ofReal etaSt := by
  obtain ⟨B, hB_one, hB⟩ :=
    exists_bufferExponent_lintegral_enorm_rpow_two_terminalCoarseBlockStochasticMax_add_subthresholdMax_le_of_Nstar
      hm sub hetaSt_pos
  refine ⟨B, hB_one, ?_⟩
  intro P hP hStruct hP4 N Nstar L i hbuffer M_sub hHM hsub
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  exact
    hB hP hStruct hP4 P
      (Homogenization.originCube d ((memoryGridScale Nstar L i : ℕ) : ℤ))
      (N := N) (m := memoryGridScale Nstar L i)
      (by rfl) hbuffer
      (fun x : Homogenization.RegCoeffField d => x) M_sub
      (aestronglyMeasurable_terminalCoarseBlockStochasticMax_origin
        hP hStruct hP4 hc N (memoryGridScale Nstar L i))
      hHM hsub

/--
Source labels `p.nodrop.CR` and `e.S.term.bound`: scalar prefactor insertion
for a terminal fluctuation estimate of the form
`T_m S_{k,m} <= C_S (eta_S + rho^2) F_i`.
-/
theorem terminalFluctuation_prefactor_le_eta_add_rhoSq_budget
    {C C_budget C_S eps T_m S_term etaS rhoSq F_i : ℝ}
    (heps_inv_nonneg : 0 ≤ eps⁻¹)
    (hC_nonneg : 0 ≤ C)
    (heta_nonneg : 0 ≤ etaS)
    (hrhoSq_nonneg : 0 ≤ rhoSq)
    (hF_nonneg : 0 ≤ F_i)
    (hS : T_m * S_term ≤ C_S * (etaS + rhoSq) * F_i)
    (hC_budget : C * C_S ≤ C_budget) :
    C * eps⁻¹ * T_m * S_term ≤
      C_budget * eps⁻¹ * etaS * F_i +
        C_budget * eps⁻¹ * rhoSq * F_i := by
  have hfactor_nonneg : 0 ≤ C * eps⁻¹ :=
    mul_nonneg hC_nonneg heps_inv_nonneg
  have hscaled :
      C * eps⁻¹ * (T_m * S_term) ≤
        C * eps⁻¹ * (C_S * (etaS + rhoSq) * F_i) :=
    mul_le_mul_of_nonneg_left hS hfactor_nonneg
  have hcoeff :
      C * eps⁻¹ * C_S ≤ C_budget * eps⁻¹ := by
    calc
      C * eps⁻¹ * C_S = (C * C_S) * eps⁻¹ := by ring
      _ ≤ C_budget * eps⁻¹ :=
          mul_le_mul_of_nonneg_right hC_budget heps_inv_nonneg
  have hterm_nonneg : 0 ≤ (etaS + rhoSq) * F_i :=
    mul_nonneg (add_nonneg heta_nonneg hrhoSq_nonneg) hF_nonneg
  have hbudget :
      C * eps⁻¹ * (C_S * (etaS + rhoSq) * F_i) ≤
        C_budget * eps⁻¹ * ((etaS + rhoSq) * F_i) := by
    calc
      C * eps⁻¹ * (C_S * (etaS + rhoSq) * F_i)
          = (C * eps⁻¹ * C_S) * ((etaS + rhoSq) * F_i) := by ring
      _ ≤ (C_budget * eps⁻¹) * ((etaS + rhoSq) * F_i) :=
          mul_le_mul_of_nonneg_right hcoeff hterm_nonneg
      _ = C_budget * eps⁻¹ * ((etaS + rhoSq) * F_i) := by ring
  calc
    C * eps⁻¹ * T_m * S_term
        = C * eps⁻¹ * (T_m * S_term) := by ring
    _ ≤ C * eps⁻¹ * (C_S * (etaS + rhoSq) * F_i) := hscaled
    _ ≤ C_budget * eps⁻¹ * ((etaS + rhoSq) * F_i) := hbudget
    _ = C_budget * eps⁻¹ * etaS * F_i +
        C_budget * eps⁻¹ * rhoSq * F_i := by ring

/--
Source labels `p.nodrop.CR` and `e.sqrt.tau.absorb`: scalar prefactor
insertion for the square-root additivity term after the source estimate
`sqrtTerm <= C_sqrt rho^{1/2} delta^{-1/2} F_i`.
-/
theorem sqrtTerm_prefactor_le_noDrop_rhoSqrt_budget
    {C C_delta C_sqrt rho delta F_i sqrtTerm : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hF_nonneg : 0 ≤ F_i)
    (hsqrt :
      sqrtTerm ≤ C_sqrt * Real.sqrt rho * Real.sqrt delta⁻¹ * F_i)
    (hbudget : C * C_sqrt * Real.sqrt delta⁻¹ ≤ C_delta) :
    C * sqrtTerm ≤ C_delta * Real.sqrt rho * F_i := by
  have hrhoF_nonneg : 0 ≤ Real.sqrt rho * F_i :=
    mul_nonneg (Real.sqrt_nonneg rho) hF_nonneg
  have hscaled :
      C * sqrtTerm ≤ C * (C_sqrt * Real.sqrt rho * Real.sqrt delta⁻¹ * F_i) :=
    mul_le_mul_of_nonneg_left hsqrt hC_nonneg
  have hbudget_scaled :
      (C * C_sqrt * Real.sqrt delta⁻¹) * (Real.sqrt rho * F_i) ≤
        C_delta * (Real.sqrt rho * F_i) :=
    mul_le_mul_of_nonneg_right hbudget hrhoF_nonneg
  calc
    C * sqrtTerm
        ≤ C * (C_sqrt * Real.sqrt rho * Real.sqrt delta⁻¹ * F_i) := hscaled
    _ = (C * C_sqrt * Real.sqrt delta⁻¹) * (Real.sqrt rho * F_i) := by ring
    _ ≤ C_delta * (Real.sqrt rho * F_i) := hbudget_scaled
    _ = C_delta * Real.sqrt rho * F_i := by ring

/-- Expected lower-scale response nonnegativity for the square-root absorber. -/
theorem expectedResponseJCubeSet_nonneg
    {d : ℕ} {P : Homogenization.Book.Ch04.CoeffLaw d}
    (Q : Homogenization.TriadicCube d) (p q : Homogenization.Vec d) :
    0 ≤ Homogenization.Book.Ch04.expectedResponseJCubeSet P Q p q := by
  dsimp [Homogenization.Book.Ch04.expectedResponseJCubeSet]
  exact
    MeasureTheory.integral_nonneg
      (fun a => Homogenization.Book.Ch04.responseJObservableCubeSet_nonneg Q p q a)

/--
Tau nonnegativity for the special terminal pair, derived from LIH integrability
under the quantitative ellipticity package.
-/
theorem tauAtScale_special_nonneg_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k ≤ m) (e : Homogenization.Vec d) :
    0 ≤
      Homogenization.Book.Ch05.tauAtScale P (m : ℤ) (k : ℤ)
        (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
        (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) := by
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hkm
  have hBlockM :
      MeasureTheory.Integrable
        (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube
          (Homogenization.originCube d (m : ℤ))) P :=
    Homogenization.Book.Ch05.Section52.originBlockIntegrableAtScale_from_P4
      hP hStruct hP4 m
  have hBlockK :
      MeasureTheory.Integrable
        (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube
          (Homogenization.originCube d (k : ℤ))) P :=
    Homogenization.Book.Ch05.Section52.originBlockIntegrableAtScale_from_P4
      hP hStruct hP4 k
  have hDescBlock :
      ∀ R,
        R ∈ Homogenization.descendantsAtScale
            (Homogenization.originCube d (m : ℤ)) (k : ℤ) →
          MeasureTheory.Integrable
            (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube R) P := by
    intro R hR
    exact
      hP.integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
        hStruct.stationary hk_nonneg hkm_int hR hBlockK
  exact
    Homogenization.Book.Ch05.Section52.tauAtScale_nonneg_of_integrable_coarseFullBlockMatrixAtCube
      hP hStruct.stationary hk_nonneg hkm_int
      (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
      (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e)
      hBlockM hDescBlock

/--
Source labels `p.nodrop.CR` and `e.sqrt.tau.absorb`: concrete square-root
additivity contribution for the special terminal pair in `p.HC.CR`.
-/
theorem centeredResponseSqrtTermAtScale_prefactor_le_noDrop_rhoSqrt_budget
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (k m : ℤ) (e : Homogenization.Vec d)
    {C C_delta C_sqrt rho delta F_i : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hC_sqrt_nonneg : 0 ≤ C_sqrt)
    (hdelta_pos : 0 < delta)
    (hF_nonneg : 0 ≤ F_i)
    (htau_nonneg :
      0 ≤
        Homogenization.Book.Ch05.tauAtScale P m k
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct m e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct m e))
    (hresponse_nonneg :
      0 ≤
        Homogenization.Book.Ch04.expectedResponseJCubeSet P
          (Homogenization.originCube d k)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct m e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct m e))
    (hprod :
      Homogenization.Book.Ch05.tauAtScale P m k
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct m e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct m e) *
        Homogenization.Book.Ch04.expectedResponseJCubeSet P
          (Homogenization.originCube d k)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct m e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct m e) ≤
        (C_sqrt * Real.sqrt rho * Real.sqrt delta⁻¹ * F_i) ^ 2)
    (hbudget : C * C_sqrt * Real.sqrt delta⁻¹ ≤ C_delta) :
    C * centeredResponseSqrtTermAtScale hP hStruct k m e ≤
      C_delta * Real.sqrt rho * F_i := by
  have hsqrt :
      centeredResponseSqrtTermAtScale hP hStruct k m e ≤
        C_sqrt * Real.sqrt rho * Real.sqrt delta⁻¹ * F_i := by
    dsimp [centeredResponseSqrtTermAtScale]
    exact
      sqrt_tau_response_absorb_delta
        (tau :=
          Homogenization.Book.Ch05.tauAtScale P m k
            (Homogenization.Book.Ch05.specialPAtScale hP hStruct m e)
            (Homogenization.Book.Ch05.specialQAtScale hP hStruct m e))
        (response :=
          Homogenization.Book.Ch04.expectedResponseJCubeSet P
            (Homogenization.originCube d k)
            (Homogenization.Book.Ch05.specialPAtScale hP hStruct m e)
            (Homogenization.Book.Ch05.specialQAtScale hP hStruct m e))
        (C := C_sqrt) (rho := rho) (delta := delta) (F_m := F_i)
        htau_nonneg hresponse_nonneg hC_sqrt_nonneg hdelta_pos hF_nonneg hprod
  exact
    sqrtTerm_prefactor_le_noDrop_rhoSqrt_budget
      hC_nonneg hF_nonneg hsqrt hbudget

/--
Source labels `p.nodrop.CR` and `e.sqrt.tau.absorb`: adjoint square-root
additivity contribution for the special terminal pair.  The lower-scale
annealed `J^*` response is represented by LIH through adjoint invariance using
the same scalar expectation as the primal term.
-/
theorem centeredResponseStarSqrtTermAtScale_prefactor_le_noDrop_rhoSqrt_budget
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (k m : ℤ) (e : Homogenization.Vec d)
    {C C_delta C_sqrt rho delta F_i : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hC_sqrt_nonneg : 0 ≤ C_sqrt)
    (hdelta_pos : 0 < delta)
    (hF_nonneg : 0 ≤ F_i)
    (htau_nonneg :
      0 ≤
        Homogenization.Book.Ch05.tauAtScale P m k
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct m e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct m e))
    (hresponse_nonneg :
      0 ≤
        Homogenization.Book.Ch04.expectedResponseJCubeSet P
          (Homogenization.originCube d k)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct m e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct m e))
    (hprod :
      Homogenization.Book.Ch05.tauAtScale P m k
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct m e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct m e) *
        Homogenization.Book.Ch04.expectedResponseJCubeSet P
          (Homogenization.originCube d k)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct m e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct m e) ≤
        (C_sqrt * Real.sqrt rho * Real.sqrt delta⁻¹ * F_i) ^ 2)
    (hbudget : C * C_sqrt * Real.sqrt delta⁻¹ ≤ C_delta) :
    C * centeredResponseStarSqrtTermAtScale hP hStruct k m e ≤
      C_delta * Real.sqrt rho * F_i := by
  simpa [centeredResponseStarSqrtTermAtScale, centeredResponseSqrtTermAtScale] using
    centeredResponseSqrtTermAtScale_prefactor_le_noDrop_rhoSqrt_budget
      hP hStruct k m e hC_nonneg hC_sqrt_nonneg hdelta_pos hF_nonneg
      htau_nonneg hresponse_nonneg hprod hbudget

/--
Source labels `p.nodrop.CR` and `e.tau.sum.absorb`: scalar prefactor
insertion after the additivity-defect sum is bounded by `C_tau rho F_i`.
-/
theorem tauSum_prefactor_le_noDrop_rho_budget
    {C C_delta C_tau eps P_tau_sum rho F_i : ℝ}
    (heps_inv_nonneg : 0 ≤ eps⁻¹)
    (hC_nonneg : 0 ≤ C)
    (hrhoF_nonneg : 0 ≤ rho * F_i)
    (htau : P_tau_sum ≤ C_tau * (rho * F_i))
    (hbudget : C * C_tau ≤ C_delta) :
    C * eps⁻¹ * P_tau_sum ≤ C_delta * eps⁻¹ * rho * F_i := by
  have hfactor_nonneg : 0 ≤ C * eps⁻¹ :=
    mul_nonneg hC_nonneg heps_inv_nonneg
  have hscaled :
      C * eps⁻¹ * P_tau_sum ≤ C * eps⁻¹ * (C_tau * (rho * F_i)) :=
    mul_le_mul_of_nonneg_left htau hfactor_nonneg
  have htail_nonneg : 0 ≤ eps⁻¹ * (rho * F_i) :=
    mul_nonneg heps_inv_nonneg hrhoF_nonneg
  have hbudget_scaled :
      (C * C_tau) * (eps⁻¹ * (rho * F_i)) ≤
        C_delta * (eps⁻¹ * (rho * F_i)) :=
    mul_le_mul_of_nonneg_right hbudget htail_nonneg
  calc
    C * eps⁻¹ * P_tau_sum
        ≤ C * eps⁻¹ * (C_tau * (rho * F_i)) := hscaled
    _ = (C * C_tau) * (eps⁻¹ * (rho * F_i)) := by ring
    _ ≤ C_delta * (eps⁻¹ * (rho * F_i)) := hbudget_scaled
    _ = C_delta * eps⁻¹ * rho * F_i := by ring

/--
Source labels `p.nodrop.CR` and `e.tau.sum.absorb`: concrete finite weighted
additivity-defect contribution in the form needed by the no-drop response
estimate.
-/
theorem weightedTauSum_prefactor_le_noDrop_rho_budget
    {ι : Type*} (s : Finset ι)
    {w tau drop : ι → ℝ} {C C_delta eps r_m P_km rho F_i Cw : ℝ}
    (heps_pos : 0 < eps)
    (hC_nonneg : 0 ≤ C)
    (hP_le : P_km ≤ 4 * r_m)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (htau_nonneg : ∀ i ∈ s, 0 ≤ tau i)
    (hrt : ∀ i ∈ s, r_m * tau i ≤ (1 / 2 : ℝ) * drop i)
    (hdrop : ∀ i ∈ s, drop i ≤ rho * F_i)
    (hCw : ∑ i ∈ s, w i ≤ Cw)
    (hrhoF_nonneg : 0 ≤ rho * F_i)
    (hbudget : C * (2 * Cw) ≤ C_delta) :
    C * eps⁻¹ * (P_km * (∑ i ∈ s, w i * tau i)) ≤
      C_delta * eps⁻¹ * rho * F_i := by
  have htau_sum :
      P_km * (∑ i ∈ s, w i * tau i) ≤ 2 * Cw * (rho * F_i) :=
    weighted_terminal_tau_absorb s hP_le hw_nonneg htau_nonneg hrt hdrop hCw
      hrhoF_nonneg
  exact
    tauSum_prefactor_le_noDrop_rho_budget
      (C := C) (C_delta := C_delta) (C_tau := 2 * Cw) (eps := eps)
      (P_tau_sum := P_km * (∑ i ∈ s, w i * tau i)) (rho := rho)
      (F_i := F_i)
      (inv_nonneg.mpr (le_of_lt heps_pos)) hC_nonneg hrhoF_nonneg htau_sum
      hbudget

/-- **Layer B linear channel: paired no-bad memory-grid response with the
edge-memory residual slot.**

Source labels `p.nodrop.CR`, `e.det.memory`, and Layer A's
`e.edge.memory.residual`.  Identical to
`expectedCenteredResponsesAtMemoryGrid_le_noDropResponseRHS_of_split_raw_highContrast_lower_memory_no_bad`,
but the lower-edge slots `h_lower`/`h_lowerStar` carry the additional
`H`-linear edge-memory residual `C_edgeMem·eps⁻¹·linTerm`, and the produced
value is `noDropResponseRHSLinear`. -/
theorem expectedCenteredResponsesAtMemoryGrid_le_noDropResponseRHSLinear_of_split_raw_highContrast_lower_memory_no_bad_linear
    {d : ℕ} [NeZero d] (hc : HighContrastExponents d) {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {N Nstar L i : ℕ} (e : Homogenization.Vec d)
    {rho C C_delta C_memory C_edgeMem C_S eps etaS etaSt decay starSqrtTerm
      weakNormGood weakNormGoodStar S_term P_tau_sum lowerEdge lowerEdgeStar
      linTerm : ℝ}
    (hC_nonneg : 0 ≤ C)
    (heps_pos : 0 < eps)
    (hetaS_nonneg : 0 ≤ etaS)
    (hetaSt_nonneg : 0 ≤ etaSt)
    (hlin_nonneg : 0 ≤ linTerm)
    (hedgeMem_nonneg : 0 ≤ C_edgeMem)
    (hC_delta_nonneg : 0 ≤ C_delta)
    (hC_S : C_S ≤ C_delta)
    (hraw :
      let m : ℕ := memoryGridScale Nstar L i
      let k : ℕ := memoryGridScale Nstar L (i - 1)
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      Homogenization.Book.Ch05.expectedCenteredResponseJAtScale hP hStruct
          (m : ℤ)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) ≤
        C * centeredResponseSqrtTermAtScale hP hStruct (k : ℤ) (m : ℤ) e +
        C * eps * F_i + C * eps⁻¹ * weakNormGood)
    (hrawStar :
      let m : ℕ := memoryGridScale Nstar L i
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      Homogenization.Book.Ch05.expectedCenteredResponseJStarAtScale hP hStruct
          (m : ℤ)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) ≤
        C * starSqrtTerm + C * eps * F_i + C * eps⁻¹ * weakNormGoodStar)
    (hweak :
      let m : ℕ := memoryGridScale Nstar L i
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      weakNormGood ≤
        weakNormContribution (1 + F_i) S_term P_tau_sum lowerEdge 0)
    (hweakStar :
      let m : ℕ := memoryGridScale Nstar L i
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      weakNormGoodStar ≤
        weakNormContribution (1 + F_i) S_term P_tau_sum lowerEdgeStar 0)
    (h_sqrt :
      let m : ℕ := memoryGridScale Nstar L i
      let k : ℕ := memoryGridScale Nstar L (i - 1)
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      C * centeredResponseSqrtTermAtScale hP hStruct (k : ℤ) (m : ℤ) e ≤
        C_delta * Real.sqrt rho * F_i)
    (h_sqrtStar :
      let m : ℕ := memoryGridScale Nstar L i
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      C * starSqrtTerm ≤ C_delta * Real.sqrt rho * F_i)
    (h_eps :
      let m : ℕ := memoryGridScale Nstar L i
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      C * eps * F_i ≤ C_delta * eps * F_i)
    (h_S :
      let m : ℕ := memoryGridScale Nstar L i
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      C * eps⁻¹ * (1 + F_i) * S_term ≤
        C_S * eps⁻¹ * etaS * F_i +
          C_S * eps⁻¹ * rho ^ 2 * F_i)
    (h_tau :
      let m : ℕ := memoryGridScale Nstar L i
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      C * eps⁻¹ * P_tau_sum ≤ C_delta * eps⁻¹ * rho * F_i)
    (h_lower :
      let m : ℕ := memoryGridScale Nstar L i
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      let Hprev : ℝ :=
        memory (memoryDecay hc L)
          (initialMemory hc.rhoM N Nstar
            (fun n => contrastExcessAtScale hP hStruct n))
          (memoryGridDrop
            (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
          (i - 1)
      C * eps⁻¹ * lowerEdge ≤
        C_delta * eps⁻¹ * decay * F_i +
          C_memory * eps⁻¹ * (Hprev ^ 2 / (1 + F_i)) +
          C_edgeMem * eps⁻¹ * linTerm)
    (h_lowerStar :
      let m : ℕ := memoryGridScale Nstar L i
      let F_i : ℝ := contrastExcessAtScale hP hStruct m
      let Hprev : ℝ :=
        memory (memoryDecay hc L)
          (initialMemory hc.rhoM N Nstar
            (fun n => contrastExcessAtScale hP hStruct n))
          (memoryGridDrop
            (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
          (i - 1)
      C * eps⁻¹ * lowerEdgeStar ≤
        C_delta * eps⁻¹ * decay * F_i +
          C_memory * eps⁻¹ * (Hprev ^ 2 / (1 + F_i)) +
          C_edgeMem * eps⁻¹ * linTerm) :
    let m : ℕ := memoryGridScale Nstar L i
    let F_i : ℝ := contrastExcessAtScale hP hStruct m
    let Hprev : ℝ :=
      memory (memoryDecay hc L)
        (initialMemory hc.rhoM N Nstar
          (fun n => contrastExcessAtScale hP hStruct n))
        (memoryGridDrop
          (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
        (i - 1)
    let rhs : ℝ :=
      noDropResponseRHSLinear C_delta C_memory C_edgeMem eps (Real.sqrt rho)
        rho etaS etaSt (rho ^ 2) decay F_i (Hprev ^ 2 / (1 + F_i)) linTerm
    Homogenization.Book.Ch05.expectedCenteredResponseJAtScale hP hStruct
        (m : ℤ)
        (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
        (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) ≤
      rhs ∧
    Homogenization.Book.Ch05.expectedCenteredResponseJStarAtScale hP hStruct
        (m : ℤ)
        (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
        (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) ≤
      rhs := by
  dsimp only
  have hF_nonneg :
      0 ≤ contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) :=
    contrastExcessAtScale_nonneg_of_P4 hP hStruct hP4
      (memoryGridScale Nstar L i)
  have hC_rhoSq : C_S + 0 ≤ C_delta := by
    simpa using hC_S
  have hraw_zero :
      Homogenization.Book.Ch05.expectedCenteredResponseJAtScale hP hStruct
          ((memoryGridScale Nstar L i : ℕ) : ℤ)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct
            ((memoryGridScale Nstar L i : ℕ) : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct
            ((memoryGridScale Nstar L i : ℕ) : ℤ) e) ≤
        C * centeredResponseSqrtTermAtScale hP hStruct
              ((memoryGridScale Nstar L (i - 1) : ℕ) : ℤ)
              ((memoryGridScale Nstar L i : ℕ) : ℤ) e +
          C * eps *
              contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) +
            C * eps⁻¹ * weakNormGood +
              (0 : ℝ) * eps⁻¹ *
                ((1 +
                    contrastExcessAtScale hP hStruct
                      (memoryGridScale Nstar L i)) * 0) := by
    calc
      Homogenization.Book.Ch05.expectedCenteredResponseJAtScale hP hStruct
          ((memoryGridScale Nstar L i : ℕ) : ℤ)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct
            ((memoryGridScale Nstar L i : ℕ) : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct
            ((memoryGridScale Nstar L i : ℕ) : ℤ) e)
          ≤
        C * centeredResponseSqrtTermAtScale hP hStruct
              ((memoryGridScale Nstar L (i - 1) : ℕ) : ℤ)
              ((memoryGridScale Nstar L i : ℕ) : ℤ) e +
          C * eps *
              contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) +
            C * eps⁻¹ * weakNormGood := hraw
      _ =
        C * centeredResponseSqrtTermAtScale hP hStruct
              ((memoryGridScale Nstar L (i - 1) : ℕ) : ℤ)
              ((memoryGridScale Nstar L i : ℕ) : ℤ) e +
          C * eps *
              contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) +
            C * eps⁻¹ * weakNormGood +
              (0 : ℝ) * eps⁻¹ *
                ((1 +
                    contrastExcessAtScale hP hStruct
                      (memoryGridScale Nstar L i)) * 0) := by
          ring
  have hrawStar_zero :
      Homogenization.Book.Ch05.expectedCenteredResponseJStarAtScale hP hStruct
          ((memoryGridScale Nstar L i : ℕ) : ℤ)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct
            ((memoryGridScale Nstar L i : ℕ) : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct
            ((memoryGridScale Nstar L i : ℕ) : ℤ) e) ≤
        C * starSqrtTerm +
          C * eps *
              contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) +
            C * eps⁻¹ * weakNormGoodStar +
              (0 : ℝ) * eps⁻¹ *
                ((1 +
                    contrastExcessAtScale hP hStruct
                      (memoryGridScale Nstar L i)) * 0) := by
    calc
      Homogenization.Book.Ch05.expectedCenteredResponseJStarAtScale hP hStruct
          ((memoryGridScale Nstar L i : ℕ) : ℤ)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct
            ((memoryGridScale Nstar L i : ℕ) : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct
            ((memoryGridScale Nstar L i : ℕ) : ℤ) e)
          ≤
        C * starSqrtTerm +
          C * eps *
              contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) +
            C * eps⁻¹ * weakNormGoodStar := hrawStar
      _ =
        C * starSqrtTerm +
          C * eps *
              contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) +
            C * eps⁻¹ * weakNormGoodStar +
              (0 : ℝ) * eps⁻¹ *
                ((1 +
                    contrastExcessAtScale hP hStruct
                      (memoryGridScale Nstar L i)) * 0) := by
          ring
  constructor
  · exact
      expectedCenteredResponseJAtScale_le_noDropResponseRHSLinear_of_split_raw_highContrast_lower_memory_linear
        hP hStruct e
        (C_raw_bad := 0) (C_S := C_S) (C_bad := 0)
        (F_i := contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
        (weakNormGood := weakNormGood)
        (T_m :=
          1 + contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
        (S_term := S_term) (P_tau_sum := P_tau_sum)
        (lowerEdge := lowerEdge) (badMaximal := 0)
        (rho := rho) (etaS := etaS) (etaSt := etaSt) (rhoSq := rho ^ 2)
        (decay := decay) (linTerm := linTerm)
        (memoryTerm :=
          (memory (memoryDecay hc L)
            (initialMemory hc.rhoM N Nstar
              (fun n => contrastExcessAtScale hP hStruct n))
            (memoryGridDrop
              (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
            (i - 1)) ^ 2 /
            (1 + contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)))
        hC_nonneg heps_pos hF_nonneg hetaS_nonneg hetaSt_nonneg
        (sq_nonneg rho) hlin_nonneg hedgeMem_nonneg hC_S hC_delta_nonneg
        hC_rhoSq hraw_zero hweak h_sqrt h_eps h_S h_tau h_lower (by
          ring_nf
          exact le_rfl)
  · exact
      expectedCenteredResponseJStarAtScale_le_noDropResponseRHSLinear_of_split_raw_highContrast_lower_memory_linear
        hP hStruct e
        (C_raw_bad := 0) (C_S := C_S) (C_bad := 0)
        (starSqrtTerm := starSqrtTerm)
        (F_i := contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
        (weakNormGood := weakNormGoodStar)
        (T_m :=
          1 + contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
        (S_term := S_term) (P_tau_sum := P_tau_sum)
        (lowerEdge := lowerEdgeStar) (badMaximal := 0)
        (rho := rho) (etaS := etaS) (etaSt := etaSt) (rhoSq := rho ^ 2)
        (decay := decay) (linTerm := linTerm)
        (memoryTerm :=
          (memory (memoryDecay hc L)
            (initialMemory hc.rhoM N Nstar
              (fun n => contrastExcessAtScale hP hStruct n))
            (memoryGridDrop
              (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
            (i - 1)) ^ 2 /
            (1 + contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)))
        hC_nonneg heps_pos hF_nonneg hetaS_nonneg hetaSt_nonneg
        (sq_nonneg rho) hlin_nonneg hedgeMem_nonneg hC_S hC_delta_nonneg
        hC_rhoSq hrawStar_zero hweakStar h_sqrtStar h_eps h_S h_tau h_lowerStar
        (by
          ring_nf
          exact le_rfl)

end Homogenization.HighContrast.EntryScale
