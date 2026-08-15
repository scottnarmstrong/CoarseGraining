import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Homogenization.HighContrast.EntryScale.NoDropResponse

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open scoped Matrix.Norms.Elementwise


/-!
# Lyapunov contraction

Planned home for the pure real-sequence contraction argument.  This phase should
depend on the no-drop response estimate, not on the old variance attempt.
-/


namespace Homogenization.HighContrast.EntryScale

/-- Lyapunov quantity `Y_i = F_i + A H_i`.

Source label: `l.lyapunov`.
-/
def lyapunovValue (A F H : ℝ) : ℝ :=
  F + A * H

/--
Source label `e.dichotomy`: if the current drop satisfies
`F_{i-1} - F_i ≥ ρ F_i`, then `F_i ≤ (1 + ρ)⁻¹ F_{i-1}`.
-/
theorem le_inv_one_add_mul_of_drop {rho F_prev F_i : ℝ}
    (hrho_nonneg : 0 ≤ rho)
    (hdrop : rho * F_i ≤ F_prev - F_i) :
    F_i ≤ (1 + rho)⁻¹ * F_prev := by
  have hden_pos : 0 < 1 + rho := by linarith
  have hscaled : (1 + rho) * F_i ≤ F_prev := by
    nlinarith
  have hinv_nonneg : 0 ≤ (1 + rho)⁻¹ :=
    inv_nonneg.mpr (le_of_lt hden_pos)
  calc
    F_i = (1 + rho)⁻¹ * ((1 + rho) * F_i) := by
      field_simp [ne_of_gt hden_pos]
    _ ≤ (1 + rho)⁻¹ * F_prev :=
      mul_le_mul_of_nonneg_left hscaled hinv_nonneg

/--
Source label `e.dichotomy`: every step is either a genuine drop, giving the
linear contraction, or it is a no-drop window.
-/
theorem drop_or_noDropWindow_of_contrast_drop {rho F_prev F_i : ℝ}
    (hrho_nonneg : 0 ≤ rho) :
    F_i ≤ (1 + rho)⁻¹ * F_prev ∨ noDropWindow rho F_prev F_i := by
  by_cases hdrop : rho * F_i ≤ F_prev - F_i
  · exact Or.inl (le_inv_one_add_mul_of_drop hrho_nonneg hdrop)
  · exact Or.inr (by
      dsimp [noDropWindow]
      linarith)

/--
Source label `e.memory.alt`: if a quantity is bounded by a small multiple of
itself plus an error, then it is controlled by twice the error.
-/
theorem le_two_mul_error_of_le_half_self_add {F coeff error : ℝ}
    (hF_nonneg : 0 ≤ F)
    (hcoeff_le : coeff ≤ (1 / 2 : ℝ))
    (hbound : F ≤ coeff * F + error) :
    F ≤ 2 * error := by
  nlinarith

/--
Source label `e.memory.alt`: adding primal and adjoint no-drop response bounds
with total coefficient at most one half leaves only the memory error.
-/
theorem memory_alt_of_pair_response_bounds
    {F primal adjoint coeff memoryError : ℝ}
    (hF_nonneg : 0 ≤ F)
    (hidentity : F = primal + adjoint)
    (hprimal : primal ≤ coeff * F + memoryError)
    (hadjoint : adjoint ≤ coeff * F + memoryError)
    (hcoeff : 2 * coeff ≤ (1 / 2 : ℝ)) :
    F ≤ 4 * memoryError := by
  have hsum : F ≤ (2 * coeff) * F + 2 * memoryError := by
    rw [hidentity]
    nlinarith
  have htwo : F ≤ 2 * (2 * memoryError) :=
    le_two_mul_error_of_le_half_self_add hF_nonneg hcoeff hsum
  linarith

/-- **Layer B: paired linear-memory response bounds give the two-term memory
alternative.**

Analog of `memory_alt_of_pair_noDropResponseRHS` carrying the extra `H`-linear
edge-memory slot: paired no-drop `noDropResponseRHSLinear` bounds, once the
small error budget is compressed, give the memory alternative with **both** a
quadratic drift term and a linear (edge) memory term:
`F ≤ 4·memoryCoeff·quadTerm + 4·edgeMemoryCoeff·linTerm`. -/
theorem memory_alt_of_pair_noDropResponseRHSLinear
    {F primal adjoint C_delta C_memory C_edgeMem eps rhoSqrt rho etaS etaSt
      rhoSq decay quadTerm linTerm coeff memoryCoeff edgeMemoryCoeff : ℝ}
    (hF_nonneg : 0 ≤ F)
    (hquad_nonneg : 0 ≤ quadTerm)
    (hlin_nonneg : 0 ≤ linTerm)
    (hidentity : F = primal + adjoint)
    (hprimal :
      primal ≤
        noDropResponseRHSLinear C_delta C_memory C_edgeMem eps rhoSqrt rho etaS
          etaSt rhoSq decay F quadTerm linTerm)
    (hadjoint :
      adjoint ≤
        noDropResponseRHSLinear C_delta C_memory C_edgeMem eps rhoSqrt rho etaS
          etaSt rhoSq decay F quadTerm linTerm)
    (hcoeff_bound :
      C_delta *
        (rhoSqrt + eps + eps⁻¹ * (etaS + etaSt + rho + rhoSq) +
          eps⁻¹ * decay) ≤ coeff)
    (hmemoryCoeff : C_memory * eps⁻¹ ≤ memoryCoeff)
    (hedgeMemoryCoeff : C_edgeMem * eps⁻¹ ≤ edgeMemoryCoeff)
    (hsmall : 2 * coeff ≤ (1 / 2 : ℝ)) :
    F ≤
      4 * (memoryCoeff * quadTerm) + 4 * (edgeMemoryCoeff * linTerm) := by
  have hprimal_linear :
      primal ≤
        coeff * F +
          (memoryCoeff * quadTerm + edgeMemoryCoeff * linTerm) := by
    have := response_le_linear_memory_of_noDropResponseRHSLinear hprimal
      hF_nonneg hquad_nonneg hlin_nonneg hcoeff_bound hmemoryCoeff
      hedgeMemoryCoeff
    linarith
  have hadjoint_linear :
      adjoint ≤
        coeff * F +
          (memoryCoeff * quadTerm + edgeMemoryCoeff * linTerm) := by
    have := response_le_linear_memory_of_noDropResponseRHSLinear hadjoint
      hF_nonneg hquad_nonneg hlin_nonneg hcoeff_bound hmemoryCoeff
      hedgeMemoryCoeff
    linarith
  have hpair :
      F ≤ 4 * (memoryCoeff * quadTerm + edgeMemoryCoeff * linTerm) :=
    memory_alt_of_pair_response_bounds hF_nonneg hidentity hprimal_linear
      hadjoint_linear hsmall
  linarith

/-- **Layer B: memory alternative with a linear (edge) memory term.**

Source labels `p.nodrop.CR`, `e.centered.identity`, `e.memory.alt`, and Layer
A's `e.edge.memory.residual`.  Analog of `memory_alt_of_memoryGrid_noDropResponseRHS`
where the paired responses are bounded by the linear-memory RHS
`noDropResponseRHSLinear` carrying the extra `H`-linear slot `linTerm`.  The
resulting memory alternative for the scalar contrast excess carries **both** the
quadratic drift term and the linear edge term:
`F_m ≤ 4·memoryCoeff·(H²/(1+F_m)) + 4·edgeMemoryCoeff·linTerm`. -/
theorem memory_alt_linear_of_memoryGrid_noDropResponseRHSLinear
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (e : Homogenization.Vec d)
    {C_delta C_memory C_edgeMem eps rho etaS etaSt decay Hprev linTerm coeff
      memoryCoeff edgeMemoryCoeff : ℝ}
    (he : Homogenization.Book.Ch02.vecNorm e = 1)
    (hlin_nonneg : 0 ≤ linTerm)
    (hprimal :
      Homogenization.Book.Ch05.expectedCenteredResponseJAtScale hP hStruct
          (m : ℤ)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) ≤
        noDropResponseRHSLinear C_delta C_memory C_edgeMem eps (Real.sqrt rho)
          rho etaS etaSt (rho ^ 2) decay (contrastExcessAtScale hP hStruct m)
          (Hprev ^ 2 / (1 + contrastExcessAtScale hP hStruct m)) linTerm)
    (hadjoint :
      Homogenization.Book.Ch05.expectedCenteredResponseJStarAtScale hP hStruct
          (m : ℤ)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) ≤
        noDropResponseRHSLinear C_delta C_memory C_edgeMem eps (Real.sqrt rho)
          rho etaS etaSt (rho ^ 2) decay (contrastExcessAtScale hP hStruct m)
          (Hprev ^ 2 / (1 + contrastExcessAtScale hP hStruct m)) linTerm)
    (hcoeff_bound :
      C_delta *
        (Real.sqrt rho + eps + eps⁻¹ * (etaS + etaSt + rho + rho ^ 2) +
          eps⁻¹ * decay) ≤ coeff)
    (hmemoryCoeff : C_memory * eps⁻¹ ≤ memoryCoeff)
    (hedgeMemoryCoeff : C_edgeMem * eps⁻¹ ≤ edgeMemoryCoeff)
    (hsmall : 2 * coeff ≤ (1 / 2 : ℝ)) :
    contrastExcessAtScale hP hStruct m ≤
      4 * (memoryCoeff *
          (Hprev ^ 2 / (1 + contrastExcessAtScale hP hStruct m))) +
        4 * (edgeMemoryCoeff * linTerm) := by
  have hF_nonneg : 0 ≤ contrastExcessAtScale hP hStruct m :=
    contrastExcessAtScale_nonneg_of_P4 hP hStruct hP4 m
  have hden_pos : 0 < 1 + contrastExcessAtScale hP hStruct m := by
    linarith
  have hquad_nonneg :
      0 ≤ Hprev ^ 2 / (1 + contrastExcessAtScale hP hStruct m) :=
    div_nonneg (sq_nonneg Hprev) (le_of_lt hden_pos)
  have hidentity :
      contrastExcessAtScale hP hStruct m =
        Homogenization.Book.Ch05.expectedCenteredResponseJAtScale hP hStruct
            (m : ℤ)
            (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
            (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) +
          Homogenization.Book.Ch05.expectedCenteredResponseJStarAtScale hP hStruct
            (m : ℤ)
            (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
            (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) := by
    simpa [contrastExcessAtScale] using
      (expectedCenteredResponses_special_add_eq_contrast
        hP hStruct hP4 m e he).symm
  exact
    memory_alt_of_pair_noDropResponseRHSLinear
      (F := contrastExcessAtScale hP hStruct m)
      (primal :=
        Homogenization.Book.Ch05.expectedCenteredResponseJAtScale hP hStruct
          (m : ℤ)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e))
      (adjoint :=
        Homogenization.Book.Ch05.expectedCenteredResponseJStarAtScale hP hStruct
          (m : ℤ)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e))
      (C_delta := C_delta) (C_memory := C_memory) (C_edgeMem := C_edgeMem)
      (eps := eps) (rhoSqrt := Real.sqrt rho) (rho := rho) (etaS := etaS)
      (etaSt := etaSt) (rhoSq := rho ^ 2) (decay := decay)
      (quadTerm := Hprev ^ 2 / (1 + contrastExcessAtScale hP hStruct m))
      (linTerm := linTerm) (coeff := coeff) (memoryCoeff := memoryCoeff)
      (edgeMemoryCoeff := edgeMemoryCoeff)
      hF_nonneg hquad_nonneg hlin_nonneg hidentity hprimal hadjoint
      hcoeff_bound hmemoryCoeff hedgeMemoryCoeff hsmall

/--
Source label `l.lyapunov`: contraction in the drop case
`F_i ≤ θ F_{i-1}`.
-/
theorem lyapunov_step_of_drop {A q theta lambda F_prev F_i H_prev H_i : ℝ}
    (hA_nonneg : 0 ≤ A)
    (hF_prev_nonneg : 0 ≤ F_prev)
    (hH_prev_nonneg : 0 ≤ H_prev)
    (hdrop : F_i ≤ theta * F_prev)
    (hmemory : H_i ≤ q * H_prev + q * F_prev)
    (hF_coeff : theta + A * q ≤ lambda)
    (hH_coeff : q ≤ lambda) :
    lyapunovValue A F_i H_i ≤ lambda * lyapunovValue A F_prev H_prev := by
  have hA_memory : A * H_i ≤ A * (q * H_prev + q * F_prev) :=
    mul_le_mul_of_nonneg_left hmemory hA_nonneg
  calc
    lyapunovValue A F_i H_i
        = F_i + A * H_i := rfl
    _ ≤ theta * F_prev + A * (q * H_prev + q * F_prev) :=
        add_le_add hdrop hA_memory
    _ = (theta + A * q) * F_prev + (A * q) * H_prev := by ring
    _ ≤ lambda * F_prev + (A * lambda) * H_prev := by
        have hFpart : (theta + A * q) * F_prev ≤ lambda * F_prev :=
          mul_le_mul_of_nonneg_right hF_coeff hF_prev_nonneg
        have hHpart : (A * q) * H_prev ≤ (A * lambda) * H_prev := by
          have hAq : A * q ≤ A * lambda :=
            mul_le_mul_of_nonneg_left hH_coeff hA_nonneg
          exact mul_le_mul_of_nonneg_right hAq hH_prev_nonneg
        exact add_le_add hFpart hHpart
    _ = lambda * lyapunovValue A F_prev H_prev := by
        rw [lyapunovValue]
        ring

/--
Source label `l.lyapunov`: contraction in the memory alternative
`F_i ≤ K' H_{i-1}`.
-/
theorem lyapunov_step_of_memory {A q rho K lambda F_prev F_i H_prev H_i : ℝ}
    (hlambda_nonneg : 0 ≤ lambda)
    (hA_nonneg : 0 ≤ A)
    (hF_prev_nonneg : 0 ≤ F_prev)
    (hH_prev_nonneg : 0 ≤ H_prev)
    (hF_by_H : F_i ≤ K * H_prev)
    (hH_by_H : H_i ≤ q * (1 + rho * K) * H_prev)
    (hcoeff : K + A * (q * (1 + rho * K)) ≤ lambda * A) :
    lyapunovValue A F_i H_i ≤ lambda * lyapunovValue A F_prev H_prev := by
  have hA_memory : A * H_i ≤ A * (q * (1 + rho * K) * H_prev) :=
    mul_le_mul_of_nonneg_left hH_by_H hA_nonneg
  have hleft :
      lyapunovValue A F_i H_i ≤
        (K + A * (q * (1 + rho * K))) * H_prev := by
    calc
      lyapunovValue A F_i H_i
          = F_i + A * H_i := rfl
      _ ≤ K * H_prev + A * (q * (1 + rho * K) * H_prev) :=
          add_le_add hF_by_H hA_memory
      _ = (K + A * (q * (1 + rho * K))) * H_prev := by ring
  have hto_A : (K + A * (q * (1 + rho * K))) * H_prev ≤
      (lambda * A) * H_prev :=
    mul_le_mul_of_nonneg_right hcoeff hH_prev_nonneg
  have hA_part : (lambda * A) * H_prev ≤
      lambda * (F_prev + A * H_prev) := by
    have hAH_le : A * H_prev ≤ F_prev + A * H_prev := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hAH_le hlambda_nonneg
    nlinarith
  calc
    lyapunovValue A F_i H_i
        ≤ (K + A * (q * (1 + rho * K))) * H_prev := hleft
    _ ≤ (lambda * A) * H_prev := hto_A
    _ ≤ lambda * (F_prev + A * H_prev) := hA_part
    _ = lambda * lyapunovValue A F_prev H_prev := by rfl

/-- **Layer B: linearize the two-term memory alternative.**

Source label `e.F.by.Hprev` extended by the linear (edge) memory term: if the
contrast is controlled by the quadratic drift term **plus** a linear term
`F ≤ Kmem·(H²/(1+F)) + Klin·H`, then after linearizing the quadratic part
(`Kmem ≤ K²`) the whole bound is linear: `F ≤ (K + Klin)·H`.  The linear term
passes straight through with its own constant `Klin`. -/
theorem le_const_mul_of_le_mul_sq_div_one_add_add_linear
    {F H Kmem K Klin : ℝ}
    (hF_nonneg : 0 ≤ F)
    (hH_nonneg : 0 ≤ H)
    (hKmem_le : Kmem ≤ K ^ 2)
    (hK_nonneg : 0 ≤ K)
    (hKlin_nonneg : 0 ≤ Klin)
    (halt : F ≤ Kmem * (H ^ 2 / (1 + F)) + Klin * H) :
    F ≤ (K + Klin) * H := by
  have hden_pos : 0 < 1 + F := by linarith
  have hKH_nonneg : 0 ≤ K * H := mul_nonneg hK_nonneg hH_nonneg
  have hKlinH_nonneg : 0 ≤ Klin * H := mul_nonneg hKlin_nonneg hH_nonneg
  -- Multiply through by `(1 + F) > 0` to clear the denominator.
  have hmul :
      F * (1 + F) ≤
        (Kmem * (H ^ 2 / (1 + F)) + Klin * H) * (1 + F) :=
    mul_le_mul_of_nonneg_right halt (le_of_lt hden_pos)
  have hproduct :
      F * (1 + F) ≤ Kmem * H ^ 2 + Klin * H * (1 + F) := by
    have hdiv : H ^ 2 / (1 + F) * (1 + F) = H ^ 2 := by
      field_simp
    calc
      F * (1 + F)
          ≤ (Kmem * (H ^ 2 / (1 + F)) + Klin * H) * (1 + F) := hmul
      _ = Kmem * (H ^ 2 / (1 + F) * (1 + F)) + Klin * H * (1 + F) := by ring
      _ = Kmem * H ^ 2 + Klin * H * (1 + F) := by rw [hdiv]
  have hKmem_H_le : Kmem * H ^ 2 ≤ (K * H) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hKmem_le (sq_nonneg H)
    nlinarith
  -- Case split on the sign of `F - Klin·H`.
  rcases le_or_gt F (Klin * H) with hle | hlt
  · -- `F ≤ Klin·H ≤ (K + Klin)·H`.
    nlinarith [hKH_nonneg]
  · -- `F - Klin·H > 0`; then `(F - Klin·H)·(1+F) ≥ (F - Klin·H)²`.
    have hG_pos : 0 ≤ F - Klin * H := by linarith
    have hG_mul :
        (F - Klin * H) * (1 + F) ≤ Kmem * H ^ 2 := by nlinarith
    have hG_sq_le : (F - Klin * H) ^ 2 ≤ (K * H) ^ 2 := by
      -- `(F - Klin·H)² ≤ (F - Klin·H)·(1+F)` since `0 ≤ F - Klin·H ≤ 1 + F`.
      have hle' : F - Klin * H ≤ 1 + F := by linarith
      nlinarith [hG_mul, hKmem_H_le, hG_pos]
    -- From `(F - Klin·H)² ≤ (K·H)²` and both nonneg, `F - Klin·H ≤ K·H`.
    nlinarith [hG_sq_le, sq_nonneg (F - Klin * H - K * H), hKH_nonneg, hG_pos]

/--
Source label `l.lyapunov`: one-step contraction from the drop/memory
dichotomy.
-/
theorem lyapunov_step_of_dichotomy
    {A q rho K theta lambda F_prev F_i H_prev H_i : ℝ}
    (hlambda_nonneg : 0 ≤ lambda)
    (hA_nonneg : 0 ≤ A)
    (hF_prev_nonneg : 0 ≤ F_prev)
    (hH_prev_nonneg : 0 ≤ H_prev)
    (hdrop_coeff : theta + A * q ≤ lambda)
    (hdrop_memory_coeff : q ≤ lambda)
    (hmemory_coeff : K + A * (q * (1 + rho * K)) ≤ lambda * A)
    (hdichotomy :
      (F_i ≤ theta * F_prev ∧ H_i ≤ q * H_prev + q * F_prev) ∨
      (F_i ≤ K * H_prev ∧ H_i ≤ q * (1 + rho * K) * H_prev)) :
    lyapunovValue A F_i H_i ≤ lambda * lyapunovValue A F_prev H_prev := by
  rcases hdichotomy with hdrop | hmemory
  · exact lyapunov_step_of_drop hA_nonneg hF_prev_nonneg hH_prev_nonneg
      hdrop.1 hdrop.2 hdrop_coeff hdrop_memory_coeff
  · exact lyapunov_step_of_memory hlambda_nonneg hA_nonneg hF_prev_nonneg
      hH_prev_nonneg hmemory.1 hmemory.2 hmemory_coeff

/-- **Layer B: one-step Lyapunov contraction with a linear (edge) memory term.**

Source labels `e.dichotomy`, `e.memory.alt`, `e.F.by.Hprev`, Layer A's
`e.edge.memory.residual`, and `l.lyapunov`.  Identical to
`lyapunov_step_of_contrast_drop_or_memory_alt`, but the no-drop memory
alternative now carries an extra `H`-linear edge term
`F_i ≤ Kmem·(H_prev²/(1+F_i)) + Klin·H_prev`.  Linearizing the quadratic part
enlarges the linear constant from `K` to `K + Klin`; the memory-coefficient
constraint is correspondingly stated with `K + Klin` (this is the "widen K"
setup — the extra linear residual is absorbed straight into the `A·H` channel
via the same recursion, with `lambda` unchanged). -/
theorem lyapunov_step_of_contrast_drop_or_memory_alt_linear
    {A q rho Kmem K Klin lambda F_prev F_i H_prev H_i : ℝ}
    (hlambda_nonneg : 0 ≤ lambda)
    (hA_nonneg : 0 ≤ A)
    (hF_prev_nonneg : 0 ≤ F_prev)
    (hF_i_nonneg : 0 ≤ F_i)
    (hH_prev_nonneg : 0 ≤ H_prev)
    (hq_nonneg : 0 ≤ q)
    (hrho_nonneg : 0 ≤ rho)
    (hKmem_le : Kmem ≤ K ^ 2)
    (hK_nonneg : 0 ≤ K)
    (hKlin_nonneg : 0 ≤ Klin)
    (hH_rec : H_i ≤ q * H_prev + q * (F_prev - F_i))
    (hmemory_alt :
      noDropWindow rho F_prev F_i →
        F_i ≤ Kmem * (H_prev ^ 2 / (1 + F_i)) + Klin * H_prev)
    (hdrop_coeff : (1 + rho)⁻¹ + A * q ≤ lambda)
    (hdrop_memory_coeff : q ≤ lambda)
    (hmemory_coeff :
      (K + Klin) + A * (q * (1 + rho * (K + Klin))) ≤ lambda * A) :
    lyapunovValue A F_i H_i ≤ lambda * lyapunovValue A F_prev H_prev := by
  have hK'_nonneg : 0 ≤ K + Klin := by linarith
  have hbranch := drop_or_noDropWindow_of_contrast_drop
    (rho := rho) (F_prev := F_prev) (F_i := F_i) hrho_nonneg
  have hdichotomy :
      (F_i ≤ (1 + rho)⁻¹ * F_prev ∧
          H_i ≤ q * H_prev + q * F_prev) ∨
      (F_i ≤ (K + Klin) * H_prev ∧
          H_i ≤ q * (1 + rho * (K + Klin)) * H_prev) := by
    rcases hbranch with hdrop | hno
    · have hDelta_le_prev : F_prev - F_i ≤ F_prev := by
        linarith
      have hqDelta_le : q * (F_prev - F_i) ≤ q * F_prev :=
        mul_le_mul_of_nonneg_left hDelta_le_prev hq_nonneg
      have hH_drop : H_i ≤ q * H_prev + q * F_prev := by
        linarith
      exact Or.inl ⟨hdrop, hH_drop⟩
    · have hF_by_H : F_i ≤ (K + Klin) * H_prev :=
        le_const_mul_of_le_mul_sq_div_one_add_add_linear hF_i_nonneg
          hH_prev_nonneg hKmem_le hK_nonneg hKlin_nonneg (hmemory_alt hno)
      have hDelta_le : F_prev - F_i ≤ rho * F_i := by
        simpa [noDropWindow] using hno
      have hqDelta_le : q * (F_prev - F_i) ≤ q * (rho * F_i) :=
        mul_le_mul_of_nonneg_left hDelta_le hq_nonneg
      have hH_le_rhoF : H_i ≤ q * H_prev + q * (rho * F_i) := by
        linarith
      have hrhoF_le : rho * F_i ≤ rho * ((K + Klin) * H_prev) :=
        mul_le_mul_of_nonneg_left hF_by_H hrho_nonneg
      have hq_rhoF_le :
          q * (rho * F_i) ≤ q * (rho * ((K + Klin) * H_prev)) :=
        mul_le_mul_of_nonneg_left hrhoF_le hq_nonneg
      have hH_memory :
          H_i ≤ q * (1 + rho * (K + Klin)) * H_prev := by
        calc
          H_i ≤ q * H_prev + q * (rho * F_i) := hH_le_rhoF
          _ ≤ q * H_prev + q * (rho * ((K + Klin) * H_prev)) :=
              add_le_add_right hq_rhoF_le (q * H_prev)
          _ = q * (1 + rho * (K + Klin)) * H_prev := by ring
      exact Or.inr ⟨hF_by_H, hH_memory⟩
  exact
    lyapunov_step_of_dichotomy
      (A := A) (q := q) (rho := rho) (K := K + Klin)
      (theta := (1 + rho)⁻¹) (lambda := lambda)
      (F_prev := F_prev) (F_i := F_i) (H_prev := H_prev) (H_i := H_i)
      hlambda_nonneg hA_nonneg hF_prev_nonneg hH_prev_nonneg
      hdrop_coeff hdrop_memory_coeff hmemory_coeff hdichotomy

/-- **Layer B: memory-grid one-step contraction with a linear (edge) memory
term.**

Source labels `e.dichotomy`, `e.H.recursion`, Layer A's
`e.edge.memory.residual`, and `l.lyapunov`.  Analog of
`lyapunov_step_of_memoryGrid_memory_alt` where the no-drop memory alternative
carries the extra `H`-linear edge term `Klin·H_prev` (already reduced from
Layer A's `4·edgeMemoryCoeff·linTerm` via the KEY CHECK).  The linear constant
is enlarged from `K` to `K + Klin`; `lambda` is unchanged. -/
theorem lyapunov_step_of_memoryGrid_memory_alt_linear
    {d : ℕ} [NeZero d] (hc : HighContrastExponents d) {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {N Nstar L i : ℕ}
    {A K Klin lambda rho memoryCoeff : ℝ}
    (hi : 1 ≤ i)
    (hlambda_nonneg : 0 ≤ lambda)
    (hA_nonneg : 0 ≤ A)
    (hK_nonneg : 0 ≤ K)
    (hKlin_nonneg : 0 ≤ Klin)
    (hKmem_le : 4 * memoryCoeff ≤ K ^ 2)
    (hdrop_coeff : (1 + rho)⁻¹ + A * memoryDecay hc L ≤ lambda)
    (hdrop_memory_coeff : memoryDecay hc L ≤ lambda)
    (hmemory_coeff :
      (K + Klin) +
          A * (memoryDecay hc L * (1 + rho * (K + Klin))) ≤ lambda * A)
    (hrho_nonneg : 0 ≤ rho)
    (hmemory_alt :
      noDropWindow rho
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1)))
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) →
        contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) ≤
          (4 * memoryCoeff) *
              ((memory (memoryDecay hc L)
                    (initialMemory hc.rhoM N Nstar
                      (fun n => contrastExcessAtScale hP hStruct n))
                    (memoryGridDrop
                      (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
                    (i - 1)) ^ 2 /
                (1 +
                  contrastExcessAtScale hP hStruct
                    (memoryGridScale Nstar L i))) +
            Klin *
              memory (memoryDecay hc L)
                (initialMemory hc.rhoM N Nstar
                  (fun n => contrastExcessAtScale hP hStruct n))
                (memoryGridDrop
                  (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
                (i - 1)) :
    let Fgrid : ℕ → ℝ := fun n => contrastExcessAtScale hP hStruct n
    let q : ℝ := memoryDecay hc L
    let H0 : ℝ := initialMemory hc.rhoM N Nstar Fgrid
    let Delta : ℕ → ℝ := memoryGridDrop Fgrid Nstar L
    let F_prev : ℝ :=
      contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1))
    let F_i : ℝ :=
      contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)
    let H_prev : ℝ := memory q H0 Delta (i - 1)
    let H_i : ℝ := memory q H0 Delta i
    lyapunovValue A F_i H_i ≤ lambda * lyapunovValue A F_prev H_prev := by
  dsimp only
  have hF_prev_nonneg :
      0 ≤ contrastExcessAtScale hP hStruct
        (memoryGridScale Nstar L (i - 1)) :=
    contrastExcessAtScale_nonneg_of_P4 hP hStruct hP4
      (memoryGridScale Nstar L (i - 1))
  have hF_i_nonneg :
      0 ≤ contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) :=
    contrastExcessAtScale_nonneg_of_P4 hP hStruct hP4
      (memoryGridScale Nstar L i)
  have hF_antitone :
      Antitone (fun n => contrastExcessAtScale hP hStruct n) :=
    contrastExcessAtScale_antitone_of_P4 hP hStruct hP4
  have hH0_nonneg :
      0 ≤ initialMemory hc.rhoM N Nstar
        (fun n => contrastExcessAtScale hP hStruct n) :=
    initialMemory_nonneg_of_antitone hF_antitone
  have hdelta_nonneg :
      ∀ n, 0 ≤ memoryGridDrop
        (fun n => contrastExcessAtScale hP hStruct n) Nstar L n := by
    intro n
    cases n with
    | zero =>
        simp
    | succ n =>
        exact memoryGridDrop_succ_nonneg_of_antitone hF_antitone Nstar L n
  have hH_prev_nonneg :
      0 ≤ memory (memoryDecay hc L)
        (initialMemory hc.rhoM N Nstar
          (fun n => contrastExcessAtScale hP hStruct n))
        (memoryGridDrop
          (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
        (i - 1) :=
    memory_nonneg (le_of_lt (memoryDecay_pos hc L)) hH0_nonneg
      hdelta_nonneg (i - 1)
  have hH_rec :
      memory (memoryDecay hc L)
          (initialMemory hc.rhoM N Nstar
            (fun n => contrastExcessAtScale hP hStruct n))
          (memoryGridDrop
            (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
          i ≤
        memoryDecay hc L *
            memory (memoryDecay hc L)
              (initialMemory hc.rhoM N Nstar
                (fun n => contrastExcessAtScale hP hStruct n))
              (memoryGridDrop
                (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
              (i - 1) +
          memoryDecay hc L *
            (contrastExcessAtScale hP hStruct
                (memoryGridScale Nstar L (i - 1)) -
              contrastExcessAtScale hP hStruct
                (memoryGridScale Nstar L i)) := by
    have hrec :=
      memoryGrid_memory_step_eq (memoryDecay hc L)
        (initialMemory hc.rhoM N Nstar
          (fun n => contrastExcessAtScale hP hStruct n))
        (fun n => contrastExcessAtScale hP hStruct n) Nstar L i hi
    exact le_of_eq (by
      simpa [memoryGridContrast] using hrec)
  exact
    lyapunov_step_of_contrast_drop_or_memory_alt_linear
      (A := A) (q := memoryDecay hc L) (rho := rho)
      (Kmem := 4 * memoryCoeff) (K := K) (Klin := Klin) (lambda := lambda)
      (F_prev :=
        contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1)))
      (F_i := contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i))
      (H_prev :=
        memory (memoryDecay hc L)
          (initialMemory hc.rhoM N Nstar
            (fun n => contrastExcessAtScale hP hStruct n))
          (memoryGridDrop
            (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
          (i - 1))
      (H_i :=
        memory (memoryDecay hc L)
          (initialMemory hc.rhoM N Nstar
            (fun n => contrastExcessAtScale hP hStruct n))
          (memoryGridDrop
            (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
          i)
      hlambda_nonneg hA_nonneg hF_prev_nonneg hF_i_nonneg hH_prev_nonneg
      (le_of_lt (memoryDecay_pos hc L)) hrho_nonneg hKmem_le hK_nonneg
      hKlin_nonneg hH_rec hmemory_alt hdrop_coeff hdrop_memory_coeff
      hmemory_coeff

/-- **Layer B capstone: memory-grid contraction directly from Layer A's
`terminalP`-carrying linear residual.**

This is the load-bearing connection of the linear edge-memory channel.  It
consumes the memory alternative in **Layer A's actual residual shape** — the
linear term is `4·edgeMemoryCoeff·((H_prev /(1+F_k))·terminalPAtScales k m)`,
exactly the `C_lin·(H_n/(1+F_k))·terminalP` residual committed in
`EdgeMemoryResidual.lean` (with `n = i-1`, `k = memoryGridScale Nstar L (i-1)`,
`m = memoryGridScale Nstar L i`) — and applies the KEY CHECK
`linearEdgeMemory_terminalPAtScales_factor_le_four_of_noDrop_of_P4`:
`(H_prev/(1+F_k))·terminalP ≤ 4·H_prev`.  Hence the linear residual reduces to
`Klin·H_prev` with `Klin = 16·edgeMemoryCoeff`, and the contraction follows from
`lyapunov_step_of_memoryGrid_memory_alt_linear`.  The `terminalP` factor is thus
fully absorbed into the `A·H` channel, with `lambda` unchanged (the memory
coefficient constraint is stated with the enlarged `K + 16·edgeMemoryCoeff`). -/
theorem lyapunov_step_of_memoryGrid_noDropResponse_lower_memory_linear
    {d : ℕ} [NeZero d] (hc : HighContrastExponents d) {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {N Nstar L i : ℕ}
    {A K lambda rho edgeMemoryCoeff memoryCoeff : ℝ}
    (hi : 1 ≤ i)
    (hlambda_nonneg : 0 ≤ lambda)
    (hA_nonneg : 0 ≤ A)
    (hK_nonneg : 0 ≤ K)
    (hedgeMemoryCoeff_nonneg : 0 ≤ edgeMemoryCoeff)
    (hKmem_le : 4 * memoryCoeff ≤ K ^ 2)
    (hdrop_coeff : (1 + rho)⁻¹ + A * memoryDecay hc L ≤ lambda)
    (hdrop_memory_coeff : memoryDecay hc L ≤ lambda)
    (hmemory_coeff :
      (K + 16 * edgeMemoryCoeff) +
          A * (memoryDecay hc L *
                (1 + rho * (K + 16 * edgeMemoryCoeff))) ≤ lambda * A)
    (hrho_nonneg : 0 ≤ rho)
    (hrho_pos : 0 < rho)
    (hrho_le_one : rho ≤ 1)
    (hmemory_alt :
      noDropWindow rho
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1)))
          (contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)) →
        contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i) ≤
          (4 * memoryCoeff) *
              ((memory (memoryDecay hc L)
                    (initialMemory hc.rhoM N Nstar
                      (fun n => contrastExcessAtScale hP hStruct n))
                    (memoryGridDrop
                      (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
                    (i - 1)) ^ 2 /
                (1 +
                  contrastExcessAtScale hP hStruct
                    (memoryGridScale Nstar L i))) +
            4 * (edgeMemoryCoeff *
                ((memory (memoryDecay hc L)
                      (initialMemory hc.rhoM N Nstar
                        (fun n => contrastExcessAtScale hP hStruct n))
                      (memoryGridDrop
                        (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
                      (i - 1) /
                    (1 +
                      contrastExcessAtScale hP hStruct
                        (memoryGridScale Nstar L (i - 1)))) *
                  terminalPAtScales hP hStruct
                    (memoryGridScale Nstar L (i - 1))
                    (memoryGridScale Nstar L i)))) :
    let Fgrid : ℕ → ℝ := fun n => contrastExcessAtScale hP hStruct n
    let q : ℝ := memoryDecay hc L
    let H0 : ℝ := initialMemory hc.rhoM N Nstar Fgrid
    let Delta : ℕ → ℝ := memoryGridDrop Fgrid Nstar L
    let F_prev : ℝ :=
      contrastExcessAtScale hP hStruct (memoryGridScale Nstar L (i - 1))
    let F_i : ℝ :=
      contrastExcessAtScale hP hStruct (memoryGridScale Nstar L i)
    let H_prev : ℝ := memory q H0 Delta (i - 1)
    let H_i : ℝ := memory q H0 Delta i
    lyapunovValue A F_i H_i ≤ lambda * lyapunovValue A F_prev H_prev := by
  dsimp only
  have hedgeMemoryCoeff16_nonneg : 0 ≤ 16 * edgeMemoryCoeff := by linarith
  have hF_antitone :
      Antitone (fun n => contrastExcessAtScale hP hStruct n) :=
    contrastExcessAtScale_antitone_of_P4 hP hStruct hP4
  have hH0_nonneg :
      0 ≤ initialMemory hc.rhoM N Nstar
        (fun n => contrastExcessAtScale hP hStruct n) :=
    initialMemory_nonneg_of_antitone hF_antitone
  have hdelta_nonneg :
      ∀ n, 0 ≤ memoryGridDrop
        (fun n => contrastExcessAtScale hP hStruct n) Nstar L n := by
    intro n
    cases n with
    | zero => simp
    | succ n =>
        exact memoryGridDrop_succ_nonneg_of_antitone hF_antitone Nstar L n
  have hH_prev_nonneg :
      0 ≤ memory (memoryDecay hc L)
        (initialMemory hc.rhoM N Nstar
          (fun n => contrastExcessAtScale hP hStruct n))
        (memoryGridDrop
          (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
        (i - 1) :=
    memory_nonneg (le_of_lt (memoryDecay_pos hc L)) hH0_nonneg
      hdelta_nonneg (i - 1)
  have hkm :
      memoryGridScale Nstar L (i - 1) ≤ memoryGridScale Nstar L i :=
    memoryGridScale_le_of_le (Nat.sub_le i 1)
  -- Reduce Layer A's `terminalP`-carrying linear residual to `16·edgeMemoryCoeff·H_prev`.
  refine
    lyapunov_step_of_memoryGrid_memory_alt_linear
      (hc := hc) (hP := hP) (hStruct := hStruct) (hP4 := hP4)
      (N := N) (Nstar := Nstar) (L := L) (i := i)
      (A := A) (K := K) (Klin := 16 * edgeMemoryCoeff) (lambda := lambda)
      (memoryCoeff := memoryCoeff) hi hlambda_nonneg hA_nonneg hK_nonneg
      hedgeMemoryCoeff16_nonneg hKmem_le hdrop_coeff hdrop_memory_coeff
      hmemory_coeff hrho_nonneg ?_
  intro hno
  -- KEY CHECK: `(H_prev/(1+F_k))·terminalP ≤ 4·H_prev`.
  have hkeycheck :
      (memory (memoryDecay hc L)
              (initialMemory hc.rhoM N Nstar
                (fun n => contrastExcessAtScale hP hStruct n))
              (memoryGridDrop
                (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
              (i - 1) /
            (1 +
              contrastExcessAtScale hP hStruct
                (memoryGridScale Nstar L (i - 1)))) *
          terminalPAtScales hP hStruct
            (memoryGridScale Nstar L (i - 1))
            (memoryGridScale Nstar L i) ≤
        4 *
          memory (memoryDecay hc L)
            (initialMemory hc.rhoM N Nstar
              (fun n => contrastExcessAtScale hP hStruct n))
            (memoryGridDrop
              (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
            (i - 1) :=
    linearEdgeMemory_terminalPAtScales_factor_le_four_of_noDrop_of_P4
      hP hStruct hP4 hkm hno hrho_pos hrho_le_one hH_prev_nonneg
  -- Apply `hmemory_alt` and dominate the linear residual by `16·edgeMemoryCoeff·H_prev`.
  have halt := hmemory_alt hno
  have hlin_dom :
      4 * (edgeMemoryCoeff *
            ((memory (memoryDecay hc L)
                  (initialMemory hc.rhoM N Nstar
                    (fun n => contrastExcessAtScale hP hStruct n))
                  (memoryGridDrop
                    (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
                  (i - 1) /
                (1 +
                  contrastExcessAtScale hP hStruct
                    (memoryGridScale Nstar L (i - 1)))) *
              terminalPAtScales hP hStruct
                (memoryGridScale Nstar L (i - 1))
                (memoryGridScale Nstar L i))) ≤
        (16 * edgeMemoryCoeff) *
          memory (memoryDecay hc L)
            (initialMemory hc.rhoM N Nstar
              (fun n => contrastExcessAtScale hP hStruct n))
            (memoryGridDrop
              (fun n => contrastExcessAtScale hP hStruct n) Nstar L)
            (i - 1) := by
    have hscaled :=
      mul_le_mul_of_nonneg_left hkeycheck hedgeMemoryCoeff_nonneg
    nlinarith [hscaled]
  linarith [halt, hlin_dom]

/--
Source label `l.lyapunov`: scalar parameter choice for the Lyapunov
contraction.  Once the no-drop memory constant `K` and the no-drop threshold
`rho` are fixed, choosing `q` below the returned threshold gives all coefficient
hypotheses needed by `lyapunov_step_of_contrast_drop_or_memory_alt`.
-/
theorem exists_lyapunov_coefficients_of_rho_pos
    {rho K : ℝ} (hrho_pos : 0 < rho) (hK_nonneg : 0 ≤ K) :
    ∃ A lambda qMax : ℝ,
      0 ≤ A ∧ 0 < lambda ∧ lambda < 1 ∧ 0 < qMax ∧
      ∀ {q : ℝ}, 0 ≤ q → q ≤ qMax →
        (1 + rho)⁻¹ + A * q ≤ lambda ∧
        q ≤ lambda ∧
        K + A * (q * (1 + rho * K)) ≤ lambda * A := by
  let theta : ℝ := (1 + rho)⁻¹
  let A : ℝ := max 1 (4 * K)
  let lambda : ℝ := (1 + theta) / 2
  let qDrop : ℝ := (lambda - theta) / A
  let qMemory : ℝ := (lambda - (1 / 4 : ℝ)) / (1 + rho * K)
  let qMax : ℝ := min (min qDrop qMemory) lambda
  have hden_theta : 1 < 1 + rho := by linarith
  have htheta_pos : 0 < theta := by
    dsimp [theta]
    exact inv_pos.mpr (by linarith)
  have htheta_lt_one : theta < 1 := by
    dsimp [theta]
    exact inv_lt_one_of_one_lt₀ hden_theta
  have hA_ge_one : 1 ≤ A := by
    dsimp [A]
    exact le_max_left 1 (4 * K)
  have hA_ge_fourK : 4 * K ≤ A := by
    dsimp [A]
    exact le_max_right 1 (4 * K)
  have hA_pos : 0 < A := by linarith
  have hA_nonneg : 0 ≤ A := le_of_lt hA_pos
  have hlambda_pos : 0 < lambda := by
    dsimp [lambda]
    linarith
  have hlambda_lt_one : lambda < 1 := by
    dsimp [lambda]
    linarith
  have htheta_lt_lambda : theta < lambda := by
    dsimp [lambda]
    linarith
  have hquarter_lt_lambda : (1 / 4 : ℝ) < lambda := by
    dsimp [lambda]
    linarith
  have hden_memory_pos : 0 < 1 + rho * K := by
    have hrhoK_nonneg : 0 ≤ rho * K :=
      mul_nonneg (le_of_lt hrho_pos) hK_nonneg
    linarith
  have hqDrop_pos : 0 < qDrop := by
    dsimp [qDrop]
    exact div_pos (sub_pos.mpr htheta_lt_lambda) hA_pos
  have hqMemory_pos : 0 < qMemory := by
    dsimp [qMemory]
    exact div_pos (sub_pos.mpr hquarter_lt_lambda) hden_memory_pos
  have hqMax_pos : 0 < qMax := by
    dsimp [qMax]
    exact lt_min (lt_min hqDrop_pos hqMemory_pos) hlambda_pos
  refine ⟨A, lambda, qMax, hA_nonneg, hlambda_pos, hlambda_lt_one,
    hqMax_pos, ?_⟩
  intro q hq_nonneg hq_le
  have hq_le_qDrop : q ≤ qDrop := by
    exact hq_le.trans (by
      dsimp [qMax]
      exact (min_le_left (min qDrop qMemory) lambda).trans
        (min_le_left qDrop qMemory))
  have hq_le_qMemory : q ≤ qMemory := by
    exact hq_le.trans (by
      dsimp [qMax]
      exact (min_le_left (min qDrop qMemory) lambda).trans
        (min_le_right qDrop qMemory))
  have hq_le_lambda : q ≤ lambda := by
    exact hq_le.trans (by
      dsimp [qMax]
      exact min_le_right (min qDrop qMemory) lambda)
  have hAq_le : A * q ≤ lambda - theta := by
    have hmul := mul_le_mul_of_nonneg_left hq_le_qDrop hA_nonneg
    have hqDrop_mul : qDrop * A = lambda - theta := by
      dsimp [qDrop]
      field_simp [ne_of_gt hA_pos]
    nlinarith
  have hdrop_coeff : theta + A * q ≤ lambda := by linarith
  have hqMemory_mul : q * (1 + rho * K) ≤ lambda - (1 / 4 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hq_le_qMemory (le_of_lt hden_memory_pos)
    have hqMemory_mul_eq : qMemory * (1 + rho * K) = lambda - (1 / 4 : ℝ) := by
      dsimp [qMemory]
      field_simp [ne_of_gt hden_memory_pos]
    nlinarith
  have hK_le_quarter_A : K ≤ (1 / 4 : ℝ) * A := by nlinarith
  have hA_memory :
      A * (q * (1 + rho * K)) ≤ A * (lambda - (1 / 4 : ℝ)) :=
    mul_le_mul_of_nonneg_left hqMemory_mul hA_nonneg
  have hmemory_coeff :
      K + A * (q * (1 + rho * K)) ≤ lambda * A := by
    nlinarith
  exact ⟨by simpa [theta] using hdrop_coeff, hq_le_lambda, hmemory_coeff⟩

/--
Source label `l.lyapunov`: if each no-drop response error group is assigned a
fixed fraction of the smallness budget, then the total primal/adjoint response
coefficient is at most `1/4`.
-/
theorem noDrop_response_error_le_quarter_of_component_budgets
    {C_delta eps rho etaS etaSt decay : ℝ}
    (h_sqrt : C_delta * Real.sqrt rho ≤ (1 / 28 : ℝ))
    (h_eps : C_delta * eps ≤ (1 / 28 : ℝ))
    (h_etaS : C_delta * eps⁻¹ * etaS ≤ (1 / 28 : ℝ))
    (h_etaSt : C_delta * eps⁻¹ * etaSt ≤ (1 / 28 : ℝ))
    (h_rho : C_delta * eps⁻¹ * rho ≤ (1 / 28 : ℝ))
    (h_rhoSq : C_delta * eps⁻¹ * rho ^ 2 ≤ (1 / 28 : ℝ))
    (h_decay : C_delta * eps⁻¹ * decay ≤ (1 / 28 : ℝ)) :
    C_delta *
      (Real.sqrt rho + eps + eps⁻¹ * (etaS + etaSt + rho + rho ^ 2) +
        eps⁻¹ * decay) ≤ (1 / 4 : ℝ) := by
  have hsplit :
      C_delta *
          (Real.sqrt rho + eps + eps⁻¹ * (etaS + etaSt + rho + rho ^ 2) +
            eps⁻¹ * decay) =
        C_delta * Real.sqrt rho + C_delta * eps +
          C_delta * eps⁻¹ * etaS + C_delta * eps⁻¹ * etaSt +
          C_delta * eps⁻¹ * rho + C_delta * eps⁻¹ * rho ^ 2 +
          C_delta * eps⁻¹ * decay := by
    ring
  rw [hsplit]
  nlinarith

/--
Sharp variant of the ordered small-parameter choice: the response-error budget
additionally reserves the source-payment slot
`C_src * (etaSrc + polyRootBound + 2*rho + c_fold) <= decay`, by inflating
`decay` with `M := 1 + 5*C_src` and shrinking the base scale `a` accordingly.
-/
theorem exists_noDrop_response_error_parameters_sharp
    {C_delta C_src : ℝ} (hC_delta_nonneg : 0 ≤ C_delta)
    (hC_src_nonneg : 0 ≤ C_src) :
    ∃ eps rho etaS etaSt decay etaSrc polyRootBound c_fold : ℝ,
      0 < eps ∧ eps ≤ 1 ∧
      0 < rho ∧ rho ≤ 1 ∧
      0 < etaS ∧ 0 < etaSt ∧ 0 < decay ∧
      0 < etaSrc ∧ 0 < polyRootBound ∧ 0 < c_fold ∧
      ((112 * (max C_delta 1 * (1 + 5 * C_src)))⁻¹) ^ 4 ≤ c_fold ∧
      C_src * (etaSrc + polyRootBound + 2 * rho + c_fold) ≤ decay ∧
      C_delta *
        (Real.sqrt rho + eps + eps⁻¹ * (etaS + etaSt + rho + rho ^ 2) +
          eps⁻¹ * decay) ≤ (1 / 4 : ℝ) := by
  let D : ℝ := max C_delta 1
  let M : ℝ := 1 + 5 * C_src
  let a : ℝ := (112 * (D * M))⁻¹
  let rho0 : ℝ := a ^ 4
  have hD_pos : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right C_delta 1)
  have hD_ge_C : C_delta ≤ D := le_max_left C_delta 1
  have hD_ge_one : 1 ≤ D := le_max_right C_delta 1
  have hM_ge_one : 1 ≤ M := by
    dsimp [M]
    linarith
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one hM_ge_one
  have hden_pos : 0 < 112 * (D * M) := by positivity
  have hden_ge_one : 1 ≤ 112 * (D * M) := by nlinarith
  have ha_pos : 0 < a := inv_pos.mpr hden_pos
  have ha_nonneg : 0 ≤ a := le_of_lt ha_pos
  have ha_le_one : a ≤ 1 := by
    refine le_of_mul_le_mul_right ?_ hden_pos
    calc
      a * (112 * (D * M)) = 1 := by
        dsimp [a]
        field_simp [ne_of_gt hden_pos]
      _ ≤ 112 * (D * M) := hden_ge_one
      _ = 1 * (112 * (D * M)) := by ring
  have hDMa : (D * M) * a = 1 / 112 := by
    dsimp [a]
    field_simp [ne_of_gt hD_pos, ne_of_gt hM_pos]
  have hDa_le : D * a ≤ 1 / 112 := by
    have hDa_eq : D * a = (D * M) * a / M := by
      field_simp [ne_of_gt hM_pos]
    rw [hDa_eq, hDMa]
    rw [div_le_iff₀ hM_pos]
    nlinarith
  have ha_sq_le_one : a ^ 2 ≤ 1 := pow_le_one₀ (n := 2) ha_nonneg ha_le_one
  have hrho0_pos : 0 < rho0 := by
    dsimp [rho0]
    exact pow_pos ha_pos 4
  have hrho0_nonneg : 0 ≤ rho0 := le_of_lt hrho0_pos
  have hrho0_le_one : rho0 ≤ 1 := by
    dsimp [rho0]
    exact pow_le_one₀ (n := 4) ha_nonneg ha_le_one
  have hsqrt_rho0 : Real.sqrt rho0 = a ^ 2 := by
    dsimp [rho0]
    have hpow : a ^ 4 = (a ^ 2) ^ 2 := by ring
    rw [hpow]
    exact Real.sqrt_sq (sq_nonneg a)
  have hCa_le : C_delta * a ≤ 1 / 112 :=
    (mul_le_mul_of_nonneg_right hD_ge_C ha_nonneg).trans hDa_le
  have h_sqrt_budget : C_delta * Real.sqrt rho0 ≤ (1 / 28 : ℝ) := by
    rw [hsqrt_rho0]
    have h1 : C_delta * a ^ 2 = (C_delta * a) * a := by ring
    rw [h1]
    calc
      (C_delta * a) * a ≤ (1 / 112 : ℝ) * 1 := by
        refine mul_le_mul hCa_le ha_le_one ha_nonneg ?_
        norm_num
      _ ≤ (1 / 28 : ℝ) := by norm_num
  have h_eps_budget : C_delta * a ≤ (1 / 28 : ℝ) :=
    hCa_le.trans (by norm_num)
  have heps_inv_rho_eq : a⁻¹ * rho0 = a ^ 3 := by
    dsimp [rho0]
    field_simp [ne_of_gt ha_pos]
  have hCa3_le : C_delta * a ^ 3 ≤ (1 / 28 : ℝ) := by
    have h1 : C_delta * a ^ 3 = (C_delta * a) * a ^ 2 := by ring
    rw [h1]
    calc
      (C_delta * a) * a ^ 2 ≤ (1 / 112 : ℝ) * 1 := by
        refine mul_le_mul hCa_le ha_sq_le_one (sq_nonneg a) ?_
        norm_num
      _ ≤ (1 / 28 : ℝ) := by norm_num
  have h_rho_budget : C_delta * a⁻¹ * rho0 ≤ (1 / 28 : ℝ) := by
    calc
      C_delta * a⁻¹ * rho0 = C_delta * (a⁻¹ * rho0) := by ring
      _ = C_delta * a ^ 3 := by rw [heps_inv_rho_eq]
      _ ≤ (1 / 28 : ℝ) := hCa3_le
  have hrho0_sq_le_rho0 : rho0 ^ 2 ≤ rho0 := by
    nlinarith [sq_nonneg rho0, hrho0_nonneg, hrho0_le_one]
  have hfactor_nonneg : 0 ≤ C_delta * a⁻¹ :=
    mul_nonneg hC_delta_nonneg (inv_nonneg.mpr ha_nonneg)
  have h_rhoSq_budget : C_delta * a⁻¹ * rho0 ^ 2 ≤ (1 / 28 : ℝ) :=
    (mul_le_mul_of_nonneg_left hrho0_sq_le_rho0 hfactor_nonneg).trans
      h_rho_budget
  have h_decay_budget : C_delta * a⁻¹ * (M * rho0) ≤ (1 / 28 : ℝ) := by
    have h1 : C_delta * a⁻¹ * (M * rho0) = (C_delta * M) * (a⁻¹ * rho0) := by
      ring
    rw [h1, heps_inv_rho_eq]
    have h2 : (C_delta * M) * a ^ 3 = ((C_delta * M) * a) * a ^ 2 := by ring
    rw [h2]
    have hCMa_le : (C_delta * M) * a ≤ 1 / 112 := by
      have h3 : (C_delta * M) * a ≤ (D * M) * a := by
        have := mul_le_mul_of_nonneg_right hD_ge_C (le_of_lt hM_pos)
        exact mul_le_mul_of_nonneg_right (by nlinarith) ha_nonneg
      rw [hDMa] at h3
      exact h3
    calc
      ((C_delta * M) * a) * a ^ 2 ≤ (1 / 112 : ℝ) * 1 := by
        refine mul_le_mul hCMa_le ha_sq_le_one (sq_nonneg a) ?_
        norm_num
      _ ≤ (1 / 28 : ℝ) := by norm_num
  have hsrc_pay : C_src * (rho0 + rho0 + 2 * rho0 + rho0) ≤ M * rho0 := by
    have h1 : C_src * (rho0 + rho0 + 2 * rho0 + rho0) = 5 * C_src * rho0 := by
      ring
    rw [h1]
    have h2 : 5 * C_src ≤ M := by
      dsimp [M]
      linarith
    exact mul_le_mul_of_nonneg_right h2 hrho0_nonneg
  have hsmall :=
    noDrop_response_error_le_quarter_of_component_budgets
      (C_delta := C_delta) (eps := a) (rho := rho0)
      (etaS := rho0) (etaSt := rho0) (decay := M * rho0)
      h_sqrt_budget h_eps_budget h_rho_budget h_rho_budget h_rho_budget
      h_rhoSq_budget h_decay_budget
  exact
    ⟨a, rho0, rho0, rho0, M * rho0, rho0, rho0, rho0,
      ha_pos, ha_le_one, hrho0_pos, hrho0_le_one,
      hrho0_pos, hrho0_pos, mul_pos hM_pos hrho0_pos,
      hrho0_pos, hrho0_pos, hrho0_pos,
      le_of_eq (by dsimp [rho0, a, D, M]), hsrc_pay, hsmall⟩

end Homogenization.HighContrast.EntryScale
