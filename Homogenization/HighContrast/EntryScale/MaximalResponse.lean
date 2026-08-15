import Mathlib.Tactic.Ring
import Homogenization.Book.Ch05.Definitions
import Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.CenteredResponses
import Homogenization.HighContrast.EntryScale.Inputs
import Homogenization.HighContrast.EntryScale.DeterministicAlgebra.P1

/-!
# Maximal centered-response estimate

Home for Proposition `p.HC.CR`.  This specializes the raw high-contrast
weak-norm lemma and centered-response energy reduction from the high-contrast
manuscript; it should not assume `p.HC.CR` as an unexplained theorem.
-/

namespace Homogenization.HighContrast.EntryScale

open MeasureTheory
open scoped BigOperators

/-- Weak-norm decomposition contribution kept before insertion into the raw
centered-response energy inequality. -/
def weakNormContribution
    (T_m S_term P_tau_sum lowerEdge badMaximal : ℝ) : ℝ :=
  T_m * S_term + P_tau_sum + lowerEdge + T_m * badMaximal

/--
Source label `e.raw.CR.energy`: square-root additivity term for the terminal
pair `p_e,q_e`, using the concrete Chapter 5 response
surface.
-/
noncomputable def centeredResponseSqrtTermAtScale {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (k m : ℤ) (e : Homogenization.Vec d) : ℝ :=
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct m e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct m e
  Real.sqrt (Homogenization.Book.Ch05.tauAtScale P m k p_e q_e) *
    Real.sqrt
      (Homogenization.Book.Ch04.expectedResponseJCubeSet P
        (Homogenization.originCube d k) p_e q_e)

/--
Source label `e.raw.CR.energy`: adjoint square-root additivity term for the
terminal pair.  The library represents the annealed lower-scale
`J^*` response through adjoint invariance by the same
`expectedResponseJCubeSet` scalar used for `J`.
-/
noncomputable def centeredResponseStarSqrtTermAtScale {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (k m : ℤ) (e : Homogenization.Vec d) : ℝ :=
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct m e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct m e
  Real.sqrt (Homogenization.Book.Ch05.tauAtScale P m k p_e q_e) *
    Real.sqrt
      (Homogenization.Book.Ch04.expectedResponseJCubeSet P
        (Homogenization.originCube d k) p_e q_e)

/--
Source label `e.centered.identity`: library-centered primal and adjoint responses
for the special vectors add to the scalar contrast excess `Theta_m - 1`, the
Lean version of the paper's `F_m`.
-/
theorem expectedCenteredResponses_special_add_eq_contrast
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (e : Homogenization.Vec d)
    (he : Homogenization.Book.Ch02.vecNorm e = 1) :
    Homogenization.Book.Ch05.expectedCenteredResponseJAtScale hP hStruct
        (m : ℤ)
        (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
        (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) +
      Homogenization.Book.Ch05.expectedCenteredResponseJStarAtScale hP hStruct
        (m : ℤ)
        (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
        (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) =
      Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ) - 1 := by
  exact
    (Homogenization.Book.Ch05.Section54.OneStepContraction.thetaAtScale_sub_one_eq_centeredResponses_special
        hP hStruct hP4 m e he).symm

/-- First-term coefficient in the special-vector library weak-norm RHS. -/
noncomputable def specialWeakNormEnergyFirstCoeffAtScale (d : ℕ) (m : ℕ) : ℝ :=
  2 *
    (1 +
      Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound
        (Homogenization.originCube d (m : ℤ)))

/--
The first weak-norm coefficient is bounded by a uniform dimensional constant.
This is the library's cutoff estimate `section53CutoffBound_le_two_pow_card`
specialized to the entry-scale special-vector coefficient.
-/
theorem specialWeakNormEnergyFirstCoeffAtScale_le_dimensional
    (d m : ℕ) :
    specialWeakNormEnergyFirstCoeffAtScale d m ≤ 2 * (1 + (2 : ℝ) ^ d) := by
  unfold specialWeakNormEnergyFirstCoeffAtScale
  have hcutoff :
      Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound
          (Homogenization.originCube d (m : ℤ)) ≤ (2 : ℝ) ^ d :=
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound_le_two_pow_card
        (Homogenization.originCube d (m : ℤ))
  nlinarith

/-- The non-additivity part of the special-vector library weak-norm RHS. -/
noncomputable def specialWeakNormEnergyRemainderAtScale
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Homogenization.Vec d) : ℝ :=
  let β :=
    Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta
      hP4
  let s := hP4.sLower + 2 * β
  let t := hP4.sUpper + 2 * β
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let j : ℕ := Int.toNat ((m : ℤ) - (k : ℤ))
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
  let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
  let gradWeak :=
    Homogenization.Book.Ch04.canonicalScalarResponseGradientWeakNormCubeSet
      Q s p_e q_e p0_e
  let fluxWeak :=
    Homogenization.Book.Ch04.canonicalScalarResponseFluxWeakNormCubeSet
      Q t p_e q_e q0_e
  let G := ∫ a, (gradWeak a) ^ 2 ∂P
  let F := ∫ a, (fluxWeak a) ^ 2 ∂P
  Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant
      Q *
      Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffScaleSep
        Q j *
        Homogenization.Book.Ch04.expectedResponseJCubeSet P Q p_e q_e +
    ((1 / 2 : ℝ) * ‖q0_e‖ *
        (((Fintype.card (Fin d) : ℝ) *
          ((3 : ℝ) ^ ((d : ℝ) + s) *
            Homogenization.cubeBesovScaleWeight (-s) Q *
              Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound
                Q s)) *
          ∫ a, gradWeak a ∂P) +
      (1 / 2 : ℝ) * ‖p0_e‖ *
        (((Fintype.card (Fin d) : ℝ) *
          ((3 : ℝ) ^ ((d : ℝ) + t) *
            Homogenization.cubeBesovScaleWeight (-t) Q *
              Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound
                Q t)) *
          ∫ a, fluxWeak a ∂P) +
      Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffProductCoeff
        Q s t *
        (Real.sqrt G * Real.sqrt F))

/-- Concrete decomposition of the library's special weak-norm RHS into the square-root
additivity term plus the remaining weak-norm scalar terms. -/
theorem specialWeakNormManuscriptRHSAtScale_eq_firstCoeff_mul_sqrtTerm_add_remainder
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Homogenization.Vec d) :
    Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.specialWeakNormManuscriptRHSAtScale
        hP hStruct hP4 k m e =
      specialWeakNormEnergyFirstCoeffAtScale d m *
          centeredResponseSqrtTermAtScale hP hStruct (k : ℤ) (m : ℤ) e +
        specialWeakNormEnergyRemainderAtScale hP hStruct hP4 k m e := by
  unfold Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.specialWeakNormManuscriptRHSAtScale
  unfold specialWeakNormEnergyFirstCoeffAtScale
  unfold centeredResponseSqrtTermAtScale
  unfold specialWeakNormEnergyRemainderAtScale
  simp [Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.jUpperWeakNormManuscriptExpectedRHSAtScale]
  ring

/--
Scalar conversion from the library's special weak-norm RHS to the raw-energy RHS
when the non-additivity remainder has already been bounded by the intended
centering and weak-norm slots.  This keeps the analytic remainder estimate
outside the raw-energy wrapper: downstream files must prove `hremainder` from
the concrete weak-norm decomposition, not assume it at the final theorem.
-/
theorem specialWeakNormManuscriptRHSAtScale_le_rawEnergyRHS_of_remainder_bound_atScales
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {C eps weakNorm : ℝ} {k m : ℕ} (e : Homogenization.Vec d)
    (hfirst_le : specialWeakNormEnergyFirstCoeffAtScale d m ≤ C)
    (hremainder :
      specialWeakNormEnergyRemainderAtScale hP hStruct hP4 k m e ≤
        C * eps * contrastExcessAtScale hP hStruct m +
          C * eps⁻¹ * weakNorm) :
    Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.specialWeakNormManuscriptRHSAtScale
        hP hStruct hP4 k m e ≤
      C * centeredResponseSqrtTermAtScale hP hStruct (k : ℤ) (m : ℤ) e +
        C * eps * contrastExcessAtScale hP hStruct m +
          C * eps⁻¹ * weakNorm := by
  let T := centeredResponseSqrtTermAtScale hP hStruct (k : ℤ) (m : ℤ) e
  let F := contrastExcessAtScale hP hStruct m
  let R := specialWeakNormEnergyRemainderAtScale hP hStruct hP4 k m e
  have hT_nonneg : 0 ≤ T := by
    dsimp [T, centeredResponseSqrtTermAtScale]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hfirst_scaled :
      specialWeakNormEnergyFirstCoeffAtScale d m * T ≤ C * T :=
    mul_le_mul_of_nonneg_right hfirst_le hT_nonneg
  calc
    Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.specialWeakNormManuscriptRHSAtScale
        hP hStruct hP4 k m e
        = specialWeakNormEnergyFirstCoeffAtScale d m * T + R := by
          simpa [T, R] using
            specialWeakNormManuscriptRHSAtScale_eq_firstCoeff_mul_sqrtTerm_add_remainder
              hP hStruct hP4 k m e
    _ ≤ C * T + R := by nlinarith [hfirst_scaled]
    _ ≤ C * T + (C * eps * F + C * eps⁻¹ * weakNorm) := by
          have hrem : R ≤ C * eps * F + C * eps⁻¹ * weakNorm := by
            simpa [F, R] using hremainder
          nlinarith
    _ =
        C * T + C * eps * F + C * eps⁻¹ * weakNorm := by
          ring

/-- Concrete primal raw-energy estimate whose weak-norm slot is supplied by a
proved bound for the library's non-additivity remainder. -/
theorem expectedCenteredResponseJAtScale_le_rawEnergyRHS_of_remainder_bound_atScales_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hstat : Homogenization.Book.Ch04.RestrictionStationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Homogenization.Vec d)
    {C eps weakNorm : ℝ}
    (hfirst_le : specialWeakNormEnergyFirstCoeffAtScale d m ≤ C)
    (hremainder :
      specialWeakNormEnergyRemainderAtScale hP hStruct hP4 k m e ≤
        C * eps * contrastExcessAtScale hP hStruct m +
          C * eps⁻¹ * weakNorm)
    (hGradSq :
      let β :=
        Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta
          hP4
      let s := hP4.sLower + 2 * β
      let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
      let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
      let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
      Integrable
        (fun a : Homogenization.RegCoeffField d =>
          (Homogenization.Book.Ch04.canonicalScalarResponseGradientWeakNormCubeSet
              (Homogenization.originCube d (m : ℤ)) s p_e q_e p0_e a.toFun) ^ 2) P)
    (hFluxSq :
      let β :=
        Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta
          hP4
      let t := hP4.sUpper + 2 * β
      let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
      let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
      let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
      Integrable
        (fun a : Homogenization.RegCoeffField d =>
          (Homogenization.Book.Ch04.canonicalScalarResponseFluxWeakNormCubeSet
              (Homogenization.originCube d (m : ℤ)) t p_e q_e q0_e a.toFun) ^ 2) P) :
    Homogenization.Book.Ch05.expectedCenteredResponseJAtScale hP hStruct
        (m : ℤ)
        (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
        (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) ≤
      C * centeredResponseSqrtTermAtScale hP hStruct (k : ℤ) (m : ℤ) e +
        C * eps * contrastExcessAtScale hP hStruct m +
          C * eps⁻¹ * weakNorm := by
  have hLIH :
      Homogenization.Book.Ch05.expectedCenteredResponseJAtScale hP hStruct
          (m : ℤ)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) ≤
        Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.specialWeakNormManuscriptRHSAtScale
          hP hStruct hP4 k m e := by
    simpa using
      Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.expectedCenteredResponseJAtScale_le_specialWeakNormManuscriptRHSAtScale
          hP hstat hStruct hP4 hkm e hGradSq hFluxSq
  have hscalar :=
    specialWeakNormManuscriptRHSAtScale_le_rawEnergyRHS_of_remainder_bound_atScales
      hP hStruct hP4 (C := C) (eps := eps) (weakNorm := weakNorm)
      (k := k) (m := m) e hfirst_le hremainder
  exact hLIH.trans hscalar

/-- Concrete adjoint raw-energy estimate whose weak-norm slot is supplied by a
proved bound for the library's non-additivity remainder. -/
theorem expectedCenteredResponseJStarAtScale_le_rawEnergyRHS_of_remainder_bound_atScales_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hstat : Homogenization.Book.Ch04.RestrictionStationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Homogenization.Vec d)
    {C eps weakNorm : ℝ}
    (hfirst_le : specialWeakNormEnergyFirstCoeffAtScale d m ≤ C)
    (hremainder :
      specialWeakNormEnergyRemainderAtScale hP hStruct hP4 k m e ≤
        C * eps * contrastExcessAtScale hP hStruct m +
          C * eps⁻¹ * weakNorm)
    (hGradSq :
      let β :=
        Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta
          hP4
      let s := hP4.sLower + 2 * β
      let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
      let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
      let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
      Integrable
        (fun a : Homogenization.RegCoeffField d =>
          (Homogenization.Book.Ch04.canonicalScalarResponseGradientWeakNormCubeSet
              (Homogenization.originCube d (m : ℤ)) s p_e q_e p0_e a.toFun) ^ 2) P)
    (hFluxSq :
      let β :=
        Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta
          hP4
      let t := hP4.sUpper + 2 * β
      let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
      let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
      let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
      Integrable
        (fun a : Homogenization.RegCoeffField d =>
          (Homogenization.Book.Ch04.canonicalScalarResponseFluxWeakNormCubeSet
              (Homogenization.originCube d (m : ℤ)) t p_e q_e q0_e a.toFun) ^ 2) P) :
    Homogenization.Book.Ch05.expectedCenteredResponseJStarAtScale hP hStruct
        (m : ℤ)
        (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
        (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) ≤
      C * centeredResponseStarSqrtTermAtScale hP hStruct (k : ℤ) (m : ℤ) e +
        C * eps * contrastExcessAtScale hP hStruct m +
          C * eps⁻¹ * weakNorm := by
  rw [
    Homogenization.Book.Ch05.Section54.OneStepContraction.expectedCenteredResponseJStarAtScale_eq_expectedCenteredResponseJAtScale
        hP hStruct hP4 m]
  simpa [centeredResponseStarSqrtTermAtScale, centeredResponseSqrtTermAtScale] using
    expectedCenteredResponseJAtScale_le_rawEnergyRHS_of_remainder_bound_atScales_of_P4
      hP hstat hStruct hP4 hkm e hfirst_le hremainder hGradSq hFluxSq
end Homogenization.HighContrast.EntryScale