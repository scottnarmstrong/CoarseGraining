import Homogenization.Deterministic.ConstantCoefficientDirichletBesov.OverlapGeometry

namespace Homogenization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Pointwise

/-- Average of a scalar field on an overlapping cube. -/
noncomputable def overlapCubeAverage {d : ℕ}
    (S : TriadicCube d) (f : Vec d → ℝ) : ℝ :=
  (overlapCubeVolume S)⁻¹ *
    ∫ x in overlapCubeSet S, f x ∂volume

theorem overlapCubeAverage_eq_integralAverage_openOverlapCubeSet {d : ℕ}
    (S : TriadicCube d) (f : Vec d → ℝ) :
    overlapCubeAverage S f = integralAverage (openOverlapCubeSet S) f := by
  unfold overlapCubeAverage integralAverage
  rw [setIntegral_overlapCubeSet_eq_setIntegral_openOverlapCubeSet,
    volume_openOverlapCubeSet_toReal]

namespace H1Function

@[simp] theorem toMeanZero_openOverlapCubeSet_apply {d : ℕ}
    (S : TriadicCube d) (u : H1Function (openOverlapCubeSet S)) (x : Vec d) :
    u.toMeanZero x = u x - overlapCubeAverage S (fun y => u y) := by
  have havg :
      integralAverage (openOverlapCubeSet S) (fun y => u y) =
        overlapCubeAverage S (fun y => u y) :=
    (overlapCubeAverage_eq_integralAverage_openOverlapCubeSet S (fun y => u y)).symm
  simp [havg]

@[simp] theorem toMeanZero_openOverlapCubeSet_grad {d : ℕ}
    (S : TriadicCube d) (u : H1Function (openOverlapCubeSet S)) (x : Vec d) :
    u.toMeanZero.toH1Function.grad x = u.grad x := by
  simp

end H1Function

/-- Coordinatewise average of a vector field on an overlapping cube. -/
noncomputable def overlapCubeAverageVec {d : ℕ}
    (S : TriadicCube d) (u : Vec d → Vec d) : Vec d :=
  fun i => overlapCubeAverage S fun x => u x i

/-- Normalized `Lᵖ` norm on an overlapping cube. -/
noncomputable def overlapCubeLpNorm {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (S : TriadicCube d) (p : ℝ≥0∞)
    (u : Vec d → E) : ℝ :=
  (MeasureTheory.eLpNorm u p (normalizedOverlapCubeMeasure S)).toReal

theorem overlapCubeAverage_eq_integral_normalizedOverlapCubeMeasure {d : ℕ}
    (S : TriadicCube d) (f : Vec d → ℝ) :
    overlapCubeAverage S f = ∫ x, f x ∂ normalizedOverlapCubeMeasure S := by
  rw [overlapCubeAverage, normalizedOverlapCubeMeasure, overlapCubeMeasure,
    MeasureTheory.integral_smul_measure]
  simp [smul_eq_mul, ENNReal.toReal_ofReal, inv_nonneg, overlapCubeVolume_nonneg]

theorem overlapCubeAverage_congr_on_overlapCubeSet {d : ℕ}
    {S : TriadicCube d} {u v : Vec d → ℝ}
    (h : ∀ x ∈ overlapCubeSet S, u x = v x) :
    overlapCubeAverage S u = overlapCubeAverage S v := by
  unfold overlapCubeAverage
  refine congrArg (fun t : ℝ => (overlapCubeVolume S)⁻¹ * t) ?_
  apply MeasureTheory.integral_congr_ae
  exact (MeasureTheory.ae_restrict_iff' (measurableSet_overlapCubeSet S)).2 <|
    Filter.Eventually.of_forall h

theorem overlapCubeAverageVec_congr_on_overlapCubeSet {d : ℕ}
    {S : TriadicCube d} {u v : Vec d → Vec d}
    (h : ∀ x ∈ overlapCubeSet S, u x = v x) :
    overlapCubeAverageVec S u = overlapCubeAverageVec S v := by
  funext i
  exact overlapCubeAverage_congr_on_overlapCubeSet
    (S := S) (u := fun x => u x i) (v := fun x => v x i)
    (fun x hx => by simpa using congrFun (h x hx) i)

theorem overlapCubeLpNorm_congr_on_overlapCubeSet_generic {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (S : TriadicCube d) (p : ℝ≥0∞)
    {u v : Vec d → E} (h : ∀ x ∈ overlapCubeSet S, u x = v x) :
    overlapCubeLpNorm S p u = overlapCubeLpNorm S p v := by
  unfold overlapCubeLpNorm
  rw [MeasureTheory.eLpNorm_congr_ae]
  rw [normalizedOverlapCubeMeasure, overlapCubeMeasure, Filter.EventuallyEq]
  exact MeasureTheory.Measure.ae_smul_measure
    ((MeasureTheory.ae_restrict_iff' (measurableSet_overlapCubeSet S)).2 <|
      Filter.Eventually.of_forall h)
    (ENNReal.ofReal ((overlapCubeVolume S)⁻¹))

@[simp] theorem overlapCubeAverage_const {d : ℕ}
    (S : TriadicCube d) (c : ℝ) :
    overlapCubeAverage S (fun _ : Vec d => c) = c := by
  rw [overlapCubeAverage_eq_integral_normalizedOverlapCubeMeasure,
    MeasureTheory.integral_const]
  simp [MeasureTheory.Measure.real, normalizedOverlapCubeMeasure_apply_univ]

@[simp] theorem overlapCubeAverageVec_const {d : ℕ}
    (S : TriadicCube d) (c : Vec d) :
    overlapCubeAverageVec S (fun _ : Vec d => c) = c := by
  funext i
  simp [overlapCubeAverageVec]

theorem overlapCubeLpNorm_nonneg {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (S : TriadicCube d) (p : ℝ≥0∞) (f : Vec d → E) :
    0 ≤ overlapCubeLpNorm S p f :=
  ENNReal.toReal_nonneg

theorem overlapCubeLpNorm_const {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (S : TriadicCube d) (p : ℝ≥0∞) (c : E) (hp : p ≠ 0) :
    overlapCubeLpNorm S p (fun _ => c) = ‖c‖ := by
  unfold overlapCubeLpNorm
  rw [MeasureTheory.eLpNorm_const c hp (normalizedOverlapCubeMeasure_ne_zero S),
    normalizedOverlapCubeMeasure_apply_univ]
  simp

theorem overlapCubeLpNorm_one_eq_integral_norm {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (S : TriadicCube d) (f : Vec d → E)
    (hf : MeasureTheory.AEStronglyMeasurable f (normalizedOverlapCubeMeasure S)) :
    overlapCubeLpNorm S 1 f = ∫ x, ‖f x‖ ∂ normalizedOverlapCubeMeasure S := by
  unfold overlapCubeLpNorm
  rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm,
    ← MeasureTheory.integral_norm_eq_lintegral_enorm hf]

theorem overlapCubeLpNorm_mul_le_mul_overlapCubeLpNorm_of_holderConjugate {d : ℕ}
    (S : TriadicCube d) (p q : ℝ≥0∞) (f g : Vec d → ℝ)
    [ENNReal.HolderConjugate p q]
    (hf : MeasureTheory.MemLp f p (normalizedOverlapCubeMeasure S))
    (hg : MeasureTheory.MemLp g q (normalizedOverlapCubeMeasure S)) :
    overlapCubeLpNorm S 1 (fun x => f x * g x) ≤
      overlapCubeLpNorm S p f * overlapCubeLpNorm S q g := by
  have hmul :
      MeasureTheory.eLpNorm (fun x => f x * g x) 1 (normalizedOverlapCubeMeasure S) ≤
        1 * MeasureTheory.eLpNorm f p (normalizedOverlapCubeMeasure S) *
          MeasureTheory.eLpNorm g q (normalizedOverlapCubeMeasure S) := by
    simpa using
      (MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
        hf.1 hg.1 (fun a b => a * b) 1
        (Filter.Eventually.of_forall fun x => by
          simp))
  have hf_top :
      MeasureTheory.eLpNorm f p (normalizedOverlapCubeMeasure S) ≠ ∞ := ne_of_lt hf.2
  have hg_top :
      MeasureTheory.eLpNorm g q (normalizedOverlapCubeMeasure S) ≠ ∞ := ne_of_lt hg.2
  have hmul_top :
      1 * MeasureTheory.eLpNorm f p (normalizedOverlapCubeMeasure S) *
        MeasureTheory.eLpNorm g q (normalizedOverlapCubeMeasure S) ≠ ∞ := by
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.one_ne_top hf_top) hg_top
  have htoReal :
      (MeasureTheory.eLpNorm (fun x => f x * g x) 1
          (normalizedOverlapCubeMeasure S)).toReal ≤
        (1 * MeasureTheory.eLpNorm f p (normalizedOverlapCubeMeasure S) *
          MeasureTheory.eLpNorm g q (normalizedOverlapCubeMeasure S)).toReal :=
    ENNReal.toReal_mono hmul_top hmul
  simpa [overlapCubeLpNorm, hf_top, hg_top, mul_assoc] using htoReal

theorem abs_overlapCubeAverage_mul_le_mul_overlapCubeLpNorm_of_holderConjugate {d : ℕ}
    (S : TriadicCube d) (p q : ℝ≥0∞) (f g : Vec d → ℝ)
    [ENNReal.HolderConjugate p q]
    (hf : MeasureTheory.MemLp f p (normalizedOverlapCubeMeasure S))
    (hg : MeasureTheory.MemLp g q (normalizedOverlapCubeMeasure S)) :
    |overlapCubeAverage S (fun x => f x * g x)| ≤
      overlapCubeLpNorm S p f * overlapCubeLpNorm S q g := by
  have hfg_meas : MeasureTheory.AEStronglyMeasurable
      (fun x => f x * g x) (normalizedOverlapCubeMeasure S) :=
    hf.1.mul hg.1
  calc
    |overlapCubeAverage S (fun x => f x * g x)|
        = |∫ x, f x * g x ∂ normalizedOverlapCubeMeasure S| := by
            rw [overlapCubeAverage_eq_integral_normalizedOverlapCubeMeasure]
    _ ≤ ∫ x, |f x * g x| ∂ normalizedOverlapCubeMeasure S :=
          MeasureTheory.abs_integral_le_integral_abs
    _ = overlapCubeLpNorm S 1 (fun x => f x * g x) := by
          symm
          simpa using overlapCubeLpNorm_one_eq_integral_norm
            S (fun x => f x * g x) hfg_meas
    _ ≤ overlapCubeLpNorm S p f * overlapCubeLpNorm S q g :=
          overlapCubeLpNorm_mul_le_mul_overlapCubeLpNorm_of_holderConjugate
            S p q f g hf hg

theorem abs_overlapCubeAverage_mul_le_mul_overlapCubeLpNorm_conjExponent {d : ℕ}
    (S : TriadicCube d) (p : ℝ≥0∞) (f g : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f p (normalizedOverlapCubeMeasure S))
    (hg : MeasureTheory.MemLp g (ENNReal.conjExponent p)
      (normalizedOverlapCubeMeasure S))
    (hp : 1 ≤ p) :
    |overlapCubeAverage S (fun x => f x * g x)| ≤
      overlapCubeLpNorm S p f * overlapCubeLpNorm S (ENNReal.conjExponent p) g := by
  letI : ENNReal.HolderConjugate p (ENNReal.conjExponent p) :=
    ENNReal.HolderConjugate.conjExponent hp
  simpa using
    abs_overlapCubeAverage_mul_le_mul_overlapCubeLpNorm_of_holderConjugate
      S p (ENNReal.conjExponent p) f g hf hg

theorem overlapCubeLpNorm_component_le_overlapCubeLpNorm {d : ℕ}
    (S : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → Vec d) (i : Fin d)
    (hu : MeasureTheory.MemLp u p (normalizedOverlapCubeMeasure S)) :
    overlapCubeLpNorm S p (fun x => u x i) ≤ overlapCubeLpNorm S p u := by
  have hui : MeasureTheory.MemLp (fun x => u x i) p
      (normalizedOverlapCubeMeasure S) := by
    simpa using (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hu
  have hpoint :
      ∀ᵐ x ∂ normalizedOverlapCubeMeasure S, ‖u x i‖ ≤ (1 : ℝ) * ‖u x‖ := by
    exact Filter.Eventually.of_forall fun x => by
      simpa using (norm_le_pi_norm (u x) i)
  have hle :
      MeasureTheory.eLpNorm (fun x => u x i) p (normalizedOverlapCubeMeasure S) ≤
        ENNReal.ofReal (1 : ℝ) *
          MeasureTheory.eLpNorm u p (normalizedOverlapCubeMeasure S) :=
    MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpoint p
  have htop_u :
      MeasureTheory.eLpNorm u p (normalizedOverlapCubeMeasure S) ≠ ∞ := ne_of_lt hu.2
  have htop_ui :
      MeasureTheory.eLpNorm (fun x => u x i) p (normalizedOverlapCubeMeasure S) ≠ ∞ :=
    ne_of_lt hui.2
  have htoReal :
      (MeasureTheory.eLpNorm (fun x => u x i) p
          (normalizedOverlapCubeMeasure S)).toReal ≤
        (MeasureTheory.eLpNorm u p (normalizedOverlapCubeMeasure S)).toReal := by
    have hle' :
        MeasureTheory.eLpNorm (fun x => u x i) p (normalizedOverlapCubeMeasure S) ≤
          MeasureTheory.eLpNorm u p (normalizedOverlapCubeMeasure S) := by
      simpa using hle
    exact ENNReal.toReal_mono htop_u hle'
  simpa [overlapCubeLpNorm] using htoReal

theorem norm_overlapCubeAverageVec_le_overlapCubeLpNorm_two {d : ℕ}
    (S : TriadicCube d) (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    ‖overlapCubeAverageVec S u‖ ≤ overlapCubeLpNorm S (2 : ℝ≥0∞) u := by
  have hconj_two : ENNReal.conjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  refine (pi_norm_le_iff_of_nonneg
    (overlapCubeLpNorm_nonneg S (2 : ℝ≥0∞) u)).2 ?_
  intro i
  have hui : MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞)
      (normalizedOverlapCubeMeasure S) := by
    simpa using (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hu
  have hconst : MeasureTheory.MemLp (fun _ : Vec d => (1 : ℝ))
      (ENNReal.conjExponent (2 : ℝ≥0∞)) (normalizedOverlapCubeMeasure S) := by
    simpa [hconj_two] using
      (MeasureTheory.memLp_const (1 : ℝ) :
        MeasureTheory.MemLp (fun _ : Vec d => (1 : ℝ))
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
  have havg :
      ‖overlapCubeAverage S (fun x => u x i)‖ ≤
        overlapCubeLpNorm S (2 : ℝ≥0∞) (fun x => u x i) *
          overlapCubeLpNorm S (2 : ℝ≥0∞) (fun _ => (1 : ℝ)) := by
    simpa [hconj_two] using
      abs_overlapCubeAverage_mul_le_mul_overlapCubeLpNorm_conjExponent
        (S := S) (p := (2 : ℝ≥0∞)) (f := fun x => u x i) (g := fun _ => (1 : ℝ))
        hui hconst (by norm_num)
  have hnorm_one : overlapCubeLpNorm S (2 : ℝ≥0∞) (fun _ => (1 : ℝ)) = 1 := by
    simpa using
      overlapCubeLpNorm_const (S := S) (p := (2 : ℝ≥0∞)) (c := (1 : ℝ))
        (by norm_num)
  have havg' :
      ‖overlapCubeAverage S (fun x => u x i)‖ ≤
        overlapCubeLpNorm S (2 : ℝ≥0∞) (fun x => u x i) := by
    simpa [hnorm_one] using havg
  calc
    ‖overlapCubeAverageVec S u i‖ =
        ‖overlapCubeAverage S (fun x => u x i)‖ := by
          simp [overlapCubeAverageVec]
    _ ≤ overlapCubeLpNorm S (2 : ℝ≥0∞) (fun x => u x i) := havg'
    _ ≤ overlapCubeLpNorm S (2 : ℝ≥0∞) u :=
          overlapCubeLpNorm_component_le_overlapCubeLpNorm S (2 : ℝ≥0∞) u i hu

theorem overlapCubeLpNorm_add_le {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (S : TriadicCube d) (p : ℝ≥0∞) (f g : Vec d → E)
    (hf : MeasureTheory.MemLp f p (normalizedOverlapCubeMeasure S))
    (hg : MeasureTheory.MemLp g p (normalizedOverlapCubeMeasure S))
    (hp : 1 ≤ p) :
    overlapCubeLpNorm S p (fun x => f x + g x) ≤
      overlapCubeLpNorm S p f + overlapCubeLpNorm S p g := by
  have hsum :
      MeasureTheory.eLpNorm (fun x => f x + g x) p (normalizedOverlapCubeMeasure S) ≤
        MeasureTheory.eLpNorm f p (normalizedOverlapCubeMeasure S) +
          MeasureTheory.eLpNorm g p (normalizedOverlapCubeMeasure S) := by
    simpa using MeasureTheory.eLpNorm_add_le hf.1 hg.1 hp
  have hsum_top :
      MeasureTheory.eLpNorm f p (normalizedOverlapCubeMeasure S) +
        MeasureTheory.eLpNorm g p (normalizedOverlapCubeMeasure S) ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ne_of_lt hf.2, ne_of_lt hg.2⟩
  have htoReal :=
    ENNReal.toReal_mono hsum_top hsum
  rw [ENNReal.toReal_add (ne_of_lt hf.2) (ne_of_lt hg.2)] at htoReal
  simpa [overlapCubeLpNorm, ne_of_lt hf.2, ne_of_lt hg.2] using htoReal

theorem overlapCubeLpNorm_two_vec_le_sum_components {d : ℕ}
    (S : TriadicCube d) (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    overlapCubeLpNorm S (2 : ℝ≥0∞) u ≤
      ∑ i : Fin d, overlapCubeLpNorm S (2 : ℝ≥0∞) (fun x => u x i) := by
  let μ : MeasureTheory.Measure (Vec d) := normalizedOverlapCubeMeasure S
  let D : Vec d → ℝ := fun x => ∑ i : Fin d, ‖u x i‖
  have hcoord_mem :
      ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) μ := by
    intro i
    simpa [μ] using (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hu
  have hcoord_norm_mem :
      ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => ‖u x i‖) (2 : ℝ≥0∞) μ := by
    intro i
    simpa using (hcoord_mem i).norm
  have hD_mem : MeasureTheory.MemLp D (2 : ℝ≥0∞) μ := by
    have hsum :=
      MeasureTheory.memLp_finset_sum (μ := μ) (p := (2 : ℝ≥0∞))
        (s := Finset.univ)
        (f := fun i : Fin d => fun x : Vec d => ‖u x i‖)
        (fun i _hi => hcoord_norm_mem i)
    simpa [D] using hsum
  have hvec_le :
      MeasureTheory.eLpNorm u (2 : ℝ≥0∞) μ ≤
        MeasureTheory.eLpNorm D (2 : ℝ≥0∞) μ := by
    have hpoint :
        ∀ᵐ x ∂μ, ‖u x‖ ≤ (1 : ℝ) * ‖D x‖ := by
      exact Filter.Eventually.of_forall fun x => by
        have hD_nonneg : 0 ≤ D x :=
          Finset.sum_nonneg fun i _hi => norm_nonneg _
        have hu_le_D : ‖u x‖ ≤ D x := by
          refine (pi_norm_le_iff_of_nonneg hD_nonneg).2 ?_
          intro i
          exact Finset.single_le_sum
            (fun j _hj => norm_nonneg (u x j)) (Finset.mem_univ i)
        simpa [Real.norm_eq_abs, abs_of_nonneg hD_nonneg] using hu_le_D
    simpa using
      (MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpoint
        (2 : ℝ≥0∞))
  have hsum_eLp :
      MeasureTheory.eLpNorm D (2 : ℝ≥0∞) μ ≤
        ∑ i : Fin d,
          MeasureTheory.eLpNorm (fun x => ‖u x i‖) (2 : ℝ≥0∞) μ := by
    have hD :
        D = ∑ i : Fin d, (fun x : Vec d => ‖u x i‖) := by
      funext x
      simp [D]
    rw [hD]
    exact
      MeasureTheory.eLpNorm_sum_le
        (μ := μ) (p := (2 : ℝ≥0∞)) (s := Finset.univ)
        (f := fun i : Fin d => fun x : Vec d => ‖u x i‖)
        (fun i _hi => (hcoord_norm_mem i).1)
        (by norm_num : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞))
  have hmain :
      MeasureTheory.eLpNorm u (2 : ℝ≥0∞) μ ≤
        ∑ i : Fin d,
          MeasureTheory.eLpNorm (fun x => ‖u x i‖) (2 : ℝ≥0∞) μ :=
    hvec_le.trans hsum_eLp
  have hsum_ne_top :
      (∑ i : Fin d,
          MeasureTheory.eLpNorm (fun x => ‖u x i‖) (2 : ℝ≥0∞) μ) ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun i _hi => (hcoord_norm_mem i).2.ne
  have htoReal :
      (MeasureTheory.eLpNorm u (2 : ℝ≥0∞) μ).toReal ≤
        (∑ i : Fin d,
          MeasureTheory.eLpNorm (fun x => ‖u x i‖) (2 : ℝ≥0∞) μ).toReal :=
    ENNReal.toReal_mono hsum_ne_top hmain
  rw [ENNReal.toReal_sum (fun i _hi => (hcoord_norm_mem i).2.ne)] at htoReal
  have hsum_toReal_norm :
      (∑ i : Fin d,
          (MeasureTheory.eLpNorm (fun x => ‖u x i‖) (2 : ℝ≥0∞) μ).toReal) =
        ∑ i : Fin d,
          (MeasureTheory.eLpNorm (fun x => u x i) (2 : ℝ≥0∞) μ).toReal := by
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [MeasureTheory.eLpNorm_norm]
  rw [hsum_toReal_norm] at htoReal
  simpa [overlapCubeLpNorm, μ] using htoReal

theorem cubeLpNorm_two_sq_eq_lintegral_rpow_enorm_toReal {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (Q : TriadicCube d) (f : Vec d → E) :
    (cubeLpNorm Q (2 : ℝ≥0∞) f) ^ 2 =
      (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ normalizedCubeMeasure Q).toReal := by
  unfold cubeLpNorm
  calc
    ((MeasureTheory.eLpNorm f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)).toReal) ^ 2
        =
          ((MeasureTheory.eLpNorm f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) ^
            (2 : ℝ)).toReal := by
          rw [← ENNReal.toReal_rpow]
          norm_num
    _ =
          (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ normalizedCubeMeasure Q).toReal := by
          rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
          let A : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ normalizedCubeMeasure Q
          change ((A ^ (1 / (2 : ℝ))) ^ (2 : ℝ)).toReal = A.toReal
          rw [← ENNReal.rpow_mul]
          norm_num

theorem cubeLpNorm_two_sq_eq_lintegral_ofReal_sq_toReal {d : ℕ}
    (Q : TriadicCube d) (f : Vec d → ℝ) :
    (cubeLpNorm Q (2 : ℝ≥0∞) f) ^ 2 =
      (∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂ normalizedCubeMeasure Q).toReal := by
  rw [cubeLpNorm_two_sq_eq_lintegral_rpow_enorm_toReal]
  congr 1
  apply MeasureTheory.lintegral_congr
  intro x
  rw [← ofReal_norm_eq_enorm]
  rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f x)) (by norm_num)]
  rw [Real.rpow_two]
  simp [Real.norm_eq_abs, sq_abs]

theorem cubeLpNorm_two_sq_le_lintegral_ofReal_vecNormSq_toReal_of_le
    {d : ℕ} {Q : TriadicCube d} {F : Vec d → Vec d} {B : ℝ≥0∞}
    (hB_ne_top : B ≠ ∞)
    (hbound :
      ∫⁻ x, ENNReal.ofReal (vecNormSq (F x)) ∂ normalizedCubeMeasure Q ≤ B) :
    (cubeLpNorm Q (2 : ℝ≥0∞) F) ^ 2 ≤ B.toReal := by
  have hnorm :
      ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂ normalizedCubeMeasure Q ≤
        ∫⁻ x, ENNReal.ofReal (vecNormSq (F x)) ∂ normalizedCubeMeasure Q :=
    MeasureTheory.lintegral_mono fun x =>
      enorm_rpow_two_le_ofReal_vecNormSq (F x)
  have hle : ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂ normalizedCubeMeasure Q ≤ B :=
    hnorm.trans hbound
  have htoReal := ENNReal.toReal_mono hB_ne_top hle
  simpa [cubeLpNorm_two_sq_eq_lintegral_rpow_enorm_toReal
    (Q := Q) (f := F)] using htoReal

theorem overlapCubeLpNorm_two_sq_eq_lintegral_rpow_enorm_toReal {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (S : TriadicCube d) (f : Vec d → E) :
    (overlapCubeLpNorm S (2 : ℝ≥0∞) f) ^ 2 =
      (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ normalizedOverlapCubeMeasure S).toReal := by
  unfold overlapCubeLpNorm
  calc
    ((MeasureTheory.eLpNorm f (2 : ℝ≥0∞)
        (normalizedOverlapCubeMeasure S)).toReal) ^ 2
        =
          ((MeasureTheory.eLpNorm f (2 : ℝ≥0∞)
              (normalizedOverlapCubeMeasure S)) ^ (2 : ℝ)).toReal := by
          rw [← ENNReal.toReal_rpow]
          norm_num
    _ =
          (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ normalizedOverlapCubeMeasure S).toReal := by
          rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
          let A : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ normalizedOverlapCubeMeasure S
          change ((A ^ (1 / (2 : ℝ))) ^ (2 : ℝ)).toReal = A.toReal
          rw [← ENNReal.rpow_mul]
          norm_num

theorem overlapCubeLpNorm_two_sq_le_lintegral_ofReal_vecNormSq_toReal_of_le
    {d : ℕ} {S : TriadicCube d} {F : Vec d → Vec d} {B : ℝ≥0∞}
    (hB_ne_top : B ≠ ∞)
    (hbound :
      ∫⁻ x, ENNReal.ofReal (vecNormSq (F x)) ∂ normalizedOverlapCubeMeasure S ≤ B) :
    (overlapCubeLpNorm S (2 : ℝ≥0∞) F) ^ 2 ≤ B.toReal := by
  have hnorm :
      ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂ normalizedOverlapCubeMeasure S ≤
        ∫⁻ x, ENNReal.ofReal (vecNormSq (F x)) ∂ normalizedOverlapCubeMeasure S :=
    MeasureTheory.lintegral_mono fun x =>
      enorm_rpow_two_le_ofReal_vecNormSq (F x)
  have hle : ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂ normalizedOverlapCubeMeasure S ≤ B :=
    hnorm.trans hbound
  have htoReal := ENNReal.toReal_mono hB_ne_top hle
  simpa [overlapCubeLpNorm_two_sq_eq_lintegral_rpow_enorm_toReal
    (S := S) (f := F)] using htoReal

theorem ae_mem_overlapCubeSet_normalizedOverlapCubeMeasure {d : ℕ}
    (S : TriadicCube d) :
    ∀ᵐ x ∂ normalizedOverlapCubeMeasure S, x ∈ overlapCubeSet S := by
  have h :
      ∀ᵐ x ∂ overlapCubeMeasure S, x ∈ overlapCubeSet S := by
    rw [overlapCubeMeasure]
    exact MeasureTheory.ae_restrict_mem (measurableSet_overlapCubeSet S)
  simpa [normalizedOverlapCubeMeasure] using
    MeasureTheory.Measure.ae_smul_measure h
      (ENNReal.ofReal ((overlapCubeVolume S)⁻¹))

theorem lintegral_ofReal_vecNormSq_le_of_forall_overlapCubeSet
    {d : ℕ} {S : TriadicCube d} {F : Vec d → Vec d} {B : ℝ}
    (hpoint : ∀ x ∈ overlapCubeSet S, vecNormSq (F x) ≤ B) :
    ∫⁻ x, ENNReal.ofReal (vecNormSq (F x)) ∂ normalizedOverlapCubeMeasure S ≤
      ENNReal.ofReal B := by
  have hmono :
      ∀ᵐ x ∂ normalizedOverlapCubeMeasure S,
        ENNReal.ofReal (vecNormSq (F x)) ≤ ENNReal.ofReal B :=
    (ae_mem_overlapCubeSet_normalizedOverlapCubeMeasure S).mono
      fun x hx => ENNReal.ofReal_le_ofReal (hpoint x hx)
  calc
    ∫⁻ x, ENNReal.ofReal (vecNormSq (F x)) ∂ normalizedOverlapCubeMeasure S
        ≤ ∫⁻ _x, ENNReal.ofReal B ∂ normalizedOverlapCubeMeasure S :=
          MeasureTheory.lintegral_mono_ae hmono
    _ = ENNReal.ofReal B := by
          simp [MeasureTheory.lintegral_const]

theorem overlapCubeLpNorm_two_sq_le_of_forall_overlapCubeSet_vecNormSq_le
    {d : ℕ} {S : TriadicCube d} {F : Vec d → Vec d} {B : ℝ}
    (hB : 0 ≤ B)
    (hpoint : ∀ x ∈ overlapCubeSet S, vecNormSq (F x) ≤ B) :
    (overlapCubeLpNorm S (2 : ℝ≥0∞) F) ^ 2 ≤ B := by
  have hbound :
      ∫⁻ x, ENNReal.ofReal (vecNormSq (F x)) ∂ normalizedOverlapCubeMeasure S ≤
        ENNReal.ofReal B :=
    lintegral_ofReal_vecNormSq_le_of_forall_overlapCubeSet
      (S := S) (F := F) hpoint
  have hnorm :=
    overlapCubeLpNorm_two_sq_le_lintegral_ofReal_vecNormSq_toReal_of_le
      (S := S) (F := F) (B := ENNReal.ofReal B)
      ENNReal.ofReal_ne_top hbound
  simpa [ENNReal.toReal_ofReal hB] using hnorm

theorem memLp_cubeMeasure_of_memLp_normalizedCubeMeasure {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (Q : TriadicCube d) {p : ℝ≥0∞} {f : Vec d → E}
    (hf : MeasureTheory.MemLp f p (normalizedCubeMeasure Q)) :
    MeasureTheory.MemLp f p (cubeMeasure Q) := by
  have hle :
      cubeMeasure Q ≤ ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q := by
    have hvol_nonneg : 0 ≤ cubeVolume Q := cubeVolume_nonneg Q
    have hmul :
        ENNReal.ofReal (cubeVolume Q) * ENNReal.ofReal ((cubeVolume Q)⁻¹) = 1 := by
      rw [← ENNReal.ofReal_mul hvol_nonneg]
      have hreal : cubeVolume Q * (cubeVolume Q)⁻¹ = 1 := by
        field_simp [(cubeVolume_pos Q).ne']
      rw [hreal]
      norm_num
    have heq : ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q = cubeMeasure Q := by
      rw [normalizedCubeMeasure]
      ext s
      rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.smul_apply]
      change
        ENNReal.ofReal (cubeVolume Q) *
            (ENNReal.ofReal ((cubeVolume Q)⁻¹) * (cubeMeasure Q) s) =
          (cubeMeasure Q) s
      rw [← mul_assoc, hmul, one_mul]
    exact le_of_eq heq.symm
  exact hf.of_measure_le_smul (c := ENNReal.ofReal (cubeVolume Q))
    ENNReal.ofReal_ne_top hle

/-- Exact normalized-to-unnormalized vector `L²` conversion on an open cube. -/
theorem cubeLpNorm_two_eq_volume_inv_rpow_half_mul_norm_toVectorL2_openCubeSet
    {d : ℕ} (Q : TriadicCube d) {f : Vec d → Vec d}
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) f =
      ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
        ‖Homogenization.toVectorL2
          (memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hf)‖ := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume Q)⁻¹)
  let μ : MeasureTheory.Measure (Vec d) := volumeMeasureOn (openCubeSet Q)
  let hopen : MemVectorL2 (openCubeSet Q) f :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hf
  have hhalf : ((1 / (2 : ℝ≥0∞)).toReal : ℝ) = (1 / 2 : ℝ) := by
    norm_num
  have hμ_eq : cubeMeasure Q = μ := by
    dsimp [μ, volumeMeasureOn]
    exact volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
  have hnorm_eq :
      cubeLpNorm Q (2 : ℝ≥0∞) f =
        (c ^ ((1 / (2 : ℝ≥0∞)).toReal) *
          MeasureTheory.eLpNorm f (2 : ℝ≥0∞) μ).toReal := by
    unfold cubeLpNorm normalizedCubeMeasure
    rw [MeasureTheory.eLpNorm_smul_measure_of_ne_top
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    simp [c, hμ_eq, μ]
  have hopen_norm :
      ‖Homogenization.toVectorL2 hopen‖ =
        (MeasureTheory.eLpNorm f (2 : ℝ≥0∞) μ).toReal := by
    dsimp [hopen, μ]
    rw [Homogenization.toVectorL2, MeasureTheory.Lp.norm_toLp]
  have hfactor :
      (c ^ ((1 / (2 : ℝ≥0∞)).toReal)).toReal =
        ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) := by
    rw [hhalf]
    dsimp [c]
    rw [ENNReal.ofReal_rpow_of_nonneg
      (inv_nonneg.mpr (cubeVolume_nonneg Q))
      (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    rw [ENNReal.toReal_ofReal
      (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _)]
  rw [hnorm_eq, ENNReal.toReal_mul, hopen_norm, hfactor]

theorem memLp_overlapCubeMeasure_of_memLp_normalizedOverlapCubeMeasure {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] (S : TriadicCube d) {p : ℝ≥0∞}
    {f : Vec d → E}
    (hf : MeasureTheory.MemLp f p (normalizedOverlapCubeMeasure S)) :
    MeasureTheory.MemLp f p (overlapCubeMeasure S) := by
  have hle :
      overlapCubeMeasure S ≤
        ENNReal.ofReal (overlapCubeVolume S) • normalizedOverlapCubeMeasure S := by
    have hvol_nonneg : 0 ≤ overlapCubeVolume S := overlapCubeVolume_nonneg S
    have hmul :
        ENNReal.ofReal (overlapCubeVolume S) *
            ENNReal.ofReal ((overlapCubeVolume S)⁻¹) = 1 := by
      rw [← ENNReal.ofReal_mul hvol_nonneg]
      have hreal : overlapCubeVolume S * (overlapCubeVolume S)⁻¹ = 1 := by
        field_simp [(overlapCubeVolume_pos S).ne']
      rw [hreal]
      norm_num
    have heq :
        ENNReal.ofReal (overlapCubeVolume S) • normalizedOverlapCubeMeasure S =
          overlapCubeMeasure S := by
      rw [normalizedOverlapCubeMeasure]
      ext s
      rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.smul_apply]
      change
        ENNReal.ofReal (overlapCubeVolume S) *
            (ENNReal.ofReal ((overlapCubeVolume S)⁻¹) *
              (overlapCubeMeasure S) s) =
          (overlapCubeMeasure S) s
      rw [← mul_assoc, hmul, one_mul]
    exact le_of_eq heq.symm
  exact hf.of_measure_le_smul (c := ENNReal.ofReal (overlapCubeVolume S))
    ENNReal.ofReal_ne_top hle

theorem memL2On_openOverlapCubeSet_of_memLp_normalizedOverlapCubeMeasure {d : ℕ}
    (S : TriadicCube d) {f : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    MemL2On (openOverlapCubeSet S) f := by
  have hfOverlap :
      MeasureTheory.MemLp f (2 : ℝ≥0∞) (overlapCubeMeasure S) :=
    memLp_overlapCubeMeasure_of_memLp_normalizedOverlapCubeMeasure S hf
  simpa [MemL2On, overlapCubeMeasure,
    volume_restrict_overlapCubeSet_eq_volume_restrict_openOverlapCubeSet S]
    using hfOverlap

theorem memVectorL2_openOverlapCubeSet_of_memLp_normalizedOverlapCubeMeasure {d : ℕ}
    (S : TriadicCube d) {f : Vec d → Vec d}
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    MemVectorL2 (openOverlapCubeSet S) f := by
  have hfOverlap :
      MeasureTheory.MemLp f (2 : ℝ≥0∞) (overlapCubeMeasure S) :=
    memLp_overlapCubeMeasure_of_memLp_normalizedOverlapCubeMeasure S hf
  simpa [MemVectorL2, overlapCubeMeasure,
    volume_restrict_overlapCubeSet_eq_volume_restrict_openOverlapCubeSet S]
    using hfOverlap

theorem memL2On_openOverlapCubeSet_normalizedOverlapCubeMeasure {d : ℕ}
    {S : TriadicCube d} {f : Vec d → ℝ}
    (hf : MemL2On (openOverlapCubeSet S) f) :
    MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S) := by
  have hfOverlap :
      MeasureTheory.MemLp f (2 : ℝ≥0∞) (overlapCubeMeasure S) := by
    simpa [MemL2On, overlapCubeMeasure,
      volume_restrict_overlapCubeSet_eq_volume_restrict_openOverlapCubeSet S]
      using hf
  simpa [normalizedOverlapCubeMeasure] using
    hfOverlap.smul_measure ENNReal.ofReal_ne_top

theorem memVectorL2_openOverlapCubeSet_normalizedOverlapCubeMeasure {d : ℕ}
    {S : TriadicCube d} {f : Vec d → Vec d}
    (hf : MemVectorL2 (openOverlapCubeSet S) f) :
    MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S) := by
  have hfOverlap :
      MeasureTheory.MemLp f (2 : ℝ≥0∞) (overlapCubeMeasure S) := by
    simpa [MemVectorL2, overlapCubeMeasure,
      volume_restrict_overlapCubeSet_eq_volume_restrict_openOverlapCubeSet S]
      using hf
  simpa [normalizedOverlapCubeMeasure] using
    hfOverlap.smul_measure ENNReal.ofReal_ne_top

/-- Exact normalized-to-unnormalized `L²` conversion on an open overlapping
cube. -/
theorem overlapCubeLpNorm_two_eq_volume_inv_rpow_half_mul_norm_toScalarL2_openOverlapCubeSet
    {d : ℕ} (S : TriadicCube d) {f : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    overlapCubeLpNorm S (2 : ℝ≥0∞) f =
      ((overlapCubeVolume S)⁻¹) ^ (1 / 2 : ℝ) *
        ‖Homogenization.toScalarL2
          (memL2On_openOverlapCubeSet_of_memLp_normalizedOverlapCubeMeasure S hf)‖ := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((overlapCubeVolume S)⁻¹)
  let μ : MeasureTheory.Measure (Vec d) := volumeMeasureOn (openOverlapCubeSet S)
  let hopen : MemScalarL2 (openOverlapCubeSet S) f :=
    memL2On_openOverlapCubeSet_of_memLp_normalizedOverlapCubeMeasure S hf
  have hhalf : ((1 / (2 : ℝ≥0∞)).toReal : ℝ) = (1 / 2 : ℝ) := by
    norm_num
  have hμ_eq : overlapCubeMeasure S = μ := by
    dsimp [μ, volumeMeasureOn]
    exact volume_restrict_overlapCubeSet_eq_volume_restrict_openOverlapCubeSet S
  have hnorm_eq :
      overlapCubeLpNorm S (2 : ℝ≥0∞) f =
        (c ^ ((1 / (2 : ℝ≥0∞)).toReal) *
          MeasureTheory.eLpNorm f (2 : ℝ≥0∞) μ).toReal := by
    unfold overlapCubeLpNorm normalizedOverlapCubeMeasure
    rw [MeasureTheory.eLpNorm_smul_measure_of_ne_top
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    simp [c, hμ_eq, μ]
  have hopen_norm :
      ‖Homogenization.toScalarL2 hopen‖ =
        (MeasureTheory.eLpNorm f (2 : ℝ≥0∞) μ).toReal := by
    dsimp [hopen, μ]
    rw [Homogenization.toScalarL2, MeasureTheory.Lp.norm_toLp]
  have hfactor :
      (c ^ ((1 / (2 : ℝ≥0∞)).toReal)).toReal =
        ((overlapCubeVolume S)⁻¹) ^ (1 / 2 : ℝ) := by
    rw [hhalf]
    dsimp [c]
    rw [ENNReal.ofReal_rpow_of_nonneg
      (inv_nonneg.mpr (overlapCubeVolume_nonneg S))
      (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    rw [ENNReal.toReal_ofReal
      (Real.rpow_nonneg (inv_nonneg.mpr (overlapCubeVolume_nonneg S)) _)]
  rw [hnorm_eq, ENNReal.toReal_mul, hopen_norm, hfactor]

theorem norm_toScalarL2_openOverlapCubeSet_eq_volume_rpow_half_mul_overlapCubeLpNorm_two
    {d : ℕ} (S : TriadicCube d) {f : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    ‖Homogenization.toScalarL2
        (memL2On_openOverlapCubeSet_of_memLp_normalizedOverlapCubeMeasure S hf)‖ =
      (overlapCubeVolume S) ^ (1 / 2 : ℝ) *
        overlapCubeLpNorm S (2 : ℝ≥0∞) f := by
  let A : ℝ := ((overlapCubeVolume S)⁻¹) ^ (1 / 2 : ℝ)
  let N : ℝ :=
    ‖Homogenization.toScalarL2
        (memL2On_openOverlapCubeSet_of_memLp_normalizedOverlapCubeMeasure S hf)‖
  let L : ℝ := overlapCubeLpNorm S (2 : ℝ≥0∞) f
  have hA_pos : 0 < A := by
    dsimp [A]
    exact Real.rpow_pos_of_pos (inv_pos.mpr (overlapCubeVolume_pos S)) _
  have hL_eq : L = A * N := by
    simpa [A, N, L] using
      overlapCubeLpNorm_two_eq_volume_inv_rpow_half_mul_norm_toScalarL2_openOverlapCubeSet
        S hf
  have hA_inv :
      A⁻¹ = (overlapCubeVolume S) ^ (1 / 2 : ℝ) := by
    dsimp [A]
    rw [Real.inv_rpow (le_of_lt (overlapCubeVolume_pos S)) (1 / 2 : ℝ)]
    rw [inv_inv]
  calc
    N = A⁻¹ * L := by
      rw [hL_eq]
      field_simp [hA_pos.ne']
    _ = (overlapCubeVolume S) ^ (1 / 2 : ℝ) * L := by
      rw [hA_inv]
    _ = (overlapCubeVolume S) ^ (1 / 2 : ℝ) *
        overlapCubeLpNorm S (2 : ℝ≥0∞) f := rfl

/-- Exact normalized-to-unnormalized vector `L²` conversion on an open
overlapping cube. -/
theorem overlapCubeLpNorm_two_eq_volume_inv_rpow_half_mul_norm_toVectorL2_openOverlapCubeSet
    {d : ℕ} (S : TriadicCube d) {f : Vec d → Vec d}
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    overlapCubeLpNorm S (2 : ℝ≥0∞) f =
      ((overlapCubeVolume S)⁻¹) ^ (1 / 2 : ℝ) *
        ‖Homogenization.toVectorL2
          (memVectorL2_openOverlapCubeSet_of_memLp_normalizedOverlapCubeMeasure S hf)‖ := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((overlapCubeVolume S)⁻¹)
  let μ : MeasureTheory.Measure (Vec d) := volumeMeasureOn (openOverlapCubeSet S)
  let hopen : MemVectorL2 (openOverlapCubeSet S) f :=
    memVectorL2_openOverlapCubeSet_of_memLp_normalizedOverlapCubeMeasure S hf
  have hhalf : ((1 / (2 : ℝ≥0∞)).toReal : ℝ) = (1 / 2 : ℝ) := by
    norm_num
  have hμ_eq : overlapCubeMeasure S = μ := by
    dsimp [μ, volumeMeasureOn]
    exact volume_restrict_overlapCubeSet_eq_volume_restrict_openOverlapCubeSet S
  have hnorm_eq :
      overlapCubeLpNorm S (2 : ℝ≥0∞) f =
        (c ^ ((1 / (2 : ℝ≥0∞)).toReal) *
          MeasureTheory.eLpNorm f (2 : ℝ≥0∞) μ).toReal := by
    unfold overlapCubeLpNorm normalizedOverlapCubeMeasure
    rw [MeasureTheory.eLpNorm_smul_measure_of_ne_top
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    simp [c, hμ_eq, μ]
  have hopen_norm :
      ‖Homogenization.toVectorL2 hopen‖ =
        (MeasureTheory.eLpNorm f (2 : ℝ≥0∞) μ).toReal := by
    dsimp [hopen, μ]
    rw [Homogenization.toVectorL2, MeasureTheory.Lp.norm_toLp]
  have hfactor :
      (c ^ ((1 / (2 : ℝ≥0∞)).toReal)).toReal =
        ((overlapCubeVolume S)⁻¹) ^ (1 / 2 : ℝ) := by
    rw [hhalf]
    dsimp [c]
    rw [ENNReal.ofReal_rpow_of_nonneg
      (inv_nonneg.mpr (overlapCubeVolume_nonneg S))
      (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    rw [ENNReal.toReal_ofReal
      (Real.rpow_nonneg (inv_nonneg.mpr (overlapCubeVolume_nonneg S)) _)]
  rw [hnorm_eq, ENNReal.toReal_mul, hopen_norm, hfactor]

theorem overlapCubeLpNorm_two_sub_overlapCubeAverage_le
    {d : ℕ} (S : TriadicCube d) (u : H1Function (openOverlapCubeSet S)) :
    overlapCubeLpNorm S (2 : ℝ≥0∞)
        (fun x => u x - overlapCubeAverage S (fun y => u y)) ≤
      ((overlapCubeVolume S)⁻¹) ^ (1 / 2 : ℝ) *
        ((overlapCubeScaleFactor S *
            (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
          ‖u.gradToVectorL2‖) := by
  let f : Vec d → ℝ := fun x => u.toMeanZero x
  have hf : MeasureTheory.MemLp f (2 : ℝ≥0∞)
      (normalizedOverlapCubeMeasure S) :=
    memL2On_openOverlapCubeSet_normalizedOverlapCubeMeasure
      (S := S) (f := f) (by
        simpa [f] using u.toMeanZero.toH1Function.memL2)
  have hfluct : (fun x => u x - overlapCubeAverage S (fun y => u y)) = f := by
    funext x
    dsimp [f]
    exact (H1Function.toMeanZero_openOverlapCubeSet_apply S u x).symm
  have hnorm :
      ‖Homogenization.toScalarL2
          (memL2On_openOverlapCubeSet_of_memLp_normalizedOverlapCubeMeasure S hf)‖ =
        (u.toMeanZero).valueL2Norm := by
    have hLp :
        Homogenization.toScalarL2
            (memL2On_openOverlapCubeSet_of_memLp_normalizedOverlapCubeMeasure S hf) =
          (u.toMeanZero).toScalarL2 := by
      apply MeasureTheory.Lp.ext
      filter_upwards
          [Homogenization.coeFn_toScalarL2
            (memL2On_openOverlapCubeSet_of_memLp_normalizedOverlapCubeMeasure S hf),
            H1Function.coeFn_toScalarL2 (u.toMeanZero.toH1Function)]
        with x hleft hright
      rw [hleft]
      change f x = (u.toMeanZero.toH1Function.toScalarL2 : Vec d → ℝ) x
      rw [hright]
    simpa [H1MeanZeroFunction.valueL2Norm] using congrArg norm hLp
  rw [hfluct]
  calc
    overlapCubeLpNorm S (2 : ℝ≥0∞) f
        =
          ((overlapCubeVolume S)⁻¹) ^ (1 / 2 : ℝ) *
            ‖Homogenization.toScalarL2
              (memL2On_openOverlapCubeSet_of_memLp_normalizedOverlapCubeMeasure S hf)‖ := by
          exact
            overlapCubeLpNorm_two_eq_volume_inv_rpow_half_mul_norm_toScalarL2_openOverlapCubeSet
              S hf
    _ =
          ((overlapCubeVolume S)⁻¹) ^ (1 / 2 : ℝ) *
            (u.toMeanZero).valueL2Norm := by
          rw [hnorm]
    _ ≤
          ((overlapCubeVolume S)⁻¹) ^ (1 / 2 : ℝ) *
            ((overlapCubeScaleFactor S *
                (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
              ‖u.gradToVectorL2‖) := by
          exact mul_le_mul_of_nonneg_left
            (openOverlapCubeMeanZero_valueL2Norm_le S u)
            (Real.rpow_nonneg (inv_nonneg.mpr (overlapCubeVolume_nonneg S)) _)

theorem overlapCubeLpNorm_two_sub_overlapCubeAverage_le_scale_mul_grad
    {d : ℕ} (S : TriadicCube d) (u : H1Function (openOverlapCubeSet S)) :
    overlapCubeLpNorm S (2 : ℝ≥0∞)
        (fun x => u x - overlapCubeAverage S (fun y => u y)) ≤
      (overlapCubeScaleFactor S *
          (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
        overlapCubeLpNorm S (2 : ℝ≥0∞) u.grad := by
  have hgrad : MeasureTheory.MemLp u.grad (2 : ℝ≥0∞)
      (normalizedOverlapCubeMeasure S) :=
    memVectorL2_openOverlapCubeSet_normalizedOverlapCubeMeasure
      (S := S) (f := u.grad) u.grad_memVectorL2
  have hgradNorm :
      ‖Homogenization.toVectorL2
          (memVectorL2_openOverlapCubeSet_of_memLp_normalizedOverlapCubeMeasure S hgrad)‖ =
        ‖u.gradToVectorL2‖ := by
    have hLp :
        Homogenization.toVectorL2
            (memVectorL2_openOverlapCubeSet_of_memLp_normalizedOverlapCubeMeasure S hgrad) =
          u.gradToVectorL2 := by
      apply MeasureTheory.Lp.ext
      filter_upwards
          [Homogenization.coeFn_toVectorL2
            (memVectorL2_openOverlapCubeSet_of_memLp_normalizedOverlapCubeMeasure S hgrad),
            H1Function.coeFn_gradToVectorL2 u]
        with x hleft hright
      rw [hleft]
      rw [hright]
    exact congrArg norm hLp
  have hgradExact :
      overlapCubeLpNorm S (2 : ℝ≥0∞) u.grad =
        ((overlapCubeVolume S)⁻¹) ^ (1 / 2 : ℝ) *
          ‖u.gradToVectorL2‖ := by
    calc
      overlapCubeLpNorm S (2 : ℝ≥0∞) u.grad
          =
            ((overlapCubeVolume S)⁻¹) ^ (1 / 2 : ℝ) *
              ‖Homogenization.toVectorL2
                (memVectorL2_openOverlapCubeSet_of_memLp_normalizedOverlapCubeMeasure
                  S hgrad)‖ := by
            exact
              overlapCubeLpNorm_two_eq_volume_inv_rpow_half_mul_norm_toVectorL2_openOverlapCubeSet
                S hgrad
      _ =
            ((overlapCubeVolume S)⁻¹) ^ (1 / 2 : ℝ) *
              ‖u.gradToVectorL2‖ := by
            rw [hgradNorm]
  calc
    overlapCubeLpNorm S (2 : ℝ≥0∞)
        (fun x => u x - overlapCubeAverage S (fun y => u y))
        ≤
          ((overlapCubeVolume S)⁻¹) ^ (1 / 2 : ℝ) *
            ((overlapCubeScaleFactor S *
                (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
              ‖u.gradToVectorL2‖) :=
          overlapCubeLpNorm_two_sub_overlapCubeAverage_le S u
    _ =
          (overlapCubeScaleFactor S *
              (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
            (((overlapCubeVolume S)⁻¹) ^ (1 / 2 : ℝ) *
              ‖u.gradToVectorL2‖) := by
          ring
    _ =
          (overlapCubeScaleFactor S *
              (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
            overlapCubeLpNorm S (2 : ℝ≥0∞) u.grad := by
          rw [hgradExact]


end

end Homogenization
