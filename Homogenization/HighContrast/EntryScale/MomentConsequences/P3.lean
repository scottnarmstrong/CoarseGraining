import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.NNReal.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Order.Interval.Finset.Nat
import Homogenization.Book.Ch05.Theorems.Section52.GeometrySeries.DescendantCardinality
import Homogenization.Deterministic.CoarsePoincare.Setup.HarmonicAndData
import Homogenization.Geometry.TriadicPartition
import Homogenization.HighContrast.EntryScale.DeterministicAlgebra
import Homogenization.HighContrast.EntryScale.MomentConsequences.P1
import Homogenization.HighContrast.EntryScale.MomentConsequences.P2

open scoped BigOperators
open scoped Topology
open Filter

namespace Homogenization.HighContrast.EntryScale

/--
Source label `M_m^st`: the finite terminal stochastic envelope is never
`top` when its weak weights are bounded by the source weak weight.
-/
theorem terminalCoarseBlockStochasticEnvelope_ne_top_of_weak_le_terminal
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    {hc : HighContrastExponents d} (N m : ℕ)
    (Q : Homogenization.TriadicCube d)
    (weak : ℕ → Homogenization.TriadicCube d → ENNReal)
    (a : Ω → Homogenization.RegCoeffField d)
    (hweak : ∀ j ∈ Finset.Icc N m,
      ∀ R ∈ Homogenization.descendantsAtDepth Q (m - j),
        weak j R ≤
          ENNReal.ofReal ((3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ))))
    (ω : Ω) :
    terminalCoarseBlockStochasticEnvelope hP hStruct N m Q weak a ω ≠ ⊤ := by
  classical
  unfold terminalCoarseBlockStochasticEnvelope
  refine finset_sup_ne_top_of_forall_ne_top (Finset.Icc N m) _ ?_
  intro j hj
  refine
    finset_sup_ne_top_of_forall_ne_top
      (Homogenization.descendantsAtDepth Q (m - j)) _ ?_
  intro R hR
  have hweak_ne_top : weak j R ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hweak j hj R hR)
  have hdev_ne_top :
      terminalCoarseBlockDeviation hP hStruct m a j R ω ≠ ⊤ := by
    unfold terminalCoarseBlockDeviation
    unfold terminalCenteredFullBlockDeviation
    unfold coarseFullBlockMatrixAtCubeProcess
    exact ENNReal.ofReal_ne_top
  exact ENNReal.mul_ne_top hweak_ne_top hdev_ne_top

/--
Source label `M_m^st`: after the finite-envelope check, the real `toReal`
maximum has exactly the original ENNReal envelope as its extended norm.
-/
theorem enorm_terminalCoarseBlockStochasticMaxOfWeak_eq_envelope_of_weak_le_terminal
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    {hc : HighContrastExponents d} (N m : ℕ)
    (Q : Homogenization.TriadicCube d)
    (weak : ℕ → Homogenization.TriadicCube d → ENNReal)
    (a : Ω → Homogenization.RegCoeffField d)
    (hweak : ∀ j ∈ Finset.Icc N m,
      ∀ R ∈ Homogenization.descendantsAtDepth Q (m - j),
        weak j R ≤
          ENNReal.ofReal ((3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ))))
    (ω : Ω) :
    ‖terminalCoarseBlockStochasticMaxOfWeak hP hStruct N m Q weak a ω‖ₑ =
      terminalCoarseBlockStochasticEnvelope hP hStruct N m Q weak a ω := by
  unfold terminalCoarseBlockStochasticMaxOfWeak
  rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal
    (terminalCoarseBlockStochasticEnvelope_ne_top_of_weak_le_terminal
      hP hStruct N m Q weak a hweak ω)

/--
Source label `M_m^st`: the unpowered terminal stochastic ENNReal maximum has
the powered terminal envelope as its `Q`-th power.
-/
theorem terminalCoarseBlockStochasticEnvelope_rpow_eq_QEnvelope
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) (N m : ℕ)
    (Q : Homogenization.TriadicCube d)
    (weak : ℕ → Homogenization.TriadicCube d → ENNReal)
    (a : Ω → Homogenization.RegCoeffField d) (ω : Ω) :
    (terminalCoarseBlockStochasticEnvelope hP hStruct N m Q weak a ω) ^ hm.Q =
      terminalCoarseBlockStochasticQEnvelope hP hStruct hm N m Q weak a ω := by
  unfold terminalCoarseBlockStochasticEnvelope
  unfold terminalCoarseBlockStochasticQEnvelope
  rw [finset_sup_rpow_of_pos (Finset.Icc N m)
      (fun j => (Homogenization.descendantsAtDepth Q (m - j)).sup
        (fun R =>
          weak j R *
            terminalCoarseBlockDeviation hP hStruct m a j R ω))
      (highCenteredMoment_Q_pos hm)]
  refine Finset.sup_congr rfl ?_
  intro j _hj
  exact
    finset_sup_rpow_of_pos (Homogenization.descendantsAtDepth Q (m - j))
      (fun R =>
        weak j R *
          terminalCoarseBlockDeviation hP hStruct m a j R ω)
      (highCenteredMoment_Q_pos hm)

/--
Source label `M_m^st`: the real terminal stochastic maximum with a supplied
weak weight is pointwise controlled by the concrete powered ENNReal envelope.
-/
theorem terminalCoarseBlockStochasticMaxOfWeak_rpow_le_QEnvelope
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) (N m : ℕ)
    (Q : Homogenization.TriadicCube d)
    (weak : ℕ → Homogenization.TriadicCube d → ENNReal)
    (a : Ω → Homogenization.RegCoeffField d) (ω : Ω) :
    ‖terminalCoarseBlockStochasticMaxOfWeak hP hStruct N m Q weak a ω‖ₑ ^ hm.Q ≤
      terminalCoarseBlockStochasticQEnvelope hP hStruct hm N m Q weak a ω := by
  have hq_nonneg : 0 ≤ hm.Q := le_of_lt (highCenteredMoment_Q_pos hm)
  have hnorm :
      ‖terminalCoarseBlockStochasticMaxOfWeak hP hStruct N m Q weak a ω‖ₑ ≤
        terminalCoarseBlockStochasticEnvelope hP hStruct N m Q weak a ω := by
    simpa [terminalCoarseBlockStochasticMaxOfWeak] using
      enorm_ennreal_toReal_le
        (terminalCoarseBlockStochasticEnvelope hP hStruct N m Q weak a ω)
  calc
    ‖terminalCoarseBlockStochasticMaxOfWeak hP hStruct N m Q weak a ω‖ₑ ^ hm.Q
        ≤ (terminalCoarseBlockStochasticEnvelope hP hStruct N m Q weak a ω) ^
            hm.Q :=
          ENNReal.rpow_le_rpow hnorm hq_nonneg
    _ = terminalCoarseBlockStochasticQEnvelope hP hStruct hm N m Q weak a ω :=
          terminalCoarseBlockStochasticEnvelope_rpow_eq_QEnvelope
            hP hStruct hm N m Q weak a ω

/--
Source label `M_m^st`: the source-weighted terminal stochastic maximum is
pointwise controlled by the corresponding powered ENNReal envelope.
-/
theorem terminalCoarseBlockStochasticMax_rpow_le_QEnvelope
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) (N m : ℕ)
    (Q : Homogenization.TriadicCube d)
    (a : Ω → Homogenization.RegCoeffField d) (ω : Ω) :
    ‖terminalCoarseBlockStochasticMax hP hStruct hc N m Q a ω‖ₑ ^ hm.Q ≤
      terminalCoarseBlockStochasticQEnvelope hP hStruct hm N m Q
        (terminalStochasticWeakWeight hc m) a ω := by
  simpa [terminalCoarseBlockStochasticMax] using
    terminalCoarseBlockStochasticMaxOfWeak_rpow_le_QEnvelope
      hP hStruct hm N m Q (terminalStochasticWeakWeight hc m) a ω

/--
Source labels `a.HM` and `l.union.bound`: named-envelope version of the
polynomial terminal coarse-block union bound.
-/
theorem lintegral_terminalCoarseBlockStochasticQEnvelope_le_polynomial_convolution_of_highMoment
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (μ : MeasureTheory.Measure Ω) (Q : Homogenization.TriadicCube d) {N m : ℕ}
    (hNm : N ≤ m) (hQ : Q.scale = (m : ℤ))
    (weak : ℕ → Homogenization.TriadicCube d → ENNReal)
    (a : Ω → Homogenization.RegCoeffField d)
    (hHM :
      HighCenteredMomentEstimate hm μ N
        (intermediateCoarseBlockDeviation hP hStruct a))
    (hweak : ∀ j ∈ Finset.Icc N m,
      ∀ R ∈ Homogenization.descendantsAtDepth Q (m - j),
        weak j R ≤
          ENNReal.ofReal ((3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ)))) :
    ∫⁻ ω, terminalCoarseBlockStochasticQEnvelope hP hStruct hm N m Q weak a ω ∂ μ ≤
      ENNReal.ofReal
        (((2 +
          Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
          (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - N : ℕ) : ℝ))))) := by
  simpa [terminalCoarseBlockStochasticQEnvelope] using
    lintegral_sup_Icc_descendantsAtDepth_weak_terminalCoarseBlockDeviation_le_polynomial_convolution_of_highMoment
      hP hStruct hP4 hm μ Q hNm hQ weak a hHM hweak

/--
Source labels `M_m^st`, `a.HM`, and `l.union.bound`: the terminal stochastic
maximum has the actual high `Q` moment supplied by the source envelope.
-/
theorem memLp_terminalCoarseBlockStochasticMax_of_QEnvelope_highMoment
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (μ : MeasureTheory.Measure Ω) (Q : Homogenization.TriadicCube d) {N m : ℕ}
    (hNm : N ≤ m) (hQ : Q.scale = (m : ℤ))
    (weak : ℕ → Homogenization.TriadicCube d → ENNReal)
    (a : Ω → Homogenization.RegCoeffField d)
    (hHM :
      HighCenteredMomentEstimate hm μ N
        (intermediateCoarseBlockDeviation hP hStruct a))
    (hweak : ∀ j ∈ Finset.Icc N m,
      ∀ R ∈ Homogenization.descendantsAtDepth Q (m - j),
        weak j R ≤
          ENNReal.ofReal ((3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ))))
    {M : Ω → ℝ} (hM : MeasureTheory.AEStronglyMeasurable M μ)
    (hMpoint : ∀ ω, ‖M ω‖ₑ ^ hm.Q ≤
      terminalCoarseBlockStochasticQEnvelope hP hStruct hm N m Q weak a ω) :
    MeasureTheory.MemLp M (ENNReal.ofReal hm.Q) μ := by
  refine ⟨hM, ?_⟩
  have hQ_pos : 0 < hm.Q := highCenteredMoment_Q_pos hm
  have hQ_nonneg : 0 ≤ hm.Q := le_of_lt hQ_pos
  have hQenn_ne_zero : ENNReal.ofReal hm.Q ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le_of_gt hQ_pos]
  have hQenn_ne_top : ENNReal.ofReal hm.Q ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    hQenn_ne_zero hQenn_ne_top]
  have hlin :
      ∫⁻ ω, ‖M ω‖ₑ ^ hm.Q ∂ μ ≤
        ENNReal.ofReal
          (((2 +
            Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
            (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
              (3 : ℝ) ^
                (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                  ((m - N : ℕ) : ℝ))))) :=
    (MeasureTheory.lintegral_mono hMpoint).trans
      (lintegral_terminalCoarseBlockStochasticQEnvelope_le_polynomial_convolution_of_highMoment
        hP hStruct hP4 hm μ Q hNm hQ weak a hHM hweak)
  simpa [ENNReal.toReal_ofReal hQ_nonneg] using
    (lt_of_le_of_lt hlin ENNReal.ofReal_lt_top)

/--
Source labels `M_m^st`, `a.HM`, and `l.union.bound`: source-weighted
specialization of the high `Q` moment for the terminal stochastic maximum.
-/
theorem memLp_terminalCoarseBlockStochasticMax_highMoment
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (μ : MeasureTheory.Measure Ω) (Q : Homogenization.TriadicCube d) {N m : ℕ}
    (hNm : N ≤ m) (hQ : Q.scale = (m : ℤ))
    (a : Ω → Homogenization.RegCoeffField d)
    (hHM :
      HighCenteredMomentEstimate hm μ N
        (intermediateCoarseBlockDeviation hP hStruct a))
    (hM :
      MeasureTheory.AEStronglyMeasurable
        (terminalCoarseBlockStochasticMax hP hStruct hc N m Q a) μ) :
    MeasureTheory.MemLp
      (terminalCoarseBlockStochasticMax hP hStruct hc N m Q a)
      (ENNReal.ofReal hm.Q) μ := by
  let weak : ℕ → Homogenization.TriadicCube d → ENNReal :=
    terminalStochasticWeakWeight hc m
  have hweak : ∀ j ∈ Finset.Icc N m,
      ∀ R ∈ Homogenization.descendantsAtDepth Q (m - j),
        weak j R ≤
          ENNReal.ofReal ((3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ))) := by
    intro j _hj R _hR
    exact le_rfl
  have hpoint : ∀ ω,
      ‖terminalCoarseBlockStochasticMax hP hStruct hc N m Q a ω‖ₑ ^ hm.Q ≤
        terminalCoarseBlockStochasticQEnvelope hP hStruct hm N m Q weak a ω := by
    intro ω
    simpa [weak] using
      terminalCoarseBlockStochasticMax_rpow_le_QEnvelope
        hP hStruct hm N m Q a ω
  exact
    memLp_terminalCoarseBlockStochasticMax_of_QEnvelope_highMoment
      hP hStruct hP4 hm μ Q hNm hQ weak a hHM hweak hM hpoint

/--
Source labels `M_m^st`, `a.HM`, and `l.union.bound`: origin-cube version of
the high `Q` moment for the source-weighted terminal stochastic maximum.
-/
theorem memLp_terminalCoarseBlockStochasticMax_origin_highMoment
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) {N m : ℕ} (hNm : N ≤ m)
    (hHM :
      HighCenteredMomentEstimate hm P N
        (intermediateCoarseBlockDeviation hP hStruct
          (fun x : Homogenization.RegCoeffField d => x))) :
    MeasureTheory.MemLp
      (terminalCoarseBlockStochasticMax hP hStruct hc N m
        (Homogenization.originCube d (m : ℤ))
        (fun x : Homogenization.RegCoeffField d => x))
      (ENNReal.ofReal hm.Q) P := by
  have hQscale : (Homogenization.originCube d (m : ℤ)).scale = (m : ℤ) := by
    simp [Homogenization.originCube]
  have hM :
      MeasureTheory.AEStronglyMeasurable
        (terminalCoarseBlockStochasticMax hP hStruct hc N m
          (Homogenization.originCube d (m : ℤ))
          (fun x : Homogenization.RegCoeffField d => x)) P :=
    aestronglyMeasurable_terminalCoarseBlockStochasticMax_origin
      hP hStruct hP4 hc N m
  exact
    memLp_terminalCoarseBlockStochasticMax_highMoment
      hP hStruct hP4 hm P (Homogenization.originCube d (m : ℤ))
      hNm hQscale (fun x : Homogenization.RegCoeffField d => x) hHM hM

/--
Source labels `M_m^st`, `a.HM`, and `l.union.bound`: once a real stochastic
maximum is pointwise controlled by the concrete terminal coarse-block
`Q`-envelope, the manuscript polynomial union estimate gives its second moment.
-/
theorem lintegral_enorm_rpow_two_le_terminalCoarseBlockStochasticQEnvelope_polynomial_convolution_of_highMoment
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (Q : Homogenization.TriadicCube d) {N m : ℕ}
    (hNm : N ≤ m) (hQ : Q.scale = (m : ℤ))
    (weak : ℕ → Homogenization.TriadicCube d → ENNReal)
    (a : Ω → Homogenization.RegCoeffField d)
    (hHM :
      HighCenteredMomentEstimate hm μ N
        (intermediateCoarseBlockDeviation hP hStruct a))
    (hweak : ∀ j ∈ Finset.Icc N m,
      ∀ R ∈ Homogenization.descendantsAtDepth Q (m - j),
        weak j R ≤
          ENNReal.ofReal ((3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ))))
    {M : Ω → ℝ} (hM : MeasureTheory.AEStronglyMeasurable M μ)
    (hMpoint : ∀ ω, ‖M ω‖ₑ ^ hm.Q ≤
      terminalCoarseBlockStochasticQEnvelope hP hStruct hm N m Q weak a ω) :
    ∫⁻ ω, ‖M ω‖ₑ ^ (2 : ℝ) ∂ μ ≤
      (ENNReal.ofReal
        (((2 +
          Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
          (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - N : ℕ) : ℝ)))))) ^ ((2 : ℝ) / hm.Q) := by
  refine
    lintegral_enorm_rpow_two_le_of_lintegral_ennreal_envelope_highCenteredMoment
      hm hM hMpoint ?_
  exact
    lintegral_terminalCoarseBlockStochasticQEnvelope_le_polynomial_convolution_of_highMoment
      hP hStruct hP4 hm μ Q hNm hQ weak a hHM hweak

/--
Source labels `M_m^st`, `a.HM`, and `l.S.and.J`: polynomial second-moment
bound for the ENNReal stochastic envelope itself.  The only non-analytic
surface retained here is measurability of the corresponding real `toReal`
maximum, inherited from the existing Lyapunov theorem.
-/
theorem lintegral_terminalCoarseBlockStochasticEnvelope_sq_le_polynomial_convolution_of_highMoment
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (Q : Homogenization.TriadicCube d) {N m : ℕ}
    (hNm : N ≤ m) (hQ : Q.scale = (m : ℤ))
    (weak : ℕ → Homogenization.TriadicCube d → ENNReal)
    (a : Ω → Homogenization.RegCoeffField d)
    (hHM :
      HighCenteredMomentEstimate hm μ N
        (intermediateCoarseBlockDeviation hP hStruct a))
    (hweak : ∀ j ∈ Finset.Icc N m,
      ∀ R ∈ Homogenization.descendantsAtDepth Q (m - j),
        weak j R ≤
          ENNReal.ofReal ((3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ))))
    (hM :
      MeasureTheory.AEStronglyMeasurable
        (terminalCoarseBlockStochasticMaxOfWeak hP hStruct N m Q weak a) μ) :
    ∫⁻ ω,
        (terminalCoarseBlockStochasticEnvelope hP hStruct N m Q weak a ω) ^ 2 ∂ μ ≤
      (ENNReal.ofReal
        (((2 +
          Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
          (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - N : ℕ) : ℝ)))))) ^ ((2 : ℝ) / hm.Q) := by
  have hsecond :
      ∫⁻ ω,
          ‖terminalCoarseBlockStochasticMaxOfWeak hP hStruct N m Q weak a ω‖ₑ ^
            (2 : ℝ) ∂ μ ≤
        (ENNReal.ofReal
          (((2 +
            Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
            (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
              (3 : ℝ) ^
                (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                  ((m - N : ℕ) : ℝ)))))) ^ ((2 : ℝ) / hm.Q) :=
    lintegral_enorm_rpow_two_le_terminalCoarseBlockStochasticQEnvelope_polynomial_convolution_of_highMoment
      hP hStruct hP4 hm μ Q hNm hQ weak a hHM hweak hM
      (fun ω =>
        terminalCoarseBlockStochasticMaxOfWeak_rpow_le_QEnvelope
          hP hStruct hm N m Q weak a ω)
  have hpoint :
      (fun ω =>
        (terminalCoarseBlockStochasticEnvelope hP hStruct N m Q weak a ω) ^ 2) ≤
        fun ω =>
          ‖terminalCoarseBlockStochasticMaxOfWeak hP hStruct N m Q weak a ω‖ₑ ^
            (2 : ℝ) := by
    intro ω
    have hnorm :
        ‖terminalCoarseBlockStochasticMaxOfWeak hP hStruct N m Q weak a ω‖ₑ =
          terminalCoarseBlockStochasticEnvelope hP hStruct N m Q weak a ω :=
      enorm_terminalCoarseBlockStochasticMaxOfWeak_eq_envelope_of_weak_le_terminal
        hP hStruct N m Q weak a hweak ω
    exact le_of_eq <| by
      change
        (terminalCoarseBlockStochasticEnvelope hP hStruct N m Q weak a ω) ^ 2 =
          ‖terminalCoarseBlockStochasticMaxOfWeak hP hStruct N m Q weak a ω‖ₑ ^
            (2 : ℝ)
      rw [← hnorm, ENNReal.rpow_two]
  exact (MeasureTheory.lintegral_mono hpoint).trans hsecond

/--
Source labels `M_m^st`, `a.HM`, and `l.S.and.J`: source-weight specialization
of the ENNReal stochastic-envelope square estimate.
-/
theorem lintegral_terminalCoarseBlockStochasticEnvelope_sq_terminalWeak_le_polynomial_convolution_of_highMoment
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (Q : Homogenization.TriadicCube d) {N m : ℕ}
    (hNm : N ≤ m) (hQ : Q.scale = (m : ℤ))
    (a : Ω → Homogenization.RegCoeffField d)
    (hHM :
      HighCenteredMomentEstimate hm μ N
        (intermediateCoarseBlockDeviation hP hStruct a))
    (hM :
      MeasureTheory.AEStronglyMeasurable
        (terminalCoarseBlockStochasticMax hP hStruct hc N m Q a) μ) :
    ∫⁻ ω,
        (terminalCoarseBlockStochasticEnvelope hP hStruct N m Q
          (terminalStochasticWeakWeight hc m) a ω) ^ 2 ∂ μ ≤
      (ENNReal.ofReal
        (((2 +
          Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
          (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - N : ℕ) : ℝ)))))) ^ ((2 : ℝ) / hm.Q) := by
  refine
    lintegral_terminalCoarseBlockStochasticEnvelope_sq_le_polynomial_convolution_of_highMoment
      hP hStruct hP4 hm μ Q hNm hQ
      (terminalStochasticWeakWeight hc m) a hHM ?_ ?_
  · intro j _hj R _hR
    rfl
  · simpa [terminalCoarseBlockStochasticMax] using hM

/--
Source labels `M_m^st`, `a.HM`, and `l.union.bound`: polynomial second-moment
bound for the literal source-weighted terminal stochastic maximum.
-/
theorem lintegral_enorm_rpow_two_terminalCoarseBlockStochasticMax_le_polynomial_convolution_of_highMoment
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (Q : Homogenization.TriadicCube d) {N m : ℕ}
    (hNm : N ≤ m) (hQ : Q.scale = (m : ℤ))
    (a : Ω → Homogenization.RegCoeffField d)
    (hM :
      MeasureTheory.AEStronglyMeasurable
        (terminalCoarseBlockStochasticMax hP hStruct hc N m Q a) μ)
    (hHM :
      HighCenteredMomentEstimate hm μ N
        (intermediateCoarseBlockDeviation hP hStruct a)) :
    ∫⁻ ω, ‖terminalCoarseBlockStochasticMax hP hStruct hc N m Q a ω‖ₑ ^
        (2 : ℝ) ∂ μ ≤
      (ENNReal.ofReal
        (((2 +
          Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ^ hm.Q) *
          (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - N : ℕ) : ℝ)))))) ^ ((2 : ℝ) / hm.Q) := by
  let weak : ℕ → Homogenization.TriadicCube d → ENNReal :=
    terminalStochasticWeakWeight hc m
  have hweak : ∀ j ∈ Finset.Icc N m,
      ∀ R ∈ Homogenization.descendantsAtDepth Q (m - j),
        weak j R ≤
          ENNReal.ofReal ((3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ))) := by
    intro j _hj R _hR
    exact le_rfl
  have hpoint : ∀ ω,
      ‖terminalCoarseBlockStochasticMax hP hStruct hc N m Q a ω‖ₑ ^ hm.Q ≤
        terminalCoarseBlockStochasticQEnvelope hP hStruct hm N m Q weak a ω := by
    intro ω
    simpa [weak] using
      terminalCoarseBlockStochasticMax_rpow_le_QEnvelope
        hP hStruct hm N m Q a ω
  simpa [terminalCoarseBlockStochasticMax, weak] using
    lintegral_enorm_rpow_two_le_terminalCoarseBlockStochasticQEnvelope_polynomial_convolution_of_highMoment
      hP hStruct hP4 hm μ Q hNm hQ weak a hHM hweak hM hpoint

/--
Source labels `e.Nstar`, `M_m^st`, `a.HM`, and `l.union.bound`: after choosing
the logarithmic buffer exponent large enough, the terminal stochastic maximum
has the buffered `2 / Q` moment bound.
-/
theorem exists_bufferExponent_lintegral_enorm_rpow_two_terminalCoarseBlockStochasticMax_le
    {d : ℕ} [NeZero d] {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) {η : ℝ} (hη : 0 < η) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        {P : Homogenization.Book.Ch04.CoeffLaw d}
        (hP : Homogenization.Book.Ch04.LawCarrier P)
        (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
        (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
        (Q : Homogenization.TriadicCube d) {N m : ℕ},
          N ≤ m → Q.scale = (m : ℤ) →
          B * Real.logb 3
              (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) ≤
            ((m - N : ℕ) : ℝ) →
          ∀ (a : Ω → Homogenization.RegCoeffField d),
            MeasureTheory.AEStronglyMeasurable
              (terminalCoarseBlockStochasticMax hP hStruct hc N m Q a) μ →
            HighCenteredMomentEstimate hm μ N
              (intermediateCoarseBlockDeviation hP hStruct a) →
              ∫⁻ ω, ‖terminalCoarseBlockStochasticMax hP hStruct hc N m Q a ω‖ₑ ^
                  (2 : ℝ) ∂ μ ≤
                (ENNReal.ofReal η) ^ ((2 : ℝ) / hm.Q) := by
  obtain ⟨B, hB_one, hB⟩ :=
    exists_bufferExponent_highCenteredMoment_convolutionEnvelope_le hm hη
  refine ⟨B, hB_one, ?_⟩
  intro Ω _ P hP hStruct hP4 μ _ Q N m hNm hQ hbuf a hM hHM
  let T : ℝ := Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4
  let n : ℕ := m - N
  have hT : 1 ≤ T := by
    simpa [T] using one_le_initialWidetildeTheta_of_P4 hP hStruct hP4
  have henv :
      hm.C_Q * (((2 + T : ℝ) ^ hm.Q) *
        (((n : ℝ) + 1) *
          (3 : ℝ) ^
            (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
              (n : ℝ)))) ≤ η :=
    hB (T := T) (n := n) hT (by simpa [T, n] using hbuf)
  have henv' :
      (((2 + T : ℝ) ^ hm.Q) *
          (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - N : ℕ) : ℝ))))) ≤ η := by
    simpa [T, n, Nat.cast_add, Nat.cast_one, mul_assoc, mul_comm, mul_left_comm]
      using henv
  have hsecond :=
    lintegral_enorm_rpow_two_terminalCoarseBlockStochasticMax_le_polynomial_convolution_of_highMoment
      hP hStruct hP4 hm μ Q hNm hQ a hM hHM
  have hp_nonneg : 0 ≤ (2 : ℝ) / hm.Q := by
    exact div_nonneg (by norm_num) (le_of_lt (highCenteredMoment_Q_pos hm))
  exact hsecond.trans <|
    ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal henv') hp_nonneg

/--
Source labels `e.Nstar`, `M_m^st`, `a.HM`, and `l.union.bound`: manuscript
form of the terminal stochastic maximal estimate with
`m >= N + ceil(B log_3(2+T))`.
-/
theorem exists_bufferExponent_lintegral_enorm_rpow_two_terminalCoarseBlockStochasticMax_le_of_Nstar
    {d : ℕ} [NeZero d] {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) {η : ℝ} (hη : 0 < η) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        {P : Homogenization.Book.Ch04.CoeffLaw d}
        (hP : Homogenization.Book.Ch04.LawCarrier P)
        (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
        (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
        (Q : Homogenization.TriadicCube d) {N m : ℕ},
          Q.scale = (m : ℤ) →
          N + Nat.ceil
              (B * Real.logb 3
                (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) ≤
            m →
          ∀ (a : Ω → Homogenization.RegCoeffField d),
            MeasureTheory.AEStronglyMeasurable
              (terminalCoarseBlockStochasticMax hP hStruct hc N m Q a) μ →
            HighCenteredMomentEstimate hm μ N
              (intermediateCoarseBlockDeviation hP hStruct a) →
              ∫⁻ ω, ‖terminalCoarseBlockStochasticMax hP hStruct hc N m Q a ω‖ₑ ^
                  (2 : ℝ) ∂ μ ≤
                (ENNReal.ofReal η) ^ ((2 : ℝ) / hm.Q) := by
  obtain ⟨B, hB_one, hB⟩ :=
    exists_bufferExponent_lintegral_enorm_rpow_two_terminalCoarseBlockStochasticMax_le
      hm hη
  refine ⟨B, hB_one, ?_⟩
  intro Ω _ P hP hStruct hP4 μ _ Q N m hQ hNstar a hM hHM
  let T : ℝ := Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4
  have hNm : N ≤ m := by omega
  have hNstarT :
      N + Nat.ceil (B * Real.logb 3 (2 + T)) ≤ m := by
    simpa [T] using hNstar
  have hceil_gap :
      Nat.ceil (B * Real.logb 3 (2 + T)) ≤ m - N := by
    omega
  have hbuf :
      B * Real.logb 3 (2 + T) ≤ ((m - N : ℕ) : ℝ) := by
    exact (Nat.ceil_le).mp hceil_gap
  exact
    hB hP hStruct hP4 μ Q hNm hQ
      (by simpa [T] using hbuf) a hM hHM

/--
Source labels `l.union.bound`, `M_m^st`, and `M_m^{<N}`: final
source-facing stochastic maximal union bound.  The terminal contribution is
the literal source-weighted coarse-block maximum, while the subthreshold
contribution is supplied only through the old polynomial high-contrast input
recorded in `a.HM.subthreshold`.
-/
theorem exists_bufferExponent_lintegral_enorm_rpow_two_terminalCoarseBlockStochasticMax_add_subthresholdMax_le_of_Nstar
    {d : ℕ} [NeZero d] {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (sub : SubthresholdPolynomialMomentParameters) {η_st : ℝ} (hη_st : 0 < η_st) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        {P : Homogenization.Book.Ch04.CoeffLaw d}
        (hP : Homogenization.Book.Ch04.LawCarrier P)
        (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
        (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
        (Q : Homogenization.TriadicCube d) {N m : ℕ},
          Q.scale = (m : ℤ) →
          N + Nat.ceil
              (B * Real.logb 3
                (2 + Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)) ≤
            m →
          ∀ (a : Ω → Homogenization.RegCoeffField d)
            (M_sub : ℕ → Ω → ℝ),
            MeasureTheory.AEStronglyMeasurable
              (terminalCoarseBlockStochasticMax hP hStruct hc N m Q a) μ →
            HighCenteredMomentEstimate hm μ N
              (intermediateCoarseBlockDeviation hP hStruct a) →
            SubthresholdPolynomialMomentEstimate hc sub μ
              (Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4)
              N M_sub →
              ∫⁻ ω, ‖terminalCoarseBlockStochasticMax hP hStruct hc N m Q a ω‖ₑ ^
                  (2 : ℝ) ∂ μ +
                ∫⁻ ω, ‖M_sub m ω‖ₑ ^ (2 : ℝ) ∂ μ ≤ ENNReal.ofReal η_st := by
  let η_half : ℝ := η_st / 2
  have hη_half_pos : 0 < η_half := by
    dsimp [η_half]
    linarith
  let η_terminal : ℝ := η_half ^ (hm.Q / 2)
  have hη_terminal_pos : 0 < η_terminal := by
    dsimp [η_terminal, η_half]
    exact Real.rpow_pos_of_pos hη_half_pos (hm.Q / 2)
  obtain ⟨Bst, hBst_one, hBst⟩ :=
    exists_bufferExponent_lintegral_enorm_rpow_two_terminalCoarseBlockStochasticMax_le_of_Nstar
      hm hη_terminal_pos
  obtain ⟨Bsub, hBsub_one, hBsub⟩ :=
    exists_bufferExponent_lintegral_enorm_rpow_two_subthresholdMax_le_of_Nstar
      hc sub hη_half_pos
  let B : ℝ := max Bst Bsub
  have hB_one : 1 ≤ B := by
    exact hBst_one.trans (le_max_left Bst Bsub)
  refine ⟨B, hB_one, ?_⟩
  intro Ω _ P hP hStruct hP4 μ _ Q N m hQ hNstar a M_sub hM hHM hsub
  let T : ℝ := Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4
  have hT : 1 ≤ T := by
    simpa [T] using one_le_initialWidetildeTheta_of_P4 hP hStruct hP4
  have hNstar_terminal :
      N + Nat.ceil (Bst * Real.logb 3 (2 + T)) ≤ m :=
    nstar_le_of_bufferExponent_le
      (B₀ := Bst) (B := B) (T := T) (N := N) (m := m)
      (le_max_left Bst Bsub) hT (by simpa [B, T] using hNstar)
  have hNstar_sub :
      N + Nat.ceil (Bsub * Real.logb 3 (2 + T)) ≤ m :=
    nstar_le_of_bufferExponent_le
      (B₀ := Bsub) (B := B) (T := T) (N := N) (m := m)
      (le_max_right Bst Bsub) hT (by simpa [B, T] using hNstar)
  have hterminal :=
    hBst hP hStruct hP4 μ Q hQ
      (by simpa [T, η_terminal, η_half] using hNstar_terminal) a hM hHM
  have hterminal_half :
      ∫⁻ ω, ‖terminalCoarseBlockStochasticMax hP hStruct hc N m Q a ω‖ₑ ^
          (2 : ℝ) ∂ μ ≤ ENNReal.ofReal η_half := by
    exact hterminal.trans
      (le_of_eq (by
        simpa [η_terminal, η_half] using
          ofReal_highCenteredMoment_halfBudget_rpow_eq hm hη_st))
  have hsub_half :
      ∫⁻ ω, ‖M_sub m ω‖ₑ ^ (2 : ℝ) ∂ μ ≤ ENNReal.ofReal η_half := by
    exact hBsub μ hT (by simpa [T, η_half] using hNstar_sub) hsub
  have hhalf_nonneg : 0 ≤ η_half := le_of_lt hη_half_pos
  calc
    ∫⁻ ω, ‖terminalCoarseBlockStochasticMax hP hStruct hc N m Q a ω‖ₑ ^
          (2 : ℝ) ∂ μ +
        ∫⁻ ω, ‖M_sub m ω‖ₑ ^ (2 : ℝ) ∂ μ
        ≤ ENNReal.ofReal η_half + ENNReal.ofReal η_half :=
          add_le_add hterminal_half hsub_half
    _ = ENNReal.ofReal η_st := by
          rw [← ENNReal.ofReal_add hhalf_nonneg hhalf_nonneg]
          congr 1
          dsimp [η_half]
          ring

end Homogenization.HighContrast.EntryScale
