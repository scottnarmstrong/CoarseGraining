import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.ScalarReduction
import Homogenization.Book.Ch05.Theorems.Section56.VarianceEstimateQuadratic.Triangle
import Homogenization.Book.Ch05.Theorems.Section57.ProbeEnvelope
import Homogenization.HighContrast.EntryScale.NoDropResponse
import Homogenization.HighContrast.EntryScale.BadMaximal.P1
import Homogenization.HighContrast.EntryScale.BadMaximal.P2

open MeasureTheory
open scoped ENNReal
open scoped Matrix.Norms.Elementwise
open scoped MatrixOrder

namespace Homogenization.HighContrast.EntryScale

noncomputable section

/--
The terminal full-norm envelope of the same library normalized fluctuation matrix.
This is an upper envelope for the spectral positive part; the exact
`‖M⁺‖ ≤ ‖M‖` bridge is intentionally kept separate.
-/
noncomputable def terminalFullBlockFluctuationNormAtScale
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.RegCoeffField d) : ℝ :=
  fullBlockOperatorNorm
    (Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationMatrix
      hP hStruct (m : ℤ) (Homogenization.cubeSet Q) a)

/--
One-block source-to-envelope bridge for the bad maximal: the manuscript
positive-part observable is controlled by the corresponding full operator
norm of the same library terminal normalized fluctuation matrix.
-/
theorem terminalSpectralPositivePartAtScale_le_terminalFullBlockFluctuationNormAtScale
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.RegCoeffField d) :
    terminalSpectralPositivePartAtScale hP hStruct m Q a ≤
      terminalFullBlockFluctuationNormAtScale hP hStruct m Q a := by
  exact
    fullBlockOperatorNorm_posPart_le
      (Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationMatrix
        hP hStruct (m : ℤ) (Homogenization.cubeSet Q) a)

/--
Source labels `M_m^st` and `e.drift.general`: for a fixed large scale `j`,
the library's terminal full-norm fluctuation is bounded by the terminal stochastic
centered fluctuation plus the deterministic annealed drift.
-/
theorem terminalFullBlockFluctuationNormAtScale_le_centered_add_drift
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (j m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.RegCoeffField d) :
    terminalFullBlockFluctuationNormAtScale hP hStruct m Q a ≤
      (terminalCoarseBlockDeviation hP hStruct m
          (fun x : Homogenization.RegCoeffField d => x) j Q a).toReal +
        terminalAnnealedFullBlockDriftAtScales hP hStruct j m := by
  let Dm := scalarFullBlockNormalizerMatrixAtScale hP hStruct m
  let A := Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube Q a
  let Aj :=
    Homogenization.toFullBlockMat
      (Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale
        hP hStruct (j : ℤ))
  let Am :=
    Homogenization.toFullBlockMat
      (Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale
        hP hStruct (m : ℤ))
  let C := Dm * scalarCenteredFullBlockMatrixAtScale hP hStruct j A * Dm
  let R := Dm * (Aj - Am) * Dm
  let M :=
    Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationMatrix
      hP hStruct (m : ℤ)
        (Homogenization.cubeSet Q) a
  have hsplit :
      M = C + R := by
    dsimp [M,
      Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationMatrix,
      Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube,
      Homogenization.coarseFullBlockMatrixObservable,
      scalarFullBlockNormalizerMatrixAtScale,
      scalarCenteredFullBlockMatrixAtScale,
      Dm, A, Aj, Am, C, R]
    noncomm_ring
  have htriangle :
      fullBlockOperatorNorm M ≤ fullBlockOperatorNorm C + fullBlockOperatorNorm R := by
    rw [hsplit]
    exact fullBlockOperatorNorm_add_le C R
  have hcenter_toReal :
      (terminalCoarseBlockDeviation hP hStruct m
          (fun x : Homogenization.RegCoeffField d => x) j Q a).toReal =
        fullBlockOperatorNorm C := by
    unfold terminalCoarseBlockDeviation terminalCenteredFullBlockDeviation
      coarseFullBlockMatrixAtCubeProcess scalarCenteredFullBlockMatrixAtScale
    change (ENNReal.ofReal (fullBlockOperatorNorm C)).toReal =
      fullBlockOperatorNorm C
    exact ENNReal.toReal_ofReal (fullBlockOperatorNorm_nonneg C)
  have hdrift :
      terminalAnnealedFullBlockDriftAtScales hP hStruct j m =
        fullBlockOperatorNorm R := by
    rfl
  calc
    terminalFullBlockFluctuationNormAtScale hP hStruct m Q a =
        fullBlockOperatorNorm M := by
          rfl
    _ ≤ fullBlockOperatorNorm C + fullBlockOperatorNorm R := htriangle
    _ =
        (terminalCoarseBlockDeviation hP hStruct m
          (fun x : Homogenization.RegCoeffField d => x) j Q a).toReal +
        terminalAnnealedFullBlockDriftAtScales hP hStruct j m := by
          rw [hcenter_toReal, hdrift]

/--
Source label `M_m^st`: any descendant block appearing in the manuscript
finite maximum is selected by the terminal stochastic maximal observable.

This is the arbitrary-descendant version of the origin-cube selection lemma
used in the response estimate.
-/
theorem weighted_terminalCoarseBlockDeviation_toReal_le_terminalCoarseBlockStochasticMax
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hc : HighContrastExponents d) {N m j : ℕ}
    (Q : Homogenization.TriadicCube d)
    (a : Ω → Homogenization.RegCoeffField d) (ω : Ω)
    {R : Homogenization.TriadicCube d}
    (hj : j ∈ Finset.Icc N m)
    (hR : R ∈ Homogenization.descendantsAtDepth Q (m - j)) :
    (terminalStochasticWeakWeight (d := d) hc m j R).toReal *
        (terminalCoarseBlockDeviation hP hStruct m a j R ω).toReal ≤
      terminalCoarseBlockStochasticMax hP hStruct hc N m Q a ω := by
  classical
  let weak : ℕ → Homogenization.TriadicCube d → ENNReal :=
    terminalStochasticWeakWeight (d := d) hc m
  let dev := terminalCoarseBlockDeviation hP hStruct m a
  let env :=
    terminalCoarseBlockStochasticEnvelope hP hStruct N m Q weak a
  have hinner :
      weak j R * dev j R ω ≤
        (Homogenization.descendantsAtDepth Q (m - j)).sup
          (fun S => weak j S * dev j S ω) := by
    exact Finset.le_sup
      (s := Homogenization.descendantsAtDepth Q (m - j))
      (f := fun S => weak j S * dev j S ω) hR
  have hterm : weak j R * dev j R ω ≤ env ω := by
    have houter :
        (Homogenization.descendantsAtDepth Q (m - j)).sup
            (fun S => weak j S * dev j S ω) ≤
          env ω := by
      dsimp [env, terminalCoarseBlockStochasticEnvelope]
      exact Finset.le_sup
        (s := Finset.Icc N m)
        (f := fun i =>
          (Homogenization.descendantsAtDepth Q (m - i)).sup
            (fun S => weak i S * dev i S ω))
        hj
    exact hinner.trans houter
  have hweak_bound : ∀ i ∈ Finset.Icc N m,
      ∀ S ∈ Homogenization.descendantsAtDepth Q (m - i),
        weak i S ≤
          ENNReal.ofReal ((3 : ℝ) ^
            (-hc.rhoM * ((m - i : ℕ) : ℝ))) := by
    intro i _hi S _hS
    dsimp [weak, terminalStochasticWeakWeight]
    exact le_rfl
  have henv_ne_top : env ω ≠ ⊤ := by
    simpa [env, weak] using
      terminalCoarseBlockStochasticEnvelope_ne_top_of_weak_le_terminal
        hP hStruct N m Q weak a hweak_bound ω
  have htoReal :
      (weak j R * dev j R ω).toReal ≤ (env ω).toReal :=
    ENNReal.toReal_mono henv_ne_top hterm
  simpa [terminalCoarseBlockStochasticMax,
    terminalCoarseBlockStochasticMaxOfWeak, env, weak, dev,
    ENNReal.toReal_mul] using htoReal

/--
Source labels `e.M.def`, `M_m^st`, and `p.nodrop.CR.badMaximal`: the
literal high-scale spectral positive-part maximal observable is pointwise
bounded by the stochastic, subthreshold, and deterministic drift split.
-/
theorem terminalSpectralPositivePartSourceMax_le_terminalBadMaximalSplitEnvelope
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hc : HighContrastExponents d) {N m : ℕ} (hNm : N ≤ m)
    (Q : Homogenization.TriadicCube d)
    (a : Ω → Homogenization.RegCoeffField d) (M_sub : ℕ → Ω → ℝ) :
    ∀ ω,
      terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a ω ≤
        terminalBadMaximalSplitEnvelope hP hStruct hc hNm Q a M_sub ω := by
  classical
  intro ω
  let B : ℝ :=
    terminalBadMaximalSplitEnvelope hP hStruct hc hNm Q a M_sub ω
  have hB_nonneg : 0 ≤ B := by
    dsimp [B, terminalBadMaximalSplitEnvelope]
    have hstoch :=
      terminalCoarseBlockStochasticMax_nonneg hP hStruct hc N m Q a ω
    have hsub : 0 ≤ |M_sub m ω| := abs_nonneg (M_sub m ω)
    have hdrift := terminalBadMaximalDriftSup_nonneg hP hStruct hc hNm
    nlinarith
  have henv_le :
      terminalSpectralPositivePartSourceEnvelope hP hStruct hc N m Q a ω ≤
        ENNReal.ofReal B := by
    dsimp [terminalSpectralPositivePartSourceEnvelope]
    refine Finset.sup_le ?_
    intro j hj
    refine Finset.sup_le ?_
    intro R hR
    apply ENNReal.ofReal_le_ofReal
    let w : ℝ := (terminalStochasticWeakWeight (d := d) hc m j R).toReal
    let spec : ℝ := terminalSpectralPositivePartAtScale hP hStruct m R (a ω)
    let full : ℝ := terminalFullBlockFluctuationNormAtScale hP hStruct m R (a ω)
    let dev : ℝ≥0∞ := terminalCoarseBlockDeviation hP hStruct m a j R ω
    let drift : ℝ := terminalAnnealedFullBlockDriftAtScales hP hStruct j m
    have hw_nonneg : 0 ≤ w := ENNReal.toReal_nonneg
    have hspec_full : spec ≤ full := by
      dsimp [spec, full]
      exact
        terminalSpectralPositivePartAtScale_le_terminalFullBlockFluctuationNormAtScale
          hP hStruct m R (a ω)
    have hfull : full ≤ dev.toReal + drift := by
      dsimp [full, dev, drift]
      exact
        terminalFullBlockFluctuationNormAtScale_le_centered_add_drift
          hP hStruct j m R (a ω)
    have hstoch :
        w * dev.toReal ≤
          terminalCoarseBlockStochasticMax hP hStruct hc N m Q a ω := by
      dsimp [w, dev]
      exact
        weighted_terminalCoarseBlockDeviation_toReal_le_terminalCoarseBlockStochasticMax
          hP hStruct hc Q a ω hj hR
    have hw_eq :
        w = (3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ)) := by
      dsimp [w, terminalStochasticWeakWeight]
      exact ENNReal.toReal_ofReal
        (le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3)
          (-hc.rhoM * ((m - j : ℕ) : ℝ))))
    have hdrift :
        w * drift ≤ terminalBadMaximalDriftSup hP hStruct hc hNm := by
      rw [hw_eq]
      rw [show -hc.rhoM * ((m - j : ℕ) : ℝ) =
          -(hc.rhoM * ((m - j : ℕ) : ℝ)) by ring]
      dsimp [drift]
      exact
        weighted_terminalAnnealedFullBlockDriftAtScales_le_terminalBadMaximalDriftSup
          hP hStruct hc hNm hj
    calc
      w * spec ≤ w * full := mul_le_mul_of_nonneg_left hspec_full hw_nonneg
      _ ≤ w * (dev.toReal + drift) := mul_le_mul_of_nonneg_left hfull hw_nonneg
      _ = w * dev.toReal + w * drift := by ring
      _ ≤ terminalCoarseBlockStochasticMax hP hStruct hc N m Q a ω +
            terminalBadMaximalDriftSup hP hStruct hc hNm :=
          add_le_add hstoch hdrift
      _ ≤ terminalCoarseBlockStochasticMax hP hStruct hc N m Q a ω +
            |M_sub m ω| + terminalBadMaximalDriftSup hP hStruct hc hNm := by
          nlinarith [abs_nonneg (M_sub m ω)]
      _ = B := by
          rfl
  have htoReal :
      (terminalSpectralPositivePartSourceEnvelope hP hStruct hc N m Q a ω).toReal ≤
        (ENNReal.ofReal B).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top henv_le
  calc
    terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a ω =
        (terminalSpectralPositivePartSourceEnvelope hP hStruct hc N m Q a ω).toReal := by
          rfl
    _ ≤ (ENNReal.ofReal B).toReal := htoReal
    _ = B := ENNReal.toReal_ofReal hB_nonneg

/--
Source labels `e.M.def`, `M_m^st`, and `a.HM`: the literal source maximal
observable has the high `Q` moment required for the bad-event truncation.
-/
theorem memLp_terminalSpectralPositivePartSourceMax_origin_highMoment
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) {N m : ℕ} (hNm : N ≤ m)
    (hHM :
      HighCenteredMomentEstimate hm P N
        (intermediateCoarseBlockDeviation hP hStruct
          (fun x : Homogenization.RegCoeffField d => x))) :
    MemLp
      (terminalSpectralPositivePartSourceMax hP hStruct hc N m
        (Homogenization.originCube d (m : ℤ))
        (fun x : Homogenization.RegCoeffField d => x))
      (ENNReal.ofReal hm.Q) P := by
  classical
  letI : IsProbabilityMeasure P := hP.isProbability
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let source : Homogenization.RegCoeffField d → ℝ :=
    terminalSpectralPositivePartSourceMax hP hStruct hc N m Q
      (fun x : Homogenization.RegCoeffField d => x)
  let stochastic : Homogenization.RegCoeffField d → ℝ :=
    terminalCoarseBlockStochasticMax hP hStruct hc N m Q
      (fun x : Homogenization.RegCoeffField d => x)
  let drift : ℝ := terminalBadMaximalDriftSup hP hStruct hc hNm
  have hstochastic :
      MemLp stochastic (ENNReal.ofReal hm.Q) P := by
    simpa [stochastic, Q] using
      memLp_terminalCoarseBlockStochasticMax_origin_highMoment
        hP hStruct hP4 hm hNm hHM
  have hdrift :
      MemLp (fun _ : Homogenization.RegCoeffField d => drift)
        (ENNReal.ofReal hm.Q) P :=
    MeasureTheory.memLp_const drift
  have henv :
      MemLp (fun ω : Homogenization.RegCoeffField d => stochastic ω + drift)
        (ENNReal.ofReal hm.Q) P :=
    hstochastic.add hdrift
  have hsource_meas : AEStronglyMeasurable source P := by
    simpa [source, Q] using
      aestronglyMeasurable_terminalSpectralPositivePartSourceMax_origin hP hStruct hc N m
  exact henv.of_le hsource_meas
    (Filter.Eventually.of_forall fun ω => by
      have hsource_nonneg : 0 ≤ source ω := by
        simpa [source, Q] using
          terminalSpectralPositivePartSourceMax_nonneg hP hStruct hc N m Q
            (fun x : Homogenization.RegCoeffField d => x) ω
      have hstoch_nonneg : 0 ≤ stochastic ω := by
        simpa [stochastic, Q] using
          terminalCoarseBlockStochasticMax_nonneg hP hStruct hc N m Q
            (fun x : Homogenization.RegCoeffField d => x) ω
      have hdrift_nonneg : 0 ≤ drift := by
        simpa [drift] using terminalBadMaximalDriftSup_nonneg hP hStruct hc hNm
      have henv_nonneg : 0 ≤ stochastic ω + drift :=
        add_nonneg hstoch_nonneg hdrift_nonneg
      have hsource_le : source ω ≤ stochastic ω + drift := by
        have hle :=
          terminalSpectralPositivePartSourceMax_le_terminalBadMaximalSplitEnvelope
            hP hStruct hc hNm Q (fun x : Homogenization.RegCoeffField d => x)
            (fun _ _ => (0 : ℝ)) ω
        simpa [source, stochastic, drift, Q, terminalBadMaximalSplitEnvelope] using hle
      calc
        ‖terminalSpectralPositivePartSourceMax hP hStruct hc N m
            (Homogenization.originCube d (m : ℤ))
            (fun x : Homogenization.RegCoeffField d => x) ω‖
            = source ω := by
              rw [Real.norm_eq_abs]
              exact abs_of_nonneg hsource_nonneg
        _ ≤ stochastic ω + drift := hsource_le
        _ = ‖stochastic ω + drift‖ := by
              rw [Real.norm_eq_abs, abs_of_nonneg henv_nonneg])

end

end Homogenization.HighContrast.EntryScale
