import Homogenization.HighContrast.EntryScale.ResponseFluctuation.P2

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization
open scoped Matrix.Norms.Elementwise


/-!
# Raw high-contrast weak-norm component

Concrete expectation-level weak-norm pieces for the raw
high-contrast centered-response inequalities.  This file deliberately proves
only component estimates from the library's/current lemmas; it does not introduce a
new source, input, or feed wrapper.
-/


namespace Homogenization.HighContrast.EntryScale

noncomputable section

open scoped Matrix.Norms.L2Operator in
theorem aemeasurable_maxDescendantBMatrixNormCoeffFieldAtScale_sub_nat
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (Q : Homogenization.TriadicCube d) (n : ℕ) :
    AEMeasurable
      (fun a : Homogenization.RegCoeffField d =>
        Homogenization.Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
          Q (Q.scale - (n : ℤ)) a) P := by
  classical
  have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
  let sDesc := Homogenization.descendantsAtScale Q (Q.scale - (n : ℤ))
  have hsDesc : sDesc.Nonempty :=
    Homogenization.descendantsAtScale_nonempty Q (sub_le_self Q.scale hn)
  have hsup :
      AEMeasurable
        (sDesc.sup' hsDesc
          (fun R (a : Homogenization.RegCoeffField d) =>
            Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix
                (Homogenization.cubeSet R) a).upperLeft)) P := by
    refine
      Homogenization.Book.Ch04.RestrictionLawCarrier.aemeasurable_finset_sup'
        hsDesc ?_
    intro R _hR
    simpa [Homogenization.Book.Ch02.matrixNorm,
      Matrix.l2_opNorm_toEuclideanCLM] using
      (hP.aemeasurable_coarseB_cubeSet R).norm
  have hfin :
      AEMeasurable
        (fun a : Homogenization.RegCoeffField d =>
          Homogenization.Book.Ch02.finsetSupReal sDesc
            (fun R =>
              Homogenization.Book.Ch02.matrixNorm
                (Homogenization.coarseBlockMatrix
                  (Homogenization.cubeSet R) a).upperLeft)) P := by
    convert hsup using 1
    ext a
    rw [Finset.sup'_apply]
    exact
      (Homogenization.Book.Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup'
        sDesc hsDesc
        (fun R =>
          Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix
              (Homogenization.cubeSet R) a).upperLeft))
  refine hfin.congr ?_
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  simpa [sDesc] using
    (Homogenization.Book.Ch04.RestrictionLawCarrier.maxDescendantBMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae
        (a := a) ha Q (Q.scale - (n : ℤ))).symm

open scoped Matrix.Norms.L2Operator in
theorem aemeasurable_maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_sub_nat
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (Q : Homogenization.TriadicCube d) (n : ℕ) :
    AEMeasurable
      (fun a : Homogenization.RegCoeffField d =>
        Homogenization.Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
          Q (Q.scale - (n : ℤ)) a) P := by
  classical
  have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
  let sDesc := Homogenization.descendantsAtScale Q (Q.scale - (n : ℤ))
  have hsDesc : sDesc.Nonempty :=
    Homogenization.descendantsAtScale_nonempty Q (sub_le_self Q.scale hn)
  have hsup :
      AEMeasurable
        (sDesc.sup' hsDesc
          (fun R (a : Homogenization.RegCoeffField d) =>
            Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix
                (Homogenization.cubeSet R) a).lowerRight)) P := by
    refine
      Homogenization.Book.Ch04.RestrictionLawCarrier.aemeasurable_finset_sup'
        hsDesc ?_
    intro R _hR
    simpa [Homogenization.Book.Ch02.matrixNorm,
      Matrix.l2_opNorm_toEuclideanCLM] using
      (hP.aemeasurable_coarseSigmaStarInv_cubeSet R).norm
  have hfin :
      AEMeasurable
        (fun a : Homogenization.RegCoeffField d =>
          Homogenization.Book.Ch02.finsetSupReal sDesc
            (fun R =>
              Homogenization.Book.Ch02.matrixNorm
                (Homogenization.coarseBlockMatrix
                  (Homogenization.cubeSet R) a).lowerRight)) P := by
    convert hsup using 1
    ext a
    rw [Finset.sup'_apply]
    exact
      (Homogenization.Book.Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup'
        sDesc hsDesc
        (fun R =>
          Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix
              (Homogenization.cubeSet R) a).lowerRight))
  refine hfin.congr ?_
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  simpa [sDesc] using
    (Homogenization.Book.Ch04.RestrictionLawCarrier.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae
        (a := a) ha Q (Q.scale - (n : ℤ))).symm

theorem aemeasurable_upperSmallSqrtTailCoeffField
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (m : ℕ) {s : ℝ} (hs : 0 < s) :
    AEMeasurable
      (fun a : Homogenization.RegCoeffField d =>
        Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
          (d := d) m s a) P := by
  classical
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  refine
    aemeasurable_of_tendsto_metrizable_ae (Filter.atTop : Filter ℕ)
      (f := fun N a =>
        ∑ j ∈ Finset.range N,
          Homogenization.Book.Ch02.geometricWeight s 1 (j + m) *
            Real.rpow
              (Homogenization.Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
                Q (-(j : ℤ)) a)
              (1 / 2 : ℝ))
      (g := fun a =>
        ∑' j : ℕ,
          Homogenization.Book.Ch02.geometricWeight s 1 (j + m) *
            Real.rpow
              (Homogenization.Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
                Q (-(j : ℤ)) a)
              (1 / 2 : ℝ)) ?_ ?_
  · intro N
    refine Finset.aemeasurable_fun_sum (μ := P)
      (f := fun j (a : Homogenization.RegCoeffField d) =>
        Homogenization.Book.Ch02.geometricWeight s 1 (j + m) *
          Real.rpow
            (Homogenization.Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
              Q (-(j : ℤ)) a)
            (1 / 2 : ℝ)) (Finset.range N) ?_
    intro j _hj
    have hscale :
        Q.scale - ((j + m : ℕ) : ℤ) = -(j : ℤ) := by
      dsimp [Q]
      simp [Homogenization.originCube]
    have hmax :
        AEMeasurable
          (fun a : Homogenization.RegCoeffField d =>
            Homogenization.Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
              Q (-(j : ℤ)) a) P := by
      convert
        aemeasurable_maxDescendantBMatrixNormCoeffFieldAtScale_sub_nat
          hP Q (j + m) using 1
      ext a
      rw [hscale]
    have hrpow : Measurable (fun x : ℝ => Real.rpow x (1 / 2 : ℝ)) :=
      (Real.continuous_rpow_const (by positivity : 0 ≤ (1 / 2 : ℝ))).measurable
    exact
      (hrpow.comp_aemeasurable hmax).const_mul
        (Homogenization.Book.Ch02.geometricWeight s 1 (j + m))
  · exact Filter.Eventually.of_forall fun a =>
      by
        have htailQ :
            Summable
              (fun j : ℕ =>
                Homogenization.Book.Ch02.geometricWeight s 1 (j + m) *
                  Real.rpow
                    (Homogenization.Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
                      Q (Q.scale - ((j + m : ℕ) : ℤ)) a)
                    (1 / 2 : ℝ)) := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            ((summable_nat_add_iff m).mpr
              (Homogenization.Book.Ch04.RestrictionLawCarrier.summable_weighted_maxDescendantBMatrixNormCoeffFieldAtScale
                  Q a hs))
        have htail :
            Summable
              (fun j : ℕ =>
                Homogenization.Book.Ch02.geometricWeight s 1 (j + m) *
                  Real.rpow
                    (Homogenization.Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
                      Q (-(j : ℤ)) a)
                    (1 / 2 : ℝ)) := by
          refine htailQ.congr ?_
          intro j
          have hscale :
              Q.scale - ((j + m : ℕ) : ℤ) = -(j : ℤ) := by
            dsimp [Q]
            simp [Homogenization.originCube]
          rw [hscale]
        exact HasSum.tendsto_sum_nat htail.hasSum

theorem aemeasurable_lowerSmallSqrtTailCoeffField
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (m : ℕ) {s : ℝ} (hs : 0 < s) :
    AEMeasurable
      (fun a : Homogenization.RegCoeffField d =>
        Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
          (d := d) m s a) P := by
  classical
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  refine
    aemeasurable_of_tendsto_metrizable_ae (Filter.atTop : Filter ℕ)
      (f := fun N a =>
        ∑ j ∈ Finset.range N,
          Homogenization.Book.Ch02.geometricWeight s 1 (j + m) *
            Real.rpow
              (Homogenization.Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
                Q (-(j : ℤ)) a)
              (1 / 2 : ℝ))
      (g := fun a =>
        ∑' j : ℕ,
          Homogenization.Book.Ch02.geometricWeight s 1 (j + m) *
            Real.rpow
              (Homogenization.Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
                Q (-(j : ℤ)) a)
              (1 / 2 : ℝ)) ?_ ?_
  · intro N
    refine Finset.aemeasurable_fun_sum (μ := P)
      (f := fun j (a : Homogenization.RegCoeffField d) =>
        Homogenization.Book.Ch02.geometricWeight s 1 (j + m) *
          Real.rpow
            (Homogenization.Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
              Q (-(j : ℤ)) a)
            (1 / 2 : ℝ)) (Finset.range N) ?_
    intro j _hj
    have hscale :
        Q.scale - ((j + m : ℕ) : ℤ) = -(j : ℤ) := by
      dsimp [Q]
      simp [Homogenization.originCube]
    have hmax :
        AEMeasurable
          (fun a : Homogenization.RegCoeffField d =>
            Homogenization.Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
              Q (-(j : ℤ)) a) P := by
      convert
        aemeasurable_maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_sub_nat
          hP Q (j + m) using 1
      ext a
      rw [hscale]
    have hrpow : Measurable (fun x : ℝ => Real.rpow x (1 / 2 : ℝ)) :=
      (Real.continuous_rpow_const (by positivity : 0 ≤ (1 / 2 : ℝ))).measurable
    exact
      (hrpow.comp_aemeasurable hmax).const_mul
        (Homogenization.Book.Ch02.geometricWeight s 1 (j + m))
  · exact Filter.Eventually.of_forall fun a =>
      by
        have htailQ :
            Summable
              (fun j : ℕ =>
                Homogenization.Book.Ch02.geometricWeight s 1 (j + m) *
                  Real.rpow
                    (Homogenization.Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
                      Q (Q.scale - ((j + m : ℕ) : ℤ)) a)
                    (1 / 2 : ℝ)) := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            ((summable_nat_add_iff m).mpr
              (Homogenization.Book.Ch04.RestrictionLawCarrier.summable_weighted_maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
                  Q a hs))
        have htail :
            Summable
              (fun j : ℕ =>
                Homogenization.Book.Ch02.geometricWeight s 1 (j + m) *
                  Real.rpow
                    (Homogenization.Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
                      Q (-(j : ℤ)) a)
                    (1 / 2 : ℝ)) := by
          refine htailQ.congr ?_
          intro j
          have hscale :
              Q.scale - ((j + m : ℕ) : ℤ) = -(j : ℤ) := by
            dsimp [Q]
            simp [Homogenization.originCube]
          rw [hscale]
        exact HasSum.tendsto_sum_nat htail.hasSum

/--
Scale-normalized laws shift the terminal scalar
`\widehat\sigma` from normalized scale `m` to original scale `k + m`.
This is the first transport lemma needed for the local-baseline lower-edge
replacement.
-/
theorem sigmaHatAtScale_restrictionScaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P) (k m : ℕ) :
    Homogenization.Book.Ch05.sigmaHatAtScale
        (hP.scaleNormalized k) (hStruct.scaleNormalized k) (m : ℤ) =
      Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct
        ((k + m : ℕ) : ℤ) := by
  simp [Homogenization.Book.Ch05.sigmaHatAtScale,
    hP.barSigmaAtScale_restrictionScaleNormalizedLaw hStruct k m,
    hP.barSigmaStarAtScale_restrictionScaleNormalizedLaw hStruct k m]

/--
The special terminal gradient vector is invariant under scale normalization,
with the normalized terminal scale transported from `m` to original scale
`k + m`.
-/
theorem specialPAtScale_restrictionScaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (k m : ℕ) (e : Homogenization.Vec d) :
    Homogenization.Book.Ch05.specialPAtScale
        (hP.scaleNormalized k) (hStruct.scaleNormalized k) (m : ℤ) e =
      Homogenization.Book.Ch05.specialPAtScale hP hStruct
        ((k + m : ℕ) : ℤ) e := by
  change
    Real.rpow
        (Homogenization.Book.Ch05.sigmaHatAtScale
          (hP.scaleNormalized k) (hStruct.scaleNormalized k) (m : ℤ))
        (-(1 / 2 : ℝ)) • e =
      Real.rpow
        (Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct
          ((k + m : ℕ) : ℤ))
        (-(1 / 2 : ℝ)) • e
  rw [sigmaHatAtScale_restrictionScaleNormalizedLaw hP hStruct k m]

/--
The special terminal flux vector is invariant under scale normalization,
with the normalized terminal scale transported from `m` to original scale
`k + m`.
-/
theorem specialQAtScale_restrictionScaleNormalizedLaw
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (k m : ℕ) (e : Homogenization.Vec d) :
    Homogenization.Book.Ch05.specialQAtScale
        (hP.scaleNormalized k) (hStruct.scaleNormalized k) (m : ℤ) e =
      Homogenization.Book.Ch05.specialQAtScale hP hStruct
        ((k + m : ℕ) : ℤ) e := by
  change
    Real.rpow
        (Homogenization.Book.Ch05.sigmaHatAtScale
          (hP.scaleNormalized k) (hStruct.scaleNormalized k) (m : ℤ))
        (1 / 2 : ℝ) • e =
      Real.rpow
        (Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct
          ((k + m : ℕ) : ℤ))
        (1 / 2 : ℝ) • e
  rw [sigmaHatAtScale_restrictionScaleNormalizedLaw hP hStruct k m]

/--
Scale-normalization transport in the form used by a window `k <= m`: normalized
scale `m-k` corresponds to original scale `m`.
-/
theorem sigmaHatAtScale_restrictionScaleNormalizedLaw_of_le
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    {k m : ℕ} (hkm : k ≤ m) :
    Homogenization.Book.Ch05.sigmaHatAtScale
        (hP.scaleNormalized k) (hStruct.scaleNormalized k)
        ((m - k : ℕ) : ℤ) =
      Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ) := by
  have h := sigmaHatAtScale_restrictionScaleNormalizedLaw hP hStruct k (m - k)
  have hsum : k + (m - k) = m := Nat.add_sub_of_le hkm
  simpa [hsum] using h

/--
Special gradient vector transport in the form used by a window `k <= m`.
-/
theorem specialPAtScale_restrictionScaleNormalizedLaw_of_le
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    {k m : ℕ} (hkm : k ≤ m) (e : Homogenization.Vec d) :
    Homogenization.Book.Ch05.specialPAtScale
        (hP.scaleNormalized k) (hStruct.scaleNormalized k)
        ((m - k : ℕ) : ℤ) e =
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e := by
  have h := specialPAtScale_restrictionScaleNormalizedLaw hP hStruct k (m - k) e
  have hsum : k + (m - k) = m := Nat.add_sub_of_le hkm
  simpa [hsum] using h

/--
Special flux vector transport in the form used by a window `k <= m`.
-/
theorem specialQAtScale_restrictionScaleNormalizedLaw_of_le
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    {k m : ℕ} (hkm : k ≤ m) (e : Homogenization.Vec d) :
    Homogenization.Book.Ch05.specialQAtScale
        (hP.scaleNormalized k) (hStruct.scaleNormalized k)
        ((m - k : ℕ) : ℤ) e =
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e := by
  have h := specialQAtScale_restrictionScaleNormalizedLaw hP hStruct k (m - k) e
  have hsum : k + (m - k) = m := Nat.add_sub_of_le hkm
  simpa [hsum] using h

/--
Source labels `p.HC.CR` and `e.P.bound`: the library's scale-zero scalar weight for
the law normalized at the left endpoint is exactly the corrected local
weak-norm scalar on the original window.
-/
theorem coarseFluctuationScalarWeightAtScale_restrictionScaleNormalizedLaw_of_le
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    {k m : ℕ} (hkm : k ≤ m) :
    coarseFluctuationScalarWeightAtScale
        (hP.scaleNormalized k) (hStruct.scaleNormalized k) (m - k) =
      localWeakNormScalarWeightAtScales hP hStruct k m := by
  let M : ℕ := m - k
  have hsigma :
      Homogenization.Book.Ch05.sigmaHatAtScale
          (hP.scaleNormalized k) (hStruct.scaleNormalized k) (M : ℤ) =
        Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ) := by
    simpa [M] using sigmaHatAtScale_restrictionScaleNormalizedLaw_of_le
      (hP := hP) (hStruct := hStruct) hkm
  have hlower :
      (hP.scaleNormalized k).barSigmaStarAtScale
          (hStruct.scaleNormalized k) (0 : ℤ) =
        hP.barSigmaStarAtScale hStruct (k : ℤ) := by
    simpa using
      hP.barSigmaStarAtScale_restrictionScaleNormalizedLaw hStruct k 0
  have hupper :
      (hP.scaleNormalized k).barSigmaAtScale
          (hStruct.scaleNormalized k) (0 : ℤ) =
        hP.barSigmaAtScale hStruct (k : ℤ) := by
    simpa using
      hP.barSigmaAtScale_restrictionScaleNormalizedLaw hStruct k 0
  change
    Homogenization.Book.Ch05.sigmaHatAtScale
        (hP.scaleNormalized k) (hStruct.scaleNormalized k) (M : ℤ) *
        ((hP.scaleNormalized k).barSigmaStarAtScale
          (hStruct.scaleNormalized k) (0 : ℤ))⁻¹ +
      (Homogenization.Book.Ch05.sigmaHatAtScale
        (hP.scaleNormalized k) (hStruct.scaleNormalized k) (M : ℤ))⁻¹ *
        (hP.scaleNormalized k).barSigmaAtScale
          (hStruct.scaleNormalized k) (0 : ℤ) =
      Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ) *
        (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ +
      (Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ *
        hP.barSigmaAtScale hStruct (k : ℤ)
  rw [hsigma, hlower, hupper]

/--
Source labels `p.HC.CR` and `e.P.bound`: the local weak-norm scalar
coefficient is nonnegative on a valid scale window.
-/
theorem localWeakNormScalarWeightAtScales_nonneg_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k ≤ m) :
    0 ≤ localWeakNormScalarWeightAtScales hP hStruct k m := by
  rw [localWeakNormScalarWeightAtScales_eq_terminalPAtScales_of_P4
    hP hStruct hP4 k m]
  exact terminalPAtScales_nonneg_of_P4 hP hStruct hP4 hkm

/--
Source labels `p.HC.CR` and `e.tau.sum.absorb`: integrability of the
response-defect square appearing in the special-vector weak-norm split.  This
is the library's finite weighted response-defect integrability theorem with all
parent/descendant response integrability inputs discharged from `(P4)`.
-/
theorem integrable_defectSum_sq_special_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hstat : Homogenization.Book.Ch04.RestrictionStationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (_hkm : k < m) (e : Homogenization.Vec d) :
    let β := section53CoarseFluctuationBeta hP4
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    MeasureTheory.Integrable
      (fun a : Homogenization.RegCoeffField d =>
        (∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
          Real.rpow (3 : ℝ)
              (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
            Real.sqrt
              (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
                (m : ℤ) n p_e q_e a)) ^ 2) P := by
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let S : Finset ℤ := Finset.Icc ((k : ℤ) + 1) (m : ℤ)
  let w : ℤ → ℝ :=
    fun n =>
      Real.rpow (3 : ℝ)
        (-β * (Int.toNat ((m : ℤ) - n) : ℝ))
  have hk_nonneg : 0 ≤ (k : ℤ) := by
    exact_mod_cast Nat.zero_le k
  have hBlockM :
      MeasureTheory.Integrable
        (Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          (Homogenization.originCube d (m : ℤ)) p_e q_e) P := by
    have hFull :
        MeasureTheory.Integrable
          (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube
            (Homogenization.originCube d (m : ℤ))) P :=
      Homogenization.Book.Ch05.Section52.originBlockIntegrableAtScale_from_P4
        hP hStruct hP4 m
    exact
      hP.integrable_restrictionResponseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
        (Homogenization.originCube d (m : ℤ)) p_e q_e hFull
  have hDesc :
      ∀ n ∈ S,
        ∀ R, R ∈ Homogenization.descendantsAtScale
            (Homogenization.originCube d (m : ℤ)) n →
          MeasureTheory.Integrable
            (Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p_e q_e) P := by
    intro n hn R hR
    have hn_bounds : (k : ℤ) + 1 ≤ n ∧ n ≤ (m : ℤ) :=
      Finset.mem_Icc.mp (by simpa [S] using hn)
    have hn_nonneg : 0 ≤ n := by
      linarith [hk_nonneg]
    have hOrigin_nat :
        MeasureTheory.Integrable
          (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube
            (Homogenization.originCube d ((Int.toNat n : ℕ) : ℤ))) P :=
      Homogenization.Book.Ch05.Section52.originBlockIntegrableAtScale_from_P4
        hP hStruct hP4 (Int.toNat n)
    have hOrigin :
        MeasureTheory.Integrable
          (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube
            (Homogenization.originCube d n)) P := by
      simpa [Int.toNat_of_nonneg hn_nonneg] using hOrigin_nat
    have hBlockR :
        MeasureTheory.Integrable
          (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube R) P :=
      hP.integrable_coarseFullBlockMatrixAtCube_of_mem_descendantsAtScale_originCube
        hstat hn_nonneg hn_bounds.2 hR hOrigin
    exact
      hP.integrable_restrictionResponseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
        R p_e q_e hBlockR
  have hw : ∀ n ∈ S, 0 ≤ w n := by
    intro n _hn
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  simpa [β, p_e, q_e, S, w] using
    integrable_sq_weighted_sqrt_responseDefectAverageAtScale
      hP hk_nonneg w p_e q_e hw hBlockM hDesc

/--
Source labels `p.HC.CR` and `e.tau.sum.absorb`: expectation-level conversion
of the local weak-norm additivity-defect slot.  The library supplies the integrated
Cauchy/stationarity estimate for the concrete special vectors; this theorem
keeps the raw local scalar `P_{k,m}` and the explicit `5 * β⁻¹` constant.

This is the tau component of the raw weak-norm inequality.  The terminal
fluctuation and lower-edge positive-excess components are separate raw
weak-norm slots and are not discarded here.
-/
theorem localWeakNormScalarWeightAtScales_mul_integral_defectSum_sq_special_le_weightedTauSumAtScales
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hstat : Homogenization.Book.Ch04.RestrictionStationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Homogenization.Vec d) :
    let β := section53CoarseFluctuationBeta hP4
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    localWeakNormScalarWeightAtScales hP hStruct k m *
        ∫ a,
          (∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
            Real.rpow (3 : ℝ)
                (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
              Real.sqrt
                (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
                  (m : ℤ) n p_e q_e a)) ^ 2 ∂P
      ≤
        (5 * localWeakNormScalarWeightAtScales hP hStruct k m * β⁻¹) *
          weightedTauSumAtScales hP hStruct hP4 k m e := by
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let c := localWeakNormScalarWeightAtScales hP hStruct k m
  let T := weightedTauSumAtScales hP hStruct hP4 k m e
  have hbase :
      ∫ a,
          (∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
            Real.rpow (3 : ℝ)
                (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
              Real.sqrt
                (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
                  (m : ℤ) n p_e q_e a)) ^ 2 ∂P
        ≤ (5 * β⁻¹) * T := by
    simpa [β, p_e, q_e, T] using
      integral_defectSum_sq_special_le_beta_inv_weightedTauSumAtScales
        hP hstat hStruct hP4 hkm e
  have hc_nonneg : 0 ≤ c := by
    simpa [c] using
      localWeakNormScalarWeightAtScales_nonneg_of_P4
        hP hStruct hP4 hkm.le
  calc
    c *
        (∫ a,
          (∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
            Real.rpow (3 : ℝ)
                (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
              Real.sqrt
                (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
                  (m : ℤ) n p_e q_e a)) ^ 2 ∂P)
        ≤ c * ((5 * β⁻¹) * T) :=
      mul_le_mul_of_nonneg_left hbase hc_nonneg
    _ = (5 * c * β⁻¹) * T := by
      ring

/--
Source labels `p.HC.CR`, `e.W.first.sum`, and `e.tau.sum.absorb`:
expectation-level local weak-norm component for the paired mismatch-square
term.  The canonical terminal slot, the local tau slot with explicit
`5 * β⁻¹` prefactor, and the local positive-excess/lower-edge integral are
kept as separate terms.

The two integrability hypotheses are the concrete analytic obligations needed
to pass from the pointwise raw split to expectations; the inequality itself is
obtained from the local paired-square lemma and the library's integrated defect-square
estimate, not assumed as a weak-norm wrapper.
-/
theorem integral_paired_mismatchTermSquares_special_le_rawHighContrastWeakNormSlots_local
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hstat : Homogenization.Book.Ch04.RestrictionStationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Homogenization.Vec d)
    (hLowerEdge_int :
      let β := section53CoarseFluctuationBeta hP4
      let s' := hP4.sLower + β
      let t' := hP4.sUpper + β
      let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
      let p_e :=
        Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
      let q_e :=
        Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
      let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
      let lowerExcess := fun a : Homogenization.RegCoeffField d =>
        max
          ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
            (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹)
          0
      let upperExcess := fun a : Homogenization.RegCoeffField d =>
        max
          (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
            hP.barSigmaAtScale hStruct (k : ℤ))
          0
      let defectSum := fun a : Homogenization.RegCoeffField d =>
        ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
          Real.rpow (3 : ℝ)
              (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
            Real.sqrt
              (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
                (m : ℤ) n p_e q_e a)
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          (σ * lowerExcess a + σ⁻¹ * upperExcess a) * defectSum a ^ 2) P) :
    let β := section53CoarseFluctuationBeta hP4
    let s := hP4.sLower + 2 * β
    let s' := hP4.sLower + β
    let t := hP4.sUpper + 2 * β
    let t' := hP4.sUpper + β
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let defectSum := fun a : Homogenization.RegCoeffField d =>
      ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
        Real.rpow (3 : ℝ)
            (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          Real.sqrt
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
              (m : ℤ) n p_e q_e a)
    let lowerExcess := fun a : Homogenization.RegCoeffField d =>
      max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹)
        0
    let upperExcess := fun a : Homogenization.RegCoeffField d =>
      max
        (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
          hP.barSigmaAtScale hStruct (k : ℤ))
        0
    let T_m := 1 + contrastExcessAtScale hP hStruct m
    let S_m := coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m
    ∫ a,
        σ *
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientMismatchTermAtScale
              (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
          σ⁻¹ *
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxMismatchTermAtScale
              (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2 ∂P
      ≤
        T_m * S_m +
          (5 * localWeakNormScalarWeightAtScales hP hStruct k m * β⁻¹) *
            weightedTauSumAtScales hP hStruct hP4 k m e +
          ∫ a, (σ * lowerExcess a + σ⁻¹ * upperExcess a) *
            defectSum a ^ 2 ∂P +
          T_m * 0 := by
  dsimp only
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let s' := hP4.sLower + β
  let t := hP4.sUpper + 2 * β
  let t' := hP4.sUpper + β
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let D := fun a : Homogenization.RegCoeffField d =>
    ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
      Real.rpow (3 : ℝ)
          (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
        Real.sqrt
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
            (m : ℤ) n p_e q_e a)
  let lowerExcess := fun a : Homogenization.RegCoeffField d =>
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹)
      0
  let upperExcess := fun a : Homogenization.RegCoeffField d =>
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
        hP.barSigmaAtScale hStruct (k : ℤ))
      0
  let lowerEdge := fun a : Homogenization.RegCoeffField d =>
    (σ * lowerExcess a + σ⁻¹ * upperExcess a) * D a ^ 2
  let c := localWeakNormScalarWeightAtScales hP hStruct k m
  let T_tau := weightedTauSumAtScales hP hStruct hP4 k m e
  let T_m : ℝ := 1 + contrastExcessAtScale hP hStruct m
  let S_m : ℝ := coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m
  let terminal : ℝ := T_m * S_m
  let lhs := fun a : Homogenization.RegCoeffField d =>
    σ *
        (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientMismatchTermAtScale
          (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
      σ⁻¹ *
        (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxMismatchTermAtScale
          (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
  let rhs := fun a : Homogenization.RegCoeffField d =>
    terminal + c * D a ^ 2 + lowerEdge a + T_m * 0
  have hDsq_int' : MeasureTheory.Integrable (fun a => D a ^ 2) P := by
    simpa [D, β, p_e, q_e] using
      integrable_defectSum_sq_special_of_P4 hP hstat hStruct hP4 hkm e
  have hLowerEdge_int' : MeasureTheory.Integrable lowerEdge P := by
    simpa [lowerEdge, D, lowerExcess, upperExcess, β, s', t', Q, p_e, q_e, σ]
      using hLowerEdge_int
  have hpoint : ∀ a, lhs a ≤ rhs a := by
    intro a
    simpa [lhs, rhs, terminal, c, D, lowerEdge, lowerExcess, upperExcess,
      β, s, s', t, t', Q, p_e, q_e, σ, T_m, S_m] using
      paired_mismatchTermSquares_special_le_rawHighContrastWeakNormContribution_local
        hP hStruct hP4 k m e a
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, Homogenization.Book.Ch05.sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hlhs_nonneg : ∀ a, 0 ≤ lhs a := by
    intro a
    dsimp [lhs]
    exact add_nonneg
      (mul_nonneg hσ_nonneg (sq_nonneg _))
      (mul_nonneg hσ_inv_nonneg (sq_nonneg _))
  have hterminal_int :
      MeasureTheory.Integrable (fun _ : Homogenization.RegCoeffField d => terminal) P :=
    MeasureTheory.integrable_const terminal
  have hcD_int : MeasureTheory.Integrable (fun a => c * D a ^ 2) P :=
    hDsq_int'.const_mul c
  have hterminal_cD_int :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d => terminal + c * D a ^ 2) P :=
    hterminal_int.add hcD_int
  have hterminal_cD_lower_int :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          terminal + c * D a ^ 2 + lowerEdge a) P :=
    hterminal_cD_int.add hLowerEdge_int'
  have hTzero_int :
      MeasureTheory.Integrable (fun _ : Homogenization.RegCoeffField d => T_m * 0) P :=
    MeasureTheory.integrable_const (T_m * 0)
  have hrhs_int : MeasureTheory.Integrable rhs P := by
    exact hterminal_cD_lower_int.add hTzero_int
  have hintegral_point : ∫ a, lhs a ∂P ≤ ∫ a, rhs a ∂P :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall hlhs_nonneg) hrhs_int
      (Filter.Eventually.of_forall hpoint)
  have hrhs_eq :
      ∫ a, rhs a ∂P =
        terminal + c * (∫ a, D a ^ 2 ∂P) +
          ∫ a, lowerEdge a ∂P + T_m * 0 := by
    have h1 :
        ∫ a, rhs a ∂P =
          ∫ a, terminal + c * D a ^ 2 + lowerEdge a ∂P +
            ∫ _a : Homogenization.RegCoeffField d, T_m * 0 ∂P := by
      dsimp [rhs]
      exact MeasureTheory.integral_add hterminal_cD_lower_int hTzero_int
    have h2 :
        ∫ a, terminal + c * D a ^ 2 + lowerEdge a ∂P =
          ∫ a, terminal + c * D a ^ 2 ∂P +
            ∫ a, lowerEdge a ∂P := by
      exact MeasureTheory.integral_add hterminal_cD_int hLowerEdge_int'
    have h3 :
        ∫ a, terminal + c * D a ^ 2 ∂P =
          ∫ _a : Homogenization.RegCoeffField d, terminal ∂P +
            ∫ a, c * D a ^ 2 ∂P := by
      exact MeasureTheory.integral_add hterminal_int hcD_int
    have hconst :
        ∫ _a : Homogenization.RegCoeffField d, terminal ∂P = terminal :=
      MeasureTheory.integral_eq_const (μ := P) (c := terminal)
        (Filter.Eventually.of_forall (fun _ => rfl))
    have hzero :
        ∫ _a : Homogenization.RegCoeffField d, T_m * 0 ∂P = T_m * 0 :=
      MeasureTheory.integral_eq_const (μ := P) (c := T_m * 0)
        (Filter.Eventually.of_forall (fun _ => rfl))
    have hmul :
        ∫ a, c * D a ^ 2 ∂P =
          c * ∫ a, D a ^ 2 ∂P :=
      MeasureTheory.integral_const_mul c
        (fun a : Homogenization.RegCoeffField d => D a ^ 2)
    calc
      ∫ a, rhs a ∂P =
          ∫ a, terminal + c * D a ^ 2 + lowerEdge a ∂P +
            ∫ _a : Homogenization.RegCoeffField d, T_m * 0 ∂P := h1
      _ =
          (∫ _a : Homogenization.RegCoeffField d, terminal ∂P +
              ∫ a, c * D a ^ 2 ∂P) +
            ∫ a, lowerEdge a ∂P +
            ∫ _a : Homogenization.RegCoeffField d, T_m * 0 ∂P := by
          rw [h2, h3]
      _ =
          (terminal + c * (∫ a, D a ^ 2 ∂P)) +
            ∫ a, lowerEdge a ∂P +
            ∫ _a : Homogenization.RegCoeffField d, T_m * 0 ∂P := by
          exact congrArg
            (fun x =>
              x + ∫ a, lowerEdge a ∂P +
                ∫ _a : Homogenization.RegCoeffField d, T_m * 0 ∂P)
            (by rw [hconst, hmul])
      _ =
          terminal + c * (∫ a, D a ^ 2 ∂P) +
            ∫ a, lowerEdge a ∂P + T_m * 0 := by
          exact congrArg
            (fun x =>
              terminal + c * (∫ a, D a ^ 2 ∂P) +
                ∫ a, lowerEdge a ∂P + x)
            hzero
  have htau :
      c * (∫ a, D a ^ 2 ∂P) ≤ (5 * c * β⁻¹) * T_tau := by
    simpa [c, D, β, p_e, q_e, T_tau] using
      localWeakNormScalarWeightAtScales_mul_integral_defectSum_sq_special_le_weightedTauSumAtScales
        hP hstat hStruct hP4 hkm e
  calc
    ∫ a, lhs a ∂P
        ≤ terminal + c * (∫ a, D a ^ 2 ∂P) +
          ∫ a, lowerEdge a ∂P + T_m * 0 := by
        simpa [hrhs_eq] using hintegral_point
    _ ≤ terminal + (5 * c * β⁻¹) * T_tau +
          ∫ a, lowerEdge a ∂P + T_m * 0 := by
        linarith

/--
Source label `p.HC.CR`: expectation-level local-to-terminal comparison for
the positive-excess lower-edge piece.  This is the faithful lower-edge
entry point for the terminal good/bad positive-part split, replacing the
stale scale-zero baseline-gap route.
-/
theorem integral_localPositiveExcess_defectSum_sq_special_le_terminalPositiveExcess
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k ≤ m) (e : Homogenization.Vec d)
    (hTerminalEdge_int :
      let β := section53CoarseFluctuationBeta hP4
      let s' := hP4.sLower + β
      let t' := hP4.sUpper + β
      let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
      let p_e :=
        Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
      let q_e :=
        Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
      let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
      let lowerTerminal := fun a : Homogenization.RegCoeffField d =>
        max
          ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
            (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
          0
      let upperTerminal := fun a : Homogenization.RegCoeffField d =>
        max
          (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
            hP.barSigmaAtScale hStruct (m : ℤ))
          0
      let defectSum := fun a : Homogenization.RegCoeffField d =>
        ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
          Real.rpow (3 : ℝ)
              (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
            Real.sqrt
              (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
                (m : ℤ) n p_e q_e a)
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) *
            defectSum a ^ 2) P) :
    let β := section53CoarseFluctuationBeta hP4
    let s' := hP4.sLower + β
    let t' := hP4.sUpper + β
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let lowerLocal := fun a : Homogenization.RegCoeffField d =>
      max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹)
        0
    let upperLocal := fun a : Homogenization.RegCoeffField d =>
      max
        (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
          hP.barSigmaAtScale hStruct (k : ℤ))
        0
    let lowerTerminal := fun a : Homogenization.RegCoeffField d =>
      max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0
    let upperTerminal := fun a : Homogenization.RegCoeffField d =>
      max
        (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0
    let defectSum := fun a : Homogenization.RegCoeffField d =>
      ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
        Real.rpow (3 : ℝ)
            (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          Real.sqrt
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
              (m : ℤ) n p_e q_e a)
    ∫ a, (σ * lowerLocal a + σ⁻¹ * upperLocal a) *
        defectSum a ^ 2 ∂P
      ≤
        ∫ a, (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) *
          defectSum a ^ 2 ∂P := by
  dsimp only at hTerminalEdge_int ⊢
  let β := section53CoarseFluctuationBeta hP4
  let s' := hP4.sLower + β
  let t' := hP4.sUpper + β
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let lowerLocal := fun a : Homogenization.RegCoeffField d =>
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹)
      0
  let upperLocal := fun a : Homogenization.RegCoeffField d =>
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
        hP.barSigmaAtScale hStruct (k : ℤ))
      0
  let lowerTerminal := fun a : Homogenization.RegCoeffField d =>
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
      0
  let upperTerminal := fun a : Homogenization.RegCoeffField d =>
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
        hP.barSigmaAtScale hStruct (m : ℤ))
      0
  let D := fun a : Homogenization.RegCoeffField d =>
    ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
      Real.rpow (3 : ℝ)
          (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
        Real.sqrt
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
            (m : ℤ) n p_e q_e a)
  let localEdge := fun a : Homogenization.RegCoeffField d =>
    (σ * lowerLocal a + σ⁻¹ * upperLocal a) * D a ^ 2
  let terminalEdge := fun a : Homogenization.RegCoeffField d =>
    (σ * lowerTerminal a + σ⁻¹ * upperTerminal a) * D a ^ 2
  have hTerminalEdge_int' : MeasureTheory.Integrable terminalEdge P := by
    simpa [terminalEdge, D, lowerTerminal, upperTerminal, β, s', t', Q,
      p_e, q_e, σ] using hTerminalEdge_int
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, Homogenization.Book.Ch05.sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hlocal_nonneg : ∀ a, 0 ≤ localEdge a := by
    intro a
    dsimp [localEdge]
    exact mul_nonneg
      (add_nonneg
        (mul_nonneg hσ_nonneg (le_max_right _ _))
        (mul_nonneg hσ_inv_nonneg (le_max_right _ _)))
      (sq_nonneg _)
  have hpoint : ∀ a, localEdge a ≤ terminalEdge a := by
    intro a
    have hweight :
        σ * lowerLocal a + σ⁻¹ * upperLocal a ≤
          σ * lowerTerminal a + σ⁻¹ * upperTerminal a := by
      simpa [Q, σ, lowerLocal, lowerTerminal, upperLocal, upperTerminal] using
        localPositiveExcessWeight_le_terminalBaseline_of_P4
          hP hStruct hP4 hkm s' t' a
    exact mul_le_mul_of_nonneg_right hweight (sq_nonneg _)
  exact
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall hlocal_nonneg) hTerminalEdge_int'
      (Filter.Eventually.of_forall hpoint)

end

end Homogenization.HighContrast.EntryScale
