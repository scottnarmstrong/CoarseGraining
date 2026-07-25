import Homogenization.HighContrast.EntryScale.BadMaximal
import Homogenization.HighContrast.EntryScale.Section52Index
import Homogenization.HighContrast.EntryScale.TerminalLowerEdge.P1

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open scoped Matrix.Norms.Elementwise
open scoped ENNReal

namespace Homogenization.HighContrast.EntryScale

noncomputable section

/--
Factored high-scale Section 5.2 sqrt-theta sum with the first-power
source-max split.  The common min/bad response factor is pulled out behind the
exact scalar edge-weight-loss coefficient.
-/
theorem section52LargeScale_terminalPositiveExcess_highSum_mul_le_edgeWeightLoss_mul_sqrt_thetaAtScale_sourceMax_min_one_add_badEventTruncation_mul_response
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {N m : ℕ} {sLower sUpper : ℝ}
    (hsLower : 0 ≤ sLower) (hsUpper : 0 ≤ sUpper)
    (a : Ω → Homogenization.RegCoeffField d) (ω : Ω)
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField (a ω))
    {J : ℝ} (hJ_nonneg : 0 ≤ J) :
    let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let sourceMax := terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a
    let B : ℝ :=
      2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
        (min (sourceMax ω) 1 * J +
          badEventTruncation sourceMax ω * J)
    let lowerSlot : {n : ℤ // n ∈ S} → ℝ := fun n =>
      let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa [Q, Homogenization.originCube] using section52LargeScaleSet_mem_le_m n.2)
      let lowerExcess : Homogenization.TriadicCube d → ℝ := fun R =>
        max
          (Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).lowerRight -
            (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
          0
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 *
        (σ * parents.sup' hparents lowerExcess) * J
    let upperSlot : {n : ℤ // n ∈ S} → ℝ := fun n =>
      let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa [Q, Homogenization.originCube] using section52LargeScaleSet_mem_le_m n.2)
      let upperExcess : Homogenization.TriadicCube d → ℝ := fun R =>
        max
          (Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).upperLeft -
            hP.barSigmaAtScale hStruct (m : ℤ))
          0
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1 *
        (σ⁻¹ * parents.sup' hparents upperExcess) * J
    let weightLossSup : {n : ℤ // n ∈ S} → ℝ := fun n =>
      let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa [Q, Homogenization.originCube] using section52LargeScaleSet_mem_le_m n.2)
      parents.sup' hparents
        (fun R =>
          ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n.1) R)⁻¹).toReal)
    let edgeWeightLoss : ℝ :=
      S.attach.sum fun n =>
        if N ≤ Int.toNat n.1 then
          (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 +
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1) *
            weightLossSup n
        else 0
    (S.attach.sum fun n =>
      if N ≤ Int.toNat n.1 then lowerSlot n + upperSlot n else 0) ≤
      edgeWeightLoss * B := by
  classical
  dsimp only
  let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let source : Ω → ℝ := terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a
  let B : ℝ :=
    2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
      (min (source ω) 1 * J + badEventTruncation source ω * J)
  let lowerSlot : {n : ℤ // n ∈ S} → ℝ := fun n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa [Q, Homogenization.originCube] using section52LargeScaleSet_mem_le_m n.2)
    let lowerExcess : Homogenization.TriadicCube d → ℝ := fun R =>
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).lowerRight -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 *
      (σ * parents.sup' hparents lowerExcess) * J
  let upperSlot : {n : ℤ // n ∈ S} → ℝ := fun n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa [Q, Homogenization.originCube] using section52LargeScaleSet_mem_le_m n.2)
    let upperExcess : Homogenization.TriadicCube d → ℝ := fun R =>
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).upperLeft -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1 *
      (σ⁻¹ * parents.sup' hparents upperExcess) * J
  let weightLossSup : {n : ℤ // n ∈ S} → ℝ := fun n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa [Q, Homogenization.originCube] using section52LargeScaleSet_mem_le_m n.2)
    parents.sup' hparents
      (fun R =>
        ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n.1) R)⁻¹).toReal)
  let edgeWeightLoss : ℝ :=
    S.attach.sum fun n =>
      if N ≤ Int.toNat n.1 then
        (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 +
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1) *
          weightLossSup n
      else 0
  have hsum :
      (S.attach.sum fun n =>
        if N ≤ Int.toNat n.1 then lowerSlot n + upperSlot n else 0) ≤
        S.attach.sum fun n =>
          (if N ≤ Int.toNat n.1 then
            (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 +
              Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1) *
              weightLossSup n
          else 0) * B := by
    refine Finset.sum_le_sum ?_
    intro n _hn
    by_cases hNn : N ≤ Int.toNat n.1
    · have hlower :
          lowerSlot n ≤
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 *
              weightLossSup n * B := by
        simpa [S, Q, σ, source, B, lowerSlot, weightLossSup] using
          section52LargeScaleWeight_terminalLowerPositiveExcess_sup_mul_le_weightLossSup_mul_two_mul_sqrt_thetaAtScale_mul_sourceMax_min_one_add_badEventTruncation_mul_response
            (hP := hP) (hStruct := hStruct) (hP4 := hP4) (hc := hc)
            (N := N) (m := m) (s := sLower) hsLower
            (n := n.1) n.2 hNn a ω ha hJ_nonneg
      have hupper :
          upperSlot n ≤
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1 *
              weightLossSup n * B := by
        simpa [S, Q, σ, source, B, upperSlot, weightLossSup] using
          section52LargeScaleWeight_terminalUpperPositiveExcess_sup_mul_le_weightLossSup_mul_two_mul_sqrt_thetaAtScale_mul_sourceMax_min_one_add_badEventTruncation_mul_response
            (hP := hP) (hStruct := hStruct) (hP4 := hP4) (hc := hc)
            (N := N) (m := m) (s := sUpper) hsUpper
            (n := n.1) n.2 hNn a ω ha hJ_nonneg
      have hcombined :
          lowerSlot n + upperSlot n ≤
            ((Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 +
              Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1) *
              weightLossSup n) * B := by
        calc
          lowerSlot n + upperSlot n ≤
              Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 *
                weightLossSup n * B +
              Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1 *
                weightLossSup n * B := add_le_add hlower hupper
          _ = ((Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 +
              Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1) *
              weightLossSup n) * B := by ring
      simpa [hNn] using hcombined
    · simp [hNn]
  have hfactor :
      (S.attach.sum fun n =>
        (if N ≤ Int.toNat n.1 then
          (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 +
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1) *
            weightLossSup n
        else 0) * B) = edgeWeightLoss * B := by
    dsimp [edgeWeightLoss]
    rw [Finset.sum_mul]
  exact hsum.trans_eq hfactor

/--
Full Section 5.2 sqrt-theta terminal positive-excess sum with the first-power
source-max split, decomposed into the low-scale remainder and the exact
high-scale edge-weight-loss coefficient.  This is the summed-weight sharp
normalization hybrid: summed `edgeWeightLoss`, sharp `2 * sqrt(theta_m)`, and
first-power `min(sourceMax,1) + badEventTruncation(sourceMax)` source factor.
-/
theorem section52LargeScale_terminalPositiveExcess_allSum_mul_le_lowSum_add_edgeWeightLoss_mul_sqrt_thetaAtScale_sourceMax_min_one_add_badEventTruncation_mul_response
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {N m : ℕ} {sLower sUpper : ℝ}
    (hsLower : 0 < sLower) (hsUpper : 0 < sUpper)
    (a : Ω → Homogenization.RegCoeffField d) (ω : Ω)
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField (a ω))
    {J : ℝ} (hJ_nonneg : 0 ≤ J) :
    let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let sourceMax := terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a
    let B : ℝ :=
      2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
        (min (sourceMax ω) 1 * J +
          badEventTruncation sourceMax ω * J)
    let lowerSlot : {n : ℤ // n ∈ S} → ℝ := fun n =>
      let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa [Q, Homogenization.originCube] using section52LargeScaleSet_mem_le_m n.2)
      let lowerExcess : Homogenization.TriadicCube d → ℝ := fun R =>
        max
          (Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).lowerRight -
            (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
          0
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 *
        (σ * parents.sup' hparents lowerExcess) * J
    let upperSlot : {n : ℤ // n ∈ S} → ℝ := fun n =>
      let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa [Q, Homogenization.originCube] using section52LargeScaleSet_mem_le_m n.2)
      let upperExcess : Homogenization.TriadicCube d → ℝ := fun R =>
        max
          (Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).upperLeft -
            hP.barSigmaAtScale hStruct (m : ℤ))
          0
      Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1 *
        (σ⁻¹ * parents.sup' hparents upperExcess) * J
    let lowSum : ℝ :=
      S.attach.sum fun n =>
        if N ≤ Int.toNat n.1 then 0 else lowerSlot n + upperSlot n
    let weightLossSup : {n : ℤ // n ∈ S} → ℝ := fun n =>
      let parents := Homogenization.descendantsAtScale Q n.1
      let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty Q
          (by simpa [Q, Homogenization.originCube] using section52LargeScaleSet_mem_le_m n.2)
      parents.sup' hparents
        (fun R =>
          ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n.1) R)⁻¹).toReal)
    let edgeWeightLoss : ℝ :=
      S.attach.sum fun n =>
        if N ≤ Int.toNat n.1 then
          (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 +
            Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1) *
            weightLossSup n
        else 0
    (S.attach.sum fun n => lowerSlot n + upperSlot n) ≤
      lowSum + edgeWeightLoss * B := by
  classical
  dsimp only
  let S := Homogenization.Book.Ch05.Section52.section52LargeScaleSet m
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let source : Ω → ℝ := terminalSpectralPositivePartSourceMax hP hStruct hc N m Q a
  let B : ℝ :=
    2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) *
      (min (source ω) 1 * J + badEventTruncation source ω * J)
  let lowerSlot : {n : ℤ // n ∈ S} → ℝ := fun n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa [Q, Homogenization.originCube] using section52LargeScaleSet_mem_le_m n.2)
    let lowerExcess : Homogenization.TriadicCube d → ℝ := fun R =>
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).lowerRight -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 *
      (σ * parents.sup' hparents lowerExcess) * J
  let upperSlot : {n : ℤ // n ∈ S} → ℝ := fun n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa [Q, Homogenization.originCube] using section52LargeScaleSet_mem_le_m n.2)
    let upperExcess : Homogenization.TriadicCube d → ℝ := fun R =>
      max
        (Homogenization.Book.Ch02.matrixNorm
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R) (a ω)).upperLeft -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0
    Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1 *
      (σ⁻¹ * parents.sup' hparents upperExcess) * J
  let lowSum : ℝ :=
    S.attach.sum fun n =>
      if N ≤ Int.toNat n.1 then 0 else lowerSlot n + upperSlot n
  let highSum : ℝ :=
    S.attach.sum fun n =>
      if N ≤ Int.toNat n.1 then lowerSlot n + upperSlot n else 0
  let weightLossSup : {n : ℤ // n ∈ S} → ℝ := fun n =>
    let parents := Homogenization.descendantsAtScale Q n.1
    let hparents : parents.Nonempty :=
      Homogenization.descendantsAtScale_nonempty Q
        (by simpa [Q, Homogenization.originCube] using section52LargeScaleSet_mem_le_m n.2)
    parents.sup' hparents
      (fun R =>
        ((terminalStochasticWeakWeight (d := d) hc m (Int.toNat n.1) R)⁻¹).toReal)
  let edgeWeightLoss : ℝ :=
    S.attach.sum fun n =>
      if N ≤ Int.toNat n.1 then
        (Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sLower m n.1 +
          Homogenization.Book.Ch05.Section52.section52LargeScaleWeight sUpper m n.1) *
          weightLossSup n
      else 0
  have hhigh : highSum ≤ edgeWeightLoss * B := by
    simpa [S, Q, σ, source, B, lowerSlot, upperSlot, highSum,
      weightLossSup, edgeWeightLoss] using
      section52LargeScale_terminalPositiveExcess_highSum_mul_le_edgeWeightLoss_mul_sqrt_thetaAtScale_sourceMax_min_one_add_badEventTruncation_mul_response
        (hP := hP) (hStruct := hStruct) (hP4 := hP4) (hc := hc)
        (N := N) (m := m) (sLower := sLower) (sUpper := sUpper)
        hsLower.le hsUpper.le a ω ha hJ_nonneg
  have hdecomp :
      (S.attach.sum fun n => lowerSlot n + upperSlot n) =
        lowSum + highSum := by
    dsimp [lowSum, highSum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro n _hn
    by_cases hNn : N ≤ Int.toNat n.1
    · simp [hNn]
    · simp [hNn]
  calc
    (S.attach.sum fun n => lowerSlot n + upperSlot n)
        = lowSum + highSum := hdecomp
    _ ≤ lowSum + edgeWeightLoss * B := by
        calc
          lowSum + highSum = highSum + lowSum := by ring
          _ ≤ edgeWeightLoss * B + lowSum := add_le_add_left hhigh lowSum
          _ = lowSum + edgeWeightLoss * B := by ring

end

end Homogenization.HighContrast.EntryScale
