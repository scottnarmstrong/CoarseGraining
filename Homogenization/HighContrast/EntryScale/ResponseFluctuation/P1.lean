import Mathlib.Algebra.Order.Field.GeomSum
import Homogenization.Book.Ch05.Theorems.Section52.P4Integrability
import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations
import Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.ResponseMoment
import Homogenization.HighContrast.EntryScale.DeterministicAlgebra
import Homogenization.HighContrast.EntryScale.MomentConsequences

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization.Book.Ch05.Section54.OneStepContraction


/-!
# Section 5.3 response and fluctuation bridges

Concrete library-facing bridges for the `l.S.and.J` phase of
the high-moment paper (Armstrong–Kuusi–Loher, to appear).  These lemmas
keep the Section 5.3 response exponent explicit and do not replace the terminal
fluctuation or response-moment estimates by wrapper assumptions.
-/


namespace Homogenization.HighContrast.EntryScale

private theorem positivePart_split_le (x base : ℝ) :
    x ≤ base + max (x - base) 0 := by
  by_cases h : x ≤ base
  · exact h.trans (le_add_of_nonneg_right (le_max_right _ _))
  · have hx : base ≤ x := le_of_lt (lt_of_not_ge h)
    have hmax : max (x - base) 0 = x - base := max_eq_left (sub_nonneg.mpr hx)
    linarith

/--
Real positive-part bookkeeping for shifting an ellipticity baseline upward.
If `baseLocal <= baseGlobal`, the local positive excess is bounded by the
scale-global positive excess plus the deterministic baseline gap.
-/
theorem positivePart_sub_le_positivePart_sub_add_baseline_gap
    {x baseLocal baseGlobal : ℝ} (hbase : baseLocal ≤ baseGlobal) :
    max (x - baseLocal) 0 ≤ max (x - baseGlobal) 0 + (baseGlobal - baseLocal) := by
  have hgap_nonneg : 0 ≤ baseGlobal - baseLocal := sub_nonneg.mpr hbase
  by_cases hx : x ≤ baseGlobal
  · have hleft : x - baseLocal ≤ baseGlobal - baseLocal := by linarith
    have hright : max (x - baseGlobal) 0 = 0 := by
      exact max_eq_right (sub_nonpos.mpr hx)
    calc
      max (x - baseLocal) 0 ≤ baseGlobal - baseLocal := max_le hleft hgap_nonneg
      _ = max (x - baseGlobal) 0 + (baseGlobal - baseLocal) := by
        rw [hright]
        ring
  · have hglob : baseGlobal ≤ x := le_of_lt (lt_of_not_ge hx)
    have hlocal : baseLocal ≤ x := hbase.trans hglob
    have hleft : max (x - baseLocal) 0 = x - baseLocal :=
      max_eq_left (sub_nonneg.mpr hlocal)
    have hright : max (x - baseGlobal) 0 = x - baseGlobal :=
      max_eq_left (sub_nonneg.mpr hglob)
    rw [hleft, hright]
    linarith

/--
Real positive-part bookkeeping for moving the baseline downward.  If
`baseSmall <= baseLarge`, then excess above `baseLarge` is dominated by excess
above `baseSmall`.
-/
theorem positivePart_sub_le_positivePart_sub_of_base_le
    {x baseSmall baseLarge : ℝ} (hbase : baseSmall ≤ baseLarge) :
    max (x - baseLarge) 0 ≤ max (x - baseSmall) 0 := by
  by_cases hx : x ≤ baseLarge
  · by_cases hxsmall : x ≤ baseSmall
    · rw [max_eq_right (sub_nonpos.mpr hx)]
      exact le_max_right _ _
    · have hsmall : baseSmall ≤ x := le_of_lt (lt_of_not_ge hxsmall)
      have hright : max (x - baseSmall) 0 = x - baseSmall :=
        max_eq_left (sub_nonneg.mpr hsmall)
      have hleft : max (x - baseLarge) 0 ≤ x - baseSmall := by
        exact max_le (by linarith) (sub_nonneg.mpr hsmall)
      simpa [hright] using hleft
  · have hlarge : baseLarge ≤ x := le_of_lt (lt_of_not_ge hx)
    have hsmall : baseSmall ≤ x := hbase.trans hlarge
    rw [max_eq_left (sub_nonneg.mpr hlarge)]
    rw [max_eq_left (sub_nonneg.mpr hsmall)]
    linarith

/--
Source label `p.HC.CR`: lower inverse ellipticity positive-excess with the
local scale-`k` baseline is bounded by the library's scale-zero positive-excess plus
the deterministic inverse-star baseline gap.
-/
theorem localLowerPositiveExcess_le_zeroBaseline_add_gap_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (rLower : ℝ) (a : Homogenization.RegCoeffField d) :
    max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField
            (Homogenization.originCube d (m : ℤ)) rLower (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹)
        0 ≤
      max
          ((Homogenization.Book.Ch04.lambdaSqCoeffField
              (Homogenization.originCube d (m : ℤ)) rLower (.finite 1) a)⁻¹ -
            (hP.barSigmaStarAtScale hStruct 0)⁻¹)
          0 +
        ((hP.barSigmaStarAtScale hStruct 0)⁻¹ -
          (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹) := by
  have hchain :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.scalarChain_of_P4
      hP hStruct hP4 (Nat.zero_le k)
  exact positivePart_sub_le_positivePart_sub_add_baseline_gap hchain.2.1

/--
Source label `p.HC.CR`: upper ellipticity positive-excess with the local
scale-`k` baseline is bounded by the library's scale-zero positive-excess plus the
deterministic upper baseline gap.
-/
theorem localUpperPositiveExcess_le_zeroBaseline_add_gap_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (rUpper : ℝ) (a : Homogenization.RegCoeffField d) :
    max
        (Homogenization.Book.Ch04.LambdaSqCoeffField
            (Homogenization.originCube d (m : ℤ)) rUpper (.finite 1) a -
          hP.barSigmaAtScale hStruct (k : ℤ))
        0 ≤
      max
          (Homogenization.Book.Ch04.LambdaSqCoeffField
              (Homogenization.originCube d (m : ℤ)) rUpper (.finite 1) a -
            hP.barSigmaAtScale hStruct 0)
          0 +
        (hP.barSigmaAtScale hStruct 0 - hP.barSigmaAtScale hStruct (k : ℤ)) := by
  have hchain :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.scalarChain_of_P4
      hP hStruct hP4 (Nat.zero_le k)
  exact positivePart_sub_le_positivePart_sub_add_baseline_gap hchain.2.2

/--
Source label `p.HC.CR`: lower inverse ellipticity positive-excess with the
local scale-`k` baseline is bounded by the terminal scale-`m` positive-excess.
This is the algebraic replacement for the scale-zero baseline comparison.
-/
theorem localLowerPositiveExcess_le_terminalBaseline_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k ≤ m) (rLower : ℝ)
    (a : Homogenization.RegCoeffField d) :
    max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField
            (Homogenization.originCube d (m : ℤ)) rLower (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹)
        0 ≤
      max
          ((Homogenization.Book.Ch04.lambdaSqCoeffField
              (Homogenization.originCube d (m : ℤ)) rLower (.finite 1) a)⁻¹ -
            (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
          0 := by
  have hchain :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.scalarChain_of_P4
      hP hStruct hP4 hkm
  exact positivePart_sub_le_positivePart_sub_of_base_le hchain.2.1

/--
Source label `p.HC.CR`: upper ellipticity positive-excess with the local
scale-`k` baseline is bounded by the terminal scale-`m` positive-excess.
-/
theorem localUpperPositiveExcess_le_terminalBaseline_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k ≤ m) (rUpper : ℝ)
    (a : Homogenization.RegCoeffField d) :
    max
        (Homogenization.Book.Ch04.LambdaSqCoeffField
            (Homogenization.originCube d (m : ℤ)) rUpper (.finite 1) a -
          hP.barSigmaAtScale hStruct (k : ℤ))
        0 ≤
      max
          (Homogenization.Book.Ch04.LambdaSqCoeffField
              (Homogenization.originCube d (m : ℤ)) rUpper (.finite 1) a -
            hP.barSigmaAtScale hStruct (m : ℤ))
          0 := by
  have hchain :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.scalarChain_of_P4
      hP hStruct hP4 hkm
  exact positivePart_sub_le_positivePart_sub_of_base_le hchain.2.2

/--
Source label `p.HC.CR`: deterministic scalar gap paid when the local
scale-`k` positive-excess baseline is compared with the library's scale-zero baseline.
-/
noncomputable def localPositiveExcessBaselineGapAtScales
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P) (k m : ℕ) : ℝ :=
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  σ *
      ((hP.barSigmaStarAtScale hStruct 0)⁻¹ -
        (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹) +
    σ⁻¹ *
      (hP.barSigmaAtScale hStruct 0 -
        hP.barSigmaAtScale hStruct (k : ℤ))

/--
Source label `p.HC.CR`: the deterministic local-to-zero positive-excess
baseline gap is nonnegative under the P4 scalar chain.
-/
theorem localPositiveExcessBaselineGapAtScales_nonneg_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) :
    0 ≤ localPositiveExcessBaselineGapAtScales hP hStruct k m := by
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let lowerGap : ℝ :=
    (hP.barSigmaStarAtScale hStruct 0)⁻¹ -
      (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹
  let upperGap : ℝ :=
    hP.barSigmaAtScale hStruct 0 -
      hP.barSigmaAtScale hStruct (k : ℤ)
  have hchain :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.scalarChain_of_P4
      hP hStruct hP4 (Nat.zero_le k)
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, Homogenization.Book.Ch05.sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hlowerGap_nonneg : 0 ≤ lowerGap := by
    dsimp [lowerGap]
    exact sub_nonneg.mpr hchain.2.1
  have hupperGap_nonneg : 0 ≤ upperGap := by
    dsimp [upperGap]
    exact sub_nonneg.mpr hchain.2.2
  dsimp [localPositiveExcessBaselineGapAtScales, σ, lowerGap, upperGap]
  exact add_nonneg
    (mul_nonneg hσ_nonneg hlowerGap_nonneg)
    (mul_nonneg hσ_inv_nonneg hupperGap_nonneg)

/--
Source label `p.HC.CR`: the weighted local positive-excess contribution is
bounded by the library's scale-zero positive-excess contribution plus the deterministic
baseline-gap scalar.  This is the pointwise algebra needed before lifting the
local paired-square split to expectations.
-/
theorem localPositiveExcessWeight_le_zeroBaseline_add_gap_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (rLower rUpper : ℝ) (a : Homogenization.RegCoeffField d) :
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let lowerLocal : ℝ :=
      max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField Q rLower (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹)
        0
    let lowerZero : ℝ :=
      max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField Q rLower (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct 0)⁻¹)
        0
    let upperLocal : ℝ :=
      max
        (Homogenization.Book.Ch04.LambdaSqCoeffField Q rUpper (.finite 1) a -
          hP.barSigmaAtScale hStruct (k : ℤ))
        0
    let upperZero : ℝ :=
      max
        (Homogenization.Book.Ch04.LambdaSqCoeffField Q rUpper (.finite 1) a -
          hP.barSigmaAtScale hStruct 0)
        0
    σ * lowerLocal + σ⁻¹ * upperLocal ≤
      σ * lowerZero + σ⁻¹ * upperZero +
        localPositiveExcessBaselineGapAtScales hP hStruct k m := by
  dsimp only
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let lowerLocal : ℝ :=
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q rLower (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹)
      0
  let lowerZero : ℝ :=
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q rLower (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct 0)⁻¹)
      0
  let upperLocal : ℝ :=
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q rUpper (.finite 1) a -
        hP.barSigmaAtScale hStruct (k : ℤ))
      0
  let upperZero : ℝ :=
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q rUpper (.finite 1) a -
        hP.barSigmaAtScale hStruct 0)
      0
  let lowerGap : ℝ :=
    (hP.barSigmaStarAtScale hStruct 0)⁻¹ -
      (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹
  let upperGap : ℝ :=
    hP.barSigmaAtScale hStruct 0 -
      hP.barSigmaAtScale hStruct (k : ℤ)
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, Homogenization.Book.Ch05.sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hlower : lowerLocal ≤ lowerZero + lowerGap := by
    simpa [Q, lowerLocal, lowerZero, lowerGap] using
      localLowerPositiveExcess_le_zeroBaseline_add_gap_of_P4
        hP hStruct hP4 k m rLower a
  have hupper : upperLocal ≤ upperZero + upperGap := by
    simpa [Q, upperLocal, upperZero, upperGap] using
      localUpperPositiveExcess_le_zeroBaseline_add_gap_of_P4
        hP hStruct hP4 k m rUpper a
  calc
    σ * lowerLocal + σ⁻¹ * upperLocal
        ≤ σ * (lowerZero + lowerGap) + σ⁻¹ * (upperZero + upperGap) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hlower hσ_nonneg)
            (mul_le_mul_of_nonneg_left hupper hσ_inv_nonneg)
    _ = σ * lowerZero + σ⁻¹ * upperZero +
          localPositiveExcessBaselineGapAtScales hP hStruct k m := by
        dsimp [localPositiveExcessBaselineGapAtScales, σ, lowerGap, upperGap]
        ring

/--
Source label `p.HC.CR`: the weighted local positive-excess contribution is
bounded by the terminal scale-`m` positive-excess contribution.  This is the
faithful algebraic entry point for the good/bad positive-part maximal split.
-/
theorem localPositiveExcessWeight_le_terminalBaseline_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k ≤ m) (rLower rUpper : ℝ)
    (a : Homogenization.RegCoeffField d) :
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
    let lowerLocal : ℝ :=
      max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField Q rLower (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹)
        0
    let lowerTerminal : ℝ :=
      max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField Q rLower (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
        0
    let upperLocal : ℝ :=
      max
        (Homogenization.Book.Ch04.LambdaSqCoeffField Q rUpper (.finite 1) a -
          hP.barSigmaAtScale hStruct (k : ℤ))
        0
    let upperTerminal : ℝ :=
      max
        (Homogenization.Book.Ch04.LambdaSqCoeffField Q rUpper (.finite 1) a -
          hP.barSigmaAtScale hStruct (m : ℤ))
        0
    σ * lowerLocal + σ⁻¹ * upperLocal ≤
      σ * lowerTerminal + σ⁻¹ * upperTerminal := by
  dsimp only
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let lowerLocal : ℝ :=
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q rLower (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹)
      0
  let lowerTerminal : ℝ :=
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q rLower (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)
      0
  let upperLocal : ℝ :=
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q rUpper (.finite 1) a -
        hP.barSigmaAtScale hStruct (k : ℤ))
      0
  let upperTerminal : ℝ :=
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q rUpper (.finite 1) a -
        hP.barSigmaAtScale hStruct (m : ℤ))
      0
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, Homogenization.Book.Ch05.sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hlower : lowerLocal ≤ lowerTerminal := by
    simpa [Q, lowerLocal, lowerTerminal] using
      localLowerPositiveExcess_le_terminalBaseline_of_P4
        hP hStruct hP4 hkm rLower a
  have hupper : upperLocal ≤ upperTerminal := by
    simpa [Q, upperLocal, upperTerminal] using
      localUpperPositiveExcess_le_terminalBaseline_of_P4
        hP hStruct hP4 hkm rUpper a
  exact add_le_add
    (mul_le_mul_of_nonneg_left hlower hσ_nonneg)
    (mul_le_mul_of_nonneg_left hupper hσ_inv_nonneg)

theorem int_toNat_nat_sub_eq_of_le {j m : ℕ} (hjm : j ≤ m) :
    Int.toNat ((m : ℤ) - (j : ℤ)) = m - j := by
  have hsub : (m : ℤ) - (j : ℤ) = ((m - j : ℕ) : ℤ) := by
    omega
  rw [hsub]
  simp only [Int.toNat_natCast]

private theorem originCube_pred_mem_childCubes_originCube {d : ℕ} (s : ℤ) :
    Homogenization.originCube d (s - 1) ∈
      Homogenization.childCubes (Homogenization.originCube d s) := by
  rw [Homogenization.mem_childCubes_iff]
  refine ⟨fun _ => (1 : Fin 3), ?_⟩
  simp only [Homogenization.originCube]
  apply congrArg₂ Homogenization.TriadicCube.mk
  · rfl
  · funext i
    norm_num

/--
Library geometry bridge: the smaller origin cube is the origin descendant at the
prescribed depth of the larger origin cube.
-/
theorem originCube_mem_descendantsAtDepth_originCube_add
    {d : ℕ} (j n : ℕ) :
    Homogenization.originCube d (j : ℤ) ∈
      Homogenization.descendantsAtDepth
        (Homogenization.originCube d ((j + n : ℕ) : ℤ)) n := by
  induction n generalizing j with
  | zero =>
      simp only [Nat.add_zero, Homogenization.descendantsAtDepth_zero,
        Finset.mem_singleton]
  | succ n ih =>
      rw [Homogenization.descendantsAtDepth_succ]
      refine Finset.mem_biUnion.mpr ?_
      refine ⟨Homogenization.originCube d ((j + 1 : ℕ) : ℤ), ?_, ?_⟩
      · have hsum : (j + 1) + n = j + (n + 1) := by omega
        simpa only [hsum] using
          ih (j + 1)
      · have hscale : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
        simpa only [hscale] using
          originCube_pred_mem_childCubes_originCube (d := d) (((j + 1 : ℕ) : ℤ))

/--
Library geometry bridge: if `j <= m`, the scale-`j` origin cube is a descendant at
depth `m - j` of the scale-`m` origin cube.
-/
theorem originCube_mem_descendantsAtDepth_originCube_of_le
    {d : ℕ} {j m : ℕ} (hjm : j ≤ m) :
    Homogenization.originCube d (j : ℤ) ∈
      Homogenization.descendantsAtDepth
        (Homogenization.originCube d (m : ℤ)) (m - j) := by
  have hsum : j + (m - j) = m := Nat.add_sub_of_le hjm
  simpa only [hsum] using
    originCube_mem_descendantsAtDepth_originCube_add (d := d) j (m - j)

theorem paired_mismatchTermSquares_special_le_localBaseline_add_positiveExcess
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Homogenization.Vec d) (a : Homogenization.RegCoeffField d) :
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
    let defectSum : ℝ :=
      ∑ n ∈ Finset.Icc (((k : ℤ) + 1)) (m : ℤ),
        Real.rpow (3 : ℝ)
            (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          Real.sqrt
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
              (m : ℤ) n p_e q_e a)
    let lowerExcess : ℝ :=
      max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹)
        0
    let upperExcess : ℝ :=
      max
        (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
          hP.barSigmaAtScale hStruct (k : ℤ))
        0
    σ *
        (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientMismatchTermAtScale
          (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
      σ⁻¹ *
        (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxMismatchTermAtScale
          (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
      ≤
        (localWeakNormScalarWeightAtScales hP hStruct k m +
            (σ * lowerExcess + σ⁻¹ * upperExcess)) *
          defectSum ^ 2 := by
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let s' := hP4.sLower + β
  let t := hP4.sUpper + 2 * β
  let t' := hP4.sUpper + β
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let D : ℝ :=
    ∑ n ∈ Finset.Icc (((k : ℤ) + 1)) (m : ℤ),
      Real.rpow (3 : ℝ)
          (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
        Real.sqrt
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
            (m : ℤ) n p_e q_e a)
  let lowerCoeff : ℝ :=
    (Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹
  let upperCoeff : ℝ :=
    Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a
  let lowerBase : ℝ := (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹
  let upperBase : ℝ := hP.barSigmaAtScale hStruct (k : ℤ)
  let lowerExcess : ℝ := max (lowerCoeff - lowerBase) 0
  let upperExcess : ℝ := max (upperCoeff - upperBase) 0
  have hβ_pos : 0 < β := by
    simpa [β] using
      Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta_pos
        hP4
  have hs'_pos : 0 < s' := by
    dsimp [s', β]
    linarith [hP4.sLower_pos, hβ_pos]
  have ht'_pos : 0 < t' := by
    dsimp [t', β]
    linarith [hP4.sUpper_pos, hβ_pos]
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ, Homogenization.Book.Ch05.sigmaHatAtScale]
    exact Real.sqrt_nonneg _
  have hσ_inv_nonneg : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ_nonneg
  have hlowerCoeff_nonneg : 0 ≤ lowerCoeff := by
    dsimp [lowerCoeff]
    exact inv_nonneg.mpr
      (Homogenization.Book.Ch04.lambdaSqCoeffField_finite_nonneg
        Q a hs'_pos (by norm_num))
  have hupperCoeff_nonneg : 0 ≤ upperCoeff := by
    dsimp [upperCoeff]
    exact Homogenization.Book.Ch04.LambdaSqCoeffField_finite_nonneg
      Q a ht'_pos (by norm_num)
  have hGradSq :
      (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientMismatchTermAtScale
          (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 =
        lowerCoeff * D ^ 2 := by
    have hgap : s - s' = β := by
      dsimp [s, s']
      ring
    dsimp [Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientMismatchTermAtScale,
      D, lowerCoeff, Q]
    rw [hgap]
    rw [mul_pow, Real.sq_sqrt hlowerCoeff_nonneg]
  have hFluxSq :
      (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxMismatchTermAtScale
          (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2 =
        upperCoeff * D ^ 2 := by
    have hgap : t - t' = β := by
      dsimp [t, t']
      ring
    dsimp [Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxMismatchTermAtScale,
      D, upperCoeff, Q]
    rw [hgap]
    rw [mul_pow, Real.sq_sqrt hupperCoeff_nonneg]
  have hlower_le : lowerCoeff ≤ lowerBase + lowerExcess := by
    simpa [lowerExcess] using positivePart_split_le lowerCoeff lowerBase
  have hupper_le : upperCoeff ≤ upperBase + upperExcess := by
    simpa [upperExcess] using positivePart_split_le upperCoeff upperBase
  have hDsq_nonneg : 0 ≤ D ^ 2 := sq_nonneg _
  have hScalarWeight :
      localWeakNormScalarWeightAtScales hP hStruct k m =
        σ * lowerBase + σ⁻¹ * upperBase := by
    unfold localWeakNormScalarWeightAtScales
    simp [σ, lowerBase, upperBase]
  calc
    σ *
        (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientMismatchTermAtScale
          (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
      σ⁻¹ *
        (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxMismatchTermAtScale
          (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
        =
      (σ * lowerCoeff + σ⁻¹ * upperCoeff) * D ^ 2 := by
        rw [hGradSq, hFluxSq]
        ring
    _ ≤
      (σ * (lowerBase + lowerExcess) +
          σ⁻¹ * (upperBase + upperExcess)) * D ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (add_le_add
            (mul_le_mul_of_nonneg_left hlower_le hσ_nonneg)
            (mul_le_mul_of_nonneg_left hupper_le hσ_inv_nonneg))
          hDsq_nonneg
    _ =
      (localWeakNormScalarWeightAtScales hP hStruct k m +
          (σ * lowerExcess + σ⁻¹ * upperExcess)) * D ^ 2 := by
        rw [hScalarWeight]
        ring

/--
Source labels `p.HC.CR`, `e.W.first.sum`, and `e.P.bound`: local
weak-norm field shape for the raw high-contrast response estimate.  The left
side is the paired gradient/flux mismatch square term.  The right side keeps
the canonical terminal-fluctuation slot `(1 + F_m) S_m`, the local
`P_{k,m}` additivity-defect coefficient, and the positive-excess lower edge
explicit.

This is a concrete weak-norm component, not a new feed or wrapper assumption.
-/
theorem paired_mismatchTermSquares_special_le_rawHighContrastWeakNormContribution_local
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Homogenization.Vec d) (a : Homogenization.RegCoeffField d) :
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
    let defectSum : ℝ :=
      ∑ n ∈ Finset.Icc (((k : ℤ) + 1)) (m : ℤ),
        Real.rpow (3 : ℝ)
            (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          Real.sqrt
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
              (m : ℤ) n p_e q_e a)
    let lowerExcess : ℝ :=
      max
        ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹)
        0
    let upperExcess : ℝ :=
      max
        (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
          hP.barSigmaAtScale hStruct (k : ℤ))
        0
    let T_m := 1 + contrastExcessAtScale hP hStruct m
    let S_m := coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m
    σ *
        (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientMismatchTermAtScale
          (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
      σ⁻¹ *
        (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxMismatchTermAtScale
          (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
      ≤
        T_m * S_m +
          localWeakNormScalarWeightAtScales hP hStruct k m * defectSum ^ 2 +
          (σ * lowerExcess + σ⁻¹ * upperExcess) * defectSum ^ 2 +
          T_m * 0 := by
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let s := hP4.sLower + 2 * β
  let s' := hP4.sLower + β
  let t := hP4.sUpper + 2 * β
  let t' := hP4.sUpper + β
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let D : ℝ :=
    ∑ n ∈ Finset.Icc (((k : ℤ) + 1)) (m : ℤ),
      Real.rpow (3 : ℝ)
          (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
        Real.sqrt
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
            (m : ℤ) n p_e q_e a)
  let lowerExcess : ℝ :=
    max
      ((Homogenization.Book.Ch04.lambdaSqCoeffField Q s' (.finite 1) a)⁻¹ -
        (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹)
      0
  let upperExcess : ℝ :=
    max
      (Homogenization.Book.Ch04.LambdaSqCoeffField Q t' (.finite 1) a -
        hP.barSigmaAtScale hStruct (k : ℤ))
      0
  let T_m : ℝ := 1 + contrastExcessAtScale hP hStruct m
  let S_m : ℝ := coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m
  have hlocal :
      σ *
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientMismatchTermAtScale
            (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
        σ⁻¹ *
          (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxMismatchTermAtScale
            (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
        ≤
          (localWeakNormScalarWeightAtScales hP hStruct k m +
              (σ * lowerExcess + σ⁻¹ * upperExcess)) * D ^ 2 := by
    simpa [β, s, s', t, t', Q, p_e, q_e, σ, D, lowerExcess, upperExcess] using
      paired_mismatchTermSquares_special_le_localBaseline_add_positiveExcess
        hP hStruct hP4 k m e a
  have hT_nonneg : 0 ≤ T_m := by
    dsimp [T_m]
    have hF_nonneg : 0 ≤ contrastExcessAtScale hP hStruct m :=
      contrastExcessAtScale_nonneg_of_P4 hP hStruct hP4 m
    linarith
  have hS_nonneg : 0 ≤ S_m := by
    simpa [S_m] using
      coarseFluctuationFullBlockSumAtScale_nonneg hP hStruct hP4 k m
  have hterminal_nonneg : 0 ≤ T_m * S_m := mul_nonneg hT_nonneg hS_nonneg
  calc
    σ *
        (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.gradientMismatchTermAtScale
          (m : ℤ) (k : ℤ) s s' p_e q_e a) ^ 2 +
      σ⁻¹ *
        (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.fluxMismatchTermAtScale
          (m : ℤ) (k : ℤ) t t' p_e q_e a) ^ 2
        ≤
      (localWeakNormScalarWeightAtScales hP hStruct k m +
          (σ * lowerExcess + σ⁻¹ * upperExcess)) * D ^ 2 := hlocal
    _ =
      localWeakNormScalarWeightAtScales hP hStruct k m * D ^ 2 +
        (σ * lowerExcess + σ⁻¹ * upperExcess) * D ^ 2 := by
        ring
    _ ≤
      T_m * S_m +
        localWeakNormScalarWeightAtScales hP hStruct k m * D ^ 2 +
        (σ * lowerExcess + σ⁻¹ * upperExcess) * D ^ 2 +
        T_m * 0 := by
        nlinarith

/--
Source label `l.S.and.J`: natural-scale version of the Section 5.3 geometric
weight in `coarseFluctuationFullBlockSumAtScale`.
-/
noncomputable def section53CoarseFluctuationScaleWeight
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m j : ℕ) : ℝ :=
  Real.rpow (3 : ℝ)
    (-(section53CoarseFluctuationBeta hP4) * ((m - j : ℕ) : ℝ))

/--
Source label `e.drift.nodrop`: geometric-summability constant for the
Section 5.3 fluctuation weights.
-/
noncomputable def section53CoarseFluctuationWeightSumConstant
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P) :
    ℝ :=
  (1 - Real.rpow (3 : ℝ) (-(section53CoarseFluctuationBeta hP4)))⁻¹

private theorem section53CoarseFluctuationBetaCoreParams_pos_of_params
    {d : ℕ}
    (params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d) :
    0 < section53CoarseFluctuationBetaCoreParams params := by
  have hgap : 0 < 1 - params.sUpper - params.sLower := by
    linarith [params.sum_lt_one]
  have hupper : 0 < params.sUpper := params.sUpper_pos
  have hlower : 0 < params.sLower := params.sLower_pos
  have hupper_gain :
      0 < params.sUpper - (d : ℝ) / (params.xi : ℝ) := by
    linarith [params.dim_div_xi_lt_sUpper]
  have hlower_gain :
      0 < params.sLower - (d : ℝ) / (params.xi : ℝ) := by
    linarith [params.dim_div_xi_lt_sLower]
  unfold section53CoarseFluctuationBetaCoreParams
  exact lt_min hgap
    (lt_min hupper (lt_min hlower (lt_min hupper_gain hlower_gain)))

private theorem section53CoarseFluctuationBetaParams_pos_of_params
    {d : ℕ}
    (params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d) :
    0 < section53CoarseFluctuationBetaParams params := by
  unfold section53CoarseFluctuationBetaParams
  nlinarith [section53CoarseFluctuationBetaCoreParams_pos_of_params params]

/--
Source label `l.S.and.J`: the two-beta block decay can be written as a power of
the one-block two-beta decay.
-/
theorem section53CoarseFluctuationBetaParams_twoBlockDecay_eq_one_pow
    {d : ℕ}
    (params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    (L : ℕ) :
    Real.rpow (3 : ℝ)
        (-2 * section53CoarseFluctuationBetaParams params * (L : ℝ)) =
      Real.rpow (3 : ℝ)
        (-2 * section53CoarseFluctuationBetaParams params) ^ L := by
  calc
    Real.rpow (3 : ℝ)
        (-2 * section53CoarseFluctuationBetaParams params * (L : ℝ)) =
      Real.rpow (3 : ℝ)
        ((-2 * section53CoarseFluctuationBetaParams params) * (L : ℝ)) := by
        congr 1
    _ =
      Real.rpow (Real.rpow (3 : ℝ)
        (-2 * section53CoarseFluctuationBetaParams params)) (L : ℝ) := by
        exact Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)
          (-2 * section53CoarseFluctuationBetaParams params) (L : ℝ)
    _ =
      Real.rpow (3 : ℝ)
        (-2 * section53CoarseFluctuationBetaParams params) ^ L := by
        exact Real.rpow_natCast
          (Real.rpow (3 : ℝ)
            (-2 * section53CoarseFluctuationBetaParams params)) L

/--
Source label `l.S.and.J`: by enlarging the fixed block length, the
parameter-level two-beta Section 5.3 decay is below any positive threshold.
-/
theorem exists_section53CoarseFluctuationBetaParams_twoBlockDecay_le_of_pos
    {d : ℕ}
    (params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    {x : ℝ} (hx_pos : 0 < x) :
    ∃ L : ℕ, 0 < L ∧
      Real.rpow (3 : ℝ)
          (-2 * section53CoarseFluctuationBetaParams params * (L : ℝ)) ≤ x := by
  let β : ℝ := section53CoarseFluctuationBetaParams params
  let q : ℝ := Real.rpow (3 : ℝ) (-2 * β)
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBetaParams_pos_of_params params
  have hq_pos : 0 < q := by
    dsimp [q]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _
  have hq_lt_one : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : (1 : ℝ) < 3)
      (by nlinarith)
  obtain ⟨L0, hL0⟩ := exists_pow_lt_of_lt_one hx_pos hq_lt_one
  refine ⟨max 1 L0, ?_, ?_⟩
  · exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 L0)
  · have hL0_le : L0 ≤ max 1 L0 := Nat.le_max_right 1 L0
    have hpow_le : q ^ max 1 L0 ≤ q ^ L0 :=
      pow_le_pow_of_le_one (le_of_lt hq_pos) (le_of_lt hq_lt_one) hL0_le
    calc
      Real.rpow (3 : ℝ)
          (-2 * section53CoarseFluctuationBetaParams params *
            ((max 1 L0 : ℕ) : ℝ)) =
          q ^ max 1 L0 := by
            simpa [β, q] using
              section53CoarseFluctuationBetaParams_twoBlockDecay_eq_one_pow
                params (max 1 L0)
      _ ≤ q ^ L0 := hpow_le
      _ ≤ x := le_of_lt hL0

/--
Source label `l.S.and.J`: the two-beta block decay decreases when the fixed
memory block length is enlarged.
-/
theorem section53CoarseFluctuationBeta_twoBlockDecay_le_of_le
    {β : ℝ} (hβ_nonneg : 0 ≤ β) {L0 L : ℕ} (hL : L0 ≤ L) :
    Real.rpow (3 : ℝ) (-2 * β * (L : ℝ)) ≤
      Real.rpow (3 : ℝ) (-2 * β * (L0 : ℝ)) := by
  have hL_real : (L0 : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast hL
  have hexp : -2 * β * (L : ℝ) ≤ -2 * β * (L0 : ℝ) := by
    nlinarith
  exact
    Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) hexp

/--
Source label `l.S.and.J`: a parameter-level two-beta block length works
uniformly for every law with the same quantitative ellipticity parameters.
-/
theorem exists_section53CoarseFluctuationBeta_twoBlockDecay_le_of_params
    {d : ℕ} [NeZero d]
    (params :
      Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d)
    {x : ℝ} (hx_pos : 0 < x) :
    ∃ L : ℕ, 0 < L ∧
      ∀ {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
        (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P),
        hP4.params = params →
          Real.rpow (3 : ℝ)
            (-2 * section53CoarseFluctuationBeta hP4 * (L : ℝ)) ≤ x := by
  obtain ⟨L, hL_pos, hL⟩ :=
    exists_section53CoarseFluctuationBetaParams_twoBlockDecay_le_of_pos
      params hx_pos
  refine ⟨L, hL_pos, ?_⟩
  intro P hP4 hparams
  have hβ :
      section53CoarseFluctuationBeta hP4 =
        section53CoarseFluctuationBetaParams params := by
    simpa [hparams] using
      (section53CoarseFluctuationBetaParams_eq_of_P4 hP4).symm
  simpa [hβ] using hL

theorem section53CoarseFluctuationScaleWeight_eq_base_pow
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m j : ℕ) :
    section53CoarseFluctuationScaleWeight hP4 m j =
      (Real.rpow (3 : ℝ) (-(section53CoarseFluctuationBeta hP4))) ^ (m - j) := by
  simpa [section53CoarseFluctuationScaleWeight] using
    Real.rpow_mul_natCast
      (by norm_num : (0 : ℝ) ≤ 3)
      (-(section53CoarseFluctuationBeta hP4))
      (m - j)

/--
Source label `e.drift.nodrop`: each Section 5.3 fluctuation weight is at most
one.  This is the finite-window substitute for the geometric summability used
in the manuscript.
-/
theorem section53CoarseFluctuationScaleWeight_le_one
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m j : ℕ) :
    section53CoarseFluctuationScaleWeight hP4 m j ≤ 1 := by
  have hbeta_nonneg : 0 ≤ section53CoarseFluctuationBeta hP4 :=
    section53CoarseFluctuationBeta_nonneg hP4
  have hgap_nonneg : 0 ≤ ((m - j : ℕ) : ℝ) := by positivity
  dsimp [section53CoarseFluctuationScaleWeight]
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by norm_num : (1 : ℝ) ≤ 3) (by nlinarith)

end Homogenization.HighContrast.EntryScale
