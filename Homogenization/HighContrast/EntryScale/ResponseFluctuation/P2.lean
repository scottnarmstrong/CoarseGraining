import Mathlib.Algebra.Order.Field.GeomSum
import Homogenization.Book.Ch05.Theorems.Section52.P4Integrability
import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations
import Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.ResponseMoment
import Homogenization.HighContrast.EntryScale.DeterministicAlgebra
import Homogenization.HighContrast.EntryScale.MomentConsequences
import Homogenization.HighContrast.EntryScale.ResponseFluctuation.P1

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization.Book.Ch05.Section54.OneStepContraction

namespace Homogenization.HighContrast.EntryScale

/--
Source label `e.tau.sum.absorb`: the concrete Section 5.3 scale weight used
in the weighted additivity-defect sum is nonnegative.
-/
theorem section53CoarseFluctuationScaleWeight_nonneg
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m j : ℕ) :
    0 ≤ section53CoarseFluctuationScaleWeight hP4 m j := by
  dsimp [section53CoarseFluctuationScaleWeight]
  exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _

/--
Source label `e.tau.sum.absorb`: the concrete weighted additivity-defect sum
appearing in the no-drop high-moment proof.
-/
noncomputable def weightedTauSumAtScales
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Homogenization.Vec d) : ℝ :=
  ∑ j ∈ Finset.Icc (k + 1) m,
    section53CoarseFluctuationScaleWeight hP4 m j *
      Homogenization.Book.Ch05.tauAtScale P (m : ℤ) (j : ℤ)
        (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
        (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e)

/--
Source labels `e.tau.sum.absorb` and `p.HC.CR`: LIH's integer-indexed
`coarseFluctuationTauSumAtScale` is the manuscript natural-scale weighted tau
sum.  This is only the reindexing step; scalar prefactors remain separate.
-/
theorem coarseFluctuationTauSumAtScale_eq_weightedTauSumAtScales
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) (e : Homogenization.Vec d) :
    coarseFluctuationTauSumAtScale hP hStruct hP4 k m e =
      weightedTauSumAtScales hP hStruct hP4 k m e := by
  classical
  unfold coarseFluctuationTauSumAtScale weightedTauSumAtScales
  rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by omega]
  refine
    (Finset.sum_bij
      (s := Finset.Icc (k + 1) m)
      (t := Finset.Icc (((k + 1 : ℕ) : ℤ)) (m : ℤ))
      (f := fun j =>
        (section53CoarseFluctuationScaleWeight hP4 m j *
          Homogenization.Book.Ch05.tauAtScale P (m : ℤ) (j : ℤ)
            (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
            (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) :
          ℝ))
      (g := fun n =>
        (Real.rpow (3 : ℝ)
            (-(section53CoarseFluctuationBeta hP4) *
              (Int.toNat ((m : ℤ) - n) : ℝ)) *
          Homogenization.Book.Ch05.tauAtScale P (m : ℤ) n
            (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
            (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) :
          ℝ))
      (fun j _hj => (j : ℤ))
      ?hmem ?hinj ?hsurj ?hterm).symm
  · intro j hj
    have hjb := Finset.mem_Icc.mp hj
    change (j : ℤ) ∈ Finset.Icc (((k + 1 : ℕ) : ℤ)) (m : ℤ)
    exact Finset.mem_Icc.mpr
      ⟨by exact_mod_cast hjb.1, by exact_mod_cast hjb.2⟩
  · intro a _ha b _hb hab
    have hcast : (a : ℤ) = (b : ℤ) := by simpa only using hab
    exact_mod_cast hcast
  · intro n hn
    have hn_bounds := Finset.mem_Icc.mp hn
    have hn_nonneg : 0 ≤ n := by
      have hk_nonneg : (0 : ℤ) ≤ (k + 1 : ℕ) := by
        exact_mod_cast Nat.zero_le (k + 1)
      exact hk_nonneg.trans hn_bounds.1
    refine ⟨Int.toNat n, ?_, ?_⟩
    · have hcast : ((Int.toNat n : ℕ) : ℤ) = n :=
        Int.toNat_of_nonneg hn_nonneg
      apply Finset.mem_Icc.mpr
      constructor
      · have hlow : ((k + 1 : ℕ) : ℤ) ≤ ((Int.toNat n : ℕ) : ℤ) := by
          simpa only [hcast] using hn_bounds.1
        exact_mod_cast hlow
      · have hhi : ((Int.toNat n : ℕ) : ℤ) ≤ (m : ℤ) := by
          simpa only [hcast] using hn_bounds.2
        exact_mod_cast hhi
    · exact Int.toNat_of_nonneg hn_nonneg
  · intro j hj
    have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
    have hto : Int.toNat ((m : ℤ) - (j : ℤ)) = m - j := by
      have hsub : (m : ℤ) - (j : ℤ) = ((m - j : ℕ) : ℤ) := by
        omega
      rw [hsub]
      simp only [Int.toNat_natCast]
    simp only [section53CoarseFluctuationScaleWeight, hto]

/--
Source label `p.HC.CR`: pointwise child-response control of the local
response-defect sum.  This is the pre-integration form needed for the
good/bad lower-edge split: the square of the geometrically weighted defect
sum is controlled by the average of child response observables in the
terminal descendants of the scale-`m` origin cube.
-/
theorem defectSum_sq_special_le_childResponseAverage
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Homogenization.Vec d)
    {a : Homogenization.CoeffField d}
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a) :
    let β := section53CoarseFluctuationBeta hP4
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    (∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
        Real.rpow (3 : ℝ)
            (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          Real.sqrt
            (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
              (m : ℤ) n p_e q_e a)) ^ 2
      ≤
        (5 * β⁻¹) ^ 2 *
          Homogenization.descendantsAverage
            (Homogenization.originCube d (m : ℤ)) (m - k)
            (fun R =>
              Homogenization.Book.Ch04.responseJObservableCubeSet R p_e q_e a) := by
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
  have hkm_int : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hkm.le
  have hβ_pos : 0 < β := by
    simpa [β] using
      Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta_pos
        hP4
  have hβ_le_one : β ≤ 1 := by
    have hsum := sUpper_add_sLower_add_four_beta_le_one hP4
    have hupper := hP4.sUpper_nonneg
    have hlower := hP4.sLower_nonneg
    have hβ_nonneg : 0 ≤ β := by
      simpa [β] using
        Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta_nonneg
          hP4
    nlinarith
  simpa [β, p_e, q_e] using
    sq_beta_weighted_sqrt_responseDefectAverageAtScale_le_childResponseAverageAtScale
      ha hk_nonneg hkm_int hβ_pos hβ_le_one p_e q_e

/--
Source labels `p.HC.CR` and `e.tau.sum.absorb`: expectation-level conversion
of the local weak-norm response-defect square into the manuscript weighted tau
sum.  The pointwise `defectSum ^ 2` in the raw weak-norm split cannot be
bounded by tau without integration; LIH supplies exactly this integrated
Cauchy/stationarity estimate, and the theorem below rewrites LIH's integer
tau sum to the natural-scale `weightedTauSumAtScales`.
-/
theorem integral_defectSum_sq_special_le_beta_inv_weightedTauSumAtScales
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hstat : Homogenization.Book.Ch04.StationaryLaw P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Homogenization.Vec d) :
    let β := section53CoarseFluctuationBeta hP4
    let p_e :=
      Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
    let q_e :=
      Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
    ∫ a,
        (∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
          Real.rpow (3 : ℝ)
              (-β * (Int.toNat ((m : ℤ) - n) : ℝ)) *
            Real.sqrt
              (Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
                (m : ℤ) n p_e q_e a)) ^ 2 ∂P
      ≤
        (5 * β⁻¹) *
          weightedTauSumAtScales hP hStruct hP4 k m e := by
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  have hbase :=
    integral_sq_beta_weighted_sqrt_responseDefectAverageAtScale_special_le_tauSum
      hP hstat hStruct hP4 hkm e
  have htau :
      coarseFluctuationTauSumAtScale hP hStruct hP4 k m e =
        weightedTauSumAtScales hP hStruct hP4 k m e :=
    coarseFluctuationTauSumAtScale_eq_weightedTauSumAtScales
      hP hStruct hP4 k m e
  simpa [β, p_e, q_e, htau] using hbase

/--
Source label `e.drift.nodrop`: geometric bound for the Section 5.3
fluctuation weights, with a constant depending only on the LIH exponent
`beta`.
-/
theorem section53CoarseFluctuationScaleWeight_sum_le_geometricConstant
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) :
    ∑ j ∈ Finset.Icc (k + 1) m,
        section53CoarseFluctuationScaleWeight hP4 m j ≤
      section53CoarseFluctuationWeightSumConstant hP4 := by
  let β := section53CoarseFluctuationBeta hP4
  let q : ℝ := Real.rpow (3 : ℝ) (-β)
  have hq_pos : 0 < q := by
    dsimp [q]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (-β)
  have hq_lt_one : q < 1 := by
    dsimp [q, β]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : (1 : ℝ) < 3)
      (by
        have hβ_pos : 0 < section53CoarseFluctuationBeta hP4 :=
          Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta_pos
            hP4
        linarith)
  have hsum_eq :
      ∑ j ∈ Finset.Icc (k + 1) m,
          section53CoarseFluctuationScaleWeight hP4 m j =
        ∑ n ∈ Finset.range (m - k), q ^ n := by
    have hreflect :
        ∑ j ∈ Finset.Icc (k + 1) m,
            section53CoarseFluctuationScaleWeight hP4 m j =
          ∑ n ∈ Finset.range (m - k), q ^ (m - k - 1 - n) := by
      refine
        (Finset.sum_bij
          (s := Finset.range (m - k))
          (t := Finset.Icc (k + 1) m)
          (f := fun n => (q ^ (m - k - 1 - n) : ℝ))
          (g := fun j => section53CoarseFluctuationScaleWeight hP4 m j)
          (fun n _hn => k + 1 + n)
          ?hmem ?hinj ?hsurj ?hterm).symm
      · intro n hn
        have hnlt : n < m - k := Finset.mem_range.mp hn
        have hlt : k + n < m := Nat.lt_sub_iff_add_lt'.mp hnlt
        change k + 1 + n ∈ Finset.Icc (k + 1) m
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro a _ha b _hb hab
        change k + 1 + a = k + 1 + b at hab
        omega
      · intro j hj
        have hj_bounds := Finset.mem_Icc.mp hj
        refine ⟨j - (k + 1), ?_, ?_⟩
        · exact Finset.mem_range.mpr (by omega)
        · change k + 1 + (j - (k + 1)) = j
          omega
      · intro n hn
        have hnlt : n < m - k := Finset.mem_range.mp hn
        have hgap : m - (k + 1 + n) = m - k - 1 - n := by omega
        change q ^ (m - k - 1 - n) =
          section53CoarseFluctuationScaleWeight hP4 m (k + 1 + n)
        rw [section53CoarseFluctuationScaleWeight_eq_base_pow, hgap]
    calc
      ∑ j ∈ Finset.Icc (k + 1) m,
          section53CoarseFluctuationScaleWeight hP4 m j =
          ∑ n ∈ Finset.range (m - k), q ^ (m - k - 1 - n) := hreflect
      _ = ∑ n ∈ Finset.range (m - k), q ^ n :=
        Finset.sum_range_reflect (fun n => q ^ n) (m - k)
  calc
    ∑ j ∈ Finset.Icc (k + 1) m,
        section53CoarseFluctuationScaleWeight hP4 m j =
        ∑ n ∈ Finset.range (m - k), q ^ n := hsum_eq
    _ ≤ (1 - q)⁻¹ := by
      rw [Finset.range_eq_Ico]
      simpa using
        geom_sum_Ico_le_of_lt_one
          (x := q) (m := 0) (n := m - k) hq_pos.le hq_lt_one
    _ = section53CoarseFluctuationWeightSumConstant hP4 := by
      rfl

/--
Source label `l.S.and.J`: natural-index form of LIH's Section 5.3 full-block
fluctuation sum.  This avoids importing the Section 5.6 reindex lemma, which is
not needed for the present development.
-/
theorem coarseFluctuationFullBlockSumAtScale_eq_nat_Icc
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) :
    coarseFluctuationFullBlockSumAtScale hP hStruct hP4 k m =
      ∑ j ∈ Finset.Icc (k + 1) m,
        section53CoarseFluctuationScaleWeight hP4 m j *
          ∫ a,
            Homogenization.Book.Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct (m : ℤ) (Homogenization.originCube d (j : ℤ)) a ∂P := by
  classical
  unfold coarseFluctuationFullBlockSumAtScale
  rw [show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by omega]
  refine
    (Finset.sum_bij
      (s := Finset.Icc (k + 1) m)
      (t := Finset.Icc (((k + 1 : ℕ) : ℤ)) (m : ℤ))
      (f := fun j =>
        (section53CoarseFluctuationScaleWeight hP4 m j *
          ∫ a,
            Homogenization.Book.Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct (m : ℤ) (Homogenization.originCube d (j : ℤ)) a ∂P : ℝ))
      (g := fun n =>
        (Real.rpow (3 : ℝ)
            (-(section53CoarseFluctuationBeta hP4) *
              (Int.toNat ((m : ℤ) - n) : ℝ)) *
          ∫ a,
            Homogenization.Book.Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
              hP hStruct (m : ℤ) (Homogenization.originCube d n) a ∂P : ℝ))
      (fun j _hj => (j : ℤ))
      ?hmem ?hinj ?hsurj ?hterm).symm
  · intro j hj
    have hjb := Finset.mem_Icc.mp hj
    change (j : ℤ) ∈ Finset.Icc (((k + 1 : ℕ) : ℤ)) (m : ℤ)
    exact Finset.mem_Icc.mpr
      ⟨by exact_mod_cast hjb.1, by exact_mod_cast hjb.2⟩
  · intro a _ha b _hb hab
    have hcast : (a : ℤ) = (b : ℤ) := by simpa only using hab
    exact_mod_cast hcast
  · intro n hn
    have hn_bounds := Finset.mem_Icc.mp hn
    have hn_nonneg : 0 ≤ n := by
      have hk_nonneg : (0 : ℤ) ≤ (k + 1 : ℕ) := by
        exact_mod_cast Nat.zero_le (k + 1)
      exact hk_nonneg.trans hn_bounds.1
    refine ⟨Int.toNat n, ?_, ?_⟩
    · have hcast : ((Int.toNat n : ℕ) : ℤ) = n :=
        Int.toNat_of_nonneg hn_nonneg
      apply Finset.mem_Icc.mpr
      constructor
      · have hlow : ((k + 1 : ℕ) : ℤ) ≤ ((Int.toNat n : ℕ) : ℤ) := by
          simpa only [hcast] using hn_bounds.1
        exact_mod_cast hlow
      · have hhi : ((Int.toNat n : ℕ) : ℤ) ≤ (m : ℤ) := by
          simpa only [hcast] using hn_bounds.2
        exact_mod_cast hhi
    · exact Int.toNat_of_nonneg hn_nonneg
  · intro j hj
    have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
    simp only [section53CoarseFluctuationScaleWeight, int_toNat_nat_sub_eq_of_le hjm]

/--
Source label `l.S.and.J`: stochastic part of the terminal-normalized
full-block fluctuation, centered at the intermediate scale `j`.
-/
noncomputable def terminalCenteredFullBlockFluctuationSqAtScale
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (j m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.CoeffField d) : ℝ :=
  fullBlockOperatorNorm
    (scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
      scalarCenteredFullBlockMatrixAtScale hP hStruct j
        (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube Q a) *
      scalarFullBlockNormalizerMatrixAtScale hP hStruct m) ^ 2

/--
Source label `l.S.and.J`: reverse deterministic split used only to prove the
integrability of the centered square.  The term centered at scale `j` is
bounded by the LIH terminal fluctuation centered at scale `m` plus a
deterministic annealed offset.
-/
theorem terminalCenteredFullBlockFluctuationSqAtScale_le_two_fullBlockFluctuation_add_const
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (j m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.CoeffField d) :
    terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m Q a ≤
      2 *
        Homogenization.Book.Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct (m : ℤ) Q a +
      2 *
        fullBlockOperatorNorm
          (scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
            (Homogenization.toFullBlockMat
                (Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale
                  hP hStruct (m : ℤ)) -
              Homogenization.toFullBlockMat
                (Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale
                  hP hStruct (j : ℤ))) *
            scalarFullBlockNormalizerMatrixAtScale hP hStruct m) ^ 2 := by
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
  have hcenter :
      scalarCenteredFullBlockMatrixAtScale hP hStruct j A =
        scalarCenteredFullBlockMatrixAtScale hP hStruct m A + (Am - Aj) := by
    dsimp [scalarCenteredFullBlockMatrixAtScale, A, Aj, Am]
    abel
  have hsplit :
      Dm * scalarCenteredFullBlockMatrixAtScale hP hStruct j A * Dm =
        Dm * scalarCenteredFullBlockMatrixAtScale hP hStruct m A * Dm +
          Dm * (Am - Aj) * Dm := by
    rw [hcenter, mul_add, add_mul]
  unfold terminalCenteredFullBlockFluctuationSqAtScale
  rw [show scalarFullBlockNormalizerMatrixAtScale hP hStruct m = Dm from rfl]
  rw [show Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube Q a = A from rfl]
  rw [hsplit]
  rw [fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq_terminal_norm_sq
    hP hStruct m Q a]
  rw [show scalarFullBlockNormalizerMatrixAtScale hP hStruct m = Dm from rfl]
  rw [show Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube Q a = A from rfl]
  exact fullBlockOperatorNorm_add_sq_le_two_mul_add
    (Dm * scalarCenteredFullBlockMatrixAtScale hP hStruct m A * Dm)
    (Dm * (Am - Aj) * Dm)

private theorem continuous_terminalCenteredFullBlockFluctuationSqFunctional
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P) (j m : ℕ) :
    Continuous fun Y : Homogenization.FullBlockMat d =>
      fullBlockOperatorNorm
        (scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
          scalarCenteredFullBlockMatrixAtScale hP hStruct j Y *
          scalarFullBlockNormalizerMatrixAtScale hP hStruct m) ^ 2 := by
  let L : Homogenization.FullBlockMat d →ₗ[ℝ]
      (EuclideanSpace ℝ (Homogenization.BlockCoord d) →L[ℝ]
        EuclideanSpace ℝ (Homogenization.BlockCoord d)) := {
    toFun := fun M =>
      Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d) (𝕜 := ℝ) M
    map_add' := by
      intro A B
      exact map_add
        (Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d) (𝕜 := ℝ)) A B
    map_smul' := by
      intro r A
      exact map_smul
        (Matrix.toEuclideanCLM (n := Homogenization.BlockCoord d) (𝕜 := ℝ)) r A
  }
  have hinner : Continuous fun Y : Homogenization.FullBlockMat d =>
      scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
        scalarCenteredFullBlockMatrixAtScale hP hStruct j Y *
        scalarFullBlockNormalizerMatrixAtScale hP hStruct m := by
    dsimp [scalarCenteredFullBlockMatrixAtScale]
    fun_prop
  have hcont : Continuous fun Y : Homogenization.FullBlockMat d =>
      ‖L (scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
        scalarCenteredFullBlockMatrixAtScale hP hStruct j Y *
        scalarFullBlockNormalizerMatrixAtScale hP hStruct m)‖ :=
    (L.continuous_of_finiteDimensional.comp hinner).norm
  simpa [fullBlockOperatorNorm, L] using hcont.pow 2

open scoped Matrix.Norms.Elementwise

/--
Source label `l.S.and.J`: `(P4)` supplies the real integrability needed for
the stochastic centered square in the Section 5.3 split.  The proof uses LIH's
full-block fluctuation-square integrability and the reverse deterministic
triangle bound above, so no stochastic integrability assumption is introduced.
-/
theorem integrable_terminalCenteredFullBlockFluctuationSqAtScale_origin_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (j m : ℕ) :
    MeasureTheory.Integrable
      (fun a : Homogenization.CoeffField d =>
        terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
          (Homogenization.originCube d (j : ℤ)) a) P := by
  letI : MeasureTheory.IsProbabilityMeasure P := hP.isProbability
  have hbase_int :
      MeasureTheory.Integrable
        (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube
          (Homogenization.originCube d (j : ℤ))) P :=
    Homogenization.Book.Ch05.Section52.originBlockIntegrableAtScale_from_P4
      hP hStruct hP4 j
  have hcentered_ae :
      MeasureTheory.AEStronglyMeasurable
        (fun a : Homogenization.CoeffField d =>
          terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
            (Homogenization.originCube d (j : ℤ)) a) P := by
    have hcomp :=
      (continuous_terminalCenteredFullBlockFluctuationSqFunctional
        hP hStruct j m).comp_aestronglyMeasurable hbase_int.aestronglyMeasurable
    simpa [terminalCenteredFullBlockFluctuationSqAtScale] using hcomp
  let driftRevSq : ℝ :=
    fullBlockOperatorNorm
      (scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
        (Homogenization.toFullBlockMat
            (Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale
              hP hStruct (m : ℤ)) -
          Homogenization.toFullBlockMat
            (Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale
              hP hStruct (j : ℤ))) *
        scalarFullBlockNormalizerMatrixAtScale hP hStruct m) ^ 2
  let rhs : Homogenization.CoeffField d → ℝ :=
    fun a =>
      2 *
        Homogenization.Book.Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct (m : ℤ) (Homogenization.originCube d (j : ℤ)) a +
      2 * driftRevSq
  have hfluct_int :
      MeasureTheory.Integrable
        (Homogenization.Book.Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
          hP hStruct (m : ℤ) (Homogenization.originCube d (j : ℤ))) P :=
    Homogenization.Book.Ch05.Section52.integrable_fullBlockNormalizedFluctuationOperatorNormSqAtScale_originCube_from_P4
      hP hStruct hP4 (m : ℤ) j
  have hrhs_int : MeasureTheory.Integrable rhs P := by
    dsimp [rhs]
    exact (hfluct_int.const_mul 2).add (MeasureTheory.integrable_const (2 * driftRevSq))
  refine MeasureTheory.Integrable.mono' hrhs_int hcentered_ae ?_
  refine Filter.Eventually.of_forall ?_
  intro a
  have hnonneg :
      0 ≤ terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
        (Homogenization.originCube d (j : ℤ)) a := by
    unfold terminalCenteredFullBlockFluctuationSqAtScale
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  simpa [rhs, driftRevSq] using
    terminalCenteredFullBlockFluctuationSqAtScale_le_two_fullBlockFluctuation_add_const
      hP hStruct j m (Homogenization.originCube d (j : ℤ)) a


/--
Source labels `a.HM`, `M_m^st`, and `l.S.and.J`: the Section 5.3 centered
square is exactly the square of the terminal coarse-block deviation used in the
high-moment maximal envelope.
-/
theorem ofReal_terminalCenteredFullBlockFluctuationSqAtScale_eq_terminalCoarseBlockDeviation_sq
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (j m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.CoeffField d) :
    ENNReal.ofReal
        (terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m Q a) =
      terminalCoarseBlockDeviation hP hStruct m
          (fun x : Homogenization.CoeffField d => x) j Q a ^ 2 := by
  unfold terminalCenteredFullBlockFluctuationSqAtScale
  unfold terminalCoarseBlockDeviation
  unfold terminalCenteredFullBlockDeviation
  unfold coarseFullBlockMatrixAtCubeProcess
  rw [ENNReal.ofReal_pow (fullBlockOperatorNorm_nonneg _) 2]

/--
Source labels `a.HM`, `M_m^st`, and `l.S.and.J`: the scale-`j` origin-cube
centered square is pointwise dominated by the finite stochastic envelope,
with only the explicit inverse weak weight lost.  This is the insertion step
for the stochastic half of the Section 5.3 fluctuation estimate.
-/
theorem ofReal_terminalCenteredFullBlockFluctuationSqAtScale_le_inv_weight_mul_terminalCoarseBlockStochasticEnvelope_sq
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hc : HighContrastExponents d) {N j m : ℕ}
    (hNj : N ≤ j) (hjm : j ≤ m)
    (a : Homogenization.CoeffField d) :
    ENNReal.ofReal
        (terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
          (Homogenization.originCube d (j : ℤ)) a) ≤
      ((terminalStochasticWeakWeight (d := d) hc m j
            (Homogenization.originCube d (j : ℤ)))⁻¹ *
        terminalCoarseBlockStochasticEnvelope hP hStruct N m
          (Homogenization.originCube d (m : ℤ))
          (terminalStochasticWeakWeight (d := d) hc m)
          (fun x : Homogenization.CoeffField d => x) a) ^ 2 := by
  classical
  let Qm := Homogenization.originCube d (m : ℤ)
  let Rj := Homogenization.originCube d (j : ℤ)
  let weak : ℕ → Homogenization.TriadicCube d → ENNReal :=
    terminalStochasticWeakWeight (d := d) hc m
  let dev :=
    terminalCoarseBlockDeviation hP hStruct m
      (fun x : Homogenization.CoeffField d => x)
  let env :=
    terminalCoarseBlockStochasticEnvelope hP hStruct N m Qm weak
      (fun x : Homogenization.CoeffField d => x)
  have hjIcc : j ∈ Finset.Icc N m := Finset.mem_Icc.mpr ⟨hNj, hjm⟩
  have hRj : Rj ∈ Homogenization.descendantsAtDepth Qm (m - j) := by
    simpa only [Qm, Rj] using
      originCube_mem_descendantsAtDepth_originCube_of_le (d := d) hjm
  have hinner :
      weak j Rj * dev j Rj a ≤
        (Homogenization.descendantsAtDepth Qm (m - j)).sup
          (fun R => weak j R * dev j R a) := by
    exact Finset.le_sup (s := Homogenization.descendantsAtDepth Qm (m - j))
      (f := fun R => weak j R * dev j R a) hRj
  have hterm : weak j Rj * dev j Rj a ≤ env a := by
    have houter :
        (Homogenization.descendantsAtDepth Qm (m - j)).sup
            (fun R => weak j R * dev j R a) ≤
          env a := by
      dsimp [env, terminalCoarseBlockStochasticEnvelope]
      exact Finset.le_sup
        (s := Finset.Icc N m)
        (f := fun i =>
          (Homogenization.descendantsAtDepth Qm (m - i)).sup
            (fun R => weak i R * dev i R a))
        hjIcc
    exact hinner.trans houter
  have hweak_ne_zero : weak j Rj ≠ 0 := by
    dsimp [weak, terminalStochasticWeakWeight]
    exact ENNReal.ofReal_ne_zero_iff.mpr
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3)
        (-hc.rhoM * ((m - j : ℕ) : ℝ)))
  have hweak_ne_top : weak j Rj ≠ ⊤ := by
    dsimp [weak, terminalStochasticWeakWeight]
    exact ENNReal.ofReal_ne_top
  have hdev_le : dev j Rj a ≤ (weak j Rj)⁻¹ * env a := by
    calc
      dev j Rj a = (weak j Rj)⁻¹ * (weak j Rj * dev j Rj a) := by
        exact (ENNReal.inv_mul_cancel_left hweak_ne_zero hweak_ne_top).symm
      _ ≤ (weak j Rj)⁻¹ * env a := by
        exact mul_le_mul_right hterm (weak j Rj)⁻¹
  have hpow : dev j Rj a ^ 2 ≤ ((weak j Rj)⁻¹ * env a) ^ 2 :=
    ENNReal.pow_le_pow_left hdev_le
  calc
    ENNReal.ofReal
        (terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
          (Homogenization.originCube d (j : ℤ)) a) =
        dev j Rj a ^ 2 := by
      simpa only [dev, Rj] using
        ofReal_terminalCenteredFullBlockFluctuationSqAtScale_eq_terminalCoarseBlockDeviation_sq
          hP hStruct j m (Homogenization.originCube d (j : ℤ)) a
    _ ≤ ((weak j Rj)⁻¹ * env a) ^ 2 := hpow

/--
Source labels `a.HM`, `M_m^st`, and `l.S.and.J`: integrated form of the
pointwise stochastic insertion for one intermediate scale.  It keeps the
estimate in `ENNReal`, before any conversion back to real-valued Section 5.3
integrals.
-/
theorem lintegral_ofReal_terminalCenteredFullBlockFluctuationSqAtScale_le_inv_weight_sq_mul_lintegral_terminalCoarseBlockStochasticEnvelope_sq
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hc : HighContrastExponents d) {N j m : ℕ}
    (hNj : N ≤ j) (hjm : j ≤ m) :
    ∫⁻ a,
        ENNReal.ofReal
          (terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
            (Homogenization.originCube d (j : ℤ)) a) ∂P ≤
      (terminalStochasticWeakWeight (d := d) hc m j
          (Homogenization.originCube d (j : ℤ)))⁻¹ ^ 2 *
        ∫⁻ a,
          (terminalCoarseBlockStochasticEnvelope hP hStruct N m
            (Homogenization.originCube d (m : ℤ))
            (terminalStochasticWeakWeight (d := d) hc m)
            (fun x : Homogenization.CoeffField d => x) a) ^ 2 ∂P := by
  classical
  let c : ENNReal :=
    terminalStochasticWeakWeight (d := d) hc m j
      (Homogenization.originCube d (j : ℤ))
  let env : Homogenization.CoeffField d → ENNReal :=
    terminalCoarseBlockStochasticEnvelope hP hStruct N m
      (Homogenization.originCube d (m : ℤ))
      (terminalStochasticWeakWeight (d := d) hc m)
      (fun x : Homogenization.CoeffField d => x)
  have hc_ne_zero : c ≠ 0 := by
    dsimp [c, terminalStochasticWeakWeight]
    exact ENNReal.ofReal_ne_zero_iff.mpr
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3)
        (-hc.rhoM * ((m - j : ℕ) : ℝ)))
  have hconst_ne_top : c⁻¹ ^ 2 ≠ ⊤ := by
    exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hc_ne_zero)
  have hpoint :
      (fun a : Homogenization.CoeffField d =>
        ENNReal.ofReal
          (terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
            (Homogenization.originCube d (j : ℤ)) a)) ≤
        fun a : Homogenization.CoeffField d => (c⁻¹ * env a) ^ 2 := by
    intro a
    simpa only [c, env] using
      ofReal_terminalCenteredFullBlockFluctuationSqAtScale_le_inv_weight_mul_terminalCoarseBlockStochasticEnvelope_sq
        hP hStruct hc hNj hjm a
  calc
    ∫⁻ a,
        ENNReal.ofReal
          (terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
            (Homogenization.originCube d (j : ℤ)) a) ∂P
        ≤ ∫⁻ a, (c⁻¹ * env a) ^ 2 ∂P :=
          MeasureTheory.lintegral_mono hpoint
    _ = ∫⁻ a, c⁻¹ ^ 2 * env a ^ 2 ∂P := by
          congr with a
          rw [mul_pow]
    _ = c⁻¹ ^ 2 * ∫⁻ a, env a ^ 2 ∂P := by
          rw [MeasureTheory.lintegral_const_mul' (c⁻¹ ^ 2)
            (fun a : Homogenization.CoeffField d => env a ^ 2) hconst_ne_top]

/--
Source labels `a.HM`, `M_m^st`, and `l.S.and.J`: finite-window integrated
stochastic insertion for the Section 5.3 centered-square sum.  The right side
is the common stochastic envelope square times the explicit finite sum of
Section 5.3 weights and inverse weak weights.
-/
theorem lintegral_ofReal_terminalCenteredFullBlockFluctuationSqAtScale_sum_le_weighted_inv_weight_sq_mul_lintegral_terminalCoarseBlockStochasticEnvelope_sq
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {N k m : ℕ} (hNk : N ≤ k + 1) :
    ∑ j ∈ Finset.Icc (k + 1) m,
        ENNReal.ofReal (section53CoarseFluctuationScaleWeight hP4 m j) *
          ∫⁻ a,
            ENNReal.ofReal
              (terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
                (Homogenization.originCube d (j : ℤ)) a) ∂P ≤
      (∑ j ∈ Finset.Icc (k + 1) m,
        ENNReal.ofReal (section53CoarseFluctuationScaleWeight hP4 m j) *
          (terminalStochasticWeakWeight (d := d) hc m j
              (Homogenization.originCube d (j : ℤ)))⁻¹ ^ 2) *
        ∫⁻ a,
          (terminalCoarseBlockStochasticEnvelope hP hStruct N m
            (Homogenization.originCube d (m : ℤ))
            (terminalStochasticWeakWeight (d := d) hc m)
            (fun x : Homogenization.CoeffField d => x) a) ^ 2 ∂P := by
  classical
  let S := Finset.Icc (k + 1) m
  let weight : ℕ → ENNReal :=
    fun j => ENNReal.ofReal (section53CoarseFluctuationScaleWeight hP4 m j)
  let weakInvSq : ℕ → ENNReal :=
    fun j =>
      (terminalStochasticWeakWeight (d := d) hc m j
          (Homogenization.originCube d (j : ℤ)))⁻¹ ^ 2
  let env : Homogenization.CoeffField d → ENNReal :=
    terminalCoarseBlockStochasticEnvelope hP hStruct N m
      (Homogenization.originCube d (m : ℤ))
      (terminalStochasticWeakWeight (d := d) hc m)
      (fun x : Homogenization.CoeffField d => x)
  let I : ENNReal := ∫⁻ a, env a ^ 2 ∂P
  have hterm :
      ∀ j ∈ S,
        weight j *
            ∫⁻ a,
              ENNReal.ofReal
                (terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
                  (Homogenization.originCube d (j : ℤ)) a) ∂P ≤
          weight j * (weakInvSq j * I) := by
    intro j hj
    have hj_bounds := Finset.mem_Icc.mp hj
    have hNj : N ≤ j := hNk.trans hj_bounds.1
    have hjm : j ≤ m := hj_bounds.2
    have hscale :=
      lintegral_ofReal_terminalCenteredFullBlockFluctuationSqAtScale_le_inv_weight_sq_mul_lintegral_terminalCoarseBlockStochasticEnvelope_sq
        hP hStruct hc hNj hjm
    exact mul_le_mul_right
      (by simpa [weakInvSq, env, I] using hscale) (weight j)
  have hrewrite :
      ∑ j ∈ S, weight j * (weakInvSq j * I) =
        (∑ j ∈ S, weight j * weakInvSq j) * I := by
    calc
      ∑ j ∈ S, weight j * (weakInvSq j * I) =
          ∑ j ∈ S, (weight j * weakInvSq j) * I := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            rw [mul_assoc]
      _ = (∑ j ∈ S, weight j * weakInvSq j) * I := by
            rw [Finset.sum_mul]
  calc
    ∑ j ∈ Finset.Icc (k + 1) m,
        ENNReal.ofReal (section53CoarseFluctuationScaleWeight hP4 m j) *
          ∫⁻ a,
            ENNReal.ofReal
              (terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
                (Homogenization.originCube d (j : ℤ)) a) ∂P
        = ∑ j ∈ S,
            weight j *
              ∫⁻ a,
                ENNReal.ofReal
                  (terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
                    (Homogenization.originCube d (j : ℤ)) a) ∂P := rfl
    _ ≤ ∑ j ∈ S, weight j * (weakInvSq j * I) := by
          exact Finset.sum_le_sum hterm
    _ = (∑ j ∈ S, weight j * weakInvSq j) * I := hrewrite
    _ =
      (∑ j ∈ Finset.Icc (k + 1) m,
        ENNReal.ofReal (section53CoarseFluctuationScaleWeight hP4 m j) *
          (terminalStochasticWeakWeight (d := d) hc m j
              (Homogenization.originCube d (j : ℤ)))⁻¹ ^ 2) *
        ∫⁻ a,
          (terminalCoarseBlockStochasticEnvelope hP hStruct N m
            (Homogenization.originCube d (m : ℤ))
            (terminalStochasticWeakWeight (d := d) hc m)
            (fun x : Homogenization.CoeffField d => x) a) ^ 2 ∂P := rfl

/--
Source labels `a.HM`, `M_m^st`, and `l.S.and.J`: convert the stochastic
centered-square estimate from the `ENNReal` lintegral form used by the
high-moment envelope into the real integral sum used by LIH's Section 5.3
full-block fluctuation sum.
-/
theorem terminalCenteredFullBlockFluctuationSqAtScale_integral_sum_le_of_lintegral_sum_le
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} {η : ℝ} (hη_nonneg : 0 ≤ η)
    (hlintegral :
      ∑ j ∈ Finset.Icc (k + 1) m,
          ENNReal.ofReal (section53CoarseFluctuationScaleWeight hP4 m j) *
            ∫⁻ a,
              ENNReal.ofReal
                (terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
                  (Homogenization.originCube d (j : ℤ)) a) ∂P ≤
        ENNReal.ofReal η) :
    ∑ j ∈ Finset.Icc (k + 1) m,
        section53CoarseFluctuationScaleWeight hP4 m j *
          ∫ a,
            terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
              (Homogenization.originCube d (j : ℤ)) a ∂P ≤ η := by
  classical
  let S := Finset.Icc (k + 1) m
  let realTerm : ℕ → ℝ := fun j =>
    section53CoarseFluctuationScaleWeight hP4 m j *
      ∫ a,
        terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
          (Homogenization.originCube d (j : ℤ)) a ∂P
  let ennTerm : ℕ → ENNReal := fun j =>
    ENNReal.ofReal (section53CoarseFluctuationScaleWeight hP4 m j) *
      ∫⁻ a,
        ENNReal.ofReal
          (terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
            (Homogenization.originCube d (j : ℤ)) a) ∂P
  have hterm_nonneg : ∀ j, j ∈ S → 0 ≤ realTerm j := by
    intro j _hj
    dsimp [realTerm]
    exact mul_nonneg
      (by
        dsimp [section53CoarseFluctuationScaleWeight]
        exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
      (MeasureTheory.integral_nonneg fun a => by
        unfold terminalCenteredFullBlockFluctuationSqAtScale
        positivity)
  have hsum_eq :
      ENNReal.ofReal (∑ j ∈ S, realTerm j) = ∑ j ∈ S, ennTerm j := by
    rw [ENNReal.ofReal_sum_of_nonneg hterm_nonneg]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hw_nonneg :
        0 ≤ section53CoarseFluctuationScaleWeight hP4 m j := by
      dsimp [section53CoarseFluctuationScaleWeight]
      exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
    have hf_int :=
      integrable_terminalCenteredFullBlockFluctuationSqAtScale_origin_of_P4
        hP hStruct hP4 j m
    have hf_nonneg :
        0 ≤ᵐ[P] fun a : Homogenization.CoeffField d =>
          terminalCenteredFullBlockFluctuationSqAtScale hP hStruct j m
            (Homogenization.originCube d (j : ℤ)) a := by
      exact Filter.Eventually.of_forall fun a => by
        unfold terminalCenteredFullBlockFluctuationSqAtScale
        positivity
    dsimp [realTerm, ennTerm]
    rw [ENNReal.ofReal_mul hw_nonneg]
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_int hf_nonneg]
  have hsum_le : ENNReal.ofReal (∑ j ∈ S, realTerm j) ≤ ENNReal.ofReal η := by
    rw [hsum_eq]
    simpa [S, ennTerm] using hlintegral
  have hreal_sum_le : ∑ j ∈ S, realTerm j ≤ η := by
    rw [← ENNReal.ofReal_le_ofReal_iff hη_nonneg]
    exact hsum_le
  simpa [S, realTerm] using hreal_sum_le

/--
Source labels `M_m^st` and `l.S.and.J`: on a fixed scale window
`j = k+1, ..., m`, the inverse square of the weak stochastic weight is bounded
by the endpoint window loss.  This is the Lean version of keeping the
`3^{rho_M(m-j)}` loss finite after the note fixes the window length.
-/
theorem terminalStochasticWeakWeight_inv_sq_le_of_mem_Icc_of_sub_le
    {d : ℕ} (hc : HighContrastExponents d) {k j m L : ℕ}
    (hj : j ∈ Finset.Icc (k + 1) m) (hWindow : m - k ≤ L)
    (R : Homogenization.TriadicCube d) :
    (terminalStochasticWeakWeight (d := d) hc m j R)⁻¹ ^ 2 ≤
      ENNReal.ofReal ((3 : ℝ) ^ (2 * hc.rhoM * (L : ℝ))) := by
  have hj_bounds := Finset.mem_Icc.mp hj
  have hgap_le_window_nat : m - j ≤ L := by
    have hgap_le_mk : m - j ≤ m - k := by omega
    exact hgap_le_mk.trans hWindow
  have hgap_le_window_real : ((m - j : ℕ) : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast hgap_le_window_nat
  have hcoef_nonneg : 0 ≤ 2 * hc.rhoM :=
    mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hc.rhoM_pos)
  have hexp_le :
      2 * hc.rhoM * ((m - j : ℕ) : ℝ) ≤ 2 * hc.rhoM * (L : ℝ) := by
    exact mul_le_mul_of_nonneg_left hgap_le_window_real hcoef_nonneg
  rw [terminalStochasticWeakWeight_inv_sq_eq]
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp_le)

/--
Source labels `M_m^st` and `l.S.and.J`: the finite-window inverse-weak-weight
loss in the integrated stochastic insertion is bounded by a constant depending
only on the window length and `rho_M`, not on an additional relation between
LIH's Section 5.3 exponent and `rho_M`.
-/
theorem section53CoarseFluctuationScaleWeight_mul_terminalStochasticWeakWeight_inv_sq_sum_le_windowConstant
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hc : HighContrastExponents d) {k m L : ℕ} (hWindow : m - k ≤ L) :
    ∑ j ∈ Finset.Icc (k + 1) m,
        ENNReal.ofReal (section53CoarseFluctuationScaleWeight hP4 m j) *
          (terminalStochasticWeakWeight (d := d) hc m j
              (Homogenization.originCube d (j : ℤ)))⁻¹ ^ 2 ≤
      (L : ENNReal) * ENNReal.ofReal ((3 : ℝ) ^ (2 * hc.rhoM * (L : ℝ))) := by
  classical
  let S := Finset.Icc (k + 1) m
  let C : ENNReal := ENNReal.ofReal ((3 : ℝ) ^ (2 * hc.rhoM * (L : ℝ)))
  have hterm :
      ∀ j ∈ S,
        ENNReal.ofReal (section53CoarseFluctuationScaleWeight hP4 m j) *
            (terminalStochasticWeakWeight (d := d) hc m j
              (Homogenization.originCube d (j : ℤ)))⁻¹ ^ 2 ≤ C := by
    intro j hj
    have hweight_le_one :
        ENNReal.ofReal (section53CoarseFluctuationScaleWeight hP4 m j) ≤ 1 := by
      simpa using
        ENNReal.ofReal_le_ofReal
          (section53CoarseFluctuationScaleWeight_le_one hP4 m j)
    have hinv_le :
        (terminalStochasticWeakWeight (d := d) hc m j
            (Homogenization.originCube d (j : ℤ)))⁻¹ ^ 2 ≤ C := by
      simpa [C] using
        terminalStochasticWeakWeight_inv_sq_le_of_mem_Icc_of_sub_le
          (d := d) hc hj hWindow (Homogenization.originCube d (j : ℤ))
    calc
      ENNReal.ofReal (section53CoarseFluctuationScaleWeight hP4 m j) *
          (terminalStochasticWeakWeight (d := d) hc m j
            (Homogenization.originCube d (j : ℤ)))⁻¹ ^ 2
          ≤ 1 * C := mul_le_mul' hweight_le_one hinv_le
      _ = C := one_mul C
  have hcard : S.card = m - k := by
    dsimp [S]
    rw [Nat.card_Icc]
    omega
  have hcard_le : ((m - k : ℕ) : ENNReal) ≤ (L : ENNReal) := by
    exact_mod_cast hWindow
  calc
    ∑ j ∈ Finset.Icc (k + 1) m,
        ENNReal.ofReal (section53CoarseFluctuationScaleWeight hP4 m j) *
          (terminalStochasticWeakWeight (d := d) hc m j
              (Homogenization.originCube d (j : ℤ)))⁻¹ ^ 2 =
        ∑ j ∈ S,
          ENNReal.ofReal (section53CoarseFluctuationScaleWeight hP4 m j) *
            (terminalStochasticWeakWeight (d := d) hc m j
                (Homogenization.originCube d (j : ℤ)))⁻¹ ^ 2 := rfl
    _ ≤ ∑ _j ∈ S, C := by
          exact Finset.sum_le_sum hterm
    _ = (S.card : ENNReal) * C := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((m - k : ℕ) : ENNReal) * C := by
          rw [hcard]
    _ ≤ (L : ENNReal) * C := by
          exact mul_le_mul' hcard_le le_rfl
    _ = (L : ENNReal) *
        ENNReal.ofReal ((3 : ℝ) ^ (2 * hc.rhoM * (L : ℝ))) := rfl

end Homogenization.HighContrast.EntryScale
