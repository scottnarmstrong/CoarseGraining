import Homogenization.Book.Ch04.Theorems.DilationLaw
import Homogenization.Book.MainResults
import Homogenization.Geometry.ConvexDomain
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Bernoulli checkerboard examples

This file constructs the scalar Bernoulli checkerboard law on coefficient
fields.  The random medium is indexed by `ℤ^d`; each open unit cube centered at
an integer lattice point receives conductance `lam` or `Lam`, while cell walls
are assigned the deterministic value `lam`.  The deterministic wall convention
keeps stationarity and signed-permutation invariance exact for pointwise
coefficient fields.
-/

namespace Homogenization
namespace Examples
namespace RandomCheckerboard

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Integer lattice indices for checkerboard cells. -/
abbrev Lattice (d : ℕ) :=
  Fin d → ℤ

/-- A checkerboard environment: one coin at each lattice cell. -/
abbrev Sample (d : ℕ) :=
  Lattice d → Bool

/-- The open unit cube centered at `z`. -/
def openUnitCell {d : ℕ} (z : Lattice d) : Set (Vec d) :=
  {x | ∀ i : Fin d, |x i - (z i : ℝ)| < (1 / 2 : ℝ)}

/-- Open checkerboard cells are Borel-measurable. -/
theorem measurableSet_openUnitCell {d : ℕ} (z : Lattice d) :
    MeasurableSet (openUnitCell z : Set (Vec d)) := by
  classical
  have hopen : IsOpen (openUnitCell z : Set (Vec d)) := by
    unfold openUnitCell
    have hset :
        {x : Vec d | ∀ i : Fin d, |x i - (z i : ℝ)| < (1 / 2 : ℝ)} =
          ⋂ i : Fin d, {x : Vec d | |x i - (z i : ℝ)| < (1 / 2 : ℝ)} := by
      ext x
      simp
    rw [hset]
    refine isOpen_iInter_of_finite fun i : Fin d => ?_
    have hleft : Continuous fun x : Vec d => |x i - (z i : ℝ)| :=
      ((continuous_apply i).sub continuous_const).abs
    have hright : Continuous fun _ : Vec d => (1 / 2 : ℝ) :=
      continuous_const
    exact isOpen_lt hleft hright
  exact hopen.measurableSet

/-- The set of lattice cells whose open interiors meet `U`. -/
def cellsMeeting {d : ℕ} (U : Set (Vec d)) : Set (Lattice d) :=
  {z | ∃ x ∈ U, x ∈ openUnitCell z}

/-- A point belongs to at most one open unit cell. -/
theorem openUnitCell_unique {d : ℕ} {x : Vec d} {z w : Lattice d}
    (hz : x ∈ openUnitCell z) (hw : x ∈ openUnitCell w) :
    z = w := by
  funext i
  by_contra hne
  have hzw_int : (1 : ℤ) ≤ |z i - w i| :=
    Int.one_le_abs (sub_ne_zero.mpr hne)
  have hzw : (1 : ℝ) ≤ |(z i : ℝ) - (w i : ℝ)| := by
    rw [← Int.cast_sub, ← Int.cast_abs]
    exact_mod_cast hzw_int
  have hz_i := hz i
  have hw_i := hw i
  have hsplit :
      (z i : ℝ) - (w i : ℝ) =
        - (x i - (z i : ℝ)) + (x i - (w i : ℝ)) := by ring
  have htriangle :
      |(z i : ℝ) - (w i : ℝ)| <
        (1 / 2 : ℝ) + (1 / 2 : ℝ) := by
    calc
      |(z i : ℝ) - (w i : ℝ)|
          = |- (x i - (z i : ℝ)) + (x i - (w i : ℝ))| := by rw [hsplit]
      _ ≤ |-(x i - (z i : ℝ))| + |x i - (w i : ℝ)| := abs_add_le _ _
      _ = |x i - (z i : ℝ)| + |x i - (w i : ℝ)| := by rw [abs_neg]
      _ < (1 / 2 : ℝ) + (1 / 2 : ℝ) := add_lt_add hz_i hw_i
  norm_num at htriangle
  linarith

/-- If a point lies in an open cell, the chosen cell used by `scalarAt` is that
cell. -/
theorem choose_openUnitCell_eq {d : ℕ} {x : Vec d} {z : Lattice d}
    (hz : x ∈ openUnitCell z) :
    Classical.choose (show ∃ w : Lattice d, x ∈ openUnitCell w from ⟨z, hz⟩) = z := by
  classical
  let h : ∃ w : Lattice d, x ∈ openUnitCell w := ⟨z, hz⟩
  change Classical.choose h = z
  exact openUnitCell_unique (Classical.choose_spec h) hz

/-- Bounded observation sets meet only finitely many open checkerboard cells. -/
theorem finite_cellsMeeting_of_isBounded {d : ℕ} {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) :
    (cellsMeeting U).Finite := by
  classical
  rcases Bornology.IsBounded.isBoundedDomain hU with ⟨R, hRpos, hR⟩
  let N : ℤ := ⌈R + 1⌉
  have hfiniteBox :
      ({z : Lattice d | ∀ i : Fin d, z i ∈ Set.Icc (-N) N}).Finite := by
    simpa using
      (Set.Finite.pi' (fun _ : Fin d => (Set.finite_Icc (-N) N)))
  refine hfiniteBox.subset ?_
  intro z hz i
  rcases hz with ⟨x, hxU, hxz⟩
  have hxR : |x i| ≤ R := hR x hxU i
  have hxz_i : |x i - (z i : ℝ)| < (1 / 2 : ℝ) := hxz i
  have hz_abs : |(z i : ℝ)| ≤ R + 1 := by
    calc
      |(z i : ℝ)|
          = |x i - (x i - (z i : ℝ))| := by congr 1; ring
      _ ≤ |x i| + |x i - (z i : ℝ)| := by
            have htri := abs_sub_le (x i) 0 (x i - (z i : ℝ))
            simpa [abs_sub_comm (z i : ℝ) (x i)] using htri
      _ ≤ R + 1 := by linarith
  have hceil : R + 1 ≤ (N : ℝ) := by
    simpa [N] using (Int.le_ceil (R + 1))
  have hleN_real : (z i : ℝ) ≤ (N : ℝ) :=
    (le_abs_self (z i : ℝ)).trans (hz_abs.trans hceil)
  have hnegN_real : (-(N : ℤ) : ℝ) ≤ (z i : ℝ) := by
    have hneg : -(R + 1) ≤ (z i : ℝ) := by
      have hnegabs : -|(z i : ℝ)| ≤ (z i : ℝ) := by
        have h := le_abs_self (-(z i : ℝ))
        rw [abs_neg] at h
        linarith
      linarith
    have hN : (-(N : ℤ) : ℝ) ≤ -(R + 1) := by
      norm_num [Int.cast_neg]
      linarith
    exact hN.trans hneg
  constructor
  · exact_mod_cast hnegN_real
  · exact_mod_cast hleN_real

/-- Conductance value associated with a coin.  `true` is heads and gives
`lam`; `false` gives `Lam`. -/
def coinConductance (lam Lam : ℝ) (b : Bool) : ℝ :=
  if b then lam else Lam

/-- A deterministic representative on walls and a random scalar value in the
unique open unit cell containing the point. -/
def scalarAt (lam Lam : ℝ) {d : ℕ} (ω : Sample d) (x : Vec d) : ℝ :=
  by
    classical
    exact
      if h : ∃ z : Lattice d, x ∈ openUnitCell z then
        coinConductance lam Lam (ω (Classical.choose h))
      else
        lam

/-- The scalar Bernoulli checkerboard coefficient field. -/
def coeffField (lam Lam : ℝ) {d : ℕ} (ω : Sample d) : CoeffField d :=
  fun x => scalarMatrix (d := d) (scalarAt lam Lam ω x)

theorem scalarAt_of_mem_openUnitCell {d : ℕ} {lam Lam : ℝ}
    {ω : Sample d} {x : Vec d} {z : Lattice d}
    (hz : x ∈ openUnitCell z) :
    scalarAt lam Lam ω x = coinConductance lam Lam (ω z) := by
  classical
  unfold scalarAt
  let h : ∃ w : Lattice d, x ∈ openUnitCell w := ⟨z, hz⟩
  rw [dif_pos h]
  congr 1
  exact congrArg ω (openUnitCell_unique (Classical.choose_spec h) hz)

theorem scalarAt_of_not_mem_any_openUnitCell {d : ℕ} {lam Lam : ℝ}
    {ω : Sample d} {x : Vec d}
    (hx : ¬ ∃ z : Lattice d, x ∈ openUnitCell z) :
    scalarAt lam Lam ω x = lam := by
  classical
  unfold scalarAt
  rw [dif_neg hx]

/-- The region where the checkerboard scalar takes the upper value `Lam`. -/
def upperConductanceRegion {d : ℕ} (ω : Sample d) : Set (Vec d) :=
  ⋃ z : {z : Lattice d // ω z = false}, openUnitCell z.1

theorem measurableSet_upperConductanceRegion {d : ℕ} (ω : Sample d) :
    MeasurableSet (upperConductanceRegion ω : Set (Vec d)) := by
  classical
  unfold upperConductanceRegion
  exact MeasurableSet.iUnion fun z => measurableSet_openUnitCell z.1

theorem scalarAt_eq_if_upperConductanceRegion {d : ℕ} {lam Lam : ℝ}
    {ω : Sample d} {x : Vec d} :
    scalarAt lam Lam ω x =
      if x ∈ upperConductanceRegion ω then Lam else lam := by
  classical
  by_cases hxUpper : x ∈ upperConductanceRegion ω
  · rcases Set.mem_iUnion.mp hxUpper with ⟨z, hxz⟩
    have hcell : x ∈ openUnitCell z.1 := hxz
    have hz : ω z.1 = false := z.2
    simp [scalarAt_of_mem_openUnitCell (lam := lam) (Lam := Lam) (ω := ω) hcell,
      coinConductance, hz, hxUpper]
  · by_cases hx : ∃ z : Lattice d, x ∈ openUnitCell z
    · let z : Lattice d := Classical.choose hx
      have hzcell : x ∈ openUnitCell z := Classical.choose_spec hx
      have hztrue : ω z = true := by
        cases hωz : ω z
        · exact False.elim (hxUpper (Set.mem_iUnion.2 ⟨⟨z, hωz⟩, hzcell⟩))
        · rfl
      simp [scalarAt_of_mem_openUnitCell (lam := lam) (Lam := Lam) (ω := ω) hzcell,
        coinConductance, hztrue, hxUpper]
    · simp [scalarAt_of_not_mem_any_openUnitCell (lam := lam) (Lam := Lam) (ω := ω) hx,
        hxUpper]

/-- For each sample, the scalar checkerboard representative is Borel-measurable
in space. -/
theorem measurable_scalarAt_spatial {d : ℕ} {lam Lam : ℝ} (ω : Sample d) :
    Measurable (fun x : Vec d => scalarAt lam Lam ω x) := by
  classical
  have hpiece :
      Measurable
        ((upperConductanceRegion ω).piecewise
          (fun _ : Vec d => Lam) (fun _ : Vec d => lam)) :=
    Measurable.piecewise (measurableSet_upperConductanceRegion ω)
      measurable_const measurable_const
  convert hpiece using 1
  funext x
  simp [Set.piecewise, scalarAt_eq_if_upperConductanceRegion]

theorem measurable_coeffField_spatial {d : ℕ} {lam Lam : ℝ} (ω : Sample d) :
    Measurable (fun x : Vec d => coeffField lam Lam ω x) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  by_cases hij : i = j
  · subst j
    simpa [coeffField, scalarMatrix] using measurable_scalarAt_spatial (lam := lam) (Lam := Lam) ω
  · simp [coeffField, scalarMatrix, hij]

theorem scalarAt_eq_lam_or_Lam {d : ℕ} {lam Lam : ℝ} (ω : Sample d) (x : Vec d) :
    scalarAt lam Lam ω x = lam ∨ scalarAt lam Lam ω x = Lam := by
  rw [scalarAt_eq_if_upperConductanceRegion]
  by_cases hx : x ∈ upperConductanceRegion ω <;> simp [hx]

theorem scalarMatrix_isEllipticMatrix_between {d : ℕ} {lam Lam sigma : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) (hsigma : sigma = lam ∨ sigma = Lam) :
    IsEllipticMatrix lam Lam (scalarMatrix (d := d) sigma) := by
  rcases hsigma with hsigma | hsigma
  · subst sigma
    exact (isEllipticMatrix_scalarMatrix (d := d) hlam).mono hlam le_rfl hle
  · subst sigma
    have hLam : 0 < Lam := lt_of_lt_of_le hlam hle
    exact (isEllipticMatrix_scalarMatrix (d := d) hLam).mono hlam hle le_rfl

theorem coeffField_aeeEllipticOn {d : ℕ} {lam Lam : ℝ} (ω : Sample d)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hlam : 0 < lam) (hle : lam ≤ Lam) :
    Book.Ch04.AEEllipticOn lam Lam U (coeffField lam Lam ω) := by
  refine ⟨hU, ?_, ?_⟩
  · intro i j
    have hentry :
        Measurable fun x : Vec d => restrictCoeffField U (coeffField lam Lam ω) x i j := by
      by_cases hij : i = j
      · subst j
        have hscalar := measurable_scalarAt_spatial (d := d) (lam := lam) (Lam := Lam) ω
        have hpiece :
            Measurable
              (U.piecewise
                (fun x : Vec d => scalarAt lam Lam ω x)
                (fun _ : Vec d => 0)) :=
          Measurable.piecewise hU hscalar measurable_const
        convert hpiece using 1
        funext x
        by_cases hx : x ∈ U <;> simp [Set.piecewise, restrictCoeffField, coeffField,
          scalarMatrix, hx]
      · have hzero :
            (fun x : Vec d => restrictCoeffField U (coeffField lam Lam ω) x i j) =
              fun _ : Vec d => 0 := by
          funext x
          by_cases hx : x ∈ U <;> simp [restrictCoeffField, coeffField, scalarMatrix, hx, hij]
        rw [hzero]
        exact measurable_const
    exact hentry.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x =>
      scalarMatrix_isEllipticMatrix_between (d := d) hlam hle
        (scalarAt_eq_lam_or_Lam (lam := lam) (Lam := Lam) ω x)

/-- Triadic rescaling preserves the deterministic ellipticity bounds of each
checkerboard sample. -/
theorem rescaleCoeffField_coeffField_aeeEllipticOn {d : ℕ} {lam Lam : ℝ}
    (k : ℕ) (ω : Sample d) {U : Set (Vec d)}
    (hU : MeasurableSet U) (hlam : 0 < lam) (hle : lam ≤ Lam) :
    Book.Ch04.AEEllipticOn lam Lam U (rescaleCoeffField k (coeffField lam Lam ω)) := by
  refine ⟨hU, ?_, ?_⟩
  · intro i j
    have hentry :
        Measurable fun x : Vec d =>
          restrictCoeffField U (rescaleCoeffField k (coeffField lam Lam ω)) x i j := by
      by_cases hij : i = j
      · subst j
        have hdil : Continuous (triadicDilateVec (d := d) k) := by
          change Continuous fun x : Fin d → ℝ => fun i => (3 : ℝ) ^ k * x i
          exact continuous_pi fun i => continuous_const.mul (continuous_apply i)
        have hscalar :
            Measurable fun x : Vec d => scalarAt lam Lam ω (triadicDilateVec k x) :=
          (measurable_scalarAt_spatial (d := d) (lam := lam) (Lam := Lam) ω).comp
            hdil.measurable
        have hpiece :
            Measurable
              (U.piecewise
                (fun x : Vec d => scalarAt lam Lam ω (triadicDilateVec k x))
                (fun _ : Vec d => 0)) :=
          Measurable.piecewise hU hscalar measurable_const
        convert hpiece using 1
        funext x
        by_cases hx : x ∈ U <;> simp [Set.piecewise, restrictCoeffField,
          rescaleCoeffField, coeffField, scalarMatrix, hx]
      · have hzero :
            (fun x : Vec d =>
                restrictCoeffField U (rescaleCoeffField k (coeffField lam Lam ω)) x i j) =
              fun _ : Vec d => 0 := by
          funext x
          by_cases hx : x ∈ U <;> simp [restrictCoeffField, rescaleCoeffField,
            coeffField, scalarMatrix, hx, hij]
        rw [hzero]
        exact measurable_const
    exact hentry.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x =>
      by
        simpa [rescaleCoeffField, coeffField] using
          scalarMatrix_isEllipticMatrix_between (d := d) hlam hle
            (scalarAt_eq_lam_or_Lam (lam := lam) (Lam := Lam) ω (triadicDilateVec k x))

/-- Restrict a sample to a finite set of lattice coordinates. -/
def sampleRestriction {d : ℕ} (F : Finset (Lattice d)) (ω : Sample d) :
    F → Bool :=
  fun z => ω z

/-- Extend finite coordinate data to a sample, using `false` off the finite set. -/
def sampleFromRestriction {d : ℕ} (F : Finset (Lattice d)) (η : F → Bool) :
    Sample d :=
  fun z => if h : z ∈ F then η ⟨z, h⟩ else false

theorem sampleFromRestriction_sampleRestriction_eq_on {d : ℕ}
    (F : Finset (Lattice d)) (ω : Sample d) :
    ∀ z ∈ F, sampleFromRestriction F (sampleRestriction F ω) z = ω z := by
  intro z hz
  simp [sampleFromRestriction, sampleRestriction, hz]

theorem coeffField_localAgreement_of_eq_on_cells {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} {F : Finset (Lattice d)} {ω ω' : Sample d}
    (hF : cellsMeeting U ⊆ (F : Set (Lattice d)))
    (hω : ∀ z ∈ F, ω z = ω' z) :
    LocalAgreementOn U (coeffField lam Lam ω) (coeffField lam Lam ω') := by
  classical
  intro x hxU
  by_cases hx : ∃ z : Lattice d, x ∈ openUnitCell z
  · let z : Lattice d := Classical.choose hx
    have hzcell : x ∈ openUnitCell z := Classical.choose_spec hx
    have hzF : z ∈ F := hF ⟨x, hxU, hzcell⟩
    simp [coeffField, scalarAt_of_mem_openUnitCell (lam := lam) (Lam := Lam)
      (ω := ω) hzcell,
      scalarAt_of_mem_openUnitCell (lam := lam) (Lam := Lam) (ω := ω') hzcell,
      hω z hzF]
  · simp [coeffField, scalarAt_of_not_mem_any_openUnitCell
      (lam := lam) (Lam := Lam) (ω := ω) hx,
      scalarAt_of_not_mem_any_openUnitCell
        (lam := lam) (Lam := Lam) (ω := ω') hx]

theorem measurable_sampleRestriction {d : ℕ} (F : Finset (Lattice d)) :
    Measurable (sampleRestriction (d := d) F) := by
  refine measurable_pi_iff.2 fun z => ?_
  simpa [sampleRestriction] using
    (measurable_pi_apply (z : Lattice d) :
      Measurable fun ω : Sample d => ω (z : Lattice d))

/-- The sigma-algebra generated by one lattice coin. -/
def sampleCoordinateSigma {d : ℕ} (z : Lattice d) : MeasurableSpace (Sample d) :=
  MeasurableSpace.comap (fun ω : Sample d => ω z) inferInstance

/-- The sigma-algebra generated by all coins in a set of lattice cells. -/
def sampleCellsSigma {d : ℕ} (S : Set (Lattice d)) : MeasurableSpace (Sample d) :=
  ⨆ z : Lattice d, ⨆ _ : z ∈ S, sampleCoordinateSigma z

theorem measurable_eval_sampleCellsSigma {d : ℕ} {S : Set (Lattice d)}
    {z : Lattice d} (hz : z ∈ S) :
    @Measurable (Sample d) Bool (sampleCellsSigma S) inferInstance (fun ω => ω z) := by
  letI : MeasurableSpace (Sample d) := sampleCellsSigma S
  change Measurable (fun ω : Sample d => ω z)
  rw [measurable_iff_comap_le]
  exact le_iSup_of_le z (le_iSup_of_le hz le_rfl)

theorem measurable_sampleRestriction_sampleCellsSigma {d : ℕ}
    {S : Set (Lattice d)} (F : Finset (Lattice d)) (hF : (F : Set (Lattice d)) ⊆ S) :
    @Measurable (Sample d) (F → Bool) (sampleCellsSigma S) inferInstance
      (sampleRestriction (d := d) F) := by
  letI : MeasurableSpace (Sample d) := sampleCellsSigma S
  change Measurable (sampleRestriction (d := d) F)
  refine measurable_pi_iff.2 fun z => ?_
  simpa [sampleRestriction] using
    measurable_eval_sampleCellsSigma (S := S) (z := (z : Lattice d)) (hF z.2)

theorem cellsMeeting_inter_subset_left {d : ℕ} (U W : Set (Vec d)) :
    cellsMeeting (U ∩ W) ⊆ cellsMeeting U := by
  intro z hz
  rcases hz with ⟨x, hx, hxz⟩
  exact ⟨x, hx.1, hxz⟩

theorem restrictCoeffField_coeffField_localAgreement_of_eq_on_cells {d : ℕ}
    {lam Lam : ℝ} {U W : Set (Vec d)} {F : Finset (Lattice d)}
    {ω ω' : Sample d}
    (hF : cellsMeeting (U ∩ W) ⊆ (F : Set (Lattice d)))
    (hω : ∀ z ∈ F, ω z = ω' z) :
    LocalAgreementOn W
      (restrictCoeffField U (coeffField lam Lam ω))
      (restrictCoeffField U (coeffField lam Lam ω')) := by
  intro x hxW
  by_cases hxU : x ∈ U
  · have hagree :
      LocalAgreementOn (U ∩ W) (coeffField lam Lam ω) (coeffField lam Lam ω') :=
      coeffField_localAgreement_of_eq_on_cells (lam := lam) (Lam := Lam)
        (U := U ∩ W) (F := F) hF hω
    simp [restrictCoeffField, hxU, hagree x ⟨hxU, hxW⟩]
  · simp [restrictCoeffField, hxU]

theorem measurable_restrictCoeffField_coeffField_localSigma_sampleCellsSigma {d : ℕ}
    {lam Lam : ℝ} (U W : Set (Vec d)) (hW : Bornology.IsBounded W) :
    @Measurable (Sample d) (CoeffField d) (sampleCellsSigma (cellsMeeting U)) (LocalSigma W)
      (fun ω => restrictCoeffField U (coeffField lam Lam ω)) := by
  classical
  letI : MeasurableSpace (Sample d) := sampleCellsSigma (cellsMeeting U)
  change @Measurable (Sample d) (CoeffField d) this (LocalSigma W)
    (fun ω : Sample d => restrictCoeffField U (coeffField lam Lam ω))
  refine measurable_generateFrom ?_
  intro s hs
  let hfinite := finite_cellsMeeting_of_isBounded (d := d) (U := U ∩ W)
    (hW.subset Set.inter_subset_right)
  let F : Finset (Lattice d) := hfinite.toFinset
  have hF_local : cellsMeeting (U ∩ W) ⊆ (F : Set (Lattice d)) := by
    intro z hz
    exact hfinite.mem_toFinset.2 hz
  have hF_cells : (F : Set (Lattice d)) ⊆ cellsMeeting U := by
    intro z hz
    exact cellsMeeting_inter_subset_left U W (hfinite.mem_toFinset.1 hz)
  let target : Set (F → Bool) :=
    {η | restrictCoeffField U (coeffField lam Lam (sampleFromRestriction F η)) ∈ s}
  have htarget : MeasurableSet target := by
    exact (Set.toFinite target).measurableSet
  have hpre :
      (fun ω : Sample d => restrictCoeffField U (coeffField lam Lam ω)) ⁻¹' s =
        (sampleRestriction F) ⁻¹' target := by
    ext ω
    have hagree :
        LocalAgreementOn W
          (restrictCoeffField U
            (coeffField lam Lam (sampleFromRestriction F (sampleRestriction F ω))))
          (restrictCoeffField U (coeffField lam Lam ω)) := by
      exact restrictCoeffField_coeffField_localAgreement_of_eq_on_cells
        (lam := lam) (Lam := Lam) (U := U) (W := W) (F := F) hF_local
        (sampleFromRestriction_sampleRestriction_eq_on F ω)
    have hiff := hs hagree
    simp [target, hiff]
  rw [hpre]
  exact (measurable_sampleRestriction_sampleCellsSigma (S := cellsMeeting U) F hF_cells) htarget

theorem measurable_restrictCoeffField_coeffField_sampleCellsSigma {d : ℕ}
    {lam Lam : ℝ} (U : Set (Vec d)) :
    @Measurable (Sample d) (CoeffField d) (sampleCellsSigma (cellsMeeting U))
      (instMeasurableSpaceCoeffField d)
      (fun ω => restrictCoeffField U (coeffField lam Lam ω)) := by
  classical
  letI : MeasurableSpace (Sample d) := sampleCellsSigma (cellsMeeting U)
  change Measurable (fun ω : Sample d => restrictCoeffField U (coeffField lam Lam ω))
  refine measurable_to_coeffField_ambient
    (d := d) (f := fun ω => restrictCoeffField U (coeffField lam Lam ω)) ?_ ?_
  · refine measurable_pi_iff.2 fun x => measurable_pi_iff.2 fun i =>
      measurable_pi_iff.2 fun j => ?_
    by_cases hxU : x ∈ U
    · by_cases hxcell : ∃ z : Lattice d, x ∈ openUnitCell z
      · let z : Lattice d := Classical.choose hxcell
        have hzcell : x ∈ openUnitCell z := Classical.choose_spec hxcell
        have hz : z ∈ cellsMeeting U := ⟨x, hxU, hzcell⟩
        have hcoin :
            @Measurable (Sample d) ℝ (sampleCellsSigma (cellsMeeting U)) inferInstance
              (fun ω => coinConductance lam Lam (ω z)) :=
          (measurable_of_finite (coinConductance lam Lam)).comp
            (measurable_eval_sampleCellsSigma (S := cellsMeeting U) hz)
        by_cases hij : i = j
        · subst j
          convert hcoin using 1
          funext ω
          simp [restrictCoeffField, coeffField, scalarMatrix, hxU,
            scalarAt_of_mem_openUnitCell (lam := lam) (Lam := Lam) (ω := ω) hzcell]
        · simp [restrictCoeffField, coeffField, scalarMatrix, hxU, hij]
      · by_cases hij : i = j
        · subst j
          have hconst :
              (fun ω : Sample d =>
                restrictCoeffField U (coeffField lam Lam ω) x i i) =
                fun _ : Sample d => lam := by
            funext ω
            simp [restrictCoeffField, coeffField, scalarMatrix, hxU,
              scalarAt_of_not_mem_any_openUnitCell (lam := lam) (Lam := Lam) (ω := ω) hxcell]
          rw [hconst]
          exact measurable_const
        · simp [restrictCoeffField, coeffField, scalarMatrix, hxU, hij]
    · simp [restrictCoeffField, hxU]
  · intro W hW
    exact measurable_restrictCoeffField_coeffField_localSigma_sampleCellsSigma
      (d := d) (lam := lam) (Lam := Lam) U W hW

theorem measurable_coeffField_restrictionSigma_sampleCellsSigma {d : ℕ}
    {lam Lam : ℝ} (U : Set (Vec d)) :
    @Measurable (Sample d) (CoeffField d) (sampleCellsSigma (cellsMeeting U))
      (RestrictionSigma U) (coeffField lam Lam) := by
  letI : MeasurableSpace (Sample d) := sampleCellsSigma (cellsMeeting U)
  rw [measurable_iff_comap_le]
  rw [RestrictionSigma, MeasurableSpace.comap_comp]
  exact (measurable_restrictCoeffField_coeffField_sampleCellsSigma
    (d := d) (lam := lam) (Lam := Lam) U).comap_le

theorem measurable_coeffField_localSigma {d : ℕ} {lam Lam : ℝ}
    (U : Set (Vec d)) (hU : Bornology.IsBounded U) :
    @Measurable (Sample d) (CoeffField d) inferInstance (LocalSigma U)
      (coeffField lam Lam) := by
  classical
  refine measurable_generateFrom ?_
  intro s hs
  let hfinite := finite_cellsMeeting_of_isBounded (d := d) (U := U) hU
  let F : Finset (Lattice d) := hfinite.toFinset
  have hF : cellsMeeting U ⊆ (F : Set (Lattice d)) := by
    intro z hz
    exact hfinite.mem_toFinset.2 hz
  let target : Set (F → Bool) :=
    {η | coeffField lam Lam (sampleFromRestriction F η) ∈ s}
  have htarget : MeasurableSet target := by
    exact (Set.toFinite target).measurableSet
  have hpre :
      (coeffField lam Lam : Sample d → CoeffField d) ⁻¹' s =
        (sampleRestriction F) ⁻¹' target := by
    ext ω
    have hagree :
        LocalAgreementOn U
          (coeffField lam Lam (sampleFromRestriction F (sampleRestriction F ω)))
          (coeffField lam Lam ω) := by
      exact coeffField_localAgreement_of_eq_on_cells (lam := lam) (Lam := Lam)
        (U := U) (F := F) hF
        (sampleFromRestriction_sampleRestriction_eq_on F ω)
    have hiff := hs hagree
    simp [target, hiff]
  rw [hpre]
  exact measurable_sampleRestriction F htarget

theorem measurable_coeffField {d : ℕ} {lam Lam : ℝ} :
    @Measurable (Sample d) (CoeffField d) inferInstance
      (instMeasurableSpaceCoeffField d) (coeffField (d := d) lam Lam) := by
  classical
  refine measurable_to_coeffField_ambient (d := d) (f := coeffField lam Lam) ?_ ?_
  · refine measurable_pi_iff.2 fun x => measurable_pi_iff.2 fun i =>
      measurable_pi_iff.2 fun j => ?_
    by_cases hx : ∃ z : Lattice d, x ∈ openUnitCell z
    · let z : Lattice d := Classical.choose hx
      have hcoin : Measurable fun ω : Sample d => coinConductance lam Lam (ω z) :=
        (measurable_of_finite (coinConductance lam Lam)).comp (measurable_pi_apply z)
      by_cases hij : i = j
      · subst j
        simpa [coeffField, scalarAt, hx, scalarMatrix] using hcoin
      · simp [coeffField, scalarAt, hx, scalarMatrix, hij]
    · by_cases hij : i = j
      · subst j
        simp [coeffField, scalarAt, hx, scalarMatrix]
      · simp [coeffField, scalarAt, hx, scalarMatrix, hij]
  · intro U hU
    exact measurable_coeffField_localSigma (d := d) (lam := lam) (Lam := Lam) U hU

/-- The Bernoulli measure on a single coin. -/
def coinMeasure (p : ℝ≥0) (hp : p ≤ 1) : Measure Bool :=
  (PMF.bernoulli p hp).toMeasure

instance instIsProbabilityMeasure_coinMeasure (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (coinMeasure p hp) :=
  PMF.toMeasure.isProbabilityMeasure (PMF.bernoulli p hp)

/-- The product Bernoulli law on all lattice coins. -/
def sampleMeasure (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : Measure (Sample d) :=
  Measure.infinitePi (fun _ : Lattice d => coinMeasure p hp)

instance instIsProbabilityMeasure_sampleMeasure (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (sampleMeasure d p hp) := by
  rw [sampleMeasure]
  infer_instance

/-- The unscaled checkerboard coefficient-field law. -/
def law (d : ℕ) (lam Lam : ℝ) (p : ℝ≥0) (hp : p ≤ 1) : Book.Ch04.CoeffLaw d :=
  Measure.map (coeffField lam Lam) (sampleMeasure d p hp)

theorem isProbabilityMeasure_law (d : ℕ) (lam Lam : ℝ) (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (law d lam Lam p hp) := by
  rw [law]
  exact Measure.isProbabilityMeasure_map
    (measurable_coeffField (d := d) (lam := lam) (Lam := Lam)).aemeasurable

theorem measurableSet_uniformEllipticitySupport {d : ℕ} {lam Lam : ℝ} :
    MeasurableSet
      {a : CoeffField d |
        ∀ Q : TriadicCube d,
          Book.Ch04.AEEllipticOn lam Lam (openCubeSet Q) a} := by
  have hQ :
      ∀ Q : TriadicCube d,
        MeasurableSet
          {a : CoeffField d | Book.Ch04.AEEllipticOn lam Lam (openCubeSet Q) a} := by
    intro Q
    exact localSigma_le_coeffField_of_isBounded (isBounded_openCubeSet Q) _
      (IsAEEllipticFieldOn.measurableSet_localSigma lam Lam (openCubeSet Q))
  simpa [Set.iInter_setOf] using
    (MeasurableSet.iInter hQ :
      MeasurableSet
        (⋂ Q : TriadicCube d,
          {a : CoeffField d | Book.Ch04.AEEllipticOn lam Lam (openCubeSet Q) a}))

theorem law_uniformEllipticityBounds {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) (p : ℝ≥0) (hp : p ≤ 1) :
    Book.MainResults.UniformEllipticityBounds (law d lam Lam p hp) lam Lam where
  lam_pos := hlam
  lam_le_Lam := hle
  aee_elliptic := by
    rw [law]
    exact
      (ae_map_iff
        (measurable_coeffField (d := d) (lam := lam) (Lam := Lam)).aemeasurable
        (measurableSet_uniformEllipticitySupport (d := d) (lam := lam) (Lam := Lam))).2
        (Filter.Eventually.of_forall fun ω Q =>
          coeffField_aeeEllipticOn (d := d) (lam := lam) (Lam := Lam) ω
            (measurableSet_openCubeSet Q) hlam hle)

theorem lawCarrier {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) (p : ℝ≥0) (hp : p ≤ 1) :
    Book.Ch04.LawCarrier (law d lam Lam p hp) := by
  letI : IsProbabilityMeasure (law d lam Lam p hp) :=
    isProbabilityMeasure_law d lam Lam p hp
  exact Book.Ch04.lawCarrier_of_aeLocallyUniformlyElliptic
    (law_uniformEllipticityBounds (d := d) hlam hle p hp).toAELocallyUniformlyEllipticLaw

/-- Translate lattice indices by an integer vector. -/
def translateLattice {d : ℕ} (z : Lattice d) (w : Lattice d) : Lattice d :=
  fun i => w i + z i

/-- Translation of lattice indices is a bijection. -/
def translateLatticeEquiv {d : ℕ} (z : Lattice d) : Lattice d ≃ Lattice d where
  toFun := translateLattice z
  invFun := fun w i => w i - z i
  left_inv := by
    intro w
    funext i
    simp [translateLattice]
  right_inv := by
    intro w
    funext i
    simp [translateLattice]

/-- Shift a sample so that cell `w` reads the old coin at `w + z`. -/
def shiftSample {d : ℕ} (z : Lattice d) (ω : Sample d) : Sample d :=
  fun w => ω (translateLattice z w)

theorem shiftSample_eq_piCongrLeft {d : ℕ} (z : Lattice d) :
    shiftSample z =
      (MeasurableEquiv.piCongrLeft (fun _ : Lattice d => Bool)
        (translateLatticeEquiv z).symm) := by
  funext ω w
  have h :=
    MeasurableEquiv.piCongrLeft_apply_apply
      (e := (translateLatticeEquiv z).symm)
      (β := fun _ : Lattice d => Bool) ω ((translateLatticeEquiv z) w)
  simpa [shiftSample] using h.symm

theorem measurable_shiftSample {d : ℕ} (z : Lattice d) :
    Measurable (shiftSample z : Sample d → Sample d) := by
  rw [shiftSample_eq_piCongrLeft]
  exact (MeasurableEquiv.piCongrLeft (fun _ : Lattice d => Bool)
    (translateLatticeEquiv z).symm).measurable

theorem sampleMeasure_map_shiftSample {d : ℕ} (z : Lattice d)
    (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map (shiftSample z) (sampleMeasure d p hp) = sampleMeasure d p hp := by
  rw [shiftSample_eq_piCongrLeft]
  have h :=
    Measure.infinitePi_map_piCongrLeft
      (X := fun _ : Lattice d => Bool)
      (μ := fun _ : Lattice d => coinMeasure p hp)
      (e := (translateLatticeEquiv z).symm)
  simpa [sampleMeasure] using h

theorem openUnitCell_translateLattice_iff {d : ℕ} (z w : Lattice d) (x : Vec d) :
    (fun i : Fin d => x i + (z i : ℝ)) ∈ openUnitCell (translateLattice z w) ↔
      x ∈ openUnitCell w := by
  constructor
  · intro hx i
    have hi := hx i
    simpa [translateLattice] using hi
  · intro hx i
    have hi := hx i
    simpa [translateLattice] using hi

theorem scalarAt_translate_intVec {d : ℕ} {lam Lam : ℝ}
    (z : Lattice d) (ω : Sample d) (x : Vec d) :
    scalarAt lam Lam ω (fun i : Fin d => x i + (z i : ℝ)) =
      scalarAt lam Lam (shiftSample z ω) x := by
  classical
  by_cases hx : ∃ w : Lattice d, x ∈ openUnitCell w
  · let w : Lattice d := Classical.choose hx
    have hxw : x ∈ openUnitCell w := Classical.choose_spec hx
    have hxshift :
        (fun i : Fin d => x i + (z i : ℝ)) ∈ openUnitCell (translateLattice z w) :=
      (openUnitCell_translateLattice_iff z w x).2 hxw
    simp [scalarAt_of_mem_openUnitCell (lam := lam) (Lam := Lam) (ω := ω) hxshift,
      scalarAt_of_mem_openUnitCell (lam := lam) (Lam := Lam) (ω := shiftSample z ω) hxw,
      shiftSample]
  · have hxshift :
        ¬ ∃ w : Lattice d,
          (fun i : Fin d => x i + (z i : ℝ)) ∈ openUnitCell w := by
      rintro ⟨w, hw⟩
      let w0 : Lattice d := (translateLatticeEquiv z).symm w
      have hw_eq : translateLattice z w0 = w := by
        exact (translateLatticeEquiv z).apply_symm_apply w
      have hxw0 : x ∈ openUnitCell w0 := by
        exact (openUnitCell_translateLattice_iff z w0 x).1 (by simpa [hw_eq] using hw)
      exact hx ⟨w0, hxw0⟩
    simp [scalarAt_of_not_mem_any_openUnitCell (lam := lam) (Lam := Lam) (ω := ω) hxshift,
      scalarAt_of_not_mem_any_openUnitCell (lam := lam) (Lam := Lam) (ω := shiftSample z ω) hx]

theorem translateByInt_coeffField {d : ℕ} {lam Lam : ℝ}
    (z : Lattice d) (ω : Sample d) :
    translateByInt z (coeffField lam Lam ω) = coeffField lam Lam (shiftSample z ω) := by
  funext x i j
  by_cases hij : i = j
  · subst j
    simp [translateByInt, translateCoeffField, coeffField, scalarMatrix, intVecToRealVec,
      scalarAt_translate_intVec]
  · simp [translateByInt, translateCoeffField, coeffField, scalarMatrix, hij]

theorem stationary_law {d : ℕ} {lam Lam : ℝ} (p : ℝ≥0) (hp : p ≤ 1) :
    Book.Ch04.StationaryLaw (law d lam Lam p hp) := by
  intro z
  rw [law]
  calc
    Measure.map (translateByInt z) (Measure.map (coeffField lam Lam) (sampleMeasure d p hp))
        =
          Measure.map
            (fun ω : Sample d => translateByInt z (coeffField lam Lam ω))
            (sampleMeasure d p hp) := by
          simpa [Function.comp] using
            (Measure.map_map
              (measurable_translateByInt (d := d) z)
              (measurable_coeffField (d := d) (lam := lam) (Lam := Lam))
              (μ := sampleMeasure d p hp))
    _ =
          Measure.map
            (fun ω : Sample d => coeffField lam Lam (shiftSample z ω))
            (sampleMeasure d p hp) := by
          congr 1
          funext ω
          exact translateByInt_coeffField z ω
    _ =
          Measure.map (coeffField lam Lam)
            (Measure.map (shiftSample z) (sampleMeasure d p hp)) := by
          symm
          simpa [Function.comp] using
            (Measure.map_map
              (measurable_coeffField (d := d) (lam := lam) (Lam := Lam))
              (measurable_shiftSample z)
              (μ := sampleMeasure d p hp))
    _ = Measure.map (coeffField lam Lam) (sampleMeasure d p hp) := by
          rw [sampleMeasure_map_shiftSample z p hp]

theorem adjointCoeffField_coeffField {d : ℕ} {lam Lam : ℝ} (ω : Sample d) :
    adjointCoeffField (coeffField lam Lam ω) = coeffField lam Lam ω := by
  funext x i j
  by_cases hij : i = j
  · subst j
    simp [adjointCoeffField, coeffField, matTranspose, scalarMatrix]
  · have hji : j ≠ i := Ne.symm hij
    simp [adjointCoeffField, coeffField, matTranspose, scalarMatrix, hij, hji]

theorem adjointInvariant_law {d : ℕ} {lam Lam : ℝ} (p : ℝ≥0) (hp : p ≤ 1) :
    Book.Ch04.AdjointInvariantLaw (law d lam Lam p hp) := by
  rw [law]
  calc
    Measure.map adjointCoeffField (Measure.map (coeffField lam Lam) (sampleMeasure d p hp))
        =
          Measure.map
            (fun ω : Sample d => adjointCoeffField (coeffField lam Lam ω))
            (sampleMeasure d p hp) := by
          simpa [Function.comp] using
            (Measure.map_map
              (measurable_adjointCoeffField (d := d))
              (measurable_coeffField (d := d) (lam := lam) (Lam := Lam))
              (μ := sampleMeasure d p hp))
    _ = Measure.map (coeffField lam Lam) (sampleMeasure d p hp) := by
          congr 1
          funext ω
          exact adjointCoeffField_coeffField ω

theorem dist_lt_one_of_mem_same_openUnitCell {d : ℕ} {x y : Vec d} {z : Lattice d}
    (hx : x ∈ openUnitCell z) (hy : y ∈ openUnitCell z) :
    dist x y < 1 := by
  refine (dist_pi_lt_iff (by norm_num : (0 : ℝ) < 1)).2 fun i => ?_
  have hx_i := hx i
  have hy_i := hy i
  have hsplit : x i - y i = (x i - (z i : ℝ)) - (y i - (z i : ℝ)) := by ring
  calc
    dist (x i) (y i) = |x i - y i| := by rw [Real.dist_eq]
    _ = |(x i - (z i : ℝ)) - (y i - (z i : ℝ))| := by rw [hsplit]
    _ ≤ |x i - (z i : ℝ)| + |y i - (z i : ℝ)| := by
          simpa [abs_sub_comm (z i : ℝ) (y i)] using
            abs_sub_le (x i - (z i : ℝ)) 0 (y i - (z i : ℝ))
    _ < (1 / 2 : ℝ) + (1 / 2 : ℝ) := add_lt_add hx_i hy_i
    _ = 1 := by norm_num

theorem disjoint_cellsMeeting_of_areUnitSeparated {d : ℕ} {U V : Set (Vec d)}
    (hUV : AreUnitSeparated U V) :
    Disjoint (cellsMeeting U) (cellsMeeting V) := by
  rw [Set.disjoint_left]
  intro z hzU hzV
  rcases hzU with ⟨x, hxU, hxz⟩
  rcases hzV with ⟨y, hyV, hyz⟩
  have hsep : 1 ≤ dist x y := hUV hxU hyV
  have hlt : dist x y < 1 := dist_lt_one_of_mem_same_openUnitCell hxz hyz
  exact not_le_of_gt hlt hsep

theorem iIndep_sampleCoordinateSigma {d : ℕ} (p : ℝ≥0) (hp : p ≤ 1) :
    ProbabilityTheory.iIndep
      (fun z : Lattice d => sampleCoordinateSigma z) (sampleMeasure d p hp) := by
  have hfun :
      ProbabilityTheory.iIndepFun
        (fun z : Lattice d => fun ω : Sample d => (fun b : Bool => b) (ω z))
        (sampleMeasure d p hp) := by
    simpa [sampleMeasure] using
      (ProbabilityTheory.iIndepFun_infinitePi
        (P := fun _ : Lattice d => coinMeasure p hp)
        (X := fun _ : Lattice d => fun b : Bool => b)
        (mX := fun _ => measurable_id))
  have hraw :=
    (ProbabilityTheory.iIndepFun_iff_iIndep
      (m := fun _ : Lattice d => inferInstance)
      (f := fun z : Lattice d => fun ω : Sample d => (fun b : Bool => b) (ω z))
      (μ := sampleMeasure d p hp)).1 hfun
  simpa [sampleCoordinateSigma] using hraw

theorem indep_sampleCellsSigma_of_disjoint {d : ℕ} {S T : Set (Lattice d)}
    (hST : Disjoint S T) (p : ℝ≥0) (hp : p ≤ 1) :
    ProbabilityTheory.Indep (sampleCellsSigma S) (sampleCellsSigma T) (sampleMeasure d p hp) := by
  have hle :
      ∀ z : Lattice d,
        sampleCoordinateSigma z ≤ (inferInstance : MeasurableSpace (Sample d)) := by
    intro z
    exact (measurable_pi_apply z).comap_le
  have hInd := iIndep_sampleCoordinateSigma (d := d) p hp
  simpa [sampleCellsSigma] using
    (ProbabilityTheory.indep_iSup_of_disjoint
      (m := fun z : Lattice d => sampleCoordinateSigma z)
      (μ := sampleMeasure d p hp) hle hInd (S := S) (T := T) hST)

theorem unitRangeDependent_law {d : ℕ} {lam Lam : ℝ} (p : ℝ≥0) (hp : p ≤ 1) :
    Book.Ch04.UnitRangeDependentLaw (law d lam Lam p hp) := by
  intro U V hUV
  rw [law]
  have hcells : Disjoint (cellsMeeting U) (cellsMeeting V) :=
    disjoint_cellsMeeting_of_areUnitSeparated hUV
  have hIndCells :
      ProbabilityTheory.Indep
        (sampleCellsSigma (cellsMeeting U))
        (sampleCellsSigma (cellsMeeting V))
        (sampleMeasure d p hp) :=
    indep_sampleCellsSigma_of_disjoint hcells p hp
  rw [ProbabilityTheory.Indep_iff]
  intro s t hs ht
  have hcoeff_meas := measurable_coeffField (d := d) (lam := lam) (Lam := Lam)
  have hs_ambient : MeasurableSet s := restrictionSigma_le_coeffField U s hs
  have ht_ambient : MeasurableSet t := restrictionSigma_le_coeffField V t ht
  have hst_ambient : MeasurableSet (s ∩ t) := hs_ambient.inter ht_ambient
  have hs_pre :
      @MeasurableSet (Sample d) (sampleCellsSigma (cellsMeeting U))
        ((coeffField lam Lam : Sample d → CoeffField d) ⁻¹' s) :=
    (measurable_coeffField_restrictionSigma_sampleCellsSigma
      (d := d) (lam := lam) (Lam := Lam) U) hs
  have ht_pre :
      @MeasurableSet (Sample d) (sampleCellsSigma (cellsMeeting V))
        ((coeffField lam Lam : Sample d → CoeffField d) ⁻¹' t) :=
    (measurable_coeffField_restrictionSigma_sampleCellsSigma
      (d := d) (lam := lam) (Lam := Lam) V) ht
  have hpre_ind :=
    (ProbabilityTheory.Indep_iff
      (sampleCellsSigma (cellsMeeting U))
      (sampleCellsSigma (cellsMeeting V))
      (sampleMeasure d p hp)).1 hIndCells
      ((coeffField lam Lam : Sample d → CoeffField d) ⁻¹' s)
      ((coeffField lam Lam : Sample d → CoeffField d) ⁻¹' t)
      hs_pre ht_pre
  rw [Measure.map_apply hcoeff_meas hst_ambient,
    Measure.map_apply hcoeff_meas hs_ambient,
    Measure.map_apply hcoeff_meas ht_ambient]
  simpa [Set.preimage_inter] using hpre_ind

def signInt (r : ℝ) : ℤ :=
  if r = 1 then 1 else -1

theorem signInt_cast_eq {r : ℝ} (hr : r = 1 ∨ r = -1) :
    (signInt r : ℝ) = r := by
  rcases hr with h | h
  · subst r
    norm_num [signInt]
  · subst r
    norm_num [signInt]

theorem signInt_mul_self {r : ℝ} (hr : r = 1 ∨ r = -1) :
    signInt r * signInt r = 1 := by
  rcases hr with h | h
  · subst r
    norm_num [signInt]
  · subst r
    norm_num [signInt]

def signedLatticeEquiv {d : ℕ} (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) : Lattice d ≃ Lattice d where
  toFun := fun w i => signInt (s (σ.symm i)) * w (σ.symm i)
  invFun := fun w i => signInt (s i) * w (σ i)
  left_inv := by
    intro w
    funext i
    have hsq := signInt_mul_self (hs i)
    dsimp
    rw [Equiv.symm_apply_apply]
    calc
      signInt (s i) * (signInt (s i) * w i)
          = (signInt (s i) * signInt (s i)) * w i := by ring
      _ = w i := by simp [hsq]
  right_inv := by
    intro w
    funext i
    have hsq := signInt_mul_self (hs (σ.symm i))
    dsimp
    rw [Equiv.apply_symm_apply]
    calc
      signInt (s (σ.symm i)) * (signInt (s (σ.symm i)) * w i)
          = (signInt (s (σ.symm i)) * signInt (s (σ.symm i))) * w i := by ring
      _ = w i := by simp [hsq]

theorem signedLatticeEquiv_apply_sigma {d : ℕ} (σ : Equiv.Perm (Fin d))
    (s : Fin d → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (w : Lattice d) (i : Fin d) :
    signedLatticeEquiv σ s hs w (σ i) = signInt (s i) * w i := by
  simp [signedLatticeEquiv]

def reindexSample {d : ℕ} (e : Lattice d ≃ Lattice d) (ω : Sample d) : Sample d :=
  fun w => ω (e w)

theorem reindexSample_eq_piCongrLeft {d : ℕ} (e : Lattice d ≃ Lattice d) :
    reindexSample e =
      (MeasurableEquiv.piCongrLeft (fun _ : Lattice d => Bool) e.symm) := by
  funext ω w
  have h :=
    MeasurableEquiv.piCongrLeft_apply_apply
      (e := e.symm) (β := fun _ : Lattice d => Bool) ω (e w)
  simpa [reindexSample] using h.symm

theorem measurable_reindexSample {d : ℕ} (e : Lattice d ≃ Lattice d) :
    Measurable (reindexSample e : Sample d → Sample d) := by
  rw [reindexSample_eq_piCongrLeft]
  exact (MeasurableEquiv.piCongrLeft (fun _ : Lattice d => Bool) e.symm).measurable

theorem sampleMeasure_map_reindexSample {d : ℕ} (e : Lattice d ≃ Lattice d)
    (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map (reindexSample e) (sampleMeasure d p hp) = sampleMeasure d p hp := by
  rw [reindexSample_eq_piCongrLeft]
  have h :=
    Measure.infinitePi_map_piCongrLeft
      (X := fun _ : Lattice d => Bool)
      (μ := fun _ : Lattice d => coinMeasure p hp)
      (e := e.symm)
  simpa [sampleMeasure] using h

theorem matVecMul_signedPermutation_apply {d : ℕ} {R : Mat d}
    {σ : Equiv.Perm (Fin d)} {s : Fin d → ℝ}
    (_hs : ∀ i, s i = 1 ∨ s i = -1)
    (hR : ∀ i j, R i j = if i = σ j then s j else 0)
    (x : Vec d) (i : Fin d) :
    matVecMul R x i = s (σ.symm i) * x (σ.symm i) := by
  unfold matVecMul
  rw [Finset.sum_eq_single (σ.symm i)]
  · rw [hR i (σ.symm i)]
    simp
  · intro j _ hj
    rw [hR i j]
    have hij : i ≠ σ j := by
      intro hij
      apply hj
      exact σ.injective (by simpa using hij.symm)
    simp [hij]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

theorem openUnitCell_signedPermutation_iff {d : ℕ} {R : Mat d}
    {σ : Equiv.Perm (Fin d)} {s : Fin d → ℝ}
    (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hR : ∀ i j, R i j = if i = σ j then s j else 0)
    (w : Lattice d) (x : Vec d) :
    matVecMul R x ∈ openUnitCell (signedLatticeEquiv σ s hs w) ↔
      x ∈ openUnitCell w := by
  constructor
  · intro hx i
    have hcoord := hx (σ i)
    have hmul := signInt_cast_eq (hs i)
    have hrewrite :
        matVecMul R x (σ i) - (signedLatticeEquiv σ s hs w (σ i) : ℝ) =
          s i * (x i - (w i : ℝ)) := by
      rw [matVecMul_signedPermutation_apply hs hR]
      simp [signedLatticeEquiv_apply_sigma, hmul]
      ring
    rw [hrewrite] at hcoord
    rcases hs i with hsi | hsi
    · simpa [hsi] using hcoord
    · simpa [hsi, abs_sub_comm] using hcoord
  · intro hx i
    let j : Fin d := σ.symm i
    have hxj := hx j
    have hmul := signInt_cast_eq (hs j)
    have hrewrite :
        matVecMul R x i - (signedLatticeEquiv σ s hs w i : ℝ) =
          s j * (x j - (w j : ℝ)) := by
      rw [matVecMul_signedPermutation_apply hs hR]
      simp [j, signedLatticeEquiv, hmul]
      ring
    rw [hrewrite]
    rcases hs j with hsj | hsj
    · simpa [hsj] using hxj
    · simpa [hsj, abs_sub_comm] using hxj

theorem scalarAt_signedPermutation {d : ℕ} {lam Lam : ℝ} {R : Mat d}
    {σ : Equiv.Perm (Fin d)} {s : Fin d → ℝ}
    (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hR : ∀ i j, R i j = if i = σ j then s j else 0)
    (ω : Sample d) (x : Vec d) :
    scalarAt lam Lam ω (matVecMul R x) =
      scalarAt lam Lam (reindexSample (signedLatticeEquiv σ s hs) ω) x := by
  classical
  by_cases hx : ∃ w : Lattice d, x ∈ openUnitCell w
  · let w : Lattice d := Classical.choose hx
    have hxw : x ∈ openUnitCell w := Classical.choose_spec hx
    have hRx :
        matVecMul R x ∈ openUnitCell (signedLatticeEquiv σ s hs w) :=
      (openUnitCell_signedPermutation_iff hs hR w x).2 hxw
    simp [scalarAt_of_mem_openUnitCell (lam := lam) (Lam := Lam) (ω := ω) hRx,
      scalarAt_of_mem_openUnitCell (lam := lam) (Lam := Lam)
        (ω := reindexSample (signedLatticeEquiv σ s hs) ω) hxw,
      reindexSample]
  · have hRx :
        ¬ ∃ w : Lattice d, matVecMul R x ∈ openUnitCell w := by
      rintro ⟨w, hw⟩
      let w0 : Lattice d := (signedLatticeEquiv σ s hs).symm w
      have hw_eq : signedLatticeEquiv σ s hs w0 = w :=
        (signedLatticeEquiv σ s hs).apply_symm_apply w
      have hxw0 : x ∈ openUnitCell w0 :=
        (openUnitCell_signedPermutation_iff hs hR w0 x).1 (by simpa [hw_eq] using hw)
      exact hx ⟨w0, hxw0⟩
    simp [scalarAt_of_not_mem_any_openUnitCell (lam := lam) (Lam := Lam) (ω := ω) hRx,
      scalarAt_of_not_mem_any_openUnitCell (lam := lam) (Lam := Lam)
        (ω := reindexSample (signedLatticeEquiv σ s hs) ω) hx]

theorem rotateCoeffField_coeffField {d : ℕ} {lam Lam : ℝ} {R : Mat d}
    {σ : Equiv.Perm (Fin d)} {s : Fin d → ℝ}
    (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hRdef : ∀ i j, R i j = if i = σ j then s j else 0)
    (ω : Sample d) :
    rotateCoeffField R (coeffField lam Lam ω) =
      coeffField lam Lam (reindexSample (signedLatticeEquiv σ s hs) ω) := by
  have hR : IsSignedPermutationMatrix R := ⟨σ, s, hs, hRdef⟩
  funext x i j
  have hscalar :
      scalarAt lam Lam ω (matVecMul R x) =
        scalarAt lam Lam (reindexSample (signedLatticeEquiv σ s hs) ω) x :=
    scalarAt_signedPermutation hs hRdef ω x
  simp [rotateCoeffField, coeffField, scalarMatrix, hscalar, hR.transpose_mul_self]

theorem isotropic_law {d : ℕ} {lam Lam : ℝ} (p : ℝ≥0) (hp : p ≤ 1) :
    Book.Ch04.IsotropicLaw (law d lam Lam p hp) := by
  intro R hR
  rcases hR with ⟨σ, s, hs, hRdef⟩
  rw [law]
  let e : Lattice d ≃ Lattice d := signedLatticeEquiv σ s hs
  calc
    Measure.map (rotateCoeffField R) (Measure.map (coeffField lam Lam) (sampleMeasure d p hp))
        =
          Measure.map
            (fun ω : Sample d => rotateCoeffField R (coeffField lam Lam ω))
            (sampleMeasure d p hp) := by
          simpa [Function.comp] using
            (Measure.map_map
              (measurable_rotateCoeffField (d := d) R ⟨σ, s, hs, hRdef⟩)
              (measurable_coeffField (d := d) (lam := lam) (Lam := Lam))
              (μ := sampleMeasure d p hp))
    _ =
          Measure.map
            (fun ω : Sample d => coeffField lam Lam (reindexSample e ω))
            (sampleMeasure d p hp) := by
          congr 1
          funext ω
          exact rotateCoeffField_coeffField (lam := lam) (Lam := Lam)
            (R := R) hs hRdef ω
    _ =
          Measure.map (coeffField lam Lam)
            (Measure.map (reindexSample e) (sampleMeasure d p hp)) := by
          symm
          simpa [Function.comp, e] using
            (Measure.map_map
              (measurable_coeffField (d := d) (lam := lam) (Lam := Lam))
              (measurable_reindexSample e)
              (μ := sampleMeasure d p hp))
    _ = Measure.map (coeffField lam Lam) (sampleMeasure d p hp) := by
          rw [sampleMeasure_map_reindexSample e p hp]

/-- The unscaled Bernoulli checkerboard law satisfies all structural
assumptions used by the public main results. -/
theorem structuralLaw {d : ℕ} {lam Lam : ℝ} (p : ℝ≥0) (hp : p ≤ 1) :
    Book.Ch04.StructuralLaw (law d lam Lam p hp) where
  stationary := stationary_law p hp
  unit_range := unitRangeDependent_law p hp
  isotropic := isotropic_law p hp
  adjoint_invariant := adjointInvariant_law p hp

/-- The scaled checkerboard law used by the public corollary. -/
def scaledLaw (d : ℕ) (lam Lam : ℝ) (p : ℝ≥0) (hp : p ≤ 1) (k : ℕ) :
    Book.Ch04.CoeffLaw d :=
  Book.Ch04.scaleNormalizedLaw k (law d lam Lam p hp)

/-- The reader-facing checkerboard scale.  A single triadic downscaling already
makes the application visibly a scaled law while preserving all constants as
dimension-only constants in the main theorem. -/
def publicScale : ℕ := 1

/-- The scaled checkerboard law has the Chapter 4 law carrier. -/
theorem scaledLawCarrier {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) (p : ℝ≥0) (hp : p ≤ 1) (k : ℕ) :
    Book.Ch04.LawCarrier (scaledLaw d lam Lam p hp k) := by
  simpa [scaledLaw] using
    (lawCarrier (d := d) (lam := lam) (Lam := Lam) hlam hle p hp).scaleNormalized k

/-- The scaled checkerboard law remains uniformly elliptic with the same
deterministic constants. -/
theorem scaledUniformEllipticityBounds {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) (p : ℝ≥0) (hp : p ≤ 1) (k : ℕ) :
    Book.MainResults.UniformEllipticityBounds (scaledLaw d lam Lam p hp k) lam Lam where
  lam_pos := hlam
  lam_le_Lam := hle
  aee_elliptic := by
    rw [scaledLaw, Book.Ch04.scaleNormalizedLaw_eq_rescaledLaw, rescaledLaw, law]
    have hmap :
        Measurable fun ω : Sample d => rescaleCoeffField k (coeffField lam Lam ω) :=
      (measurable_rescaleCoeffField (d := d) k).comp
        (measurable_coeffField (d := d) (lam := lam) (Lam := Lam))
    rw [Measure.map_map (measurable_rescaleCoeffField (d := d) k)
      (measurable_coeffField (d := d) (lam := lam) (Lam := Lam))]
    exact
      (ae_map_iff hmap.aemeasurable
        (measurableSet_uniformEllipticitySupport (d := d) (lam := lam) (Lam := Lam))).2
        (Filter.Eventually.of_forall fun ω Q =>
          rescaleCoeffField_coeffField_aeeEllipticOn (d := d)
            (lam := lam) (Lam := Lam) k ω
            (measurableSet_openCubeSet Q) hlam hle)

/-- The scaled checkerboard law satisfies the structural assumptions. -/
theorem scaledStructuralLaw {d : ℕ} {lam Lam : ℝ}
    (p : ℝ≥0) (hp : p ≤ 1) (k : ℕ) :
    Book.Ch04.StructuralLaw (scaledLaw d lam Lam p hp k) := by
  simpa [scaledLaw] using
    (structuralLaw (d := d) (lam := lam) (Lam := Lam) p hp).scaleNormalized k

/-- The main-result setup associated with the scaled Bernoulli checkerboard. -/
def checkerboardSetup {d : ℕ} [NeZero d]
    (two_le_dim : 2 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ Lam)
    (p : ℝ≥0) (hp : p ≤ 1) : Book.MainResults.Setup d where
  two_le_dim := two_le_dim
  P := scaledLaw d lam Lam p hp publicScale
  hP := scaledLawCarrier (d := d) (lam := lam) (Lam := Lam)
    hlam hle p hp publicScale
  hStruct := scaledStructuralLaw (d := d) (lam := lam) (Lam := Lam)
    p hp publicScale
  lam := lam
  Lam := Lam
  hUE := scaledUniformEllipticityBounds (d := d) (lam := lam) (Lam := Lam)
    hlam hle p hp publicScale

/-- **Quenched comparison for the Bernoulli checkerboard.**

For the triadically scaled Bernoulli checkerboard with coin parameter `p` and
conductances `lam`, `Lam`, all law assumptions in the public uniform-ellipticity
comparison theorem are discharged by the construction.  The constants are chosen
before `lam`, `Lam`, `p`, the realization, the cube, the forcing, and the
solutions. -/
theorem randomCheckerboard_quenchedComparison
    {d : ℕ} [NeZero d] :
    ∃ C α Cscale : ℝ,
      0 < C ∧ 0 < α ∧ 0 < Cscale ∧
      ∀ (two_le_dim : 2 ≤ d) (lam Lam : ℝ)
        (hlam : 0 < lam) (hle : lam ≤ Lam)
        (p : ℝ≥0) (hp : p ≤ 1),
        let S : Book.MainResults.Setup d :=
          checkerboardSetup two_le_dim lam Lam hlam hle p hp
        ∃ sigmaBar : ℝ,
          0 < sigmaBar ∧
          ∃ X : CoeffField d → ℝ,
            S.IsMinimalScale X Cscale ∧
            ∀ᵐ aω ∂S.P,
              ∀ (ha : Book.Ch04.AELocallyUniformlyEllipticField aω)
                {m : ℕ} {g : Vec d → Vec d}
                (pair : S.ComparisonPair aω ha m g),
                X aω ≤ (3 : ℝ) ^ m →
                Book.Ch03.ForceSobolevRegularity
                  (Book.MainResults.originCube d m) Book.MainResults.fixedComparisonS g →
                S.comparisonDefect Book.MainResults.fixedComparisonS pair ≤
                  C * ((3 : ℝ) ^ m / X aω) ^ (-α) *
                    S.comparisonData Book.MainResults.fixedComparisonS pair := by
  classical
  obtain ⟨C, α, Cscale, hC, hα, hCscale, hmain⟩ :=
    Book.MainResults.homogenizationComparison_uniformEllipticity (d := d)
  refine ⟨C, α, Cscale, hC, hα, hCscale, ?_⟩
  intro two_le_dim lam Lam hlam hle p hp
  exact hmain (checkerboardSetup two_le_dim lam Lam hlam hle p hp)

end

end RandomCheckerboard
end Examples
end Homogenization
