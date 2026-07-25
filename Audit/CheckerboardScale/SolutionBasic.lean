import Mathlib
import Audit.PolynomialScale.SolutionBasic

attribute [-instance] Homogenization.instMeasurableSpaceVec
attribute [-instance] Homogenization.instMeasurableSpaceMat
attribute [-instance] Homogenization.instMeasurableSpaceCoeffField

/-!
# Statement-level audit vocabulary for the checkerboard homogenization scale

This file holds the Mathlib-shaped statement vocabulary for the comparator
solution of the Bernoulli-checkerboard homogenization-scale corollary.  The
shared vocabulary — the local mirrors of the ambient fields, the
regular-fields carrier and its σ-algebra, cubes, Sobolev objects, the block
formalism with the coarse-graining variational quantity `Mu`, the annealed
coarse matrices, and the scalar contrast selector
`PolynomialScale.thetaAtScale` — is imported from
`Audit.PolynomialScale.SolutionBasic` (identical declarations at identical
names).  This file adds the Bernoulli checkerboard law mirror
(`RandomCheckerboard.law`): the cellwise scalar sample map packaged as a
carrier element, the Bernoulli product measure on coin samples, and its
pushforward law on the carrier.  `Solution.lean` imports this file and adds
the private bridges to the repository theorem together with the audited
theorem itself.

The audited theorem carries the explicit dimension restriction `hd : 3 ≤ d`
(`d > 2`); the capstone's ellipticity parameter is instantiated at `Θ = Lam`,
in whose quadratic-form ellipticity class `IsEllipticMatrix 1 Lam`
(coercivity together with the inverse quadratic-form bound; the fields are
general non-symmetric matrices) the checkerboard realizations lie.
-/

namespace Homogenization
namespace StatementAudit

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

/-! ## Bernoulli checkerboard specialization -/

namespace RandomCheckerboard

section

attribute [local instance] Classical.propDecidable

abbrev Lattice (d : ℕ) :=
  Fin d → ℤ

abbrev Sample (d : ℕ) :=
  Lattice d → Bool

def openUnitCell {d : ℕ} (z : Lattice d) : Set (Vec d) :=
  {x | ∀ i : Fin d, |x i - (z i : ℝ)| < (1 / 2 : ℝ)}

def coinConductance (lam Lam : ℝ) (b : Bool) : ℝ :=
  if b then lam else Lam

def scalarAt {d : ℕ} (lam Lam : ℝ) (ω : Sample d) (x : Vec d) : ℝ :=
  if h : ∃ z : Lattice d, x ∈ openUnitCell z then
    coinConductance lam Lam (ω (Classical.choose h))
  else
    lam

def coeffField {d : ℕ} (lam Lam : ℝ) (ω : Sample d) : CoeffField d :=
  fun x => scalarMatrix (d := d) (scalarAt lam Lam ω x)

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

theorem scalarAt_of_mem_openUnitCell {d : ℕ} {lam Lam : ℝ}
    {ω : Sample d} {x : Vec d} {z : Lattice d}
    (hz : x ∈ openUnitCell z) :
    scalarAt lam Lam ω x = coinConductance lam Lam (ω z) := by
  classical
  have h : ∃ w : Lattice d, x ∈ openUnitCell w := ⟨z, hz⟩
  rw [scalarAt, dif_pos h]
  congr 1
  exact congrArg ω (openUnitCell_unique (Classical.choose_spec h) hz)

theorem scalarAt_of_not_mem_any_openUnitCell {d : ℕ} {lam Lam : ℝ}
    {ω : Sample d} {x : Vec d}
    (hx : ¬ ∃ z : Lattice d, x ∈ openUnitCell z) :
    scalarAt lam Lam ω x = lam := by
  classical
  rw [scalarAt, dif_neg hx]

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

theorem scalarAt_eq_lam_or_Lam {d : ℕ} {lam Lam : ℝ} (ω : Sample d) (x : Vec d) :
    scalarAt lam Lam ω x = lam ∨ scalarAt lam Lam ω x = Lam := by
  rw [scalarAt_eq_if_upperConductanceRegion]
  by_cases hx : x ∈ upperConductanceRegion ω <;> simp [hx]

theorem abs_scalarAt_le {d : ℕ} {lam Lam : ℝ} (ω : Sample d) (x : Vec d) :
    |scalarAt lam Lam ω x| ≤ max |lam| |Lam| := by
  rcases scalarAt_eq_lam_or_Lam (lam := lam) (Lam := Lam) ω x with h | h
  · rw [h]; exact le_max_left _ _
  · rw [h]; exact le_max_right _ _

/-- A bounded measurable scalar field is locally integrable. -/
theorem locallyIntegrable_of_bounded_measurable {d : ℕ} {f : Vec d → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    MeasureTheory.LocallyIntegrable f MeasureTheory.volume := by
  rw [MeasureTheory.locallyIntegrable_iff]
  intro k hk
  refine MeasureTheory.Measure.integrableOn_of_bounded (hk.measure_lt_top).ne
    hf.aestronglyMeasurable (M := C) ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using hC x

/-- The checkerboard realization as a carrier element (mirrors
`checkerRegField`). -/
noncomputable def checkerRegField {d : ℕ} (lam Lam : ℝ) (ω : Sample d) :
    RegCoeffField d where
  toFun := coeffField lam Lam ω
  entry_measurable := fun i j => by
    by_cases hij : i = j
    · subst j
      simpa [coeffField, scalarMatrix] using
        measurable_scalarAt_spatial (lam := lam) (Lam := Lam) ω
    · simp [coeffField, scalarMatrix, hij]
  entry_locInt := fun i j => by
    by_cases hij : i = j
    · subst j
      have hmeas : Measurable (fun x : Vec d => coeffField lam Lam ω x i i) := by
        simpa [coeffField, scalarMatrix] using
          measurable_scalarAt_spatial (lam := lam) (Lam := Lam) ω
      refine locallyIntegrable_of_bounded_measurable hmeas
        (C := max |lam| |Lam|) fun x => ?_
      simpa [coeffField, scalarMatrix] using
        abs_scalarAt_le (lam := lam) (Lam := Lam) ω x
    · have hzero : (fun x : Vec d => coeffField lam Lam ω x i j)
          = fun _ : Vec d => (0 : ℝ) := by
        funext x
        simp [coeffField, scalarMatrix, hij]
      rw [hzero]
      exact MeasureTheory.locallyIntegrable_const (0 : ℝ)

def coinMeasure (p : ℝ≥0) (hp : p ≤ 1) : Measure Bool :=
  (PMF.bernoulli p hp).toMeasure

def sampleMeasure (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : Measure (Sample d) :=
  Measure.infinitePi (fun _ : Lattice d => coinMeasure p hp)

noncomputable def law (d : ℕ) (lam Lam : ℝ) (p : ℝ≥0) (hp : p ≤ 1) : CoeffLaw d :=
  Measure.map (checkerRegField lam Lam) (sampleMeasure d p hp)

end

end RandomCheckerboard

end

end StatementAudit
end Homogenization
