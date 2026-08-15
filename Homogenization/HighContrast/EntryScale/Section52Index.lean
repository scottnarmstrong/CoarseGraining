import Homogenization.Book.Ch05.Theorems.Section52.Weights

/-!
# Section 5.2 index conversions

Small local wrappers around the library's Section 5.2 large-scale
index facts, plus the scale-to-depth descendant conversion used by terminal
lower-edge bridges.
-/

namespace Homogenization.HighContrast.EntryScale

noncomputable section

/-- A Section 5.2 large-scale index is nonnegative. -/
theorem section52LargeScaleSet_mem_nonneg {m : ℕ} {n : ℤ}
    (hn : n ∈ Homogenization.Book.Ch05.Section52.section52LargeScaleSet m) :
    0 ≤ n :=
  Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_nonneg hn

/-- A Section 5.2 large-scale index is bounded by the terminal scale. -/
theorem section52LargeScaleSet_mem_le_m {m : ℕ} {n : ℤ}
    (hn : n ∈ Homogenization.Book.Ch05.Section52.section52LargeScaleSet m) :
    n ≤ (m : ℤ) :=
  Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m hn

/-- The natural index attached to a Section 5.2 large-scale index is bounded by `m`. -/
theorem section52LargeScaleSet_mem_toNat_le {m : ℕ} {n : ℤ}
    (hn : n ∈ Homogenization.Book.Ch05.Section52.section52LargeScaleSet m) :
    Int.toNat n ≤ m :=
  Int.toNat_le.mpr (section52LargeScaleSet_mem_le_m hn)

/--
Section 5.2 large-scale absolute indices lie in the natural source-window
once the lower endpoint is supplied.
-/
theorem section52LargeScaleSet_toNat_mem_Icc
    {m N : ℕ} {n : ℤ}
    (hn : n ∈ Homogenization.Book.Ch05.Section52.section52LargeScaleSet m)
    (hN : N ≤ Int.toNat n) :
    Int.toNat n ∈ Finset.Icc N m :=
  Finset.mem_Icc.mpr ⟨hN, section52LargeScaleSet_mem_toNat_le hn⟩

/--
For an integer scale `n` between `0` and `m`, descendants of the origin cube at
scale `n` are descendants at depth `m - Int.toNat n`.
-/
theorem descendantsAtScale_originCube_eq_descendantsAtDepth_sub_toNat
    {d m : ℕ} {n : ℤ} (hn_nonneg : 0 ≤ n) (hn_le_m : n ≤ (m : ℤ)) :
    Homogenization.descendantsAtScale (Homogenization.originCube d (m : ℤ)) n =
      Homogenization.descendantsAtDepth (Homogenization.originCube d (m : ℤ))
        (m - Int.toNat n) := by
  rw [Homogenization.descendantsAtScale_eq_descendantsAtDepth
    (Homogenization.originCube d (m : ℤ))
    (by simpa [Homogenization.originCube] using hn_le_m)]
  congr 1
  simp [Homogenization.originCube]
  omega

/--
Section 5.2 large-scale indices convert descendants at absolute scale `n` into
descendants at depth `m - Int.toNat n` below the origin cube.
-/
theorem descendantsAtScale_originCube_eq_descendantsAtDepth_of_mem_section52LargeScaleSet
    {d m : ℕ} {n : ℤ}
    (hn : n ∈ Homogenization.Book.Ch05.Section52.section52LargeScaleSet m) :
    Homogenization.descendantsAtScale (Homogenization.originCube d (m : ℤ)) n =
      Homogenization.descendantsAtDepth (Homogenization.originCube d (m : ℤ))
        (m - Int.toNat n) :=
  descendantsAtScale_originCube_eq_descendantsAtDepth_sub_toNat
    (section52LargeScaleSet_mem_nonneg hn) (section52LargeScaleSet_mem_le_m hn)
end
end Homogenization.HighContrast.EntryScale