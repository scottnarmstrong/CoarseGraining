import Homogenization.Book.Ch04.Measurability
import Homogenization.Book.Ch04.Internal.AEESliceAssembly.MuFamily

namespace Homogenization
namespace Book
namespace Ch04

open MeasureTheory

/-!
# `Mu` measurability

This file is the public Ch4 handoff for the coarse-grained energy `Mu`.
The honest endpoint is law-relative `AEMeasurable`: the law carrier gives the
AEE quantitative elliptic slice cover only almost surely.
-/

namespace LawCarrier

/-- Assemble law-relative `Mu` measurability from canonical AEE-slice
measurability and the `LawCarrier` slice cover.

This is the countable-slice bookkeeping theorem; the theorem
`aemeasurable_Mu_cubeSet` below supplies the canonical slice-local input. -/
theorem aemeasurable_Mu_cubeSet_of_measurable_aeeQuantitativeSlice
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (P0 : BlockVec d)
    (hMuSlice :
      ∀ k : ℕ,
        @Measurable
          {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a}
          ℝ
          (AEEQuantitativeEllipticSlice.localMeasurableSpace (cubeSet Q) k)
          (borel ℝ)
          (fun a => Mu (cubeSet Q) P0 a.1)) :
    AEMeasurable (fun a : CoeffField d => Mu (cubeSet Q) P0 a) P := by
  classical
  refine NullMeasurable.aemeasurable ?_
  intro s hs
  let X : CoeffField d → ℝ := fun a => Mu (cubeSet Q) P0 a
  let slice : ℕ → Set (CoeffField d) :=
    fun k => {a : CoeffField d | AEEQuantitativeEllipticSlice (cubeSet Q) k a}
  let covered : Set (CoeffField d) := ⋃ k : ℕ, slice k
  let pieces : Set (CoeffField d) :=
    ⋃ k : ℕ, slice k ∩ X ⁻¹' s
  have hpieces_null : NullMeasurableSet pieces P := by
    refine NullMeasurableSet.iUnion ?_
    intro k
    let sliceSubtype :=
      {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a}
    let subTarget : Set sliceSubtype := {a | Mu (cubeSet Q) P0 a.1 ∈ s}
    have hSubtype :
        @MeasurableSet sliceSubtype
          (AEEQuantitativeEllipticSlice.localMeasurableSpace (cubeSet Q) k)
          subTarget := by
      exact (hMuSlice k) hs
    have hSubtype_comap :
        @MeasurableSet sliceSubtype
          (MeasurableSpace.comap Subtype.val (localSigma (cubeSet Q)))
          subTarget := by
      simpa [AEEQuantitativeEllipticSlice.localMeasurableSpace, sliceSubtype]
        using hSubtype
    rcases
        (MeasurableSpace.measurableSet_comap (f := Subtype.val)
          (m := localSigma (cubeSet Q)) (s := subTarget)).mp
          hSubtype_comap with
      ⟨t, ht, hpre⟩
    have hlocal_piece :
        @MeasurableSet (CoeffField d) (localSigma (cubeSet Q))
          (slice k ∩ X ⁻¹' s) := by
      have hslice :
          @MeasurableSet (CoeffField d) (localSigma (cubeSet Q)) (slice k) :=
        hP.measurableSet_aeeQuantitativeEllipticSlice_cubeSet Q k
      have ht_piece :
          @MeasurableSet (CoeffField d) (localSigma (cubeSet Q)) (slice k ∩ t) :=
        hslice.inter ht
      have hseteq : slice k ∩ t = slice k ∩ X ⁻¹' s := by
        ext a
        constructor
        · rintro ⟨ha_slice, ha_t⟩
          refine ⟨ha_slice, ?_⟩
          have ha_sub :
              (⟨a, ha_slice⟩ :
                {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a})
                  ∈ subTarget := by
            have ha_pre :
                (⟨a, ha_slice⟩ :
                  {a : CoeffField d //
                    AEEQuantitativeEllipticSlice (cubeSet Q) k a})
                    ∈ Subtype.val ⁻¹' t := by
              simpa using ha_t
            simpa [hpre, sliceSubtype] using ha_pre
          simpa [subTarget, X, sliceSubtype] using ha_sub
        · rintro ⟨ha_slice, ha_s⟩
          refine ⟨ha_slice, ?_⟩
          have ha_sub :
              (⟨a, ha_slice⟩ :
                {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a})
                  ∈ subTarget := by
            simpa [subTarget, X, sliceSubtype] using ha_s
          simpa [Set.preimage] using
            (show (⟨a, ha_slice⟩ :
                {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a})
                ∈ Subtype.val ⁻¹' t from by
              simpa [hpre, sliceSubtype] using ha_sub)
      simpa [hseteq] using ht_piece
    exact hP.local_observable_measurable.nullMeasurable_localSigma
      (cubeSet Q) (slice k ∩ X ⁻¹' s) hlocal_piece
  have hcovered_ae :
      ∀ᵐ a ∂P, a ∈ covered := by
    filter_upwards [hP.ae_exists_aeeQuantitativeEllipticSlice_cubeSet Q] with a ha
    exact Set.mem_iUnion.mpr ha
  have hEq : X ⁻¹' s =ᵐ[P] pieces := by
    filter_upwards [hcovered_ae] with a ha_cover
    apply propext
    constructor
    · intro ha_s
      rcases Set.mem_iUnion.mp ha_cover with ⟨k, ha_slice⟩
      exact Set.mem_iUnion.mpr ⟨k, ⟨ha_slice, ha_s⟩⟩
    · intro ha_piece
      rcases Set.mem_iUnion.mp ha_piece with ⟨k, ha_piece_k⟩
      exact ha_piece_k.2
  exact hpieces_null.congr hEq.symm

/-- The canonical Chapter 4 law-facing measurability theorem for `Mu` on a
deterministic triadic cube.  Downstream chapters should use this theorem
directly; `coarseBlockMatrix`, `ResponseJ`, and `BlockJ` measurability should
be derived from this finite-polarization root. -/
theorem aemeasurable_Mu_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (P0 : BlockVec d) :
    AEMeasurable (fun a : CoeffField d => Mu (cubeSet Q) P0 a) P :=
  hP.aemeasurable_Mu_cubeSet_of_measurable_aeeQuantitativeSlice Q P0
    (fun k =>
      Homogenization.measurable_Mu_aeeQuantitativeSlice_canonical_cubeSet
        (Q := Q) (k := k) P0)

/-- Law-relative local-test measurable representative of `Mu` on a fixed
triadic cube.  The raw `Mu` need only be a.e. on the elliptic support of the
law; this theorem chooses the canonical countable AEE-slice representative,
which is genuinely `localSigma (cubeSet Q)`-measurable and agrees with the raw
observable almost surely. -/
theorem exists_isLocalRandomVariable_ae_eq_Mu_cubeSet
    {d : ℕ} {P : CoeffLaw d} (hP : LawCarrier P)
    (Q : TriadicCube d) (P0 : BlockVec d) :
    ∃ Y : CoeffField d → ℝ,
      IsLocalRandomVariable (cubeSet Q) Y ∧
        (fun a : CoeffField d => Mu (cubeSet Q) P0 a) =ᵐ[P] Y := by
  classical
  let slice : ℕ → Set (CoeffField d) :=
    fun k => {a : CoeffField d | AEEQuantitativeEllipticSlice (cubeSet Q) k a}
  let covered : Set (CoeffField d) := ⋃ k : ℕ, slice k
  let cover : Option ℕ → Set (CoeffField d)
    | none => coveredᶜ
    | some k => slice k
  let f : (i : Option ℕ) → cover i → ℝ
    | none, _ => 0
    | some _k, a => Mu (cubeSet Q) P0 a.1
  have hagree :
      ∀ (i j : Option ℕ) (a : CoeffField d)
        (hai : a ∈ cover i) (haj : a ∈ cover j),
          f i ⟨a, hai⟩ = f j ⟨a, haj⟩ := by
    intro i j a hai haj
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some k =>
            exfalso
            have ha_covered : a ∈ covered :=
              Set.mem_iUnion.mpr ⟨k, by simpa [cover] using haj⟩
            have ha_not_covered : a ∉ covered := by
              simpa [cover] using hai
            exact ha_not_covered ha_covered
    | some k =>
        cases j with
        | none =>
            exfalso
            have ha_covered : a ∈ covered :=
              Set.mem_iUnion.mpr ⟨k, by simpa [cover] using hai⟩
            have ha_not_covered : a ∉ covered := by
              simpa [cover] using haj
            exact ha_not_covered ha_covered
        | some _ => rfl
  have hcover : ⋃ i : Option ℕ, cover i = Set.univ := by
    ext a
    constructor
    · intro _ha
      exact Set.mem_univ a
    · intro _ha
      by_cases ha : a ∈ covered
      · rcases Set.mem_iUnion.mp ha with ⟨k, hk⟩
        exact Set.mem_iUnion.mpr ⟨some k, by simpa [cover] using hk⟩
      · exact Set.mem_iUnion.mpr ⟨none, by simpa [cover] using ha⟩
  let Y : CoeffField d → ℝ := Set.liftCover cover f hagree hcover
  refine ⟨Y, ?_, ?_⟩
  · change @Measurable (CoeffField d) ℝ (localSigma (cubeSet Q)) _ Y
    letI : MeasurableSpace (CoeffField d) := localSigma (cubeSet Q)
    have hcover_meas : ∀ i : Option ℕ, MeasurableSet (cover i) := by
      intro i
      cases i with
      | none =>
          exact (MeasurableSet.iUnion fun k =>
            hP.measurableSet_aeeQuantitativeEllipticSlice_cubeSet Q k).compl
      | some k =>
          exact hP.measurableSet_aeeQuantitativeEllipticSlice_cubeSet Q k
    have hfm : ∀ i : Option ℕ, Measurable (f i) := by
      intro i
      cases i with
      | none =>
          exact measurable_const
      | some k =>
          have hA :
              IsLocalSigmaMeasurableOn
                (fun a : cover (some k) => (a : CoeffField d)) (cubeSet Q) := by
            change @Measurable (cover (some k)) (CoeffField d) _
              (localSigma (cubeSet Q)) (fun a : cover (some k) => (a : CoeffField d))
            exact measurable_subtype_coe
          have hSlice :
              ∀ a : cover (some k),
                AEEQuantitativeEllipticSlice (cubeSet Q) k
                  ((fun a : cover (some k) => (a : CoeffField d)) a) := by
            intro a
            change (a : CoeffField d) ∈ slice k
            simp [cover] at a
            exact a.2
          simpa [f, cover] using
            Homogenization.measurable_Mu_comp_aeeQuantitativeSlice_canonical_cubeSet
              Q (fun a : cover (some k) => (a : CoeffField d)) hA hSlice P0
    simpa [Y] using measurable_liftCover cover hcover_meas f hfm hagree hcover
  · have hcovered_ae : ∀ᵐ a ∂P, a ∈ covered := by
      filter_upwards [hP.ae_exists_aeeQuantitativeEllipticSlice_cubeSet Q] with a ha
      exact Set.mem_iUnion.mpr ha
    filter_upwards [hcovered_ae] with a ha
    rcases Set.mem_iUnion.mp ha with ⟨k, hak⟩
    have ha_cover : a ∈ cover (some k) := by
      simpa [cover, slice] using hak
    dsimp [Y]
    rw [Set.liftCover_of_mem
      (S := cover) (f := f) (hf := hagree) (hS := hcover) (i := some k) ha_cover]

end LawCarrier

end Ch04
end Book
end Homogenization
