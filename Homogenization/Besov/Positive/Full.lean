import Homogenization.Besov.Positive.Overlap

namespace Homogenization

open scoped BigOperators ENNReal

/-!
## Full positive Besov wrappers

The following value sets record all finite-depth truncations. The full seminorm
wrappers use `sSup`; the overlap full norm wrappers are defined as full seminorm
plus the fixed parent mean term. Since the codomain is `ℝ`, boundedness is
recorded separately in regularity packages whenever a theorem needs these full
wrappers to behave as finite norms.
-/

noncomputable def cubeBesovDisjointSeminormValueSet {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) : Set ℝ :=
  Set.range fun N : ℕ => cubeBesovDisjointPartialSeminorm Q s p q N u

noncomputable def cubeBesovDisjointSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  sSup (cubeBesovDisjointSeminormValueSet Q s p q u)

noncomputable def cubeBesovDisjointSeminormTopValueSet {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) : Set ℝ :=
  Set.range fun N : ℕ => cubeBesovDisjointPartialSeminormTop Q s p N u

noncomputable def cubeBesovDisjointSeminormTop {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  sSup (cubeBesovDisjointSeminormTopValueSet Q s p u)

noncomputable def cubeBesovDisjointNormValueSet {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) : Set ℝ :=
  Set.range fun N : ℕ => cubeBesovDisjointPartialNorm Q s p q N u

noncomputable def cubeBesovDisjointNorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  sSup (cubeBesovDisjointNormValueSet Q s p q u)

noncomputable def cubeBesovDisjointNormTopValueSet {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) : Set ℝ :=
  Set.range fun N : ℕ => cubeBesovDisjointPartialNormTop Q s p N u

noncomputable def cubeBesovDisjointNormTop {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  sSup (cubeBesovDisjointNormTopValueSet Q s p u)

noncomputable def cubeBesovOverlapSeminormValueSet {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) : Set ℝ :=
  Set.range fun N : ℕ => cubeBesovOverlapPartialSeminorm Q s p q N u

noncomputable def cubeBesovOverlapSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  sSup (cubeBesovOverlapSeminormValueSet Q s p q u)

noncomputable def cubeBesovOverlapSeminormTopValueSet {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) : Set ℝ :=
  Set.range fun N : ℕ => cubeBesovOverlapPartialSeminormTop Q s p N u

noncomputable def cubeBesovOverlapSeminormTop {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  sSup (cubeBesovOverlapSeminormTopValueSet Q s p u)

noncomputable def cubeBesovOverlapNormValueSet {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) : Set ℝ :=
  Set.range fun N : ℕ => cubeBesovOverlapPartialNorm Q s p q N u

noncomputable def cubeBesovOverlapNorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  cubeBesovOverlapSeminorm Q s p q u +
    cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖

noncomputable def cubeBesovOverlapNormTopValueSet {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) : Set ℝ :=
  Set.range fun N : ℕ => cubeBesovOverlapPartialNormTop Q s p N u

noncomputable def cubeBesovOverlapNormTop {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  cubeBesovOverlapSeminormTop Q s p u +
    cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖

structure CubeBesovDisjointRegularity {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) : Prop where
  partialSeminorms_bddAbove :
    BddAbove (cubeBesovDisjointSeminormValueSet Q s p q u)

structure CubeBesovDisjointRegularityTop {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) : Prop where
  partialSeminorms_bddAbove :
    BddAbove (cubeBesovDisjointSeminormTopValueSet Q s p u)

structure CubeBesovOverlapRegularity {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) : Prop where
  partialSeminorms_bddAbove :
    BddAbove (cubeBesovOverlapSeminormValueSet Q s p q u)

structure CubeBesovOverlapRegularityTop {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) : Prop where
  partialSeminorms_bddAbove :
    BddAbove (cubeBesovOverlapSeminormTopValueSet Q s p u)

theorem CubeBesovDisjointRegularity.seminormValueSet_bddAbove {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p q : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovDisjointRegularity Q s p q u) :
    BddAbove (cubeBesovDisjointSeminormValueSet Q s p q u) :=
  hu.partialSeminorms_bddAbove

theorem CubeBesovDisjointRegularityTop.seminormValueSet_bddAbove {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovDisjointRegularityTop Q s p u) :
    BddAbove (cubeBesovDisjointSeminormTopValueSet Q s p u) :=
  hu.partialSeminorms_bddAbove

theorem CubeBesovOverlapRegularity.seminormValueSet_bddAbove {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p q : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovOverlapRegularity Q s p q u) :
    BddAbove (cubeBesovOverlapSeminormValueSet Q s p q u) :=
  hu.partialSeminorms_bddAbove

theorem CubeBesovOverlapRegularityTop.seminormValueSet_bddAbove {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovOverlapRegularityTop Q s p u) :
    BddAbove (cubeBesovOverlapSeminormTopValueSet Q s p u) :=
  hu.partialSeminorms_bddAbove

theorem cubeBesovDisjointSeminormValueSet_nonempty {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) :
    (cubeBesovDisjointSeminormValueSet Q s p q u).Nonempty :=
  ⟨cubeBesovDisjointPartialSeminorm Q s p q 0 u, ⟨0, rfl⟩⟩

theorem cubeBesovDisjointSeminormTopValueSet_nonempty {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) :
    (cubeBesovDisjointSeminormTopValueSet Q s p u).Nonempty :=
  ⟨cubeBesovDisjointPartialSeminormTop Q s p 0 u, ⟨0, rfl⟩⟩

theorem cubeBesovDisjointNormValueSet_nonempty {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) :
    (cubeBesovDisjointNormValueSet Q s p q u).Nonempty :=
  ⟨cubeBesovDisjointPartialNorm Q s p q 0 u, ⟨0, rfl⟩⟩

theorem cubeBesovDisjointNormTopValueSet_nonempty {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) :
    (cubeBesovDisjointNormTopValueSet Q s p u).Nonempty :=
  ⟨cubeBesovDisjointPartialNormTop Q s p 0 u, ⟨0, rfl⟩⟩

theorem cubeBesovOverlapSeminormValueSet_nonempty {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) :
    (cubeBesovOverlapSeminormValueSet Q s p q u).Nonempty :=
  ⟨cubeBesovOverlapPartialSeminorm Q s p q 0 u, ⟨0, rfl⟩⟩

theorem cubeBesovOverlapSeminormTopValueSet_nonempty {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) :
    (cubeBesovOverlapSeminormTopValueSet Q s p u).Nonempty :=
  ⟨cubeBesovOverlapPartialSeminormTop Q s p 0 u, ⟨0, rfl⟩⟩

theorem cubeBesovOverlapNormValueSet_nonempty {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) :
    (cubeBesovOverlapNormValueSet Q s p q u).Nonempty :=
  ⟨cubeBesovOverlapPartialNorm Q s p q 0 u, ⟨0, rfl⟩⟩

theorem cubeBesovOverlapNormTopValueSet_nonempty {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) :
    (cubeBesovOverlapNormTopValueSet Q s p u).Nonempty :=
  ⟨cubeBesovOverlapPartialNormTop Q s p 0 u, ⟨0, rfl⟩⟩

theorem cubeBesovDisjointNormValueSet_bddAbove_of_seminormValueSet_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞)
    (u : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovDisjointSeminormValueSet Q s p q u)) :
    BddAbove (cubeBesovDisjointNormValueSet Q s p q u) := by
  rcases hBdd with ⟨B, hB⟩
  let A : ℝ := cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖
  refine ⟨B + A, ?_⟩
  rintro x ⟨N, rfl⟩
  simpa [cubeBesovDisjointPartialNorm, cubeBesovPartialNorm,
    cubeBesovDisjointPartialSeminorm, A] using
    add_le_add_right (hB ⟨N, rfl⟩) A

theorem cubeBesovDisjointNormTopValueSet_bddAbove_of_seminormValueSet_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovDisjointSeminormTopValueSet Q s p u)) :
    BddAbove (cubeBesovDisjointNormTopValueSet Q s p u) := by
  rcases hBdd with ⟨B, hB⟩
  let A : ℝ := cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖
  refine ⟨B + A, ?_⟩
  rintro x ⟨N, rfl⟩
  simpa [cubeBesovDisjointPartialNormTop, cubeBesovPartialNormTop,
    cubeBesovDisjointPartialSeminormTop, A] using
    add_le_add_right (hB ⟨N, rfl⟩) A

theorem cubeBesovOverlapNormValueSet_bddAbove_of_seminormValueSet_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞)
    (u : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovOverlapSeminormValueSet Q s p q u)) :
    BddAbove (cubeBesovOverlapNormValueSet Q s p q u) := by
  rcases hBdd with ⟨B, hB⟩
  let A : ℝ := cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖
  refine ⟨B + A, ?_⟩
  rintro x ⟨N, rfl⟩
  simpa [cubeBesovOverlapPartialNorm, A] using
    add_le_add_right (hB ⟨N, rfl⟩) A

theorem cubeBesovOverlapNormTopValueSet_bddAbove_of_seminormValueSet_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovOverlapSeminormTopValueSet Q s p u)) :
    BddAbove (cubeBesovOverlapNormTopValueSet Q s p u) := by
  rcases hBdd with ⟨B, hB⟩
  let A : ℝ := cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖
  refine ⟨B + A, ?_⟩
  rintro x ⟨N, rfl⟩
  simpa [cubeBesovOverlapPartialNormTop, A] using
    add_le_add_right (hB ⟨N, rfl⟩) A

theorem CubeBesovDisjointRegularity.normValueSet_bddAbove {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p q : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovDisjointRegularity Q s p q u) :
    BddAbove (cubeBesovDisjointNormValueSet Q s p q u) :=
  cubeBesovDisjointNormValueSet_bddAbove_of_seminormValueSet_bddAbove
    Q s p q u hu.partialSeminorms_bddAbove

theorem CubeBesovDisjointRegularityTop.normValueSet_bddAbove {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovDisjointRegularityTop Q s p u) :
    BddAbove (cubeBesovDisjointNormTopValueSet Q s p u) :=
  cubeBesovDisjointNormTopValueSet_bddAbove_of_seminormValueSet_bddAbove
    Q s p u hu.partialSeminorms_bddAbove

theorem CubeBesovOverlapRegularity.normValueSet_bddAbove {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p q : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovOverlapRegularity Q s p q u) :
    BddAbove (cubeBesovOverlapNormValueSet Q s p q u) :=
  cubeBesovOverlapNormValueSet_bddAbove_of_seminormValueSet_bddAbove
    Q s p q u hu.partialSeminorms_bddAbove

theorem CubeBesovOverlapRegularityTop.normValueSet_bddAbove {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovOverlapRegularityTop Q s p u) :
    BddAbove (cubeBesovOverlapNormTopValueSet Q s p u) :=
  cubeBesovOverlapNormTopValueSet_bddAbove_of_seminormValueSet_bddAbove
    Q s p u hu.partialSeminorms_bddAbove

theorem cubeBesovDisjointPartialSeminorm_le_cubeBesovDisjointSeminorm_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞)
    (u : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovDisjointSeminormValueSet Q s p q u))
    (N : ℕ) :
    cubeBesovDisjointPartialSeminorm Q s p q N u ≤
      cubeBesovDisjointSeminorm Q s p q u := by
  unfold cubeBesovDisjointSeminorm
  exact le_csSup hBdd ⟨N, rfl⟩

theorem cubeBesovDisjointPartialSeminormTop_le_cubeBesovDisjointSeminormTop_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovDisjointSeminormTopValueSet Q s p u))
    (N : ℕ) :
    cubeBesovDisjointPartialSeminormTop Q s p N u ≤
      cubeBesovDisjointSeminormTop Q s p u := by
  unfold cubeBesovDisjointSeminormTop
  exact le_csSup hBdd ⟨N, rfl⟩

theorem cubeBesovDisjointPartialNorm_le_cubeBesovDisjointNorm_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞)
    (u : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovDisjointNormValueSet Q s p q u))
    (N : ℕ) :
    cubeBesovDisjointPartialNorm Q s p q N u ≤
      cubeBesovDisjointNorm Q s p q u := by
  unfold cubeBesovDisjointNorm
  exact le_csSup hBdd ⟨N, rfl⟩

theorem cubeBesovDisjointPartialNormTop_le_cubeBesovDisjointNormTop_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovDisjointNormTopValueSet Q s p u))
    (N : ℕ) :
    cubeBesovDisjointPartialNormTop Q s p N u ≤
      cubeBesovDisjointNormTop Q s p u := by
  unfold cubeBesovDisjointNormTop
  exact le_csSup hBdd ⟨N, rfl⟩

theorem cubeBesovOverlapPartialSeminorm_le_cubeBesovOverlapSeminorm_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞)
    (u : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovOverlapSeminormValueSet Q s p q u))
    (N : ℕ) :
    cubeBesovOverlapPartialSeminorm Q s p q N u ≤
      cubeBesovOverlapSeminorm Q s p q u := by
  unfold cubeBesovOverlapSeminorm
  exact le_csSup hBdd ⟨N, rfl⟩

theorem cubeBesovOverlapPartialSeminormTop_le_cubeBesovOverlapSeminormTop_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovOverlapSeminormTopValueSet Q s p u))
    (N : ℕ) :
    cubeBesovOverlapPartialSeminormTop Q s p N u ≤
      cubeBesovOverlapSeminormTop Q s p u := by
  unfold cubeBesovOverlapSeminormTop
  exact le_csSup hBdd ⟨N, rfl⟩

theorem cubeBesovOverlapPartialNorm_le_cubeBesovOverlapNorm_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞)
    (u : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovOverlapSeminormValueSet Q s p q u))
    (N : ℕ) :
    cubeBesovOverlapPartialNorm Q s p q N u ≤
      cubeBesovOverlapNorm Q s p q u := by
  unfold cubeBesovOverlapPartialNorm cubeBesovOverlapNorm
  exact add_le_add
    (cubeBesovOverlapPartialSeminorm_le_cubeBesovOverlapSeminorm_of_bddAbove
      Q s p q u hBdd N)
    le_rfl

theorem cubeBesovOverlapPartialNormTop_le_cubeBesovOverlapNormTop_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovOverlapSeminormTopValueSet Q s p u))
    (N : ℕ) :
    cubeBesovOverlapPartialNormTop Q s p N u ≤
      cubeBesovOverlapNormTop Q s p u := by
  unfold cubeBesovOverlapPartialNormTop cubeBesovOverlapNormTop
  exact add_le_add
    (cubeBesovOverlapPartialSeminormTop_le_cubeBesovOverlapSeminormTop_of_bddAbove
      Q s p u hBdd N)
    le_rfl

theorem cubeBesovDisjointSeminorm_nonneg_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovDisjointSeminormValueSet Q s p q u)) :
    0 ≤ cubeBesovDisjointSeminorm Q s p q u := by
  exact
    (cubeBesovPartialSeminorm_nonneg Q s p q 0 u).trans
      (cubeBesovDisjointPartialSeminorm_le_cubeBesovDisjointSeminorm_of_bddAbove
        Q s p q u hBdd 0)

theorem cubeBesovDisjointSeminormTop_nonneg_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovDisjointSeminormTopValueSet Q s p u)) :
    0 ≤ cubeBesovDisjointSeminormTop Q s p u := by
  exact
    (cubeBesovPartialSeminormTop_nonneg Q s p 0 u).trans
      (cubeBesovDisjointPartialSeminormTop_le_cubeBesovDisjointSeminormTop_of_bddAbove
        Q s p u hBdd 0)

theorem cubeBesovDisjointNorm_nonneg_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovDisjointNormValueSet Q s p q u)) :
    0 ≤ cubeBesovDisjointNorm Q s p q u := by
  exact
    (cubeBesovPartialNorm_nonneg Q s p q 0 u).trans
      (cubeBesovDisjointPartialNorm_le_cubeBesovDisjointNorm_of_bddAbove
        Q s p q u hBdd 0)

theorem cubeBesovDisjointNormTop_nonneg_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovDisjointNormTopValueSet Q s p u)) :
    0 ≤ cubeBesovDisjointNormTop Q s p u := by
  exact
    (cubeBesovPartialNormTop_nonneg Q s p 0 u).trans
      (cubeBesovDisjointPartialNormTop_le_cubeBesovDisjointNormTop_of_bddAbove
        Q s p u hBdd 0)

theorem cubeBesovOverlapSeminorm_nonneg_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovOverlapSeminormValueSet Q s p q u)) :
    0 ≤ cubeBesovOverlapSeminorm Q s p q u := by
  exact
    (cubeBesovOverlapPartialSeminorm_nonneg Q s p q 0 u).trans
      (cubeBesovOverlapPartialSeminorm_le_cubeBesovOverlapSeminorm_of_bddAbove
        Q s p q u hBdd 0)

theorem cubeBesovOverlapSeminormTop_nonneg_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovOverlapSeminormTopValueSet Q s p u)) :
    0 ≤ cubeBesovOverlapSeminormTop Q s p u := by
  exact
    (cubeBesovOverlapPartialSeminormTop_nonneg Q s p 0 u).trans
      (cubeBesovOverlapPartialSeminormTop_le_cubeBesovOverlapSeminormTop_of_bddAbove
        Q s p u hBdd 0)

theorem cubeBesovOverlapNorm_nonneg_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovOverlapSeminormValueSet Q s p q u)) :
    0 ≤ cubeBesovOverlapNorm Q s p q u := by
  unfold cubeBesovOverlapNorm
  exact add_nonneg
    (cubeBesovOverlapSeminorm_nonneg_of_bddAbove Q s p q u hBdd)
    (mul_nonneg (cubeBesovScaleWeight_nonneg s Q) (norm_nonneg _))

theorem cubeBesovOverlapNormTop_nonneg_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovOverlapSeminormTopValueSet Q s p u)) :
    0 ≤ cubeBesovOverlapNormTop Q s p u := by
  unfold cubeBesovOverlapNormTop
  exact add_nonneg
    (cubeBesovOverlapSeminormTop_nonneg_of_bddAbove Q s p u hBdd)
    (mul_nonneg (cubeBesovScaleWeight_nonneg s Q) (norm_nonneg _))

theorem CubeBesovDisjointRegularity.partialSeminorm_le_seminorm {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p q : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovDisjointRegularity Q s p q u) (N : ℕ) :
    cubeBesovDisjointPartialSeminorm Q s p q N u ≤
      cubeBesovDisjointSeminorm Q s p q u :=
  cubeBesovDisjointPartialSeminorm_le_cubeBesovDisjointSeminorm_of_bddAbove
    Q s p q u hu.partialSeminorms_bddAbove N

theorem CubeBesovDisjointRegularityTop.partialSeminorm_le_seminorm {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovDisjointRegularityTop Q s p u) (N : ℕ) :
    cubeBesovDisjointPartialSeminormTop Q s p N u ≤
      cubeBesovDisjointSeminormTop Q s p u :=
  cubeBesovDisjointPartialSeminormTop_le_cubeBesovDisjointSeminormTop_of_bddAbove
    Q s p u hu.partialSeminorms_bddAbove N

theorem CubeBesovOverlapRegularity.partialSeminorm_le_seminorm {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p q : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovOverlapRegularity Q s p q u) (N : ℕ) :
    cubeBesovOverlapPartialSeminorm Q s p q N u ≤
      cubeBesovOverlapSeminorm Q s p q u :=
  cubeBesovOverlapPartialSeminorm_le_cubeBesovOverlapSeminorm_of_bddAbove
    Q s p q u hu.partialSeminorms_bddAbove N

theorem CubeBesovOverlapRegularityTop.partialSeminorm_le_seminorm {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovOverlapRegularityTop Q s p u) (N : ℕ) :
    cubeBesovOverlapPartialSeminormTop Q s p N u ≤
      cubeBesovOverlapSeminormTop Q s p u :=
  cubeBesovOverlapPartialSeminormTop_le_cubeBesovOverlapSeminormTop_of_bddAbove
    Q s p u hu.partialSeminorms_bddAbove N

theorem CubeBesovDisjointRegularity.partialNorm_le_norm {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p q : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovDisjointRegularity Q s p q u) (N : ℕ) :
    cubeBesovDisjointPartialNorm Q s p q N u ≤
      cubeBesovDisjointNorm Q s p q u :=
  cubeBesovDisjointPartialNorm_le_cubeBesovDisjointNorm_of_bddAbove
    Q s p q u hu.normValueSet_bddAbove N

theorem CubeBesovDisjointRegularityTop.partialNorm_le_norm {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovDisjointRegularityTop Q s p u) (N : ℕ) :
    cubeBesovDisjointPartialNormTop Q s p N u ≤
      cubeBesovDisjointNormTop Q s p u :=
  cubeBesovDisjointPartialNormTop_le_cubeBesovDisjointNormTop_of_bddAbove
    Q s p u hu.normValueSet_bddAbove N

theorem CubeBesovOverlapRegularity.partialNorm_le_norm {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p q : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovOverlapRegularity Q s p q u) (N : ℕ) :
    cubeBesovOverlapPartialNorm Q s p q N u ≤
      cubeBesovOverlapNorm Q s p q u :=
  cubeBesovOverlapPartialNorm_le_cubeBesovOverlapNorm_of_bddAbove
    Q s p q u hu.partialSeminorms_bddAbove N

theorem CubeBesovOverlapRegularityTop.partialNorm_le_norm {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovOverlapRegularityTop Q s p u) (N : ℕ) :
    cubeBesovOverlapPartialNormTop Q s p N u ≤
      cubeBesovOverlapNormTop Q s p u :=
  cubeBesovOverlapPartialNormTop_le_cubeBesovOverlapNormTop_of_bddAbove
    Q s p u hu.partialSeminorms_bddAbove N

theorem CubeBesovDisjointRegularity.seminorm_nonneg {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p q : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovDisjointRegularity Q s p q u) :
    0 ≤ cubeBesovDisjointSeminorm Q s p q u :=
  cubeBesovDisjointSeminorm_nonneg_of_bddAbove
    Q s p q u hu.partialSeminorms_bddAbove

theorem CubeBesovDisjointRegularityTop.seminorm_nonneg {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovDisjointRegularityTop Q s p u) :
    0 ≤ cubeBesovDisjointSeminormTop Q s p u :=
  cubeBesovDisjointSeminormTop_nonneg_of_bddAbove
    Q s p u hu.partialSeminorms_bddAbove

theorem CubeBesovOverlapRegularity.seminorm_nonneg {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p q : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovOverlapRegularity Q s p q u) :
    0 ≤ cubeBesovOverlapSeminorm Q s p q u :=
  cubeBesovOverlapSeminorm_nonneg_of_bddAbove
    Q s p q u hu.partialSeminorms_bddAbove

theorem CubeBesovOverlapRegularityTop.seminorm_nonneg {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovOverlapRegularityTop Q s p u) :
    0 ≤ cubeBesovOverlapSeminormTop Q s p u :=
  cubeBesovOverlapSeminormTop_nonneg_of_bddAbove
    Q s p u hu.partialSeminorms_bddAbove

theorem CubeBesovDisjointRegularity.norm_nonneg {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p q : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovDisjointRegularity Q s p q u) :
    0 ≤ cubeBesovDisjointNorm Q s p q u :=
  cubeBesovDisjointNorm_nonneg_of_bddAbove
    Q s p q u hu.normValueSet_bddAbove

theorem CubeBesovDisjointRegularityTop.norm_nonneg {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovDisjointRegularityTop Q s p u) :
    0 ≤ cubeBesovDisjointNormTop Q s p u :=
  cubeBesovDisjointNormTop_nonneg_of_bddAbove
    Q s p u hu.normValueSet_bddAbove

theorem CubeBesovOverlapRegularity.norm_nonneg {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p q : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovOverlapRegularity Q s p q u) :
    0 ≤ cubeBesovOverlapNorm Q s p q u :=
  cubeBesovOverlapNorm_nonneg_of_bddAbove
    Q s p q u hu.partialSeminorms_bddAbove

theorem CubeBesovOverlapRegularityTop.norm_nonneg {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞} {u : Vec d → ℝ}
    (hu : CubeBesovOverlapRegularityTop Q s p u) :
    0 ≤ cubeBesovOverlapNormTop Q s p u :=
  cubeBesovOverlapNormTop_nonneg_of_bddAbove
    Q s p u hu.partialSeminorms_bddAbove

@[simp] theorem cubeBesovDisjointSeminorm_const {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : ℝ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hq0 : q ≠ 0) (hqTop : q ≠ ∞) :
    cubeBesovDisjointSeminorm Q s p q (fun _ => u) = 0 := by
  unfold cubeBesovDisjointSeminorm cubeBesovDisjointSeminormValueSet
  simp [cubeBesovDisjointPartialSeminorm, hp0, hpTop, hq0, hqTop]

@[simp] theorem cubeBesovDisjointSeminorm_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hq0 : q ≠ 0) (hqTop : q ≠ ∞) :
    cubeBesovDisjointSeminorm Q s p q (fun _ => (0 : ℝ)) = 0 := by
  simpa using cubeBesovDisjointSeminorm_const
    (Q := Q) (s := s) (p := p) (q := q) (u := (0 : ℝ))
    hp0 hpTop hq0 hqTop

@[simp] theorem cubeBesovDisjointSeminormTop_const {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : ℝ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovDisjointSeminormTop Q s p (fun _ => u) = 0 := by
  unfold cubeBesovDisjointSeminormTop cubeBesovDisjointSeminormTopValueSet
  simp [cubeBesovDisjointPartialSeminormTop, hp0, hpTop]

@[simp] theorem cubeBesovDisjointSeminormTop_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovDisjointSeminormTop Q s p (fun _ => (0 : ℝ)) = 0 := by
  simpa using cubeBesovDisjointSeminormTop_const
    (Q := Q) (s := s) (p := p) (u := (0 : ℝ)) hp0 hpTop

@[simp] theorem cubeBesovDisjointNorm_const {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : ℝ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hq0 : q ≠ 0) (hqTop : q ≠ ∞) :
    cubeBesovDisjointNorm Q s p q (fun _ => u) =
      cubeBesovScaleWeight s Q * ‖u‖ := by
  unfold cubeBesovDisjointNorm cubeBesovDisjointNormValueSet
  simp [cubeBesovDisjointPartialNorm, hp0, hpTop, hq0, hqTop]

@[simp] theorem cubeBesovDisjointNorm_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hq0 : q ≠ 0) (hqTop : q ≠ ∞) :
    cubeBesovDisjointNorm Q s p q (fun _ => (0 : ℝ)) = 0 := by
  simpa using cubeBesovDisjointNorm_const
    (Q := Q) (s := s) (p := p) (q := q) (u := (0 : ℝ))
    hp0 hpTop hq0 hqTop

@[simp] theorem cubeBesovDisjointNormTop_const {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : ℝ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovDisjointNormTop Q s p (fun _ => u) =
      cubeBesovScaleWeight s Q * ‖u‖ := by
  unfold cubeBesovDisjointNormTop cubeBesovDisjointNormTopValueSet
  simp [cubeBesovDisjointPartialNormTop, hp0, hpTop]

@[simp] theorem cubeBesovDisjointNormTop_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovDisjointNormTop Q s p (fun _ => (0 : ℝ)) = 0 := by
  simpa using cubeBesovDisjointNormTop_const
    (Q := Q) (s := s) (p := p) (u := (0 : ℝ)) hp0 hpTop

@[simp] theorem cubeBesovOverlapSeminorm_const {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : ℝ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hq0 : q ≠ 0) (hqTop : q ≠ ∞) :
    cubeBesovOverlapSeminorm Q s p q (fun _ => u) = 0 := by
  unfold cubeBesovOverlapSeminorm cubeBesovOverlapSeminormValueSet
  simp [hp0, hpTop, hq0, hqTop]

@[simp] theorem cubeBesovOverlapSeminorm_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hq0 : q ≠ 0) (hqTop : q ≠ ∞) :
    cubeBesovOverlapSeminorm Q s p q (fun _ => (0 : ℝ)) = 0 := by
  simpa using cubeBesovOverlapSeminorm_const
    (Q := Q) (s := s) (p := p) (q := q) (u := (0 : ℝ))
    hp0 hpTop hq0 hqTop

@[simp] theorem cubeBesovOverlapSeminormTop_const {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : ℝ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovOverlapSeminormTop Q s p (fun _ => u) = 0 := by
  unfold cubeBesovOverlapSeminormTop cubeBesovOverlapSeminormTopValueSet
  simp [hp0, hpTop]

@[simp] theorem cubeBesovOverlapSeminormTop_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovOverlapSeminormTop Q s p (fun _ => (0 : ℝ)) = 0 := by
  simpa using cubeBesovOverlapSeminormTop_const
    (Q := Q) (s := s) (p := p) (u := (0 : ℝ)) hp0 hpTop

@[simp] theorem cubeBesovOverlapNorm_const {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : ℝ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hq0 : q ≠ 0) (hqTop : q ≠ ∞) :
    cubeBesovOverlapNorm Q s p q (fun _ => u) =
      cubeBesovScaleWeight s Q * ‖u‖ := by
  unfold cubeBesovOverlapNorm
  rw [cubeBesovOverlapSeminorm_const
    (Q := Q) (s := s) (p := p) (q := q) (u := u) hp0 hpTop hq0 hqTop]
  rw [cubeAverage_const Q u]
  simp

@[simp] theorem cubeBesovOverlapNorm_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hq0 : q ≠ 0) (hqTop : q ≠ ∞) :
    cubeBesovOverlapNorm Q s p q (fun _ => (0 : ℝ)) = 0 := by
  simpa using cubeBesovOverlapNorm_const
    (Q := Q) (s := s) (p := p) (q := q) (u := (0 : ℝ))
    hp0 hpTop hq0 hqTop

@[simp] theorem cubeBesovOverlapNormTop_const {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : ℝ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovOverlapNormTop Q s p (fun _ => u) =
      cubeBesovScaleWeight s Q * ‖u‖ := by
  unfold cubeBesovOverlapNormTop
  rw [cubeBesovOverlapSeminormTop_const
    (Q := Q) (s := s) (p := p) (u := u) hp0 hpTop]
  rw [cubeAverage_const Q u]
  simp

@[simp] theorem cubeBesovOverlapNormTop_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovOverlapNormTop Q s p (fun _ => (0 : ℝ)) = 0 := by
  simpa using cubeBesovOverlapNormTop_const
    (Q := Q) (s := s) (p := p) (u := (0 : ℝ)) hp0 hpTop

end Homogenization
