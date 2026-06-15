import Homogenization.Geometry.Domain

namespace Homogenization

structure TriadicCube (d : ℕ) where
  scale : ℤ
  index : Fin d → ℤ
deriving DecidableEq, Repr

noncomputable def cubeScaleFactor {d : ℕ} (Q : TriadicCube d) : ℝ :=
  (3 : ℝ) ^ Q.scale

/-- Half-open realization of a triadic cube, used for exact cube partitions. -/
def cubeSet {d : ℕ} (Q : TriadicCube d) : Set (Vec d) :=
  { x | ∀ i,
      (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q ≤ x i) ∧
      (x i < (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)) }

/-- Open realization of a triadic cube, used when analytic lemmas require open domains. -/
def openCubeSet {d : ℕ} (Q : TriadicCube d) : Set (Vec d) :=
  { x | ∀ i,
      (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q < x i) ∧
      (x i < (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)) }

/-- The standard centered triadic cube `\square_m = [-3^m / 2, 3^m / 2)^d`. -/
def originCube (d : ℕ) (m : ℤ) : TriadicCube d :=
  { scale := m
    index := 0 }

def translateCube {d : ℕ} (shift : Fin d → ℤ) (Q : TriadicCube d) : TriadicCube d :=
  { scale := Q.scale
    index := fun i => Q.index i + shift i }

@[simp] theorem cubeScaleFactor_originCube {d : ℕ} (m : ℤ) :
    cubeScaleFactor (originCube d m) = (3 : ℝ) ^ m :=
  rfl

@[simp] theorem cubeScaleFactor_translateCube {d : ℕ} (shift : Fin d → ℤ) (Q : TriadicCube d) :
    cubeScaleFactor (translateCube shift Q) = cubeScaleFactor Q :=
  rfl

@[simp] theorem mem_cubeSet_originCube_iff {d : ℕ} {m : ℤ} {x : Vec d} :
    x ∈ cubeSet (originCube d m) ↔
      ∀ i, ((-(1 / 2 : ℝ)) * (3 : ℝ) ^ m ≤ x i) ∧ (x i < (1 / 2 : ℝ) * (3 : ℝ) ^ m) := by
  constructor
  · intro hx i
    simpa [cubeSet, originCube, cubeScaleFactor, sub_eq_add_neg] using hx i
  · intro hx i
    simpa [cubeSet, originCube, cubeScaleFactor, sub_eq_add_neg] using hx i

@[simp] theorem mem_openCubeSet_originCube_iff {d : ℕ} {m : ℤ} {x : Vec d} :
    x ∈ openCubeSet (originCube d m) ↔
      ∀ i, ((-(1 / 2 : ℝ)) * (3 : ℝ) ^ m < x i) ∧ (x i < (1 / 2 : ℝ) * (3 : ℝ) ^ m) := by
  constructor
  · intro hx i
    simpa [openCubeSet, originCube, cubeScaleFactor, sub_eq_add_neg] using hx i
  · intro hx i
    simpa [openCubeSet, originCube, cubeScaleFactor, sub_eq_add_neg] using hx i

@[simp] theorem mem_cubeSet_translateCube_iff {d : ℕ} {shift : Fin d → ℤ}
    {Q : TriadicCube d} {x : Vec d} :
    x ∈ cubeSet (translateCube shift Q) ↔
      x - (fun i => (shift i : ℝ) * cubeScaleFactor Q) ∈ cubeSet Q := by
  simp only [cubeSet, translateCube, cubeScaleFactor]
  constructor
  · intro hx i
    rcases hx i with ⟨hlo, hhi⟩
    constructor
    · refine le_sub_iff_add_le.mpr ?_
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_mul] using hlo
    · refine sub_lt_iff_lt_add.mpr ?_
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_mul] using hhi
  · intro hx i
    rcases hx i with ⟨hlo, hhi⟩
    constructor
    · have hlo' :
        (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q) +
            (shift i : ℝ) * cubeScaleFactor Q ≤
          x i :=
        le_sub_iff_add_le.mp hlo
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_mul] using hlo'
    · have hhi' :
        x i <
          (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q) +
            (shift i : ℝ) * cubeScaleFactor Q :=
        sub_lt_iff_lt_add.mp hhi
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_mul] using hhi

@[simp] theorem mem_openCubeSet_translateCube_iff {d : ℕ} {shift : Fin d → ℤ}
    {Q : TriadicCube d} {x : Vec d} :
    x ∈ openCubeSet (translateCube shift Q) ↔
      x - (fun i => (shift i : ℝ) * cubeScaleFactor Q) ∈ openCubeSet Q := by
  simp only [openCubeSet, translateCube, cubeScaleFactor]
  constructor
  · intro hx i
    rcases hx i with ⟨hlo, hhi⟩
    constructor
    · refine lt_sub_iff_add_lt.mpr ?_
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_mul] using hlo
    · refine sub_lt_iff_lt_add.mpr ?_
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_mul] using hhi
  · intro hx i
    rcases hx i with ⟨hlo, hhi⟩
    constructor
    · have hlo' :
        (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q) +
            (shift i : ℝ) * cubeScaleFactor Q <
          x i :=
        lt_sub_iff_add_lt.mp hlo
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_mul] using hlo'
    · have hhi' :
        x i <
          (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q) +
            (shift i : ℝ) * cubeScaleFactor Q :=
        sub_lt_iff_lt_add.mp hhi
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_mul] using hhi

def parentCube {d : ℕ} (Q : TriadicCube d) : TriadicCube d :=
  { scale := Q.scale + 1
    index := fun i => Int.ediv (Q.index i + 1) 3 }

def childCubes {d : ℕ} (Q : TriadicCube d) : Finset (TriadicCube d) :=
  Finset.univ.image fun digits : Fin d → Fin 3 =>
    { scale := Q.scale - 1
      index := fun i => 3 * Q.index i + (digits i : ℤ) - 1 }

def descendantsAtDepth {d : ℕ} (Q : TriadicCube d) : ℕ → Finset (TriadicCube d)
  | 0 => {Q}
  | n + 1 => (descendantsAtDepth Q n).biUnion childCubes

def descendantsAtScale {d : ℕ} (Q : TriadicCube d) (k : ℤ) : Finset (TriadicCube d) :=
  if _h : k ≤ Q.scale then
    descendantsAtDepth Q (Int.toNat (Q.scale - k))
  else
    ∅

noncomputable def cubeVolume {d : ℕ} (Q : TriadicCube d) : ℝ :=
  (cubeScaleFactor Q) ^ d

end Homogenization
