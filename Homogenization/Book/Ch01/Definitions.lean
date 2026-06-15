import Homogenization.Besov.Duality.Full
import Homogenization.Book.Ch01.FieldSpaces

namespace Homogenization
namespace Book
namespace Ch01

open scoped ENNReal

/-!
# Chapter 1 public vocabulary

This file gives Chapter 1 a note-facing entry point without redefining the
underlying analysis.  The names below are abbreviations for the internally
proved cube, normalized norm, and Besov APIs.
-/

abbrev Vec (d : ℕ) :=
  Homogenization.Vec d

abbrev Cube (d : ℕ) :=
  Homogenization.TriadicCube d

noncomputable section

/-- Normalized cube average, matching the notes' `\fint_Q`. -/
noncomputable abbrev normalizedAverage {d : ℕ} (Q : Cube d)
    (u : Vec d → ℝ) : ℝ :=
  Homogenization.cubeAverage Q u

/-- Normalized cube `L^p` norm. -/
noncomputable abbrev normalizedLpNorm {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (Q : Cube d) (p : ℝ≥0∞)
    (u : Vec d → E) : ℝ :=
  Homogenization.cubeLpNorm Q p u

/-- Normalized cube `W^{1,p}` seminorm, with the gradient supplied as an
a.e.-representative. -/
noncomputable abbrev normalizedW1pSeminorm {d : ℕ} (Q : Cube d)
    (p : ℝ≥0∞) (Du : Vec d → Vec d) : ℝ :=
  Homogenization.cubeW1pSeminorm Q p Du

/-- Normalized cube `W^{1,p}` norm, with the gradient supplied as an
a.e.-representative. -/
noncomputable abbrev normalizedW1pNorm {d : ℕ} (Q : Cube d)
    (p : ℝ≥0∞) (u : Vec d → ℝ) (Du : Vec d → Vec d) : ℝ :=
  Homogenization.cubeW1pNorm Q p u Du

/-- Finite-depth positive Besov norm. -/
noncomputable abbrev positiveBesovPartialNorm {d : ℕ} (Q : Cube d)
    (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  Homogenization.cubeBesovDisjointPartialNorm Q s p q N u

/-- Finite-depth positive Besov norm in the `q = ∞` endpoint. -/
noncomputable abbrev positiveBesovPartialNormTop {d : ℕ} (Q : Cube d)
    (s : ℝ) (p : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  Homogenization.cubeBesovDisjointPartialNormTop Q s p N u

/-- Finite-depth positive Besov seminorm in the manuscript `q = 2` case. -/
noncomputable abbrev positiveBesovPartialSeminormTwo {d : ℕ} (Q : Cube d)
    (s : ℝ) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  Homogenization.cubeBesovDisjointPartialSeminorm Q s
    (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u

/-- Infinite-depth positive Besov seminorm in the manuscript `q = 2` case. -/
noncomputable abbrev positiveBesovSeminormTwo {d : ℕ} (Q : Cube d)
    (s : ℝ) (u : Vec d → ℝ) : ℝ :=
  sSup (Set.range fun N : ℕ =>
    Homogenization.cubeBesovDisjointPartialSeminorm Q s
      (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u)

/-- Finite-depth positive Besov norm in the manuscript `q = 2` case. -/
noncomputable abbrev positiveBesovPartialNormTwo {d : ℕ} (Q : Cube d)
    (s : ℝ) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  Homogenization.cubeBesovDisjointPartialNorm Q s
    (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u

/-- Infinite-depth positive Besov norm in the manuscript `q = 2` case. -/
noncomputable abbrev positiveBesovNormTwo {d : ℕ} (Q : Cube d)
    (s : ℝ) (u : Vec d → ℝ) : ℝ :=
  sSup (Set.range fun N : ℕ =>
    Homogenization.cubeBesovDisjointPartialNorm Q s
      (2 : ℝ≥0∞) (2 : ℝ≥0∞) (N + 1) u)

/-- Dimension-dependent constant in the positive Besov localization lemma.

The current cube-discrete proof gives the uniform value `2`; the argument keeps
the manuscript-shaped `d` parameter so downstream theorem statements can cite a
dimension constant. -/
noncomputable abbrev positiveBesovLocalizeConstant (_d : ℕ) : ℝ := 2

/-- Dimension-dependent constant in the negative Besov localization lemma. -/
noncomputable abbrev negativeBesovLocalizeConstant (_d : ℕ) : ℝ := 2

/-- Infinite-depth positive Besov norm in the `q = ∞` endpoint. -/
noncomputable abbrev positiveBesovNormTop {d : ℕ} (Q : Cube d)
    (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  sSup (Set.range fun N : ℕ =>
    Homogenization.cubeBesovDisjointPartialNormTop Q s p (N + 1) u)

/-- Componentwise vector-valued infinite-depth positive Besov norm in the
`q = ∞` endpoint.  This is the public convention for vector-valued Chapter 1
statements: sum the scalar positive Besov norms of the components. -/
noncomputable abbrev positiveBesovVectorNormTop {d : ℕ} (Q : Cube d)
    (s : ℝ) (p : ℝ≥0∞) (u : Vec d → Vec d) : ℝ :=
  ∑ i : Fin d, positiveBesovNormTop Q s p (fun x => u x i)

/-- Concrete circ negative Besov norm. -/
noncomputable abbrev circNegativeBesovNorm {d : ℕ} (Q : Cube d)
    (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  Homogenization.cubeBesovCircNorm Q s p q u

/-- Finite-depth concrete circ negative Besov norm. -/
noncomputable abbrev circNegativeBesovPartialNorm {d : ℕ} (Q : Cube d)
    (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  Homogenization.cubeBesovCircPartialNorm Q s p q N u

/-- Mean-zero dual negative Besov seminorm. -/
noncomputable abbrev dualNegativeBesovSeminorm {d : ℕ} (Q : Cube d)
    (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  Homogenization.cubeBesovDualMeanZeroSeminorm Q s p q u

/-- Full dual negative Besov norm. -/
noncomputable abbrev dualNegativeBesovNorm {d : ℕ} (Q : Cube d)
    (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  Homogenization.cubeBesovDualFullNorm Q s p q u

end

end Ch01
end Book
end Homogenization
