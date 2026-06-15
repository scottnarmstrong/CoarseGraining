import Homogenization.Sobolev.PotentialSolenoidalL2
import Homogenization.Sobolev.H1.LocalizedZeroTrace

namespace Homogenization
namespace Book
namespace Ch01

/-!
# Chapter 1 public field-space predicates

This lightweight module exposes the potential, solenoidal, and localized
zero-trace vocabulary needed by later chapter definitions without importing the
Chapter 1 Besov abbreviations.
-/

/-- Public `L²` potential fields on `U`, stated up to a.e. equality. -/
def PotentialFieldOn {d : ℕ} (U : Set (Vec d)) (f : Vec d → Vec d) : Prop :=
  MemVectorL2 U f ∧ ∃ u : H1Function U, f =ᵐ[volumeMeasureOn U] u.grad

/-- Public zero-trace `L²` potential fields on `U`, stated up to a.e. equality. -/
def PotentialZeroTraceFieldOn {d : ℕ} (U : Set (Vec d))
    (f : Vec d → Vec d) : Prop :=
  MemVectorL2 U f ∧
    ∃ u : H10Function U, f =ᵐ[volumeMeasureOn U] u.toH1Function.grad

/-- Public localized scalar zero-trace condition.

This is the a.e./Sobolev replacement for saying that a scalar function vanishes
on the part of `∂Ω` seen through the localization window `V`: every smooth
compactly supported cutoff localized in `V` turns the function into an
admissible `H¹₀(Ω)` test function. -/
abbrev LocalizedZeroTraceFunctionOn {d : ℕ} (Ω V : Set (Vec d))
    (u : Vec d → ℝ) : Prop :=
  Homogenization.LocalizedZeroTraceFunctionOn Ω V u

/-- Public `L²` solenoidal fields on `U`. The integral formulation is
a.e.-insensitive once the `L²` representative is fixed. -/
def SolenoidalFieldOn {d : ℕ} (U : Set (Vec d)) (g : Vec d → Vec d) : Prop :=
  MemVectorL2 U g ∧
    ∀ φ : H10Function U,
      ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume = 0

/-- Public `L²` solenoidal fields with zero normal trace on `U`. -/
def SolenoidalZeroNormalTraceFieldOn {d : ℕ} (U : Set (Vec d))
    (g : Vec d → Vec d) : Prop :=
  MemVectorL2 U g ∧
    ∀ φ : H1Function U,
      ∫ x in U, vecDot (g x) (φ.grad x) ∂MeasureTheory.volume = 0

end Ch01
end Book
end Homogenization
