import Homogenization.Book.Ch04.Measurability
import Homogenization.Probability.LocalObservable

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Local coefficient observables

This file starts the Ch4 theorem surface for coefficient-field observables.
The primitive observable is the smooth local test used to generate
the restriction-local observable interface; downstream code should compose from
bundled `Observable`s instead of reproving measurability in Chapter 5.
-/

namespace Observable

/-- The smooth coefficient-field test observable,
bundled with its Ch4 locality proof. -/
noncomputable def localTest {d : ℕ} {U : Set (Vec d)}
    (e e' : Vec d) {φ : Vec d → ℝ}
    (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ U) :
    Observable d U ℝ where
  toFun := localTestObservable e e' φ
  isLocal := by
    refine measurable_of_isLocalObservable_restrictionSigma
      (measurable_localTestObservable e e' hφ_cont hφ_compact) ?_
    intro a b hab
    unfold localTestObservable
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    by_cases hxU : x ∈ U
    · simp [hab x hxU]
    · have hφ_zero : φ x = 0 := by
        by_contra hφx
        exact hxU (hφ_support (subset_tsupport φ hφx))
      simp [hφ_zero]

@[simp]
theorem localTest_apply {d : ℕ} {U : Set (Vec d)}
    (e e' : Vec d) {φ : Vec d → ℝ}
    (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ U) (a : CoeffField d) :
    localTest e e' hφ_cont hφ_compact hφ_support a =
      localTestObservable e e' φ a :=
  rfl

end Observable

end Ch04
end Book
end Homogenization
