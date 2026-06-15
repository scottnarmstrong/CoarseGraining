import Homogenization.Book.Ch04.Measurability

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Local coefficient observables

This file starts the Ch4 theorem surface for coefficient-field observables.
The primitive observable is the smooth local test used to generate
`localSigma`; downstream code should compose from bundled `Observable`s instead
of reproving measurability in Chapter 5.
-/

namespace Observable

/-- The smooth coefficient-field test observable that generates `localSigma`,
bundled with its Ch4 locality proof. -/
noncomputable def localTest {d : ℕ} {U : Set (Vec d)}
    (e e' : Vec d) {φ : Vec d → ℝ}
    (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ U) :
    Observable d U ℝ where
  toFun := localTestObservable e e' φ
  isLocal := by
    change @Measurable (CoeffField d) ℝ (localSigma U) (borel ℝ)
      (localTestObservable e e' φ)
    simpa [localSigma] using
      measurable_localTestObservable_localSigma
        (U := U) e e' hφ_cont hφ_compact hφ_support

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
