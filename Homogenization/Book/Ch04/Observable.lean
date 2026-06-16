import Homogenization.Book.Ch04.Law

namespace Homogenization
namespace Book
namespace Ch04

open MeasureTheory

/-!
# Local observables

`IsLocalRandomVariable U X` is the only Ch4 predicate for random observables.
Everything downstream should enter measurability through this predicate and the
promotion lemmas in `Ch04.Measurability`.
-/

/-- A random observable depending only on the restriction-local coefficient-field
sigma algebra on `U`. -/
def IsLocalRandomVariable {β : Type*} [MeasurableSpace β] {d : ℕ}
    (U : Set (Vec d)) (X : CoeffField d → β) : Prop :=
  @Measurable (CoeffField d) β (restrictionSigma U) _ X

namespace IsLocalRandomVariable

/-- Monotonicity of the restriction-local coefficient-field sigma algebra. -/
theorem restrictionSigma_mono {d : ℕ} {U V : Set (Vec d)} (hUV : U ⊆ V) :
    restrictionSigma U ≤ restrictionSigma V :=
  RestrictionSigma_mono hUV

/-- A local observable on a smaller observation set is local on any larger one. -/
theorem mono {β : Type*} [MeasurableSpace β] {d : ℕ}
    {U V : Set (Vec d)} {X : CoeffField d → β}
    (hUV : U ⊆ V) (hX : IsLocalRandomVariable U X) :
    IsLocalRandomVariable V X := by
  intro s hs
  exact (restrictionSigma_mono (d := d) hUV) (X ⁻¹' s) (hX hs)

/-- Constant local observables. -/
theorem const {β : Type*} [MeasurableSpace β] {d : ℕ}
    (U : Set (Vec d)) (b : β) :
    IsLocalRandomVariable U (fun _a : CoeffField d => b) :=
  measurable_const

/-- Compose a local observable with a measurable map. -/
theorem comp_measurable {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {d : ℕ} {U : Set (Vec d)} {X : CoeffField d → β}
    (hX : IsLocalRandomVariable U X) {g : β → γ} (hg : Measurable g) :
    IsLocalRandomVariable U (fun a => g (X a)) :=
  hg.comp hX

/-- Locality of a vector-valued observable follows componentwise. -/
theorem vec_of_components {d m : ℕ} {U : Set (Vec d)}
    {X : CoeffField d → Vec m}
  (hX : ∀ i : Fin m, IsLocalRandomVariable U (fun a => X a i)) :
    IsLocalRandomVariable U X := by
  change @Measurable (CoeffField d) (Vec m) (restrictionSigma U) _ X
  rw [@measurable_pi_iff (CoeffField d) (Fin m) (fun _ => ℝ)
    (restrictionSigma U) (fun _ => inferInstance) X]
  intro i
  exact hX i

/-- Components of a vector-valued local observable are local. -/
theorem vec_component {d m : ℕ} {U : Set (Vec d)}
    {X : CoeffField d → Vec m}
    (hX : IsLocalRandomVariable U X) (i : Fin m) :
    IsLocalRandomVariable U (fun a => X a i) := by
  change @Measurable (CoeffField d) ℝ (restrictionSigma U) _ (fun a => X a i)
  exact ((@measurable_pi_iff (CoeffField d) (Fin m) (fun _ => ℝ)
    (restrictionSigma U) (fun _ => inferInstance) X).mp
    (show @Measurable (CoeffField d) (Vec m) (restrictionSigma U) _ X from hX)) i

/-- Locality of a matrix-valued observable follows entrywise. -/
theorem mat_of_entries {d m : ℕ} {U : Set (Vec d)}
    {X : CoeffField d → Mat m}
    (hX : ∀ i j : Fin m, IsLocalRandomVariable U (fun a => X a i j)) :
    IsLocalRandomVariable U X := by
  change @Measurable (CoeffField d) (Mat m) (restrictionSigma U) _ X
  rw [@measurable_pi_iff (CoeffField d) (Fin m) (fun _ => Fin m → ℝ)
    (restrictionSigma U) (fun _ => inferInstance) X]
  intro i
  rw [@measurable_pi_iff (CoeffField d) (Fin m) (fun _ => ℝ)
    (restrictionSigma U) (fun _ => inferInstance) (fun a => X a i)]
  intro j
  exact hX i j

/-- Entries of a matrix-valued local observable are local. -/
theorem mat_entry {d m : ℕ} {U : Set (Vec d)}
    {X : CoeffField d → Mat m}
    (hX : IsLocalRandomVariable U X) (i j : Fin m) :
    IsLocalRandomVariable U (fun a => X a i j) := by
  change @Measurable (CoeffField d) ℝ (restrictionSigma U) _ (fun a => X a i j)
  have hi :
      @Measurable (CoeffField d) (Fin m → ℝ) (restrictionSigma U) _
        (fun a => X a i) :=
    ((@measurable_pi_iff (CoeffField d) (Fin m) (fun _ => Fin m → ℝ)
      (restrictionSigma U) (fun _ => inferInstance) X).mp
        (show @Measurable (CoeffField d) (Mat m) (restrictionSigma U) _ X from hX)) i
  exact ((@measurable_pi_iff (CoeffField d) (Fin m) (fun _ => ℝ)
    (restrictionSigma U) (fun _ => inferInstance) (fun a => X a i)).mp hi) j

/-- Sum of real-valued local observables. -/
theorem add {d : ℕ} {U : Set (Vec d)} {X Y : CoeffField d → ℝ}
    (hX : IsLocalRandomVariable U X) (hY : IsLocalRandomVariable U Y) :
    IsLocalRandomVariable U (fun a => X a + Y a) :=
  Measurable.add hX hY

/-- Negation of a real-valued local observable. -/
theorem neg {d : ℕ} {U : Set (Vec d)} {X : CoeffField d → ℝ}
    (hX : IsLocalRandomVariable U X) :
    IsLocalRandomVariable U (fun a => -X a) :=
  Measurable.neg hX

/-- Difference of real-valued local observables. -/
theorem sub {d : ℕ} {U : Set (Vec d)} {X Y : CoeffField d → ℝ}
    (hX : IsLocalRandomVariable U X) (hY : IsLocalRandomVariable U Y) :
    IsLocalRandomVariable U (fun a => X a - Y a) :=
  Measurable.sub hX hY

/-- Product of real-valued local observables. -/
theorem mul {d : ℕ} {U : Set (Vec d)} {X Y : CoeffField d → ℝ}
    (hX : IsLocalRandomVariable U X) (hY : IsLocalRandomVariable U Y) :
    IsLocalRandomVariable U (fun a => X a * Y a) :=
  Measurable.mul hX hY

/-- Inverse of a real-valued local observable. -/
theorem inv {d : ℕ} {U : Set (Vec d)} {X : CoeffField d → ℝ}
    (hX : IsLocalRandomVariable U X) :
    IsLocalRandomVariable U (fun a => (X a)⁻¹) :=
  Measurable.inv hX

/-- Absolute value of a real-valued local observable. -/
theorem abs {d : ℕ} {U : Set (Vec d)} {X : CoeffField d → ℝ}
    (hX : IsLocalRandomVariable U X) :
    IsLocalRandomVariable U (fun a => |X a|) :=
  continuous_abs.measurable.comp hX

/-- Finite sums of real-valued local observables. -/
theorem finset_sum {d : ℕ} {ι : Type*} [Fintype ι]
    {U : Set (Vec d)} {X : ι → CoeffField d → ℝ}
    (hX : ∀ i, IsLocalRandomVariable U (X i)) :
    IsLocalRandomVariable U (fun a => ∑ i, X i a) := by
  classical
  exact Finset.measurable_sum Finset.univ fun i _hi => hX i

end IsLocalRandomVariable

/-- Bundled Chapter 4 observable.  This is the canonical object Ch5 should
consume: a function of the coefficient field together with its local-test
measurability proof. -/
structure Observable (d : ℕ) (U : Set (Vec d)) (β : Type*)
    [MeasurableSpace β] where
  toFun : CoeffField d → β
  isLocal : IsLocalRandomVariable U toFun

namespace Observable

variable {d m : ℕ} {U V : Set (Vec d)}

instance {β : Type*} [MeasurableSpace β] :
    CoeFun (Observable d U β) (fun _ => CoeffField d → β) :=
  ⟨Observable.toFun⟩

/-- Enlarge the observation set of a bundled observable. -/
def mono {β : Type*} [MeasurableSpace β] (X : Observable d U β)
    (hUV : U ⊆ V) : Observable d V β where
  toFun := X
  isLocal := X.isLocal.mono hUV

/-- Constant bundled observables. -/
def const {β : Type*} [MeasurableSpace β] (U : Set (Vec d)) (b : β) :
    Observable d U β where
  toFun := fun _a => b
  isLocal := IsLocalRandomVariable.const U b

/-- Measurable postcomposition of a bundled observable. -/
def comp {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (X : Observable d U β) (g : β → γ) (hg : Measurable g) :
    Observable d U γ where
  toFun := fun a => g (X a)
  isLocal := X.isLocal.comp_measurable hg

/-- Build a vector-valued bundled observable from bundled components. -/
def vecOfComponents (X : Fin m → Observable d U ℝ) :
    Observable d U (Vec m) where
  toFun := fun a i => X i a
  isLocal := IsLocalRandomVariable.vec_of_components fun i => (X i).isLocal

/-- Extract one component of a vector-valued bundled observable. -/
def vecComponent (X : Observable d U (Vec m)) (i : Fin m) :
    Observable d U ℝ where
  toFun := fun a => X a i
  isLocal := X.isLocal.vec_component i

/-- Build a matrix-valued bundled observable from bundled entries. -/
def matOfEntries (X : Fin m → Fin m → Observable d U ℝ) :
    Observable d U (Mat m) where
  toFun := fun a i j => X i j a
  isLocal := IsLocalRandomVariable.mat_of_entries fun i j => (X i j).isLocal

/-- Extract one entry of a matrix-valued bundled observable. -/
def matEntry (X : Observable d U (Mat m)) (i j : Fin m) :
    Observable d U ℝ where
  toFun := fun a => X a i j
  isLocal := X.isLocal.mat_entry i j

/-- Sum of real-valued bundled observables. -/
protected def add (X Y : Observable d U ℝ) : Observable d U ℝ where
  toFun := fun a => X a + Y a
  isLocal := X.isLocal.add Y.isLocal

/-- Negation of a real-valued bundled observable. -/
protected def neg (X : Observable d U ℝ) : Observable d U ℝ where
  toFun := fun a => -X a
  isLocal := X.isLocal.neg

/-- Difference of real-valued bundled observables. -/
protected def sub (X Y : Observable d U ℝ) : Observable d U ℝ where
  toFun := fun a => X a - Y a
  isLocal := X.isLocal.sub Y.isLocal

/-- Product of real-valued bundled observables. -/
protected def mul (X Y : Observable d U ℝ) : Observable d U ℝ where
  toFun := fun a => X a * Y a
  isLocal := X.isLocal.mul Y.isLocal

/-- Inverse of a real-valued bundled observable. -/
protected noncomputable def inv (X : Observable d U ℝ) : Observable d U ℝ where
  toFun := fun a => (X a)⁻¹
  isLocal := X.isLocal.inv

/-- Absolute value of a real-valued bundled observable. -/
protected def abs (X : Observable d U ℝ) : Observable d U ℝ where
  toFun := fun a => |X a|
  isLocal := X.isLocal.abs

/-- Finite sum of real-valued bundled observables over a finite type. -/
def finsetSum {ι : Type*} [Fintype ι] (X : ι → Observable d U ℝ) :
    Observable d U ℝ where
  toFun := fun a => ∑ i, X i a
  isLocal := IsLocalRandomVariable.finset_sum fun i => (X i).isLocal

end Observable

end Ch04
end Book
end Homogenization
