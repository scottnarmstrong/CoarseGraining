import Homogenization.HighContrast.Corridor.FixedPhase.ClampedObservable
import Homogenization.HighContrast.Corridor.FixedPhase.EfronSteinAE

/-!
# The Efron–Stein bound for the fixed-phase observable

The capstone.  Combining the product-measurable clamped observable
(`ClampedObservable`) with the landed a.e.-measurable Efron–Stein transfer
(`efronStein_transfer_ae`), we obtain the Efron–Stein variance bound for the
fixed-phase observable `F_σ` in the **two-field surgery** (`patchCore`) form that
the fixed-phase variance assembly consumes.

The two evaluation-point identities are *exact* tuple identities (no a.e.
reasoning): with `patchCore` the two-field core surgery,
`Function.update (R a) k (a'|_{coreBox k}) = R (patchCore k a a')`, so the
resampled observable is literally the diagonal observable of the surgered field.
All a.e. reasoning is confined to the single truncation-congruence layer:
`clampedPhaseObservable (R b) = F_σ(b)` for measurable, a.e.-elliptic `b`
(`clampedPhaseObservable_restrict_eq_of_field`), instantiated at `b = a` and at
`b = patchCore k a a'` under `ThetaEllipticLaw` for both draws.
-/

open Homogenization
open scoped MeasureTheory ProbabilityTheory BigOperators
open MeasureTheory ProbabilityTheory

namespace Homogenization

variable {d : ℕ}

/-! ## The two-field core surgery -/

/-- The two-field core surgery: `a'` on the core `coreBox ℓ σ j`, `a` off it. -/
noncomputable def patchCore (ℓ : ℝ) (σ : Vec d) (j : Fin d → ℤ) (a a' : CoeffField d) :
    CoeffField d := by
  classical
  exact fun x => if x ∈ coreBox ℓ σ j then a' x else a x

@[simp] theorem patchCore_apply_of_mem {ℓ : ℝ} {σ : Vec d} {j : Fin d → ℤ}
    {a a' : CoeffField d} {x : Vec d} (hx : x ∈ coreBox ℓ σ j) :
    patchCore ℓ σ j a a' x = a' x := by simp [patchCore, hx]

@[simp] theorem patchCore_apply_of_not_mem {ℓ : ℝ} {σ : Vec d} {j : Fin d → ℤ}
    {a a' : CoeffField d} {x : Vec d} (hx : x ∉ coreBox ℓ σ j) :
    patchCore ℓ σ j a a' x = a x := by simp [patchCore, hx]

theorem measurable_patchCore_entry {ℓ : ℝ} {σ : Vec d} {j : Fin d → ℤ}
    {a a' : CoeffField d}
    (ha : ∀ i j' : Fin d, Measurable fun x : Vec d => a x i j')
    (ha' : ∀ i j' : Fin d, Measurable fun x : Vec d => a' x i j') :
    ∀ i j' : Fin d, Measurable fun x : Vec d => patchCore ℓ σ j a a' x i j' := by
  classical
  intro i j'
  have hrw : (fun x : Vec d => patchCore ℓ σ j a a' x i j')
      = fun x : Vec d => if x ∈ coreBox ℓ σ j then a' x i j' else a x i j' := by
    funext x
    by_cases hx : x ∈ coreBox ℓ σ j
    · rw [patchCore_apply_of_mem hx, if_pos hx]
    · rw [patchCore_apply_of_not_mem hx, if_neg hx]
  rw [hrw]
  exact Measurable.ite (measurableSet_coreBox ℓ σ j) (ha' i j') (ha i j')

theorem ae_isEllipticMatrix_patchCore {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {j : Fin d → ℤ}
    {a a' : CoeffField d}
    (ha : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 Θ (a x))
    (ha' : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 Θ (a' x)) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 Θ (patchCore ℓ σ j a a' x) := by
  filter_upwards [ha, ha'] with x hxa hxa'
  by_cases hx : x ∈ coreBox ℓ σ j
  · rw [patchCore_apply_of_mem hx]; exact hxa'
  · rw [patchCore_apply_of_not_mem hx]; exact hxa

/-! ## The exact update identity -/

theorem restrictCoeffField_congr {U : Set (Vec d)} {f g : CoeffField d}
    (h : ∀ x ∈ U, f x = g x) : restrictCoeffField U f = restrictCoeffField U g := by
  funext x
  by_cases hx : x ∈ U
  · rw [restrictCoeffField_apply_of_mem hx, restrictCoeffField_apply_of_mem hx, h x hx]
  · rw [restrictCoeffField_apply_of_not_mem hx, restrictCoeffField_apply_of_not_mem hx]

/-- **Exact update identity.**  Updating the `k`-th coordinate of the diagonal
restriction tuple by a fresh core-restriction of `a'` equals the diagonal
restriction tuple of the surgered field `patchCore k a a'` (using core
disjointness off `k`). -/
theorem update_restrict_eq_restrict_patchCore {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {σ : Vec d}
    {K : Finset (Fin d → ℤ)} (k : {k // k ∈ K}) (a a' : CoeffField d) :
    Function.update
        (fun k' : {k // k ∈ K} => restrictCoeffField (coreBox ℓ σ k'.val) a) k
        (restrictCoeffField (coreBox ℓ σ k.val) a')
      = fun k' : {k // k ∈ K} =>
          restrictCoeffField (coreBox ℓ σ k'.val) (patchCore ℓ σ k.val a a') := by
  classical
  funext k'
  rcases eq_or_ne k' k with rfl | hkk'
  · rw [Function.update_self]
    refine restrictCoeffField_congr (fun x hx => ?_)
    rw [patchCore_apply_of_mem hx]
  · rw [Function.update_of_ne hkk']
    refine restrictCoeffField_congr (fun x hx => ?_)
    have hne : k.val ≠ k'.val := fun h => hkk' (Subtype.ext h.symm)
    have hxnk : x ∉ coreBox ℓ σ k.val := not_mem_coreBox_of_mem hℓ σ hne hx
    rw [patchCore_apply_of_not_mem hxnk]

/-! ## The Efron–Stein bound -/

/-- **Efron–Stein for the fixed-phase observable.**
Under a unit-range-dependent, `Θ`-elliptic probability law, the variance of the
fixed-phase observable is controlled by the sum, over the cores meeting the
cube, of the two-field core-resampling energies — the `patchCore` form consumed
by the fixed-phase variance assembly. -/
theorem efronStein_phaseObservable [NeZero d]
    {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ} (hℓ : 0 < ℓ) (hΘ : 1 ≤ Θ) (P : BlockVec d)
    {L : Measure (CoeffField d)} [IsProbabilityMeasure L]
    (hURD : IsUnitRangeDependent L) (hL : ThetaEllipticLaw Θ L)
    (K : Finset (Fin d → ℤ))
    (hK : ∀ k : Fin d → ℤ,
      (coreBox ℓ σ k ∩ cubeSet (originCube d m)).Nonempty → k ∈ K) :
    Var[fun a => phaseObservable ℓ σ m P a; L]
      ≤ (1 / 2) * ∑ k : {k // k ∈ K},
          ∫ a, ∫ a',
            (phaseObservable ℓ σ m P (patchCore ℓ σ k.val a a')
              - phaseObservable ℓ σ m P a) ^ 2 ∂L ∂L := by
  classical
  -- pairwise unit-separation of the cores
  have hsep : Pairwise fun i j : {k // k ∈ K} =>
      AreUnitSeparated (coreBox ℓ σ i.val) (coreBox ℓ σ j.val) :=
    pairwise_areUnitSeparated_coreBox hℓ.le σ (Subtype.val_injective)
  -- the clamped observable is measurable and globally bounded
  have hG : AEStronglyMeasurable
      (fun y : {k // k ∈ K} → CoeffField d => clampedPhaseObservable ℓ σ Θ m P K y)
      (Measure.pi (fun i : {k // k ∈ K} =>
        L.map (restrictCoeffField (coreBox ℓ σ i.val)))) :=
    (measurable_clampedPhaseObservable P K).aestronglyMeasurable
  have hMG : ∀ y, |clampedPhaseObservable ℓ σ Θ m P K y| ≤ phaseBound Θ P :=
    abs_clampedPhaseObservable_le hΘ P K
  -- run the landed a.e.-measurable transfer
  have key :=
    efronStein_transfer_ae (C := fun i : {k // k ∈ K} => coreBox ℓ σ i.val) hsep hURD
      hG hMG (fun a k => restrictCoeffField (coreBox ℓ σ k.val) a) rfl
  -- diagonal identity `G ∘ R =ᵐ[L] F_σ`
  have hGRae :
      ((fun y : {k // k ∈ K} → CoeffField d => clampedPhaseObservable ℓ σ Θ m P K y) ∘
          fun a k => restrictCoeffField (coreBox ℓ σ k.val) a)
        =ᵐ[L] fun a => phaseObservable ℓ σ m P a := by
    filter_upwards [hL] with a ha
    exact clampedPhaseObservable_restrict_eq_of_field hℓ hΘ P K hK a ha.1 ha.2
  -- lift the `ThetaEllipticLaw` events to the product law
  have hL1 : ∀ᵐ p ∂(L.prod L),
      (∀ i j : Fin d, Measurable fun x : Vec d => p.1 x i j) ∧
        ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 Θ (p.1 x) :=
    (Measure.quasiMeasurePreserving_fst).ae hL
  have hL2 : ∀ᵐ p ∂(L.prod L),
      (∀ i j : Fin d, Measurable fun x : Vec d => p.2 x i j) ∧
        ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 Θ (p.2 x) :=
    (Measure.quasiMeasurePreserving_snd).ae hL
  have hRae_prod : ∀ᵐ p ∂(L.prod L),
      clampedPhaseObservable ℓ σ Θ m P K
          (fun k => restrictCoeffField (coreBox ℓ σ k.val) p.1)
        = phaseObservable ℓ σ m P p.1 :=
    (Measure.quasiMeasurePreserving_fst).ae hGRae
  -- the per-core double-integral transfer
  have hterm : ∀ k : {k // k ∈ K},
      (∫ a, ∫ a',
        (clampedPhaseObservable ℓ σ Θ m P K
            (Function.update
              (fun k' => restrictCoeffField (coreBox ℓ σ k'.val) a) k
              (restrictCoeffField (coreBox ℓ σ k.val) a'))
          - clampedPhaseObservable ℓ σ Θ m P K
              (fun k' => restrictCoeffField (coreBox ℓ σ k'.val) a)) ^ 2 ∂L ∂L)
        = ∫ a, ∫ a',
            (phaseObservable ℓ σ m P (patchCore ℓ σ k.val a a')
              - phaseObservable ℓ σ m P a) ^ 2 ∂L ∂L := by
    intro k
    have hupd : ∀ᵐ p ∂(L.prod L),
        clampedPhaseObservable ℓ σ Θ m P K
            (Function.update
              (fun k' => restrictCoeffField (coreBox ℓ σ k'.val) p.1) k
              (restrictCoeffField (coreBox ℓ σ k.val) p.2))
          = phaseObservable ℓ σ m P (patchCore ℓ σ k.val p.1 p.2) := by
      filter_upwards [hL1, hL2] with p hp1 hp2
      rw [update_restrict_eq_restrict_patchCore hℓ.le k p.1 p.2]
      exact clampedPhaseObservable_restrict_eq_of_field hℓ hΘ P K hK
        (patchCore ℓ σ k.val p.1 p.2)
        (measurable_patchCore_entry hp1.1 hp2.1)
        (ae_isEllipticMatrix_patchCore hp1.2 hp2.2)
    have hprodae :
        (fun p : CoeffField d × CoeffField d =>
          (clampedPhaseObservable ℓ σ Θ m P K
              (Function.update
                (fun k' => restrictCoeffField (coreBox ℓ σ k'.val) p.1) k
                (restrictCoeffField (coreBox ℓ σ k.val) p.2))
            - clampedPhaseObservable ℓ σ Θ m P K
                (fun k' => restrictCoeffField (coreBox ℓ σ k'.val) p.1)) ^ 2)
          =ᵐ[L.prod L]
        (fun p : CoeffField d × CoeffField d =>
          (phaseObservable ℓ σ m P (patchCore ℓ σ k.val p.1 p.2)
            - phaseObservable ℓ σ m P p.1) ^ 2) := by
      filter_upwards [hupd, hRae_prod] with p h1 h2
      rw [h1, h2]
    refine integral_congr_ae ?_
    filter_upwards [Measure.ae_ae_of_ae_prod hprodae] with a haa
    exact integral_congr_ae haa
  -- assemble
  calc Var[fun a => phaseObservable ℓ σ m P a; L]
      = Var[(fun y : {k // k ∈ K} → CoeffField d => clampedPhaseObservable ℓ σ Θ m P K y) ∘
            fun a k => restrictCoeffField (coreBox ℓ σ k.val) a; L] :=
        (variance_congr hGRae).symm
    _ ≤ (1 / 2) * ∑ k : {k // k ∈ K},
          ∫ a, ∫ a',
            (clampedPhaseObservable ℓ σ Θ m P K
                (Function.update
                  (fun k' => restrictCoeffField (coreBox ℓ σ k'.val) a) k
                  (restrictCoeffField (coreBox ℓ σ k.val) a'))
              - clampedPhaseObservable ℓ σ Θ m P K
                  (fun k' => restrictCoeffField (coreBox ℓ σ k'.val) a)) ^ 2 ∂L ∂L := key
    _ = (1 / 2) * ∑ k : {k // k ∈ K},
          ∫ a, ∫ a',
            (phaseObservable ℓ σ m P (patchCore ℓ σ k.val a a')
              - phaseObservable ℓ σ m P a) ^ 2 ∂L ∂L := by
        congr 1
        exact Finset.sum_congr rfl (fun k _ => hterm k)

end Homogenization
