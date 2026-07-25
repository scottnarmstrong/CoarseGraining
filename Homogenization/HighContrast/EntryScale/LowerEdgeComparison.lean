import Homogenization.Book.Ch05.Theorems.Section52.ScalarAlgebra
import Homogenization.Book.Ch05.Theorems.Section52.MomentBounds
import Homogenization.Book.Ch04.Theorems.MomentFactorBounds.Helpers
import Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.InputSpecializations.FaithfulDescendant
import Homogenization.Deterministic.MultiscaleQuantitiesBasic.Foundation.GeometricOne
import Homogenization.HighContrast.EntryScale.DeterministicAlgebra
import Homogenization.HighContrast.EntryScale.RawHighContrastWeakNorm
import Homogenization.HighContrast.EntryScale.ResponseMoment
import Homogenization.HighContrast.EntryScale.Section52Index

/-!
# Multiscale lower-edge coefficient comparison

This file contains the algebraic landing pad for the corrected multiscale
lower-edge coefficient. The analytic work is to prove the dimensionless
component bound for the full descendant coefficient. Once that bound is
available, the theorems below convert it into the terminal scalar prefactor
already used by final assembly.
-/

namespace Homogenization.HighContrast.EntryScale

open Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations
open Homogenization.Book.Ch05.Section54.OneStepContraction

noncomputable section

/-- Small-tail observable in the current-baseline upper Section 5.2 split. -/
noncomputable def lowerEdgeCurrentUpperSection52SmallTail
    (d : Nat) [NeZero d] (k : Nat) (s : Real) :
    Homogenization.RegCoeffField d -> Real := fun a =>
  Homogenization.Book.Ch05.Section52.upperSmallSqrtTailCoeffField
      (d := d) k s a ^ 2 /
    Homogenization.Book.Ch05.Section52.section52SmallTailWeight s k

/-- Large-scale parent-window observable in the current-baseline upper Section 5.2 split. -/
noncomputable def lowerEdgeCurrentUpperSection52LargeScalePositiveExcess
    {d : Nat} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (k : Nat) (s : Real)
    (n : {n : Int //
      n ∈ Homogenization.Book.Ch05.Section52.section52LargeScaleSet k}) :
    Homogenization.RegCoeffField d -> Real := fun a =>
  Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s k n.1 *
    (let parents := Homogenization.descendantsAtScale
        (Homogenization.originCube d (k : Int)) n.1
     let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty
          (Homogenization.originCube d (k : Int))
          (Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
     parents.sup' hparents
      (fun Q =>
        max
          (Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix
                (Homogenization.cubeSet Q) a).upperLeft -
            Homogenization.Book.Ch02.matrixNorm
              (hP.barSigmaAtScale hStruct (k : Int) •
                (1 : Homogenization.Mat d)))
          0))

/-- Small-tail observable in the current-baseline lower/star Section 5.2 split. -/
noncomputable def lowerEdgeCurrentLowerSection52SmallTail
    (d : Nat) [NeZero d] (k : Nat) (s : Real) :
    Homogenization.RegCoeffField d -> Real := fun a =>
  Homogenization.Book.Ch05.Section52.lowerSmallSqrtTailCoeffField
      (d := d) k s a ^ 2 /
    Homogenization.Book.Ch05.Section52.section52SmallTailWeight s k

/-- Large-scale parent-window observable in the current-baseline lower/star Section 5.2 split. -/
noncomputable def lowerEdgeCurrentLowerSection52LargeScalePositiveExcess
    {d : Nat} [NeZero d] {P : Homogenization.Book.Ch04.CoeffLaw d}
    (hP : Homogenization.Book.Ch04.LawCarrier P)
    (hStruct : Homogenization.Book.Ch04.StructuralLaw P)
    (k : Nat) (s : Real)
    (n : {n : Int //
      n ∈ Homogenization.Book.Ch05.Section52.section52LargeScaleSet k}) :
    Homogenization.RegCoeffField d -> Real := fun a =>
  Homogenization.Book.Ch05.Section52.section52LargeScaleWeight s k n.1 *
    (let parents := Homogenization.descendantsAtScale
        (Homogenization.originCube d (k : Int)) n.1
     let hparents : parents.Nonempty :=
        Homogenization.descendantsAtScale_nonempty
          (Homogenization.originCube d (k : Int))
          (Homogenization.Book.Ch05.Section52.section52LargeScaleSet_mem_le_m n.2)
     parents.sup' hparents
      (fun Q =>
        max
          (Homogenization.Book.Ch02.matrixNorm
              (Homogenization.coarseBlockMatrix
                (Homogenization.cubeSet Q) a).lowerRight -
            Homogenization.Book.Ch02.matrixNorm
              ((hP.barSigmaStarAtScale hStruct (k : Int))⁻¹ •
                (1 : Homogenization.Mat d)))
          0))