import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.CoeffField
import Homogenization.Book.Ch03.Definitions
import Homogenization.Book.Ch02.Theorems.HomogenizationError
import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity
import Homogenization.Deterministic.CoarseFluxResponse.RHS
import Homogenization.Deterministic.HomogenizationBlackBoxes.Duality
import Homogenization.Deterministic.HomogenizationBlackBoxes.CoarseGrainingL2
import Homogenization.Deterministic.CoarsePoincareRHS.ForceLocalization
import Homogenization.Deterministic.CoarsePoincareRHS.TerminalBounds
import Homogenization.Deterministic.WeakFluxRHS.GlobalIteration
import Homogenization.Deterministic.WeakFluxRHS.WeakSolutionBridge
import Homogenization.Deterministic.WeakNormInterfaces.AECongruence
import Homogenization.Deterministic.WeakNormInterfacesComponentwise
import Homogenization.PDE.EnergyIdentities
import Homogenization.PDE.NeumannRHS
import Homogenization.Sobolev.PotentialSolenoidalCubeBridge

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Public H1 domain casts for Chapter 3

This file contains small domain-cast helpers used to transport public open-cube
H1, H10, and mean-zero H1 data to the deterministic cube realization.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable def castH1Domain {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1Function U) : H1Function V :=
  hUV ▸ u

noncomputable def castH10Domain {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H10Function U) : H10Function V :=
  hUV ▸ u

@[simp] theorem castH1Domain_grad {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1Function U) :
    (castH1Domain hUV u).grad = u.grad := by
  subst V
  rfl

@[simp] theorem castH1Domain_toFun {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1Function U) :
    (castH1Domain hUV u).toFun = u.toFun := by
  subst V
  rfl

@[simp] theorem castH10Domain_toH1Function_grad
    {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H10Function U) :
    (castH10Domain hUV u).toH1Function.grad = u.toH1Function.grad := by
  subst V
  rfl

@[simp] theorem castH10Domain_toH1Function_toFun
    {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H10Function U) :
    (castH10Domain hUV u).toH1Function.toFun = u.toH1Function.toFun := by
  subst V
  rfl

noncomputable def castH1MeanZeroDomain {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1MeanZeroFunction U) : H1MeanZeroFunction V :=
  hUV ▸ u

@[simp] theorem castH1MeanZeroDomain_toH1Function_grad
    {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1MeanZeroFunction U) :
    (castH1MeanZeroDomain hUV u).toH1Function.grad =
      u.toH1Function.grad := by
  subst V
  rfl

@[simp] theorem castH1MeanZeroDomain_toH1Function_toFun
    {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1MeanZeroFunction U) :
    (castH1MeanZeroDomain hUV u).toH1Function.toFun =
      u.toH1Function.toFun := by
  subst V
  rfl


end

end Ch03
end Book
end Homogenization
