import Homogenization.Book.Ch01.Definitions
import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.Regularity

namespace Homogenization
namespace Book
namespace Ch01

open scoped ENNReal

noncomputable section

/-- Public selected Neumann `W^{2,2}` / Calderon-Zygmund constant on cubes. -/
noncomputable abbrev cubeNeumannW22Constant (d : ℕ) [NeZero d] : ℝ :=
  Homogenization.cubeNeumannW22CalderonZygmundConstant d

theorem cubeNeumannW22Constant_nonneg (d : ℕ) [NeZero d] :
    0 ≤ cubeNeumannW22Constant d := by
  simpa [cubeNeumannW22Constant] using
    Homogenization.cubeNeumannW22CalderonZygmundConstant_nonneg d

/-- Public cube Neumann `W^{2,2}` / Calderon-Zygmund regularity theorem. -/
theorem cubeNeumannW22Regularity {d : ℕ} [NeZero d] (Q : Cube d) :
    Homogenization.CubeNeumannW22CalderonZygmundRegularity Q
      (cubeNeumannW22Constant d) := by
  simpa [cubeNeumannW22Constant] using
    Homogenization.cubeNeumannW22CalderonZygmundRegularity Q

/-- Dimension-uniform existence form of cube Neumann `W^{2,2}` regularity. -/
theorem exists_cubeNeumannW22RegularityInDimension (d : ℕ) [NeZero d] :
    ∃ C : ℝ,
      Homogenization.CubeNeumannW22CalderonZygmundRegularityInDimension d C :=
  Homogenization.exists_cubeNeumannW22CalderonZygmundRegularityInDimension d

end

end Ch01
end Book
end Homogenization
