import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ArbitraryCubeEndpoint

namespace Homogenization

open scoped ENNReal

noncomputable section

/-- Neumann `W2,2` / Calderon-Zygmund regularity for the mean-zero Neumann
Poisson problem on a cube, stated in the downstream positive Besov form.

Informally, if `-Delta W = F - (F)_Q` with Neumann boundary condition and
zero average, then `||nabla^2 W||_L2(Q) <= C ||F||_L2(Q)`. Local Poincare on
each triadic subcube converts this Hessian estimate into the uniform
`B^1_{2,infty}` bounds on the components of `nabla W` recorded by
`CubePoissonGradientDualTestNormL2CoreEstimate`. -/
def CubeNeumannW22CalderonZygmundRegularity {d : ℕ}
    (Q : TriadicCube d) (C : ℝ) : Prop :=
  CubePoissonGradientDualTestNormL2CoreEstimate Q C

/-- Dimension-uniform Neumann `W2,2` / Calderon-Zygmund regularity on cubes. -/
def CubeNeumannW22CalderonZygmundRegularityInDimension
    (d : ℕ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ Q : TriadicCube d, CubeNeumannW22CalderonZygmundRegularity Q C

/-- Chosen dimension-only Neumann `W2,2` / Calderon-Zygmund constant, obtained
from the exact reflected-parent depth constant plus the exact component-average
constant. -/
noncomputable def cubeNeumannW22CalderonZygmundConstant
    (d : ℕ) [NeZero d] : ℝ :=
  originCubeWeakInteriorDepthConstantExact d 0 +
    (d : ℝ) * (originCubeMeanZeroH1CoerciveEstimate d 0).constant

theorem cubeNeumannW22CalderonZygmundConstant_nonneg
    (d : ℕ) [NeZero d] :
    0 ≤ cubeNeumannW22CalderonZygmundConstant d := by
  exact add_nonneg
    (originCubeWeakInteriorDepthConstantExact_nonneg d 0)
    (mul_nonneg (Nat.cast_nonneg d)
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg)

/-- Selected dimension-uniform Neumann `W2,2` / Calderon-Zygmund regularity on
a cube. -/
theorem cubeNeumannW22CalderonZygmundRegularity
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    CubeNeumannW22CalderonZygmundRegularity Q
      (cubeNeumannW22CalderonZygmundConstant d) := by
  have hcore :=
    MeanZeroNeumannPoissonSolution.cubePoissonGradientDualTestNormL2CoreEstimate_cube Q
  have hdepth := cubeWeakInteriorDepthConstant_eq_dimensionConstant Q
  have havg := cubePoissonGradientAverageConstant_eq_dimensionConstant Q
  simpa [CubeNeumannW22CalderonZygmundRegularity,
    cubeNeumannW22CalderonZygmundConstant, hdepth, havg] using hcore

/-- Dimension-uniform Neumann `W2,2` / Calderon-Zygmund regularity exists with
the explicit constant above. -/
theorem exists_cubeNeumannW22CalderonZygmundRegularityInDimension
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, CubeNeumannW22CalderonZygmundRegularityInDimension d C := by
  exact ⟨cubeNeumannW22CalderonZygmundConstant d,
    cubeNeumannW22CalderonZygmundConstant_nonneg d,
    cubeNeumannW22CalderonZygmundRegularity⟩

/-- Local existence form of the dimension-uniform Neumann `W2,2` /
Calderon-Zygmund regularity input. -/
theorem exists_cubeNeumannW22CalderonZygmundRegularity
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    ∃ C : ℝ, CubeNeumannW22CalderonZygmundRegularity Q C :=
  ⟨cubeNeumannW22CalderonZygmundConstant d,
    cubeNeumannW22CalderonZygmundRegularity Q⟩

/-- Downstream positive-test core estimate obtained from the named Neumann
`W2,2` / Calderon-Zygmund regularity statement. -/
theorem exists_cubePoissonGradientDualTestNormL2CoreEstimate
    {d : ℕ} [NeZero d] (Q : TriadicCube d) :
    ∃ C : ℝ, CubePoissonGradientDualTestNormL2CoreEstimate Q C := by
  exact
    ⟨cubeNeumannW22CalderonZygmundConstant d,
      cubeNeumannW22CalderonZygmundRegularity Q⟩

end

end Homogenization
