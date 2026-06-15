import Homogenization.Internal.Ch02.SymmetricDirichletNeumann

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public symmetric Dirichlet--Neumann theorem package
`l.symmetric.dirichlet.neumann.split.basic.definitions`.

The coefficient hypotheses are note-facing and a.e.-native: `a` is a public
coefficient field on a bounded open convex Chapter 2 domain, and `hsym` is
symmetry almost everywhere on that domain. -/
theorem responseSymmetricDirichletNeumannTheory {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (hsym : CoeffOn.IsSymmetric a) :
    ResponseSymmetricDirichletNeumannTheory U a hsym :=
  Homogenization.Internal.Ch02.BookCh02.responseSymmetricDirichletNeumannTheory
    U a hsym

end

end Ch02
end Book
end Homogenization
