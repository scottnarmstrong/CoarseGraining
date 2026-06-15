import Homogenization.Internal.Ch02.BlockMatrixField

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public Chapter 2 block-matrix field algebra theorem
`l.block.matrix.field.basic.definitions`. -/
theorem blockMatrixFieldAlgebraTheory {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    BlockMatrixFieldAlgebraTheory U a :=
  Homogenization.Internal.Ch02.BookCh02.blockMatrixFieldAlgebraTheory U a

end

end Ch02
end Book
end Homogenization
