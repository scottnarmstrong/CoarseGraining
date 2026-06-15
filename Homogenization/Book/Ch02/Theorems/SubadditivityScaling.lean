import Homogenization.Internal.Ch02.SubadditivityScaling

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public theorem for `l.cg.subadditivity.basic.definitions`. -/
theorem responseSubadditivityAndScalingTheory {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    ResponseSubadditivityAndScalingTheory U a :=
  Homogenization.Internal.Ch02.BookCh02.responseSubadditivityAndScalingTheory U a

end

end Ch02
end Book
end Homogenization
