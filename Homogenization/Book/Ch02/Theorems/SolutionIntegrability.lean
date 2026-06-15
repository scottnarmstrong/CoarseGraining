import Homogenization.Book.Ch02.Theorems.Existence
import Homogenization.Internal.Ch02.Representatives

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Solution

/-- Public solutions have `L²` flux on their Chapter 2 domain.

The public coefficient object is only a.e.-elliptic.  The proof changes to the
internal pointwise-good representative, applies the deterministic flux `L²`
bound there, and transports the result back across the a.e. equality of
coefficient representatives. -/
theorem flux_memVectorL2 {d : ℕ} {U : Domain d} {a : CoeffOn U}
    (u : Solution U a) :
    MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (a.toCoeffField x) (u.toH1.grad x)) := by
  let b : CoeffOn U := Internal.Ch02.BookCh02.pointwiseCoeffOn U a
  have hb : CoeffOn.AEEq b a := by
    simpa [b] using Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U a
  have hEll :
      IsEllipticFieldOn b.lam b.Lam (U : Set (Vec d)) b.toCoeffField := by
    simpa [b] using Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn U a
  have hbase :
      MemVectorL2 (U : Set (Vec d))
        (fun x => matVecMul (b.toCoeffField x) (u.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1.grad_memVectorL2
  refine MeasureTheory.MemLp.ae_eq ?_ hbase
  exact hb.mono fun x hx => by
    simp [hx]

end Solution

end

end Ch02
end Book
end Homogenization
