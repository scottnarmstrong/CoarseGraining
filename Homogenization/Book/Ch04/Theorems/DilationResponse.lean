import Homogenization.Book.Ch04.Theorems.DilationLaw

namespace Homogenization
namespace Book
namespace Ch04

noncomputable section

/-!
# Response observables under dilation

This file exposes the arbitrary-cube response observable transport used by the
Section 5.6 wrap-around branch.  `DilationLaw` already contained the origin-cube
specialization needed for scale-normalized laws; descendant averages need the
same statement before specializing to origin descendants.
-/

theorem responseJObservableCubeSet_rescaleCoeffField_of_aelocallyUniformlyElliptic
    {d : ℕ} [NeZero d] {a : CoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (k : ℕ)
    (Q : TriadicCube d) (p q : Vec d) :
    responseJObservableCubeSet Q p q (rescaleCoeffField k a) =
      responseJObservableCubeSet (Ch02.dilateCube (k : ℤ) Q) p q a := by
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let G : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField
      (rescaleCoeffField k a) (ha.of_rescaleCoeffField k)
  let B : Ch02.TriadicCoeffFamily d := Ch02.TriadicCoeffFamily.dilate (-(k : ℤ)) F
  let Qsrc : TriadicCube d := Ch02.dilateCube (k : ℤ) Q
  have htarget : Ch02.dilateCube (-(k : ℤ)) Qsrc = Q := by
    simpa [Qsrc] using Ch02.dilateCube_neg_dilateCube (k : ℤ) Q
  have hGB : Ch02.TriadicCoeffFamily.AEEq G B := by
    simpa [G, B, F] using triadicCoeffFamily_rescaleCoeffField_aeeq_dilate ha k
  have hAEEq : Ch02.responseJ (Ch02.cubeDomain Q) (G.coeffOn Q) p q =
      Ch02.responseJ (Ch02.cubeDomain Q) (B.coeffOn Q) p q :=
    Ch02.responseJ_eq_ofAEEq (hGB Q) p q
  have hdilate :=
    Ch02.responseJ_dilate
      (Ch02.TriadicCoeffFamily.isDilation_dilate (-(k : ℤ)) F Qsrc) p q
  have hdilate' :
      Ch02.responseJ (Ch02.cubeDomain Q) (B.coeffOn Q) p q =
        Ch02.responseJ (Ch02.cubeDomain Qsrc) (F.coeffOn Qsrc) p q := by
    rw [htarget] at hdilate
    simpa [B] using hdilate
  calc
    responseJObservableCubeSet Q p q (rescaleCoeffField k a)
        = Ch02.responseJ (Ch02.cubeDomain Q) (G.coeffOn Q) p q := by
          symm
          calc
            Ch02.responseJ (Ch02.cubeDomain Q) (G.coeffOn Q) p q =
                ResponseJ (openCubeSet Q) p q (rescaleCoeffField k a) := by
                  simpa [G, triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
                    coeffOnOfAEEllipticOn_toCoeffField, Ch02.cubeDomain_coe] using
                    Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ
                      (Ch02.cubeDomain Q) (G.coeffOn Q) p q
            _ = responseJObservableCubeSet Q p q (rescaleCoeffField k a) := by
                  rw [← responseJ_cubeSet_eq_openCubeSet_of_triadicCube Q p q
                    (rescaleCoeffField k a)]
                  rfl
    _ = Ch02.responseJ (Ch02.cubeDomain Q) (B.coeffOn Q) p q := hAEEq
    _ = Ch02.responseJ (Ch02.cubeDomain Qsrc) (F.coeffOn Qsrc) p q := hdilate'
    _ = responseJObservableCubeSet Qsrc p q a := by
          calc
            Ch02.responseJ (Ch02.cubeDomain Qsrc) (F.coeffOn Qsrc) p q =
                ResponseJ (openCubeSet Qsrc) p q a := by
                  simpa [F, Qsrc, triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
                    coeffOnOfAEEllipticOn_toCoeffField, Ch02.cubeDomain_coe] using
                    Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ
                      (Ch02.cubeDomain Qsrc) (F.coeffOn Qsrc) p q
            _ = responseJObservableCubeSet Qsrc p q a := by
                  rw [← responseJ_cubeSet_eq_openCubeSet_of_triadicCube Qsrc p q a]
                  rfl

/-- Scalar response observables under the dilation defining
`scaleNormalizedLaw`, for arbitrary triadic cubes. -/
theorem responseJObservableCubeSet_dilateCoeffField_neg_nat_of_aelocallyUniformlyElliptic
    {d : ℕ} [NeZero d] {a : CoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (k : ℕ)
    (Q : TriadicCube d) (p q : Vec d) :
    responseJObservableCubeSet Q p q (Ch02.dilateCoeffField (-(k : ℤ)) a) =
      responseJObservableCubeSet (Ch02.dilateCube (k : ℤ) Q) p q a := by
  rw [← rescaleCoeffField_eq_dilateCoeffField_neg_nat]
  exact responseJObservableCubeSet_rescaleCoeffField_of_aelocallyUniformlyElliptic
    ha k Q p q

end

end Ch04
end Book
end Homogenization
