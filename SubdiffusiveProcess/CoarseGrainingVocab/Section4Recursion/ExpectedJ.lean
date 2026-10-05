module

public import SubdiffusiveProcess.CoarseGrainingVocab.Induction

@[expose] public section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization.Book

noncomputable section




/-- Turn the literal expectation of a response difference into the difference
of the expected responses. -/
theorem expectedJDifference_eq_sub {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n m : ℕ) (p q : Vec d)
    (hn : Integrable (fun ω =>
      J (Ch02.cubeDomain (Homogenization.originCube d (n : ℤ)))
        ((aCutoffFamily M L ω).coeffOn
          (Homogenization.originCube d (n : ℤ))) p q) M.P.toMeasure)
    (hm : Integrable (fun ω =>
      J (Ch02.cubeDomain (Homogenization.originCube d (m : ℤ)))
        ((aCutoffFamily M L ω).coeffOn
          (Homogenization.originCube d (m : ℤ))) p q) M.P.toMeasure) :
    expectedJDifference M L n m p q =
      expectedJ M L n p q - expectedJ M L m p q := by
  unfold expectedJDifference expectedJ
  rw [integral_sub hn hm]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
