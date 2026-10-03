module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.PointwiseBoundedness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.ResponseBudgetSplit

@[expose] public section

/-!
# Pointwise Section 6 response budget

This closes the boundedness guard in the committed sensitivity/localization
chain from membership in the first good-field event.  Unlike the parallel
almost-everywhere module, the result is valid for every sample in the frozen
good event.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization

open Homogenization Homogenization.Book

noncomputable section

variable {d : ℕ}

/-- Pointwise, guard-free form of the split response budget. -/
theorem weightedPaperScalarProbe_tailAverage_le_split_of_mem_goodEvent
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m n j : ℕ}
    (hnm : n ≤ m) (hmL : m ≤ L) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (hj : j ≤ m) (hnj : n + 2 ≤ j)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ))
    (hann : triadicCubeShift R ∈ cube d j \ cube d (j - 1))
    {e : Vec d} (he : vecNormSq e = 1)
    (hgood : omega ∈ goodEvent M none m 0 1 s) :
    (3 : ℝ) ^ (-(3 / 2) * (s * ((m - n : ℕ) : ℝ))) *
        paperScalarProbe (originCube d (n : ℤ))
          (aCutoffFamily M L
            (translatePotentialSample (triadicCubeShift R) omega))
          (tailCoefficientCubeAverage M L m omega) e ≤
      2 * (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
          section6Response M n n omega (triadicCubeShift R) e +
        36 * ratioCollapseConstant d ^ 2 *
          ((3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
              longRatioGradientTail m omega ^ 2 +
            (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
              supNormOn (cube d n)
                (shellBlock m n
                  (translatePotentialSample (triadicCubeShift R) omega)) ^ 2 +
            2 * (s⁻¹) ^ 2 * M.delta ^ 4) := by
  apply weightedPaperScalarProbe_tailAverage_le_split_of_goodEvent_descendant
    M hnm hmL hsLower hsUpper hj hnj omega hR hann he hgood
  exact bddAbove_goodFieldTwo_values_of_goodFieldOne
    m (m - n) zero_le_one hsUpper omega hgood.1

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
