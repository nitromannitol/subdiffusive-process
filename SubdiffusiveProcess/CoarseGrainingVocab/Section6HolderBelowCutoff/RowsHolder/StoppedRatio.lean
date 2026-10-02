import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.RatioAssembly
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder.GoodScaleSuffix
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.GoodScaleSuffix
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffBRatio
import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder

open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

private abbrev Sample_cut (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The explicit parent/shell budget has the manuscript's linear exponential
form.  This elementary collapse is uniform in the window length. -/
theorem stopped_ratio_budget_le_exp_cut {d : ℕ} {E s R : ℝ}
    (hE : 0 ≤ E) (hR : R ≤ E) :
    (1 + (d : ℝ) * E * Real.exp ((d : ℝ) * E)) ^ 2 *
        Real.exp (E / (3 : ℝ) ^ (-(s / 8)) + R) ≤
      Real.exp ((4 * (d : ℝ) + ((3 : ℝ) ^ (-(s / 8)))⁻¹ + 1) * E) :=
  Section6Holder.stopped_ratio_budget_le_exp hE hR

/-- `e.cutoff.Holder.b.ratio` in its final linear-in-window exponential form:
`e.ratio.of.bs` with **no relation between `m` and `L`**. -/
theorem stopped_tailAverage_ratio_bounds_exp_cut {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L n q m : ℕ}
    (hnm : n < m) (hnq : n ≤ q) (hqm : q ≤ m)     (epsilon s lambda : ℝ) (hepsilon : 0 ≤ epsilon) (hs : s ≤ 1 / 2)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (hdelta : M.delta ^ 2 ≤ lambda) (omega : Sample_cut d) (z : Vec d)
    (hz : z ∈ cube d m)
    (hsumZ : (∑ i ∈ Finset.Icc n m,
      accumulatedError M (some L) i z s omega) ≤
        lambda * ((m : ℝ) - (n : ℝ)))
    (hsum0 : (∑ i ∈ Finset.Icc n m,
      accumulatedError M (some L) i 0 s omega) ≤
        lambda * ((m : ℝ) - (n : ℝ)))
    (hbadZ : (∑ i ∈ Finset.Icc n m,
        (1 - if omega ∈ goodEvent M (some L) i z epsilon s then (1 : ℝ) else 0)) <
      1 + lambda * ((m : ℝ) - (n : ℝ)))
    (hbad0 : (∑ i ∈ Finset.Icc n m,
        (1 - if omega ∈ goodEvent M (some L) i 0 epsilon s then (1 : ℝ) else 0)) <
      1 + lambda * ((m : ℝ) - (n : ℝ))) :
    let C := 4 * (d : ℝ) + ((3 : ℝ) ^ (-(s / 8)))⁻¹ + 1
    tailAverage M L q omega (translatedCube d (q : ℤ) z) /
        tailCoefficientCubeAverage M L m omega ≤
          Real.exp (C * lambda * ((m : ℝ) - (n : ℝ))) ∧
      tailCoefficientCubeAverage M L m omega /
        tailAverage M L q omega (translatedCube d (q : ℤ) z) ≤
          Real.exp (C * lambda * ((m : ℝ) - (n : ℝ))) :=
  stopped_tailAverage_ratio_bounds_exp_cutoff M hnm hnq hqm epsilon s lambda
    hepsilon hs hlambda0 hlambda1 hdelta omega z hz hsumZ hsum0 hbadZ hbad0

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder
