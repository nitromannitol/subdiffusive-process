module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.RatioAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder.GoodScaleSuffix
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.GoodScaleSuffix
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffBRatio
public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments

@[expose] public section

/-!
# Hölder Step 3: the stopped coefficient-ratio display, at the cutoff carrier

This is the deterministic content of `e.ratio.of.bs` with the binder `m ≤ L`
removed, i.e. the manuscript's `e.cutoff.Holder.b.ratio`
The mathematics lives in
`Section6HolderBelowCutoff.CutoffBRatio`, which splits the three regimes
`L ≤ q` (both factors saturated), `m ≤ L` (the uncut estimate, through the
carrier transports of `StoppingSaturation`) and `q ≤ L ≤ m` (only the layers
`q+1, …, L` occur).  This module is the row-facing name.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder

open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable


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
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L n q m : ℕ}
    (hnm : n < m) (hnq : n ≤ q) (hqm : q ≤ m)     (epsilon s lambda : ℝ) (hepsilon : 0 ≤ epsilon) (hs : s ≤ 1 / 2)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (hdelta : M.delta ^ 2 ≤ lambda) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z : Vec d)
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
