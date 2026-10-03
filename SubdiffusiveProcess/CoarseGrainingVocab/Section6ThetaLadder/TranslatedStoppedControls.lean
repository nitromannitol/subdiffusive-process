module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.TranslatedStoppingEvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.GoodEvent

@[expose] public section

/-!
# Theta-perturbed ladder: translated stopped good-scale controls

The combined finite-cutoff stopping depth is uniform over all grid centers in
the parent cube.  On the translated stopping event, its good-density half
therefore bounds the exact finite-cutoff failure row at every physical center
`z + q`, with `q` a grid center in the origin-centered parent.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The good-density half of the stopped controls at a translated physical
center. -/
theorem translatedThetaLadder_stopped_goodFailure
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (C1 C2 : ℝ) (step m n j0 : ℕ) (z : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hstop : omega ∈
      translatedThetaLadderStoppingEvent M L C1 C2 step m j0 z)
    (hj0 : j0 ≤ m - n) (q : Vec d)
    (hqgrid : OnTriadicGrid n q) (hqmem : q ∈ cube d m) :
    (∑ i ∈ Finset.Icc n m,
        ((1 : ℝ) - if omega ∈ goodEvent M (some L) i (z + q)
          (Section6Stopping.holderStoppingEpsilon C2 thetaLadderExponent)
          Section6Stopping.holderStoppingS then 1 else 0)) <
      1 + Section6Stopping.holderStoppingLambda C1 thetaLadderExponent *
        ((m : ℝ) - (n : ℝ)) := by
  have hdepthNat : thetaLadderStoppingScale M L C1 C2 step m
      (translatePotentialSample z omega) ≤ m - n :=
    hstop.trans hj0
  have hdepthPos : 0 < thetaLadderStoppingScale M L C1 C2 step m
      (translatePotentialSample z omega) :=
    by
      exact Section6Stopping.measurableCutoffHolderStoppingScale_pos
        M L thetaLadderExponent
        (Section6Stopping.holderStoppingLambda C1 thetaLadderExponent)
        (Section6Stopping.holderStoppingEpsilon C2 thetaLadderExponent)
        step m (translatePotentialSample z omega)
  have hnm : n ≤ m := by omega
  have hdepthInt :
      (thetaLadderStoppingScale M L C1 C2 step m
          (translatePotentialSample z omega) : ℤ) ≤
        (m : ℤ) - (n : ℤ) := by
    rw [← Int.ofNat_sub hnm]
    exact_mod_cast hdepthNat
  have hcontrols :=
    Section6Stopping.measurableCutoffHolder_stopped_controls_at_parameters
      M L C1 C2 thetaLadderExponent step m n
      (translatePotentialSample z omega) hdepthInt q hqgrid hqmem
  have hgood := hcontrols.2
  simpa only [Section6Covariance.mem_goodEvent_translatePotentialSample] using hgood

/-- The same stopped bound on any initial subinterval ending below the parent
scale. -/
theorem translatedThetaLadder_stopped_goodFailure_interval
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (C1 C2 : ℝ) (step m n top j0 : ℕ) (z : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hstop : omega ∈
      translatedThetaLadderStoppingEvent M L C1 C2 step m j0 z)
    (hj0 : j0 ≤ m - n) (htop : top ≤ m) (q : Vec d)
    (hqgrid : OnTriadicGrid n q) (hqmem : q ∈ cube d m) :
    (∑ i ∈ Finset.Icc n top,
        ((1 : ℝ) - if omega ∈ goodEvent M (some L) i (z + q)
          (Section6Stopping.holderStoppingEpsilon C2 thetaLadderExponent)
          Section6Stopping.holderStoppingS then 1 else 0)) <
      1 + Section6Stopping.holderStoppingLambda C1 thetaLadderExponent *
        ((m : ℝ) - (n : ℝ)) := by
  have hfull := translatedThetaLadder_stopped_goodFailure
    M L C1 C2 step m n j0 z omega hstop hj0 q hqgrid hqmem
  have hsub : Finset.Icc n top ⊆ Finset.Icc n m := by
    intro i hi
    exact Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hi).1,
      (Finset.mem_Icc.1 hi).2.trans htop⟩
  have hle :
      (∑ i ∈ Finset.Icc n top,
          ((1 : ℝ) - if omega ∈ goodEvent M (some L) i (z + q)
            (Section6Stopping.holderStoppingEpsilon C2 thetaLadderExponent)
            Section6Stopping.holderStoppingS then 1 else 0)) ≤
        ∑ i ∈ Finset.Icc n m,
          ((1 : ℝ) - if omega ∈ goodEvent M (some L) i (z + q)
            (Section6Stopping.holderStoppingEpsilon C2 thetaLadderExponent)
            Section6Stopping.holderStoppingS then 1 else 0) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro i _ _
      split_ifs <;> norm_num)
  exact hle.trans_lt hfull

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
