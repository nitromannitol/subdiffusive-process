module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.CutoffHolderScale

@[expose] public section

/-!
# Boundary Hölder below the cutoff: stopped carrier

The manuscript's `L < m` branch uses the cutoff good events and the cutoff
stopping scale.  This file fixes that carrier once, before any row assembly.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.BelowCutoff

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The stopping carrier used by every datum-bearing below-cutoff row. -/
abbrev boundaryCutoffStoppingScale {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (alpha C1 C2 : ℝ)
    (step m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℕ :=
  Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
    (Section6Stopping.holderStoppingLambda C1 alpha)
    (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega

/-- Both stopped rows at the literal cutoff carrier. -/
theorem boundaryCutoff_stopped_controls {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (C1 C2 alpha : ℝ) (step m n : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hn : (boundaryCutoffStoppingScale M L alpha C1 C2 step m omega : ℤ) ≤
      (m : ℤ) - (n : ℤ)) (z : Vec d) (hzgrid : OnTriadicGrid n z)
    (hzmem : z ∈ cube d m) :
    (∑ j ∈ Finset.Icc n m,
        accumulatedError M (some L) j z Section6Stopping.holderStoppingS omega) ≤
        Section6Stopping.holderStoppingLambda C1 alpha * ((m : ℝ) - (n : ℝ)) ∧
      (∑ j ∈ Finset.Icc n m,
          (1 - if omega ∈ goodEvent M (some L) j z
            (Section6Stopping.holderStoppingEpsilon C2 alpha)
            Section6Stopping.holderStoppingS then 1 else 0)) <
        1 + Section6Stopping.holderStoppingLambda C1 alpha *
          ((m : ℝ) - (n : ℝ)) := by
  exact Section6Stopping.measurableCutoffHolder_stopped_controls_at_parameters
    M L C1 C2 alpha step m n omega hn z hzgrid hzmem

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.BelowCutoff
