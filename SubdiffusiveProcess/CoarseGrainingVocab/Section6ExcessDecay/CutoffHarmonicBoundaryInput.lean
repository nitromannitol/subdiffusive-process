
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.BelowCutoffInputs
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicComparisonCollapse
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicStepRowWindowStep
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior.WellPosed

@[expose] public section

/-!
# The boundary harmonic-approximation input at a finite cutoff

This module closes
`Section6ExcessDecay.BoundaryCutoffHarmonicApproximationInputV6`, the proved
harmonic v6 statement with exactly the two source-prescribed changes of

1. the premise `m ≤ L` is deleted;
2. `goodEvent M none (n+2) z 1 (s/8)` is replaced by
   `goodEvent M (some L) (n+2) z 1 (s/8)`.

The manuscript asks for the harmonic argument  to be re-run with
the cutoff response `G^{(L)}` and the cutoff event `𝒢^{(L)}`.  That is exactly
what `SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic` does: every declaration of
the committed boundary chain whose *statement* mentions the good event has a
companion there carrying `𝒢^{(L)}` and no relation between `L` and the scale,
and every deterministic ingredient is quoted from the committed chain unchanged.

Clauses (A) and (B) — existence and a.e. uniqueness of the constant-coefficient
harmonic replacement — mention neither the coefficient nor the event, and are
the unconditional `Section6HarmonicInterior.interiorHarmonic_wellPosed`, exactly
as in the uncut assembly `Section6HarmonicBoundary.FrozenAssembly`.


-/

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section
attribute [local instance] Classical.propDecidable

/-- **The boundary harmonic-approximation clause on the finite-cutoff good
event.**  This is `SubdiffusiveProcess.Frozen.Section6.harmonic_approximation_good_scales` with
the premise `m ≤ L` deleted and the good event replaced by `𝒢^{(L)}`. -/
theorem boundaryCutoffHarmonicApproximationInputV6 (d : ℕ) [NeZero d] :
    BoundaryCutoffHarmonicApproximationInputV6 d := by
  obtain ⟨Cbd, hCbd, hbrow⟩ :=
    Section6CutoffHarmonic.exists_boundaryStepCellParentRow d
  obtain ⟨Cb, hCb, hrow⟩ :=
    Section6CutoffHarmonic.exists_boundaryCellManuscriptRow_of_boundaryStepCellParentRow
      d hCbd hbrow
  obtain ⟨C, hC0, hmain⟩ :=
    Section6CutoffHarmonic.harmonicComparisonClauseV6_of_cellRow d hCb hrow
  refine ⟨C, hC0, ?_⟩
  intro M s hs L m n hnm z hz x hx ω u h g hdir hgex hh y hy hcov hloc uD
    hfval hfgrad
  exact ⟨(Section6HarmonicInterior.interiorHarmonic_wellPosed d n y uD).1,
    (Section6HarmonicInterior.interiorHarmonic_wellPosed d n y uD).2,
    hmain M s hs L m n hnm z hz x hx ω u h g hdir hgex hh y hy hcov hloc uD
      hfval hfgrad⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
