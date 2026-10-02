/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.BelowCutoffInputs
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicComparisonCollapse
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicStepRowWindowStep
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior.WellPosed




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
