module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.GoodEventDensity

@[expose] public section

/-!
# Conjunct (1) of `p.cutoff.regularity.good.scales`, in the shape

The finite-cutoff density estimate
`e.cutoff.regularity.density`  is proved in
`SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.exists_measure_cutoffGoodEvent_badDensity_le`
with the parameter block ordered `s theta epsilon`.  The anchor orders
it `s epsilon theta`.  This module records the ordering, so that the
provider consumes conjunct (1) with no reshaping at the assembly site.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Conjunct (1) of the finite-cutoff good-scale proposition, in the
binder order. -/
theorem exists_cutoff_regularity_density_clause (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ L : ℕ,
      ∀ s epsilon theta : ℝ, s ∈ Set.Ioc 0 1 → epsilon ∈ Set.Ioc 0 1 →
        theta ∈ Set.Ioc 0 1 →
        C * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 * |Real.log M.delta| ≤
            theta →
        ∀ m0 K : ℕ,
          M.P.toMeasure {omega | (∑ m ∈ Finset.Icc m0 (m0 + K),
              if omega ∈ goodEvent M (some L) m 0 epsilon s then (1 : ℝ)
                else 0) / (K + 1) ≤ 1 - theta} ≤
            ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * theta /
              (C * M.delta ^ 2 * |Real.log M.delta|)) * (K + 1))) := by
  obtain ⟨C, hC, hbound⟩ :=
    Section6Cutoff.exists_measure_cutoffGoodEvent_badDensity_le d
  exact ⟨C, hC, fun M L s epsilon theta hs hepsilon htheta hsmall m0 K =>
    hbound M L s theta epsilon hs htheta hepsilon hsmall m0 K⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
