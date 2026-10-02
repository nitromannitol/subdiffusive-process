import SubdiffusiveProcess.Frozen.Section6.DensityOfGoodScales

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Paper



theorem p_density_of_good_scales
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s theta epsilon : ℝ,
      s ∈ Set.Ioc 0 1 → theta ∈ Set.Ioc 0 1 → epsilon ∈ Set.Ioc 0 1 →
      C * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 * |Real.log M.delta| ≤ theta →
      ∀ m0 K : ℕ,
        M.P.toMeasure {ω | (∑ m ∈ Finset.Icc m0 (m0 + K),
            if ω ∈ goodEvent M none m 0 epsilon s then (1 : ℝ) else 0) /
              (K + 1) ≤ 1 - theta} ≤
          ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * theta /
            (C * M.delta ^ 2 * |Real.log M.delta|)) * (K + 1))) :=
  SubdiffusiveProcess.Frozen.Section6.density_of_good_scales d

end Paper
