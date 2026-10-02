import SubdiffusiveProcess.MeyersRegularity.Scaling

/-! Interior Meyers regularity: Final. -/

open MeasureTheory Filter Set TopologicalSpace
open Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators

noncomputable section
namespace SubdiffusiveProcess.MeyersRegularity

theorem exists_meyers_estimate (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ epsilon C : ℝ, 0 < epsilon ∧ 0 < C ∧ Meyers.MeyersEstimate d p epsilon C := by
  obtain ⟨epsilon, C, hε, _, hC, hunit⟩ := exists_unit_meyers_estimate d hd p hp
  exact ⟨epsilon, C, hε, hC, meyersEstimate_of_unit hd hp hunit⟩

end SubdiffusiveProcess.MeyersRegularity
