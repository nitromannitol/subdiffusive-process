import Mathlib
import SubdiffusiveProcess.Paper.aux_macro_energy_recurrence
import SubdiffusiveProcess.Paper.aux_macro_moment_bank
import SubdiffusiveProcess.Paper.in_6_16

/-! Stage 3 (calibration): the random prefix length at frame `N + j`, FE level `N`, has the geometric tail of `Sreg.tail`
(arbitrary levels and scales), uniformly in `N`.  Analogue of `aux_prop_growth_trunc_macro_energy_prefix_fixed`. -/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem calib3_prefix {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M) (alpha κ : ℝ)
    (hδC : M.delta ≤ Sreg.C⁻¹) (hα : alpha ∈ Sreg.alphaRange)
    (hκ : κ = (1 - alpha) ^ 2 / (Sreg.C * M.delta ^ 2 * |Real.log M.delta|))
    (hκ0 : 0 < κ) (z : SpatialCoordinates d) (j : ℕ) :
    ∃ Lmac : ℕ → BilateralField d → ℕ,
      (∀ N, Measurable (Lmac N)) ∧
      (∀ N k : ℕ, (chaosSampleLaw M).toMeasure {om | k < Lmac N om} ≤
        ENNReal.ofReal (Sreg.C * Real.exp (κ * Sreg.C) * Real.exp (-κ * k))) ∧
      (∀ om, ∀ N : ℕ, Sreg.prefixLen N alpha (N + j) ((3 : ℝ) ^ (N + j) • z)
        (aux_aux_macro_energy_recurrence_relabel (N + j) om) ≤ Lmac N om) := by
  refine ⟨fun N om => Sreg.prefixLen N alpha (N + j) ((3 : ℝ) ^ (N + j) • z)
    (aux_aux_macro_energy_recurrence_relabel (N + j) om), fun N => (Sreg.prefix_measurable _ _ _ _).comp
    (aux_aux_macro_moment_bank_relabel_measurePreserving M (N + j)).measurable, ?_,
    fun om N => le_rfl⟩
  intro N k
  have hpres := aux_aux_macro_moment_bank_relabel_measurePreserving M (N + j)
  have hset : {om | k < Sreg.prefixLen N alpha (N + j) ((3 : ℝ) ^ (N + j) • z)
      (aux_aux_macro_energy_recurrence_relabel (N + j) om)} = aux_aux_macro_moment_bank_relabel (N + j) ⁻¹'
      {om | k < Sreg.prefixLen N alpha (N + j) ((3 : ℝ) ^ (N + j) • z) om} := rfl
  rw [hset, hpres.measure_preimage
    (measurableSet_lt measurable_const (Sreg.prefix_measurable _ _ _ _)).nullMeasurableSet]
  exact aux_aux_macro_moment_bank_tail_geometric M Sreg alpha κ hδC hα hκ hκ0.le _ _ _ k

end Paper
