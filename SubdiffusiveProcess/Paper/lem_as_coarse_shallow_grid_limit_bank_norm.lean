module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper

/-- Uniform finite-response moments pass to a limit in measure. -/
theorem lem_as_coarse_shallow_grid_limit_bank_norm
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p C : ℝ≥0∞) (hC : C < ∞)
    (R : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hRmeas : ∀ N, AEStronglyMeasurable (R N) P)
    (hRbound : ∀ N, eLpNorm (R N) p P ≤ C)
    (hconv : TendstoInMeasure P R atTop Z) :
    MemLp Z p P ∧ eLpNorm Z p P ≤ C := by
  have hZbound : eLpNorm Z p P ≤ C :=
    eLpNorm_le_of_tendstoInMeasure (Filter.Eventually.of_forall hRbound)
      hconv hRmeas
  have hZmeas : AEStronglyMeasurable Z P :=
    hconv.aestronglyMeasurable hRmeas
  exact ⟨lt_of_le_of_lt hZbound hC, hZbound⟩

end Paper

