module

public import SubdiffusiveProcess.Paper.affine_source_cells_env

@[expose] public section




open Filter MeasureTheory Set SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped Topology ENNReal BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper
abbrev aux_cor_32_Cells (d H1 : ℕ) := Σ n : ℕ, Fin n → OddGridIndex d (subdivisionHalfWidth H1)
/-- The actual reference scalar: positive deterministic normalizer times the retained infrared weight. -/
def aux_cor_32_reference {d : ℕ}
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (eRef : ℕ → ℝ)
    (k : ℕ) (z : SpatialCoordinates d) (omega : BilateralField d) : ℝ :=
  eRef k * Real.exp (H omega z + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z)
end SubdiffusiveProcess.Paper
