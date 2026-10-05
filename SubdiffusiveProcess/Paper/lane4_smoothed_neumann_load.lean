module

public import SubdiffusiveProcess.EllipticRegularity.Carriers

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



def lane4_smoothed_neumann_load {d : ℕ} (p : SpatialCoordinates d) (rho : ℝ → ℝ)
    (eps : ℝ) : SpatialCoordinates d → ℝ :=
  fun x => ∑ i : Fin d, p i * (eps⁻¹ * rho ((1 - x i) / eps) - eps⁻¹ * rho (x i / eps))

end SubdiffusiveProcess.Paper
