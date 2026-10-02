import SubdiffusiveProcess.Lane4.Carriers

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



def lane4_smoothed_neumann_load {d : ℕ} (p : SpatialCoordinates d) (rho : ℝ → ℝ)
    (eps : ℝ) : SpatialCoordinates d → ℝ :=
  fun x => ∑ i : Fin d, p i * (eps⁻¹ * rho ((1 - x i) / eps) - eps⁻¹ * rho (x i / eps))

end Paper
