import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Paper.lem_19_interpolation_upgrade

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
noncomputable section
namespace Paper

/-- Three-quarter classes on every centred cube have a half-order lift. -/
theorem aux_mfd_prop_uniform_resolvent_half_lift {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (v : CubeFractionalL2 (k := 1) hd z r hr threeQuarterOrder) :
    ∃ w : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder,
      w.val 0 = v.val 0 := by
  exact ⟨⟨v.val, aux_lem_19_interpolation_upgrade_half_mem d hd z r hr v.val v.property⟩, rfl⟩

end Paper
