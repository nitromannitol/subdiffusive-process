module

public import SubdiffusiveProcess.EllipticRegularity.CubeDilation

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



theorem lane4_cube_volume_scaling :
  ∀ (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
    volume (centeredCube z r hr : Set (SpatialCoordinates d)) =
      ENNReal.ofReal (r ^ d) := by
  intro d z r hr
  rw [centeredCube_eq_pi z hr, volume_pi_pi]
  have hint : ∀ i : Fin d,
      volume (Set.Ioo (z i - r / 2) (z i + r / 2)) = ENNReal.ofReal r := by
    intro i
    rw [Real.volume_Ioo]
    ring_nf
  simp only [hint, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow hr.le]

end SubdiffusiveProcess.Paper
