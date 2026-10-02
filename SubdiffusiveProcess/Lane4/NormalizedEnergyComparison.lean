import SubdiffusiveProcess.Lane3.LocalEnergyAux
import SubdiffusiveProcess.Lane4.Carriers
import Mathlib.Tactic

/-! # Comparison of normalized energies on nested sets -/

open MeasureTheory TopologicalSpace

noncomputable section

namespace SubdiffusiveProcess.Lane4

/-- Enlarging the averaging set controls normalized energy by the square root of
the volume ratio. -/
theorem normalizedEnergyNorm_le_sqrt_volume_ratio
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)} (a : PositiveCoefficient Ω)
    {s t : Set (SpatialCoordinates d)} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : s ⊆ t) (hvs : 0 < volume.real s) (hvt : 0 < volume.real t)
    (g : HilbertGradient Ω) :
    normalizedEnergyNorm a hs g ≤
      Real.sqrt (volume.real t / volume.real s) * normalizedEnergyNorm a ht g := by
  have he : localGradientEnergy a hs g ≤ localGradientEnergy a ht g :=
    Lane3.localGradientEnergy_mono a hs ht hst g
  have het : 0 ≤ localGradientEnergy a ht g :=
    localGradientEnergy_nonneg a ht g
  have hq : localGradientEnergy a hs g / volume.real s ≤
      (volume.real t / volume.real s) *
        (localGradientEnergy a ht g / volume.real t) := by
    have hr : (volume.real t / volume.real s) *
        (localGradientEnergy a ht g / volume.real t) =
          localGradientEnergy a ht g / volume.real s := by
      field_simp
    rw [hr]
    exact div_le_div_of_nonneg_right he hvs.le
  unfold normalizedEnergyNorm
  calc
    Real.sqrt (localGradientEnergy a hs g / volume.real s)
        ≤ Real.sqrt ((volume.real t / volume.real s) *
            (localGradientEnergy a ht g / volume.real t)) := Real.sqrt_le_sqrt hq
    _ = Real.sqrt (volume.real t / volume.real s) *
          Real.sqrt (localGradientEnergy a ht g / volume.real t) := by
          rw [Real.sqrt_mul (by positivity)]


end SubdiffusiveProcess.Lane4
