module

public import SubdiffusiveProcess.Lane2.OddExtension
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal Topology Distributions ContDiff

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ}

/-- **Almost-everywhere oddness becomes pointwise for a continuous
representative**, and therefore forces the value zero at every point fixed by
the reflection.  This is the paper's "its almost-everywhere oddness is then
pointwise, so it vanishes on every active face"
(`eq:mfd-18`). -/
theorem lane2_eq_zero_of_ae_odd_of_continuousOn
    {S : Set (SpatialCoordinates d)} (hS : IsOpen S)
    (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hsymm : Set.MapsTo (coordinateReflection z I) S S)
    {g : SpatialCoordinates d → ℝ} (hg : ContinuousOn g S)
    (hodd : ∀ᵐ x ∂(volume.restrict S),
      g (coordinateReflection z I x) = -g x)
    {x : SpatialCoordinates d} (hx : x ∈ S)
    (hfix : coordinateReflection z I x = x) : g x = 0 := by
  have hcont1 : ContinuousOn (fun y => g (coordinateReflection z I y)) S :=
    hg.comp ((coordinateReflection_isometry z I).continuous.continuousOn) hsymm
  have hcont2 : ContinuousOn (fun y => -g y) S := hg.neg
  have hU : S ⊆ closure (interior S) := by
    rw [hS.interior_eq]
    exact subset_closure
  have heq : Set.EqOn (fun y => g (coordinateReflection z I y)) (fun y => -g y) S :=
    MeasureTheory.Measure.eqOn_of_ae_eq hodd hcont1 hcont2 hU
  have hval := heq hx
  simp only [hfix] at hval
  linarith

/-- A point of the window lying on every active reflection plane is fixed by the
reflection, so a continuous almost-everywhere odd representative vanishes there.
The active planes are `{x : x i = z i}` for `i ∈ I`. -/
theorem lane2_eq_zero_on_activeFaces
    {S : Set (SpatialCoordinates d)} (hS : IsOpen S)
    (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hsymm : Set.MapsTo (coordinateReflection z I) S S)
    {g : SpatialCoordinates d → ℝ} (hg : ContinuousOn g S)
    (hodd : ∀ᵐ x ∂(volume.restrict S),
      g (coordinateReflection z I x) = -g x)
    {x : SpatialCoordinates d} (hx : x ∈ S)
    (hface : ∀ i ∈ I, x i = z i) : g x = 0 := by
  refine lane2_eq_zero_of_ae_odd_of_continuousOn hS z I hsymm hg hodd hx ?_
  funext i
  simp only [coordinateReflection]
  split_ifs with hi
  · rw [hface i hi]; ring
  · rfl

/-- The alternating multi-face odd extension is a finite signed sum of zero
extensions of reflected data; each summand is weakly Sobolev by
`lane2_zeroExtensionSobolevData_mem_weak_of_killed` together with
`reflectionSobolevData_mem_killed`, so the sum is.  This is the algebraic half of
the multi-face composition: only the geometry of the `2 ^ |I|` pieces remains. -/
theorem lane2_sum_mem_weakSobolevGraph {U : Opens (SpatialCoordinates d)}
    {ι : Type*} [DecidableEq ι] (T : Finset ι) (c : ι → ℝ)
    (w : ι → SobolevData U) (hw : ∀ j ∈ T, w j ∈ weakSobolevGraph U) :
    (∑ j ∈ T, c j • w j) ∈ weakSobolevGraph U :=
  Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (hw j hj)

/-- One piece of the multi-face composition: the zero extension of the datum
pulled back by the reflection in a subset `J` of the active coordinates is weakly
Sobolev on the window, for a killed datum. -/
theorem lane2_reflectedPiece_mem_weak {U W V : Opens (SpatialCoordinates d)}
    (z : SpatialCoordinates d) (J : Finset (Fin d))
    (hpre : coordinateReflection z J ⁻¹' (W : Set (SpatialCoordinates d)) =
      (V : Set (SpatialCoordinates d)))
    (hle : V ≤ U) {u : SobolevData W} (hu : u ∈ killedSobolevGraph W) :
    zeroExtensionSobolevData hle (reflectionSobolevData z J hpre u) ∈
      weakSobolevGraph U :=
  lane2_zeroExtensionSobolevData_mem_weak_of_killed hle
    (reflectionSobolevData_mem_killed z J hpre hu)

end SubdiffusiveProcess
