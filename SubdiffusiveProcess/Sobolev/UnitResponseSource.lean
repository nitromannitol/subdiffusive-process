module

public import SubdiffusiveProcess.Sobolev.NativeRepresentativeData
public import SubdiffusiveProcess.Sobolev.ResponseMomentBounds
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section

/-! A fixed nonzero smooth interior source on the unit cube.
This choice is deterministic and makes no assertion about random coefficients. -/

open MeasureTheory Set TopologicalSpace Homogenization
open scoped Distributions ContDiff

namespace SubdiffusiveProcess
noncomputable section

/-- A smooth cutoff supported strictly inside the unit cube. -/
def unitResponseBump (d : ℕ) : ContDiffBump (0 : SpatialCoordinates d) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- The fixed unit-cube smooth test associated with the interior cutoff. -/
def unitResponseTest (d : ℕ) :
    𝓓(centeredCube (0 : SpatialCoordinates d) 1 one_pos, ℝ) :=
  ⟨unitResponseBump d, (unitResponseBump d).contDiff,
    (unitResponseBump d).hasCompactSupport, by
      rw [(unitResponseBump d).tsupport_eq]
      exact Metric.closedBall_subset_ball (by norm_num [unitResponseBump])⟩

/-- The fixed test has value one at the origin. -/
theorem unitResponseTest_zero (d : ℕ) : unitResponseTest d 0 = 1 := by
  exact (unitResponseBump d).one_of_mem_closedBall
    (Metric.mem_closedBall_self (by norm_num [unitResponseBump]))

/-- The fixed source is nonzero as a Lebesgue L² class. -/
theorem unitResponseTest_l2_ne_zero (d : ℕ) : testL2 (unitResponseTest d) ≠ 0 := by
  intro hzero
  have hae : (unitResponseTest d : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d))] (fun _ => 0) := by
    have h := (testL2_coeFn (unitResponseTest d)).symm
    rw [hzero] at h
    exact h.trans (Lp.coeFn_zero _ _ _)
  have heq := Measure.eqOn_of_ae_eq hae
    (unitResponseTest d).contDiff.continuous.continuousOn continuousOn_const
    (by rw [(centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen.interior_eq]; exact subset_closure)
  have h := heq (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))
  rw [unitResponseTest_zero] at h
  exact one_ne_zero h

/-- The fixed test has native H¹ data with its literal smooth representative. -/
theorem exists_unitResponse_native (d : ℕ) :
    ∃ phi : H1Function (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)),
      phi.toFun = unitResponseTest d ∧
      (sobolevDataOfH1 phi).1 = testL2 (unitResponseTest d) := by
  let u := smoothSobolevData (unitResponseTest d)
  obtain ⟨phi, hphi, hdata⟩ := exists_nativeH1Function_of_ae_representative
    ⟨u, smoothSobolevData_mem (unitResponseTest d)⟩
    (unitResponseTest d) (testL2_coeFn (unitResponseTest d))
  exact ⟨phi, hphi, congrArg Prod.fst hdata⟩

end
end SubdiffusiveProcess
