module

public import SubdiffusiveProcess.Variational.DualEnergy
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.DirichletForm.All
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology

namespace Paper

/-- Every genuine finite dual-energy form on a nonempty cube has a positive
finite-energy element. Density excludes the zero vector as the whole domain;
the operator-norm dual estimate makes that element's energy positive. -/
theorem thm_c1_cube_positive_energy {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (E : DirichletForm.ClosedForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u) :
    ∃ u : DomainL2 (centeredCube z r hr),
      u ∈ limitFormDomain G ∧ 0 < (limitFormEnergy G u).toReal := by
  let μ := volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
  haveI : IsFiniteMeasure μ := inferInstance
  have hmass : 0 < μ.real Set.univ := by
    simpa only [μ, measureReal_def, Measure.restrict_apply_univ] using
      centeredCube_volume_pos z hr
  have hone : Lp.const 2 μ (1 : ℝ) ≠ 0 := by
    apply norm_pos_iff.mp
    rw [Lp.norm_const' 2 μ (1 : ℝ) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hmass _)
  obtain ⟨u, hu, hune⟩ := E.denseDomain.exists_mem_open
    (isClosed_singleton.isOpen_compl : IsOpen ({0}ᶜ : Set (DomainL2 (centeredCube z r hr))))
    ⟨Lp.const 2 μ 1, hone⟩
  have henergy : limitFormEnergy G u = (E.form u u : EReal) := by
    rw [← hE u, E.energy_of_mem hu]
  have hnorm := norm_sq_le_operatorNorm_mul_quadraticDual G u (E.form u u) henergy
  have hpositive : 0 < E.form u u := by
    have hnormpos : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hune)
    have hmulpos := lt_of_lt_of_le hnormpos hnorm
    exact pos_of_mul_pos_right hmulpos (norm_nonneg G)
  refine ⟨u, ?_, ?_⟩
  · change limitFormEnergy G u < ⊤
    rw [henergy]
    exact EReal.coe_lt_top _
  · rwa [henergy, EReal.toReal_coe]

/-- The name under which the lemma was first stated inside `thm_c1`. -/
theorem aux_thm_c1_cube_positive_energy {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (E : DirichletForm.ClosedForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u) :
    ∃ u : DomainL2 (centeredCube z r hr),
      u ∈ limitFormDomain G ∧ 0 < (limitFormEnergy G u).toReal :=
  thm_c1_cube_positive_energy z r hr G E hE

end Paper
