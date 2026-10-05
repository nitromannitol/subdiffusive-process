module

public import SubdiffusiveProcess.Paper.inputs_classical_e5_energy
public import SubdiffusiveProcess.EllipticRegularity.Carriers

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem inputs_EM_witness (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (F : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) :
    _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F := by
  exact ⟨inputs_classical_e5_energy d (centeredCube z r hr) F⟩

end SubdiffusiveProcess.Paper
