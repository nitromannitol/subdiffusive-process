module

public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.DirichletForm.FOTProduct

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem inputs_classical_fot_normal_contractions {X : Type*} [MeasurableSpace X]
    (m : Measure X) (E : _root_.DirichletForm m) :
    DirichletForm.HasNormalContractions E := by
  exact DirichletForm.hasNormalContractions E

end Paper

