module

public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.DirichletForm.FOTProduct

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- FOT Theorem 1.4.1: on a Dirichlet form (a closed symmetric form on which the unit contraction
operates) every normal contraction operates: for `u ∈ D(E)` and `T` a normal contraction, `T ∘ u ∈ D(E)`
and `E(T∘u) ≤ E(u)`.  PROVED from the library theorem `SubdiffusiveProcess.DirichletForm.hasNormalContractions`
(`SubdiffusiveProcess/SubdiffusiveProcess.DirichletForm/FOTProduct.lean`, the Lipschitz calculus of a Dirichlet form). -/
theorem inputs_classical_fot_normal_contractions {X : Type*} [MeasurableSpace X]
    (m : Measure X) (E : _root_.SubdiffusiveProcess.DirichletForm m) :
    _root_.SubdiffusiveProcess.DirichletForm.HasNormalContractions E := by
  exact _root_.SubdiffusiveProcess.DirichletForm.hasNormalContractions E

end SubdiffusiveProcess.Paper

