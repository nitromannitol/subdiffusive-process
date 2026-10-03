module

public import SubdiffusiveProcess.DirichletForm.FOTProduct
public import SubdiffusiveProcess.DirichletForm.EnergyMeasure

@[expose] public section

open MeasureTheory

namespace SubdiffusiveProcess.Section9

/-- The proved FOT product calculus supplies the core-algebra interface of a
regular Dirichlet form. No extra algebra-closure premise is needed. -/
theorem isCoreAlgebra_of_isRegular
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {mu : Measure X}
    (E : _root_.DirichletForm mu) (hE : _root_.DirichletForm.IsRegular E.toClosedForm) :
    _root_.DirichletForm.IsCoreAlgebra E.toClosedForm where
  isRegular := hE
  mul_mem := _root_.DirichletForm.mul_mem E
  comp_mem := _root_.DirichletForm.comp_mem E
  mul_comp_mem := _root_.DirichletForm.mul_comp_mem E
  mul_mem_of_bounded := _root_.DirichletForm.mul_mem_of_bounded E

end SubdiffusiveProcess.Section9
