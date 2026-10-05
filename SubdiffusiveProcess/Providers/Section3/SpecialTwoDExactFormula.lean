module

public import SubdiffusiveProcess.CoarseGrainingVocab.DykhneStationaryLimit
public import SubdiffusiveProcess.CoarseGrainingVocab.PlanarStreamFunction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitGridMaximum

@[expose] public section

/-!
# Provider: the two-dimensional exact formula

Assembles `p.special.two.d.exact.formula` from the stationary planar
duality identity, the planar zero-normal stream-function theorem, and
positivity of the homogenized coefficient.
-/

open SubdiffusiveProcess.CoarseGrainingVocab

theorem SubdiffusiveProcess.Providers.Section3.special_two_d_exact_formula
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) :
    ahom M m =
      Real.exp (-(m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) :=
  ahom_eq_planarLambda_of_streamFunction M m
    (fun n => planarZeroNormalStreamFunctionOn_openCubeSet_originCube n)
    (ahom_pos M m)
