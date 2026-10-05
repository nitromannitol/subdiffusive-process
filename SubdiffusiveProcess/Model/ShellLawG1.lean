module

public import SubdiffusiveProcess.Assumptions.Actions
public import SubdiffusiveProcess.Model.LocalSigma
public import SubdiffusiveProcess.Model.ZeroPotentialLaw
public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-!
# Assumption (g1)
-/

open Homogenization MeasureTheory ProbabilityTheory

/-- Mean zero, stationarity, and range-one dependence of the unit-scale
potential, assumption (g1), paper label `a.g1`. -/
structure SubdiffusiveProcess.Model.ShellLawG1 (d : ℕ)
    (P : ProbabilityMeasure (_root_.SubdiffusiveProcess.Model.PotentialSample d)) : Prop where
  integrable : ∀ x : Vec d,
    Integrable (fun ω : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ ω 0 x) P.toMeasure
  mean_zero : ∀ x : Vec d,
    ∫ ω : _root_.SubdiffusiveProcess.Model.PotentialSample d, ω 0 x ∂P.toMeasure = 0
  stationary : ∀ z : Vec d,
    Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.translate z)
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw P).toMeasure =
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw P).toMeasure
  range_dependence : ∀ (U V : Set (Vec d)),
    MeasurableSet U → MeasurableSet V →
      (∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V →
        Real.sqrt (d : ℝ) ≤ euclideanNorm (x - y)) →
      Indep (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma U)
        (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma V)
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw P).toMeasure
