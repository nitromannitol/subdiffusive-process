module

public import SubdiffusiveProcess.Assumptions.Actions
public import SubdiffusiveProcess.Frozen.Assumptions.LocalSigma
public import SubdiffusiveProcess.Frozen.Assumptions.ZeroPotentialLaw
public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-!
# Assumption (g1)
-/

open Homogenization MeasureTheory ProbabilityTheory




structure SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 (d : ℕ)
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) : Prop where
  integrable : ∀ x : Vec d,
    Integrable (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d ↦ ω 0 x) P.toMeasure
  mean_zero : ∀ x : Vec d,
    ∫ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d, ω 0 x ∂P.toMeasure = 0
  stationary : ∀ z : Vec d,
    Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z)
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).toMeasure =
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).toMeasure
  range_dependence : ∀ (U V : Set (Vec d)),
    MeasurableSet U → MeasurableSet V →
      (∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V →
        Real.sqrt (d : ℝ) ≤ euclideanNorm (x - y)) →
      Indep (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U)
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma V)
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).toMeasure

