module

public import SubdiffusiveProcess.Main.DiffusionPath
public import SubdiffusiveProcess.Main.BilateralField
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Kernel.Basic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

open SubdiffusiveProcess

namespace SubdiffusiveProcess.Paper



def in_brownian_normalization {d : ℕ}
    (B : Kernel (SpatialCoordinates d) (DiffusionPath d)) : Prop :=
  IsMarkovKernel B ∧
    (∀ x : SpatialCoordinates d,
      Measure.map (fun path : DiffusionPath d => path 0) (B x) = Measure.dirac x) ∧
    (∀ x : SpatialCoordinates d, ∀ k : ℕ, ∀ t : Fin (k + 1) → ℝ≥0, Monotone t →
      Measure.map
          (fun path : DiffusionPath d => fun i : Fin k => fun j : Fin d =>
            (path (t i.succ)) j - (path (t i.castSucc)) j)
          (B x)
        = Measure.pi (fun i : Fin k => Measure.pi (fun _j : Fin d =>
            ProbabilityTheory.gaussianReal 0 (2 * (t i.succ - t i.castSucc)))))

end SubdiffusiveProcess.Paper
