import SubdiffusiveProcess.Main.DiffusionPath
import SubdiffusiveProcess.Main.BilateralField
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Kernel.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

open SubdiffusiveProcess

namespace Paper



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
        = Measure.pi (fun i : Fin k => Measure.pi (fun j : Fin d =>
            ProbabilityTheory.gaussianReal 0 (2 * (t i.succ - t i.castSucc)))))

end Paper
