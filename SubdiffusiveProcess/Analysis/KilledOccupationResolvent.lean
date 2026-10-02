import SubdiffusiveProcess.Main.DiffusionPath
import SubdiffusiveProcess.Main.BilateralField
import SubdiffusiveProcess.Main.ChaosSampleLaw
import MarkovProcess.Path.ExitTime
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-! Actual finite-cutoff killed occupation resolvents, with their source data
kept explicit. No variational identification or convergence input is contained
in this definition. -/
open MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Analysis

/-- Integrate the discounted source until the path first leaves the open set. -/
def killedOccupationResolvent {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Q : Set (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (N : ℕ) (omega : BilateralField d) (lam : ℝ)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (x : SpatialCoordinates d) : ℝ :=
  ∫ path, (∫ t in Set.Ioi (0 : ℝ),
    Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q path}
      (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
    ∂(KN N (omega, x))

end SubdiffusiveProcess.Analysis
