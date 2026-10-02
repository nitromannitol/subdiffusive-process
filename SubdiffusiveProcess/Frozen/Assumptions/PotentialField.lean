import Homogenization.Ambient.Euclidean
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Scalar potential fields
-/

open Homogenization Topology




def SubdiffusiveProcess.Frozen.Assumptions.PotentialField (d : ℕ) :=
  {p : C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ) //
    (∀ x, HasFDerivAt p.1 (p.2 x) x) ∧
      ∀ K : Set (Vec d), IsCompact K →
        ∃ C : NNReal, LipschitzOnWith C p.2 K}

