module

public import Homogenization.Ambient.Euclidean
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.EMetricSpace.Lipschitz

@[expose] public section

/-!
# Scalar potential fields
-/

open Homogenization Topology




def SubdiffusiveProcess.Frozen.Assumptions.PotentialField (d : ℕ) :=
  {p : C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ) //
    (∀ x, HasFDerivAt p.1 (p.2 x) x) ∧
      ∀ K : Set (Vec d), IsCompact K →
        ∃ C : NNReal, LipschitzOnWith C p.2 K}

