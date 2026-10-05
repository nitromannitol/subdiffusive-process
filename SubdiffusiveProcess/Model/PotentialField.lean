module

public import Homogenization.Ambient.Euclidean
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.EMetricSpace.Lipschitz

@[expose] public section

/-!
# Locally regular scalar potential fields

`PotentialField d` carries a continuous scalar function and a continuous
linear-derivative field. It certifies the derivative at every point and a
Lipschitz bound for that derivative on every compact set. Every element of
the carrier is therefore locally `C¹ˑ¹`, rather than only almost every
sample under an unspecified law. `GMCModel` supplies the probability law
and standing layer assumptions on this carrier.
-/

open Homogenization Topology

/-- A scalar `C¹ˑ¹_loc` potential.  The compact-set Lipschitz certificate is
the cube-wise form of local Lipschitz regularity used in assumption (g2),
`a.g2`. -/

def SubdiffusiveProcess.Model.PotentialField (d : ℕ) :=
  {p : C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ) //
    (∀ x, HasFDerivAt p.1 (p.2 x) x) ∧
      ∀ K : Set (Vec d), IsCompact K →
        ∃ C : NNReal, LipschitzOnWith C p.2 K}

