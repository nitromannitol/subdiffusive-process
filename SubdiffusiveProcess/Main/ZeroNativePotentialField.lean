module

public import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
public import SubdiffusiveProcess.Assumptions.AnchoredPartialSum
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

def zeroNativePotentialField (d : ℕ) :
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField d := by
  refine ⟨(0, 0), ?_, ?_⟩
  · intro x
    simpa using! (hasFDerivAt_const (x := x) (c := (0 : ℝ)))
  · intro K _hK
    exact ⟨0, by simp [LipschitzOnWith]⟩

end SubdiffusiveProcess
