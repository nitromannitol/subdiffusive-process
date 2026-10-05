module

public import SubdiffusiveProcess.Sobolev.SmoothFractionalUpstream
public import SubdiffusiveProcess.Main.CubeFractionalL2Norm
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal ContDiff
noncomputable section

namespace SubdiffusiveProcess

def halfFractionalOrder : Set.Ioo (0 : ℝ) 1 :=
  ⟨1 / 2, by norm_num, by norm_num⟩

end SubdiffusiveProcess
