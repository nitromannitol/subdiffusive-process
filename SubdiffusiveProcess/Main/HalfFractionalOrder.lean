import SubdiffusiveProcess.Sobolev.SmoothFractionalUpstream
import SubdiffusiveProcess.Main.CubeFractionalL2Norm
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory Set TopologicalSpace
open scoped ENNReal ContDiff
noncomputable section

namespace SubdiffusiveProcess

def halfFractionalOrder : Set.Ioo (0 : ℝ) 1 :=
  ⟨1 / 2, by norm_num, by norm_num⟩

end SubdiffusiveProcess
