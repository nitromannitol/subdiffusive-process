module

public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.ResponseMoments.ScalarAndAffine
public import SubdiffusiveProcess.ResponseMoments.Forms
public import SubdiffusiveProcess.ResponseMoments.UpperDensity
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



theorem thm_c1_scalar (c : ℝ) (hc : 0 < c) (pn : ℝ) (hpn : 0 < pn)
    (LamE LamF vol : ℕ → ℝ) (hvol : ∀ k, 0 < vol k)
    (hprop : ∀ k, LamF k = c * LamE k)
    (hE : Tendsto (fun k => |LamE k / vol k - pn ^ 2|) atTop (𝓝 0))
    (hF : Tendsto (fun k => |LamF k / vol k - pn ^ 2|) atTop (𝓝 0)) :
    c = 1 :=
  scalar_equals_one c hc pn hpn LamE LamF vol hvol hprop hE hF

end SubdiffusiveProcess.Paper
