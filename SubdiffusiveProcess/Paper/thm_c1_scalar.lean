import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Lane3.ScalarAndAffine
import SubdiffusiveProcess.Lane3.Forms
import SubdiffusiveProcess.Lane3.UpperDensity
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem thm_c1_scalar (c : ℝ) (hc : 0 < c) (pn : ℝ) (hpn : 0 < pn)
    (LamE LamF vol : ℕ → ℝ) (hvol : ∀ k, 0 < vol k)
    (hprop : ∀ k, LamF k = c * LamE k)
    (hE : Tendsto (fun k => |LamE k / vol k - pn ^ 2|) atTop (𝓝 0))
    (hF : Tendsto (fun k => |LamF k / vol k - pn ^ 2|) atTop (𝓝 0)) :
    c = 1 :=
  scalar_equals_one c hc pn hpn LamE LamF vol hvol hprop hE hF

end Paper
