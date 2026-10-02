import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Passing a Lipschitz-seminorm bound to a pointwise limit

The `C¹ˑ¹` carrier stores no second derivative, so the paper's Hessian
control is read as a Lipschitz seminorm of the gradient.  The Cauchy form of
that seminorm passes to the limit by the elementary argument isolated here.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

open Filter Topology

variable {X : Type*} [PseudoMetricSpace X] {E : Type*} [NormedAddCommGroup E]

/-- If the differences `F m - F n` are eventually `c`-Lipschitz on `K` and `F n`
converges pointwise on `K` to `f`, then `F m - f` is `c`-Lipschitz on `K`. -/
theorem lipschitzOnWith_sub_limit {F : ℕ → X → E} {f : X → E} {K : Set X}
    {c : NNReal} {m : ℕ}
    (hlim : ∀ x ∈ K, Tendsto (fun n => F n x) atTop (nhds (f x)))
    (h : ∀ᶠ n in atTop, LipschitzOnWith c (fun x => F m x - F n x) K) :
    LipschitzOnWith c (fun x => F m x - f x) K := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have h1 : Tendsto (fun n => F m x - F n x) atTop (nhds (F m x - f x)) :=
    Tendsto.sub tendsto_const_nhds (hlim x hx)
  have h2 : Tendsto (fun n => F m y - F n y) atTop (nhds (F m y - f y)) :=
    Tendsto.sub tendsto_const_nhds (hlim y hy)
  refine le_of_tendsto (Tendsto.dist h1 h2) ?_
  filter_upwards [h] with n hn
  exact hn.dist_le_mul x hx y hy

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
