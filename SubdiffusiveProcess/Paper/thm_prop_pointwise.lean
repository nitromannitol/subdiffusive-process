import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Lane3.Proportionality
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



theorem thm_prop_pointwise
    (V : Type) [AddCommGroup V] [Module ℝ V] (X : Type) [MeasurableSpace X]
    (E F : LocalEnergy V X) (m M k1 : ℝ)
    (hmpos : 0 < m) (hmM : m ≤ M) (hk1 : 0 < k1)
    (hmE : ∀ u : V, m * E.form u u ≤ F.form u u)
    (hME : ∀ u : V, F.form u u ≤ M * E.form u u)
    (hMinf : ∀ b : ℝ, (∀ u : V, F.form u u ≤ b * E.form u u) → M ≤ b)
    (hmsup : ∀ b : ℝ, (∀ u : V, b * E.form u u ≤ F.form u u) → b ≤ m)
    (himp : m < M →
      ((∀ u : V, F.form u u ≤ (M - k1 * (M - m)) * E.form u u) ∨
        (∀ u : V, (m + k1 * (M - m)) * E.form u u ≤ F.form u u))) :
    M = m ∧ ∀ u : V, F.form u u = m * E.form u u :=
  proportionality E F m M k1 hmpos hmM hk1 hmE hME hMinf hmsup himp

end Paper
