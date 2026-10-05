module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! A one-sided comparison tail passes through convergence in measure with
strict threshold slack. No measurability of the fixed comparison function
is needed because all event probabilities are outer measures.
-/
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace SubdiffusiveProcess

/-- Eventual comparison tails pass to a limit in measure at a larger threshold. -/
theorem measure_sub_limit_gt_le {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (u : ℕ → Omega → ℝ) (v g : Omega → ℝ)
    (hconv : TendstoInMeasure mu u atTop g)
    (a b : ℝ) (hab : a < b) (c : ℝ≥0∞)
    (hbound : ∀ᶠ n in atTop, mu {omega | a < v omega - u n omega} ≤ c) :
    mu {omega | b < v omega - g omega} ≤ c := by
  have hgap : 0 < ENNReal.ofReal (b - a) := ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  have hclose := hconv (ENNReal.ofReal (b - a)) hgap
  have hlim : Tendsto (fun n => c + mu {omega |
      ENNReal.ofReal (b - a) ≤ edist (u n omega) (g omega)}) atTop (𝓝 c) := by
    simpa only [add_zero] using hclose.const_add c
  apply ge_of_tendsto hlim
  filter_upwards [hbound] with n hn
  have hincl : {omega | b < v omega - g omega} ⊆
      {omega | a < v omega - u n omega} ∪
        {omega | ENNReal.ofReal (b - a) ≤ edist (u n omega) (g omega)} := by
    intro omega homega
    by_cases hbad : a < v omega - u n omega
    · exact Or.inl hbad
    · right
      have hbad' : v omega - u n omega ≤ a := le_of_not_gt hbad
      have homega' : b < v omega - g omega := homega
      have hdiff : b - a ≤ u n omega - g omega := by
        linarith only [hbad', homega']
      change ENNReal.ofReal (b - a) ≤ edist (u n omega) (g omega)
      rw [edist_dist, Real.dist_eq]
      exact ENNReal.ofReal_le_ofReal (hdiff.trans (le_abs_self _))
  exact (measure_mono hincl).trans ((measure_union_le _ _).trans (add_le_add hn le_rfl))

end SubdiffusiveProcess
