import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Instances.Real.Lemmas
open Filter
open scoped Topology

/-! Diagonal recovery preserves every cutoff and selects only the approximation row. -/

namespace SubdiffusiveProcess
theorem exists_recoverySequence_of_approximations
    {X Y : Type*} [PseudoMetricSpace Y]
    (ι : X → Y) (E : ℕ → X → ℝ)
    (u : ℕ → Y) (e : ℕ → ℝ) (v : ℕ → ℕ → X)
    (uLim : Y) (eLim : ℝ)
    (hu : Tendsto u atTop (𝓝 uLim))
    (he : Tendsto e atTop (𝓝 eLim))
    (hv : ∀ j : ℕ, Tendsto (fun n => (ι (v j n), E n (v j n))) atTop
      (𝓝 (u j, e j))) :
    ∃ w : ℕ → X, Tendsto (fun n => (ι (w n), E n (w n))) atTop
      (𝓝 (uLim, eLim)) := by
  let f : ℕ → ℕ → Y × ℝ := fun j n ↦ (ι (v j n), E n (v j n))
  let a : ℕ → Y × ℝ := fun j ↦ (u j, e j)
  have hf : ∀ j : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      dist (f j n) (a j) < 1 / (j + 1 : ℝ) := by
    intro j
    exact (Metric.tendsto_atTop.1 (hv j)) _ (by positivity)
  choose N hN using hf
  let k : ℕ → ℕ := fun n ↦ Nat.findGreatest (fun j ↦ N j ≤ n) n
  have hk_tendsto : Tendsto k atTop atTop := by
    refine tendsto_atTop.2 fun j ↦ ?_
    filter_upwards [eventually_ge_atTop (max j (N j))] with n hn
    exact Nat.le_findGreatest (le_trans (le_max_left _ _) hn) (le_trans (le_max_right _ _) hn)
  have hdist : Tendsto (fun n ↦ dist (a (k n)) (f (k n) n)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
    refine ⟨max (N 0) (max j (N j)), fun n hn ↦ ?_⟩
    have hn0 : N 0 ≤ n := le_trans (le_max_left _ _) hn
    have hkn : N (k n) ≤ n := by
      change N (Nat.findGreatest (fun j ↦ N j ≤ n) n) ≤ n
      exact Nat.findGreatest_spec (P := fun j ↦ N j ≤ n) (Nat.zero_le n) hn0
    have hjk : j ≤ k n := by
      apply Nat.le_findGreatest
      · exact le_trans (le_max_left _ _)
          (le_trans (le_max_right _ _) hn)
      · exact le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _) hn)
    have hvalue : dist (a (k n)) (f (k n) n) < ε := by
      rw [dist_comm]
      refine lt_trans (hN (k n) n hkn) (lt_of_le_of_lt ?_ hj)
      exact one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.succ_le_succ hjk)
    simpa [Real.dist_eq, abs_of_nonneg dist_nonneg] using hvalue
  refine ⟨fun n ↦ v (k n) n, ?_⟩
  have ha : Tendsto a atTop (𝓝 (uLim, eLim)) := by
    rw [nhds_prod_eq]
    exact hu.prodMk he
  have hak : Tendsto (fun n ↦ a (k n)) atTop (𝓝 (uLim, eLim)) := ha.comp hk_tendsto
  exact hak.congr_dist hdist

end SubdiffusiveProcess
