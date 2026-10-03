module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Topology.MetricSpace.Cauchy

@[expose] public section

/-! Persistent approximants converge uniformly when changes occur only where
both old and new values have a vanishing error from one fixed function.
No geometric partition or energy estimate is asserted. -/
open Filter
open scoped Topology
noncomputable section
namespace SubdiffusiveProcess

/-- Refinement that preserves old values or changes them within a vanishing common error is uniformly convergent. -/
theorem exists_uniform_limit_of_persistent_refinement
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (F : ℕ → X → ℝ) (hF : ∀ n, Continuous (F n)) (b : X → ℝ)
    (eps : ℕ → ℝ) (heps : ∀ n, 0 ≤ eps n) (hzero : Tendsto eps atTop (𝓝 0))
    (hRefine : ∀ n m, n ≤ m → ∀ x,
      F m x = F n x ∨ (|F n x - b x| ≤ eps n ∧ |F m x - b x| ≤ eps n)) :
    ∃ g : X → ℝ, Continuous g ∧ TendstoUniformly F g atTop := by
  let f : ℕ → C(X, ℝ) := fun n => ⟨F n, hF n⟩
  have hbound : ∀ n m, n ≤ m → dist (f n) (f m) ≤ 2 * eps n := by
    intro n m hnm
    apply (ContinuousMap.dist_le (mul_nonneg (by norm_num) (heps n))).mpr
    intro x
    rcases hRefine n m hnm x with heq | hclose
    · change dist (F n x) (F m x) ≤ _
      rw [heq, dist_self]
      exact mul_nonneg (by norm_num) (heps n)
    · have htri := dist_triangle (F n x) (b x) (F m x)
      change dist (F n x) (F m x) ≤ _
      have hleft : dist (F n x) (b x) ≤ eps n := by
        simpa only [Real.dist_eq] using hclose.1
      have hright : dist (b x) (F m x) ≤ eps n := by
        simpa only [Real.dist_eq, abs_sub_comm] using hclose.2
      linarith only [htri, hleft, hright]
  have hzero' : Tendsto (fun n => 2 * eps n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hzero
  have hc : CauchySeq f := cauchySeq_of_le_tendsto_0' (fun n => 2 * eps n) hbound hzero'
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨g, g.continuous, ContinuousMap.tendsto_iff_tendstoUniformly.mp hg⟩

end SubdiffusiveProcess
