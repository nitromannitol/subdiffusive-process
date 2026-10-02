import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.UniformSpace.Cauchy

open Filter Set
open scoped Topology
namespace SubdiffusiveProcess

/-- Uniform approximation by totally bounded ranges gives a convergent subsequence. -/
theorem exists_subseq_of_totallyBounded_approximations
    {X : Type*} [MetricSpace X] [CompleteSpace X] (v : ℕ → X)
    (happrox : ∀ eps > (0 : ℝ), ∃ w : ℕ → X,
      TotallyBounded (range w) ∧ ∀ n, dist (v n) (w n) < eps) :
    ∃ (phi : ℕ → ℕ) (w : X),
      StrictMono phi ∧ Tendsto (fun n => v (phi n)) atTop (𝓝 w) := by
  have hv : TotallyBounded (range v) := by
    apply Metric.totallyBounded_iff.mpr
    intro eps heps
    obtain ⟨w, hw, hdist⟩ := happrox (eps / 2) (half_pos heps)
    obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp hw (eps / 2) (half_pos heps)
    refine ⟨t, ht, ?_⟩
    rintro x ⟨n, rfl⟩
    obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.mp (hcover (mem_range_self n))
    apply mem_iUnion₂.mpr
    refine ⟨y, hyt, ?_⟩
    exact (dist_triangle (v n) (w n) y).trans_lt (by
      have h := hdist n
      have h' : dist (w n) y < eps / 2 := hy
      linarith)
  have hcompact := hv.closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨w, _, phi, hphi, hlim⟩ :=
    hcompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  exact ⟨phi, w, hphi, hlim⟩

end SubdiffusiveProcess
