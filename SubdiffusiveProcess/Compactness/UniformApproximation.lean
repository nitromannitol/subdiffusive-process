module

public import SubdiffusiveProcess.Compactness.PointwiseExtraction
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Uniform approximation by equicontinuous families preserves compactness.
This module gives the approximation step used for nonsmooth boundary data;
it does not assert any regularity estimate for the approximating family.
-/

open Filter
open scoped Topology

namespace SubdiffusiveProcess

/-- Uniform approximation by equicontinuous families gives equicontinuity of the target family. -/
theorem equicontinuous_of_uniform_approximation
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (F : ℕ → X → Y) (A : ℕ → ℕ → X → Y)
    (hA : ∀ m, Equicontinuous (A m))
    (happrox : ∀ eps : ℝ, 0 < eps → ∃ m, ∀ n x, dist (F n x) (A m n x) < eps) :
    Equicontinuous F := by
  intro x
  apply Metric.equicontinuousAt_iff.mpr
  intro eps heps
  have hthird : 0 < eps / 3 := div_pos heps (by norm_num)
  obtain ⟨m, hm⟩ := happrox (eps / 3) hthird
  obtain ⟨delta, hdelta, hd⟩ := Metric.equicontinuousAt_iff.mp (hA m x) (eps / 3) hthird
  refine ⟨delta, hdelta, ?_⟩
  intro y hy n
  have htriangle : dist (F n x) (F n y) ≤
      dist (F n x) (A m n x) + dist (A m n x) (A m n y) + dist (A m n y) (F n y) :=
    (dist_triangle (F n x) (A m n x) (F n y)).trans
      (by linarith only [dist_triangle (A m n x) (A m n y) (F n y)])
  have hfirst := hm n x
  have hmiddle := hd y hy n
  have hlast : dist (A m n y) (F n y) < eps / 3 := by
    simpa only [dist_comm] using hm n y
  linarith only [htriangle, hfirst, hmiddle, hlast]

/-- On a compact space, a pointwise bounded family with equicontinuous uniform approximants has a uniformly converging subsequence. -/
theorem exists_uniform_subseq_of_uniform_approximation
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [TopologicalSpace.SeparableSpace X] [Nonempty X]
    (F : ℕ → X → ℝ) (A : ℕ → ℕ → X → ℝ)
    (hA : ∀ m, Equicontinuous (A m))
    (happrox : ∀ eps : ℝ, 0 < eps → ∃ m, ∀ n x, dist (F n x) (A m n x) < eps)
    (hbound : ∀ x, ∃ M : ℝ, ∀ n, ‖F n x‖ ≤ M) :
    ∃ (g : X → ℝ) (ns : ℕ → ℕ), StrictMono ns ∧ Continuous g ∧
      TendstoUniformly (fun n => F (ns n)) g atTop := by
  have hF := equicontinuous_of_uniform_approximation F A hA happrox
  obtain ⟨g, ns, hns, hgc, hlim⟩ := exists_pointwise_subseq_of_equicontinuous hF hbound
  refine ⟨g, ns, hns, hgc, ?_⟩
  apply UniformFun.tendsto_iff_tendstoUniformly.mp
  exact ((hF.comp ns).tendsto_uniformFun_iff_pi atTop g).mpr (tendsto_pi_nhds.mpr hlim)

section MetricApproximation

open Set

/-- Uniform approximation by precompact families preserves precompactness. -/
theorem totallyBounded_range_of_uniform_approximation {X ι : Type*} [PseudoMetricSpace X]
    {f : ι → X} (h : ∀ ε > (0 : ℝ), ∃ g : ι → X,
      TotallyBounded (range g) ∧ ∀ i, dist (f i) (g i) < ε) :
    TotallyBounded (range f) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := h (ε / 2) (by linarith)
  obtain ⟨T, hT, hcover⟩ := Metric.totallyBounded_iff.mp hg (ε / 2) (by linarith)
  refine ⟨T, hT, ?_⟩
  rintro x ⟨i, rfl⟩
  have hi := hcover (mem_range_self i)
  rcases mem_iUnion.mp hi with ⟨y, hy⟩
  rcases mem_iUnion.mp hy with ⟨hyT, hyball⟩
  refine mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hyT, ?_⟩⟩
  change dist (f i) y < ε
  exact (dist_triangle _ (g i) _).trans_lt (by
    have := hfg i
    have := Metric.mem_ball.mp hyball
    linarith)

/-- The band-approximation compactness step of Proposition 33, in any complete metric space. -/
theorem isCompact_closure_range_of_approximating_compact_ranges {X ι : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] {f : ι → X} {g : ℕ → ι → X}
    {err : ℕ → ℝ} (hc : ∀ H, IsCompact (closure (range (g H))))
    (he : Tendsto err atTop (𝓝 0)) (hfg : ∀ H i, dist (f i) (g H i) ≤ err H) :
    IsCompact (closure (range f)) := by
  apply TotallyBounded.isCompact_of_isClosed _ isClosed_closure
  apply TotallyBounded.closure
  apply totallyBounded_range_of_uniform_approximation
  intro ε hε
  obtain ⟨H, hH⟩ := (he.eventually_lt_const hε).exists
  exact ⟨g H, (hc H).totallyBounded.subset subset_closure,
    fun i => (hfg H i).trans_lt hH⟩

end MetricApproximation

end SubdiffusiveProcess
