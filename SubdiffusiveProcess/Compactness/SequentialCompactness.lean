import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Choose




open Filter Set
open scoped Topology
namespace SubdiffusiveProcess

/-- Sequential precompactness implies compactness of the closure in a metric space. -/
theorem isCompact_closure_of_subseq_tendsto {X : Type*} [PseudoMetricSpace X] {S : Set X}
    (hS : ∀ u : ℕ → X, (∀ n, u n ∈ S) →
      ∃ (x : X) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x)) :
    IsCompact (closure S) := by
  apply IsSeqCompact.isCompact
  intro u hu
  have he (n : ℕ) : ∃ v ∈ S, dist (u n) v < ((n : ℝ) + 1)⁻¹ :=
    Metric.mem_closure_iff.mp (hu n) _ (by positivity)
  choose v hv hdist using he
  obtain ⟨x, φ, hφ, hlim⟩ := hS v hv
  have hx : x ∈ closure S := mem_closure_of_tendsto hlim (Eventually.of_forall (fun n => hv (φ n)))
  have hz : Tendsto (fun n => dist (u n) (v n)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) (fun n => (hdist n).le)
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hclose := hz.comp hφ.tendsto_atTop
  refine ⟨x, hx, φ, hφ, ?_⟩
  exact (tendsto_iff_of_dist hclose).mpr hlim

end SubdiffusiveProcess

namespace SubdiffusiveProcess

/-- Convergence along every subsequence of moving points is uniform on a compact set.
This is the final compact-starting-set argument of `mfd:lem-resolvents-to-paths`;
the process-specific convergence at moving points is a separate hypothesis here. -/
theorem tendstoUniformlyOn_of_compact_moving_points
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {s : Set X} (hs : IsCompact s) {F : ℕ → X → Y} {f : X → Y}
    (hf : ContinuousOn f s)
    (h : ∀ (u : ℕ → X) (x : X) (φ : ℕ → ℕ),
      (∀ n, u n ∈ s) → x ∈ s → StrictMono φ →
      Tendsto u atTop (𝓝 x) →
      Tendsto (fun n => F (φ n) (u n)) atTop (𝓝 (f x))) :
    TendstoUniformlyOn F f atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hεevent
  have hbad : ∃ᶠ n in atTop, ∃ x ∈ s, ε ≤ dist (f x) (F n x) := by
    rw [Filter.not_eventually] at hεevent
    exact hεevent.mono fun n hn => by
      simp only [not_forall, not_lt] at hn
      obtain ⟨x, hxs, hdistx⟩ := hn
      exact ⟨x, hxs, hdistx⟩
  obtain ⟨ψ, hψ, hbadψ⟩ := extraction_of_frequently_atTop hbad
  choose u hu hdist using hbadψ
  obtain ⟨x, hx, φ, hφ, huφ⟩ := hs.tendsto_subseq hu
  have hfu : Tendsto (fun n => f (u (φ n))) atTop (𝓝 (f x)) :=
    (hf x hx).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨huφ, Eventually.of_forall (fun n => hu (φ n))⟩)
  have hFu : Tendsto (fun n => F ((ψ ∘ φ) n) (u (φ n))) atTop (𝓝 (f x)) :=
    h (u ∘ φ) x (ψ ∘ φ) (fun n => hu (φ n)) hx (hψ.comp hφ) huφ
  have hdist_zero :
      Tendsto (fun n => dist (f (u (φ n))) (F (ψ (φ n)) (u (φ n)))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, dist_self] using hfu.dist hFu
  have hdist_lower : ∀ n, ε ≤ dist (f (u (φ n))) (F (ψ (φ n)) (u (φ n))) :=
    fun n => hdist (φ n)
  have hevent_lt : ∀ᶠ n in atTop,
      dist (f (u (φ n))) (F (ψ (φ n)) (u (φ n))) < ε :=
    ((Metric.tendsto_nhds.1 hdist_zero) ε hε).mono fun n hn => by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using hn
  obtain ⟨n, hnlt, hnge⟩ :=
    (hevent_lt.and (Eventually.of_forall hdist_lower)).exists
  exact (not_lt_of_ge hnge) hnlt

end SubdiffusiveProcess
