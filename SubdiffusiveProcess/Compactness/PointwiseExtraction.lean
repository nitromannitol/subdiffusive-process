import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith

/-!
# Dense-set subsequence extraction

Source: Lemma 32, `lem:conditional-compact`. This reusable topological step
uses only separability, equicontinuity and pointwise boundedness. The response
consumer proves these hypotheses from the potential comparison and moment bound.
-/

open Filter Set
open scoped Topology
namespace SubdiffusiveProcess

/-- Dense-set extraction for an equicontinuous, pointwise bounded real family.
No compactness or completeness of the parameter space is required. -/
theorem exists_pointwise_subseq_of_equicontinuous {X : Type*} [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] [Nonempty X] {f : ℕ → X → ℝ}
    (heq : Equicontinuous f) (hbound : ∀ x, ∃ M : ℝ, ∀ n, ‖f n x‖ ≤ M) :
    ∃ (g : X → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ Continuous g ∧
      ∀ x, Tendsto (fun n => f (φ n) x) atTop (𝓝 (g x)) := by
  classical
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq X
  choose M hM using fun k => hbound (d k)
  have hc : IsCompact {a : ℕ → ℝ | ∀ k, a k ∈ Icc (-M k) (M k)} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  obtain ⟨a, _, φ, hφ, hlim⟩ := hc.tendsto_subseq
    (x := fun n k => f n (d k)) (fun n k => by
      simpa only [Real.norm_eq_abs, abs_le] using hM k n)
  have hcauchy (x : X) : CauchySeq (fun n => f (φ n) x) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨δ, hδ, he⟩ := Metric.equicontinuousAt_iff.mp (heq x) (ε / 3) (by linarith)
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp hd x δ hδ
    have hk' : dist (d k) x < δ := by rwa [dist_comm]
    have hdk : CauchySeq (fun n => f (φ n) (d k)) :=
      ((tendsto_pi_nhds.mp hlim) k).cauchySeq
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hdk (ε / 3) (by linarith)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hleft := he (d k) hk' (φ m)
    have hright := he (d k) hk' (φ n)
    have hmid := hN m hm n hn
    calc
      dist (f (φ m) x) (f (φ n) x) ≤
          dist (f (φ m) x) (f (φ m) (d k)) +
          dist (f (φ m) (d k)) (f (φ n) (d k)) +
          dist (f (φ n) (d k)) (f (φ n) x) := dist_triangle4 _ _ _ _
      _ < ε := by rw [dist_comm (f (φ n) (d k))]; linarith
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  refine ⟨g, φ, hφ, ?_, hg⟩
  apply (tendsto_pi_nhds.mpr hg).continuous_of_equicontinuous
  exact heq.comp φ

end SubdiffusiveProcess
