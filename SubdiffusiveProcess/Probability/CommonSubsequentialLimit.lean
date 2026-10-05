module

public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Basic

@[expose] public section

/-!
# Common limit of a compact sequence with unique subsequential limits

A sequence of real random variables such that every subsequence has an almost surely convergent
further subsequence, and any two almost surely convergent subsequences have almost surely equal
limits, has one limit `Rlim` along which every subsequence has a further subsequence converging
almost surely.  This is the subsequence-criterion form of convergence in probability.
-/

open MeasureTheory Filter
open scoped Topology

namespace SubdiffusiveProcess

/-- Relative compactness (every subsequence has an a.s. convergent refinement) and uniqueness of
a.s. subsequential limits give one common limit along every subsequence's refinement. -/
theorem exists_common_limit_of_compact_of_unique
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : ℕ → Ω → ℝ)
    (hcompact : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧ ∃ L : Ω → ℝ,
      ∀ᵐ ω ∂μ, Tendsto (fun n => f (ψ (ψ' n)) ω) atTop (𝓝 (L ω)))
    (hunique : ∀ φ₁ φ₂ : ℕ → ℕ, StrictMono φ₁ → StrictMono φ₂ → ∀ L₁ L₂ : Ω → ℝ,
      (∀ᵐ ω ∂μ, Tendsto (fun n => f (φ₁ n) ω) atTop (𝓝 (L₁ ω))) →
      (∀ᵐ ω ∂μ, Tendsto (fun n => f (φ₂ n) ω) atTop (𝓝 (L₂ ω))) → L₁ =ᵐ[μ] L₂) :
    ∃ Rlim : Ω → ℝ, ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => f (ψ (ψ' n)) ω) atTop (𝓝 (Rlim ω)) := by
  obtain ⟨ψ₀, hψ₀, L₀, hL₀⟩ := hcompact id strictMono_id
  refine ⟨L₀, fun ψ hψ => ?_⟩
  obtain ⟨ψ', hψ', L, hL⟩ := hcompact ψ hψ
  refine ⟨ψ', hψ', ?_⟩
  have hL₀' : ∀ᵐ ω ∂μ, Tendsto (fun n => f (ψ₀ n) ω) atTop (𝓝 (L₀ ω)) := hL₀
  have heq : L₀ =ᵐ[μ] L := hunique ψ₀ (ψ ∘ ψ') hψ₀ (hψ.comp hψ') L₀ L hL₀' hL
  filter_upwards [hL, heq] with ω h1 h2
  rw [← h2] at h1
  exact h1

end SubdiffusiveProcess
