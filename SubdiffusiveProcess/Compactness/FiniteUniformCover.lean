import SubdiffusiveProcess.Compactness.SequentialCompactness
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Uniform subsequences on finite covers

This module constructs a single uniform subsequence from finitely many local extraction properties.
It does not require compactness of the covered space or the cover pieces.
-/

open Filter Set
open scoped Topology
noncomputable section
namespace SubdiffusiveProcess

/-- A finite family of pieces admits one subsequence converging uniformly on each piece. -/
private theorem exists_uniform_subsequence_on_finset
    {X : Type*} [TopologicalSpace X] {I : Type*} [Fintype I]
    (S : I → Set X) (f : ℕ → X → ℝ)
    (hlocal : ∀ i, ∀ sigma : ℕ → ℕ, StrictMono sigma →
      ∃ tau : ℕ → ℕ, StrictMono tau ∧ ∃ g : X → ℝ,
        TendstoUniformlyOn (fun n => f (sigma (tau n))) g atTop (S i))
    (s : Finset I) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧ ∀ i ∈ s, ∃ g : X → ℝ,
      TendstoUniformlyOn (fun n => f (sigma n)) g atTop (S i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨id, strictMono_id, ?_⟩
      intro i hi
      simp only [Finset.notMem_empty] at hi
  | @insert i s hi ih =>
      obtain ⟨sigma, hσ, hprior⟩ := ih
      obtain ⟨tau, hτ, g, hnew⟩ := hlocal i sigma hσ
      refine ⟨sigma ∘ tau, hσ.comp hτ, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjs
      · subst j
        exact ⟨g, hnew⟩
      · obtain ⟨g₀, h₀⟩ := hprior j hjs
        exact ⟨g₀, h₀.seq_tendstoUniformlyOn tau hτ.tendsto_atTop⟩

/-- A finite cover admits one uniform subsequence when every restricted bank is sequentially precompact. -/
theorem exists_uniform_subsequence_of_finite_cover
    {X : Type*} [TopologicalSpace X] {I : Type*} [Fintype I]
    (S : I → Set X) (hcover : ∀ x : X, ∃ i, x ∈ S i)
    (f : ℕ → X → ℝ) (hcont : ∀ n, Continuous (f n))
    (hlocal : ∀ i, ∀ sigma : ℕ → ℕ, StrictMono sigma →
      ∃ tau : ℕ → ℕ, StrictMono tau ∧ ∃ g : X → ℝ,
        TendstoUniformlyOn (fun n => f (sigma (tau n))) g atTop (S i)) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧ ∃ g : X → ℝ,
      Continuous g ∧ TendstoUniformly (fun n => f (sigma n)) g atTop := by
  classical
  obtain ⟨sigma, hσ, hlimits⟩ :=
    exists_uniform_subsequence_on_finset S f hlocal Finset.univ
  let gi : I → X → ℝ := fun i => Classical.choose (hlimits i (Finset.mem_univ i))
  have hgi : ∀ i, TendstoUniformlyOn (fun n => f (sigma n)) (gi i) atTop (S i) := by
    intro i
    exact Classical.choose_spec (hlimits i (Finset.mem_univ i))
  let g : X → ℝ := fun x => gi (Classical.choose (hcover x)) x
  have hglue : ∀ i x, x ∈ S i → gi i x = g x := by
    intro i x hix
    have hchosen : x ∈ S (Classical.choose (hcover x)) := Classical.choose_spec (hcover x)
    have hi := (hgi i).tendsto_at hix
    have hchosen' := (hgi (Classical.choose (hcover x))).tendsto_at hchosen
    have heq : gi i x = gi (Classical.choose (hcover x)) x :=
      tendsto_nhds_unique hi hchosen'
    change gi i x = gi (Classical.choose (hcover x)) x
    exact heq
  have huniform : TendstoUniformly (fun n => f (sigma n)) g atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hpieces : ∀ i, ∀ᶠ n in atTop, ∀ x ∈ S i,
        dist (gi i x) (f (sigma n) x) < ε := by
      intro i
      exact (Metric.tendstoUniformlyOn_iff.mp (hgi i)) ε hε
    have hall : ∀ᶠ n in atTop, ∀ i, ∀ x ∈ S i,
        dist (gi i x) (f (sigma n) x) < ε :=
      Filter.eventually_all.mpr hpieces
    filter_upwards [hall] with n hn x
    obtain ⟨i, hxi⟩ := hcover x
    have hbound := hn i x hxi
    rw [← hglue i x hxi]
    exact hbound
  refine ⟨sigma, hσ, g, ?_, huniform⟩
  exact huniform.continuous
    (Filter.Eventually.of_forall (fun n => hcont (sigma n))).frequently

end SubdiffusiveProcess
