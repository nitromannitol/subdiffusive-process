import SubdiffusiveProcess.Compactness.SequentialCompactness
import Mathlib.Order.Filter.AtTopBot.Finite
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Joint subsequences for countably many precompact sequences.
No energy or PDE compactness hypothesis is proved here. -/
open Filter Set
open scoped Topology
noncomputable section
namespace SubdiffusiveProcess

/-- A metric sequence whose every subsequence has a convergent subsequence has compact range closure. -/
theorem isCompact_closure_range_of_subseq_compact
    {X : Type*} [PseudoMetricSpace X] (u : ℕ → X)
    (h : ∀ rho : ℕ → ℕ, StrictMono rho →
      ∃ (x : X) (tau : ℕ → ℕ), StrictMono tau ∧ Tendsto (fun n => u (rho (tau n))) atTop (𝓝 x)) :
    IsCompact (closure (range u)) := by
  classical
  apply isCompact_closure_of_subseq_tendsto
  intro v hv
  choose k hk using hv
  by_cases hkt : Tendsto k atTop atTop
  · obtain ⟨rho, hrho, hkrho⟩ := strictMono_subseq_of_tendsto_atTop hkt
    obtain ⟨x, tau, htau, hlim⟩ := h (k ∘ rho) hkrho
    refine ⟨x, rho ∘ tau, hrho.comp htau, ?_⟩
    simpa only [Function.comp_apply, hk] using hlim
  · have hb : ∃ B : ℕ, ∃ᶠ n in atTop, k n < B := by
      rw [tendsto_atTop] at hkt
      push_neg at hkt
      obtain ⟨B, hB⟩ := hkt
      exact ⟨B, hB⟩
    obtain ⟨B, hB⟩ := hb
    have hex : ∃ᶠ n in atTop, ∃ j ∈ Iio B, k n = j :=
      hB.mono (fun n hn => ⟨k n, hn, rfl⟩)
    obtain ⟨j, _, hj⟩ := (frequently_exists_finite (finite_Iio B)).mp hex
    obtain ⟨rho, hrho, heq⟩ := extraction_of_frequently_atTop hj
    refine ⟨u j, rho, hrho, ?_⟩
    have hconst : v ∘ rho = fun _ => u j := by
      funext n
      rw [Function.comp_apply, ← hk (rho n), heq n]
    rw [hconst]
    exact tendsto_const_nhds

/-- Countably many metric precompact sequences admit one common convergent subsequence. -/
theorem exists_joint_subseq_of_countable_subseq_compact
    {I : Type*} [Countable I] {X : I → Type*} [∀ i, PseudoMetricSpace (X i)]
    (u : ∀ i, ℕ → X i)
    (h : ∀ i (rho : ℕ → ℕ), StrictMono rho →
      ∃ (x : X i) (tau : ℕ → ℕ), StrictMono tau ∧ Tendsto (fun n => u i (rho (tau n))) atTop (𝓝 x)) :
    ∃ (rho : ℕ → ℕ) (x : ∀ i, X i), StrictMono rho ∧
      ∀ i, Tendsto (fun n => u i (rho n)) atTop (𝓝 (x i)) := by
  have hc : IsCompact {x : ∀ i, X i | ∀ i, x i ∈ closure (range (u i))} :=
    isCompact_pi_infinite (fun i => isCompact_closure_range_of_subseq_compact (u i) (h i))
  obtain ⟨x, _, rho, hrho, hlim⟩ := hc.tendsto_subseq (fun n i => subset_closure (mem_range_self n))
  exact ⟨rho, x, hrho, tendsto_pi_nhds.mp hlim⟩

/-- Countably many continuous families compact on every subsequence admit one common uniform subsequence. -/
theorem exists_joint_uniform_subseq_of_countable_compact
    {I X : Type*} [Countable I] [TopologicalSpace X]
    (S : I → Set X) (hS : ∀ i, IsCompact (S i))
    (U : I → ℕ → X → ℝ) (hU : ∀ i n, ContinuousOn (U i n) (S i))
    (h : ∀ i (rho : ℕ → ℕ), StrictMono rho →
      ∃ (tau : ℕ → ℕ) (V : X → ℝ), StrictMono tau ∧ ContinuousOn V (S i) ∧
        TendstoUniformlyOn (fun n => U i (rho (tau n))) V atTop (S i)) :
    ∃ (rho : ℕ → ℕ) (V : I → X → ℝ), StrictMono rho ∧
      ∀ i, ContinuousOn (V i) (S i) ∧
        TendstoUniformlyOn (fun n => U i (rho n)) (V i) atTop (S i) := by
  classical
  letI compactS : ∀ i, CompactSpace (S i) := fun i => isCompact_iff_compactSpace.mp (hS i)
  let u : ∀ i, ℕ → C(S i, ℝ) := fun i n => ⟨fun x => U i n x, (continuousOn_iff_continuous_restrict.mp (hU i n))⟩
  have hcompact : ∀ i (rho : ℕ → ℕ), StrictMono rho →
      ∃ (x : C(S i, ℝ)) (tau : ℕ → ℕ), StrictMono tau ∧
        Tendsto (fun n => u i (rho (tau n))) atTop (𝓝 x) := by
    intro i rho hrho
    obtain ⟨tau, V, htau, hVc, hlim⟩ := h i rho hrho
    refine ⟨⟨fun x => V x, (continuousOn_iff_continuous_restrict.mp hVc)⟩, tau, htau, ?_⟩
    apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe] at hlim
    exact hlim
  obtain ⟨rho, v, hrho, hlim⟩ := exists_joint_subseq_of_countable_subseq_compact u hcompact
  let V : I → X → ℝ := fun i x => if hx : x ∈ S i then v i ⟨x, hx⟩ else 0
  have hV (i : I) (x : S i) : V i x = v i x := by
    simp only [V, dif_pos x.property]
  refine ⟨rho, V, hrho, ?_⟩
  intro i
  constructor
  · rw [continuousOn_iff_continuous_restrict]
    convert (v i).continuous using 1
    exact funext (hV i)
  · rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    convert ContinuousMap.tendsto_iff_tendstoUniformly.mp (hlim i) using 1
    exact funext (hV i)

end SubdiffusiveProcess
