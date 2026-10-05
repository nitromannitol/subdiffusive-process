module

public import Mathlib

@[expose] public section

/-! Simultaneous almost-sure extraction towards specified countably many limits.
The limits are identified beforehand; no completeness or limit choice is used. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory
open scoped Topology ENNReal BigOperators

namespace SubdiffusiveProcess.Section9

/-- A countable family converging in measure has one common almost-sure subsequence. -/
theorem exists_common_ae_subsequence
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {F : ℕ → Type*} [∀ i, PseudoEMetricSpace (F i)]
    (X : ∀ i, ℕ → Ω → F i) (G : ∀ i, Ω → F i)
    (h : ∀ i, TendstoInMeasure P (X i) atTop (G i)) :
    ∃ seq : ℕ → ℕ, StrictMono seq ∧
      ∀ᵐ ω ∂P, ∀ i, Tendsto (fun n => X i (seq n) ω) atTop (𝓝 (G i ω)) := by
  classical
  choose N0 hN0 using fun i k =>
    ExistsSeqTendstoAe.exists_nat_measure_lt_two_inv (h i) k
  let M : ℕ → ℕ := fun k => ∑ i ∈ Finset.range (k + 1), N0 i k
  let seq : ℕ → ℕ := fun k => k + ∑ j ∈ Finset.range (k + 1), M j
  have hseq : StrictMono seq := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    change k + ∑ j ∈ Finset.range (k + 1), M j <
      k + 1 + ∑ j ∈ Finset.range (k + 1 + 1), M j
    rw [Finset.sum_range_succ _ (k + 1)]
    omega
  have hbound : ∀ i k : ℕ, i ≤ k → N0 i k ≤ seq k := by
    intro i k hik
    have h1 : N0 i k ≤ M k :=
      Finset.single_le_sum (f := fun j => N0 j k) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (by omega))
    have h2 : M k ≤ ∑ j ∈ Finset.range (k + 1), M j :=
      Finset.single_le_sum (f := M) (fun _ _ => Nat.zero_le _)
        (Finset.self_mem_range_succ k)
    exact h1.trans (h2.trans (Nat.le_add_left _ _))
  have hae : ∀ i, ∀ᵐ ω ∂P,
      Tendsto (fun n => X i (seq n) ω) atTop (𝓝 (G i ω)) := by
    intro i
    let s : ℕ → Set Ω := fun k =>
      {ω | i ≤ k ∧ (2 : ℝ≥0∞)⁻¹ ^ k ≤ edist (X i (seq k) ω) (G i ω)}
    have hs : ∀ k, P (s k) ≤ (2 : ℝ≥0∞)⁻¹ ^ k := by
      intro k
      by_cases hik : i ≤ k
      · exact (measure_mono (fun _ hω => hω.2)).trans
          (hN0 i k (seq k) (hbound i k hik))
      · have hempty : s k = ∅ := by
          ext ω
          simp only [s, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
          exact fun h => absurd h hik
        rw [hempty, measure_empty]
        exact bot_le
    have hsum : ∑' k, P (s k) ≠ ∞ := by
      refine ne_top_of_le_ne_top (b := ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ k) ?_
        (ENNReal.tsum_le_tsum hs)
      simp only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.ofNat_ne_top
    filter_upwards [ae_eventually_notMem hsum] with ω hω
    rw [EMetric.tendsto_atTop]
    intro ε hε
    obtain ⟨K, hK⟩ := ENNReal.exists_inv_two_pow_lt hε.ne'
    obtain ⟨N, hN⟩ := eventually_atTop.mp hω
    refine ⟨max N (max i K), fun n hn => ?_⟩
    have hi : i ≤ n := (le_trans (le_max_left i K) (le_max_right N (max i K))).trans hn
    have hKn : K ≤ n := (le_trans (le_max_right i K) (le_max_right N (max i K))).trans hn
    have hsmall : edist (X i (seq n) ω) (G i ω) < (2 : ℝ≥0∞)⁻¹ ^ n := by
      apply lt_of_not_ge
      exact fun he => hN n ((le_max_left _ _).trans hn) ⟨hi, he⟩
    exact hsmall.trans_le ((pow_le_pow_of_le_one (by simp) (by simp) hKn).trans hK.le)
  exact ⟨seq, hseq, ae_all_iff.mpr hae⟩


/-- Two sequences converging in measure converge jointly in the product metric. -/
theorem tendstoInMeasure_prod
    {Ω E F : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    (P : Measure Ω) (X : ℕ → Ω → E) (Y : ℕ → Ω → F) (G : Ω → E) (H : Ω → F)
    (hX : TendstoInMeasure P X atTop G) (hY : TendstoInMeasure P Y atTop H) :
    TendstoInMeasure P (fun n ω => (X n ω, Y n ω)) atTop (fun ω => (G ω, H ω)) := by
  intro ε hε
  have hsum := (hX ε hε).add (hY ε hε)
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) (fun n => ?_)
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simpa only [Set.mem_union, Set.mem_ofPred_eq, Prod.edist_eq, le_max_iff] using hω

end SubdiffusiveProcess.Section9
