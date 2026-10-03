module

public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Subsequence criteria for convergence in probability (generic)

Two generic facts about a probability space:

* if countably many real random variables `X j N` tend to `0` in probability as `N → ∞`, then
  along any `φ` tending to infinity there is a further subsequence along which they all tend to
  `0` almost surely, simultaneously in `j`;
* a real sequence in `[0, ∞]` tends to `0` as soon as every strictly increasing subsequence has
  a further subsequence tending to `0`.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

namespace SubdiffusiveProcess

/-- Diagonal Borel--Cantelli extraction: countably many sequences tending to `0` in probability
have a common further subsequence, inside any subsequence tending to infinity, along which they
tend to `0` almost surely, simultaneously in the family index. -/
theorem exists_strictMono_ae_forall_tendsto_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → ℕ → Ω → ℝ)
    (hX : ∀ j : ℕ, ∀ eps : ℝ, 0 < eps →
      Tendsto (fun N => P {ω | eps ≤ |X j N ω|}) atTop (𝓝 0))
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ ω ∂P, ∀ j : ℕ, Tendsto (fun n => X j (φ (ψ n)) ω) atTop (𝓝 0) := by
  have hev : ∀ n : ℕ, ∀ᶠ k in atTop, ∀ j ∈ Finset.range (n + 1),
      P {ω | 1 / ((n : ℝ) + 1) ≤ |X j (φ k) ω|} ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n
    have hpos : (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ n := ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) n
    have h1 : ∀ j ∈ Finset.range (n + 1), ∀ᶠ N in atTop,
        P {ω | 1 / ((n : ℝ) + 1) ≤ |X j N ω|} ≤ (2⁻¹ : ℝ≥0∞) ^ n := fun j _ =>
      (ENNReal.tendsto_nhds_zero.1 (hX j (1 / ((n : ℝ) + 1)) (by positivity))) _ hpos
    exact hφ.eventually ((Finset.range (n + 1)).eventually_all.2 h1)
  obtain ⟨ψ, hψ, hψP⟩ := Filter.extraction_forall_of_eventually hev
  refine ⟨ψ, hψ, ?_⟩
  rw [ae_all_iff]
  intro j
  let s : ℕ → Set Ω := fun n => {ω | 1 / ((n + j : ℕ) + 1 : ℝ) ≤ |X j (φ (ψ (n + j))) ω|}
  have hs : ∀ n, P (s n) ≤ (2⁻¹ : ℝ≥0∞) ^ (n + j) := fun n =>
    hψP (n + j) j (Finset.mem_range.2 (by omega))
  have hsum : ∑' n, P (s n) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hs)
    have : ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + j) = (2⁻¹ : ℝ≥0∞) ^ j * ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n := by
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr fun n => by rw [pow_add, mul_comm]
    rw [this, ENNReal.tsum_geometric]
    refine ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 two_ne_zero)) ?_
    refine ENNReal.inv_ne_top.2 fun h => ?_
    exact absurd (tsub_eq_zero_iff_le.1 h) (not_le.2 (ENNReal.inv_lt_one.2 ENNReal.one_lt_two))
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  have hlt : ∀ᶠ n in atTop, |X j (φ (ψ (n + j))) ω| < 1 / ((n + j : ℕ) + 1 : ℝ) := by
    filter_upwards [hω] with n hn
    exact not_le.1 hn
  have hzero : Tendsto (fun n : ℕ => X j (φ (ψ (n + j))) ω) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun n : ℕ => 1 / (((n + j : ℕ) : ℝ) + 1)) ?_ ?_
    · filter_upwards [hlt] with n hn
      rw [Real.norm_eq_abs]
      exact hn.le
    · have h0 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      have h1 : Tendsto (fun n : ℕ => ((n + j : ℕ) : ℝ) + 1) atTop atTop := by
        refine tendsto_atTop_mono (fun n => ?_) h0
        push_cast
        linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      simpa only [Pi.inv_def, one_div] using h1.inv_tendsto_atTop
  exact (tendsto_add_atTop_iff_nat j).1 hzero

/-- Subsequence criterion for a `[0, ∞]`-valued sequence: if every strictly increasing
subsequence has a further subsequence tending to `0`, the whole sequence tends to `0`. -/
theorem tendsto_zero_of_forall_subseq {a : ℕ → ℝ≥0∞}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (fun n => a (φ (ψ n))) atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  by_contra hne
  rw [ENNReal.tendsto_nhds_zero] at hne
  push_neg at hne
  obtain ⟨c, hc, hfreq⟩ := hne
  obtain ⟨φ, hφ, hφc⟩ := Filter.extraction_of_frequently_atTop hfreq
  obtain ⟨ψ, hψ, hconv⟩ := h φ hφ
  have hev := (ENNReal.tendsto_nhds_zero.1 hconv) c hc
  obtain ⟨n, hn⟩ := hev.exists
  exact absurd (hφc (ψ n)) (not_lt.2 hn)

/-- The `ε`–`ρ` form of convergence to `0` in `[0, ∞]`. -/
theorem tendsto_zero_ennreal_iff_real (a : ℕ → ℝ≥0∞) :
    Tendsto a atTop (𝓝 0) ↔
      ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N, N0 ≤ N → a N ≤ ENNReal.ofReal rho := by
  rw [ENNReal.tendsto_nhds_zero]
  constructor
  · intro h rho hrho
    exact Filter.eventually_atTop.1 (h _ (ENNReal.ofReal_pos.2 hrho))
  · intro h ε hε
    rcases eq_or_ne ε ⊤ with rfl | hne
    · exact Filter.Eventually.of_forall fun N => le_top
    · obtain ⟨N0, hN0⟩ := h ε.toReal (ENNReal.toReal_pos hε.ne' hne)
      exact Filter.eventually_atTop.2 ⟨N0, fun N hN => (hN0 N hN).trans (by
        rw [ENNReal.ofReal_toReal hne])⟩

end SubdiffusiveProcess
