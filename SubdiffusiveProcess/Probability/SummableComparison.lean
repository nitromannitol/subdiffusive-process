import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Filter MeasureTheory Set
open scoped Topology ENNReal

/-! # Almost-sure convergence from summable relative response errors

This is the Borel–Cantelli step of `mfd:prop-as-response-bank` in the revised
convergence section. It consumes summable comparisons at every fixed tolerance;
it does not establish those estimates for the random elliptic responses.
-/

namespace SubdiffusiveProcess

/-- Summable errors at every fixed relative tolerance imply full-sequence convergence. -/
theorem ae_tendsto_of_summable_relative_comparison
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Z : ℕ → Ω → ℝ} {Zlim : Ω → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ r : ℕ → ℝ,
      Tendsto r atTop (𝓝 0) ∧
      (∑' n, μ {ω | ε * (|Zlim ω| + 1) + r n < |Z n ω - Zlim ω|}) ≠ ∞) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => Z n ω) atTop (𝓝 (Zlim ω)) := by
  have hpos : ∀ k : ℕ, (0 : ℝ) < 1 / (k + 1 : ℝ) := by
    intro k
    positivity
  choose r hr hsum using fun (k : ℕ) => h (1 / (k + 1 : ℝ)) (hpos k)
  have hae : ∀ k : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      ω ∉ {ω | (1 / (k + 1 : ℝ)) * (|Zlim ω| + 1) + r k n <
        |Z n ω - Zlim ω|} := fun k => ae_eventually_notMem (hsum k)
  rw [← eventually_countable_forall] at hae
  filter_upwards [hae] with ω hω
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (div_pos hε (by positivity : 0 < |Zlim ω| + 2))
  have hrk : ∀ᶠ n in atTop, r k n < 1 / (k + 1 : ℝ) :=
    (Metric.tendsto_nhds.1 (hr k) _ (hpos k)).mono fun n hn => by
      exact lt_of_le_of_lt (le_abs_self (r k n)) (by simpa [Real.dist_eq] using hn)
  filter_upwards [hω k, hrk] with n hn hn_r
  rw [Real.dist_eq]
  have hbound : |Z n ω - Zlim ω| ≤
      (1 / (k + 1 : ℝ)) * (|Zlim ω| + 1) + r k n := le_of_not_gt hn
  calc
    |Z n ω - Zlim ω| ≤
        (1 / (k + 1 : ℝ)) * (|Zlim ω| + 1) + r k n := hbound
    _ < (1 / (k + 1 : ℝ)) * (|Zlim ω| + 2) := by
      nlinarith [hpos k]
    _ < ε := by
      simpa [mul_comm] using
        (lt_div_iff₀' (by positivity : 0 < |Zlim ω| + 2)).mp hk

/-- A countable response family converges on one common full-measure event. -/
theorem ae_forall_tendsto_of_summable_relative_comparison
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {μ : Measure Ω}
    {Z : ι → ℕ → Ω → ℝ} {Zlim : ι → Ω → ℝ}
    (h : ∀ i, ∀ ε : ℝ, 0 < ε → ∃ r : ℕ → ℝ,
      Tendsto r atTop (𝓝 0) ∧
      (∑' n, μ {ω | ε * (|Zlim i ω| + 1) + r n < |Z i n ω - Zlim i ω|}) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ i, Tendsto (fun n => Z i n ω) atTop (𝓝 (Zlim i ω)) := by
  exact ae_all_iff.2 fun i =>
    ae_tendsto_of_summable_relative_comparison (h i)


/-- Geometric relative-comparison tails imply almost-sure convergence along the full sequence.
The constants and initial cutoff may depend on accuracy; the finite initial segment
is handled using the finiteness of the measure. -/
theorem ae_tendsto_of_geometric_relative_comparison
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Z : ℕ → Ω → ℝ} {Zlim : Ω → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∃ ρ : ℝ,
      0 ≤ ρ ∧ ρ < 1 ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
        μ {ω | ε * (|Zlim ω| + 1) + C * ρ ^ n < |Z n ω - Zlim ω|} ≤
          ENNReal.ofReal (C * ρ ^ n)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => Z n ω) atTop (𝓝 (Zlim ω)) := by
  apply ae_tendsto_of_summable_relative_comparison
  intro ε hε
  obtain ⟨C, hC, ρ, hρ, hρ_one, N₀, hbound⟩ := h ε hε
  refine ⟨fun n => C * ρ ^ n, ?_, ?_⟩
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ_one).const_mul C
  · let b : ℕ → ℝ := fun n =>
      (if n < N₀ then (μ Set.univ).toReal else 0) + C * ρ ^ n
    have hb_nonneg : ∀ n, 0 ≤ b n := by
      intro n
      dsimp [b]
      positivity
    have hgeom : Summable (fun n : ℕ => C * ρ ^ n) :=
      (summable_geometric_of_lt_one hρ hρ_one).mul_left C
    have hb_sum : Summable b := by
      apply hgeom.congr_atTop
      filter_upwards [eventually_ge_atTop N₀] with n hn
      simp only [b, if_neg (not_lt_of_ge hn), zero_add]
    have hmeasure : ∀ n,
        μ {ω | ε * (|Zlim ω| + 1) + C * ρ ^ n < |Z n ω - Zlim ω|} ≤
          ENNReal.ofReal (b n) := by
      intro n
      by_cases hn : n < N₀
      · calc
          μ {ω | ε * (|Zlim ω| + 1) + C * ρ ^ n < |Z n ω - Zlim ω|}
              ≤ μ Set.univ := measure_mono (subset_univ _)
          _ = ENNReal.ofReal (μ Set.univ).toReal :=
            (ENNReal.ofReal_toReal IsFiniteMeasure.measure_univ_lt_top.ne).symm
          _ ≤ ENNReal.ofReal (b n) := by
            apply ENNReal.ofReal_le_ofReal
            simp only [b, if_pos hn]
            exact le_add_of_nonneg_right (mul_nonneg hC (pow_nonneg hρ n))
      · calc
          μ {ω | ε * (|Zlim ω| + 1) + C * ρ ^ n < |Z n ω - Zlim ω|}
              ≤ ENNReal.ofReal (C * ρ ^ n) := hbound n (le_of_not_gt hn)
          _ = ENNReal.ofReal (b n) := by
            simp only [b, if_neg hn, zero_add]
    have hb_ofReal_ne_top : (∑' n, ENNReal.ofReal (b n)) ≠ ∞ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg hb_nonneg hb_sum]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top hb_ofReal_ne_top (ENNReal.tsum_le_tsum hmeasure)

end SubdiffusiveProcess
