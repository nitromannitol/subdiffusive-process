import Mathlib
import MarkovProcess.Path.ExitTime
import SubdiffusiveProcess.Main.DiffusionPath
open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace Paper

/-- Source L:147–150. Pool order `astra10_0927_summable_exits`; independently harvested. -/
theorem aux_lim_nonbrownian_summable_exits
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (s : ℕ → Ω → ℝ≥0∞) (hs : ∀ n, Measurable (s n))
    (hint : (∑' n, ∫⁻ w, s n w ∂P) ≠ ⊤) :
    ∀ᵐ w ∂P, Tendsto (fun n => s n w) atTop (𝓝 0) := by
    have hF_meas : Measurable (fun w => ∑' n, s n w) := Measurable.ennreal_tsum hs
    have hF_int : ∫⁻ w, (∑' n, s n w) ∂P = ∑' n, ∫⁻ w, s n w ∂P :=
      lintegral_tsum (fun n => (hs n).aemeasurable)
    have hF_lt : ∀ᵐ w ∂P, (∑' n, s n w) < ⊤ :=
      MeasureTheory.ae_lt_top hF_meas (by rw [hF_int]; exact hint)
    filter_upwards [hF_lt] with w hw
    exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top (ne_of_lt hw)

/-- Source L:151–161. Pool order `astra10_0927_mixture_carrier`; independently harvested. -/
theorem aux_lim_nonbrownian_mixture_carrier
    {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ]
    (P : Measure X) (nu : Measure Θ) (kappa : Kernel Θ X)
    (E : Set X) (hE : MeasurableSet E) (hP : P Eᶜ = 0)
    (hQ : ∀ θ, kappa θ E = 0) : P ⟂ₘ nu.bind kappa := by
  refine ⟨Eᶜ, hE.compl, hP, ?_⟩
  rw [compl_compl, Measure.bind_apply hE kappa.aemeasurable]
  simp only [hQ, lintegral_zero]

/-- Source L:163–169. Pool order `astra10_0927_barycentre_carrier`; independently harvested. -/
theorem aux_lim_nonbrownian_barycentre_carrier
    {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ]
    (nu : Measure Θ) (kappa : Kernel Θ X) (E : Set X)
    (hE : MeasurableSet E) (hbar : (nu.bind kappa) Eᶜ = 0) :
    ∀ᵐ θ ∂nu, kappa θ Eᶜ = 0 := by
  have hmeas : Measurable (fun θ => kappa θ Eᶜ) := Kernel.measurable_coe kappa hE.compl
  rw [Measure.bind_apply hE.compl (Kernel.aemeasurable kappa)] at hbar
  exact (MeasureTheory.lintegral_eq_zero_iff hmeas).mp hbar

/-- Source L:194–203. Pool order `astra10_0927_markov_bc`; independently harvested. -/
theorem aux_lim_paths_markov_bc
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (s : ℕ → Ω → ℝ≥0∞) (hs : ∀ n, Measurable (s n))
    (a : ℕ → ℝ≥0∞) (ha0 : ∀ n, a n ≠ 0) (hat : ∀ n, a n ≠ ⊤)
    (hint : (∑' n, (∫⁻ w, s n w ∂P) / a n) ≠ ⊤) :
    ∀ᵐ w ∂P, ∀ᶠ n in atTop, s n w < a n := by
  have h_bound : ∀ n, P {w | a n ≤ s n w} ≤ (∫⁻ w, s n w ∂P) / a n := by
    intro n
    exact MeasureTheory.meas_ge_le_lintegral_div (μ := P) (f := s n) (hs n).aemeasurable (ha0 n) (hat n)
  have h_le : (∑' n, P {w | a n ≤ s n w}) ≤ ∑' n, (∫⁻ w, s n w ∂P) / a n :=
    ENNReal.tsum_le_tsum h_bound
  have h_ne : (∑' n, P {w | a n ≤ s n w}) ≠ ⊤ := by
    intro htop
    have hle' : (⊤ : ℝ≥0∞) ≤ ∑' n, (∫⁻ w, s n w ∂P) / a n := by
      rw [← htop]
      exact h_le
    exact hint (top_le_iff.mp hle')
  filter_upwards [MeasureTheory.ae_eventually_notMem (μ := P) (s := fun n => {w | a n ≤ s n w}) h_ne] with w hw
  exact hw.mono (fun n hn => by
    simpa only [Set.mem_setOf_eq, not_le] using hn)

end Paper
