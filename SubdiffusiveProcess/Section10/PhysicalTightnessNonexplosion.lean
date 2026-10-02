import SubdiffusiveProcess.Section10.PhysicalTightnessPointwise
import MarkovProcess.Lifetime.Nonexplosion

/-!
# Nonexplosion from annealed compact containment

An arbitrarily small measurable majorant yields one full event carrying zero mass
simultaneously for every starting point in the specified set; no measurability of
an uncountable supremum and no exceptional-start removal are used. Countable
intersection over cutoffs, integer time horizons and a compact exhaustion proves
nonexplosion of the actual supplied lifetime laws. This is paper §8, Step 2.
The quantitative containment estimate itself is a separate, explicit input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness

/-- Vanishing annealed majorants remove every starting point simultaneously,
without a measurable supremum assumption. -/
theorem ae_forall_eq_zero_of_majorants {Ω Z : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (B : Set Z) (f : Ω → Z → ENNReal)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ G : Ω → ENNReal, Measurable G ∧
      (∀ᵐ ω ∂μ, ∀ x ∈ B, f ω x ≤ G ω) ∧ ∫⁻ ω, G ω ∂μ ≤ ENNReal.ofReal ε) :
    ∀ᵐ ω ∂μ, ∀ x ∈ B, f ω x = 0 := by
  have hpos : ∀ n : ℕ, 0 < (1 / 2 : ℝ) ^ n := fun n => pow_pos (by norm_num) n
  choose G hG hpoint hmoment using fun n => hsmall ((1 / 2 : ℝ) ^ n) (hpos n)
  let F : Ω → ENNReal := fun ω => ⨅ n : ℕ, G n ω
  have hF : Measurable F := Measurable.iInf hG
  have hint : ∀ n : ℕ, (∫⁻ ω, F ω ∂μ) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
    intro n
    exact (lintegral_mono (fun ω => iInf_le (fun k => G k ω) n)).trans (hmoment n)
  have htend : Tendsto (fun n : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) := by
    have hr : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hr
  have hzero : ∫⁻ ω, F ω ∂μ = 0 := le_antisymm (ge_of_tendsto' htend hint) (zero_le _)
  have hae : F =ᵐ[μ] 0 := (lintegral_eq_zero_iff hF).mp hzero
  filter_upwards [hae, ae_all_iff.mpr hpoint] with ω hω hωpoint
  intro x hx
  apply le_antisymm _ (zero_le _)
  have h : f ω x ≤ F ω := le_iInf fun n => hωpoint n x hx
  simpa only [hω] using h

/-- A containment estimate at every integer horizon, arbitrarily small in
annealed expectation, implies simultaneous all-start nonexplosion. The exit
domain may vary with the requested error. -/
theorem nonexplosion_of_annealed_containment {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    (LN : ℕ → Kernel (Ω × Vec d) (Path d))
    (hcontain : ∀ N n m : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ (U : Set (Vec d)) (G : Ω → ENNReal), Measurable G ∧
        (∀ᵐ ω ∂μ, ∀ x ∈ Metric.closedBall (0 : Vec d) (m : ℝ),
          LN N (ω, x) {w | LifetimePath.exitTime U w ≤ (n : ENNReal)} ≤ G ω) ∧
        ∫⁻ ω, G ω ∂μ ≤ ENNReal.ofReal ε) :
    ∀ᵐ ω ∂μ, ∀ N : ℕ, ∀ x : Vec d,
      ∀ᵐ w ∂LN N (ω, x), w.lifetime = ⊤ := by
  have hzero : ∀ N n m : ℕ, ∀ᵐ ω ∂μ,
      ∀ x ∈ Metric.closedBall (0 : Vec d) (m : ℝ),
        LN N (ω, x) {w | w.lifetime ≤ (n : ENNReal)} = 0 := by
    intro N n m
    apply ae_forall_eq_zero_of_majorants μ (Metric.closedBall (0 : Vec d) (m : ℝ))
      (fun ω x => LN N (ω, x) {w | w.lifetime ≤ (n : ENNReal)})
    intro ε hε
    obtain ⟨U, G, hG, hpoint, hmoment⟩ := hcontain N n m ε hε
    refine ⟨G, hG, ?_, hmoment⟩
    filter_upwards [hpoint] with ω hω
    intro x hx
    exact (measure_mono (fun w hw =>
      (LifetimePath.exitTime_le_lifetime U w).trans hw)).trans (hω x hx)
  have hall : ∀ᵐ ω ∂μ, ∀ N n m : ℕ,
      ∀ x ∈ Metric.closedBall (0 : Vec d) (m : ℝ),
        LN N (ω, x) {w | w.lifetime ≤ (n : ENNReal)} = 0 :=
    ae_all_iff.mpr fun N => ae_all_iff.mpr fun n => ae_all_iff.mpr (hzero N n)
  filter_upwards [hall] with ω hω
  intro N x
  obtain ⟨m, hm⟩ := exists_nat_gt (dist x (0 : Vec d))
  have hx : x ∈ Metric.closedBall (0 : Vec d) (m : ℝ) := Metric.mem_closedBall.mpr hm.le
  have halive : ∀ n : ℕ, ∀ᵐ w ∂LN N (ω, x),
      ¬ w.lifetime ≤ (n : ENNReal) := fun n =>
    (measure_eq_zero_iff_ae_notMem.mp (hω N n m x hx))
  filter_upwards [ae_all_iff.mpr halive] with w hw
  by_contra hfinite
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hfinite
  exact hw n hn.le

end SubdiffusiveProcess.Section10.PhysicalTightness
