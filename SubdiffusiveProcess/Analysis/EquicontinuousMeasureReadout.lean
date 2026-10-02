import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.MetricSpace.Basic

open Filter MeasureTheory Topology
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Analysis

/-- Convergence in measure of representatives with a common local modulus gives
pointwise convergence at each point in the support of the measure. -/
theorem tendsto_at_support_of_tendstoInMeasure_of_common_modulus
    {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (nu : Measure X) (f : ℕ → X → ℝ) (g : X → ℝ)
    (hprob : TendstoInMeasure nu f atTop g) (x : X)
    (hpos : ∀ delta : ℝ, 0 < delta → 0 < nu (Metric.ball x delta))
    (hmod : ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ y ∈ Metric.ball x delta,
        (∀ n, |f n y - f n x| < eps) ∧ |g y - g x| < eps) :
    Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨delta, hdelta, hlocal⟩ := hmod (eps / 4) (by positivity)
  have hb : Tendsto (fun n => nu {y | eps / 2 ≤ dist (f n y) (g y)}) atTop (𝓝 0) :=
    (tendstoInMeasure_iff_dist.mp hprob) (eps / 2) (by positivity)
  have hevent : ∀ᶠ n in atTop,
      nu {y | eps / 2 ≤ dist (f n y) (g y)} < nu (Metric.ball x delta) :=
    hb.eventually (eventually_lt_nhds (hpos delta hdelta))
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hevent
  refine ⟨N0, fun n hn => ?_⟩
  by_contra hbad
  have hbad' : eps ≤ |f n x - g x| := by simpa only [Real.dist_eq, not_lt] using hbad
  have hsub : Metric.ball x delta ⊆ {y | eps / 2 ≤ dist (f n y) (g y)} := by
    intro y hy
    obtain ⟨hf, hg⟩ := hlocal y hy
    have htri : |f n x - g x| ≤ |f n x - f n y| + |f n y - g y| + |g y - g x| := by
      calc
        _ = |(f n x - f n y) + (f n y - g y) + (g y - g x)| := by congr 1; ring
        _ ≤ _ := by
          have h1 := norm_add_le ((f n x - f n y) + (f n y - g y)) (g y - g x)
          have h2 := norm_add_le (f n x - f n y) (f n y - g y)
          simp only [Real.norm_eq_abs] at h1 h2
          linarith
    have hfx : |f n x - f n y| < eps / 4 := by simpa only [abs_sub_comm] using hf n
    change eps / 2 ≤ dist (f n y) (g y)
    rw [Real.dist_eq]
    linarith
  exact not_lt_of_ge (measure_mono hsub) (hN0 n hn)

end SubdiffusiveProcess.Analysis
