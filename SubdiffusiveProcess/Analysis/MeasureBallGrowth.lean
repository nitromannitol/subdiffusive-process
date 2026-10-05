module

public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SubdiffusiveProcess

/-- A ball-growth estimate with centres in a small cell gives the estimate
for arbitrary centres, with only the geometric factor `2 ^ t`. -/
theorem measure_ball_inter_growth_of_centers_mem
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (mu : Measure X) (q : Set X) (z : X) (hz : z ∈ q)
    (hq : q ⊆ ball z 1) (K t : ℝ) (hK : 0 ≤ K) (ht : 0 ≤ t)
    (hg : ∀ x ∈ q, ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      mu (ball x rho ∩ q) ≤ ENNReal.ofReal (K * rho ^ t)) :
    ∀ (x : X) (rho : ℝ), 0 < rho → rho ≤ 1 →
      mu (ball x rho ∩ q) ≤ ENNReal.ofReal ((2 ^ t * K) * rho ^ t) := by
  intro x rho hrho _hrho1
  have hfactor : K * (2 * rho) ^ t = (2 ^ t * K) * rho ^ t := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hrho.le]
    ring
  by_cases hsmall : 2 * rho ≤ 1
  · by_cases hne : (ball x rho ∩ q).Nonempty
    · obtain ⟨y, hyx, hyq⟩ := hne
      have hsub : ball x rho ∩ q ⊆ ball y (2 * rho) ∩ q := by
        rintro a ⟨hax, haq⟩
        refine ⟨?_, haq⟩
        have hx : dist a x < rho := hax
        have hy : dist x y < rho := by simpa only [Metric.mem_ball, dist_comm] using hyx
        exact (dist_triangle a x y).trans_lt (by linarith)
      refine (measure_mono hsub).trans ((hg y hyq (2 * rho) (by positivity) hsmall).trans_eq ?_)
      rw [hfactor]
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]
      exact bot_le
  · have hmass : mu q ≤ ENNReal.ofReal K := by
      simpa only [inter_eq_right.mpr hq, Real.one_rpow, mul_one] using hg z hz 1 one_pos le_rfl
    have hscale : 1 ≤ (2 * rho) ^ t := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 1 ≤ 2 * rho) ht
    refine (measure_mono inter_subset_right).trans (hmass.trans (ENNReal.ofReal_le_ofReal ?_))
    rw [← hfactor]
    exact le_mul_of_one_le_right hK hscale

end SubdiffusiveProcess

