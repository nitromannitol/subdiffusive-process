module

public import SubdiffusiveProcess.Sobolev.WeakGradient
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

@[expose] public section

open MeasureTheory Set TopologicalSpace
namespace SubdiffusiveProcess

/-- Local integrability of the radial power used to dominate fractional differences; the ambient max norm is only the dominating kernel. -/
theorem integrableOn_norm_rpow_ball
    {d : ℕ} (hd : 0 < d) (q R : ℝ) (hq : -(d : ℝ) < q) :
    IntegrableOn (fun x : SpatialCoordinates d => ‖x‖ ^ q)
      (Metric.ball (0 : SpatialCoordinates d) R) := by
  by_cases hR : 0 < R
  · letI : Inhabited (Fin d) := ⟨⟨0, hd⟩⟩
    letI : Nontrivial (SpatialCoordinates d) := Pi.nontrivial
    rw [← integrable_indicator_iff Metric.isOpen_ball.measurableSet]
    have hfun :
        (Metric.ball (0 : SpatialCoordinates d) R).indicator
            (fun x : SpatialCoordinates d => ‖x‖ ^ q) =
          fun x => (Iio R).indicator (fun t : ℝ => t ^ q) ‖x‖ := by
      funext x
      by_cases hx : x ∈ Metric.ball (0 : SpatialCoordinates d) R
      · rw [indicator_of_mem hx, indicator_of_mem]
        simpa only [mem_Iio, dist_zero_right] using Metric.mem_ball.mp hx
      · rw [indicator_of_notMem hx, indicator_of_notMem]
        intro hnorm
        apply hx
        apply Metric.mem_ball.mpr
        simpa only [mem_Iio, dist_zero_right] using hnorm
    rw [hfun, MeasureTheory.integrable_fun_norm_addHaar volume]
    rw [← integrable_indicator_iff measurableSet_Ioi]
    have hexp : -1 < (d : ℝ) - 1 + q := by linarith
    have hpow : IntegrableOn (fun y : ℝ => y ^ ((d : ℝ) - 1 + q)) (Ioo 0 R) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hR).2 hexp
    apply (hpow.integrable_indicator measurableSet_Ioo).congr
    filter_upwards [] with y
    simp only [Module.finrank_fin_fun, indicator_apply, mem_Ioi, mem_Iio, mem_Ioo,
      smul_eq_mul]
    by_cases hy : 0 < y
    · by_cases hyR : y < R
      · simp only [hy, hyR, and_self, if_true]
        rw [← Real.rpow_natCast, ← Real.rpow_add hy]
        congr 2
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd))]
        norm_num
      · simp [hy, hyR]
    · simp [hy]
  · have : Metric.ball (0 : SpatialCoordinates d) R = ∅ := by
      rw [Metric.ball_eq_empty]
      exact le_of_not_gt hR
    rw [this]
    exact integrableOn_empty

end SubdiffusiveProcess
