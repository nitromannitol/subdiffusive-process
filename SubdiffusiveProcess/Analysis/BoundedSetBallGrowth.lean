import SubdiffusiveProcess.Analysis.MeasureBallGrowth
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! A finite cover converts interior ball-growth estimates into total mass and
arbitrary-centre estimates on relatively compact sets. No random bounds are asserted. -/

open MeasureTheory Set Metric
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess

/-- A relatively compact set has a uniform geometric factor for interior ball-growth estimates. -/
theorem boundedSet_measure_ball_growth
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (q : Set X) (hq : IsCompact (closure q)) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (mu : Measure X) (K t : ℝ), 0 ≤ K → 0 ≤ t →
      (∀ x ∈ q, ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
        mu (ball x rho ∩ q) ≤ ENNReal.ofReal (K * rho ^ t)) →
      mu q ≤ ENNReal.ofReal (A * K) ∧
      ∀ (x : X) (rho : ℝ), 0 < rho → rho ≤ 1 →
        mu (ball x rho ∩ q) ≤ ENNReal.ofReal ((2 ^ t * (A * K)) * rho ^ t) := by
  classical
  obtain ⟨s, hsq, hs, hcover⟩ :=
    exists_finite_cover_balls_of_isCompact_closure hq (by norm_num : (0 : ℝ) < 1)
  let F := hs.toFinset
  let A : ℝ := (F.card : ℝ) + 1
  have hA : 1 ≤ A := by
    dsimp only [A]
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  refine ⟨A, hA, ?_⟩
  intro mu K t hK ht hg
  have hmass : mu q ≤ ENNReal.ofReal (A * K) := by
    have hsub : q ⊆ ⋃ x ∈ F, ball x 1 ∩ q := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
      exact mem_iUnion₂.mpr ⟨y, hs.mem_toFinset.mpr hy, hxy, hx⟩
    calc
      mu q ≤ mu (⋃ x ∈ F, ball x 1 ∩ q) := measure_mono hsub
      _ ≤ ∑ x ∈ F, mu (ball x 1 ∩ q) := measure_biUnion_finset_le F _
      _ ≤ ∑ _x ∈ F, ENNReal.ofReal K := by
        apply Finset.sum_le_sum
        intro x hx
        simpa only [Real.one_rpow, mul_one] using
          hg x (hsq (hs.mem_toFinset.mp hx)) 1 one_pos le_rfl
      _ = ENNReal.ofReal ((F.card : ℝ) * K) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (A * K) := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by dsimp only [A]; linarith only []) hK)
  refine ⟨hmass, ?_⟩
  intro x rho hrho _hrho1
  have hfactor : A * K * (2 * rho) ^ t = (2 ^ t * (A * K)) * rho ^ t := by
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
        exact (dist_triangle a x y).trans_lt (by linarith only [hx, hy])
      refine (measure_mono hsub).trans ((hg y hyq (2 * rho) (by positivity) hsmall).trans ?_)
      rw [← hfactor]
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hK hA)
        (Real.rpow_nonneg (by positivity) _)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]
      exact zero_le _
  · have hscale : 1 ≤ (2 * rho) ^ t := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow
        (by norm_num : (0 : ℝ) ≤ 1) (by linarith only [hsmall] : 1 ≤ 2 * rho) ht
    refine (measure_mono inter_subset_right).trans (hmass.trans (ENNReal.ofReal_le_ofReal ?_))
    rw [← hfactor]
    exact le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans hA) hK) hscale

end SubdiffusiveProcess
