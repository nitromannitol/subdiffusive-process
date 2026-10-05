module

public import SubdiffusiveProcess.KilledFeller.KillPath
public import MarkovProcess.Semigroup.GeneratorResolvent
public import Mathlib.Topology.Compactness.Compact
public import SubdiffusiveProcess.KilledFeller.KilledLaplaceIntegrand

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.KilledFeller

/-- Compact sets of continuous paths have a common modulus at time zero. -/
theorem compact_paths_small_time {X : Type*} [PseudoMetricSpace X]
    (K : Set (ContinuousPath X)) (hK : IsCompact K) (r : ℝ) (hr : 0 < r) :
    ∃ h : ℝ≥0, 0 < h ∧ ∀ w ∈ K, ∀ t : ℝ≥0, t ≤ h → dist (w t) (w 0) < r := by
  have hc : Continuous (fun p : ℝ≥0 × ContinuousPath X => dist (p.2 p.1) (p.2 0)) :=
    (ContinuousEval.continuous_eval.comp (continuous_snd.prodMk continuous_fst)).dist
      ((continuous_eval_const 0).comp continuous_snd)
  have hevent : ∀ᶠ t : ℝ≥0 in 𝓝 0, ∀ w ∈ K, dist (w t) (w 0) < r :=
    hK.eventually_forall_of_forall_eventually fun w _ =>
      hc.continuousAt.eventually (isOpen_Iio.mem_nhds (by simpa only [dist_self, Set.mem_Iio] using hr))
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨⟨delta / 2, le_of_lt (half_pos hdelta)⟩,
    NNReal.coe_pos.mp (half_pos hdelta), ?_⟩
  intro w hw t ht
  have htball : t ∈ Metric.ball (0 : ℝ≥0) delta := by
    rw [Metric.mem_ball, NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg t.coe_nonneg]
    exact (show (t : ℝ) ≤ delta / 2 from ht).trans_lt (half_lt_self hdelta)
  exact hball htball w hw

/-- A compact-path complement majorant bounds every short-time displacement event. -/
theorem displacement_measure_le_of_compact
    {X : Type*} [PseudoMetricSpace X] (K : Set (ContinuousPath X))
    (r : ℝ) (h : ℝ≥0)
    (hsmall : ∀ w ∈ K, ∀ t : ℝ≥0, t ≤ h → dist (w t) (w 0) < r)
    (mu : Measure (ContinuousPath X)) (x : X)
    (hstart : ∀ᵐ w ∂mu, w 0 = x) :
    mu {w | ∃ t : ℝ≥0, t ≤ h ∧ r < dist (w t) x} ≤ mu Kᶜ := by
  apply measure_mono_ae
  filter_upwards [hstart] with w hw
  rintro ⟨t, ht, hdist⟩
  intro hwK
  have hlt := hsmall w hwK t ht
  rw [hw] at hlt
  exact (not_lt_of_gt hdist) hlt

/-- Killing near the starting point changes a zero-extended test by at most its modulus. -/
theorem killed_test_sub_le_of_small_displacement {d : ℕ}
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (hzero : ∀ x ∉ U, f x = 0)
    (r m : ℝ) (_hm : 0 ≤ m)
    (hmod : ∀ x y : SpatialCoordinates d, dist x y ≤ r → |f x - f y| ≤ m)
    (w : DiffusionPath d) (h t : ℝ≥0) (ht : t ≤ h)
    (hsmall : ∀ s : ℝ≥0, s ≤ h → dist (w s) (w 0) ≤ r) :
    |(if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0) - f (w 0)| ≤ m := by
  by_cases hlt : (t : ℝ≥0∞) < ContinuousPath.exitTime U w
  · rw [ite_eq_left hlt]
    exact hmod (w t) (w 0) (hsmall t ht)
  · rw [ite_eq_right hlt]
    obtain ⟨s, hs⟩ :=
      (ContinuousPath.exitTime_le_iff_mem_hitsSetBy U hU t w).mp (le_of_not_gt hlt)
    have hnear := hmod (w s) (w 0) (hsmall s (s.property.trans ht))
    rw [hzero _ hs] at hnear
    exact hnear

/-- The paper's normalized killed-resolvent estimate, including paths killed before h. -/
theorem killed_resolvent_normalization_bound {d : ℕ}
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (hzero : ∀ x ∉ U, f x = 0)
    (lam h r m : ℝ) (hlam : 0 < lam) (hh : 0 < h) (_hr : 0 < r) (hm : 0 ≤ m)
    (hmod : ∀ x y : SpatialCoordinates d, dist x y ≤ r → |f x - f y| ≤ m)
    (mu : Measure (DiffusionPath d)) [IsProbabilityMeasure mu]
    (x : SpatialCoordinates d) (hstart : ∀ᵐ w ∂mu, w 0 = x) :
    |lam * (∫ w, (∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U w}
          (fun s => Real.exp (-lam * s) * f (w (Real.toNNReal s))) t) ∂mu) - f x| ≤
      m + 2 * ‖f‖ * (Real.exp (-lam * h) +
        mu.real {w | ∃ t : ℝ≥0, (t : ℝ) ≤ h ∧ r < dist (w t) x}) := by
  classical
  let Bad : Set (DiffusionPath d) := {w | ∃ t : ℝ≥0, (t : ℝ) ≤ h ∧ r < dist (w t) x}
  have hBad : MeasurableSet Bad := (SubdiffusiveProcess.KilledFeller.isOpen_displacement_event x h r).measurableSet
  let V : DiffusionPath d → ℝ := fun w =>
    lam * (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * SubdiffusiveProcess.KilledFeller.killedTest U f w t)
  have hVmeas : Measurable V :=
    measurable_const.mul (SubdiffusiveProcess.KilledFeller.measurable_killedLaplace U hU f lam)
  have hVbound : ∀ w, |V w| ≤ ‖f‖ :=
    fun w => SubdiffusiveProcess.KilledFeller.abs_normalized_killedLaplace_le U f w hlam
  have hVint : Integrable V mu :=
    (integrable_const ‖f‖).mono' hVmeas.aestronglyMeasurable
      (Eventually.of_forall fun w => by simpa only [Real.norm_eq_abs] using hVbound w)
  let C : ℝ := m + 2 * ‖f‖ * Real.exp (-lam * h)
  have hC : 0 ≤ C := add_nonneg hm (mul_nonneg (by positivity) (Real.exp_pos _).le)
  have hpoint : ∀ᵐ w ∂mu, |V w - f x| ≤ C + 2 * ‖f‖ * Bad.indicator (fun _ => (1 : ℝ)) w := by
    filter_upwards [hstart] with w hw
    by_cases hbad : w ∈ Bad
    · rw [indicator_of_mem hbad, mul_one]
      calc
        |V w - f x| ≤ |V w| + |f x| := abs_sub _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add (hVbound w)
          (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x)
        _ ≤ C + 2 * ‖f‖ := by linarith only [hC]
    · rw [indicator_of_notMem hbad, mul_zero, add_zero]
      have hsmall : ∀ s : ℝ≥0, s ≤ Real.toNNReal h → dist (w s) (w 0) ≤ r := by
        intro s hs
        rw [hw]
        apply le_of_not_gt
        intro hd
        apply hbad
        refine ⟨s, ?_, hd⟩
        have hs' : (s : ℝ) ≤ (Real.toNNReal h : ℝ) := hs
        rwa [Real.coe_toNNReal h hh.le] at hs'
      have hnear : ∀ t ∈ Ioc (0 : ℝ) h,
          |SubdiffusiveProcess.KilledFeller.killedTest U f w t - f x| ≤ m := by
        intro t ht
        have ht' : Real.toNNReal t ≤ Real.toNNReal h := Real.toNNReal_mono ht.2
        have htest := killed_test_sub_le_of_small_displacement U hU f hzero r m hm hmod
          w (Real.toNNReal h) (Real.toNNReal t) ht' hsmall
        rw [hw] at htest
        exact htest
      have hbound : ∀ t ∈ Ioi (0 : ℝ),
          |SubdiffusiveProcess.KilledFeller.killedTest U f w t - f x| ≤ 2 * ‖f‖ := by
        intro t _
        calc
          |SubdiffusiveProcess.KilledFeller.killedTest U f w t - f x| ≤
              |SubdiffusiveProcess.KilledFeller.killedTest U f w t| + |f x| := abs_sub _ _
          _ ≤ ‖f‖ + ‖f‖ := add_le_add (SubdiffusiveProcess.KilledFeller.abs_killedTest_le U f w t)
            (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x)
          _ = 2 * ‖f‖ := (two_mul _).symm
      exact SubdiffusiveProcess.KilledFeller.normalized_laplace_deviation_bound
        (SubdiffusiveProcess.KilledFeller.killedTest U f w)
        ((SubdiffusiveProcess.KilledFeller.measurable_killedTest U hU f).comp measurable_prodMk_left)
        lam h (f x) m (2 * ‖f‖) hlam hh.le hm (by positivity) hbound hnear
  have hmajor : Integrable (fun w => C + 2 * ‖f‖ * Bad.indicator (fun _ => (1 : ℝ)) w) mu :=
    (integrable_const C).add (((integrable_const (1 : ℝ)).indicator hBad).const_mul (2 * ‖f‖))
  have hcompare : |∫ w, V w - f x ∂mu| ≤
      ∫ w, C + 2 * ‖f‖ * Bad.indicator (fun _ => (1 : ℝ)) w ∂mu := by
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le hmajor
    simpa only [Real.norm_eq_abs] using hpoint
  have hleft : lam * (∫ w, (∫ t in Ioi (0 : ℝ),
      {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U w}.indicator
        (fun s => Real.exp (-lam * s) * f (w (Real.toNNReal s))) t) ∂mu) - f x =
      ∫ w, V w - f x ∂mu := by
    simp_rw [SubdiffusiveProcess.KilledFeller.indicator_exp_eq_exp_killedTest]
    rw [integral_sub hVint (integrable_const (f x))]
    simp only [V, integral_const_mul, integral_const, probReal_univ, smul_eq_mul,
      one_mul]
  have hBI : (∫ w, Bad.indicator (fun _ => (1 : ℝ)) w ∂mu) = mu.real Bad := by
    simpa only [smul_eq_mul, mul_one] using (integral_indicator_const (1 : ℝ) hBad :
      (∫ w, Bad.indicator (fun _ => (1 : ℝ)) w ∂mu) = mu.real Bad • (1 : ℝ))
  rw [hleft]
  calc
    |∫ w, V w - f x ∂mu| ≤
        ∫ w, C + 2 * ‖f‖ * Bad.indicator (fun _ => (1 : ℝ)) w ∂mu := hcompare
    _ = m + 2 * ‖f‖ * (Real.exp (-lam * h) + mu.real Bad) := by
      rw [integral_add (integrable_const C)
        (((integrable_const (1 : ℝ)).indicator hBad).const_mul (2 * ‖f‖)),
        integral_const_mul, hBI]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, C]
      ring

end SubdiffusiveProcess.KilledFeller
