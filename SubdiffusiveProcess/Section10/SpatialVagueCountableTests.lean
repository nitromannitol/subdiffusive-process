module

public import SubdiffusiveProcess.Section10.SpatialVagueEvaluations
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.UrysohnsLemma

@[expose] public section

/-! Dense real compact tests in fixed compact windows, together with
nonnegative compact tests controlling the mass of each window. -/

open MeasureTheory SubdiffusiveProcess Filter Topology Set TopologicalSpace
open scoped CompactlySupported ENNReal

noncomputable section
namespace SubdiffusiveProcess.Section10

def spatialTestWindow (d n : ℕ) : Set (SpatialCoordinates d) :=
  Metric.closedBall 0 ((n : ℝ) + 1)

instance spatialTestWindowCompact (d n : ℕ) : CompactSpace (spatialTestWindow d n) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : SpatialCoordinates d) ((n : ℝ) + 1))

abbrev SupportedSpatialTest (d n : ℕ) :=
  {f : C_c(SpatialCoordinates d, ℝ) // tsupport (f : SpatialCoordinates d → ℝ) ⊆
    spatialTestWindow d n}

def supportedTestRestriction {d n : ℕ} (f : SupportedSpatialTest d n) :
    C(spatialTestWindow d n, ℝ) := f.val.toContinuousMap.restrict _

instance supportedSpatialTestPseudoMetric (d n : ℕ) :
    PseudoMetricSpace (SupportedSpatialTest d n) :=
  PseudoMetricSpace.induced supportedTestRestriction inferInstance

instance supportedSpatialTestSecondCountable (d n : ℕ) :
    SecondCountableTopology (SupportedSpatialTest d n) :=
  secondCountableTopology_induced _ _ supportedTestRestriction

instance supportedSpatialTestNonempty (d n : ℕ) : Nonempty (SupportedSpatialTest d n) :=
  ⟨⟨0, by simp⟩⟩

def spatialDenseTest (d n j : ℕ) : C_c(SpatialCoordinates d, ℝ) :=
  (denseSeq (SupportedSpatialTest d n) j).val

theorem exists_spatialDenseTest_approx {d n : ℕ} (f : C_c(SpatialCoordinates d, ℝ))
    (hf : tsupport (f : SpatialCoordinates d → ℝ) ⊆ spatialTestWindow d n)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ j : ℕ, ∀ x ∈ spatialTestWindow d n, |spatialDenseTest d n j x - f x| < eps := by
  obtain ⟨j, hj⟩ := (denseRange_denseSeq (SupportedSpatialTest d n)).exists_dist_lt
    ⟨f, hf⟩ heps
  refine ⟨j, fun x hx => ?_⟩
  have hb := ContinuousMap.dist_apply_le_dist
    (f := supportedTestRestriction (denseSeq (SupportedSpatialTest d n) j))
    (g := supportedTestRestriction ⟨f, hf⟩) ⟨x, hx⟩
  exact (show |spatialDenseTest d n j x - f x| ≤
    dist (denseSeq (SupportedSpatialTest d n) j) ⟨f, hf⟩ by
      simpa only [Real.dist_eq, supportedTestRestriction, ContinuousMap.restrict_apply, spatialDenseTest] using! hb).trans_lt
        (by simpa only [dist_comm] using hj)

theorem exists_spatialTestWindow_support {d : ℕ} (f : C_c(SpatialCoordinates d, ℝ)) :
    ∃ n, tsupport (f : SpatialCoordinates d → ℝ) ⊆ spatialTestWindow d n := by
  obtain ⟨r, hr⟩ := f.hasCompactSupport.isBounded.subset_closedBall (0 : SpatialCoordinates d)
  obtain ⟨n, hn⟩ := exists_nat_ge r
  exact ⟨n, hr.trans (Metric.closedBall_subset_closedBall (by linarith))⟩

theorem exists_spatial_mass_test (d n : ℕ) :
    ∃ g : C_c(SpatialCoordinates d, ℝ),
      (∀ x, 0 ≤ g x) ∧ ∀ x ∈ spatialTestWindow d n, g x = 1 := by
  obtain ⟨g, hg, hgc, _, h01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    (isCompact_closedBall (0 : SpatialCoordinates d) ((n : ℝ) + 1))
    (Metric.isOpen_ball (x := (0 : SpatialCoordinates d)) (ε := ((n : ℝ) + 2)))
    (Metric.closedBall_subset_ball (by linarith : (n : ℝ) + 1 < n + 2))
  exact ⟨⟨g, hgc⟩, fun x => (h01 x).1, fun x hx => hg hx⟩

def spatialMassTest (d n : ℕ) : C_c(SpatialCoordinates d, ℝ) :=
  Classical.choose (exists_spatial_mass_test d n)

theorem spatialMassTest_spec (d n : ℕ) :
    (∀ x, 0 ≤ spatialMassTest d n x) ∧
      ∀ x ∈ spatialTestWindow d n, spatialMassTest d n x = 1 :=
  Classical.choose_spec (exists_spatial_mass_test d n)

theorem spatial_window_mass_le_test {d n : ℕ} (mu : LocallyFiniteSpatialMeasure d) :
    mu.val.real (spatialTestWindow d n) ≤ ∫ x, spatialMassTest d n x ∂mu.val := by
  letI := mu.property
  let K := spatialTestWindow d n
  have hK : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
  haveI : IsFiniteMeasure (mu.val.restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ, K, spatialTestWindow] using
      (isCompact_closedBall (0 : SpatialCoordinates d) ((n : ℝ) + 1)).measure_lt_top⟩
  have hi : Integrable (K.indicator (fun _ => (1 : ℝ))) mu.val :=
    (integrable_indicator_iff hK).mpr (integrable_const 1)
  calc mu.val.real K = ∫ x, K.indicator (fun _ => (1 : ℝ)) x ∂mu.val := by
        simp [integral_indicator hK]
    _ ≤ ∫ x, spatialMassTest d n x ∂mu.val :=
      integral_mono hi (integrable_spatialVagueTest mu _) (fun x => by
        by_cases hx : x ∈ K
        · simp only [Set.indicator_of_mem hx, (spatialMassTest_spec d n).2 x hx, le_refl]
        · simp only [Set.indicator_of_notMem hx]
          exact (spatialMassTest_spec d n).1 x)

/-- Uniform approximation on a common compact support bounds the integral
error by the compact mass, for the literal locally finite measure. -/
theorem spatial_test_integral_error {d n : ℕ} (mu : LocallyFiniteSpatialMeasure d)
    (f g : C_c(SpatialCoordinates d, ℝ))
    (hf : tsupport (f : SpatialCoordinates d → ℝ) ⊆ spatialTestWindow d n)
    (hg : tsupport (g : SpatialCoordinates d → ℝ) ⊆ spatialTestWindow d n)
    (eps : ℝ) (happrox : ∀ x ∈ spatialTestWindow d n, |f x - g x| ≤ eps) :
    |(∫ x, f x ∂mu.val) - ∫ x, g x ∂mu.val| ≤ eps * mu.val.real (spatialTestWindow d n) := by
  letI := mu.property
  let K := spatialTestWindow d n
  have hK : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
  haveI : IsFiniteMeasure (mu.val.restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ, K, spatialTestWindow] using
      (isCompact_closedBall (0 : SpatialCoordinates d) ((n : ℝ) + 1)).measure_lt_top⟩
  rw [← integral_sub (integrable_spatialVagueTest mu f) (integrable_spatialVagueTest mu g)]
  have heq : (∫ x in K, (f x - g x) ∂mu.val) = ∫ x, (f x - g x) ∂mu.val :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hf0 : f x = 0 := by
        by_contra hn
        exact hx (hf (subset_tsupport _ hn))
      have hg0 : g x = 0 := by
        by_contra hn
        exact hx (hg (subset_tsupport _ hn))
      simp [hf0, hg0])
  rw [← heq, ← Real.norm_eq_abs]
  have hb := norm_integral_le_of_norm_le_const (μ := mu.val.restrict K)
    (f := fun x => f x - g x) (by
      filter_upwards [ae_restrict_mem hK] with x hx
      simpa only [Real.norm_eq_abs] using happrox x hx)
  simpa only [measureReal_def, Measure.restrict_apply_univ] using hb

end SubdiffusiveProcess.Section10
