import SubdiffusiveProcess.Section10.GaussianDichotomy
import SubdiffusiveProcess.Section10.HyperplaneGrowth




open MeasureTheory ProbabilityTheory SubdiffusiveProcess

noncomputable section

namespace SubdiffusiveProcess.Section10

/-- Singularity of pushforwards pulls back under a measurable observation. -/
theorem mutuallySingular_of_map
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P Q : Measure X) (f : X → Y) (hf : Measurable f)
    (h : P.map f ⟂ₘ Q.map f) : P ⟂ₘ Q := by
  obtain ⟨A, hA, hP, hQ⟩ := h
  refine ⟨f ⁻¹' A, hf hA, ?_, ?_⟩
  · rwa [Measure.map_apply hf hA] at hP
  · rw [← Set.preimage_compl]
    rwa [Measure.map_apply hf hA.compl] at hQ

/-- A measure singular to volume and null on proper affine hyperplanes is
mutually singular with every Gaussian, including covariance rank zero. -/
theorem mutuallySingular_gaussian_of_hyperplane_null
    {d : ℕ} (mu G : Measure (SpatialCoordinates d)) [IsGaussian G]
    (hs : mu ⟂ₘ volume)
    (hplanes : ∀ L : StrongDual ℝ (SpatialCoordinates d), L ≠ 0 →
      ∀ a : ℝ, mu {x | L x = a} = 0) : mu ⟂ₘ G := by
  rcases Paper.aux_lim_nongaussian_gaussian_dichotomy G with hG | ⟨L, hL, a, ha⟩
  · exact hs.mono_ac Measure.AbsolutelyContinuous.rfl hG
  · refine ⟨{x | L x = a}, (isClosed_eq L.continuous continuous_const).measurableSet,
      hplanes L hL a, ?_⟩
    exact ha

/-- G1: every transition measure dominated by the same singular, hyperplane-null
measure is singular to volume and to every Gaussian law. Local finiteness and
probability normalization are not needed for this implication. -/
theorem dominated_measure_gaussian_singular
    {d : ℕ} (mu P : Measure (SpatialCoordinates d))
    (hs : mu ⟂ₘ volume)
    (hplanes : ∀ L : StrongDual ℝ (SpatialCoordinates d), L ≠ 0 →
      ∀ a : ℝ, mu {x | L x = a} = 0)
    (hP : P ≪ mu) :
    P ⟂ₘ volume ∧ ∀ G : Measure (SpatialCoordinates d), IsGaussian G → P ⟂ₘ G := by
  refine ⟨hs.mono_ac hP Measure.AbsolutelyContinuous.rfl, ?_⟩
  intro G hG
  letI : IsGaussian G := hG
  exact (mutuallySingular_gaussian_of_hyperplane_null mu G hs hplanes).mono_ac
    hP Measure.AbsolutelyContinuous.rfl

/-- The paper's existing local growth export supplies all affine-hyperplane
nullity at once, for arbitrary spatial dimension `d ≥ 2`. -/
theorem dominated_measure_gaussian_singular_of_local_growth
    {d : ℕ} (hd : 2 ≤ d) (mu P : Measure (SpatialCoordinates d)) [NoAtoms mu]
    (hs : mu ⟂ₘ volume)
    (hg : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1),
        ∀ r : ℝ, 0 < r → r ≤ 1 →
          mu (Metric.ball x r) ≤ ENNReal.ofReal (K * r ^ ((d : ℝ) - 1 / 2)))
    (hP : P ≪ mu) :
    P ⟂ₘ volume ∧ ∀ G : Measure (SpatialCoordinates d), IsGaussian G → P ⟂ₘ G := by
  exact dominated_measure_gaussian_singular mu P hs
    (Paper.aux_lim_nongaussian_hyperplanes_of_local_growth hd mu hg) hP

end SubdiffusiveProcess.Section10
