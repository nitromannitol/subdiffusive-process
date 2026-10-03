module

public import SubdiffusiveProcess.Probability.PositiveTimeLaplace
public import SubdiffusiveProcess.Processes.PathTestIntegral
@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators BoundedContinuousFunction
namespace SubdiffusiveProcess

/-- Equality of integrated path tests gives equality at every positive cumulative time vector. -/
theorem path_product_expectation_eq_of_integrated_tests
    {d k : ℕ}
    [MeasurableSpace C(ℝ≥0, SpatialCoordinates d)]
    [BorelSpace C(ℝ≥0, SpatialCoordinates d)]
    (P Q : ProbabilityMeasure C(ℝ≥0, SpatialCoordinates d))
    (f : Fin k → (SpatialCoordinates d →ᵇ ℝ))
    (heq : ∀ m : Fin k → ℕ,
      (∫ z : C(ℝ≥0, SpatialCoordinates d),
        (∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i},
          Real.exp (-(∑ i : Fin k, (m i + 1 : ℝ) * s i)) *
            ∏ i : Fin k, f i (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))))
        ∂(P : Measure C(ℝ≥0, SpatialCoordinates d))) =
      ∫ z : C(ℝ≥0, SpatialCoordinates d),
        (∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i},
          Real.exp (-(∑ i : Fin k, (m i + 1 : ℝ) * s i)) *
            ∏ i : Fin k, f i (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))))
        ∂(Q : Measure C(ℝ≥0, SpatialCoordinates d)))
    (s : Fin k → ℝ) (hs : ∀ i, 0 < s i) :
    (∫ z : C(ℝ≥0, SpatialCoordinates d),
      ∏ i : Fin k, f i (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)))
      ∂(P : Measure C(ℝ≥0, SpatialCoordinates d))) =
    ∫ z : C(ℝ≥0, SpatialCoordinates d),
      ∏ i : Fin k, f i (z (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)))
      ∂(Q : Measure C(ℝ≥0, SpatialCoordinates d)) := by
  classical
  have hS : MeasurableSet {s : Fin k → ℝ | ∀ i, 0 < s i} := by
    rw [show {s : Fin k → ℝ | ∀ i, 0 < s i} =
        Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)) by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, Set.mem_Ioi, forall_const]]
    exact (measurableSet_pi Set.finite_univ.countable).2 <|
      Or.inl fun _ _ => measurableSet_Ioi
  let times : {s : Fin k → ℝ // ∀ i, 0 < s i} → (Fin k → ℝ≥0) :=
    fun u i => Real.toNNReal (∑ j ∈ Finset.Iic i, u.val j)
  have htimes : Continuous times := by
    dsimp only [times]
    fun_prop
  let C : ℝ := ∏ i : Fin k, ‖f i‖
  let mkExpectation (R : ProbabilityMeasure C(ℝ≥0, SpatialCoordinates d)) :
      {s : Fin k → ℝ // ∀ i, 0 < s i} →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨fun u => ∫ z : C(ℝ≥0, SpatialCoordinates d),
          ∏ i : Fin k, f i (z (times u i)) ∂(R : Measure C(ℝ≥0, SpatialCoordinates d)),
        (continuous_path_product_expectation R f).comp htimes⟩
      (2 * C) (by
        intro x y
        rw [Real.dist_eq]
        apply (abs_sub _ _).trans
        have hbound (u : {s : Fin k → ℝ // ∀ i, 0 < s i}) :
            |∫ z : C(ℝ≥0, SpatialCoordinates d),
              ∏ i : Fin k, f i (z (times u i)) ∂(R : Measure C(ℝ≥0, SpatialCoordinates d))| ≤ C := by
          rw [← Real.norm_eq_abs]
          calc
            ‖∫ z : C(ℝ≥0, SpatialCoordinates d),
                ∏ i : Fin k, f i (z (times u i)) ∂(R : Measure C(ℝ≥0, SpatialCoordinates d))‖
                ≤ ∫ _ : C(ℝ≥0, SpatialCoordinates d), C
                    ∂(R : Measure C(ℝ≥0, SpatialCoordinates d)) := by
                  apply norm_integral_le_of_norm_le (integrable_const C)
                  filter_upwards with z
                  rw [Real.norm_eq_abs, Finset.abs_prod]
                  exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ =>
                    BoundedContinuousFunction.norm_coe_le_norm (f i) _
            _ = C := by simp
        calc
          _ ≤ C + C := add_le_add (hbound x) (hbound y)
          _ = 2 * C := by ring)
  have hFG : mkExpectation P = mkExpectation Q := by
    apply boundedContinuous_eq_of_positiveInteger_laplace
    intro m
    have hraw : (∫ u in {u : Fin k → ℝ | ∀ i, 0 < u i},
        Real.exp (-(∑ i : Fin k, (m i + 1 : ℝ) * u i)) *
        (∫ z : C(ℝ≥0, SpatialCoordinates d),
          ∏ i : Fin k, f i (z (Real.toNNReal (∑ j ∈ Finset.Iic i, u j)))
          ∂(P : Measure C(ℝ≥0, SpatialCoordinates d)))) =
      ∫ u in {u : Fin k → ℝ | ∀ i, 0 < u i},
        Real.exp (-(∑ i : Fin k, (m i + 1 : ℝ) * u i)) *
        (∫ z : C(ℝ≥0, SpatialCoordinates d),
          ∏ i : Fin k, f i (z (Real.toNNReal (∑ j ∈ Finset.Iic i, u j)))
          ∂(Q : Measure C(ℝ≥0, SpatialCoordinates d))) := by
      rw [← integral_integrated_path_test P f (fun i => (m i + 1 : ℝ)) (fun i => by positivity),
        ← integral_integrated_path_test Q f (fun i => (m i + 1 : ℝ)) (fun i => by positivity)]
      exact heq m
    have hP := integral_subtype_comap (μ := volume) hS
      (fun u : Fin k → ℝ => Real.exp (-(∑ i : Fin k, (m i + 1 : ℝ) * u i)) *
        ∫ z : C(ℝ≥0, SpatialCoordinates d),
          ∏ i : Fin k, f i (z (Real.toNNReal (∑ j ∈ Finset.Iic i, u j)))
          ∂(P : Measure C(ℝ≥0, SpatialCoordinates d)))
    have hQ := integral_subtype_comap (μ := volume) hS
      (fun u : Fin k → ℝ => Real.exp (-(∑ i : Fin k, (m i + 1 : ℝ) * u i)) *
        ∫ z : C(ℝ≥0, SpatialCoordinates d),
          ∏ i : Fin k, f i (z (Real.toNNReal (∑ j ∈ Finset.Iic i, u j)))
          ∂(Q : Measure C(ℝ≥0, SpatialCoordinates d)))
    calc
      _ = ∫ u in {u : Fin k → ℝ | ∀ i, 0 < u i},
          Real.exp (-(∑ i : Fin k, (m i + 1 : ℝ) * u i)) *
            (∫ z : C(ℝ≥0, SpatialCoordinates d),
              ∏ i : Fin k, f i (z (Real.toNNReal (∑ j ∈ Finset.Iic i, u j)))
              ∂(P : Measure C(ℝ≥0, SpatialCoordinates d))) := by
                simpa only [mkExpectation, times] using! hP
      _ = _ := hraw
      _ = _ := by simpa only [mkExpectation, times] using! hQ.symm
  have hv := DFunLike.congr_fun hFG (⟨s, hs⟩ : {s : Fin k → ℝ // ∀ i, 0 < s i})
  simpa only [mkExpectation, times] using! hv


end SubdiffusiveProcess
