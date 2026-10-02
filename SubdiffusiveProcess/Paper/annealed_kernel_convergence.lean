import SubdiffusiveProcess.Paper.prop_as_quenched
import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
import SubdiffusiveProcess.Main.PathLevyProkhorovDist
import SubdiffusiveProcess.Main.ChaosSampleLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory SubdiffusiveProcess Topology
open scoped ENNReal NNReal

namespace Paper



theorem annealed_kernel_convergence {d : Nat}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (KN : Nat → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (hconv : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∃ N0 : Nat, ∀ N, N0 ≤ N → ∀ x ∈ B,
        pathLevyProkhorovDist (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
          (jointPathProbabilityMeasure K hK omega x) < eps) :
    ∀ x : SpatialCoordinates d, ∀ F : BoundedContinuousFunction (DiffusionPath d) ℝ,
      Tendsto
        (fun N : Nat => ∫ omega, (∫ path, F path ∂(KN N (omega, x)))
          ∂(chaosSampleLaw M).toMeasure)
        atTop
        (nhds (∫ omega, (∫ path, F path ∂(K (omega, x)))
          ∂(chaosSampleLaw M).toMeasure)) := by
  intro x F
  letI : MetricSpace (DiffusionPath d) :=
    TopologicalSpace.completelyMetrizableMetric (DiffusionPath d)
  have hpoint : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      Tendsto
        (fun N : Nat => ∫ path, F path ∂(KN N (omega, x)))
        atTop
        (nhds (∫ path, F path ∂(K (omega, x)))) := by
    filter_upwards [hconv] with omega hω
    let μN : Nat → ProbabilityMeasure (DiffusionPath d) := fun N =>
      jointPathProbabilityMeasure (KN N) (hKN N) omega x
    let μ : ProbabilityMeasure (DiffusionPath d) :=
      jointPathProbabilityMeasure K hK omega x
    have hdist : ∀ eps : ℝ, 0 < eps → ∃ N0 : Nat, ∀ N, N0 ≤ N →
        pathLevyProkhorovDist (μN N) μ < eps := by
      intro eps heps
      obtain ⟨N0, hN0⟩ := hω {x} isCompact_singleton eps heps
      refine ⟨N0, fun N hN => ?_⟩
      exact hN0 N hN x (Set.mem_singleton x)
    have hμ : Tendsto
        (fun N => (LevyProkhorov.ofMeasure (μN N) :
          LevyProkhorov (ProbabilityMeasure (DiffusionPath d))))
        atTop
        (nhds (LevyProkhorov.ofMeasure μ)) := by
      apply Metric.tendsto_atTop.2
      intro eps heps
      obtain ⟨N0, hN0⟩ := hdist eps heps
      refine ⟨N0, fun N hN => ?_⟩
      rw [LevyProkhorov.dist_probabilityMeasure_def]
      exact hN0 N hN
    have hμ' : Tendsto (fun N => μN N) atTop (nhds μ) :=
      (LevyProkhorov.continuous_toMeasure_probabilityMeasure.tendsto
        (LevyProkhorov.ofMeasure μ)).comp hμ
    have hF := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ') F
    simpa [μN, μ, jointPathProbabilityMeasure] using hF
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
      (bound := fun _ => ‖F‖)
  · intro N
    exact ((F.continuous.stronglyMeasurable.integral_kernel).comp_measurable
      (measurable_prodMk_right (y := x))).aestronglyMeasurable
  · exact integrable_const ‖F‖
  · intro N
    filter_upwards with omega
    letI : IsProbabilityMeasure (KN N (omega, x)) :=
      (hKN N).isProbabilityMeasure (omega, x)
    exact (norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall fun path => F.norm_coe_le_norm path)).trans_eq (by
        simp only [MeasureTheory.measureReal_def,
          MeasureTheory.IsProbabilityMeasure.measure_univ, ENNReal.toReal_one, mul_one])
  · exact hpoint

end Paper
