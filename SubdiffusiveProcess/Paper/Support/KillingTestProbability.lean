module

public import SubdiffusiveProcess.Paper.Support.KillingFixedTest
public import SubdiffusiveProcess.Section9.KilledUniformCommonSubsequence
public import SubdiffusiveProcess.Analysis.KilledOccupationResolvent

@[expose] public section

/-! Supports: mfd_lem_killing.
Actual-law identification at a fixed shift and source, simultaneously at every
starting point. Uniform convergence in probability produces the required common
subsequence; it is not assumed on the full sequence.
-/
open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.Analysis
open scoped ENNReal NNReal LevyProkhorov
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem aux_mfd_lem_killing_identify_test_in_probability
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (hin : in_crossing M H PN KN)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (Rf Rone : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hpath : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps →
        Tendsto (fun N => (chaosSampleLaw M).toMeasure
          {omega | ∃ x ∈ B, eps ≤ pathLevyProkhorovDist
            (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
            (jointPathProbabilityMeasure K hK omega x)}) atTop (𝓝 0))
    (hf : ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
      ∃ N0 : ℕ, ∀ N, N0 ≤ N → (chaosSampleLaw M).toMeasure
        {omega | ∃ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
          eps ≤ |killedOccupationResolvent (centeredCube z r hr) KN N omega lam f x -
            Rf omega x|} ≤ ENNReal.ofReal rho)
    (hone : ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
      ∃ N0 : ℕ, ∀ N, N0 ≤ N → (chaosSampleLaw M).toMeasure
        {omega | ∃ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
          eps ≤ |killedOccupationResolvent (centeredCube z r hr) KN N omega lam
            (BoundedContinuousFunction.const _ 1) x - Rone omega x|} ≤ ENNReal.ofReal rho)
    (hzero : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)), Rone omega x = 0) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
        Rf omega x = killedOccupationResolvent (centeredCube z r hr)
          (fun _ => K) 0 omega lam f x := by
  classical
  let S : ℕ → Set (SpatialCoordinates d)
    | 0 => closure (centeredCube z r hr : Set (SpatialCoordinates d))
    | 1 => closure (centeredCube z r hr : Set (SpatialCoordinates d))
    | n + 2 => Metric.closedBall 0 n
  let D : ℕ → ℕ → BilateralField d → SpatialCoordinates d → ℝ
    | 0, N, omega, x =>
        |killedOccupationResolvent (centeredCube z r hr) KN N omega lam f x - Rf omega x|
    | 1, N, omega, x =>
        |killedOccupationResolvent (centeredCube z r hr) KN N omega lam
          (BoundedContinuousFunction.const _ 1) x - Rone omega x|
    | _ + 2, N, omega, x => pathLevyProkhorovDist
        (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
        (jointPathProbabilityMeasure K hK omega x)
  have hD : ∀ i eps, 0 < eps → ∀ rho : ℝ, 0 < rho →
      ∃ N0 : ℕ, ∀ N, N0 ≤ N → (chaosSampleLaw M).toMeasure
        {omega | ∃ x ∈ S i, eps ≤ D i N omega x} ≤ ENNReal.ofReal rho := by
    intro i eps heps rho hrho
    rcases i with _ | i
    · exact hf eps heps rho hrho
    rcases i with _ | n
    · exact hone eps heps rho hrho
    · exact (SubdiffusiveProcess.tendsto_zero_ennreal_iff_real _).mp
        (hpath _ (isCompact_closedBall _ _) eps heps) rho hrho
  obtain ⟨phi, _hphi, hae⟩ := SubdiffusiveProcess.Section9.exists_ae_uniform_on_countable_sets_subsequence
    (chaosSampleLaw M).toMeasure S D hD
  have hrestart := lem_tightness_deterministic_restart hd M H PN KN hKN hin
  filter_upwards [hae, hrestart, hzero] with omega hω hrω hzω
  intro x hx
  have hrad : 0 < r / 2 := half_pos hr
  have hQ : (centeredCube z r hr : Set (SpatialCoordinates d)) = Metric.ball z (r / 2) := rfl
  have hcl : closure (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Metric.closedBall z (r / 2) := by rw [hQ, closure_ball _ hrad.ne']
  let μN : ℕ → SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d) :=
    fun j y => jointPathProbabilityMeasure (KN (phi j)) (hKN (phi j)) omega y
  have hrest : ∀ j y (t : ℝ≥0) (A : Set (DiffusionPath d)),
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d) t] A →
        ∀ F : DiffusionPath d → ℝ≥0∞, Measurable F →
          (∫⁻ p in A, F (ContinuousPath.shift t p) ∂(μN j y : Measure _)) =
            ∫⁻ p in A, ∫⁻ q, F q ∂(μN j (p t) : Measure _) ∂(μN j y : Measure _) :=
    fun j y t A hA F hF => hrω (phi j) y t A hA F hF
  have hunifone : ∀ eps : ℝ, 0 < eps → ∃ J0 : ℕ, ∀ j, J0 ≤ j →
      ∀ y ∈ Metric.closedBall z (r / 2),
        |∫ p, aux_in_stopped_passage_occ (Metric.ball z (r / 2)) lam
          (BoundedContinuousFunction.const _ 1) p ∂(μN j y : Measure _) - Rone omega y| < eps := by
    intro eps heps
    obtain ⟨J0, hJ0⟩ := hω 1 eps heps
    refine ⟨J0, fun j hj y hy => ?_⟩
    exact hJ0 j hj y (by change y ∈ closure _; rw [hcl]; exact hy)
  have hLf : Tendsto (fun j => ∫ p,
      aux_in_stopped_passage_occ (Metric.ball z (r / 2)) lam f p ∂(μN j x : Measure _))
      atTop (𝓝 (Rf omega x)) := by
    rw [Metric.tendsto_atTop]
    intro eps heps
    obtain ⟨J0, hJ0⟩ := hω 0 eps heps
    refine ⟨J0, fun j hj => ?_⟩
    rw [Real.dist_eq]
    exact hJ0 j hj x (subset_closure hx)
  obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
  have hxn : x ∈ Metric.closedBall (0 : SpatialCoordinates d) n := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hn
  have hμ : Tendsto (fun j => μN j x) atTop
      (𝓝 (jointPathProbabilityMeasure K hK omega x)) := by
    apply aux_in_stopped_passage_tendsto_of_pathLP
    intro eps heps
    obtain ⟨J0, hJ0⟩ := hω (n + 2) eps heps
    exact ⟨J0, fun j hj => hJ0 j hj x hxn⟩
  have hRzero : ∀ y ∈ Metric.sphere z (r / 2), Rone omega y = 0 := by
    intro y hy
    apply hzω y
    rw [hQ, Metric.mem_ball, Metric.mem_sphere] at *
    exact not_lt.mpr hy.ge
  exact aux_mfd_lem_killing_identify_one_test z hrad hlam μN
    (jointPathProbabilityMeasure K hK omega x) hrest (Rone omega)
    (Rone omega).continuous.continuousOn hRzero hunifone x hx hμ f (Rf omega x) hLf

end Paper
