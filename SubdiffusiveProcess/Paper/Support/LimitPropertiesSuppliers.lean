import SubdiffusiveProcess.Main.BilateralField
import SubdiffusiveProcess.Main.CutoffSpeedMeasure
import SubdiffusiveProcess.Main.CutoffSpeedDensity
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.WeightedChaosCutoff
import SubdiffusiveProcess.Main.ChaosCutoff
import SubdiffusiveProcess.Main.ConditionalFineFiltration
import SubdiffusiveProcess.Main.MeasuresConvergeLocally
import SubdiffusiveProcess.Main.SemigroupSymmetric
import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
import SubdiffusiveProcess.Main.HasStrongMarkovRestart
import SubdiffusiveProcess.Main.HasFiniteMeanExits
import SubdiffusiveProcess.Main.PathLevyProkhorovDist
import SubdiffusiveProcess.Main.PhysicalRescaledPath
import SubdiffusiveProcess.Main.PhysicalTimeFactor
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.DiffusionPath
import SubdiffusiveProcess.Main.MeasureTrace
import SubdiffusiveProcess.Sobolev.ResponseSpace
import SubdiffusiveProcess.Lane3.DirichletForm
import SubdiffusiveProcess.Lane2.KilledInverse
import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.Probability.CubeMassMartingale
import SubdiffusiveProcess.Main.CommonScaleLaw
import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Inputs.MarkovProcesses
import MarkovProcess.Trajectory.StoppingLtTop
import MarkovProcess.Path.ExitTime
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
import SubdiffusiveProcess.Frozen.Vocab.Ahom
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import SubdiffusiveProcess.Probability.PathLawMetricSeparation
import SubdiffusiveProcess.Lane1.TimeMarginal
import SubdiffusiveProcess.Paper.prop_quenched_convergence
import SubdiffusiveProcess.Paper.limit_kernel
import SubdiffusiveProcess.Paper.prop_chaos_growth
import SubdiffusiveProcess.Paper.prop_limit_properties_strong_markov
import SubdiffusiveProcess.Paper.prop_limit_properties_cutoff_symmetry
import SubdiffusiveProcess.Paper.prop_limit_properties_symmetry_limit
import SubdiffusiveProcess.Paper.in_cutoff_start_continuity
import SubdiffusiveProcess.Paper.in_crossing
import SubdiffusiveProcess.Paper.tight_fixed_cutoff
import SubdiffusiveProcess.Paper.cutoff_lifetime_package




open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem aux_prop_limit_properties_of_suppliers
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hP : ∀ omega, (P omega).IsConservative)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (hin : in_crossing M H PN KN)
    (hinput : aux_cutoff_lifetime_package_LocalInput M H KN)
    (hlim : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x)
    (hconv : ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      Tendsto (fun N ↦ (chaosSampleLaw M).toMeasure
          {omega : BilateralField d | ∃ x ∈ B, eps ≤
            pathLevyProkhorovDist
              (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
              (jointPathProbabilityMeasure K hK omega x)}) atTop (nhds 0))
    (hmu : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∃ mu : Measure (SpatialCoordinates d),
        MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N) mu ∧
        IsLocallyFiniteMeasure mu) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x) ∧
      (∀ (t : ℝ≥0) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
        Continuous (kernelIntegral (P omega t) f)) ∧
      HasStrongMarkovRestart K omega ∧
      (∀ mu : Measure (SpatialCoordinates d),
        MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N) mu →
        IsLocallyFiniteMeasure mu → SemigroupSymmetric (P omega) mu) := by
  obtain ⟨L, hL, hLlocal, hLstrong⟩ := aux_cutoff_lifetime_package_local M H KN hinput
  have hlocal := tight_fixed_cutoff hd M H hH PN KN hKN hin L hL
    hLlocal
  have hcontKN := in_cutoff_start_continuity hd M H hH PN KN hKN hin hlocal
  have htri : ∀ (a b c : ProbabilityMeasure (DiffusionPath d)),
      pathLevyProkhorovDist a c ≤ pathLevyProkhorovDist a b +
        pathLevyProkhorovDist b c := by
    intro a b c
    letI : MetricSpace (DiffusionPath d) :=
      TopologicalSpace.completelyMetrizableMetric (DiffusionPath d)
    exact levyProkhorovDist_triangle (a : Measure (DiffusionPath d))
      (b : Measure (DiffusionPath d)) (c : Measure (DiffusionPath d))
  have hsymm : ∀ (a b : ProbabilityMeasure (DiffusionPath d)),
      pathLevyProkhorovDist a b = pathLevyProkhorovDist b a := by
    intro a b
    letI : MetricSpace (DiffusionPath d) :=
      TopologicalSpace.completelyMetrizableMetric (DiffusionPath d)
    exact levyProkhorovDist_comm (a : Measure (DiffusionPath d))
      (b : Measure (DiffusionPath d))
  have hcauchy : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
        ∃ N0 : ℕ, ∀ N N', N0 ≤ N → N0 ≤ N' →
          (chaosSampleLaw M).toMeasure
              {omega : BilateralField d | ∃ x ∈ B, eps ≤
                pathLevyProkhorovDist
                  (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                  (jointPathProbabilityMeasure (KN N') (hKN N') omega x)} ≤
            ENNReal.ofReal rho := by
    intro B hB eps heps rho hrho
    have heps2 : 0 < eps / 2 := by linarith
    have hrho2 : 0 < rho / 2 := by linarith
    have hN := (hconv B hB (eps / 2) heps2).eventually_lt_const
      (ENNReal.ofReal_pos.mpr hrho2)
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 hN
    refine ⟨N0, ?_⟩
    intro N N' hN0N hN0N'
    have hN' := hN0 N hN0N
    have hN'' := hN0 N' hN0N'
    have hsubset :
        {omega : BilateralField d | ∃ x ∈ B, eps ≤
          pathLevyProkhorovDist
            (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
            (jointPathProbabilityMeasure (KN N') (hKN N') omega x)} ⊆
        {omega : BilateralField d | ∃ x ∈ B, eps / 2 ≤
          pathLevyProkhorovDist
            (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
            (jointPathProbabilityMeasure K hK omega x)} ∪
        {omega : BilateralField d | ∃ x ∈ B, eps / 2 ≤
          pathLevyProkhorovDist
            (jointPathProbabilityMeasure (KN N') (hKN N') omega x)
            (jointPathProbabilityMeasure K hK omega x)} := by
      intro omega homega
      rcases homega with ⟨x, hxB, hdist⟩
      have hleft : eps / 2 ≤ pathLevyProkhorovDist
          (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
          (jointPathProbabilityMeasure K hK omega x) ∨
          eps / 2 ≤ pathLevyProkhorovDist
          (jointPathProbabilityMeasure K hK omega x)
          (jointPathProbabilityMeasure (KN N') (hKN N') omega x) := by
        by_contra hn
        push_neg at hn
        have hbound := htri
          (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
          (jointPathProbabilityMeasure K hK omega x)
          (jointPathProbabilityMeasure (KN N') (hKN N') omega x)
        linarith
      rcases hleft with hleft | hright
      · exact Or.inl ⟨x, hxB, hleft⟩
      · exact Or.inr ⟨x, hxB, (hsymm _ _).symm ▸ hright⟩
    calc
      (chaosSampleLaw M).toMeasure
          {omega : BilateralField d | ∃ x ∈ B, eps ≤
            pathLevyProkhorovDist
              (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
              (jointPathProbabilityMeasure (KN N') (hKN N') omega x)} ≤
        (chaosSampleLaw M).toMeasure
          ({omega : BilateralField d | ∃ x ∈ B, eps / 2 ≤
            pathLevyProkhorovDist
              (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
              (jointPathProbabilityMeasure K hK omega x)} ∪
           {omega : BilateralField d | ∃ x ∈ B, eps / 2 ≤
            pathLevyProkhorovDist
              (jointPathProbabilityMeasure (KN N') (hKN N') omega x)
              (jointPathProbabilityMeasure K hK omega x)}) :=
          measure_mono hsubset
      _ ≤ (chaosSampleLaw M).toMeasure
          {omega : BilateralField d | ∃ x ∈ B, eps / 2 ≤
            pathLevyProkhorovDist
              (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
              (jointPathProbabilityMeasure K hK omega x)} +
          (chaosSampleLaw M).toMeasure
          {omega : BilateralField d | ∃ x ∈ B, eps / 2 ≤
            pathLevyProkhorovDist
              (jointPathProbabilityMeasure (KN N') (hKN N') omega x)
              (jointPathProbabilityMeasure K hK omega x)} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (rho / 2) + ENNReal.ofReal (rho / 2) :=
        add_le_add hN'.le hN''.le
      _ = ENNReal.ofReal rho := by
        have hrhohalf : 0 ≤ rho / 2 := hrho2.le
        rw [← ENNReal.ofReal_add hrhohalf hrhohalf]
        congr 1
        ring
  have hmarkov := hin.2.2
  obtain ⟨P0, hP0, K0, hK0, hcont0, hlim0, hconv0⟩ :=
    limit_kernel hd M H hH PN KN hKN hin hcauchy hcontKN hmarkov
  have hK0eq : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps →
        (chaosSampleLaw M).toMeasure
          {omega : BilateralField d | ∃ x ∈ B, eps ≤
            pathLevyProkhorovDist
              (jointPathProbabilityMeasure K hK omega x)
              (jointPathProbabilityMeasure K0 hK0 omega x)} = 0 := by
    intro B hB eps heps
    apply le_antisymm
    · refine ENNReal.le_of_forall_pos_le_add ?_
      intro eta heta heta_top
      have hetaR : 0 < (eta : ℝ) := by exact_mod_cast heta
      have heps2 : 0 < eps / 2 := by linarith
      have hhalf : 0 < (eta : ℝ) / 2 := by linarith
      have hN1 := (hconv B hB (eps / 2) heps2).eventually_lt_const
        (ENNReal.ofReal_pos.mpr hhalf)
      obtain ⟨N1, hN1⟩ := eventually_atTop.1 hN1
      obtain ⟨N2, hN2⟩ := hconv0 B hB (eps / 2) heps2 ((eta : ℝ) / 2) hhalf
      let N0 := max N1 N2
      have hN1' := hN1 N0 (le_max_left _ _)
      have hN2' := hN2 N0 (le_max_right _ _)
      have hhalf_eq : ENNReal.ofReal ((eta : ℝ) / 2) =
          ENNReal.ofReal (eta : ℝ) / 2 := by
        simpa using (ENNReal.ofReal_div_of_pos (x := (eta : ℝ)) (y := (2 : ℝ))
          (by norm_num))
      rw [hhalf_eq] at hN1' hN2'
      have hsubset :
          {omega : BilateralField d | ∃ x ∈ B, eps ≤
            pathLevyProkhorovDist
              (jointPathProbabilityMeasure K hK omega x)
              (jointPathProbabilityMeasure K0 hK0 omega x)} ⊆
          {omega : BilateralField d | ∃ x ∈ B, eps / 2 ≤
            pathLevyProkhorovDist
              (jointPathProbabilityMeasure (KN N0) (hKN N0) omega x)
              (jointPathProbabilityMeasure K hK omega x)} ∪
          {omega : BilateralField d | ∃ x ∈ B, eps / 2 ≤
            pathLevyProkhorovDist
              (jointPathProbabilityMeasure (KN N0) (hKN N0) omega x)
              (jointPathProbabilityMeasure K0 hK0 omega x)} := by
        intro omega homega
        rcases homega with ⟨x, hxB, hdist⟩
        have hsplit : eps / 2 ≤ pathLevyProkhorovDist
            (jointPathProbabilityMeasure (KN N0) (hKN N0) omega x)
            (jointPathProbabilityMeasure K hK omega x) ∨
            eps / 2 ≤ pathLevyProkhorovDist
            (jointPathProbabilityMeasure (KN N0) (hKN N0) omega x)
            (jointPathProbabilityMeasure K0 hK0 omega x) := by
          by_contra hn
          push_neg at hn
          have hbound := htri
            (jointPathProbabilityMeasure K hK omega x)
            (jointPathProbabilityMeasure (KN N0) (hKN N0) omega x)
            (jointPathProbabilityMeasure K0 hK0 omega x)
          have hfirst : pathLevyProkhorovDist
              (jointPathProbabilityMeasure K hK omega x)
              (jointPathProbabilityMeasure (KN N0) (hKN N0) omega x) < eps / 2 := by
            rw [hsymm]
            exact hn.1
          have hsecond : pathLevyProkhorovDist
              (jointPathProbabilityMeasure (KN N0) (hKN N0) omega x)
              (jointPathProbabilityMeasure K0 hK0 omega x) < eps / 2 := hn.2
          linarith
        rcases hsplit with hleft | hright
        · exact Or.inl ⟨x, hxB, hleft⟩
        · exact Or.inr ⟨x, hxB, hright⟩
      have hbound :
          (chaosSampleLaw M).toMeasure
            {omega : BilateralField d | ∃ x ∈ B, eps ≤
              pathLevyProkhorovDist
                (jointPathProbabilityMeasure K hK omega x)
                (jointPathProbabilityMeasure K0 hK0 omega x)} ≤
            ENNReal.ofReal (eta : ℝ) := by
        calc
          (chaosSampleLaw M).toMeasure
              {omega : BilateralField d | ∃ x ∈ B, eps ≤
                pathLevyProkhorovDist
                  (jointPathProbabilityMeasure K hK omega x)
                  (jointPathProbabilityMeasure K0 hK0 omega x)} ≤
            (chaosSampleLaw M).toMeasure
              ({omega : BilateralField d | ∃ x ∈ B, eps / 2 ≤
                pathLevyProkhorovDist
                  (jointPathProbabilityMeasure (KN N0) (hKN N0) omega x)
                  (jointPathProbabilityMeasure K hK omega x)} ∪
               {omega : BilateralField d | ∃ x ∈ B, eps / 2 ≤
                pathLevyProkhorovDist
                  (jointPathProbabilityMeasure (KN N0) (hKN N0) omega x)
                  (jointPathProbabilityMeasure K0 hK0 omega x)}) :=
              measure_mono hsubset
          _ ≤ (chaosSampleLaw M).toMeasure
              {omega : BilateralField d | ∃ x ∈ B, eps / 2 ≤
                pathLevyProkhorovDist
                  (jointPathProbabilityMeasure (KN N0) (hKN N0) omega x)
                  (jointPathProbabilityMeasure K hK omega x)} +
              (chaosSampleLaw M).toMeasure
              {omega : BilateralField d | ∃ x ∈ B, eps / 2 ≤
                pathLevyProkhorovDist
                  (jointPathProbabilityMeasure (KN N0) (hKN N0) omega x)
                  (jointPathProbabilityMeasure K0 hK0 omega x)} := measure_union_le _ _
          _ ≤ ENNReal.ofReal (eta : ℝ) / 2 + ENNReal.ofReal (eta : ℝ) / 2 :=
            add_le_add hN1'.le hN2'
          _ = ENNReal.ofReal (eta : ℝ) := by
            calc
              ENNReal.ofReal (eta : ℝ) / 2 + ENNReal.ofReal (eta : ℝ) / 2 =
                  (ENNReal.ofReal (eta : ℝ) + ENNReal.ofReal (eta : ℝ)) / 2 := by
                exact ENNReal.div_add_div_same
              _ = ENNReal.ofReal ((eta : ℝ) + (eta : ℝ)) / 2 := by
                rw [ENNReal.ofReal_add (by positivity) (by positivity)]
              _ = ENNReal.ofReal (eta : ℝ) := by
                rw [show (eta : ℝ) + (eta : ℝ) = (eta : ℝ) * 2 by ring]
                rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
                rw [← ENNReal.ofReal_div_of_pos (x := (eta : ℝ) * 2) (y := (2 : ℝ))
                  (by norm_num)]
                congr 1
                ring
      simpa using hbound
    · exact bot_le
  have haeK : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ x : SpatialCoordinates d,
        jointPathProbabilityMeasure K hK omega x =
          jointPathProbabilityMeasure K0 hK0 omega x := by
    have hbounds : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ (m k : ℕ) (x : SpatialCoordinates d),
          x ∈ Metric.closedBall (0 : SpatialCoordinates d) (m : ℝ) →
          pathLevyProkhorovDist
            (jointPathProbabilityMeasure K hK omega x)
            (jointPathProbabilityMeasure K0 hK0 omega x) <
            1 / ((k : ℝ) + 1) := by
      apply ae_all_iff.2
      intro m
      apply ae_all_iff.2
      intro k
      have heps : 0 < (1 : ℝ) / ((k : ℝ) + 1) := by positivity
      have hz := hK0eq (Metric.closedBall (0 : SpatialCoordinates d) (m : ℝ))
        (isCompact_closedBall _ _) (1 / ((k : ℝ) + 1)) heps
      have hnot : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ¬ ∃ x ∈ Metric.closedBall (0 : SpatialCoordinates d) (m : ℝ),
            1 / ((k : ℝ) + 1) ≤
              pathLevyProkhorovDist
                (jointPathProbabilityMeasure K hK omega x)
                (jointPathProbabilityMeasure K0 hK0 omega x) := by
        apply MeasureTheory.ae_iff.mpr
        simpa using hz
      filter_upwards [hnot] with omega homega
      intro x hx
      exact lt_of_not_ge (fun h => homega ⟨x, hx, h⟩)
    filter_upwards [hbounds] with omega hbounds
    intro x
    obtain ⟨m, hm⟩ := exists_nat_ge (dist x 0)
    have hxball : x ∈ Metric.closedBall (0 : SpatialCoordinates d) (m : ℝ) := by
      rw [Metric.mem_closedBall]
      simpa [dist_comm] using hm
    have hlt : ∀ k : ℕ,
        pathLevyProkhorovDist
          (jointPathProbabilityMeasure K hK omega x)
          (jointPathProbabilityMeasure K0 hK0 omega x) <
          1 / ((k : ℝ) + 1) := fun k => hbounds m k x hxball
    have hle : pathLevyProkhorovDist
        (jointPathProbabilityMeasure K hK omega x)
        (jointPathProbabilityMeasure K0 hK0 omega x) ≤ 0 := by
      exact le_of_tendsto_of_tendsto tendsto_const_nhds
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        (Eventually.of_forall fun k => (hlt k).le)
    have hnonneg : 0 ≤ pathLevyProkhorovDist
        (jointPathProbabilityMeasure K hK omega x)
        (jointPathProbabilityMeasure K0 hK0 omega x) := by
      unfold pathLevyProkhorovDist
      change 0 ≤ ENNReal.toReal _
      exact ENNReal.toReal_nonneg
    exact SubdiffusiveProcess.pathLevyProkhorovDist_eq_zero_iff _ _ |>.mp
      (le_antisymm hle hnonneg)
  have hcontK : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x) := by
    filter_upwards [hcont0, haeK] with omega h0 heq
    exact h0.congr (fun x => (heq x).symm)
  have hcontP : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (t : ℝ≥0) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
        Continuous (kernelIntegral (P omega t) f) := by
    filter_upwards [hcontK, hlim] with omega hKcont hlimomega
    intro t f
    let F : BoundedContinuousFunction (DiffusionPath d) ℝ :=
      f.compContinuous ⟨fun path : DiffusionPath d => path t, continuous_eval_const t⟩
    have hF :=
      (ProbabilityMeasure.continuous_iff_forall_continuous_integral.mp hKcont) F
    have hInt : ∀ x : SpatialCoordinates d,
        (∫ path, F path ∂(jointPathProbabilityMeasure K hK omega x)) =
          kernelIntegral (P omega t) f x := by
      intro x
      have hfdd : (K (omega, x)).map
          (ContinuousPath.finsetEvaluation ({t} : Finset ℝ≥0)) =
          SubMarkovKernelSemigroup.finiteSetKernel (P omega) ({t} : Finset ℝ≥0) x := by
        rw [← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _)]
        exact hlimomega ({t} : Finset ℝ≥0) x
      have hmap := SubdiffusiveProcess.map_eval_eq_of_finsetEvaluation
        (P omega) (K (omega, x)) x t hfdd
      simp only [F, BoundedContinuousFunction.compContinuous_apply]
      change (∫ path, f (path t) ∂(K (omega, x))) = _
      rw [← integral_map (continuous_eval_const t).measurable.aemeasurable
        f.continuous.aestronglyMeasurable, hmap]
      rfl
    exact hF.congr hInt
  have hstrong : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      HasStrongMarkovRestart K omega :=
    prop_limit_properties_strong_markov hd M H PN P KN hKN K hK hcontK hin hlim hconv
  have hsym0 : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ N : ℕ, SemigroupSymmetric (PN N omega) (cutoffSpeedMeasure M H omega N) :=
    prop_limit_properties_cutoff_symmetry M H PN KN hin L hL hLlocal hLstrong
  have hsym : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ mu : Measure (SpatialCoordinates d),
        MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N) mu →
        IsLocallyFiniteMeasure mu → SemigroupSymmetric (P omega) mu :=
    prop_limit_properties_symmetry_limit M H PN P KN hKN K hK hlim hconv hin.2.2
      hcontKN hcontK hsym0
  filter_upwards [hcontK, hcontP, hstrong, hsym] with omega hKcont hPcont hstr hsy
  exact ⟨hKcont, hPcont, hstr, hsy⟩

end Paper

