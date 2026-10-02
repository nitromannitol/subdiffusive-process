import SubdiffusiveProcess.Paper.in_crossing
import SubdiffusiveProcess.Paper.in_cutoff_local_path_tightness
import SubdiffusiveProcess.Paper.in_cutoff_fdd_start_continuity
import MarkovProcess.Trajectory.WeakContinuity

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem in_cutoff_start_continuity
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (hlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ T : ℝ≥0, ∀ r : ℝ≥0∞, 0 < r → ∀ eta : ℝ≥0∞, 0 < eta →
          (∃ delta : ℝ≥0∞, 0 < delta ∧
            ∀ x ∈ B,
              ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
                ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
                (ContinuousPath.modulusSet T delta r)ᶜ ≤ eta) ∧
          (∃ K0 : Set (SpatialCoordinates d), IsCompact K0 ∧
            ∀ x ∈ B,
              ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
                ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
                {path : DiffusionPath d | ∀ s : ℝ≥0, s ≤ T → path s ∈ K0}ᶜ ≤ eta)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      Continuous (fun x : SpatialCoordinates d =>
        jointPathProbabilityMeasure (KN N) (hKN N) omega x) := by
  have hfdd := in_cutoff_fdd_start_continuity hd M H hH PN KN hin
  have htight := in_cutoff_local_path_tightness hd M H hH PN KN hKN hin hlocal
  filter_upwards [hfdd, htight] with omega homega htightomega
  intro N
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro F
  refine continuous_iff_continuousAt.mpr fun x0 ↦
    Metric.tendsto_nhds.mpr fun eps heps ↦ ?_
  set eps5 : ℝ := eps / 5 with heps5def
  have heps5 : 0 < eps5 := by positivity
  set Ctot : ℝ := ‖F‖ + (‖F‖ + eps5) with hCtotdef
  have hCtotpos : 0 < Ctot := by
    rw [hCtotdef]
    have hnorm := norm_nonneg F
    linarith
  set eta : ℝ := eps5 / Ctot with hetadef
  have hetapos : 0 < eta := div_pos heps5 hCtotpos
  obtain ⟨K0, hK0compact, hK0nhds⟩ := exists_compact_mem_nhds x0
  obtain ⟨Kp, hKpcompact, hKpmass⟩ :=
    htightomega N K0 hK0compact eta hetapos
  obtain ⟨G, hGcyl, hGnorm, hGapprox⟩ :=
    ContinuousPath.exists_boundedCylinder_approx F hKpcompact heps5
  have hKpmeas : MeasurableSet Kp := hKpcompact.isClosed.measurableSet
  have herror : ∀ x ∈ K0,
      |(∫ omega, F omega ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x :
          ProbabilityMeasure (DiffusionPath d))) -
        ∫ omega, G omega ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x :
          ProbabilityMeasure (DiffusionPath d))| ≤ 2 * eps5 := by
    intro x hx
    have hmass : ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
        ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d)).real Kpᶜ ≤ eta := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal hetapos.le (hKpmass x hx)
    have hbase := abs_integral_sub_le_of_approx_on
      ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
        ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d)) F G
      hKpmeas heps5.le hGapprox
    have hFG : ‖F‖ + ‖G‖ ≤ Ctot := by
      rw [hCtotdef]
      linarith [hGnorm]
    have hprod : (‖F‖ + ‖G‖) *
        ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
          ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d)).real Kpᶜ ≤ eps5 := by
      calc
        (‖F‖ + ‖G‖) *
            ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
              ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d)).real Kpᶜ
            ≤ Ctot * eta :=
          mul_le_mul hFG hmass measureReal_nonneg hCtotpos.le
        _ = eps5 := by
          rw [hetadef]
          field_simp
    linarith [hbase, hprod]
  have hcylinder : Continuous (fun x ↦
      ∫ path, G path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x :
        ProbabilityMeasure (DiffusionPath d))) := by
    obtain ⟨I, g, hg⟩ := hGcyl
    have h := homega N I g
    apply h.congr
    intro x
    rw [show (∫ path, G path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x :
        ProbabilityMeasure (DiffusionPath d))) =
        ∫ path, g (ContinuousPath.finsetEvaluation I path) ∂
          (jointPathProbabilityMeasure (KN N) (hKN N) omega x :
            ProbabilityMeasure (DiffusionPath d)) by
      congr 1
      funext path
      exact hg path]
    rw [← integral_map (ContinuousPath.measurable_finsetEvaluation I).aemeasurable
      g.continuous.aestronglyMeasurable]
    change (∫ y, g y ∂((KN N).map (ContinuousPath.finsetEvaluation I) (omega, x))) =
      ∫ y, g y ∂Measure.map (ContinuousPath.finsetEvaluation I) (KN N (omega, x))
    rw [← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
  have hnear : ∀ᶠ x in nhds x0,
      |(∫ path, G path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x :
          ProbabilityMeasure (DiffusionPath d))) -
        ∫ path, G path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x0 :
          ProbabilityMeasure (DiffusionPath d))| < eps5 := by
    have h := Metric.tendsto_nhds.mp (hcylinder.continuousAt (x := x0)) eps5 heps5
    simpa only [Real.dist_eq] using h
  filter_upwards [hnear, hK0nhds] with x hxnear hxK0
  rw [Real.dist_eq]
  have h1 := herror x hxK0
  have h2 := herror x0 (mem_of_mem_nhds hK0nhds)
  have h2' :
      |(∫ path, G path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x0 :
          ProbabilityMeasure (DiffusionPath d))) -
        ∫ path, F path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x0 :
          ProbabilityMeasure (DiffusionPath d))| ≤ 2 * eps5 := by
    rw [abs_sub_comm]
    exact h2
  have htri1 := abs_sub_le
    (∫ path, F path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x :
      ProbabilityMeasure (DiffusionPath d)))
    (∫ path, G path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x :
      ProbabilityMeasure (DiffusionPath d)))
    (∫ path, F path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x0 :
      ProbabilityMeasure (DiffusionPath d)))
  have htri2 := abs_sub_le
    (∫ path, G path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x :
      ProbabilityMeasure (DiffusionPath d)))
    (∫ path, G path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x0 :
      ProbabilityMeasure (DiffusionPath d)))
    (∫ path, F path ∂(jointPathProbabilityMeasure (KN N) (hKN N) omega x0 :
      ProbabilityMeasure (DiffusionPath d)))
  rw [heps5def] at h1 h2' hxnear
  linarith [htri1, htri2, h1, h2', hxnear]

end Paper
