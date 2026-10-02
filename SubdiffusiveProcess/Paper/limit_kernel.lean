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
import SubdiffusiveProcess.Paper.finiteDimensional_cutoff
import SubdiffusiveProcess.Paper.in_crossing
import SubdiffusiveProcess.Paper.in_cutoff_start_continuity
import SubdiffusiveProcess.Paper.prop_quenched_convergence
import SubdiffusiveProcess.Paper.resolvent_datum
import SubdiffusiveProcess.Paper.limit_kernel_path_limit
import SubdiffusiveProcess.Paper.limit_kernel_markov_passage

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem limit_kernel
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (hcauchy : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
        ∃ N0 : ℕ, ∀ N N' : ℕ, N0 ≤ N → N0 ≤ N' →
          (chaosSampleLaw M).toMeasure
              {omega : BilateralField d | ∃ x ∈ B, eps ≤
                pathLevyProkhorovDist
                  (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                  (jointPathProbabilityMeasure (KN N') (hKN N') omega x)} ≤
            ENNReal.ofReal rho)
    (hcont : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ N : ℕ, Continuous (fun x : SpatialCoordinates d =>
        jointPathProbabilityMeasure (KN N) (hKN N) omega x))
    (hmarkov : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (I : Finset ℝ≥0) (x : SpatialCoordinates d),
        (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
          SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x) :
    ∃ (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
      (_ : ∀ omega, (P omega).IsConservative)
      (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
      (hK : IsMarkovKernel K),
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        Continuous (fun x : SpatialCoordinates d =>
          jointPathProbabilityMeasure K hK omega x)) ∧
      ((∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
          SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x) ∧
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
          ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
            (chaosSampleLaw M).toMeasure
                {omega : BilateralField d | ∃ x ∈ B, eps ≤
                  pathLevyProkhorovDist
                    (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                    (jointPathProbabilityMeasure K hK omega x)} ≤
              ENNReal.ofReal rho) := by
  classical
  have hpath_limit :
      ∃ (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hK : IsMarkovKernel K),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          Continuous (fun x : SpatialCoordinates d =>
            jointPathProbabilityMeasure K hK omega x)) ∧
        (∀ B : Set (SpatialCoordinates d), IsCompact B →
          ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
            ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
              (chaosSampleLaw M).toMeasure
                  {omega : BilateralField d | ∃ x ∈ B, eps ≤
                    pathLevyProkhorovDist
                      (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                      (jointPathProbabilityMeasure K hK omega x)} ≤
                ENNReal.ofReal rho) := by
    exact limit_kernel_path_limit M KN hKN hcauchy hcont
  obtain ⟨K, hK, hK_cont, hK_conv⟩ := hpath_limit
  have hlimit_markov :
      ∃ (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (_ : ∀ omega, (P omega).IsConservative),
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
            SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x := by
    exact limit_kernel_markov_passage hd M H PN KN hKN hin K hK hK_cont hK_conv
  obtain ⟨P, hP, hP_attach⟩ := hlimit_markov
  exact ⟨P, hP, K, hK, hK_cont, ⟨hP_attach, hK_conv⟩⟩

end Paper
