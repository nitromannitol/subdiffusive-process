module

public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.CutoffSpeedMeasure
public import SubdiffusiveProcess.Main.CutoffSpeedDensity
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.WeightedChaosCutoff
public import SubdiffusiveProcess.Main.ChaosCutoff
public import SubdiffusiveProcess.Main.ConditionalFineFiltration
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.Main.SemigroupSymmetric
public import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
public import SubdiffusiveProcess.Main.HasStrongMarkovRestart
public import SubdiffusiveProcess.Main.HasFiniteMeanExits
public import SubdiffusiveProcess.Main.PathLevyProkhorovDist
public import SubdiffusiveProcess.Main.PhysicalRescaledPath
public import SubdiffusiveProcess.Main.PhysicalTimeFactor
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.DiffusionPath
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.ResponseMoments.DirichletForm
public import SubdiffusiveProcess.VariationalResponses.KilledInverse
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Probability.CubeMassMartingale
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Inputs.MarkovProcesses
public import MarkovProcess.Trajectory.StoppingLtTop
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.Frozen.Vocab.Ahom
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import SubdiffusiveProcess.Paper.finiteDimensional_cutoff
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.in_cutoff_start_continuity
public import SubdiffusiveProcess.Paper.prop_quenched_convergence
public import SubdiffusiveProcess.Paper.resolvent_datum
public import SubdiffusiveProcess.Paper.limit_kernel_path_limit
public import SubdiffusiveProcess.Paper.limit_kernel_markov_passage

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



theorem limit_kernel
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (_hH : InfraredCharacterization M H)
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
    (_hmarkov : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
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

end SubdiffusiveProcess.Paper
