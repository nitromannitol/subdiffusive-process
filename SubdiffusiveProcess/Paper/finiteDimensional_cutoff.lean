module

public import SubdiffusiveProcess.Paper.finiteDimensional_cutoff_full_coefficient_semigroup
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
public import SubdiffusiveProcess.Vocab.Ahom
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.finiteDimensional_cutoff_nonexplosion
public import SubdiffusiveProcess.Paper.finiteDimensional_cutoff_path_kernel
public import SubdiffusiveProcess.Paper.resolvent_datum
public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Paper.in_normalization
public import SubdiffusiveProcess.Paper.coefficient_physical_identity

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



theorem finiteDimensional_cutoff
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∃ (PN : ℕ → BilateralField d →
            SubMarkovKernelSemigroup (SpatialCoordinates d))
          (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d)
            (DiffusionPath d)),
          (∀ N, IsMarkovKernel (KN N)) ∧ in_crossing M H PN KN := by
  obtain ⟨delta0_nonexp, hdelta0_nonexp_pos, hnonexplosion⟩ :=
    _root_.SubdiffusiveProcess.Paper.finiteDimensional_cutoff_nonexplosion hd
  obtain ⟨delta0_full, hdelta0_full_pos, hfull⟩ :=
    _root_.SubdiffusiveProcess.Paper.finiteDimensional_cutoff_full_coefficient_semigroup hd
  set delta0 := min delta0_nonexp delta0_full with hdelta0_def
  have hdelta0_pos : 0 < delta0 := lt_min hdelta0_nonexp_pos hdelta0_full_pos
  refine ⟨delta0, hdelta0_pos, ?_⟩
  intro M H hH hdelta
  have hdelta_nonexp : M.delta ≤ delta0_nonexp :=
    le_trans hdelta (min_le_left _ _)
  have hdelta_full : M.delta ≤ delta0_full :=
    le_trans hdelta (min_le_right _ _)
  have hnonexplosion_M := hnonexplosion M H hH hdelta_nonexp
  have hfull_M := hfull M H hH hdelta_full
  obtain ⟨PN, hPNcons, hPNfeller, hres⟩ := hfull_M hnonexplosion_M
  obtain ⟨KN, hKN_markov, hKN_fdd⟩ :=
    _root_.SubdiffusiveProcess.Paper.finiteDimensional_cutoff_path_kernel hd M H hH PN hPNcons hPNfeller hres hnonexplosion_M
  refine ⟨PN, KN, hKN_markov, ?_⟩
  unfold in_crossing
  exact ⟨hres, hPNcons, hKN_fdd⟩

end SubdiffusiveProcess.Paper
