import SubdiffusiveProcess.Paper.finiteDimensional_cutoff_full_coefficient_semigroup
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
import SubdiffusiveProcess.Paper.in_crossing
import SubdiffusiveProcess.Paper.finiteDimensional_cutoff_nonexplosion
import SubdiffusiveProcess.Paper.finiteDimensional_cutoff_path_kernel
import SubdiffusiveProcess.Paper.resolvent_datum
import SubdiffusiveProcess.Paper.lem_infrared
import SubdiffusiveProcess.Paper.in_normalization
import SubdiffusiveProcess.Paper.coefficient_physical_identity

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem finiteDimensional_cutoff
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∃ (PN : ℕ → BilateralField d →
            SubMarkovKernelSemigroup (SpatialCoordinates d))
          (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d)
            (DiffusionPath d)),
          (∀ N, IsMarkovKernel (KN N)) ∧ in_crossing M H PN KN := by
  obtain ⟨delta0_nonexp, hdelta0_nonexp_pos, hnonexplosion⟩ :=
    Paper.finiteDimensional_cutoff_nonexplosion hd
  obtain ⟨delta0_full, hdelta0_full_pos, hfull⟩ :=
    Paper.finiteDimensional_cutoff_full_coefficient_semigroup hd
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
    Paper.finiteDimensional_cutoff_path_kernel hd M H hH PN hPNcons hPNfeller hres hnonexplosion_M
  refine ⟨PN, KN, hKN_markov, ?_⟩
  unfold in_crossing
  exact ⟨hres, hPNcons, hKN_fdd⟩

end Paper
