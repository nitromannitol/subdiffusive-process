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
import SubdiffusiveProcess.Paper.lem_resolvents_to_paths
import SubdiffusiveProcess.Paper.limit_kernel
import SubdiffusiveProcess.Paper.in_cutoff_start_continuity
import SubdiffusiveProcess.Paper.Support.LimitPropertiesSuppliers
import SubdiffusiveProcess.Paper.cor_as_resolvent
import SubdiffusiveProcess.Paper.cube_exhaustion
import SubdiffusiveProcess.Paper.lem_killing
import SubdiffusiveProcess.Paper.in_crossing
import SubdiffusiveProcess.Paper.cutoff_lifetime_package

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem prop_as_quenched
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (hin : in_crossing M H PN KN)
    (hinput : aux_cutoff_lifetime_package_LocalInput M H KN)
    (Qc : ℕ → SpatialCoordinates d) (Qr : ℕ → ℝ) (hQr : ∀ n, 0 < Qr n)
    (hQ : ∀ U : Set (SpatialCoordinates d), Bornology.IsBounded U →
      ∃ n : ℕ, U ⊆ (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)))
    (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hP : ∀ omega, (P omega).IsConservative)
    (hkilled : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∀ eps : ℝ, 0 < eps →
            ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
              ∀ x ∈ closure (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)),
                |(∫ path, (∫ t in Set.Ioi (0 : ℝ),
                      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                        ((centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) path}
                        (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                    ∂(KN N (omega, x)))
                 - (∫ path, (∫ t in Set.Ioi (0 : ℝ),
                        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                          ((centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) path}
                          (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                      ∂(K (omega, x)))| < eps)
    (hprops : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x) ∧
      HasStrongMarkovRestart K omega)
    (hlim : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (I : Finset ℝ≥0) (x : SpatialCoordinates d),
        K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
          SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x)
    (hfiniteCont : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      Continuous (fun x : SpatialCoordinates d =>
        jointPathProbabilityMeasure (KN N) (hKN N) omega x)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ eps : ℝ, 0 < eps → ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ x ∈ B,
          pathLevyProkhorovDist
            (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
            (jointPathProbabilityMeasure K hK omega x) < eps := by
  obtain ⟨L, hL, hLlocal, hLstrong⟩ := aux_cutoff_lifetime_package_local M H KN hinput
  have hin' := hin
  unfold in_crossing at hin'
  filter_upwards [hkilled, hprops, hlim, hfiniteCont, hin'.1, hin'.2.2, hLlocal, hLstrong]
    with omega hk hp hl hfc hN hI hLloc hLstr
  intro B hB eps heps
  exact lem_resolvents_to_paths hd M H hH PN KN hKN K hK hin P hP Qc Qr hQr hQ omega ⟨hN, hI⟩
    (fun N => L N omega) (fun N x => hL N omega x) hLloc hLstr hl hk hp.1 hp.2 hfc B hB eps heps


end Paper
