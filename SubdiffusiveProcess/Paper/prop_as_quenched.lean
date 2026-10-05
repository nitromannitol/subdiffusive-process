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
public import SubdiffusiveProcess.Vocab.Ahom
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import SubdiffusiveProcess.Paper.lem_resolvents_to_paths
public import SubdiffusiveProcess.Paper.limit_kernel
public import SubdiffusiveProcess.Paper.in_cutoff_start_continuity
public import SubdiffusiveProcess.Paper.Support.LimitPropertiesSuppliers
public import SubdiffusiveProcess.Paper.cor_as_resolvent
public import SubdiffusiveProcess.Paper.cube_exhaustion
public import SubdiffusiveProcess.Paper.lem_killing
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.cutoff_lifetime_package

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



theorem prop_as_quenched
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
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


end SubdiffusiveProcess.Paper
