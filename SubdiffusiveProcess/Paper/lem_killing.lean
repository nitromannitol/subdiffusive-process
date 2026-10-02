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
import SubdiffusiveProcess.Paper.Support.LimitPropertiesSuppliers

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem lem_killing
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
    (Qc : ℕ → SpatialCoordinates d) (Qr : ℕ → ℝ) (hQr : ∀ n, 0 < Qr n)
    (RN : ℕ → ℕ → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (Rlim : ℕ → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hident : ∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
        (x : SpatialCoordinates d),
      RN n N omega lam f x =
        ∫ path, (∫ t in Set.Ioi (0 : ℝ),
            Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              ((centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) path}
              (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
          ∂(KN N (omega, x)))
    (hres : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ x ∈ (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)),
          Tendsto (fun N => RN n N omega lam f x) atTop
            (nhds (Rlim n omega lam f x)))
    (hpass : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ x ∈ (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)),
          Tendsto (fun N ↦ ∫ path, (∫ t in Set.Ioi (0 : ℝ),
                Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                  ((centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) path}
                  (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
              ∂(KN N (omega, x)))
            atTop
            (nhds (∫ path, (∫ t in Set.Ioi (0 : ℝ),
                  Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                    ((centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) path}
                    (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                ∂(K (omega, x))))) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ x ∈ (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)),
          Rlim n omega lam f x =
            ∫ path, (∫ t in Set.Ioi (0 : ℝ),
                Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                  ((centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) path}
                  (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
              ∂(K (omega, x)) := by
  filter_upwards [hres, hpass] with omega hr hp
  intro n lam hlam f x hx
  refine tendsto_nhds_unique ?_ (hp n lam hlam f x hx)
  refine (hr n lam hlam f x hx).congr fun N => ?_
  exact hident n N omega lam f x

end Paper
