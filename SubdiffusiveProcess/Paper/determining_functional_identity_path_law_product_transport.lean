module

public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Main.DiffusionPath
public import MarkovProcess.FiniteTime.ProjectiveFamily

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess.Paper



theorem determining_functional_identity_path_law_product_transport
    {d : Nat}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : Nat → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : Nat → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (_hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (N : Nat) (I : Finset NNReal)
      (x : SpatialCoordinates d)
      (g : I → BoundedContinuousFunction (SpatialCoordinates d) ℝ),
      (∫ path, ∏ t : I, g t (path (t : NNReal)) ∂(KN N (omega, x))) =
        ∫ y, ∏ t : I, g t (y t) ∂
          (SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x) := by
  rcases hin with ⟨_, _, hmap⟩
  filter_upwards [hmap] with omega hmap
  intro N I x g
  have heval : Measurable (ContinuousPath.finsetEvaluation
      (alpha := SpatialCoordinates d) I) := by
    rw [measurable_pi_iff]
    intro t
    exact ContinuousPath.measurable_coordinateProcess (alpha := SpatialCoordinates d) (t : NNReal)
  have htest : Measurable (fun y : I → SpatialCoordinates d ↦
      ∏ t : I, g t (y t)) := by
    exact Finset.univ.measurable_fun_prod fun t _ ↦
      (g t).continuous.measurable.comp (measurable_pi_apply t)
  have hmap' : Measure.map (ContinuousPath.finsetEvaluation
      (alpha := SpatialCoordinates d) I) (KN N (omega, x)) =
      SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x := by
    simpa only [Kernel.map_apply _ heval] using hmap N I x
  calc
    (∫ path, ∏ t : I, g t (path (t : NNReal)) ∂(KN N (omega, x))) =
        ∫ y, (∏ t : I, g t (y t)) ∂
          Measure.map (ContinuousPath.finsetEvaluation
            (alpha := SpatialCoordinates d) I) (KN N (omega, x)) := by
      symm
      rw [integral_map heval.aemeasurable htest.aestronglyMeasurable]
      rfl
    _ = ∫ y, ∏ t : I, g t (y t) ∂
          (SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x) := by
      rw [hmap']

end SubdiffusiveProcess.Paper
