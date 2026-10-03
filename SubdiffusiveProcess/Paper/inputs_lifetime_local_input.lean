module

public import SubdiffusiveProcess.Paper.inputs_local_attached_identification

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem inputs_lifetime_local_input
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hd : 2 ≤ d) (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (hcross : in_crossing M H PN KN) :
    aux_cutoff_lifetime_package_LocalInput M H KN := by
  exact ⟨inputs_local_attached_identification M H hd hH PN KN hKN hcross⟩

end Paper

