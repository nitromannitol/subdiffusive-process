module

public import SubdiffusiveProcess.Paper.inputs_lifetime_local_input

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem inputs_lifetime_witness
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H →
      (∃ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ N, IsMarkovKernel (KN N)) ∧ in_crossing M H PN KN) →
      ∃ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ N, IsMarkovKernel (KN N)) ∧ in_crossing M H PN KN ∧
          aux_cutoff_lifetime_package_LocalInput M H KN := by
  rintro M H hH ⟨PN, KN, hKN, hcross⟩
  exact ⟨PN, KN, hKN, hcross,
    inputs_lifetime_local_input M H hd hH PN KN hKN hcross⟩

end Paper

