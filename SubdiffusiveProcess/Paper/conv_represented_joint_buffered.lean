module

public import SubdiffusiveProcess.Paper.conv_represented_catalogue_buffered
public import SubdiffusiveProcess.Paper.conv_represented_env_interface_buffered

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- One common represented pair of operators and expanding catalogues retaining the collar traces. -/
def conv_represented_joint_buffered (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d) (envE envF : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ) : Prop :=
  aux_conv_represented_env_interface_joint d model H Ω P field envE envF z r hr Sspace
      GNE GNF GE GF NE NF ∧
    ∀ k : ℕ, ∃ e : ℕ → ℕ, (∀ i ≤ k, ∃ j, e j = i) ∧
      conv_represented_catalogue_buffered d hd model H Ω P envE envF
        (z ∘ e) (r ∘ e) (fun j => hr (e j)) (fun j => Sspace (e j)) NE NF alpha eta

end Paper
