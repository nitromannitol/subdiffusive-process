module

public import SubdiffusiveProcess.Paper.conv_represented_catalogue_grids
public import SubdiffusiveProcess.Paper.conv_represented_env_interface_buffered

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- One common represented pair of operators and expanding catalogues retaining the rational grids and collar traces. -/
def conv_represented_joint_grids (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
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
    (NE NF : ℕ → ℕ) (alpha eta : ℝ)
    (E : _root_.SubdiffusiveProcess.Paper.in_J d) (beta0 t0 : ℝ) : Prop :=
  aux_conv_represented_env_interface_joint d model H Ω P field envE envF z r hr Sspace
      GNE GNF GE GF NE NF ∧
    ∀ k : ℕ, ∃ e : ℕ → ℕ, (∀ i ≤ k, ∃ j, e j = i) ∧
      conv_represented_catalogue_grids d hd model H Ω P envE envF
        (z ∘ e) (r ∘ e) (fun j => hr (e j)) (fun j => Sspace (e j)) NE NF alpha eta E beta0 t0

end SubdiffusiveProcess.Paper
