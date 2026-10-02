import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal NNReal

namespace Paper



def in_joint_extracted_candidates
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GN : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) : Prop :=
  IsProbabilityMeasure P ∧
  Measurable field ∧
  Measure.map field P = (chaosSampleLaw M).toMeasure ∧
  InfraredCharacterization M H ∧
  (StrictMono NE ∧ StrictMono NF) ∧
  (∀ i, (S i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i))) ∧
  (∀ i N ω f, GN i N ω f =
    (responseSolution (S i)
      (Lane4.cutoffPositiveCoefficient M H (field ω) N (z i) (hr i))
      ((sobolevVolumeLoad f).comp (S i).space.subtypeL)).val.1) ∧
  (∀ᵐ ω ∂P, ∀ i,
    Tendsto (fun n => GN i (NE n) ω) atTop (𝓝 (GE i ω)) ∧
    Tendsto (fun n => GN i (NF n) ω) atTop (𝓝 (GF i ω)))

end Paper
