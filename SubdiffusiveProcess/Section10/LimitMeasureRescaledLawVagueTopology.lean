module

public import SubdiffusiveProcess.Section10.LimitMeasureRescaledLawCarrier
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.Constructions

@[expose] public section

/-! The literal vague topology on actual locally finite spatial measures.
Only its definition and elementary convergence characterization are proved
here. No Riesz, Radon or Polish-space theory is developed, and no Borel
identification is assumed or instantiated. -/

open MeasureTheory SubdiffusiveProcess Filter Topology
open scoped CompactlySupported

noncomputable section
namespace SubdiffusiveProcess.Section10

/-- The vague topology is the initial topology of all real compact-test
integrals of the actual measure. The carrier remains the literal locally
finite measure subtype; it is not replaced by its test readouts. -/
@[instance_reducible]
def spatialVagueTopology (d : ℕ) : TopologicalSpace (LocallyFiniteSpatialMeasure d) :=
  TopologicalSpace.induced
    (fun mu : LocallyFiniteSpatialMeasure d =>
      fun f : C_c(SpatialCoordinates d, ℝ) => ∫ x, f x ∂mu.val) inferInstance

instance instSpatialVagueTopology (d : ℕ) :
    TopologicalSpace (LocallyFiniteSpatialMeasure d) := spatialVagueTopology d

/-- Every member of the literal carrier is a regular Borel measure, by the
existing Mathlib finite-dimensional sigma-compact regularity instance. -/
theorem locallyFiniteSpatialMeasure_regular {d : ℕ} (mu : LocallyFiniteSpatialMeasure d) :
    mu.val.Regular := by
  have : IsLocallyFiniteMeasure mu.val := mu.property
  infer_instance

/-- Compact tests are genuinely integrable on every measure in the carrier. -/
theorem integrable_spatialVagueTest {d : ℕ} (mu : LocallyFiniteSpatialMeasure d)
    (f : C_c(SpatialCoordinates d, ℝ)) : Integrable f mu.val := by
  have : IsLocallyFiniteMeasure mu.val := mu.property
  exact f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport

/-- The named topology has exactly the test-integral convergence used by
the actual existing limiting-measure supplier. -/
theorem tendsto_spatialVagueTopology_iff {d : ℕ}
    (muN : ℕ → LocallyFiniteSpatialMeasure d) (mu : LocallyFiniteSpatialMeasure d) :
    Tendsto muN atTop (𝓝 mu) ↔
      MeasuresConvergeLocally (fun n => (muN n).val) mu.val := by
  change Tendsto muN atTop
    (@nhds _ (spatialVagueTopology d) mu) ↔ _
  rw [spatialVagueTopology, nhds_induced, Filter.tendsto_comap_iff, tendsto_pi_nhds]
  rfl

end SubdiffusiveProcess.Section10
