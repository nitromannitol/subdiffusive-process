import SubdiffusiveProcess.Main.BilateralField
import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.Main.CommonScaleLaw
import SubdiffusiveProcess.Geometry.Cube
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Probability.Martingale.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

open Filter MeasureTheory ProbabilityTheory Topology
open scoped CompactlySupported ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

def conditionalFineFiltration {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) :
    Filtration ℕ (inferInstance : MeasurableSpace (BilateralField d)) where
  seq N :=
    (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap H ⊔
    (⨆ j : Fin (N + 1),
      (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
        (fun omega ↦ omega (-(Int.ofNat j))))
  mono' N N' hNN' := by
    apply sup_le_sup le_rfl
    refine iSup_le fun j ↦ le_iSup_of_le
      ⟨j, Nat.lt_succ_of_le ((Nat.lt_succ_iff.mp j.isLt).trans hNN')⟩ ?_
    rfl
  le' N := by
    apply sup_le
    · exact hH.comap_le
    · exact iSup_le (fun j ↦ (measurable_pi_apply _).comap_le)

end SubdiffusiveProcess
